module

public import Protobuf.Json.Types
public import Protobuf.Base64

public section

namespace Protobuf.Json

open Lean
open google.protobuf
open Protobuf.Reflection

private abbrev JM := ExceptT Error IO

private def liftReflection
    (result : IO (Except ReflectionError α)) : JM α := do
  liftExcept ((← result).mapError Error.reflection)

private def jsonKind : Lean.Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

private def childPath (path field : String) : String :=
  if path == "$" then s!"$.{field}" else s!"{path}.{field}"

private def indexPath (path : String) (index : Nat) : String :=
  s!"{path}[{index}]"

private def checkDepth (path : String) (remaining : Nat) : JM Nat := do
  if remaining == 0 then
    throw (.recursionLimit path)
  return remaining - 1

private def fieldProto (field : FieldDescriptor) : JM FieldDescriptorProto := do
  let some proto ← field.toProto
    | throw (.reflection (.staleDescriptor field.fullName))
  return proto

private def fieldNumber (field : FieldDescriptor) : JM Int32 := do
  let some number ← field.number
    | throw (.reflection
        (.invalidFieldDescriptor field.fullName "field number is absent"))
  return number

private def fieldType
    (field : FieldDescriptor) : JM FieldDescriptorProto.Type := do
  let some type ← field.effectiveWireType
    | throw (.reflection
        (.invalidFieldDescriptor field.fullName "field type is absent"))
  return type

private def ordinaryFieldName
    (field : FieldDescriptor) (useProtoName : Bool) : JM String := do
  let name? ←
    if useProtoName then field.name else field.jsonName
  let some name := name?
    | throw (.reflection
        (.invalidFieldDescriptor field.fullName "field name is absent"))
  return name

private def outputFieldName
    (field : FieldDescriptor) (options : PrintOptions) : JM String := do
  if (← field.isExtension).getD false then
    return s!"[{field.fullName}]"
  ordinaryFieldName field options.useProtoFieldNames

private def intJson (value : Int) : Lean.Json :=
  .num (JsonNumber.fromInt value)

private def natJson (value : Nat) : Lean.Json :=
  .num (JsonNumber.fromNat value)

/--
Convert a finite IEEE-754 binary64 value to an exact decimal JSON number.

Lean's general-purpose `JsonNumber.fromFloat?` currently goes through
`Float.toString`, whose native implementation prints only six fractional
digits.  In particular, ordinary small protobuf values such as the minimum
normal float and double become zero.  A binary float is an integer times a
power of two, so spelling negative powers with `5^n / 10^n` gives an exact,
portable representation without relying on a platform formatter.
-/
private def finiteFloatJsonNumber (value : Float) : JsonNumber :=
  let bits := value.toBits.toNat
  let negative := (bits >>> 63) != 0
  let rawExponent := (bits >>> 52) &&& 0x7ff
  let fraction := bits &&& ((1 <<< 52) - 1)
  let (significand, exponent) :=
    if rawExponent == 0 then
      (fraction, (-1074 : Int))
    else
      ((1 <<< 52) + fraction, Int.ofNat rawExponent - 1023 - 52)
  if significand == 0 then
    0
  else if exponent >= 0 then
    let magnitude := significand * (2 ^ exponent.toNat)
    { mantissa := if negative then -Int.ofNat magnitude else Int.ofNat magnitude
      exponent := 0 }
  else
    let decimalExponent := exponent.natAbs
    let magnitude := significand * (5 ^ decimalExponent)
    { mantissa := if negative then -Int.ofNat magnitude else Int.ofNat magnitude
      exponent := decimalExponent }

private def floatJson (value : Float) : Lean.Json :=
  if value.isNaN then
    .str "NaN"
  else if value.isInf then
    .str (if value > 0 then "Infinity" else "-Infinity")
  else
    .num (finiteFloatJsonNumber value)

private def enumDefaultNumber (descriptor : EnumDescriptor) : JM Int32 := do
  let values ← descriptor.values
  let some first := values[0]?
    | throw (.invalidValue "$"
        s!"enum `{descriptor.fullName}` has no declared values")
  let some number ← first.number
    | throw (.reflection (.staleDescriptor descriptor.fullName))
  return number

private def defaultValueForField (field : FieldDescriptor) : JM Value := do
  match ← fieldType field with
  | .TYPE_DOUBLE => return .double 0
  | .TYPE_FLOAT => return .float 0
  | .TYPE_INT64 | .TYPE_SFIXED64 | .TYPE_SINT64 =>
      return .int64 0
  | .TYPE_UINT64 | .TYPE_FIXED64 => return .uint64 0
  | .TYPE_INT32 | .TYPE_SFIXED32 | .TYPE_SINT32 =>
      return .int32 0
  | .TYPE_FIXED32 | .TYPE_UINT32 => return .uint32 0
  | .TYPE_BOOL => return .bool false
  | .TYPE_STRING => return .string .empty
  | .TYPE_BYTES => return .bytes ByteArray.empty
  | .TYPE_ENUM =>
      let some descriptor ← field.enumType
        | throw (.reflection
            (.unresolvedEnumType ((← fieldProto field).type_name.getD "")))
      return .enum descriptor (← enumDefaultNumber descriptor)
  | .TYPE_MESSAGE | .TYPE_GROUP =>
      let some descriptor ← field.messageType
        | throw (.reflection
            (.unresolvedMessageType ((← fieldProto field).type_name.getD "")))
      return .message descriptor .empty
  | .«Unknown.Value» number =>
      throw (.invalidValue "$" s!"unknown protobuf field type {number}")

private def valueIsDefault (value : Value) : JM Bool := do
  match value with
  | .double value => return value == 0
  | .float value => return value == 0
  | .int64 value => return value == 0
  | .uint64 value => return value == 0
  | .int32 value => return value == 0
  | .uint32 value => return value == 0
  | .bool value => return !value
  | .string value => return value.isEmpty
  | .bytes value => return value.isEmpty
  | .enum descriptor number =>
      return number == (← enumDefaultNumber descriptor)
  | .message _ _ => return false

private def parseIntegralNumber
    (path : String) (number : JsonNumber) : JM Int := do
  if number.exponent == 0 then
    return number.mantissa
  if number.mantissa == 0 then
    return 0
  let digits := number.mantissa.natAbs.repr.length
  if number.exponent >= digits then
    throw (.invalidValue path "integer value has a nonzero fractional part")
  let divisor := 10 ^ number.exponent
  unless number.mantissa % Int.ofNat divisor == 0 do
    throw (.invalidValue path "integer value has a nonzero fractional part")
  return number.mantissa / Int.ofNat divisor

private def parseIntegral
    (path : String) (json : Lean.Json) : JM Int := do
  match json with
  | .num number => parseIntegralNumber path number
  | .str text =>
      if text.trimAscii.copy != text then
        throw (.invalidValue path s!"`{text}` is not a valid integer")
      let parsed ←
        match Lean.Json.parse text with
        | .ok parsed => pure parsed
        | .error _ =>
            throw (.invalidValue path s!"`{text}` is not a valid integer")
      match parsed with
      | .num number => parseIntegralNumber path number
      | _ => throw (.invalidValue path s!"`{text}` is not a valid integer")
  | _ => throw (.typeMismatch path "integer or numeric string" (jsonKind json))

private def requireRange
    (path typeName : String) (value minimum maximum : Int) : JM Int := do
  if value < minimum || value > maximum then
    throw (.invalidValue path
      s!"{value} is outside the {typeName} range [{minimum}, {maximum}]")
  return value

private def parseFloat (path : String) (json : Lean.Json) : JM Float := do
  match json with
  | .num number =>
      let value := number.toFloat
      if !value.isFinite then
        throw (.invalidValue path "floating-point value is out of range")
      return value
  | .str "NaN" => return Float.ofBits 0x7ff8000000000000
  | .str "Infinity" => return Float.ofBits 0x7ff0000000000000
  | .str "-Infinity" => return Float.ofBits 0xfff0000000000000
  | .str text =>
      if text.trimAscii.copy != text then
        throw (.invalidValue path
          s!"`{text}` is not a valid floating-point value")
      match Lean.Json.parse text with
      | .ok (.num number) =>
          let value := number.toFloat
          if !value.isFinite then
            throw (.invalidValue path "floating-point value is out of range")
          return value
      | _ => throw (.invalidValue path s!"`{text}` is not a valid floating-point value")
  | _ =>
      throw (.typeMismatch path "number or numeric string" (jsonKind json))

private def decodeJsonBase64 (path text : String) : JM ByteArray := do
  let normalizedChars := text.toList.map fun c =>
    if c == '-' then '+' else if c == '_' then '/' else c
  let normalized := String.ofList normalizedChars
  let remainder := normalized.length % 4
  if remainder == 1 then
    throw (.invalidValue path "invalid base64 length")
  let padded :=
    if remainder == 0 then normalized
    else normalized ++ String.ofList (List.replicate (4 - remainder) '=')
  match Protobuf.Base64.decode padded with
  | .ok bytes => return bytes
  | .error detail => throw (.invalidValue path detail)

private def enumJson
    (path : String) (descriptor : EnumDescriptor) (number : Int32)
    (options : PrintOptions) : JM Lean.Json := do
  if descriptor.fullName == "google.protobuf.NullValue" && number == 0 then
    return .null
  if options.useEnumNumbers then
    return intJson number.toInt
  if let some value ← descriptor.findValueByNumber number then
    let some name ← value.name
      | throw (.reflection (.staleDescriptor descriptor.fullName))
    return .str name
  if (← descriptor.isClosed).getD false then
    throw (.invalidValue path
      s!"closed enum `{descriptor.fullName}` has unknown value {number}")
  return intJson number.toInt

private def requiredFieldByNumber
    (descriptor : MessageDescriptor) (number : Int32)
    (path : String) : JM FieldDescriptor := do
  let some field ← descriptor.findFieldByNumber number
    | throw (.invalidValue path
        s!"`{descriptor.fullName}` has no field {number}")
  return field

private def singularOrDefault
    (message : DynamicMessage) (field : FieldDescriptor) : JM Value := do
  let values ← liftReflection (message.presentValues field)
  match values.back? with
  | some value => return value
  | none => defaultValueForField field

private def isWrapperType (fullName : String) : Bool :=
  fullName == "google.protobuf.DoubleValue" ||
  fullName == "google.protobuf.FloatValue" ||
  fullName == "google.protobuf.Int64Value" ||
  fullName == "google.protobuf.UInt64Value" ||
  fullName == "google.protobuf.Int32Value" ||
  fullName == "google.protobuf.UInt32Value" ||
  fullName == "google.protobuf.BoolValue" ||
  fullName == "google.protobuf.StringValue" ||
  fullName == "google.protobuf.BytesValue"

private def floorDiv (value divisor : Int) : Int :=
  if value >= 0 then
    value / divisor
  else
    -((-value + divisor - 1) / divisor)

private def isLeapYear (year : Int) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

private def daysInMonth (year month : Int) : Int :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear year then 29 else 28
  | _ => 0

/-- Days since 1970-01-01. -/
private def daysFromCivil (year month day : Int) : Int :=
  let year := year - (if month <= 2 then 1 else 0)
  let era := floorDiv year 400
  let yearOfEra := year - era * 400
  let monthPrime := month + (if month > 2 then -3 else 9)
  let dayOfYear := (153 * monthPrime + 2) / 5 + day - 1
  let dayOfEra :=
    yearOfEra * 365 + yearOfEra / 4 - yearOfEra / 100 + dayOfYear
  era * 146097 + dayOfEra - 719468

private def civilFromDays (days : Int) : Int × Int × Int :=
  let z := days + 719468
  let era := floorDiv z 146097
  let dayOfEra := z - era * 146097
  let yearOfEra :=
    (dayOfEra - dayOfEra / 1460 + dayOfEra / 36524 -
      dayOfEra / 146096) / 365
  let year0 := yearOfEra + era * 400
  let dayOfYear :=
    dayOfEra - (365 * yearOfEra + yearOfEra / 4 - yearOfEra / 100)
  let monthPrime := (5 * dayOfYear + 2) / 153
  let day := dayOfYear - (153 * monthPrime + 2) / 5 + 1
  let month := monthPrime + (if monthPrime < 10 then 3 else -9)
  let year := year0 + (if month <= 2 then 1 else 0)
  (year, month, day)

private def zeroPad (width : Nat) (value : Nat) : String :=
  let text := value.repr
  String.ofList (List.replicate (width - text.length) '0') ++ text

private def decimalSlice?
    (text : String) (start length : Nat) : Option Nat :=
  (text.drop start |>.take length |>.toString).toNat?

private def parseFractionNanos
    (path fraction : String) : JM Int := do
  if fraction.isEmpty || fraction.length > 9 then
    throw (.invalidValue path
      "fractional seconds must contain between 1 and 9 digits")
  let some value := fraction.toNat?
    | throw (.invalidValue path "fractional seconds contain a non-digit")
  return Int.ofNat (value * 10 ^ (9 - fraction.length))

private def formatNanos (nanos : Nat) : String :=
  if nanos == 0 then
    ""
  else if nanos % 1000000 == 0 then
    "." ++ zeroPad 3 (nanos / 1000000)
  else if nanos % 1000 == 0 then
    "." ++ zeroPad 6 (nanos / 1000)
  else
    "." ++ zeroPad 9 nanos

private def timestampJson
    (message : DynamicMessage) (path : String) : JM Lean.Json := do
  let secondsField ← requiredFieldByNumber message.descriptor 1 path
  let nanosField ← requiredFieldByNumber message.descriptor 2 path
  let .int64 seconds ← singularOrDefault message secondsField
    | throw (.invalidValue path "Timestamp.seconds is not int64")
  let .int32 nanos ← singularOrDefault message nanosField
    | throw (.invalidValue path "Timestamp.nanos is not int32")
  let seconds := seconds.toInt
  let nanos := nanos.toInt
  if seconds < -62135596800 || seconds > 253402300799 then
    throw (.invalidValue path "Timestamp seconds are outside years 0001 through 9999")
  if nanos < 0 || nanos > 999999999 then
    throw (.invalidValue path "Timestamp nanos are outside [0, 999999999]")
  let days := floorDiv seconds 86400
  let secondOfDay := seconds - days * 86400
  let (year, month, day) := civilFromDays days
  let hour := secondOfDay / 3600
  let minute := (secondOfDay % 3600) / 60
  let second := secondOfDay % 60
  return .str <|
    zeroPad 4 year.toNat ++ "-" ++ zeroPad 2 month.toNat ++ "-" ++
    zeroPad 2 day.toNat ++ "T" ++ zeroPad 2 hour.toNat ++ ":" ++
    zeroPad 2 minute.toNat ++ ":" ++ zeroPad 2 second.toNat ++
    formatNanos nanos.toNat ++ "Z"

private def parseTimestampText
    (path text : String) : JM (Int × Int) := do
  if text.length < 20 then
    throw (.invalidValue path "Timestamp is shorter than RFC 3339 syntax")
  unless (text.drop 4 |>.take 1 |>.toString) == "-" &&
      (text.drop 7 |>.take 1 |>.toString) == "-" &&
      (text.drop 10 |>.take 1 |>.toString) == "T" &&
      (text.drop 13 |>.take 1 |>.toString) == ":" &&
      (text.drop 16 |>.take 1 |>.toString) == ":" do
    throw (.invalidValue path "Timestamp is not valid RFC 3339")
  let some year := decimalSlice? text 0 4
    | throw (.invalidValue path "Timestamp year is invalid")
  let some month := decimalSlice? text 5 2
    | throw (.invalidValue path "Timestamp month is invalid")
  let some day := decimalSlice? text 8 2
    | throw (.invalidValue path "Timestamp day is invalid")
  let some hour := decimalSlice? text 11 2
    | throw (.invalidValue path "Timestamp hour is invalid")
  let some minute := decimalSlice? text 14 2
    | throw (.invalidValue path "Timestamp minute is invalid")
  let some second := decimalSlice? text 17 2
    | throw (.invalidValue path "Timestamp second is invalid")
  let year := Int.ofNat year
  let month := Int.ofNat month
  let day := Int.ofNat day
  if year < 1 || year > 9999 || month < 1 || month > 12 ||
      day < 1 || day > daysInMonth year month ||
      hour > 23 || minute > 59 || second > 59 then
    throw (.invalidValue path "Timestamp contains an out-of-range date or time")
  let suffix := (text.drop 19).toString
  let (nanos, zone) ←
    if suffix.startsWith "." then
      let rest := (suffix.drop 1).toString
      let zoneIndex :=
        rest.toList.findIdx? fun c => c == 'Z' || c == '+' || c == '-'
      let some zoneIndex := zoneIndex
        | throw (.invalidValue path "Timestamp has no timezone")
      let fraction := (rest.take zoneIndex).toString
      let zone := (rest.drop zoneIndex).toString
      pure (← parseFractionNanos path fraction, zone)
    else
      pure (0, suffix)
  let offsetSeconds ←
    if zone == "Z" then
      pure 0
    else
      if zone.length != 6 ||
          !((zone.startsWith "+") || (zone.startsWith "-")) ||
          (zone.drop 3 |>.take 1 |>.toString) != ":" then
        throw (.invalidValue path "Timestamp timezone is invalid")
      let some zoneHour := decimalSlice? zone 1 2
        | throw (.invalidValue path "Timestamp timezone hour is invalid")
      let some zoneMinute := decimalSlice? zone 4 2
        | throw (.invalidValue path "Timestamp timezone minute is invalid")
      if zoneHour > 23 || zoneMinute > 59 then
        throw (.invalidValue path "Timestamp timezone is out of range")
      let magnitude := Int.ofNat (zoneHour * 3600 + zoneMinute * 60)
      pure (if zone.startsWith "-" then -magnitude else magnitude)
  let localSeconds :=
    daysFromCivil year month day * 86400 +
      Int.ofNat (hour * 3600 + minute * 60 + second)
  let seconds := localSeconds - offsetSeconds
  if seconds < -62135596800 || seconds > 253402300799 then
    throw (.invalidValue path "Timestamp normalizes outside years 0001 through 9999")
  return (seconds, nanos)

private def parseTimestamp
    (descriptor : MessageDescriptor) (path : String)
    (json : Lean.Json) : JM DynamicMessage := do
  let .str text := json
    | throw (.typeMismatch path "RFC 3339 string" (jsonKind json))
  let (seconds, nanos) ← parseTimestampText path text
  let secondsField ← requiredFieldByNumber descriptor 1 path
  let nanosField ← requiredFieldByNumber descriptor 2 path
  let message : DynamicMessage := { descriptor }
  let message ← liftReflection <|
    message.setSingular secondsField (.int64 (Int64.ofInt seconds))
  liftReflection <|
    message.setSingular nanosField (.int32 (Int32.ofInt nanos))

private def durationJson
    (message : DynamicMessage) (path : String) : JM Lean.Json := do
  let secondsField ← requiredFieldByNumber message.descriptor 1 path
  let nanosField ← requiredFieldByNumber message.descriptor 2 path
  let .int64 seconds ← singularOrDefault message secondsField
    | throw (.invalidValue path "Duration.seconds is not int64")
  let .int32 nanos ← singularOrDefault message nanosField
    | throw (.invalidValue path "Duration.nanos is not int32")
  let seconds := seconds.toInt
  let nanos := nanos.toInt
  if seconds < -315576000000 || seconds > 315576000000 then
    throw (.invalidValue path "Duration seconds are out of range")
  if nanos < -999999999 || nanos > 999999999 ||
      (seconds < 0 && nanos > 0) || (seconds > 0 && nanos < 0) then
    throw (.invalidValue path "Duration seconds and nanos have inconsistent signs")
  let negative := seconds < 0 || nanos < 0
  return .str <|
    (if negative then "-" else "") ++ seconds.natAbs.repr ++
    formatNanos nanos.natAbs ++ "s"

private def parseDurationText
    (path text : String) : JM (Int × Int) := do
  unless text.endsWith "s" do
    throw (.invalidValue path "Duration must end in `s`")
  let body := (text.dropEnd 1).toString
  let negative := body.startsWith "-"
  let unsigned := if negative then (body.drop 1).toString else body
  if unsigned.isEmpty then
    throw (.invalidValue path "Duration has no numeric value")
  let pieces := unsigned.splitOn "."
  if pieces.length > 2 then
    throw (.invalidValue path "Duration contains more than one decimal point")
  let wholeText := pieces[0]!
  let some whole := wholeText.toNat?
    | throw (.invalidValue path "Duration seconds are not decimal digits")
  let nanos ←
    match pieces[1]? with
    | none => pure 0
    | some fraction => parseFractionNanos path fraction
  let seconds := Int.ofNat whole
  let seconds := if negative then -seconds else seconds
  let nanos := if negative then -nanos else nanos
  if seconds < -315576000000 || seconds > 315576000000 then
    throw (.invalidValue path "Duration seconds are out of range")
  return (seconds, nanos)

private def parseDuration
    (descriptor : MessageDescriptor) (path : String)
    (json : Lean.Json) : JM DynamicMessage := do
  let .str text := json
    | throw (.typeMismatch path "duration string" (jsonKind json))
  let (seconds, nanos) ← parseDurationText path text
  let secondsField ← requiredFieldByNumber descriptor 1 path
  let nanosField ← requiredFieldByNumber descriptor 2 path
  let message : DynamicMessage := { descriptor }
  let message ← liftReflection <|
    message.setSingular secondsField (.int64 (Int64.ofInt seconds))
  liftReflection <|
    message.setSingular nanosField (.int32 (Int32.ofInt nanos))

private def snakePathToJson
    (path value : String) : JM String := do
  let mut out := ""
  let mut upperNext := false
  for c in value.toList do
    if c == '_' then
      if upperNext then
        throw (.invalidValue path
          s!"FieldMask path `{value}` cannot round trip through JSON")
      upperNext := true
    else if c.isUpper then
      throw (.invalidValue path
        s!"FieldMask path `{value}` contains an uppercase character")
    else if upperNext then
      if !c.isLower then
        throw (.invalidValue path
          s!"FieldMask path `{value}` cannot round trip through JSON")
      out := out.push c.toUpper
      upperNext := false
    else
      out := out.push c
  if upperNext then
    throw (.invalidValue path
      s!"FieldMask path `{value}` ends in an underscore")
  return out

private def jsonPathToSnake
    (path value : String) : JM String := do
  if value.contains '_' then
    throw (.invalidValue path
      s!"FieldMask JSON path `{value}` contains an underscore")
  let mut out := ""
  for c in value.toList do
    if c.isUpper then
      out := out.push '_' |>.push c.toLower
    else
      out := out.push c
  return out

private def fieldMaskJson
    (message : DynamicMessage) (path : String) : JM Lean.Json := do
  let pathsField ← requiredFieldByNumber message.descriptor 1 path
  let values ← liftReflection (message.presentValues pathsField)
  let mut paths := #[]
  for i in [:values.size] do
    let .string value := values[i]!
      | throw (.invalidValue (indexPath path i)
          "FieldMask.paths contains a non-string value")
    let some value := value.toString?
      | throw (.invalidValue (indexPath path i)
          "FieldMask.paths contains invalid UTF-8")
    paths := paths.push (← snakePathToJson (indexPath path i) value)
  return .str (String.intercalate "," paths.toList)

private def parseFieldMask
    (descriptor : MessageDescriptor) (path : String)
    (json : Lean.Json) : JM DynamicMessage := do
  let .str text := json
    | throw (.typeMismatch path "FieldMask string" (jsonKind json))
  let pathsField ← requiredFieldByNumber descriptor 1 path
  let pieces := if text.isEmpty then [] else text.splitOn ","
  let mut values := #[]
  for piece in pieces do
    values := values.push
      (.string (← jsonPathToSnake path piece))
  let message : DynamicMessage := { descriptor }
  liftReflection (message.setValues pathsField values)

private def checkRequiredFields
    (message : DynamicMessage) (path : String) : JM Unit := do
  for field in (← message.descriptor.fields) do
    if (← field.isRequired).getD false then
      let values ← liftReflection (message.presentValues field)
      if values.isEmpty then
        let name := (← field.name).getD field.fullName
        throw (.missingRequiredField path name)

mutual

private partial def encodeValue
    (value : Value) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  match value with
  | .int32 value => return intJson value.toInt
  | .int64 value => return .str value.toInt.repr
  | .uint32 value => return natJson value.toNat
  | .uint64 value => return .str value.toNat.repr
  | .bool value => return .bool value
  | .string value =>
      let some text := value.toString?
        | throw (.invalidValue path "protobuf string contains invalid UTF-8")
      return .str text
  | .bytes value => return .str (Protobuf.Base64.encode value)
  | .float value => return floatJson value.toFloat
  | .double value => return floatJson value
  | .enum descriptor number =>
      enumJson path descriptor number options
  | .message descriptor wire =>
      encodeMessage { descriptor, wire } path options remaining

private partial def encodeMapKey
    (value : Value) (path : String) : JM String := do
  match value with
  | .int32 value => return value.toInt.repr
  | .int64 value => return value.toInt.repr
  | .uint32 value => return value.toNat.repr
  | .uint64 value => return value.toNat.repr
  | .bool value => return if value then "true" else "false"
  | .string value =>
      let some text := value.toString?
        | throw (.invalidValue path "map key contains invalid UTF-8")
      return text
  | _ => throw (.invalidValue path "illegal protobuf map key type")

private partial def encodeMap
    (values : Array Value) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let mut object : Std.TreeMap.Raw String Lean.Json := {}
  for i in [:values.size] do
    let .message descriptor wire := values[i]!
      | throw (.invalidValue (indexPath path i)
          "map entry is not a message")
    let entry : DynamicMessage := { descriptor, wire }
    let some keyField ← descriptor.findFieldByNumber 1
      | throw (.invalidValue path "map entry has no key field")
    let some valueField ← descriptor.findFieldByNumber 2
      | throw (.invalidValue path "map entry has no value field")
    let keyValues ← liftReflection (entry.presentValues keyField)
    let key ←
      match keyValues.back? with
      | some key => pure key
      | none => defaultValueForField keyField
    let keyText ← encodeMapKey key (indexPath path i)
    let valueValues ← liftReflection (entry.presentValues valueField)
    let mapValue ←
      match valueValues.back? with
      | some value => pure value
      | none => defaultValueForField valueField
    let json ← encodeValue mapValue (childPath path keyText) options remaining
    object := object.insert keyText json
  return .obj object

private partial def encodeWrapper
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let field ← requiredFieldByNumber message.descriptor 1 path
  encodeValue (← singularOrDefault message field) path options remaining

private partial def encodeStruct
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let field ← requiredFieldByNumber message.descriptor 1 path
  let values ← liftReflection (message.presentValues field)
  encodeMap values path options remaining

private partial def encodeListValue
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let field ← requiredFieldByNumber message.descriptor 1 path
  let values ← liftReflection (message.presentValues field)
  let mut out := #[]
  for i in [:values.size] do
    out := out.push
      (← encodeValue values[i]! (indexPath path i) options remaining)
  return .arr out

private partial def encodeGoogleValue
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  for number in [1:7] do
    let field ← requiredFieldByNumber message.descriptor
      (Int32.ofInt number) path
    let values ← liftReflection (message.presentValues field)
    if let some value := values.back? then
      if number == 1 then
        return .null
      if number == 2 then
        let .double numberValue := value
          | throw (.invalidValue path
              "google.protobuf.Value.number_value is not a double")
        unless numberValue.isFinite do
          throw (.invalidValue path
            "google.protobuf.Value cannot represent a non-finite JSON number")
      return ← encodeValue value path options remaining
  throw (.invalidValue path
    "google.protobuf.Value has no active kind")

private partial def hasCustomJsonRepresentation (fullName : String) : Bool :=
  isWrapperType fullName ||
  fullName == "google.protobuf.Any" ||
  fullName == "google.protobuf.Timestamp" ||
  fullName == "google.protobuf.Duration" ||
  fullName == "google.protobuf.FieldMask" ||
  fullName == "google.protobuf.Struct" ||
  fullName == "google.protobuf.Value" ||
  fullName == "google.protobuf.ListValue"

private partial def encodeAny
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let typeUrlField ← requiredFieldByNumber message.descriptor 1 path
  let valueField ← requiredFieldByNumber message.descriptor 2 path
  let .string rawTypeUrl ← singularOrDefault message typeUrlField
    | throw (.invalidValue path "Any.type_url is not a string")
  let some typeUrl := rawTypeUrl.toString?
    | throw (.invalidValue path "Any.type_url contains invalid UTF-8")
  if typeUrl.isEmpty then
    return .obj {}
  unless typeUrl.contains '/' do
    throw (.invalidValue path "Any.type_url is not URL-shaped")
  let some typeName := (typeUrl.splitOn "/").getLast?
    | throw (.invalidValue path "Any.type_url has no type name")
  let some resolver := options.types
    | throw (.unresolvedType typeName)
  let some descriptor ← resolver.findMessageByName typeName
    | throw (.unresolvedType typeName)
  let .bytes bytes ← singularOrDefault message valueField
    | throw (.invalidValue path "Any.value is not bytes")
  let embedded ←
    liftExcept ((DynamicMessage.decode descriptor bytes).mapError Error.reflection)
  let embeddedJson ← encodeMessage embedded path options remaining
  let mut object : Std.TreeMap.Raw String Lean.Json := {}
  object := object.insert "@type" (.str typeUrl)
  if hasCustomJsonRepresentation descriptor.fullName then
    object := object.insert "value" embeddedJson
  else
    let .obj fields := embeddedJson
      | throw (.invalidValue path
          s!"ordinary Any payload `{descriptor.fullName}` did not encode as an object")
    object := fields.foldl (init := object) fun object name value =>
      object.insert name value
  return .obj object

private partial def encodeField?
    (message : DynamicMessage) (field : FieldDescriptor) (path : String)
    (options : PrintOptions) (remaining : Nat) :
    JM (Option (String × Lean.Json)) := do
  let name ← outputFieldName field options
  let fieldPath := childPath path name
  let values ← liftReflection (message.presentValues field)
  let repeated := (← field.isRepeated).getD false
  if repeated then
    if values.isEmpty && !options.emitFieldsWithoutPresence then
      return none
    let json ←
      if (← field.isMap).getD false then
        encodeMap values fieldPath options remaining
      else
        let mut out := #[]
        for i in [:values.size] do
          out := out.push
            (← encodeValue values[i]! (indexPath fieldPath i) options remaining)
        pure (.arr out)
    return some (name, json)
  let hasPresence := (← field.hasPresence).getD true
  let value ←
    match values.back? with
    | some value => pure value
    | none =>
        if !hasPresence && options.emitFieldsWithoutPresence then
          defaultValueForField field
        else
          return none
  if !hasPresence && !options.emitFieldsWithoutPresence &&
      (← valueIsDefault value) then
    return none
  return some (name, ← encodeValue value fieldPath options remaining)

private partial def presentExtensionFields
    (message : DynamicMessage) (resolver : ExtensionResolver) :
    JM (Array FieldDescriptor) := do
  let ordinary ← message.descriptor.fields
  let mut ordinaryNumbers : Std.HashSet Nat := {}
  for field in ordinary do
    if let some number ← field.number then
      if number > 0 then
        ordinaryNumbers := ordinaryNumbers.insert number.toInt.toNat
  let mut seen : Std.HashSet Nat := {}
  let mut out := #[]
  for record in message.wire.records do
    let number := record.fieldNum
    if ordinaryNumbers.contains number || seen.contains number ||
        number > 0x7fffffff then
      continue
    seen := seen.insert number
    let signed := Int32.ofInt (Int.ofNat number)
    if let some field ←
        resolver.findExtensionByNumber message.descriptor signed then
      out := out.push field
  return out.qsort fun a b =>
    a.fullName < b.fullName

private partial def encodeRegularMessage
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let mut fields ← message.descriptor.fields
  if let some resolver := options.extensions then
    fields := fields ++ (← presentExtensionFields message resolver)
  let mut object : Std.TreeMap.Raw String Lean.Json := {}
  for field in fields do
    if let some (name, value) ←
        encodeField? message field path options remaining then
      object := object.insert name value
  return .obj object

private partial def encodeMessage
    (message : DynamicMessage) (path : String) (options : PrintOptions)
    (remaining : Nat) : JM Lean.Json := do
  let remaining ← checkDepth path remaining
  unless options.allowPartial do
    checkRequiredFields message path
  match message.descriptor.fullName with
  | "google.protobuf.Timestamp" => timestampJson message path
  | "google.protobuf.Duration" => durationJson message path
  | "google.protobuf.FieldMask" => fieldMaskJson message path
  | "google.protobuf.Struct" =>
      encodeStruct message path options remaining
  | "google.protobuf.Value" =>
      encodeGoogleValue message path options remaining
  | "google.protobuf.ListValue" =>
      encodeListValue message path options remaining
  | "google.protobuf.Any" =>
      encodeAny message path options remaining
  | fullName =>
      if isWrapperType fullName then
        encodeWrapper message path options remaining
      else
        encodeRegularMessage message path options remaining

end

private def findOrdinaryFieldByJsonName
    (descriptor : MessageDescriptor) (name : String) :
    JM (Option FieldDescriptor) := do
  let fields ← descriptor.fields
  let mut found : Option FieldDescriptor := none
  for field in fields do
    let protoName ← field.name
    let jsonName ← field.jsonName
    if protoName == some name || jsonName == some name then
      if found.isSome && found != some field then
        throw (.invalidValue "$"
          s!"JSON name `{name}` is ambiguous in `{descriptor.fullName}`")
      found := some field
  return found

private def findInputField
    (descriptor : MessageDescriptor) (name : String)
    (options : ParseOptions) : JM (Option FieldDescriptor) := do
  if name.startsWith "[" && name.endsWith "]" then
    let fullName := (name.drop 1 |>.dropEnd 1).toString
    let some resolver := options.extensions | return none
    return ← resolver.findExtensionByName descriptor fullName
  findOrdinaryFieldByJsonName descriptor name

private def parseMapKey
    (field : FieldDescriptor) (path text : String) : JM Value := do
  match ← fieldType field with
  | .TYPE_STRING => return .string text
  | .TYPE_BOOL =>
      match text with
      | "true" => return .bool true
      | "false" => return .bool false
      | _ => throw (.invalidValue path s!"`{text}` is not a boolean map key")
  | .TYPE_INT32 | .TYPE_SINT32 | .TYPE_SFIXED32 =>
      let some value := text.toInt?
        | throw (.invalidValue path s!"`{text}` is not an integer map key")
      let value ← requireRange path "int32" value (-2147483648) 2147483647
      return .int32 (Int32.ofInt value)
  | .TYPE_INT64 | .TYPE_SINT64 | .TYPE_SFIXED64 =>
      let some value := text.toInt?
        | throw (.invalidValue path s!"`{text}` is not an integer map key")
      let value ← requireRange path "int64" value
        (-9223372036854775808) 9223372036854775807
      return .int64 (Int64.ofInt value)
  | .TYPE_UINT32 | .TYPE_FIXED32 =>
      let some value := text.toNat?
        | throw (.invalidValue path s!"`{text}` is not an unsigned map key")
      if value > 4294967295 then
        throw (.invalidValue path s!"{value} is outside the uint32 range")
      return .uint32 (UInt32.ofNat value)
  | .TYPE_UINT64 | .TYPE_FIXED64 =>
      let some value := text.toNat?
        | throw (.invalidValue path s!"`{text}` is not an unsigned map key")
      if value > 18446744073709551615 then
        throw (.invalidValue path s!"{value} is outside the uint64 range")
      return .uint64 (UInt64.ofNat value)
  | _ => throw (.invalidValue path "illegal protobuf map key type")

private def parseEnum
    (field : FieldDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) : JM (Option Value) := do
  let some descriptor ← field.enumType
    | throw (.reflection
        (.unresolvedEnumType ((← fieldProto field).type_name.getD "")))
  match json with
  | .str name =>
      if let some value ← descriptor.findValueByName name then
        let some number ← value.number
          | throw (.reflection (.staleDescriptor descriptor.fullName))
        return some (.enum descriptor number)
      if options.discardUnknownFields then
        return none
      throw (.invalidValue path
        s!"unknown value `{name}` for enum `{descriptor.fullName}`")
  | .num _ =>
      let value ← parseIntegral path json
      let value ← requireRange path "enum" value (-2147483648) 2147483647
      let number := Int32.ofInt value
      if (← descriptor.isClosed).getD false &&
          (← descriptor.findValueByNumber number).isNone then
        throw (.invalidValue path
          s!"unknown numeric value {number} for closed enum `{descriptor.fullName}`")
      return some (.enum descriptor number)
  | _ => throw (.typeMismatch path "enum name or integer" (jsonKind json))

mutual

private partial def parseSingular
    (field : FieldDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM (Option Value) := do
  let type ← fieldType field
  if json.isNull then
    if type == .TYPE_ENUM then
      if let some enum ← field.enumType then
        if enum.fullName == "google.protobuf.NullValue" then
          return some (.enum enum 0)
    if type == .TYPE_MESSAGE then
      if let some message ← field.messageType then
        if message.fullName == "google.protobuf.Value" then
          let parsed ← parseMessage message path json options remaining
          return some (.message parsed.descriptor parsed.wire)
    return none
  match type with
  | .TYPE_DOUBLE => return some (.double (← parseFloat path json))
  | .TYPE_FLOAT =>
      let parsed ← parseFloat path json
      let value := parsed.toFloat32
      if parsed.isFinite && !value.isFinite then
        throw (.invalidValue path "float value is out of range")
      return some (.float value)
  | .TYPE_INT32 | .TYPE_SFIXED32 | .TYPE_SINT32 =>
      let value ← parseIntegral path json
      let value ← requireRange path "int32" value (-2147483648) 2147483647
      return some (.int32 (Int32.ofInt value))
  | .TYPE_UINT32 | .TYPE_FIXED32 =>
      let value ← parseIntegral path json
      let value ← requireRange path "uint32" value 0 4294967295
      return some (.uint32 (UInt32.ofNat value.toNat))
  | .TYPE_INT64 | .TYPE_SFIXED64 | .TYPE_SINT64 =>
      let value ← parseIntegral path json
      let value ← requireRange path "int64" value
        (-9223372036854775808) 9223372036854775807
      return some (.int64 (Int64.ofInt value))
  | .TYPE_UINT64 | .TYPE_FIXED64 =>
      let value ← parseIntegral path json
      let value ← requireRange path "uint64" value 0
        18446744073709551615
      return some (.uint64 (UInt64.ofNat value.toNat))
  | .TYPE_BOOL =>
      let .bool value := json
        | throw (.typeMismatch path "boolean" (jsonKind json))
      return some (.bool value)
  | .TYPE_STRING =>
      let .str value := json
        | throw (.typeMismatch path "string" (jsonKind json))
      return some (.string value)
  | .TYPE_BYTES =>
      let .str value := json
        | throw (.typeMismatch path "base64 string" (jsonKind json))
      return some (.bytes (← decodeJsonBase64 path value))
  | .TYPE_ENUM => parseEnum field path json options
  | .TYPE_MESSAGE | .TYPE_GROUP =>
      let some descriptor ← field.messageType
        | throw (.reflection
            (.unresolvedMessageType ((← fieldProto field).type_name.getD "")))
      let parsed ← parseMessage descriptor path json options remaining
      return some (.message descriptor parsed.wire)
  | .«Unknown.Value» number =>
      throw (.invalidValue path s!"unknown protobuf field type {number}")

private partial def parseRepeated
    (message : DynamicMessage) (field : FieldDescriptor) (path : String)
    (json : Lean.Json) (options : ParseOptions) (remaining : Nat) :
    JM DynamicMessage := do
  if json.isNull then
    return ← liftReflection (message.clearField field)
  let .arr values := json
    | throw (.typeMismatch path "array" (jsonKind json))
  let mut parsed := #[]
  for i in [:values.size] do
    let itemPath := indexPath path i
    if values[i]!.isNull then
      let type ← fieldType field
      let permitsNull ←
        if type == .TYPE_ENUM then
          let descriptor? ← field.enumType
          pure (descriptor?.any fun descriptor =>
            descriptor.fullName == "google.protobuf.NullValue")
        else if type == .TYPE_MESSAGE then
          let descriptor? ← field.messageType
          pure (descriptor?.any fun descriptor =>
            descriptor.fullName == "google.protobuf.Value")
        else
          pure false
      unless permitsNull do
        throw (.invalidValue itemPath
          "null is not allowed inside a repeated field")
    if let some value ←
        parseSingular field itemPath values[i]! options remaining then
      parsed := parsed.push value
  liftReflection (message.setValues field parsed)

private partial def parseMap
    (message : DynamicMessage) (field : FieldDescriptor) (path : String)
    (json : Lean.Json) (options : ParseOptions) (remaining : Nat) :
    JM DynamicMessage := do
  if json.isNull then
    return ← liftReflection (message.clearField field)
  let .obj object := json
    | throw (.typeMismatch path "object" (jsonKind json))
  let some entryDescriptor ← field.messageType
    | throw (.invalidValue path "map field has no entry descriptor")
  let some keyField ← entryDescriptor.findFieldByNumber 1
    | throw (.invalidValue path "map entry has no key field")
  let some valueField ← entryDescriptor.findFieldByNumber 2
    | throw (.invalidValue path "map entry has no value field")
  let entries ← object.foldlM (init := #[]) fun entries key item => do
    let itemPath := childPath path key
    let keyValue ← parseMapKey keyField itemPath key
    if item.isNull then
      let type ← fieldType valueField
      let permitsNull ←
        if type == .TYPE_ENUM then
          let descriptor? ← valueField.enumType
          pure (descriptor?.any fun descriptor =>
            descriptor.fullName == "google.protobuf.NullValue")
        else if type == .TYPE_MESSAGE then
          let descriptor? ← valueField.messageType
          pure (descriptor?.any fun descriptor =>
            descriptor.fullName == "google.protobuf.Value")
        else
          pure false
      unless permitsNull do
        throw (.invalidValue itemPath "null is not allowed as a map value")
    let some value ←
        parseSingular valueField itemPath item options remaining
      | return entries
    let entry : DynamicMessage := { descriptor := entryDescriptor }
    let entry ← liftReflection (entry.setSingular keyField keyValue)
    let entry ← liftReflection (entry.setSingular valueField value)
    return entries.push (.message entryDescriptor entry.wire)
  liftReflection (message.setValues field entries)

private partial def parseWrapper
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let message : DynamicMessage := { descriptor }
  if json.isNull then
    return message
  let field ← requiredFieldByNumber descriptor 1 path
  let some value ← parseSingular field path json options remaining
    | return message
  liftReflection (message.setSingular field value)

private partial def parseStruct
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let field ← requiredFieldByNumber descriptor 1 path
  parseMap { descriptor } field path json options remaining

private partial def parseListValue
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let field ← requiredFieldByNumber descriptor 1 path
  parseRepeated { descriptor } field path json options remaining

private partial def parseGoogleValue
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let (number, value) ←
    match json with
    | .null =>
        let field ← requiredFieldByNumber descriptor 1 path
        let some enum ← field.enumType
          | throw (.invalidValue path "Value.null_value has no enum descriptor")
        pure (1, .enum enum 0)
    | .num number =>
        let value := number.toFloat
        unless value.isFinite do
          throw (.invalidValue path
            "google.protobuf.Value number is outside the double range")
        pure (2, .double value)
    | .str value => pure (3, .string value)
    | .bool value => pure (4, .bool value)
    | .obj _ =>
        let field ← requiredFieldByNumber descriptor 5 path
        let some nestedDescriptor ← field.messageType
          | throw (.invalidValue path "Value.struct_value has no message descriptor")
        let nested ← parseMessage nestedDescriptor path json options remaining
        pure (5, .message nestedDescriptor nested.wire)
    | .arr _ =>
        let field ← requiredFieldByNumber descriptor 6 path
        let some nestedDescriptor ← field.messageType
          | throw (.invalidValue path "Value.list_value has no message descriptor")
        let nested ← parseMessage nestedDescriptor path json options remaining
        pure (6, .message nestedDescriptor nested.wire)
  let field ← requiredFieldByNumber descriptor (Int32.ofInt number) path
  liftReflection (({ descriptor } : DynamicMessage).setSingular field value)

private partial def parseAny
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let .obj object := json
    | throw (.typeMismatch path "Any object" (jsonKind json))
  let some typeJson := object.get? "@type"
    | if object.isEmpty then
        return { descriptor }
      else
        throw (.invalidValue path "Any object has no `@type` field")
  let .str typeUrl := typeJson
    | throw (.typeMismatch (childPath path "@type") "string" (jsonKind typeJson))
  unless typeUrl.contains '/' do
    throw (.invalidValue path "Any.type_url is not URL-shaped")
  let some typeName := (typeUrl.splitOn "/").getLast?
    | throw (.invalidValue path "Any.type_url has no type name")
  if typeName.isEmpty then
    throw (.invalidValue path "Any.type_url has an empty type name")
  let some resolver := options.types
    | throw (.unresolvedType typeName)
  let some embeddedDescriptor ← resolver.findMessageByName typeName
    | throw (.unresolvedType typeName)
  let embeddedJson ←
    if hasCustomJsonRepresentation embeddedDescriptor.fullName then
      let some value := object.get? "value"
        | throw (.invalidValue path
            "Any containing a well-known type has no `value` field")
      if !options.discardUnknownFields then
        object.foldlM (init := ()) fun _ name _ => do
          unless name == "@type" || name == "value" do
            throw (.unknownField path name)
      pure value
    else
      let fields : Std.TreeMap.Raw String Lean.Json :=
        object.foldl (init := {}) fun fields name value =>
        if name == "@type" then fields else fields.insert name value
      pure (.obj fields)
  let embedded ←
    parseMessage embeddedDescriptor path embeddedJson options remaining
  let bytes ←
    liftExcept ((DynamicMessage.encode embedded).mapError Error.reflection)
  let typeUrlField ← requiredFieldByNumber descriptor 1 path
  let valueField ← requiredFieldByNumber descriptor 2 path
  let message : DynamicMessage := { descriptor }
  let message ← liftReflection <|
    message.setSingular typeUrlField (.string typeUrl)
  liftReflection <|
    message.setSingular valueField (.bytes bytes)

private partial def parseRegularMessage
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let .obj object := json
    | throw (.typeMismatch path "object" (jsonKind json))
  let initial : DynamicMessage := { descriptor }
  let (_, _, message) ← object.foldlM
      (init := (({} : Std.HashSet String),
        ({} : Std.HashMap Nat String), initial))
      fun (seen, oneofs, message) name value => do
        let some field ← findInputField descriptor name options
          | if options.discardUnknownFields then
              return (seen, oneofs, message)
            else
              throw (.unknownField path name)
        if seen.contains field.fullName then
          throw (.duplicateField path name)
        let seen := seen.insert field.fullName
        let proto ← fieldProto field
        let mut oneofs := oneofs
        if let some index := proto.oneof_index then
          let type ← fieldType field
          let nullActivates ←
            if type == .TYPE_ENUM then
              let descriptor? ← field.enumType
              pure (descriptor?.any fun descriptor =>
                descriptor.fullName == "google.protobuf.NullValue")
            else if type == .TYPE_MESSAGE then
              let descriptor? ← field.messageType
              pure (descriptor?.any fun descriptor =>
                descriptor.fullName == "google.protobuf.Value")
            else
              pure false
          if value.isNull && !nullActivates then
            pure ()
          else
            let index := index.toInt.toNat
            if let some previous := oneofs[index]? then
              if previous != field.fullName then
                throw (.duplicateField path name)
            oneofs := oneofs.insert index field.fullName
        let fieldPath := childPath path name
        let message ←
          if (← field.isMap).getD false then
            parseMap message field fieldPath value options remaining
          else if (← field.isRepeated).getD false then
            parseRepeated message field fieldPath value options remaining
          else
            match ← parseSingular field fieldPath value options remaining with
            | none => liftReflection (message.clearField field)
            | some parsed => liftReflection (message.setSingular field parsed)
        return (seen, oneofs, message)
  return message

private partial def parseMessage
    (descriptor : MessageDescriptor) (path : String) (json : Lean.Json)
    (options : ParseOptions) (remaining : Nat) : JM DynamicMessage := do
  let remaining ← checkDepth path remaining
  let message ←
    match descriptor.fullName with
    | "google.protobuf.Timestamp" => parseTimestamp descriptor path json
    | "google.protobuf.Duration" => parseDuration descriptor path json
    | "google.protobuf.FieldMask" => parseFieldMask descriptor path json
    | "google.protobuf.Struct" =>
        parseStruct descriptor path json options remaining
    | "google.protobuf.Value" =>
        parseGoogleValue descriptor path json options remaining
    | "google.protobuf.ListValue" =>
        parseListValue descriptor path json options remaining
    | "google.protobuf.Any" =>
        parseAny descriptor path json options remaining
    | fullName =>
        if isWrapperType fullName then
          parseWrapper descriptor path json options remaining
        else
          parseRegularMessage descriptor path json options remaining
  unless options.allowPartial do
    checkRequiredFields message path
  return message

end

def dynamicToJson
    (message : DynamicMessage) (options : PrintOptions := {}) :
    IO (Except Error Lean.Json) :=
  (encodeMessage message "$" options options.recursionLimit).run

def dynamicToJsonString
    (message : DynamicMessage) (options : PrintOptions := {}) :
    IO (Except Error String) := do
  return (← dynamicToJson message options).map fun json =>
    if options.pretty then json.pretty options.lineWidth else json.compress

def dynamicOfJson
    (descriptor : MessageDescriptor) (json : Lean.Json)
    (options : ParseOptions := {}) :
    IO (Except Error DynamicMessage) :=
  (parseMessage descriptor "$" json options options.recursionLimit).run

private def dropJsonWhitespace : List Char → List Char
  | ' ' :: rest => dropJsonWhitespace rest
  | '\t' :: rest => dropJsonWhitespace rest
  | '\r' :: rest => dropJsonWhitespace rest
  | '\n' :: rest => dropJsonWhitespace rest
  | rest => rest

private def jsonHexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

private def jsonHexQuad
    (a b c d : Char) : Except String Nat := do
  let some a := jsonHexDigit? a | throw "invalid JSON Unicode escape"
  let some b := jsonHexDigit? b | throw "invalid JSON Unicode escape"
  let some c := jsonHexDigit? c | throw "invalid JSON Unicode escape"
  let some d := jsonHexDigit? d | throw "invalid JSON Unicode escape"
  return (a <<< 12) ||| (b <<< 8) ||| (c <<< 4) ||| d

private partial def scanJsonString
    (input : List Char) (reversed : List Char := ['"']) :
    Except String (String × List Char) :=
  match input with
  | [] => .error "unterminated JSON string"
  | '"' :: rest =>
      .ok (String.ofList (('"' :: reversed).reverse), rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let codeUnit ← jsonHexQuad a b c d
      let first := ['\\', 'u', a, b, c, d]
      if 0xd800 ≤ codeUnit && codeUnit ≤ 0xdbff then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: rest => do
            let low ← jsonHexQuad e f g h
            unless 0xdc00 ≤ low && low ≤ 0xdfff do
              throw "high surrogate is not followed by a low surrogate"
            let second := ['\\', 'u', e, f, g, h]
            scanJsonString rest ((first ++ second).reverse ++ reversed)
        | _ => throw "unpaired high surrogate in JSON string"
      else if 0xdc00 ≤ codeUnit && codeUnit ≤ 0xdfff then
        throw "unpaired low surrogate in JSON string"
      else
        scanJsonString rest (first.reverse ++ reversed)
  | '\\' :: escaped :: rest =>
      scanJsonString rest (escaped :: '\\' :: reversed)
  | '\\' :: [] => .error "unterminated JSON escape"
  | c :: rest => scanJsonString rest (c :: reversed)

private def decodeJsonKey (token : String) : Except String String := do
  match Lean.Json.parse token with
  | .ok (.str key) => return key
  | .ok _ => throw "object key is not a string"
  | .error detail => throw detail

mutual

private partial def scanJsonValue (input : List Char) :
    Except String (List Char) := do
  match dropJsonWhitespace input with
  | [] => throw "missing JSON value"
  | '{' :: rest => scanJsonObject rest
  | '[' :: rest => scanJsonArray rest
  | '"' :: rest =>
      let (_, rest) ← scanJsonString rest
      return rest
  | input =>
      let rest := input.dropWhile fun c =>
        c != ',' && c != ']' && c != '}' &&
          c != ' ' && c != '\t' && c != '\r' && c != '\n'
      if rest.length == input.length then
        throw "missing JSON value"
      return rest

private partial def scanJsonObject (input : List Char) :
    Except String (List Char) := do
  let rec loop (input : List Char) (seen : Std.HashSet String) :
      Except String (List Char) := do
    match dropJsonWhitespace input with
    | '}' :: rest => return rest
    | '"' :: rest =>
        let (token, rest) ← scanJsonString rest
        let key ← decodeJsonKey token
        if seen.contains key then
          throw s!"duplicate JSON object key `{key}`"
        let seen := seen.insert key
        let rest := dropJsonWhitespace rest
        let ':' :: rest := rest
          | throw "missing colon after JSON object key"
        let rest ← scanJsonValue rest
        match dropJsonWhitespace rest with
        | ',' :: rest => loop rest seen
        | '}' :: rest => return rest
        | _ => throw "missing comma or closing brace in JSON object"
    | _ => throw "JSON object key is not a string"
  loop input {}

private partial def scanJsonArray (input : List Char) :
    Except String (List Char) := do
  let rec loop (input : List Char) : Except String (List Char) := do
    match dropJsonWhitespace input with
    | ']' :: rest => return rest
    | input =>
        let rest ← scanJsonValue input
        match dropJsonWhitespace rest with
        | ',' :: rest => loop rest
        | ']' :: rest => return rest
        | _ => throw "missing comma or closing bracket in JSON array"
  loop input

end

private def checkDuplicateJsonKeys (text : String) : Except String Unit := do
  let rest ← scanJsonValue text.toList
  unless (dropJsonWhitespace rest).isEmpty do
    throw "trailing content after JSON value"

def dynamicOfJsonString
    (descriptor : MessageDescriptor) (text : String)
    (options : ParseOptions := {}) :
    IO (Except Error DynamicMessage) := do
  match Lean.Json.parse text with
  | .error detail => return .error (.invalidJson detail)
  | .ok json =>
      match checkDuplicateJsonKeys text with
      | .error detail => return .error (.invalidJson detail)
      | .ok () => dynamicOfJson descriptor json options

def toJson
    (value : α) [ReflectMessage α] (options : PrintOptions := {}) :
    IO (Except Error Lean.Json) := do
  match DynamicMessage.ofStatic value with
  | .error error => return .error (.reflection error)
  | .ok message => dynamicToJson message options

def toJsonString
    (value : α) [ReflectMessage α] (options : PrintOptions := {}) :
    IO (Except Error String) := do
  match DynamicMessage.ofStatic value with
  | .error error => return .error (.reflection error)
  | .ok message => dynamicToJsonString message options

def fromJson
    (json : Lean.Json) (α : Type) [ReflectMessage α]
    (options : ParseOptions := {}) : IO (Except Error α) := do
  match ← dynamicOfJson (messageDescriptor α) json options with
  | .error error => return .error error
  | .ok message =>
      return (message.toStatic α).mapError Error.reflection

def fromJsonString
    (text : String) (α : Type) [ReflectMessage α]
    (options : ParseOptions := {}) : IO (Except Error α) := do
  match ← dynamicOfJsonString (messageDescriptor α) text options with
  | .error error => return .error error
  | .ok message =>
      return (message.toStatic α).mapError Error.reflection

end Protobuf.Json
