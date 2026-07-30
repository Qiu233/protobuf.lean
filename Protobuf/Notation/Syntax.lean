module

public meta import Lean.Parser
public meta import Lean.PrettyPrinter.Formatter
public meta import Lean.PrettyPrinter.Parenthesizer
public import Lean.Syntax

public section

namespace Protobuf.Notation

/--
Decode the unsigned part of a protobuf `intLit`.

Protobuf deliberately uses C-style leading-zero octal, whereas Lean treats
`077` as decimal and uses `0o`/`0b` prefixes for octal/binary.  Keep this
conversion independent of Lean's `TSyntax.getNat`: parser antiquotations can
inject an already-built `num` node and therefore bypass lexical checks.
-/
private def protobufDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then
    some (n - 48)
  else if 65 ≤ n && n ≤ 70 then
    some (n - 65 + 10)
  else if 97 ≤ n && n ≤ 102 then
    some (n - 97 + 10)
  else
    none

private def parseProtobufDigits?
    (radix : Nat) (digits : List Char) : Option Nat := do
  if digits.isEmpty then
    none
  else
    digits.foldlM (init := 0) fun value c => do
      let digit ← protobufDigitValue? c
      if digit < radix then
        some (value * radix + digit)
      else
        none

def parseProtobufIntLiteralText? (text : String) : Option Nat :=
  match text.toList with
  | [] => none
  | ['0'] => some 0
  | '0' :: marker :: digits =>
      if marker == 'x' || marker == 'X' then
        parseProtobufDigits? 16 digits
      else
        parseProtobufDigits? 8 (marker :: digits)
  | first :: rest =>
      if '1' ≤ first && first ≤ '9' then
        parseProtobufDigits? 10 (first :: rest)
      else
        none

def protobufIntLiteralValue? (stx : Lean.TSyntax `num) : Option Nat := do
  let text ← stx.raw[0].isIdOrAtom?
  parseProtobufIntLiteralText? text

/--
Validate and convert a protobuf integer literal to a decimal Lean `num` node.

The original source position is retained for diagnostics, but the token text is
decimal so every existing downstream `getNat` and generated Lean term observes
protobuf's radix semantics.
-/
def canonicalProtobufIntLiteral?
    (stx : Lean.TSyntax `num) : Option (Lean.TSyntax `num) := do
  let value ← protobufIntLiteralValue? stx
  pure (Lean.Syntax.mkNatLit value stx.raw.getHeadInfo)

private meta def parseProtobufIntLiteralTextForParser?
    (text : String) : Option Nat :=
  let digitValue? (c : Char) : Option Nat :=
    let n := c.toNat
    if 48 ≤ n && n ≤ 57 then
      some (n - 48)
    else if 65 ≤ n && n ≤ 70 then
      some (n - 65 + 10)
    else if 97 ≤ n && n ≤ 102 then
      some (n - 97 + 10)
    else
      none
  let parseDigits? (radix : Nat) (digits : List Char) : Option Nat := do
    if digits.isEmpty then
      none
    else
      digits.foldlM (init := 0) fun value c => do
        let digit ← digitValue? c
        if digit < radix then
          some (value * radix + digit)
        else
          none
  match text.toList with
  | [] => none
  | ['0'] => some 0
  | '0' :: marker :: digits =>
      if marker == 'x' || marker == 'X' then
        parseDigits? 16 digits
      else
        parseDigits? 8 (marker :: digits)
  | first :: rest =>
      if '1' ≤ first && first ≤ '9' then
        parseDigits? 10 (first :: rest)
      else
        none

private meta def isProtobufIntLiteralForParser
    (stx : Lean.Syntax) : Bool :=
  match stx[0].isIdOrAtom? with
  | some text => (parseProtobufIntLiteralTextForParser? text).isSome
  | none => false

@[run_parser_attribute_hooks]
meta def protobufIntLit : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot
    (Lean.Parser.mkAntiquot "num" Lean.numLitKind)
    (Lean.Parser.numLitNoAntiquot >>
      Lean.Parser.checkStackTop
        isProtobufIntLiteralForParser
        "expected a protobuf integer literal (decimal, leading-zero octal, or 0x hexadecimal)")

/--
Compatibility parser used only while elaborating syntax quotations in the
descriptor frontends.  Protoc descriptors never carry a leading `+`, but an
existing defensive branch still quotes that shape.  Keeping the branch
quotation-only lets those modules compile without making `+1` legal source
text; consumers reject a forged plus node again.
-/
private meta def protobufQuotationOnlyPlusFn : Lean.Parser.ParserFn := fun c s =>
  let parsed := (Lean.Parser.symbolNoAntiquot "+").fn c s
  if parsed.hasError then
    parsed
  else if c.quotDepth > 0 || c.get parsed.pos == '$' then
    parsed
  else
    s.mkUnexpectedError
      "protobuf numeric literals do not allow a leading plus sign"

meta def protobufQuotationOnlyPlus : Lean.Parser.Parser := {
  info := (Lean.Parser.symbolNoAntiquot "+").info
  fn := protobufQuotationOnlyPlusFn
}

open Lean.PrettyPrinter Lean.PrettyPrinter.Formatter in
@[combinator_formatter protobufQuotationOnlyPlus]
meta def protobufQuotationOnlyPlus.formatter : Formatter :=
  symbolNoAntiquot.formatter "+"

open Lean.PrettyPrinter Lean.PrettyPrinter.Parenthesizer in
@[combinator_parenthesizer protobufQuotationOnlyPlus]
meta def protobufQuotationOnlyPlus.parenthesizer : Parenthesizer :=
  symbolNoAntiquot.parenthesizer "+"

private meta def isProtobufDecimalDigit (c : Char) : Bool :=
  let n := c.toNat
  48 ≤ n && n ≤ 57

private meta def takeProtobufDecimalDigitsFn : Lean.Parser.ParserFn :=
  Lean.Parser.takeWhileFn isProtobufDecimalDigit

private meta def requireProtobufDecimalDigitsFn : Lean.Parser.ParserFn := fun c s =>
  let start := s.pos
  let s := takeProtobufDecimalDigitsFn c s
  if s.pos == start then
    s.mkUnexpectedError
      "expected decimal digits in protobuf floating-point literal"
  else
    s

private meta def consumeProtobufFloatCharFn : Lean.Parser.ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s.mkEOIError
  else
    s.next' c i h

private meta def parseProtobufExponentFn : Lean.Parser.ParserFn := fun c s =>
  let current := c.get s.pos
  if current != 'e' && current != 'E' then
    s
  else
    let s := consumeProtobufFloatCharFn c s
    let current := c.get s.pos
    let s :=
      if current == '+' || current == '-' then
        consumeProtobufFloatCharFn c s
      else
        s
    requireProtobufDecimalDigitsFn c s

private def normalizeProtobufFloatToken (raw : String) : String :=
  if raw.startsWith "." then "0" ++ raw else raw

/--
Validate the token body of a protobuf `floatLit` and return spelling accepted by
Lean's `scientific` elaborator.  In particular, `.5` becomes `0.5`.

The leading sign is a separate syntax token.  Protoc's definitive handwritten
tokenizer commits to an octal integer token when an initial `0` is followed by
another digit, so `00.5` and `01e2` are not subsequently reinterpreted as
floating-point literals.
-/
def canonicalProtobufFloatLiteral?
    (stx : Lean.TSyntax `scientific) :
    Option (Lean.TSyntax `scientific) := do
  let raw ← stx.raw[0].isIdOrAtom?
  if raw.contains '_' then
    none
  else
    let normalized := normalizeProtobufFloatToken raw
    match normalized.toList with
    | '0' :: second :: _ =>
        if '0' ≤ second && second ≤ '9' then
          none
        else if (Lean.Syntax.decodeScientificLitVal? normalized).isSome then
          pure (Lean.Syntax.mkScientificLit normalized stx.raw.getHeadInfo)
        else
          none
    | _ =>
        if (Lean.Syntax.decodeScientificLitVal? normalized).isSome then
          pure (Lean.Syntax.mkScientificLit normalized stx.raw.getHeadInfo)
        else
          none

private meta def pushProtobufScientific
    (start : String.Pos.Raw) : Lean.Parser.ParserFn := fun c s =>
  if s.hasError then
    s
  else
    let stop := s.pos
    let raw := c.extract start stop
    let normalized := if raw.startsWith "." then "0" ++ raw else raw
    let leading := c.mkEmptySubstringAt start
    let s := Lean.Parser.whitespace c s
    let trailing := c.substring (startPos := stop) (stopPos := s.pos)
    let info := Lean.SourceInfo.original leading start trailing stop
    s.pushSyntax (Lean.Syntax.mkScientificLit normalized info)

private meta def protobufFloatLitFn : Lean.Parser.ParserFn := fun c s =>
  let start := s.pos
  let first := c.get s.pos
  let s :=
    if first == '.' then
      let s := consumeProtobufFloatCharFn c s
      let s := requireProtobufDecimalDigitsFn c s
      if s.hasError then s else parseProtobufExponentFn c s
    else if isProtobufDecimalDigit first then
      let afterFirst := c.next s.pos
      if first == '0' && isProtobufDecimalDigit (c.get afterFirst) then
        s.mkUnexpectedError
          "protobuf floating-point literals cannot have a multi-digit leading-zero integer part"
      else
        let s := takeProtobufDecimalDigitsFn c s
        let current := c.get s.pos
        if current == '.' then
          let s := consumeProtobufFloatCharFn c s
          let s := takeProtobufDecimalDigitsFn c s
          parseProtobufExponentFn c s
        else if current == 'e' || current == 'E' then
          parseProtobufExponentFn c s
        else
          s.mkUnexpectedError
            "expected a decimal point or exponent in protobuf floating-point literal"
    else
      s.mkUnexpectedError "expected a protobuf floating-point literal"
  pushProtobufScientific start c s

meta def protobufFloatLitNoAntiquot : Lean.Parser.Parser := {
  info :=
    (Lean.Parser.numLitNoAntiquot <|>
      Lean.Parser.scientificLitNoAntiquot <|>
      Lean.Parser.symbol ".").info
  fn := protobufFloatLitFn
}

open Lean.PrettyPrinter Lean.PrettyPrinter.Formatter in
@[combinator_formatter protobufFloatLitNoAntiquot]
meta def protobufFloatLitNoAntiquot.formatter : Formatter :=
  visitAtom Lean.scientificLitKind

open Lean.PrettyPrinter Lean.PrettyPrinter.Parenthesizer in
@[combinator_parenthesizer protobufFloatLitNoAntiquot]
meta def protobufFloatLitNoAntiquot.parenthesizer : Parenthesizer :=
  visitToken

@[run_parser_attribute_hooks]
meta def protobufFloatLit : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot
    (Lean.Parser.mkAntiquot "scientific" Lean.scientificLitKind)
    protobufFloatLitNoAntiquot

declare_syntax_cat options_value (behavior := symbol)

syntax ident : options_value
syntax str : options_value
syntax &"true" : options_value
syntax &"false" : options_value
syntax protobufFloatLit : options_value
syntax "-" protobufFloatLit : options_value
syntax protobufQuotationOnlyPlus protobufFloatLit : options_value
syntax protobufIntLit : options_value
syntax "-" protobufIntLit : options_value
syntax protobufQuotationOnlyPlus protobufIntLit : options_value
syntax "-" &"inf" : options_value
syntax "-" &"nan" : options_value

syntax options_entry := ident " = " options_value

syntax options := "[" options_entry,*,? "]"


declare_syntax_cat enum_value (behavior := symbol)

syntax protobufIntLit : enum_value
syntax "-" protobufIntLit : enum_value

syntax enum_entry := ident " = " enum_value ";"

syntax (name := enumDec) "enum " ident (options)? " {" ppLine (enum_entry ppLine)* "}" : command


syntax message_entry_modifier := &"optional" <|> &"repeated" <|> &"required"

syntax message_field_type_normal := ident
syntax message_field_type_map := &"map" "<" ident "," ident ">"

syntax message_field_type := message_field_type_map <|> message_field_type_normal

syntax message_entry := (message_entry_modifier)? message_field_type ident " = " protobufIntLit (options)? ";"

syntax (name := messageDec) "message " ident (options)? " {" ppLine (message_entry ppLine)* "}" : command

syntax (name := oneofDec) "oneof " ident " {" ppLine (message_entry ppLine)*  "}" : command

syntax (name := extendDec) "extend " ident " {" ppLine (message_entry ppLine)* "}" : command

syntax proto_decl := enumDec <|> messageDec <|> oneofDec

syntax (name := proto_mutual_stx) "proto_mutual " "{" ppLine (proto_decl ppLine)* "}" : command

namespace PrettyPrinter

open Lean

private def extract_num : TSyntax `num → String := fun x => x.raw[0].isIdOrAtom?.getD (panic! "num")

private partial def renderIdentName : Name → String
  | .anonymous => panic! "anonymous protobuf identifier"
  | .num parent value => s!"{renderIdentName parent}.{value}"
  | .str .anonymous part =>
      Name.escapePart part (force := true)
        |>.getD (panic! "unrenderable protobuf identifier component")
  | .str (.str .anonymous "_root_") part =>
      -- `_root_` is Lean's root qualifier, deliberately introduced for
      -- references to built-in google.protobuf declarations.
      "_root_." ++
        (Name.escapePart part (force := true)
          |>.getD (panic! "unrenderable protobuf identifier component"))
  | .str parent part =>
      renderIdentName parent ++ "." ++
        (Name.escapePart part (force := true)
          |>.getD (panic! "unrenderable protobuf identifier component"))

private def extract_id : TSyntax `ident → String := fun x =>
  /-
  Quoted notation carries fresh macro scopes even though protobuf names are
  schema identifiers rather than Lean bindings.  Every actual name component
  is force-escaped as well: protobuf identifiers such as `match`, `do`, and
  `structure` are legal, but printing them as bare Lean tokens does not parse.
  -/
  renderIdentName x.getId.eraseMacroScopes

private def tokenTextSafe (context : String) (stx : Syntax) :
    Except String String :=
  match stx.isIdOrAtom? with
  | some text =>
      if text.isEmpty then
        throw s!"cannot render {context}: token is empty"
      else
        pure text
  | none =>
      throw s!"cannot render {context}: expected an identifier or atom token"

private def protobufIntTextSafe
    (context : String) (stx : TSyntax `num) : Except String String := do
  let some canonical := canonicalProtobufIntLiteral? stx
    | throw s!"cannot render {context}: invalid protobuf integer literal"
  tokenTextSafe context canonical.raw[0]

private def protobufFloatTextSafe
    (context : String) (stx : TSyntax `scientific) :
    Except String String := do
  let some canonical := canonicalProtobufFloatLiteral? stx
    | throw s!"cannot render {context}: invalid protobuf floating-point literal"
  tokenTextSafe context canonical.raw[0]

private partial def renderIdentNameSafe : Name → Except String String
  | .anonymous =>
      throw "cannot render protobuf identifier: name is anonymous"
  | .num _ value =>
      /-
      Numeric `Name` components are used internally by Lean, but the `ident`
      parser category has no source spelling that preserves them.  Printing
      `.1` would instead be parsed as projection syntax (where it is accepted
      at all), so reject it rather than claiming a lossless command reprint.
      -/
      throw s!"cannot render protobuf identifier: numeric name component {value} has no identifier syntax"
  | .str .anonymous part =>
      match Name.escapePart part (force := true) with
      | some escaped => pure escaped
      | none =>
          throw s!"cannot render protobuf identifier component {part.quote} as Lean syntax"
  | .str (.str .anonymous "_root_") part => do
      -- This exact prefix is deliberately used for references to protobuf's
      -- built-in declarations in the Lean root namespace.
      let escaped ←
        match Name.escapePart part (force := true) with
        | some escaped => pure escaped
        | none =>
            throw s!"cannot render protobuf identifier component {part.quote} as Lean syntax"
      return "_root_." ++ escaped
  | .str parent part => do
      let renderedPrefix ← renderIdentNameSafe parent
      let escaped ←
        match Name.escapePart part (force := true) with
        | some escaped => pure escaped
        | none =>
            throw s!"cannot render protobuf identifier component {part.quote} as Lean syntax"
      return renderedPrefix ++ "." ++ escaped

private def extractIdSafe (x : TSyntax `ident) : Except String String :=
  match x.raw with
  | .ident _ _ name _ => renderIdentNameSafe name.eraseMacroScopes
  | _ => throw "cannot render protobuf identifier: malformed identifier syntax"

/--
Safely render an option value generated by the protobuf frontend.

Unlike `pprint`, this entry point and every `pprintSafe` function below
propagates malformed syntax and unrepresentable Lean names through `Except`.
The standalone plugin uses only this API, so a forged descriptor cannot turn a
`panic!` fallback into generated source.
-/
def options_value.pprintSafe : TSyntax `options_value → Except String String
  | `(options_value| $x:ident) => extractIdSafe x
  | `(options_value| $x:scientific) =>
      protobufFloatTextSafe "scientific option value" x
  | `(options_value| -$x:scientific) => do
      return "-" ++ (← protobufFloatTextSafe "scientific option value" x)
  | `(options_value| +$x:scientific) =>
      throw "cannot render scientific option value: protobuf literals do not allow a leading plus sign"
  | `(options_value| $x:num) =>
      protobufIntTextSafe "numeric option value" x
  | `(options_value| -$x:num) => do
      return "-" ++ (← protobufIntTextSafe "numeric option value" x)
  | `(options_value| +$x:num) =>
      throw "cannot render numeric option value: protobuf literals do not allow a leading plus sign"
  | `(options_value| -inf) => pure "-inf"
  | `(options_value| -nan) => pure "-nan"
  | `(options_value| true) => pure "true"
  | `(options_value| false) => pure "false"
  | `(options_value| $x:str) =>
      tokenTextSafe "string option value" x.raw[0]
  | _ => throw "cannot render malformed protobuf option value syntax"

def options_entry.pprintSafe :
    TSyntax ``options_entry → Except String String
  | `(options_entry| $x = $v) => do
      return s!"{← extractIdSafe x} = {← options_value.pprintSafe v}"
  | _ => throw "cannot render malformed protobuf option entry syntax"

def options.pprintSafe : TSyntax ``options → Except String String
  | `(options| [ $xs,* ]) => do
      let entries ← xs.getElems.toList.mapM options_entry.pprintSafe
      return s!"[ {String.intercalate "," entries} ]"
  | _ => throw "cannot render malformed protobuf options syntax"

def enum_value.pprintSafe : TSyntax `enum_value → Except String String
  | `(enum_value| $n:num) =>
      protobufIntTextSafe "enum numeric value" n
  | `(enum_value| -$n:num) => do
      return "-" ++ (← protobufIntTextSafe "enum numeric value" n)
  | _ => throw "cannot render malformed protobuf enum value syntax"

def enum_entry.pprintSafe : TSyntax ``enum_entry → Except String String
  | `(enum_entry| $x = $n:enum_value;) => do
      return s!"{← extractIdSafe x} = {← enum_value.pprintSafe n};"
  | _ => throw "cannot render malformed protobuf enum entry syntax"

def message_entry_modifier.pprintSafe :
    TSyntax ``message_entry_modifier → Except String String
  | `(message_entry_modifier| optional) => pure "optional"
  | `(message_entry_modifier| repeated) => pure "repeated"
  | `(message_entry_modifier| required) => pure "required"
  | _ => throw "cannot render malformed protobuf field modifier syntax"

def message_field_type.pprintSafe :
    TSyntax ``message_field_type → Except String String
  | `(message_field_type| $x:ident) => extractIdSafe x
  | `(message_field_type| map<$k:ident, $v:ident>) => do
      return s!"map<{← extractIdSafe k}, {← extractIdSafe v}>"
  | _ => throw "cannot render malformed protobuf field type syntax"

private def options?.pprintSafe :
    Option (TSyntax ``options) → Except String String
  | some opts => do return " " ++ (← options.pprintSafe opts)
  | none => pure ""

def message_entry.pprintSafe :
    TSyntax ``message_entry → Except String String
  | `(message_entry| $[$m?]? $t:message_field_type $x:ident = $n:num $[$opts?]?;) => do
      let modifier ←
        match m? with
        | some modifier =>
            (· ++ " ") <$> message_entry_modifier.pprintSafe modifier
        | none => pure ""
      let fieldType ← message_field_type.pprintSafe t
      let fieldName ← extractIdSafe x
      let fieldNumber ← protobufIntTextSafe "protobuf field number" n
      let opts ← options?.pprintSafe opts?
      return s!"{modifier}{fieldType} {fieldName} = {fieldNumber}{opts};"
  | _ => throw "cannot render malformed protobuf field syntax"

private def joinSafeLines (xs : List String) : String :=
  match xs with
  | [] => ""
  | _ =>
      "\n" ++ String.intercalate "\n" (xs.map (fun x => s!"  {x}")) ++
        "\n"

def enumDec.pprintSafe : TSyntax ``enumDec → Except String String
  | `(enumDec| enum $x:ident $[$opts?]? { $[$entries]* }) => do
      let name ← extractIdSafe x
      let opts ← options?.pprintSafe opts?
      let body ← entries.toList.mapM enum_entry.pprintSafe
      return s!"enum {name}{opts} \{{joinSafeLines body}}"
  | _ => throw "cannot render malformed protobuf enum declaration syntax"

def messageDec.pprintSafe : TSyntax ``messageDec → Except String String
  | `(messageDec| message $x:ident $[$opts?]? { $[$entries]* }) => do
      let name ← extractIdSafe x
      let opts ← options?.pprintSafe opts?
      let body ← entries.toList.mapM message_entry.pprintSafe
      return s!"message {name}{opts} \{{joinSafeLines body}}"
  | _ => throw "cannot render malformed protobuf message declaration syntax"

def oneofDec.pprintSafe : TSyntax ``oneofDec → Except String String
  | `(oneofDec| oneof $x:ident { $[$entries]* }) => do
      let name ← extractIdSafe x
      let body ← entries.toList.mapM message_entry.pprintSafe
      return s!"oneof {name} \{{joinSafeLines body}}"
  | _ => throw "cannot render malformed protobuf oneof declaration syntax"

def extendDec.pprintSafe : TSyntax ``extendDec → Except String String
  | `(extendDec| extend $x:ident { $[$entries]* }) => do
      let name ← extractIdSafe x
      let body ← entries.toList.mapM message_entry.pprintSafe
      return s!"extend {name} \{{joinSafeLines body}}"
  | _ => throw "cannot render malformed protobuf extension declaration syntax"

def proto_decl.pprintSafe : TSyntax ``proto_decl → Except String String :=
  fun s =>
    let declaration := s.raw[0]
    match declaration.getKind with
    | ``enumDec => enumDec.pprintSafe <| TSyntax.mk declaration
    | ``messageDec => messageDec.pprintSafe <| TSyntax.mk declaration
    | ``oneofDec => oneofDec.pprintSafe <| TSyntax.mk declaration
    | kind =>
        throw s!"cannot render malformed protobuf mutual declaration kind {kind}"

def proto_mutual_stx.pprintSafe :
    TSyntax ``proto_mutual_stx → Except String String
  | `(proto_mutual_stx| proto_mutual { $[$decls]* }) => do
      let body ← decls.toList.mapM proto_decl.pprintSafe
      return s!"proto_mutual \{{joinSafeLines body}}"
  | _ => throw "cannot render malformed protobuf mutual declaration syntax"

private def reprintLeafSafe
    (info : SourceInfo) (value : String) : String :=
  match info with
  | .original leading _ trailing _ => s!"{leading}{value}{trailing}"
  | _ => s!" {value} "

private partial def reprintSyntaxSafe : Syntax → Except String String
  | .missing => throw "cannot render generated command: syntax is missing"
  | .atom info value => pure <| reprintLeafSafe info value
  | .ident info _ value _ => do
      /-
      `Syntax.ident` retains the raw token spelling, but antiquotation can
      construct an identifier whose raw spelling is not valid Lean source
      (`match`, an anonymous name, or a component containing `»`).  Render the
      semantic name canonically instead, erasing quotation hygiene and
      force-escaping every source-level component.  `renderIdentNameSafe`
      returns an error for names Lean cannot represent; it never substitutes a
      `panic!` fallback into plugin output.
      -/
      let rendered ← renderIdentNameSafe value.eraseMacroScopes
      pure <| reprintLeafSafe info rendered
  | .node _ kind args =>
      if kind == `hygieneInfo then
        /-
        Hygienic parentheses carry an internal anonymous identifier below
        this metadata node.  It has no source spelling: the surrounding
        `hygienicLParen` already contains the real `(` token.  Descending into
        it would incorrectly reject every explicitly parenthesized generated
        term as an anonymous source identifier.
        -/
        pure ""
      else if kind == choiceKind then
        match args[0]? with
        | none =>
            throw "cannot render generated command: empty parser choice node"
        | some first => do
            let rendered ← reprintSyntaxSafe first
            for alternative in args[1...*] do
              let alternativeRendered ← reprintSyntaxSafe alternative
              unless alternativeRendered == rendered do
                throw
                  "cannot render generated command: parser choice alternatives print differently"
            return rendered
      else do
        let rendered ← args.toList.mapM reprintSyntaxSafe
        pure <| String.join rendered

/--
Safely render a complete generated command. Custom protobuf declarations use
their structural renderer; other commands are accepted only when Lean can
losslessly reprint their syntax.
-/
def command.pprintSafe (s : TSyntax `command) : Except String String :=
  match s.raw.getKind with
  | ``enumDec => enumDec.pprintSafe <| TSyntax.mk s.raw
  | ``oneofDec => oneofDec.pprintSafe <| TSyntax.mk s.raw
  | ``messageDec => messageDec.pprintSafe <| TSyntax.mk s.raw
  | ``proto_mutual_stx => proto_mutual_stx.pprintSafe <| TSyntax.mk s.raw
  | ``extendDec => extendDec.pprintSafe <| TSyntax.mk s.raw
  | kind =>
      match reprintSyntaxSafe s.raw with
      | .ok rendered =>
          if rendered.isEmpty then
            throw s!"cannot render empty generated command kind {kind}"
          else
            pure rendered
      | .error err =>
          throw s!"cannot render generated command kind {kind}: {err}"

def options_value.pprint : TSyntax `options_value → String
  | `(options_value| $x:ident) => s!"{extract_id x}"
  | `(options_value| $x:scientific) => s!"{x.raw[0].isIdOrAtom?.getD (panic! "scientific")}"
  | `(options_value| -$x:scientific) => s!"-{x.raw[0].isIdOrAtom?.getD (panic! "-scientific")}"
  | `(options_value| +$x:scientific) => s!"+{x.raw[0].isIdOrAtom?.getD (panic! "+scientific")}"
  | `(options_value| $x:num) => extract_num x
  | `(options_value| -$x:num) => s!"-{extract_num x}"
  | `(options_value| +$x:num) => s!"+{extract_num x}"
  | `(options_value| -inf) => "-inf"
  | `(options_value| -nan) => "-nan"
  | `(options_value| true) => s!"true"
  | `(options_value| false) => s!"false"
  | `(options_value| $x:str) => s!"{x.raw[0].isIdOrAtom?.getD (panic! "str")}"
  | _ => panic! "options_value"

def options_entry.pprint : TSyntax ``options_entry → String
  | `(options_entry| $x = $v) => s!"{extract_id x} = {options_value.pprint v}"
  | _ => panic! "options_entry"

def options.pprint : TSyntax ``options → String
  | `(options| [ $xs,* ]) => s!"[ {String.intercalate "," (xs.getElems.toList.map options_entry.pprint)} ]"
  | _ => panic! "options"

def enum_value.pprint : TSyntax `enum_value → String
  | `(enum_value| $n:num) => extract_num n
  | `(enum_value| -$n:num) => s!"-{extract_num n}"
  | _ => panic! "enum_value"

def enum_entry.pprint : TSyntax ``enum_entry → String
  | `(enum_entry| $x = $n:enum_value;) => s!"{extract_id x} = {enum_value.pprint n};"
  | _ => panic! "enum_entry"

def message_entry_modifier.pprint : TSyntax ``message_entry_modifier → String
  | `(message_entry_modifier| optional) => "optional"
  | `(message_entry_modifier| repeated) => "repeated"
  | `(message_entry_modifier| required) => "required"
  | _ => panic! "message_entry_modifier"

def message_field_type.pprint : TSyntax ``message_field_type → String
  | `(message_field_type| $x:ident) => extract_id x
  | `(message_field_type| map<$k:ident, $v:ident>) => s!"map<{extract_id k}, {extract_id v}>"
  | _ => panic! "message_field_type"

private def options?.pprint : Option (TSyntax ``options) → String
  | some opts => s!" {options.pprint opts}"
  | none => ""

def message_entry.pprint : TSyntax ``message_entry → String
  | `(message_entry| $[$m?]? $t:message_field_type $x:ident = $n:num $[$opts?]?;) =>
      s!"{((message_entry_modifier.pprint <$> m?).map (fun x => s!"{x} ")).getD ""}{message_field_type.pprint t} {extract_id x} = {extract_num n} {options?.pprint opts?};"
  | _ => panic! "message_entry"

private def join_lines (xs : List String) : String :=
  match xs with
  | [] => ""
  | _ => "\n" ++ String.intercalate "\n" (xs.map (fun x => s!"  {x}")) ++ "\n"

def enumDec.pprint : TSyntax ``enumDec → String
  | `(enumDec| enum $x:ident $[$opts?]? { $[$entries]* }) =>
      let body := join_lines (entries.toList.map enum_entry.pprint)
      s!"enum {extract_id x}{options?.pprint opts?} \{{body}}"
  | _ => panic! "enumDec"

def messageDec.pprint : TSyntax ``messageDec → String
  | `(messageDec| message $x:ident $[$opts?]? { $[$entries]* }) =>
      let body := join_lines (entries.toList.map message_entry.pprint)
      s!"message {extract_id x}{options?.pprint opts?} \{{body}}"
  | _ => panic! "messageDec"

def oneofDec.pprint : TSyntax ``oneofDec → String
  | `(oneofDec| oneof $x:ident { $[$entries]* }) =>
      let body := join_lines (entries.toList.map message_entry.pprint)
      s!"oneof {extract_id x} \{{body}}"
  | _ => panic! "oneofDec"

def extendDec.pprint : TSyntax ``extendDec → String
  | `(extendDec| extend $x:ident { $[$entries]* }) =>
      let body := join_lines (entries.toList.map message_entry.pprint)
      s!"extend {extract_id x} \{{body}}"
  | _ => panic! "extendDec"

def proto_decl.pprint : TSyntax ``proto_decl → String := fun s =>
  match s.raw[0].getKind with
  | ``enumDec => enumDec.pprint <| TSyntax.mk s.raw[0]
  | ``messageDec => messageDec.pprint <| TSyntax.mk s.raw[0]
  | ``oneofDec => oneofDec.pprint <| TSyntax.mk s.raw[0]
  | _ => panic! "proto_decl"

def proto_mutual_stx.pprint : TSyntax ``proto_mutual_stx → String
  | `(proto_mutual_stx| proto_mutual { $[$decls]* }) =>
      let body := join_lines (decls.toList.map proto_decl.pprint)
      s!"proto_mutual \{{body}}"
  | _ => panic! "proto_mutual_stx"
