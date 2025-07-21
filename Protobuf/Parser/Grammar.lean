import Lean

open Lean Parser PrettyPrinter

namespace Protobuf.Parser

section

/-!
letter = "A" ... "Z" | "a" ... "z"
decimalDigit = "0" ... "9"
octalDigit   = "0" ... "7"
hexDigit     = "0" ... "9" | "A" ... "F" | "a" ... "f"

ident = letter { letter | decimalDigit | "_" }
fullIdent = ident { "." ident }
messageName = ident
enumName = ident
fieldName = ident
oneofName = ident
mapName = ident
serviceName = ident
rpcName = ident
messageType = [ "." ] { ident "." } messageName
enumType = [ "." ] { ident "." } enumName
-/

private def is_letter : Char → Bool := Char.isAlpha
private def is_decimalDigit : Char → Bool := Char.isDigit
private def is_octalDigit : Char → Bool := fun c => '0' ≤ c && c ≤ '7'
private def is_hexDigit : Char → Bool := fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/--
This function generates `ident` while ensuring it is not escaped has no more than one "parts".
* To be escaped, we mean something enclosed by `«»`.
* To have more than one parts, we mean something like `A.B` with separating dots.
-/
partial def pidentFnAux (startPos : String.Pos) (tk : Option Token) (r : Name) : ParserFn :=
  let rec parse (r : Name) (c s) :=
    let input := c.input
    let i     := s.pos
    if h : input.atEnd i then
      s.mkEOIError
    else
      let curr := input.get' i h
      if curr.isAlpha then
        let startPart := i
        let s         := takeWhileFn (fun c => c.isAlpha || c.isDigit || c == '_') c (s.next input i)
        let stopPart  := s.pos
        let r := .str r (input.extract startPart stopPart)
        mkIdResult startPos tk r c s
      else
        mkTokenAndFixPos startPos tk c s
  parse r

def pidentFn : ParserFn := fun c s =>
  let i := s.pos
  pidentFnAux i none .anonymous c s

def pidentNoAntiquot : Parser := {
  fn   := pidentFn
  info := identNoAntiquot.info
}

/--
`pident := [a-zA-Z][a-zA-Z_]*`

`isPseudoKind` mut be true to be compatible (only logically) with `ident`'s parenthesizer and formatter.
`identKind` is not used since we still want to quote and antiquote as if it were a real node.
-/
def pident : Parser :=
  withAntiquot (mkAntiquot "pident" decl_name% (isPseudoKind := true)) pidentNoAntiquot

run_meta do
  modifyEnv fun env => addSyntaxNodeKind env ``Protobuf.Parser.pident

attribute [combinator_parenthesizer Protobuf.Parser.pident] ident.parenthesizer
attribute [combinator_formatter Protobuf.Parser.pident] ident.formatter
attribute [parenthesizer Protobuf.Parser.pident] ident.parenthesizer
attribute [formatter Protobuf.Parser.pident] ident.formatter

run_meta do
  modifyEnv fun env => addSyntaxNodeKind env `Protobuf.Parser.fullIdent

/--
`fullIdent := sepBy1(pident, ".")` where there are no spaces
-/
@[run_parser_attribute_hooks]
def fullIdent : Parser := withAntiquot (mkAntiquot "fullIdent" decl_name%) <| node decl_name% <|
  sepBy1 pident "." (checkNoWsBefore >> "." >> checkNoWsBefore)

attribute [parenthesizer Protobuf.Parser.fullIdent] fullIdent.parenthesizer
attribute [formatter Protobuf.Parser.fullIdent] fullIdent.formatter

abbrev messageName := pident
abbrev enumName    := pident
abbrev fieldName   := pident
abbrev oneofName   := pident
abbrev mapName     := pident
abbrev serviceName := pident
abbrev rpcName     := pident

attribute [run_parser_attribute_hooks, inherit_doc pident]
  messageName
  enumName
  fieldName
  oneofName
  mapName
  serviceName
  rpcName

run_meta do
  modifyEnv fun env => addSyntaxNodeKind env `Protobuf.Parser.dot_pident

/--
`dot_pident := (".")? sepBy1(pident, ".")` where there are no spaces
-/
@[run_parser_attribute_hooks]
def dot_pident : Parser := withAntiquot (mkAntiquot "dot_pident" decl_name%) <| node decl_name% <|
  optional ("." >> checkNoWsBefore) >> sepBy1 pident "." (checkNoWsBefore >> "." >> checkNoWsBefore)

attribute [parenthesizer Protobuf.Parser.dot_pident] dot_pident.parenthesizer
attribute [formatter Protobuf.Parser.dot_pident] dot_pident.formatter

abbrev messageType := dot_pident
abbrev enumType := dot_pident

attribute [run_parser_attribute_hooks, inherit_doc dot_pident]
  messageType
  enumType

end

section

/-!
intLit     = decimalLit | octalLit | hexLit
decimalLit = [-] ( "1" ... "9" ) { decimalDigit }
octalLit   = [-] "0" { octalDigit }
hexLit     = [-] "0" ( "x" | "X" ) hexDigit { hexDigit }

floatLit = [-] ( decimals "." [ decimals ] [ exponent ] | decimals exponent | "."decimals [ exponent ] ) | "inf" | "nan"
decimals  = [-] decimalDigit { decimalDigit }
exponent  = ( "e" | "E" ) [ "+" | "-" ] decimals
-/

def decimalLitKind := `Protobuf.Parser.decimalLit
def octalLitKind := `Protobuf.Parser.octalLit
def hexLitKind := `Protobuf.Parser.hexLit

def decimalLitFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    if curr.isDigit then
      let s := takeWhile1Fn Char.isDigit "invalid decimal digit" c s
      mkNodeToken decimalLitKind i c s
    else s.mkUnexpectedError "invalid decimal literal"

def octalLitFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    if curr = '0' then
      let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "invalid octal digit" c (s.next' input i h)
      mkNodeToken octalLitKind i c s
    else s.mkUnexpectedError "invalid octal literal"

def hexLitFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let begin := i
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr = '0' then
      if h : input.atEnd i then s.mkEOIError
      else
        let curr := input.get' i h
        let i    := input.next' i h
        if curr = 'x' || curr = 'X' then
          let s := takeWhile1Fn (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "invalid hexadecimal digit" c (s.setPos i)
          mkNodeToken hexLitKind begin c s
        else
          s.mkUnexpectedError "invalid hexadecimal literal"
    else s.mkUnexpectedError "invalid hexadecimal literal"

def decimalLitNoAntiquot : Parser where
  fn := decimalLitFn

open Parenthesizer in
@[combinator_parenthesizer decimalLitNoAntiquot]
def decimalLitNoAntiquot.parenthesizer : Parenthesizer := do
  checkKind decimalLitKind
  visitArgs do
    visitToken

open Formatter Syntax MonadTraverser in
@[combinator_formatter decimalLitNoAntiquot]
def decimalLitNoAntiquot.formatter : Formatter := do
  checkKind decimalLitKind
  visitArgs do
    let stx ← getCur
    match stx with
    | .atom _ s =>
      modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
      goLeft
    | _ => throwError s!"not a decimal literal: {stx}"

def octalLitNoAntiquot : Parser where
  fn := octalLitFn

open Parenthesizer in
@[combinator_parenthesizer octalLitNoAntiquot]
def octalLitNoAntiquot.parenthesizer : Parenthesizer := do
  checkKind octalLitKind
  visitArgs do
    visitToken

open Formatter Syntax MonadTraverser in
@[combinator_formatter octalLitNoAntiquot]
def octalLitNoAntiquot.formatter : Formatter := do
  checkKind octalLitKind
  visitArgs do
    let stx ← getCur
    match stx with
    | .atom _ s =>
      modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
      goLeft
    | _ => throwError s!"not an octal literal: {stx}"

def hexLitNoAntiquot : Parser where
  fn := hexLitFn

open Parenthesizer in
@[combinator_parenthesizer hexLitNoAntiquot]
def hexLitNoAntiquot.parenthesizer : Parenthesizer := do
  checkKind hexLitKind
  visitArgs do
    visitToken

open Formatter Syntax MonadTraverser in
@[combinator_formatter hexLitNoAntiquot]
def hexLitNoAntiquot.formatter : Formatter := do
  checkKind hexLitKind
  visitArgs do
    let stx ← getCur
    match stx with
    | .atom _ s =>
      modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
      goLeft
    | _ => throwError s!"not a hexadecimal literal: {stx}"

@[run_parser_attribute_hooks]
def decimalLit : Parser := withAntiquot (mkAntiquot "decimalLit" decimalLitKind) decimalLitNoAntiquot

@[run_parser_attribute_hooks]
def octalLit : Parser := withAntiquot (mkAntiquot "octalLit" octalLitKind) octalLitNoAntiquot

@[run_parser_attribute_hooks]
def hexLit : Parser := withAntiquot (mkAntiquot "hexLit" hexLitKind) hexLitNoAntiquot

run_meta do
  modifyEnv fun env =>
    let env := addSyntaxNodeKind env decimalLitKind
    let env := addSyntaxNodeKind env octalLitKind
    let env := addSyntaxNodeKind env hexLitKind
    env

attribute [parenthesizer Protobuf.Parser.decimalLit] decimalLit.parenthesizer
attribute [formatter Protobuf.Parser.decimalLit] decimalLit.formatter

attribute [parenthesizer Protobuf.Parser.octalLit] octalLit.parenthesizer
attribute [formatter Protobuf.Parser.octalLit] octalLit.formatter

attribute [parenthesizer Protobuf.Parser.hexLit] hexLit.parenthesizer
attribute [formatter Protobuf.Parser.hexLit] hexLit.formatter

syntax intLit := atomic(octalLit) <|> atomic(hexLit) <|> atomic(decimalLit)

syntax boolLit := &"true" <|> &"false"
syntax floatLit := scientificLit -- TODO: refine

end

syntax emptyStatement := ";"

/-!
constant = fullIdent | ( [ "-" | "+" ] intLit ) | ( [ "-" | "+" ] floatLit ) |
                strLit | boolLit | MessageValue
-/
syntax protobuf_const :=
  fullIdent <|>
  atomic("-" intLit) <|>
  atomic("+" intLit) <|>
  intLit <|>
  atomic("-" floatLit) <|>
  atomic("+" floatLit) <|>
  floatLit <|>
  strLit <|> -- TODO: refine
  boolLit
  -- TODO: `MessageValue`

section

/-!
syntax = "syntax" "=" ("'" "proto3" "'" | '"' "proto3" '"') ";"
-/

def syntaxSpec.v3SingleQuoteKind : Name := `Protobuf.Parser.syntaxSpec.v3SingleQuote
def syntaxSpec.v3DoubleQuoteKind : Name := `Protobuf.Parser.syntaxSpec.v3DoubleQuote

def syntaxSpec.v3SingleQuoteFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let begin := i
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    if curr = '\'' then
      let s := strAux "proto3" "unexpected end of input" ⟨0⟩ c (s.next' input i h)
      let i := s.pos
      if h : input.atEnd i then
        s.mkEOIError
      else
        let curr := input.get' i h
        if curr != '\'' then
          s.mkUnexpectedError "unknown protobuf version specification"
        else
          let s := s.next' input i h
          mkNodeToken v3SingleQuoteKind begin c s
    else s.mkUnexpectedError "invalid decimal literal"

def syntaxSpec.v3DoubleQuoteFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let begin := i
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    if curr = '\"' then
      let s := strAux "proto3" "unexpected end of input" ⟨0⟩ c (s.next' input i h)
      let i := s.pos
      if h : input.atEnd i then
        s.mkEOIError
      else
        let curr := input.get' i h
        if curr != '\"' then
          s.mkUnexpectedError "unknown protobuf version specification"
        else
          let s := s.next' input i h
          mkNodeToken v3DoubleQuoteKind begin c s
    else s.mkUnexpectedError "invalid decimal literal"

def syntaxSpec.v3SingleQuote : Parser where
  fn := syntaxSpec.v3SingleQuoteFn

def syntaxSpec.v3DoubleQuote : Parser where
  fn := syntaxSpec.v3DoubleQuoteFn

run_meta do
  modifyEnv fun env =>
    let env := addSyntaxNodeKind env syntaxSpec.v3SingleQuoteKind
    let env := addSyntaxNodeKind env syntaxSpec.v3DoubleQuoteKind
    env

open Parenthesizer in
@[combinator_parenthesizer syntaxSpec.v3SingleQuote, parenthesizer Protobuf.Parser.syntaxSpec.v3SingleQuote]
def syntaxSpec.v3SingleQuote.parenthesizer : Parenthesizer := do
  checkKind v3SingleQuoteKind
  visitArgs do
    visitToken

open Formatter Syntax MonadTraverser in
@[combinator_formatter syntaxSpec.v3SingleQuote, formatter Protobuf.Parser.syntaxSpec.v3SingleQuote]
def syntaxSpec.v3SingleQuote.formatter : Formatter := do
  checkKind v3SingleQuoteKind
  visitArgs do
    let stx ← getCur
    match stx with
    | .atom _ s =>
      modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
      goLeft
    | _ => throwError s!"not an atom: {stx}"

open Parenthesizer in
@[combinator_parenthesizer syntaxSpec.v3DoubleQuote, parenthesizer Protobuf.Parser.syntaxSpec.v3DoubleQuote]
def syntaxSpec.v3DoubleQuote.parenthesizer : Parenthesizer := do
  checkKind v3DoubleQuoteKind
  visitArgs do
    visitToken

open Formatter Syntax MonadTraverser in
@[combinator_formatter syntaxSpec.v3DoubleQuote, formatter Protobuf.Parser.syntaxSpec.v3DoubleQuote]
def syntaxSpec.v3DoubleQuote.formatter : Formatter := do
  checkKind v3DoubleQuoteKind
  visitArgs do
    let stx ← getCur
    match stx with
    | .atom _ s =>
      modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
      goLeft
    | _ => throwError s!"not an atom: {stx}"

syntax syntaxSpecCandidates := syntaxSpec.v3SingleQuote <|> syntaxSpec.v3DoubleQuote
syntax syntaxSpec := &"syntax" ppSpace "=" ppSpace syntaxSpecCandidates ";"

end

/-!
import = "import" [ "weak" | "public" ] strLit ";"
-/
syntax importKind := &"weak" <|> &"public"
syntax pimport := &"import" ppSpace (importKind ppSpace)? strLit ";"

/-!
package = "package" fullIdent ";"
-/
syntax package := &"package" ppSpace fullIdent ";"

/-!
option = "option" optionName  "=" constant ";"
optionName = ( ident | bracedFullIdent ) { "." ( ident | bracedFullIdent ) }
bracedFullIdent = "(" ["."] fullIdent ")"
optionNamePart = { ident | "(" ["."] fullIdent ")" }
-/
syntax bracedFullIdent := "(" (".")? fullIdent ")"
syntax optionName := (pident <|> bracedFullIdent) (atomic("." noWs pident) <|> atomic(".(" (".")? fullIdent ")"))*
syntax option := &"option" ppSpace optionName ppSpace "=" ppSpace protobuf_const ";"

/-!
type = "double" | "float" | "int32" | "int64" | "uint32" | "uint64"
      | "sint32" | "sint64" | "fixed32" | "fixed64" | "sfixed32" | "sfixed64"
      | "bool" | "string" | "bytes" | messageType | enumType
fieldNumber = intLit;
-/

syntax type :=
  &"double" <|>
  &"float" <|>
  &"int32" <|>
  &"int64" <|>
  &"uint32" <|>
  &"uint64" <|>
  &"sint32" <|>
  &"sint64" <|>
  &"fixed32" <|>
  &"fixed64" <|>
  &"sfixed32" <|>
  &"sfixed64" <|>
  &"bool" <|>
  &"string" <|>
  &"bytes" <|>
  dot_pident -- `enumType` parser is equivalent to this


/-!
field = [ "repeated" | "optional" ] type fieldName "=" fieldNumber [ "[" fieldOptions "]" ] ";"
fieldOptions = fieldOption { ","  fieldOption }
fieldOption = optionName "=" constant
-/
syntax fieldModifier := &"repeated" <|> &"optional"
syntax fieldOption := optionName ppSpace "=" ppSpace protobuf_const
syntax fieldOptions := fieldOption,+
syntax field := (fieldModifier ppSpace)? type ppSpace fieldName ppSpace "=" ppSpace intLit (ppSpace "[" fieldOptions "]")? ";"

run_meta do
  let s ← `(field| foo.Bar nested_message = 2;)
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

/-!
oneof = "oneof" oneofName "{" { option | oneofField } "}"
oneofField = type fieldName "=" fieldNumber [ "[" fieldOptions "]" ] ";"
-/
syntax oneofField := type ppSpace fieldName ppSpace "=" ppSpace intLit (ppSpace "[" fieldOptions "]")? ";"
syntax oneof := &"oneof" ppSpace oneofName "{" ppLine ((option <|> oneofField) ppLine)* "}"

run_meta do
  let s ← `(oneof|
    oneof foo {
      string name = 4;
      SubMessage sub_message = 9;
    })
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

/-!
mapField = "map" "<" keyType "," type ">" mapName "=" fieldNumber [ "[" fieldOptions "]" ] ";"
keyType = "int32" | "int64" | "uint32" | "uint64" | "sint32" | "sint64" |
          "fixed32" | "fixed64" | "sfixed32" | "sfixed64" | "bool" | "string"
-/
syntax keyType :=
  &"int32" <|>
  &"int64" <|>
  &"uint32" <|>
  &"uint64" <|>
  &"sint32" <|>
  &"sint64" <|>
  &"fixed32" <|>
  &"fixed64" <|>
  &"sfixed32" <|>
  &"sfixed64" <|>
  &"bool" <|>
  &"string"

syntax mapField := &"map" "<" keyType "," ppSpace type ">" ppSpace mapName ppSpace "=" ppSpace intLit (ppSpace "[" fieldOptions "]")? ";"

run_meta do
  let s ← `(mapField| map<string, Project> projects = 3;)
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

section

/-!
reserved = "reserved" ( ranges | strFieldNames ) ";"
ranges = range { "," range }
range =  intLit [ "to" ( intLit | "max" ) ]
strFieldNames = strFieldName { "," strFieldName }
strFieldName = "'" fieldName "'" | '"' fieldName '"'
-/

syntax strFieldName := strLit
syntax strFieldNames := strFieldName,+
syntax range := intLit (ppSpace &"to" ppSpace (intLit <|> &"max"))?
syntax ranges := range,+
syntax reserved := &"reserved" ppSpace (strFieldNames <|> ranges) ";"

run_meta do
  let s ← `(reserved| reserved 2, 15, 9 to 11;)
  let t ← `(reserved| reserved "foo", "bar";)
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk t}"

end

section

/-!
enum = "enum" enumName enumBody
enumBody = "{" { option | enumField | emptyStatement | reserved } "}"
enumField = ident "=" [ "-" ] intLit [ "[" enumValueOption { ","  enumValueOption } "]" ]";"
enumValueOption = optionName "=" constant
-/

syntax enumValueOption := optionName ppSpace "=" ppSpace protobuf_const
syntax enumField := pident ppSpace "=" ppSpace ("-")? intLit (ppSpace "[" enumValueOption,+ "]")? ";"
syntax enumBody := "{" ppLine ((option <|> reserved <|> enumField <|> emptyStatement) ppLine)* "}"
syntax enum := &"enum" ppSpace enumName ppSpace enumBody

run_meta do
  let s ← `(enum|
    enum EnumAllowingAlias {
      option allow_alias = true;
      EAA_UNSPECIFIED = 0;
      EAA_STARTED = 1;
      EAA_RUNNING = 2 [(custom_option) = "hello world"];
      reserved 2;
    }
    )
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

end

section

/-!
message = "message" messageName messageBody
messageBody = "{" { field | enum | message | option | oneof | mapField |
reserved | emptyStatement } "}"
-/

declare_syntax_cat message_body_entry (behavior := symbol)
-- `message` can occur in `messageBody`, thus we must use a category to prevent aggresive recursion

def messageBodyEntry := categoryParser `message_body_entry 0

syntax messageBody := "{" ppLine (messageBodyEntry ppLine)* "}"
syntax message := &"message" ppSpace messageName messageBody

syntax field : message_body_entry
syntax enum : message_body_entry
syntax message : message_body_entry
syntax option : message_body_entry
syntax oneof : message_body_entry
syntax mapField : message_body_entry
syntax reserved : message_body_entry
syntax emptyStatement : message_body_entry

run_meta do
  let s ← `(message| message Outer {
      option (my_option).a = true;
      message Inner {
        int64 ival = 1;
      }
      map<int32, string> my_map = 2;
    }
    )
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

run_meta do
  let s ← `(message| message Outer {
      T.A a = 1;
    }
    )
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

end

/-!
service = "service" serviceName "{" { option | rpc | emptyStatement } "}"
rpc = "rpc" rpcName "(" [ "stream" ] messageType ")" "returns" "(" [ "stream" ]
messageType ")" (( "{" {option | emptyStatement } "}" ) | ";")
-/

syntax rpc :=
  &"rpc" ppSpace rpcName ppSpace "(" (&"stream")? ppSpace messageType ")" ppSpace
    &"returns" ppSpace "(" (&"stream")? ppSpace messageType ")"
      (("{" (option <|> emptyStatement)* "}") <|> ";")

syntax service := &"service" ppSpace serviceName ppSpace "{" ppLine ((option <|> rpc <|> emptyStatement) ppLine)* "}"

run_meta do
  let s ← `(service|service SearchService {
    rpc Search (SearchRequest) returns (SearchResponse);
    })
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"

/-!
proto = [syntax] { import | package | option | topLevelDef | emptyStatement }
topLevelDef = message | enum | service
-/

syntax topLevelDef := message <|> enum <|> service
syntax proto := (syntaxSpec ppLine)? ((pimport <|> package <|> option <|> topLevelDef <|> emptyStatement) ppLine)*

run_meta do
  let s ← `(proto|syntax = "proto3";
    import public "other.proto";
    option java_package = "com.example.foo";
    enum EnumAllowingAlias {
      option allow_alias = true;
      EAA_UNSPECIFIED = 0;
      EAA_STARTED = 1;
      EAA_RUNNING = 1;
      EAA_FINISHED = 2 [(custom_option) = "hello world"];
    }
    message Outer {
      option (my_option).a = true;
      message Inner {
        int64 ival = 1;
      }
      repeated Inner inner_message = 2;
      EnumAllowingAlias enum_field = 3;
      map<int32, string> my_map = 4;
    }
  )
  println! "{← PrettyPrinter.ppTerm <| TSyntax.mk s}"
