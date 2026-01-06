module

public section

namespace Protobuf.Notation

declare_syntax_cat options_value (behavior := symbol)

syntax ident : options_value
syntax str : options_value
syntax &"true" : options_value
syntax &"false" : options_value
syntax scientific : options_value
syntax "-" scientific : options_value
syntax "+" scientific : options_value
syntax num : options_value
syntax "-" num : options_value
syntax "+" num : options_value

syntax options_entry := ident " = " options_value

syntax options := "[" options_entry,*,? "]"


syntax enum_entry := ident " = " num ";"

syntax (name := enumDec) "enum " ident (options)? " {" ppLine (enum_entry ppLine)* "}" : command


syntax message_entry_modifier := &"optional" <|> &"repeated" <|> &"required"

syntax message_field_type_normal := ident
syntax message_field_type_map := &"map" "<" ident "," ident ">"

syntax message_field_type := message_field_type_map <|> message_field_type_normal

syntax message_entry := (message_entry_modifier)? message_field_type ident " = " num (options)? ";"

syntax (name := messageDec) "message " ident (options)? " {" ppLine (message_entry ppLine)* "}" : command

syntax (name := oneofDec) "oneof " ident " {" ppLine (message_entry ppLine)*  "}" : command

syntax proto_decl := enumDec <|> messageDec <|> oneofDec

syntax (name := proto_mutual_stx) "proto_mutual " "{" ppLine (proto_decl ppLine)* "}" : command

namespace PrettyPrinter

open Lean

private def extract_num : TSyntax `num → String := fun x => x.raw[0].isIdOrAtom?.getD (panic! "num")

private def extract_id : TSyntax `ident → String := fun x => x.getId.toString

def options_value.pprint : TSyntax `options_value → String
  | `(options_value| $x:ident) => s!"{extract_id x}"
  | `(options_value| $x:scientific) => s!"{x.raw[0].isIdOrAtom?.getD (panic! "scientific")}"
  | `(options_value| -$x:scientific) => s!"-{x.raw[0].isIdOrAtom?.getD (panic! "-scientific")}"
  | `(options_value| +$x:scientific) => s!"+{x.raw[0].isIdOrAtom?.getD (panic! "+scientific")}"
  | `(options_value| $x:num) => extract_num x
  | `(options_value| -$x:num) => s!"-{extract_num x}"
  | `(options_value| +$x:num) => s!"+{extract_num x}"
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

def enum_entry.pprint : TSyntax ``enum_entry → String
  | `(enum_entry| $x = $n:num;) => s!"{extract_id x} = {extract_num n};"
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
