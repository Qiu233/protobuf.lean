import Protobuf.Parser.Grammar
import Lake
open Lean Parser Elab Command

namespace Protobuf.Parser

syntax (name := loadProto) "#load_proto" str : command

@[command_elab loadProto]
def elabProto : CommandElab := fun stx => do
  let `(command| #load_proto $pathStx) := stx | throwUnsupportedSyntax
  let path := System.FilePath.mk pathStx.getString
  unless ← path.pathExists do
    throwErrorAt pathStx "file does not exist"
  let code ← IO.FS.readFile path
  let env ← getEnv
  let t := evalParserConst ``proto
  let ictx : InputContext := mkInputContext code path.toString
  let options ← getOptions
  let tt := getTokenTable env -- get current token table otherwise some token will fail
  let s := t.run ictx { env, options } tt (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    throwError "parsing of \"{path}\" failed with errors at {ictx.fileMap.toPosition s.pos}:\n{errorMsg}"
  let proto := s.stxStack.back
  let proto : TSyntax ``proto := TSyntax.mk proto
  println! "{proto}"

#check TSyntax.mk

#load_proto "Test/A.proto"
