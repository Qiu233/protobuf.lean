import Protobuf.Parser.Grammar

namespace Protobuf.Elab

open Lean Parser Elab Command

inductive ScopeKind where
  | package (files : List System.FilePath)
  | message (file : System.FilePath)
  | service (file : System.FilePath)
deriving Repr

def ScopeKind.getPath! : ScopeKind → System.FilePath
  | .package files => files.head!
  | .message file | .service file => file

-- structure Scope where
--   fullName : List String -- TODO: prevent storing the key
--   kind : ScopeKind
--   leaves : Array (System.FilePath × String) -- leaves are identifiers (with no dots) that are **not** scopes

inductive Scope where
  | scope (fullName : List String) (kind : ScopeKind)
  | leaf (fullName : List String) (file : System.FilePath)
deriving Repr

def Scope.fullName : Scope → List String
  | .scope x _ | .leaf x _ => x

def Scope.getPath! : Scope → System.FilePath
  | .scope _ x => x.getPath!
  | .leaf _ x => x

abbrev ProtoScopes := PrefixTree String Scope compare

structure Context where
  /-- name/path of the .proto file -/
  fileName : String
  -- /-- see `-IPATH` argument of protoc -/
  -- proto_paths : Array System.FilePath
  /-- to prevent cyclic import -/
  imported_chain : Std.HashSet String
  /-- the enclosing scope into which we add parsed stuff -/
  current_scope : List String

structure State where
  scopes : ProtoScopes := {}
  /-- to prevent parsing and loading the same file again and again -/
  cache : Std.HashMap String (TSyntax ``proto × ProtoScopes)

/-- M should provide all contextual information that is needed to translate a protobuf construct. -/
abbrev M := ReaderT Context <| StateRefT State CoreM

-- def load_and_parse (pathTk : Syntax) (dir : System.FilePath) : M (Array (TSyntax ``proto)) := do
--   let env ← getEnv
--   let options ← getOptions
--   let tt := getTokenTable env -- get current token table otherwise some token will fail
--   let pmctx : ParserModuleContext := {env, options}
--   unless ← dir.pathExists do
--     throwErrorAt pathTk "path \"{dir}\" does not exists"
--   let files ← dir.walkDir
--   files.mapM fun file => do
--     let code ←
--       try IO.FS.readFile file
--       catch e => throwError "failed to read file content from \"{file}\" due to error:\n{e.toMessageData}"
--     let parser := evalParserConst ``proto
--     let ictx : InputContext := mkInputContext code file.toString
--     let s := parser.run ictx pmctx tt (mkParserState ictx.input)
--     if let some errorMsg := s.errorMsg then
--       throwError "parsing of \"{file}\" failed with errors at {ictx.fileMap.toPosition s.pos}:\n{errorMsg}"
--     let proto := s.stxStack.back
--     return TSyntax.mk proto

def getFileName : M String := fun c => pure c.fileName

def load_and_parse (file : System.FilePath) : M (TSyntax ``proto) := do
  let env ← getEnv
  let options ← getOptions
  let tt := getTokenTable env -- get current token table otherwise some token will fail
  let pmctx : ParserModuleContext := {env, options}
  unless ← file.pathExists do
    throwError "file \"{file}\" does not exists"
  let code ←
    try IO.FS.readFile file
    catch e => throwError "failed to read file content from \"{file}\" due to error:\n{e.toMessageData}"
  let parser := evalParserConst ``proto
  let ictx : InputContext := mkInputContext code file.toString
  let s := parser.run ictx pmctx tt (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    throwError "parsing of \"{file}\" failed with errors at {ictx.fileMap.toPosition s.pos}:\n{errorMsg}"
  let proto := s.stxStack.back
  return TSyntax.mk proto

-- def merge_scopes (file : String) (a : ProtoScopes) : M Unit := do
--   let curr := (← get).scopes
--   let r ← a.foldM (init := curr) fun x c => do
--     let k := x.fullName
--     match c.find? k with
--     | none => return c.insert k x
--     | some v => -- now we shall merge the two `Scope`
--       match v.kind, x.kind with
--       | .package fs, .package fs' => -- both are packages
--         for (from', n) in x.leaves do
--           let fname := String.intercalate "." (k ++ [n])
--           if c.find? (k ++ [n]) |>.isSome then
--             throwError "{file}: \"{fname}\" is already defined in file \"{from'}}\"."
--           if v.leaves.any (fun p => p.2 == n) then
--             throwError "{file}: \"{fname}\" is already defined (as something other than a package) in file \"{from'}}\"."
--         return c.insert k {v with kind := .package (fs ++ fs').eraseDups, leaves := v.leaves.append x.leaves}
--       | .message from', _ | .service from', _ => -- cannot merge
--         throwError "{file}: \"{k}\" is already defined (as something other than a package) in file \"{from'}}\"."
--       | .package froms, _ => -- cannot merge
--         throwError "{file}: \"{k}\" is already defined in file \"{froms.head?.getD "unknown"}}\"."
--   modify fun s => {s with scopes := r}

private def _root_.Lean.TSyntax.toIdent (stx : TSyntax ``pident) : TSyntax `ident := TSyntax.mk stx.raw

@[specialize]
def withNestedScope {α} (s : String) (x : M α) : M α := fun c => do
  x ({c with current_scope := c.current_scope ++ [s]})

def join_pidents (ts : Syntax.TSepArray `Protobuf.Parser.pident ".") : Ident := Id.run do
  assert! ts.getElems.size != 0
  if ts.getElems.any (fun x => x.toIdent.getId.hasMacroScopes) then
    panic! "join_pidents: input cannot contain macro scopes"
  let ts := ts.getElems |>.map TSyntax.toIdent
  let ts := ts.flatMap fun x => (x.getId.components).toArray.map fun x => x.toString
  let t := ts.foldl (init := Name.anonymous) Name.str
  return Lean.mkIdent t

def resolve_message_enum_type (name : TSyntax ``dot_pident) : M (TSyntax ``dot_pident) := do
  let `(dot_pident| $[.%$leading_dot?]? $ts.*) := name | throwUnsupportedSyntax
  if leading_dot?.isSome then
    return name
  else
    sorry

def resolve_type (e : TSyntax ``type) : M (TSyntax ``type) := do
  match e with
  | `(type| double  )   => return e
  | `(type| float   )   => return e
  | `(type| int32   )   => return e
  | `(type| int64   )   => return e
  | `(type| uint32  )   => return e
  | `(type| uint64  )   => return e
  | `(type| sint32  )   => return e
  | `(type| sint64  )   => return e
  | `(type| fixed32 )   => return e
  | `(type| fixed64 )   => return e
  | `(type| sfixed32)   => return e
  | `(type| sfixed64)   => return e
  | `(type| bool    )   => return e
  | `(type| string  )   => return e
  | `(type| bytes   )   => return e
  | `(type| $name:dot_pident) =>
    let s ← resolve_message_enum_type name
    `(type| $s:dot_pident)
  | _ => throwUnsupportedSyntax

@[inline]
def intercalateName : List String → String := String.intercalate "."

syntax "throwProtoError " term:max ppSpace (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwProtoError $file:term $msg:interpolatedStr) => `(throwError "{$file}: {m! $msg}")
  | `(throwProtoError $file:term $msg:term)            => `(throwError "{$file}: {$msg}")

def throwIsAlreadyDefined (file : System.FilePath) (name : List String) (from' : System.FilePath) : M α := do
  throwProtoError file "{file}: \"{intercalateName name}\" is already defined in file \"{from'}}\"."

def throwIsAlreadyDefinedNotPackage (file : System.FilePath) (name : List String) (from' : System.FilePath) : M α := do
  throwProtoError file "{file}: \"{intercalateName name}\" is already defined (as something other than a package) in file \"{from'}}\"."

def find_scope_node? (k : List String) : M (Option Scope) := do
  let scopes := (← get).scopes
  return scopes.find? k

@[inline]
def insert_scope_raw (k : List String) (scope : Scope) : M Unit := do
  modify fun s => {s with scopes := s.scopes.insert k scope}

def insert_scope_nodup (file : System.FilePath) (name : String) (f : List String → System.FilePath → Scope) : M Unit := do
  let k := (← read).current_scope ++ [name]
  let s ← find_scope_node? k
  match s with
  | none => insert_scope_raw k (f k file)
  | some x =>
    match x with
    | .scope _ (.package paths) =>
      throwIsAlreadyDefined file k paths.head!
    | .scope _ kind =>
      throwIsAlreadyDefinedNotPackage file k kind.getPath!
    | .leaf _ file =>
      throwIsAlreadyDefinedNotPackage file k file

@[inline]
def insert_leaf (name : String) : M Unit := do
  insert_scope_nodup (← getFileName) name .leaf

@[inline]
def insert_message (name : String) : M Unit := do
  insert_scope_nodup (← getFileName) name (fun k file => .scope k (.message file))

@[inline]
def insert_package (name : String) : M Unit := do
  let file ← getFileName
  let k := (← read).current_scope ++ [name]
  let s ← find_scope_node? k
  match s with
  | none => insert_scope_raw k (.scope k (.package [file]))
  | some x =>
    match x with
    | .scope _ (.package paths) =>
      insert_scope_raw k (.scope k (.package <| paths ++ [System.FilePath.mk file]))
    | .scope _ kind =>
      throwIsAlreadyDefinedNotPackage file k kind.getPath!
    | .leaf _ file =>
      throwIsAlreadyDefinedNotPackage file k file

@[inline]
def insert_service (file : System.FilePath) (name : String) : M Unit := do
  insert_scope_nodup file name (fun k file => .scope k (.service file))

mutual

partial def preprocess_message_entry (e : TSyntax `message_body_entry) : M Unit := do
  match e with
  | `(message_body_entry| $m:message) =>
    preprocess_message m
  | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) =>
    insert_leaf name.toIdent.getId.toString
  | _ => pure ()

partial def preprocess_message (stx : TSyntax ``message) : M Unit := do
  let `(message| message $name:pident { $entries* }) := stx | throwUnsupportedSyntax
  let id := name.toIdent
  insert_message id.getId.toString
  withNestedScope id.getId.toString do
    entries.forM preprocess_message_entry

end

def preprocess_options (code : TSyntax ``proto) : M Unit := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax

def preprocess_enum (code : TSyntax ``enum) : M Unit := do
  let `(enum| enum $name:pident $body:enumBody) := code | throwUnsupportedSyntax

def preprocess_service (code : TSyntax ``service) : M Unit := do
  let `(service| service $name:pident { $ts* }) := code | throwUnsupportedSyntax

def preprocess_top_level_defs (code : TSyntax ``proto) : M Unit := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  ts.forM fun t => do
    match t with
    | `(topLevelDef| $m:message) =>
      preprocess_message m
    | `(topLevelDef| $m:enum) =>
      preprocess_enum m
    | `(topLevelDef| $m:service) =>
      preprocess_service m
    | _ => pure ()

def preprocess_package (code : TSyntax ``proto) : M (List String) := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  let ts := ts.filter fun s => s.raw.getKind == ``package
  if ts.size = 0 then
    return []
  if ts.size > 1 then
    throwProtoError (← getFileName) "multiple package declarations."
  let t := ts[0]!
  match t with
  | `(package| package $ns.* ;) =>
    let parts := ns.getElems.map fun x => x.toIdent.getId.toString
    return parts.toList
  | _ => throwUnsupportedSyntax

def f : M Unit := do
  let p ← load_and_parse "Test/C.proto"
  let pack ← preprocess_package p
  withReader (fun c => {c with current_scope := pack}) do
    preprocess_top_level_defs p

run_meta do
  let (_, r) ← f { fileName := "Test/C.proto", current_scope := [], imported_chain := {} } |>.run { cache := {} }
  -- println! "{r.scopes}"
  r.scopes.forM fun x => do
    println! "{intercalateName x.fullName}"

-- def process_message_entry (e : TSyntax `message_body_entry) : M (TSyntax `message_body_entry) := do
--   match e with
--   | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) =>
--     let type ← resolve_type type
--     `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;)
--   | _ => throwUnsupportedSyntax

-- def process_message (stx : TSyntax ``message) : M (TSyntax ``message) := do
--   let `(message| message $name:pident { $entries* }) := stx | throwUnsupportedSyntax
--   let id := name.toIdent
--   let entries ← withNestedScope id.getId.toString <| entries.mapM process_message_entry
--   `(message| message $name:pident { $entries* })

-- def process_options (code : TSyntax ``proto) : M Unit := do
--   let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
--   for t in ts do
--     match t with
--     | `(option| option $name:optionName = $val;) => throwError "process_options not implemented yet"
--     | _ => continue

-- def process_enum (code : TSyntax ``enum) : M (TSyntax ``enum) := do
--   pure code

-- def process_service (code : TSyntax ``service) : M (TSyntax ``service) := do
--   pure code

-- def process_top_level_defs (code : TSyntax ``proto) : M (TSyntax ``proto) := do
--   let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
--   let ts ← ts.mapM (β := TSyntax
--                   [`Protobuf.Parser.pimport, `Protobuf.Parser.package, `Protobuf.Parser.option, `Protobuf.Parser.topLevelDef,
--                     `Protobuf.Parser.emptyStatement]) fun (t : TSyntax
--                         [`Protobuf.Parser.pimport, `Protobuf.Parser.package, `Protobuf.Parser.option, `Protobuf.Parser.topLevelDef,
--                           `Protobuf.Parser.emptyStatement]) => do
--     match t with
--     | `(topLevelDef| $m:message) =>
--       let m ← process_message m
--       `(topLevelDef| $m:message)
--     | `(topLevelDef| $m:enum) =>
--       let m ← process_enum m
--       `(topLevelDef| $m:enum)
--     | `(topLevelDef| $m:service) =>
--       let m ← process_service m
--       `(topLevelDef| $m:service)
--     | _ => pure t
--   `(proto| $[$stxSpec?]? $ts*)

-- mutual

-- partial def load_proto (file : System.FilePath) : M (TSyntax ``proto) := do
--   let proto ← load_and_parse file
--   process_header proto
--   -- now the scopes are checked and merged
--   process_options proto
--   process_top_level_defs proto

-- partial def process_header (code : TSyntax ``proto) : M Unit := do
--   let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
--   let imports := ts.filter fun x => x.raw.getKind == ``pimport
--   let packageDecl := ts.filter fun x => x.raw.getKind == ``package
--   let currentFile ← getFileName
--   if packageDecl.size > 1 then
--     throwError "{currentFile}: multiple package definitions."
--   let importFiles ← imports.mapM fun x => do
--     match x with
--       | `(pimport| import $[$kind]? $file;) =>
--         match kind with
--         | none => return file.getString.trim
--         | some k =>
--           match k with
--           | `(importKind| public) => return file.getString.trim
--           | `(importKind| weak) => throwError "{currentFile}: weak import is not currently supported."
--           | _ => throwUnsupportedSyntax
--       | _ => unreachable!
--   if !importFiles.allDiff then
--     throwError "{currentFile}: duplicate imports to the same file."
--   let newChain := (← read).imported_chain.insert currentFile
--   importFiles.forM fun i => do
--     if newChain.contains i then
--       throwError "cyclic imports detected for {i}"
--     let subCtx : Context := { fileName := i, imported_chain := newChain, current_scope := [] }
--     let cache := (← get).cache
--     let (processed, r) ← load_proto i subCtx |>.run { cache := (← get).cache } -- only carry the cache
--     let scopes := r.scopes
--     modify (fun s => {s with cache := s.cache.insert i (processed, scopes)}) -- update the cache
--     merge_scopes i scopes

-- end

#exit


syntax (name := loadProto) "#load_proto" str : command

@[command_elab loadProto]
def elabProto : CommandElab := fun stx => do
  let `(command| #load_proto $pathStx) := stx | throwUnsupportedSyntax
  let path := System.FilePath.mk pathStx.getString
  -- load_and_parse pathStx path
  sorry

-- #load_proto "Test"

-- instance : Default Int32 where
--   pdefault := 0

-- structure A where
--   a : Option String := none -- optional string
--   b : Int32 := pdefault -- int32

-- set_option hygiene false in
-- run_meta do
--   let s ← `(fullIdent| x.y.z)
--   let `(fullIdent| $ts.*) := s | return
--   println! "{join_pidents ts}"

#check Syntax

run_meta do
  let s ← `(decl_name%)
  println! "{s}"

#exit

def translate_message_entry (e : TSyntax `message_body_entry) : M Unit := do
  match e with
  | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) =>
    let id := name.toIdent
    -- let s ← `(structure $id where)
    let s ← `(structSimpleBinder| $id:ident : T)
    pure ()
  | _ => throwUnsupportedSyntax

#check structFields

def translate_message (stx : TSyntax ``message) : M Unit := do
  let `(message| message $name:pident { $entries* }) := stx | throwUnsupportedSyntax
  let id := name.toIdent
  let r ← entries.mapM translate_message_entry
  pure ()

run_meta do
  let msg ← `(message|
    message Test {
      optional string a = 1;
      int32 outer = 2;
    }
  )
  translate_message msg
