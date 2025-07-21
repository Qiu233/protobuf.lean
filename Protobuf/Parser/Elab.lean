import Protobuf.Parser.Grammar

namespace Protobuf.Elab

open Lean Parser Elab Command

inductive ScopeKind where
  | package (files : List System.FilePath)
  | message (file : System.FilePath)
  | service (file : System.FilePath)
deriving Repr

inductive LeafKind where
  /--
  A field that is not a `map<.., ..>`.
  The only possibilities are
  * fields of scalar type
  * fields of message type
  * fields of enum type
  * fields of oneof type
  -/
  | field
  /-- A oneof declaration. -/
  | oneof
  /-- An rpc declaration inside a service body. -/
  | rpc
  /-- An enum declaration. -/
  | enum
deriving Repr

def ScopeKind.getPath! : ScopeKind → System.FilePath
  | .package files => files.head!
  | .message file | .service file => file

inductive Scope where
  | scope (fullName : List String) (kind : ScopeKind)
  | leaf (fullName : List String) (kind : LeafKind) (file : System.FilePath)
deriving Repr

def Scope.fullName : Scope → List String
  | .scope x _ | .leaf x _ _  => x

def Scope.getPath! : Scope → System.FilePath
  | .scope _ x => x.getPath!
  | .leaf _ _ x => x

abbrev ProtoScopes := PrefixTree String Scope compare

structure Context where
  /-- name/path of the .proto file -/
  fileName : String := ""
  /-- see `-IPATH` argument of protoc -/
  proto_paths : List System.FilePath := []
  /-- to prevent cyclic import -/
  imported_chain : Std.HashSet String := {}
  /-- the enclosing scope into which we add parsed stuff -/
  current_scope : List String := []

structure State where
  -- the accumulative trie of scope and names
  scopes : ProtoScopes := {}
  /-- to prevent parsing and loading the same file again and again -/
  cache : Std.HashMap String (TSyntax ``proto × ProtoScopes)

/-- M should provide all contextual information that is needed to translate a protobuf construct. -/
abbrev M := ReaderT Context <| StateRefT State CoreM

syntax "throwProtoError " term:max ppSpace (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwProtoError $file:term $msg:interpolatedStr) => `(throwError "{$file}: {m! $msg}")
  | `(throwProtoError $file:term $msg:term)            => `(throwError "{$file}: {$msg}")

def getFileName : M String := fun c => pure c.fileName

def resolve_file (fileName : String) : M System.FilePath := do
  let mut paths := (← read).proto_paths
  if paths.isEmpty then
    paths := ["."]
  let cdds := paths.map fun x => x.join (System.FilePath.mk fileName)
  for cdd in cdds do
    unless ← cdd.pathExists do
      continue
    if ← cdd.isDir then
      continue
    return cdd
  throwProtoError (← getFileName) "no file \"{fileName}\" can be resolved with accordance to search paths"

def load_and_parse (fileName : String) : M (TSyntax ``proto) := do
  let file ← resolve_file fileName
  let code ←
    try IO.FS.readFile file
    catch e => throwError "failed to read file content from \"{file}\" due to error:\n{e.toMessageData}"
  let env ← getEnv
  let options ← getOptions
  let tt := getTokenTable env -- get current token table otherwise some token will fail
  let pmctx : ParserModuleContext := {env, options}
  let parser := evalParserConst ``proto
  let ictx : InputContext := mkInputContext code file.toString
  let s := parser.run ictx pmctx tt (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    throwError "parsing of \"{file}\" failed with errors at {ictx.fileMap.toPosition s.pos}:\n{errorMsg}"
  let proto := s.stxStack.back
  return TSyntax.mk proto

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

@[inline]
def intercalateName : List String → String := String.intercalate "."

def throwIsAlreadyDefined (file : System.FilePath) (name : List String) (from' : System.FilePath) : M α := do
  throwProtoError file "\"{intercalateName name}\" is already defined in file \"{from'}\"."

def throwIsAlreadyDefinedNotPackage (file : System.FilePath) (name : List String) (from' : System.FilePath) : M α := do
  throwProtoError file "\"{intercalateName name}\" is already defined (as something other than a package) in file \"{from'}\"."

def find_scope_node? (k : List String) : M (Option Scope) := do
  let scopes := (← get).scopes
  return scopes.find? k

@[inline]
def insert_scope_raw (k : List String) (scope : Scope) : M Unit := do
  modify fun s => {s with scopes := s.scopes.insert k scope}

@[specialize]
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
    | .leaf _ _ file =>
      throwIsAlreadyDefinedNotPackage file k file

@[inline]
def insert_leaf (name : String) (kind : LeafKind) : M Unit := do
  insert_scope_nodup (← getFileName) name (.leaf · kind ·)

@[inline]
def insert_message (name : String) : M Unit := do
  insert_scope_nodup (← getFileName) name (fun k file => .scope k (.message file))

@[inline]
def insert_package (parts : List String) : M Unit := do
  let file ← getFileName
  let mut k := []
  for p in parts do
    k := k ++ [p]
    let s ← find_scope_node? k
    match s with
    | none => insert_scope_raw k (.scope k (.package [file]))
    | some x =>
      match x with
      | .scope _ (.package paths) =>
        insert_scope_raw k (.scope k (.package <| paths ++ [System.FilePath.mk file]))
      | .scope _ kind =>
        throwIsAlreadyDefinedNotPackage file k kind.getPath!
      | .leaf _ _ file =>
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
    insert_leaf name.toIdent.getId.toString .field
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
    let k := parts.toList
    insert_package k
    return k
  | _ => throwUnsupportedSyntax

--

private def to_fully_qualified_pidents (parts : List String) : M <| (TSyntax ``dot_pident) := do
  let ts : TSyntaxArray ``pident ← parts.toArray.mapM fun x => do
    let p := Lean.mkIdent (Name.mkSimple x)
    return TSyntax.mk p.raw
  `(dot_pident| .$ts.*)

@[specialize]
def resolve_core_loop {α} (f : List String → M (Option α)) : M (Option α) := do
  let mut current_scope := (← read).current_scope
  while True do
    if let some r ← f current_scope then
      return some r
    if current_scope.isEmpty then -- we must check again when it is emtpy
      break
    current_scope := current_scope.take (current_scope.length - 1) -- go up
  return none

@[specialize]
def resolve_single {α} (name : String) (f : List String → Scope → M (Option α)) : M (Option (Scope × α)) := do
  resolve_core_loop fun s => do
    let k := s ++ [name]
    let scopes := (← get).scopes
    if let some r := scopes.find? k then
      if let some a ← f k r then
        return some (r, a)
    return none

def resolve_scope (name : String) : M (Option (Scope × List String)) := do
  resolve_single name fun k s => do
    match s with
    | (.scope _ _) => return some k
    | _ => return none

private def pidents_to_ident (stx : TSyntaxArray ``pident) : M <| TSyntax `ident := do
  let ts := stx.map fun x => x.toIdent.getId.toString
  let n := ts.foldl (init := Name.anonymous) Name.str
  return mkIdent n

@[specialize]
def resolve_core (name : TSyntax ``dot_pident) (f : List String → Scope → M Bool) (errNotFound : {α : Type} → String → M α) : M (TSyntax ``dot_pident) := do
  let `(dot_pident| $[.%$leading_dot?]? $ts.*) := name | throwUnsupportedSyntax
  if leading_dot?.isSome then
    return name
  else
    let parts := ts.getElems
    if h' : parts.size ≤ 1 then
      if h0 : parts.size = 0 then
        throwProtoError (← getFileName) "resolve_core: impossible, input name has no parts"
      else -- unqualified, like `A`
        let last := parts[0]
        let n := last.toIdent.getId.toString
        let r? ← resolve_single n fun k s => do
          if ← f k s then
            return some k
          else return none
        if let some (r, k) := r? then
          return ← to_fully_qualified_pidents k
        else
          errNotFound n
    else -- partially qualified, like `A.B`
      let pname := (← pidents_to_ident parts).getId.toString
      let some (scope, k) ← resolve_scope parts[0].toIdent.getId.toString |
        throwProtoError (← getFileName) "failed to resolve package, message, or service with name \"{pname}\"" -- this error message cannot be redirected
      let tail := parts.toList.tail.map fun x => x.toIdent.getId.toString
      let scopes := (← get).scopes
      let k := k ++ tail
      if let some r := scopes.find? k then
        if ← f k r then
          return ← to_fully_qualified_pidents k
      errNotFound pname

def resolve_message_enum_type (name : TSyntax ``dot_pident) : M (TSyntax ``dot_pident) := do
  resolve_core name (fun _ s => return s matches (.scope _ (ScopeKind.message _)) | (.leaf _ (LeafKind.enum) _))
    (fun n => do throwProtoError (← getFileName) "failed to resolve message or enum with name \"{n}\"")

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

mutual

partial def process_message_entry (e : TSyntax `message_body_entry) : M (TSyntax `message_body_entry) := do
  match e with
  | `(message_body_entry| $m:message) =>
    let m ← process_message m
    `(message_body_entry| $m:message)
  | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) =>
    let type ← resolve_type type
    `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;)
  | _ => throwUnsupportedSyntax

partial def process_message (stx : TSyntax ``message) : M (TSyntax ``message) := do
  let `(message| message $name:pident { $entries* }) := stx | throwUnsupportedSyntax
  let id := name.toIdent
  let entries ← withNestedScope id.getId.toString <| entries.mapM process_message_entry
  `(message| message $name:pident { $entries* })

end

def process_options (code : TSyntax ``proto) : M Unit := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  for t in ts do
    match t with
    | `(option| option $name:optionName = $val;) => throwError "process_options not implemented yet"
    | _ => continue

def process_enum (code : TSyntax ``enum) : M (TSyntax ``enum) := do
  pure code

def process_service (code : TSyntax ``service) : M (TSyntax ``service) := do
  pure code

def process_top_level_defs (code : TSyntax ``proto) : M (TSyntax ``proto) := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  let ts ← ts.mapM (β := TSyntax
                  [`Protobuf.Parser.pimport, `Protobuf.Parser.package, `Protobuf.Parser.option, `Protobuf.Parser.topLevelDef,
                    `Protobuf.Parser.emptyStatement]) fun (t : TSyntax
                        [`Protobuf.Parser.pimport, `Protobuf.Parser.package, `Protobuf.Parser.option, `Protobuf.Parser.topLevelDef,
                          `Protobuf.Parser.emptyStatement]) => do
    match t with
    | `(topLevelDef| $m:message) =>
      let m ← process_message m
      `(topLevelDef| $m:message)
    | `(topLevelDef| $m:enum) =>
      let m ← process_enum m
      `(topLevelDef| $m:enum)
    | `(topLevelDef| $m:service) =>
      let m ← process_service m
      `(topLevelDef| $m:service)
    | _ => pure t
  `(proto| $[$stxSpec?]? $ts*)

def merge_scopes (file : String) (a : ProtoScopes) : M Unit := do
  let curr := (← get).scopes
  let r ← a.foldM (init := curr) fun x c => do
    let k := x.fullName
    match c.find? k with
    | none => return c.insert k x
    | some v => -- now we shall merge the two `Scope`
      match v, x with
      | .scope _ (.package paths), .scope _ (.package paths') =>
        return c.insert k (.scope k (.package (paths ++ paths').eraseDups))
      | .scope _ (.package paths), _ =>
        throwIsAlreadyDefined file k paths.head!
      | .scope _ kind, _ =>
        throwIsAlreadyDefinedNotPackage file k kind.getPath!
      | .leaf _ _ file, _ =>
        throwIsAlreadyDefinedNotPackage file k file
  modify fun s => {s with scopes := r}

mutual

partial def load_proto (file : String) : M (TSyntax ``proto) := do
  withReader (fun s => {s with fileName := file}) do
    let proto ← load_and_parse file
    process_header proto
    -- now the scopes are checked and merged
    process_options proto
    let pack ← preprocess_package proto
    withReader (fun c => {c with current_scope := pack}) do
      preprocess_top_level_defs proto
      process_top_level_defs proto

partial def process_header (code : TSyntax ``proto) : M Unit := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  let imports := ts.filter fun x => x.raw.getKind == ``pimport
  let packageDecl := ts.filter fun x => x.raw.getKind == ``package
  let currentFile ← getFileName
  if packageDecl.size > 1 then
    throwError "{currentFile}: multiple package definitions."
  let importFiles ← imports.mapM fun x => do
    match x with
      | `(pimport| import $[$kind]? $file;) =>
        match kind with
        | none => return file.getString.trim
        | some k =>
          match k with
          | `(importKind| public) => return file.getString.trim
          | `(importKind| weak) => throwError "{currentFile}: weak import is not currently supported."
          | _ => throwUnsupportedSyntax
      | _ => unreachable!
  if !importFiles.allDiff then
    throwError "{currentFile}: duplicate imports to the same file."
  let newChain := (← read).imported_chain.insert currentFile
  importFiles.forM fun i => do
    if newChain.contains i then
      throwError "cyclic imports detected for {i}"
    let paths := (← read).proto_paths
    let subCtx : Context := { imported_chain := newChain, proto_paths := paths }
    let cache := (← get).cache
    if let some _ := cache[i]? then
      return -- do not merge scopes, it is already in cache which means we have already merged it
    else
      let (processed, r) ← load_proto i subCtx |>.run { cache := cache } -- only carry the cache
      let scopes := r.scopes
      modify (fun s => {s with cache := s.cache.insert i (processed, scopes)}) -- update the cache
      merge_scopes i scopes

end

run_meta do
  let (r, s) ← load_proto "E.proto" { proto_paths := ["Test"] } |>.run {cache := {}}
  s.scopes.forM fun x => do
    println! "{intercalateName x.fullName}"
  println! "{r}"
