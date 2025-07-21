import Protobuf.Parser.Grammar

namespace Protobuf.Elab

open Lean Parser Elab Command

section

@[specialize]
private partial def _root_.Lean.PrefixTreeNode.foldMatchingM' {m α β σ}
  [Monad m] (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) (init : σ) (f : List α → β → σ → m σ) : m σ :=
  let rec fold : PrefixTreeNode α β → σ → List α → m σ
    | PrefixTreeNode.Node b? n, d, k => do
      let d ← match b? with
        | none   => pure d
        | some b => f k.reverse b d
      n.foldM (init := d) fun d a t => fold t d (a :: k)
  let rec find : List α → List α → PrefixTreeNode α β → σ → m σ := fun ks r t d => do
    match ks, t, d with
    | [],    t, d => fold t d r
    | k::ks, PrefixTreeNode.Node _ m, d =>
      match RBNode.find cmp m k with
      | none   => pure init
      | some t => find ks (k :: r) t d
  find k [] t init

@[inline]
private def _root_.Lean.PrefixTree.foldMatchingM' [Monad m] (t : PrefixTree α β p) (k : List α) (init : σ) (f : List α → β → σ → m σ) : m σ :=
  t.val.foldMatchingM' p k init f

@[inline]
private def _root_.Lean.PrefixTree.foldM' [Monad m] (t : PrefixTree α β p) (init : σ) (f : List α → β → σ → m σ) : m σ :=
  t.foldMatchingM' [] init f

@[inline]
private def _root_.Lean.PrefixTree.forMatchingM' [Monad m] (t : PrefixTree α β p) (k : List α) (f : List α → β → m Unit) : m Unit :=
  t.val.foldMatchingM' p k () (fun k b _ => f k b)

@[inline]
private def _root_.Lean.PrefixTree.forM' [Monad m] (t : PrefixTree α β p) (f : List α → β → m Unit) : m Unit :=
  t.forMatchingM' [] f

end

abbrev PName := List String

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
  | mapField
  | reserved
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

inductive NameNode where
  | scope (kind : ScopeKind)
  | leaf (kind : LeafKind) (file : System.FilePath)
deriving Repr

-- def NameNode.fullName : NameNode → PName
--   | .scope x _ | .leaf x _ _  => x

def NameNode.getPath! : NameNode → System.FilePath
  | .scope x => x.getPath!
  | .leaf _ x => x

abbrev ProtoScopes := PrefixTree String NameNode compare

structure FileCache where
  file : String
  /-- the syntax names of which have been resolved to fully qualified form, that is, with a leading dot -/
  processed : TSyntax ``proto
  /-- the imported and defined symbols -/
  scopes : ProtoScopes

structure Context where
  /-- name/path of the .proto file -/
  fileName : String := ""
  /-- see `-IPATH` argument of protoc -/
  proto_paths : List System.FilePath := []
  /-- to prevent cyclic import -/
  imported_chain : Std.HashSet String := {}
  /-- the enclosing scope into which we add parsed stuff -/
  current_scope : PName := []

structure State where
  -- the accumulative trie of scope and names
  scopes : ProtoScopes := {}
  /-- to prevent parsing and loading the same file again and again -/
  cache : Std.HashMap String FileCache

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
def intercalateName : PName → String := String.intercalate "."

def throwIsAlreadyDefined (file : System.FilePath) (name : PName) (from' : System.FilePath) : M α := do
  throwProtoError file "\"{intercalateName name}\" is already defined in file \"{from'}\"."

def throwIsAlreadyDefinedNotPackage (file : System.FilePath) (name : PName) (from' : System.FilePath) : M α := do
  throwProtoError file "\"{intercalateName name}\" is already defined (as something other than a package) in file \"{from'}\"."

def find_scope_node? (k : PName) : M (Option NameNode) := do
  let scopes := (← get).scopes
  return scopes.find? k

@[inline]
def insert_scope_raw (k : PName) (scope : NameNode) : M Unit := do
  modify fun s => {s with scopes := s.scopes.insert k scope}

@[specialize]
def insert_scope_nodup (file : System.FilePath) (name : String) (f : System.FilePath → NameNode) : M Unit := do
  let k := (← read).current_scope ++ [name]
  let s ← find_scope_node? k
  match s with
  | none => insert_scope_raw k (f file)
  | some x =>
    match x with
    | .scope (.package paths) =>
      throwIsAlreadyDefined file k paths.head!
    | .scope kind =>
      throwIsAlreadyDefinedNotPackage file k kind.getPath!
    | .leaf _ file =>
      throwIsAlreadyDefinedNotPackage file k file

@[inline]
def insert_leaf (name : String) (kind : LeafKind) : M Unit := do
  insert_scope_nodup (← getFileName) name (.leaf kind ·)

@[inline]
def insert_message (name : String) : M Unit := do
  insert_scope_nodup (← getFileName) name (fun file => .scope (.message file))

@[inline]
def insert_package (parts : PName) : M Unit := do
  let file ← getFileName
  let mut k := []
  for p in parts do
    k := k ++ [p]
    let s ← find_scope_node? k
    match s with
    | none => insert_scope_raw k (.scope (.package [file]))
    | some x =>
      match x with
      | .scope (.package paths) =>
        insert_scope_raw k (.scope (.package <| paths ++ [System.FilePath.mk file]))
      | .scope kind =>
        throwIsAlreadyDefinedNotPackage file k kind.getPath!
      | .leaf _ file =>
        throwIsAlreadyDefinedNotPackage file k file


@[inline]
def insert_service (name : String) : M Unit := do
  insert_scope_nodup (← getFileName) name (fun file => .scope (.service file))

mutual

partial def preprocess_message_entry (e : TSyntax `message_body_entry) : M Unit := do
  match e with
  | `(message_body_entry| $m:message) =>
    preprocess_message m
  | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) =>
    insert_leaf name.toIdent.getId.toString .field
  | `(message_body_entry| enum $name:pident $body:enumBody) =>
    insert_leaf name.toIdent.getId.toString .enum
  | `(message_body_entry| map<$k,$v> $name:pident = $num:intLit $[[$options?]]?;) =>
    insert_leaf name.toIdent.getId.toString .mapField
  | `(message_body_entry| reserved $ts,*;) =>
    for t in ts.getElems do
      let `(strFieldName| $s:str) := t | continue
      let n := s.getString
      unless n.all (fun c => c.isAlpha || c.isDigit || c == '_') do
        throwProtoError (← getFileName) "{n} is not a valid reserved name"
      insert_leaf n .reserved
  | `(message_body_entry| option $name:optionName = $c:protobuf_const;) =>
    pure ()
  | `(message_body_entry| ;)
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
  let `(enum| enum $name:pident {$body*}) := code | throwUnsupportedSyntax
  let id := name.toIdent
  insert_leaf id.getId.toString .enum

def preprocess_service (code : TSyntax ``service) : M Unit := do
  let `(service| service $name:pident { $body* }) := code | throwUnsupportedSyntax
  let id := name.toIdent
  insert_service id.getId.toString
  withNestedScope id.getId.toString do
    for b in body do
      match b with
      | `(rpc| rpc $name:pident ( $[stream]? $typed:dot_pident ) returns ( $[stream]? $typer:dot_pident ) {$body*})
      | `(rpc| rpc $name:pident ( $[stream]? $typed:dot_pident ) returns ( $[stream]? $typer:dot_pident );) =>
        insert_leaf name.toIdent.getId.toString .rpc
      | `(option| option $name:optionName = $c:protobuf_const;)
      | `(emptyStatement| ;)
      | _ => pure ()

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

def preprocess_package (code : TSyntax ``proto) : M PName := do
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

private def to_fully_qualified_pidents (parts : PName) : M <| (TSyntax ``dot_pident) := do
  let ts : TSyntaxArray ``pident ← parts.toArray.mapM fun x => do
    let p := Lean.mkIdent (Name.mkSimple x)
    return TSyntax.mk p.raw
  `(dot_pident| .$ts.*)

@[specialize]
def resolve_core_loop {α} (f : PName → M (Option α)) : M (Option α) := do
  let mut current_scope := (← read).current_scope
  while True do
    if let some r ← f current_scope then
      return some r
    if current_scope.isEmpty then -- we must check again when it is emtpy
      break
    current_scope := current_scope.take (current_scope.length - 1) -- go up
  return none

@[specialize]
def resolve_single {α} (name : String) (f : PName → NameNode → M (Option α)) : M (Option (NameNode × α)) := do
  resolve_core_loop fun s => do
    let k := s ++ [name]
    let scopes := (← get).scopes
    if let some r := scopes.find? k then
      if let some a ← f k r then
        return some (r, a)
    return none

def resolve_scope (name : String) : M (Option (NameNode × PName)) := do
  resolve_single name fun k s => do
    match s with
    | (.scope _) => return some k
    | _ => return none

private def pidents_to_ident (stx : TSyntaxArray ``pident) : CoreM <| TSyntax `ident := do
  let ts := stx.map fun x => x.toIdent.getId.toString
  let n := ts.foldl (init := Name.anonymous) Name.str
  return mkIdent n

@[specialize]
def resolve_core (name : TSyntax ``dot_pident) (f : PName → NameNode → M Bool) (errNotFound : {α : Type} → String → M α) : M (TSyntax ``dot_pident) := do
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
  resolve_core name (fun _ s => return s matches (.scope (ScopeKind.message _)) | (.leaf (LeafKind.enum) _))
    (fun n => do throwProtoError (← getFileName) "failed to resolve message or enum with name \"{n}\"")

def resolve_type (e : TSyntax ``type) : M (TSyntax ``type) := do
  match e with
  | `(type| double  )
  | `(type| float   )
  | `(type| int32   )
  | `(type| int64   )
  | `(type| uint32  )
  | `(type| uint64  )
  | `(type| sint32  )
  | `(type| sint64  )
  | `(type| fixed32 )
  | `(type| fixed64 )
  | `(type| sfixed32)
  | `(type| sfixed64)
  | `(type| bool    )
  | `(type| string  )
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
  | `(message_body_entry| enum $name:pident $body:enumBody) =>
    return e
  | `(message_body_entry| map<$k,$v> $name:pident = $num:intLit $[[$options?]]?;) =>
    let v ← resolve_type v
    `(message_body_entry| map<$k,$v> $name:pident = $num:intLit $[[$options?]]?;)
  | `(message_body_entry| reserved $ts,*;) =>
    return e
  | `(message_body_entry| option $name:optionName = $c:protobuf_const;)
  | `(message_body_entry| ;) => return e
  | _ => return e

partial def process_message (stx : TSyntax ``message) : M (TSyntax ``message) := do
  let `(message| message $name:pident { $entries* }) := stx | throwUnsupportedSyntax
  let id := name.toIdent
  let entries ← withNestedScope id.getId.toString <| entries.mapM process_message_entry
  `(message| message $name:pident { $entries* })

end

def process_options (code : TSyntax ``proto) : M Unit := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax

def process_enum (code : TSyntax ``enum) : M (TSyntax ``enum) := do
  pure code

def process_service (code : TSyntax ``service) : M (TSyntax ``service) := do
  let `(service| service $name:pident { $body* }) := code | throwUnsupportedSyntax
  withNestedScope name.toIdent.getId.toString do
    let body ← body.mapM (β := TSyntax [`Protobuf.Parser.option, `Protobuf.Parser.rpc, `Protobuf.Parser.emptyStatement]) fun (b : TSyntax [`Protobuf.Parser.option, `Protobuf.Parser.rpc, `Protobuf.Parser.emptyStatement]) => do
      match b with
      | `(rpc| rpc $name:pident ( $[stream%$tk1]? $typed:dot_pident ) returns ( $[stream%$tk2]? $typer:dot_pident ) {$body*}) =>
        let typed ← resolve_message_enum_type typed
        let typer ← resolve_message_enum_type typer
        `(rpc| rpc $name:pident ( $[stream%$tk1]? $typed:dot_pident ) returns ( $[stream%$tk2]? $typer:dot_pident ) {$body*})
      | `(rpc| rpc $name:pident ( $[stream%$tk1]? $typed:dot_pident ) returns ( $[stream%$tk2]? $typer:dot_pident );) =>
        let typed ← resolve_message_enum_type typed
        let typer ← resolve_message_enum_type typer
        `(rpc| rpc $name:pident ( $[stream%$tk1]? $typed:dot_pident ) returns ( $[stream%$tk2]? $typer:dot_pident );)
      | `(option| option $name:optionName = $c:protobuf_const;)
      | `(emptyStatement| ;)
      | _ => pure b
    `(service| service $name:pident { $body* })

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
  let r ← a.foldM' (init := curr) fun k x c => do
    match c.find? k with
    | none => return c.insert k x
    | some v => -- now we shall merge the two `Scope`
      match v, x with
      | .scope (.package paths), .scope (.package paths') =>
        return c.insert k (.scope (.package (paths ++ paths').eraseDups))
      | .scope (.package paths), _ =>
        throwIsAlreadyDefined file k paths.head!
      | .scope kind, _ =>
        throwIsAlreadyDefinedNotPackage file k kind.getPath!
      | .leaf _ file, _ =>
        throwIsAlreadyDefinedNotPackage file k file
  modify fun s => {s with scopes := r}

mutual

private partial def load_proto (file : String) : M (TSyntax ``proto) := do
  withReader (fun s => {s with fileName := file}) do
    let proto ← load_and_parse file
    process_header proto
    -- now the scopes are checked and merged
    process_options proto
    let pack ← preprocess_package proto
    withReader (fun c => {c with current_scope := pack}) do
      preprocess_top_level_defs proto
      let r ← process_top_level_defs proto
      modify (fun s => {s with cache := s.cache.insert file ⟨file, r, s.scopes⟩})
      return r

private partial def process_header (code : TSyntax ``proto) : M Unit := do
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
  let paths := (← read).proto_paths
  let subCtx : Context := { imported_chain := newChain, proto_paths := paths }
  importFiles.forM fun i => do
    if newChain.contains i then
      throwError "cyclic imports detected for {i}"
    let cache := (← get).cache
    if let some _ := cache[i]? then
      return -- it is already merged somewhere else
    else
      let (_, r) ← load_proto i subCtx |>.run { cache := cache } -- only carry the cache
      let scopes := r.scopes
      modify (fun s => {s with cache := r.cache}) -- update the cache
      merge_scopes i scopes

end

def load_protos (paths : Array System.FilePath) (files : Array String) : CoreM (Array FileCache × Std.HashMap String FileCache) := do
  let paths := paths.toList
  let mut cache : Std.HashMap String FileCache := {}
  for file in files do
    let (_, s) ← load_proto file { proto_paths := paths } |>.run { cache := cache }
    cache := s.cache
  let ts ← files.mapM fun x => do
    let some v := cache.get? x | throwError "load_protos: impossible, there should be earlier errors"
    pure v
  return (ts, cache)

def type_to_term (e : TSyntax ``type) : CoreM Term := do
  match e with
  | `(type| double  ) => `($(mkIdent ``Float    ))
  | `(type| float   ) => `($(mkIdent ``Float32  ))
  | `(type| int32   ) => `($(mkIdent ``Int32    ))
  | `(type| int64   ) => `($(mkIdent ``Int64    ))
  | `(type| uint32  ) => `($(mkIdent ``UInt32   ))
  | `(type| uint64  ) => `($(mkIdent ``UInt64   ))
  | `(type| sint32  ) => `($(mkIdent ``Int32    ))
  | `(type| sint64  ) => `($(mkIdent ``Int64    ))
  | `(type| fixed32 ) => `($(mkIdent ``UInt32   ))
  | `(type| fixed64 ) => `($(mkIdent ``UInt64   ))
  | `(type| sfixed32) => `($(mkIdent ``Int32    ))
  | `(type| sfixed64) => `($(mkIdent ``Int64    ))
  | `(type| bool    ) => `($(mkIdent ``Bool     ))
  | `(type| string  ) => `($(mkIdent ``String   ))
  | `(type| bytes   ) => `($(mkIdent ``ByteArray))
  | `(type| $name:dot_pident) =>
    match name with
    | `(dot_pident| .$ns.*) => pidents_to_ident ns
    | _ => throwError "type_to_term: impossible"
  | _ => throwUnsupportedSyntax

variable (cache : Std.HashMap String FileCache) in
mutual

private partial def genName (s : TSyntax ``pident) : ReaderT (List String) CoreM Ident := do
  let ps ← read
  let ps := ps ++ [s.toIdent.getId.toString]
  let name := ps.foldl (init := Name.anonymous) Name.str
  return Lean.mkIdent name

partial def translate_message (e : TSyntax ``message) : ReaderT (List String) CoreM (Array Command) := do
  let `(message| message $name:pident { $body* }) := e | throwUnsupportedSyntax
  let rs ← withReader (fun c => c ++ [name.toIdent.getId.toString]) do
    body.mapM translate_message_body_entry_def
  let rs := rs.flatMap id
  let r ← translate_message_body_entry name body
  return rs ++ r

partial def translate_enum (e : TSyntax ``enum) : ReaderT (List String) CoreM (Array Command) := do
  let `(enum| enum $name:pident { $body* }) := e | throwUnsupportedSyntax
  let fs := body.filterMap fun x => if x.raw.getKind == ``enumField then some (TSyntax.mk (ks := ``enumField) x.raw) else none
  let ns ← fs.mapM fun x => do
    let `(enumField| $name:pident = $[-]? $num $[[$options?,*]]?;) := x | unreachable!
    pure name.toIdent
  let s ← `(command| inductive $(← genName name):ident where $[| $ns:ident]*)
  return #[s]

partial def translate_message_body_entry_def (e : TSyntax `message_body_entry) : ReaderT (List String) CoreM (Array Command) := do
  match e with
  | `(message_body_entry| $e:enum) =>
    translate_enum e
  | `(message_body_entry| $m:message) =>
    translate_message m
  | `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) => pure #[]
  | `(message_body_entry| map<$k,$v> $name:pident = $num:intLit $[[$options?]]?;) => pure #[]
  | `(message_body_entry| reserved $ts,*;) => pure #[]
  | `(message_body_entry| option $name:optionName = $c:protobuf_const;) => pure #[]
  | `(message_body_entry| ;)
  | _ => pure #[]

partial def translate_message_body_entry (name : TSyntax ``pident) (e : TSyntaxArray `message_body_entry) : ReaderT (List String) CoreM (Array Command) := do
  let ts := e.filterMap fun x => if x.raw[0].getKind == ``field then some (TSyntax.mk (ks := ``enumField) x.raw) else none
  let rs ← ts.mapM fun t => do
    let `(message_body_entry| $[$modifier?]? $type:type $name:pident = $num:intLit $[[$options?]]?;) := t | unreachable!
    let type' ← type_to_term type
    `(Parser.Command.structSimpleBinder| $(name.toIdent):ident : $type')
  let fields ← `(Parser.Command.structFields| $rs*)
  let c ← `(command| structure $(← genName name) where $fields:structFields)
  return #[c]

partial def translate_top_level_defs (code : TSyntax ``proto) : ReaderT (List String) CoreM (Array Command) := do
  let `(proto| $[$stxSpec?]? $ts*) := code | throwUnsupportedSyntax
  ts.flatMapM fun t => do
    let `(topLevelDef| $t:topLevelDef) := t | return #[]
    match t with
    | `(topLevelDef| $e:enum) =>
      translate_enum e
    | `(topLevelDef| $m:message) =>
      translate_message m
    | `(topLevelDef| service $name:pident { $body* }) => return #[]
    | _ => throwUnsupportedSyntax

end

variable (cache : Std.HashMap String FileCache) in
/-- we assume there is not cycle dependency -/
partial def translate_proto (file : String) : StateRefT (Std.HashSet String) CoreM (Array Command) := do
  if (← get).contains file then
    return #[]
  let some c := cache[file]? | throwError "file {file} not loaded"
  let proto := c.processed
  let pack ← preprocess_package proto {} |>.run' { cache := {} }
  let `(proto| $[$stxSpec?]? $ts*) := proto | throwUnsupportedSyntax
  let imports := ts.filter fun x => x.raw.getKind == ``pimport
  let importFiles ← imports.mapM fun x => do
    match x with
      | `(pimport| import $[$kind]? $file;) =>
        match kind with
        | none => return file.getString.trim
        | some k =>
          match k with
          | `(importKind| public) => return file.getString.trim
          | `(importKind| weak) => unreachable!
          | _ => throwUnsupportedSyntax
      | _ => unreachable!
  let pres ← importFiles.flatMapM translate_proto
  --
  let cs ← translate_top_level_defs proto pack
  modify fun s => s.insert file
  return pres ++ cs

variable (cache : Std.HashMap String FileCache) in
def translate_protos (files : Array String) : CoreM (Array Command) := do
  let mut s : (Std.HashSet String) := {}
  let mut cmds := #[]
  for file in files do
    let (r, s') ← translate_proto cache file |>.run s
    cmds := cmds.append r
    s := s'
  return cmds

syntax (name := loadProtobufCommand) "#load_protobuf " "[" str,* "]" "[" str,* "]" : command

@[command_elab loadProtobufCommand]
def elabLoadProtobufCommand : CommandElab := fun stx => do
  let `(command| #load_protobuf [$pathsStx,*] [$filesStx,*]) := stx | throwUnsupportedSyntax
  let paths ← pathsStx.getElems.mapM fun (x : TSyntax `str) => do
    let s := System.FilePath.mk x.getString
    unless ← s.pathExists do
      throwErrorAt x "path does not exist"
    unless ← s.isDir do
      throwErrorAt x "path is not a directory"
    pure s
  let files := filesStx.getElems.map fun x => x.getString
  runTermElabM fun _ => do
    let (r, cache) ← load_protos paths files
    let cmds ← translate_protos cache files
    let cmds := cmds.toList.mergeSort fun x y =>
      match x, y with
      | `(command| $m:declModifiers $c:inductive), _ => true
      | `(command| $m:declModifiers $c:structure), r => !(y matches `(command| $m:declModifiers $c:inductive))
      | _, _ => false
    let a := cmds.findIdx (α := Command) (fun x => x matches `(command| $m:declModifiers $c:structure))
    let b := cmds.length - cmds.reverse.findIdx (α := Command) (fun x => x matches `(command| $m:declModifiers $c:structure))
    let sub := cmds.extract a b
    let cmds ←
      if sub.isEmpty then
        pure cmds
      else
        let h := cmds.take a
        let t := cmds.drop b
        pure <| h ++ [← `(command| mutual $(sub.toArray)* end)] ++ t
    let t := MessageData.joinSep (cmds.map fun x => m!"{x}") m!"\n\n"
    logInfo m!"{t}"


#load_protobuf ["Test"] ["descriptor.proto"]
