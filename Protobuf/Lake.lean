import Lean
import Lake
import Protobuf.Internal.Desc

open Lake DSL System
open Lean


-- def load
#check Target

-- def compile_proto : Target FilePath
#check TextFilePath

#check buildArtifactUnlessUpToDate
#check LeanLibConfig
#check LeanLib

#check inputFile
#check inputFileCommand
#check inputFileAttr

-- public configuration ProtobufFileConfig (name : Name) where
--   /-- path to the `.proto` source file -/
--   path : FilePath := name.toString (escape := false)

-- public structure ConfigTarget (kind : Name) where
--   /-- The package the target belongs to. -/
--   pkg : Package
--   /-- The target's name. -/
--   name : Name
--   /-- The target's user-defined configuration. -/
--   config : ConfigType kind pkg.name name

-- #check elabInputfileCommand
-- attribute [command_elab] elabInputfileCommand

#check Target
#check LakeM
#check FetchM
#check SpawnM
#check ScriptM
#check getBuildDir

#check IO.FS.withTempFile

open Protobuf Internal.Desc


def compile_proto_ (srcFile : FilePath) (targetLeanPath : FilePath) : FetchM (Job FilePath) := do
  let inputJob ← inputFile srcFile (text := true)
  inputJob.mapM fun srcFile => do
    let a ← buildArtifactUnlessUpToDate srcFile (ext := "lean") (text := true) do
      let bin ← IO.FS.withTempFile fun h _ => do
        proc { cmd := "protoc", args := #[srcFile.toString] }
        h.readBinToEnd -- TODO: may be too large, make it incremental
      let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
        | .ok data => pure data
        | .error e => error s!"failed to parse protoc output: {e}"
      let desc ← match FileDescriptorSet.fromMessage data with
        | .ok d => pure d
        | .error e => error s!"failed to parse protoc output: {e}"
      sorry
    return a.path

structure M.Context where
  currentMacroScope : Nat := 0
  ref : Syntax := mkNullNode
  currentNamePrefixRev : List String := []

abbrev M := ReaderT M.Context <| StateRefT Nat IO

@[inline]
def M.run : M α → IO α := fun x => x { } |>.run' 0

@[inline]
def wrapName : String → M Name := fun s c =>
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str x
  return (go c.currentNamePrefixRev).str s

@[specialize]
def withNewNameLevel (n : String) (x : M α) : M α := fun c => x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }

@[specialize, always_inline]
protected def M.withFreshMacroScope {α} (x : M α) : M α := do
  let fresh ← modifyGetThe Nat (fun st => (st, st + 1))
  withReader (fun ctx => { ctx with currentMacroScope := fresh }) x

@[always_inline]
instance : MonadRef M where
  getRef := fun c => return c.ref
  withRef stx x := fun c => x {c with ref := stx}

@[always_inline]
instance : MonadQuotation M where
  getCurrMacroScope := fun c => return c.currentMacroScope
  getContext := return .anonymous
  withFreshMacroScope := M.withFreshMacroScope

def read_proto (srcFile : FilePath) : IO FileDescriptorSet := do
  let bin ← IO.FS.withTempFile fun h tmp => do
    _ ← IO.Process.run { cmd := "protoc", args := #[srcFile.toString, "-o", tmp.toString] }
    h.readBinToEnd -- TODO: may be too large, make it incremental
  let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
    | .ok data => pure data
    | .error e => error s!"failed to parse protoc output: {e}"
  let desc ← match FileDescriptorSet.fromMessage data with
    | .ok d => pure d
    | .error e => error s!"failed to parse protoc output: {e}"

def compile_proto (desc : FileDescriptorSet) : M Unit := do
  println! "{repr desc}"
  -- for file in desc.file do
  --   -- let t := file.name
  --   println! "{file.name}"
  --   -- println! "{repr file.}"
  --   for m in file.message_type do
  --     println! "{m.name}"
  --     -- println! "{repr m.options}"
  --     for f in m.field do
  --       println! "{f.name}"
  --       println! "{repr f.options}"
  --       println! "{repr f.proto3_optional}"
  --   -- println! "{file.syntax}"
  --   -- println! "{repr file.edition}"
  --   -- println! "{repr file.options}"

def test : M Unit := do
  let x ← read_proto "Test/A.proto"
  compile_proto x

-- #eval compile_proto_ "Test/B.proto" "./B.lean"
#check FetchM.toFn

#check Workspace.runFetchM

#eval test.run

-- proto3

def compile_message_field (field : FieldDescriptorProto) : M String := do
  sorry

local
macro "get!! " src:term:max " ! " err:term : term =>
  ``(Option.getDM $src (error s!"{decl_name%}: {$err}"))

local
macro "get!! " src:term:max : term => ``(Option.getDM $src (error s!"{decl_name%}"))

@[inline]
private def joinLines (xs : Array String) : String := String.intercalate "\n" xs.toList

structure EnumValueMData where

def compile_enum (e : EnumDescriptorProto) : M (Array Command) := do
  let enumName ← get!! e.name ! "expected enum name"
  let typeName ← wrapName enumName
  let typeId := mkIdent typeName
  let vNames ← e.value.mapM fun v => get!! v.name
  let vNames := vNames.map fun x => typeName.str x
  let vIds := vNames.map mkIdent
  let vNums ← e.value.mapM fun v => get!! v.number
  let vNumsQ := vNums.map fun x => quote x.toUInt32.toNat
  let unknownName := `«Unknown.Value»
  let unknownCtorId := mkIdent <| typeName.append unknownName
  let typeDef ← `(enum' $typeId { $[$vIds = $vNumsQ;]* })
  let t ← e.value.mapM fun v => do
    let x := v.options
    pure ()
  sorry

#exit

#[{ name := some "N",
    value := #[{ name := some "A", number := some 0, options := none },
              { name := some "B", number := some 2, options := none }],
    options := none,
    reserved_range := #[],
    reserved_name := #[] }]
