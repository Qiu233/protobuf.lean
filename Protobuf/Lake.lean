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
  currentMacroScope : Nat
  ref : Syntax

abbrev M := ReaderT M.Context <| StateRefT Nat IO

@[inline]
def M.run : M α → IO α := fun x => x { currentMacroScope := 0, ref := mkNullNode } |>.run' 0

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
  for file in desc.file do
    -- let t := file.name
    println! "{file.name}"
    -- println! "{repr file.}"
    for m in file.message_type do
      println! "{m.name}"
      -- println! "{repr m.options}"
      for f in m.field do
        println! "{f.name}"
        println! "{repr f.options}"
        println! "{repr f.proto3_optional}"
    -- println! "{file.syntax}"
    -- println! "{repr file.edition}"
    -- println! "{repr file.options}"

def test : M Unit := do
  let x ← read_proto "Test/A.proto"
  compile_proto x

-- #eval compile_proto_ "Test/B.proto" "./B.lean"
#check FetchM.toFn

#check Workspace.runFetchM

#eval test.run
