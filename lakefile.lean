import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.4.0"
  releaseRepo := "https://github.com/Lean-zh/protobuf"
  preferReleaseBuild := true

require binary from git "https://github.com/Lean-zh/binary.git"

@[default_target]
lean_lib Protobuf where
  -- The `Protobuf` root does not import `Protobuf.Json`, so name it here as
  -- well; the release archive ships exactly what this library builds.
  globs := #[.one `Protobuf, .one `Protobuf.Json]

lean_exe Plugin where
  root := `Plugin
  exeName := "protoc-gen-lean4"

lean_lib Bench where
  roots := #[`Test.Bench]

lean_exe benchWire where
  root := `Test.Bench.Wire

lean_exe benchCodec where
  root := `Test.Bench.Codec

lean_exe testVersionsSemantics where
  root := `Test.Runtime.VersionsSemantics

lean_exe testVersionsValidation where
  root := `Test.Core.VersionsValidation

lean_exe testExtensions where
  root := `Test.Runtime.Extensions

lean_exe testClosedEnum where
  root := `Test.Runtime.ClosedEnum

lean_exe testUtf8Validation where
  root := `Test.Runtime.Utf8Validation

lean_exe testReflection where
  root := `Test.Runtime.Reflection

lean_exe testProtoJson where
  root := `Test.Runtime.ProtoJson

lean_exe testProtoJsonWellKnown where
  root := `Test.Runtime.ProtoJsonWellKnown

lean_exe testProtoJsonConformance where
  root := `Test.Conformance.ProtoJsonConformance

lean_lib Tests where
  roots := #[
    `Test.Core.Utils,
    `Test.Core.EncodingWire,
    `Test.Core.Desc,
    `Test.Core.VersionsValidation,
    `Test.Codegen.ExtensionTagBase,
    `Test.Codegen.ExtensionKnownTagCollisionsBase,
    `Test.Codegen.ExtensionKnownTagCollisions,
    `Test.Codegen.NotationSyntax,
    `Test.Codegen.Folder,
    `Test.Codegen.NamingCollisions,
    `Test.Codegen.WideCodegen,
    `Test.Codegen.OneofParentCollisionBase,
    `Test.Codegen.OneofParentCollisions,
    `Test.Codegen.RootName,
    `Test.Codegen.VisibilityRetainedOptions,
    `Test.Runtime.Proto3,
    `Test.Runtime.VersionsSemantics,
    `Test.Runtime.Extensions,
    `Test.Runtime.ClosedEnum,
    `Test.Runtime.Utf8Validation,
    `Test.Runtime.Reflection,
    `Test.Runtime.ProtoJson,
    `Test.Runtime.ProtoJsonWellKnown,
    `Test.Runtime.RecursionDepth,
    `Test.Runtime.RequiredMerge,
    `Test.Runtime.Groups,
    `Test.Integration.ElabStandaloneImport,
    `Test.Official.OfficialSmokeUnittestProto3,
    `Test.Official.OfficialStruct,
    `Test.Official.OfficialConformanceProto3
  ]

@[test_driver]
script test (_args) do
  let runLake (args : Array String) : IO UInt32 := do
    let child ← IO.Process.spawn {
      cmd := "lake"
      args
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit
    }
    child.wait

  let buildExit ← runLake #[
    "build",
    "+Test.Core.Utils",
    "+Test.Core.EncodingWire",
    "+Test.Codegen.ExtensionTagBase",
    "+Test.Codegen.ExtensionKnownTagCollisions",
    "+Test.Codegen.NotationSyntax",
    "+Test.Codegen.Folder",
    "+Test.Core.Desc",
    "+Test.Runtime.Proto3",
    "+Test.Runtime.RecursionDepth",
    "+Test.Runtime.RequiredMerge",
    "+Test.Runtime.Groups",
    "+Test.Codegen.NamingCollisions",
    "+Test.Codegen.WideCodegen",
    "+Test.Codegen.OneofParentCollisions",
    "+Test.Codegen.RootName",
    "+Test.Integration.ElabStandaloneImport",
    "+Test.Codegen.VisibilityRetainedOptions",
    "+Test.Official.OfficialSmokeUnittestProto3",
    "+Test.Official.OfficialStruct",
    "Plugin",
    "testVersionsSemantics",
    "testVersionsValidation",
    "testExtensions",
    "testClosedEnum",
    "testUtf8Validation",
    "testReflection",
    "testProtoJson",
    "testProtoJsonWellKnown"
  ]
  if buildExit != 0 then
    return buildExit

  -- Keep the largest upstream schema in a separate Lake invocation so it
  -- cannot overlap other generated-code jobs and multiply peak memory usage.
  let conformanceExit ←
    runLake #["build", "+Test.Official.OfficialConformanceProto3"]
  if conformanceExit != 0 then
    return conformanceExit

  for executable in #[
      "testVersionsSemantics",
      "testVersionsValidation",
      "testExtensions",
      "testClosedEnum",
      "testUtf8Validation",
      "testReflection",
      "testProtoJson",
      "testProtoJsonWellKnown"
    ] do
    let runExit ← runLake #["exe", executable]
    if runExit != 0 then
      return runExit

  let pluginTest ← IO.Process.spawn {
    cmd := "bash"
    args := #["Test/Integration/Plugin.sh"]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  let pluginExit ← pluginTest.wait
  if pluginExit != 0 then
    return pluginExit


  -- Nothing below the `Protobuf` root imports `Protobuf.Json`, so only the
  -- library's globs keep it in the build, and a release archive holds exactly
  -- what that library builds. Clients of the source tree cannot show this up,
  -- because Lake builds a module they import on demand.
  let some protobufLib := (← getWorkspace).findLeanLib? `Protobuf
    | do
      IO.eprintln "the workspace defines no `Protobuf` library"
      return 1
  unless (← protobufLib.getModuleArray).any (·.name == `Protobuf.Json) do
    IO.eprintln "`Protobuf.Json` is not a module of the `Protobuf` library"
    return 1

  -- Clients of a release do reach it as a library module, so build one and run
  -- it: the module has to link, not merely resolve.
  let clientDir : System.FilePath := "Test" / "Integration" / "Client"
  let clientBuild ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "client"]
    cwd := clientDir
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  let clientBuildExit ← clientBuild.wait
  if clientBuildExit != 0 then
    return clientBuildExit

  let client ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "client"]
    cwd := clientDir
  }
  if client.exitCode != 0 then
    IO.eprint client.stderr
    return client.exitCode
  let expected := "{\"name\":\"payload\",\"number\":3}"
  let rendered := client.stdout.trimAscii.toString
  if rendered != expected then
    IO.eprintln s!"json client printed {rendered}, expected {expected}"
    return 1

  return 0
