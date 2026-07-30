import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"

require binary from git "https://github.com/Lean-zh/binary"

@[default_target]
lean_lib Protobuf where

lean_exe Plugin where
  root := `Plugin
  exeName := "protoc-gen-lean4"

lean_lib Bench where
  roots := #[`Test.Bench]

lean_exe benchProtoEncode where
  root := `Test.Bench.ProtoEncode

lean_exe benchProtoDecode where
  root := `Test.Bench.ProtoDecode

lean_exe benchWire where
  root := `Test.Bench.Wire

lean_exe benchJsonEncode where
  root := `Test.Bench.JsonEncode

lean_exe benchJsonDecode where
  root := `Test.Bench.JsonDecode

lean_exe testVersionsSemantics where
  root := `Test.VersionsSemantics

lean_exe testVersionsValidation where
  root := `Test.VersionsValidation

lean_exe testExtensions where
  root := `Test.Extensions

lean_exe testClosedEnum where
  root := `Test.ClosedEnum

lean_exe testUtf8Validation where
  root := `Test.Utf8Validation

lean_exe testReflection where
  root := `Test.Reflection

lean_exe testProtoJson where
  root := `Test.ProtoJson

lean_exe testProtoJsonWellKnown where
  root := `Test.ProtoJsonWellKnown

lean_exe testProtoJsonConformance where
  root := `Test.ProtoJsonConformance

lean_lib Tests where
  roots := #[
    `Test.Utils,
    `Test.EncodingWire,
    `Test.ExtensionTagBase,
    `Test.ExtensionKnownTagCollisionsBase,
    `Test.ExtensionKnownTagCollisions,
    `Test.NotationSyntax,
    `Test.Proto3,
    `Test.Folder,
    `Test.Desc,
    `Test.VersionsSemantics,
    `Test.VersionsValidation,
    `Test.Extensions,
    `Test.ClosedEnum,
    `Test.Utf8Validation,
    `Test.Reflection,
    `Test.ProtoJson,
    `Test.ProtoJsonWellKnown,
    `Test.RecursionDepth,
    `Test.RequiredMerge,
    `Test.Groups,
    `Test.NamingCollisions,
    `Test.WideCodegen,
    `Test.OneofParentCollisionBase,
    `Test.OneofParentCollisions,
    `Test.RootName,
    `Test.ElabStandaloneImport,
    `Test.VisibilityRetainedOptions,
    `Test.OfficialSmokeUnittestProto3,
    `Test.OfficialStruct,
    `Test.OfficialConformanceProto3
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
    "+Test.Utils",
    "+Test.EncodingWire",
    "+Test.ExtensionTagBase",
    "+Test.ExtensionKnownTagCollisions",
    "+Test.NotationSyntax",
    "+Test.Proto3",
    "+Test.Folder",
    "+Test.Desc",
    "+Test.RecursionDepth",
    "+Test.RequiredMerge",
    "+Test.Groups",
    "+Test.NamingCollisions",
    "+Test.WideCodegen",
    "+Test.OneofParentCollisions",
    "+Test.RootName",
    "+Test.ElabStandaloneImport",
    "+Test.VisibilityRetainedOptions",
    "+Test.OfficialSmokeUnittestProto3",
    "+Test.OfficialStruct",
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
    runLake #["build", "+Test.OfficialConformanceProto3"]
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
    args := #["Test/PluginIntegration.sh"]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  let pluginExit ← pluginTest.wait
  if pluginExit != 0 then
    return pluginExit

  return 0
