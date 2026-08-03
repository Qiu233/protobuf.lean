import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.2.0"
  releaseRepo := "https://github.com/Lean-zh/protobuf"
  preferReleaseBuild := true

require binary from git "https://github.com/Lean-zh/binary.git"

@[default_target]
lean_lib Protobuf where

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

  return 0
