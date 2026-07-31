# Test layout

- `Core/` contains focused tests for wire primitives, descriptor decoding,
  validation, and shared utilities.
- `Codegen/` exercises notation elaboration, generated names, generated helper
  structure, imports, and compile-time diagnostics.
- `Runtime/` covers generated binary codecs, reflection, ProtoJSON, extensions,
  recursion limits, and version-specific runtime semantics.
- `Official/` compiles and exercises schemas copied from the upstream protobuf
  test suite.
- `Conformance/` contains adapters used by external conformance runners.
- `Integration/` tests the standalone `protoc-gen-lean4` process.
- `Fixtures/` contains schemas and request/data files consumed by the suites
  above.
- `Bench/` contains performance workloads and its runner.
