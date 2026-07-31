import Test.Bench.Common

open Test.Bench

namespace Test.Bench.Codec

inductive Implementation where
  | binary
  | leanJson
  | protoJson

def Implementation.parse (value : String) : IO Implementation :=
  match value with
  | "lean-binary" => pure .binary
  | "lean-json" => pure .leanJson
  | "lean-protojson" => pure .protoJson
  | _ =>
      throw <| IO.userError
        s!"unknown implementation `{value}`; expected lean-binary, lean-json, or lean-protojson"

def Implementation.label : Implementation → String
  | .binary => "lean-binary"
  | .leanJson => "lean-json"
  | .protoJson => "lean-protojson"

inductive Operation where
  | encode
  | decode

def Operation.parse (value : String) : IO Operation :=
  match value with
  | "encode" => pure .encode
  | "decode" => pure .decode
  | _ => throw <| IO.userError s!"unknown operation `{value}`; expected encode or decode"

def Operation.label : Operation → String
  | .encode => "encode"
  | .decode => "decode"

structure Config where
  implementation : Implementation
  operation : Operation
  itemCount : Nat
  iterations : Nat
  validate : Bool

private def parseValidation (value : String) : IO Bool :=
  match value with
  | "0" => pure false
  | "1" => pure true
  | _ => throw <| IO.userError "validate must be 0 or 1"

def Config.parse (args : List String) : IO Config := do
  let [implementation, operation, itemCount, iterations, validate] := args
    | throw <| IO.userError
        "usage: <lean-binary|lean-json|lean-protojson> <encode|decode> <items> <steady-iterations> <validate:0|1>"
  let implementation ← Implementation.parse implementation
  let operation ← Operation.parse operation
  let itemCount ← parseNatArg "items" itemCount
  let iterations ← parseNatArg "steady-iterations" iterations
  let validate ← parseValidation validate
  pure
    { implementation
    , operation
    , itemCount
    , iterations
    , validate
    }

structure Result where
  dataSetupNs : Nat
  inputSetupNs : Nat
  firstNs : Nat
  steadyNs : Nat
  outputBytes : Nat
  contentHash : UInt64
  outputHash : UInt64
  checksum : Nat

private def Result.print (cfg : Config) (result : Result) : IO Unit := do
  let nsPerOperation :=
    if cfg.iterations == 0 then 0 else result.steadyNs / cfg.iterations
  IO.println <|
    s!"BENCH_RESULT implementation={cfg.implementation.label} operation={cfg.operation.label} " ++
    s!"items={cfg.itemCount} iterations={cfg.iterations} " ++
    s!"data_setup_ns={result.dataSetupNs} input_setup_ns={result.inputSetupNs} " ++
    s!"first_ns={result.firstNs} steady_ns={result.steadyNs} " ++
    s!"steady_ns_per_op={nsPerOperation} output_bytes={result.outputBytes} " ++
    s!"content_hash={result.contentHash} output_hash={result.outputHash} " ++
    s!"checksum={result.checksum} validation={if cfg.validate then 1 else 0}"

@[noinline]
private def materializeBatch (batch : Batch) : IO Batch :=
  pure batch

@[noinline]
private def encodeLeanJsonIO (batch : Batch) : IO String :=
  pure (encodeLeanJson batch)

private def measure (action : IO α) : IO (Nat × α) := do
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  return (stop - start, result)

private def validateBatch
    (expectedHash : UInt64) (batch : Batch) (description : String) : IO Unit := do
  let actualHash := batchContentHash batch
  unless actualHash == expectedHash do
    throw <| IO.userError
      s!"{description} content mismatch: expected {expectedHash}, got {actualHash}"

private def prepareBatch (itemCount : Nat) : IO (Nat × Batch) := do
  let start ← IO.monoNanosNow
  let batch ← materializeBatch (mkBatch itemCount)
  let stop ← IO.monoNanosNow
  return (stop - start, batch)

private def runBinaryEncode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (firstNs, first) ← measure (encodeProto batch)
  let mut last := first
  let mut checksum := consumeBytes first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let bytes ← encodeProto batch
    checksum := checksum + consumeBytes bytes
    last := bytes
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash (← decodeProto last) "lean-binary encode"
  pure
    { dataSetupNs
    , inputSetupNs := 0
    , firstNs
    , steadyNs := stop - start
    , outputBytes := last.size
    , contentHash := expectedHash
    , outputHash := byteArrayHash last
    , checksum
    }

private def runBinaryDecode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (inputSetupNs, input) ← measure (encodeProto batch)
  let (firstNs, first) ← measure (decodeProto input)
  let mut last := first
  let mut checksum := consumeBatch first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let decoded ← decodeProto input
    checksum := checksum + consumeBatch decoded
    last := decoded
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash last "lean-binary decode"
  pure
    { dataSetupNs
    , inputSetupNs
    , firstNs
    , steadyNs := stop - start
    , outputBytes := input.size
    , contentHash := expectedHash
    , outputHash := byteArrayHash input
    , checksum
    }

private def runLeanJsonEncode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (firstNs, first) ← measure (encodeLeanJsonIO batch)
  let mut last := first
  let mut checksum := consumeString first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let text ← encodeLeanJsonIO batch
    checksum := checksum + consumeString text
    last := text
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash (← decodeLeanJson last) "lean-json encode"
  pure
    { dataSetupNs
    , inputSetupNs := 0
    , firstNs
    , steadyNs := stop - start
    , outputBytes := last.utf8ByteSize
    , contentHash := expectedHash
    , outputHash := stringHash last
    , checksum
    }

private def runLeanJsonDecode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (inputSetupNs, input) ← measure (encodeLeanJsonIO batch)
  let (firstNs, first) ← measure (decodeLeanJson input)
  let mut last := first
  let mut checksum := consumeBatch first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let decoded ← decodeLeanJson input
    checksum := checksum + consumeBatch decoded
    last := decoded
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash last "lean-json decode"
  pure
    { dataSetupNs
    , inputSetupNs
    , firstNs
    , steadyNs := stop - start
    , outputBytes := input.utf8ByteSize
    , contentHash := expectedHash
    , outputHash := stringHash input
    , checksum
    }

private def runProtoJsonEncode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (firstNs, first) ← measure (encodeProtoJson batch)
  let mut last := first
  let mut checksum := consumeString first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let text ← encodeProtoJson batch
    checksum := checksum + consumeString text
    last := text
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash (← decodeProtoJson last) "lean-protojson encode"
  pure
    { dataSetupNs
    , inputSetupNs := 0
    , firstNs
    , steadyNs := stop - start
    , outputBytes := last.utf8ByteSize
    , contentHash := expectedHash
    , outputHash := stringHash last
    , checksum
    }

private def runProtoJsonDecode (cfg : Config) : IO Result := do
  let (dataSetupNs, batch) ← prepareBatch cfg.itemCount
  let expectedHash := batchContentHash batch
  let (inputSetupNs, input) ← measure (encodeProtoJson batch)
  let (firstNs, first) ← measure (decodeProtoJson input)
  let mut last := first
  let mut checksum := consumeBatch first
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let decoded ← decodeProtoJson input
    checksum := checksum + consumeBatch decoded
    last := decoded
  let stop ← IO.monoNanosNow
  if cfg.validate then
    validateBatch expectedHash last "lean-protojson decode"
  pure
    { dataSetupNs
    , inputSetupNs
    , firstNs
    , steadyNs := stop - start
    , outputBytes := input.utf8ByteSize
    , contentHash := expectedHash
    , outputHash := stringHash input
    , checksum
    }

private def run (cfg : Config) : IO Result :=
  match cfg.implementation, cfg.operation with
  | .binary, .encode => runBinaryEncode cfg
  | .binary, .decode => runBinaryDecode cfg
  | .leanJson, .encode => runLeanJsonEncode cfg
  | .leanJson, .decode => runLeanJsonDecode cfg
  | .protoJson, .encode => runProtoJsonEncode cfg
  | .protoJson, .decode => runProtoJsonDecode cfg

end Test.Bench.Codec

def main (args : List String) : IO Unit := do
  if args == ["startup"] then
    IO.println "BENCH_RESULT implementation=lean-runtime operation=startup items=0 iterations=0 data_setup_ns=0 input_setup_ns=0 first_ns=0 steady_ns=0 steady_ns_per_op=0 output_bytes=0 content_hash=0 output_hash=0 checksum=0 validation=0"
  else
    let cfg ← Test.Bench.Codec.Config.parse args
    (← Test.Bench.Codec.run cfg).print cfg
