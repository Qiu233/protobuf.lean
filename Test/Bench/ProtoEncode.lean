import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 200
  let batch := mkBatch cfg.itemCount
  let warmup ← encodeProto batch
  let mut totalBytes := 0
  let mut checksum := 0
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let bytes ← encodeProto batch
    totalBytes := totalBytes + bytes.size
    checksum := checksum + consumeBytes bytes
  let stop ← IO.monoNanosNow
  printTiming "protobuf encode"
    { elapsedNs := stop - start
    , iterations := cfg.iterations
    , processedBytes := totalBytes
    }
    s!"items={cfg.itemCount} wire_bytes={warmup.size} checksum={checksum}"
