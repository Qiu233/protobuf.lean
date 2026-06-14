import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 200
  let batch := mkBatch cfg.itemCount
  let mut totalBytes := 0
  let mut checksum := 0
  for _ in [0:cfg.iterations] do
    let bytes ← encodeProto batch
    totalBytes := totalBytes + bytes.size
    checksum := checksum + bytes.size
  IO.println s!"protobuf encode: items={cfg.itemCount} iterations={cfg.iterations} total_bytes={totalBytes} checksum={checksum}"
