import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 200
  let batch := mkBatch cfg.itemCount
  let bytes ← encodeProto batch
  let mut totalItems := 0
  let mut checksum := 0
  for _ in [0:cfg.iterations] do
    let decoded ← decodeProto bytes
    totalItems := totalItems + decoded.items.size
    checksum := checksum + batchChecksum decoded
  IO.println s!"protobuf decode: items={cfg.itemCount} iterations={cfg.iterations} input_bytes={bytes.size} total_items={totalItems} checksum={checksum}"
