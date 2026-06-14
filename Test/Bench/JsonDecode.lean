import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 100
  let batch := mkBatch cfg.itemCount
  let text := encodeJson batch
  let mut totalItems := 0
  let mut checksum := 0
  for _ in [0:cfg.iterations] do
    let decoded ← decodeJson text
    totalItems := totalItems + decoded.items.size
    checksum := checksum + batchChecksum decoded
  IO.println s!"json decode: items={cfg.itemCount} iterations={cfg.iterations} input_utf8_bytes={text.utf8ByteSize} total_items={totalItems} checksum={checksum}"
