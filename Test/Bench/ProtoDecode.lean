import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 200
  let batch := mkBatch cfg.itemCount
  let bytes ← encodeProto batch
  let warmup ← decodeProto bytes
  let mut totalItems := 0
  let mut checksum := 0
  let mut last := warmup
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let decoded ← decodeProto bytes
    totalItems := totalItems + decoded.items.size
    checksum := checksum + consumeBatch decoded
    last := decoded
  let stop ← IO.monoNanosNow
  let deepChecksum := batchChecksum last
  printTiming "protobuf decode"
    { elapsedNs := stop - start
    , iterations := cfg.iterations
    , processedBytes := bytes.size * cfg.iterations
    }
    s!"items={cfg.itemCount} wire_bytes={bytes.size} total_items={totalItems} checksum={checksum} deep_checksum={deepChecksum}"
