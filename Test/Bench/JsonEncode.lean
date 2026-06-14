import Test.Bench.Common
open Test.Bench

def main (args : List String) : IO Unit := do
  let cfg ← readConfig args 2000 100
  let batch := mkBatch cfg.itemCount
  let mut totalBytes := 0
  let mut checksum := 0
  for _ in [0:cfg.iterations] do
    let text := encodeJson batch
    totalBytes := totalBytes + text.utf8ByteSize
    checksum := checksum + text.length
  IO.println s!"json encode: items={cfg.itemCount} iterations={cfg.iterations} total_utf8_bytes={totalBytes} checksum={checksum}"
