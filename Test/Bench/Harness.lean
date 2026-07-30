namespace Test.Bench

def parseNatArg (name : String) (s : String) : IO Nat := do
  let some n := s.toNat? | throw <| IO.userError s!"invalid {name}: {s}"
  return n

structure Config where
  itemCount : Nat
  iterations : Nat

def readConfig (args : List String) (defaultItems defaultIterations : Nat) : IO Config := do
  let cfg ←
    match args with
    | [] =>
        pure { itemCount := defaultItems, iterations := defaultIterations }
    | [itemCount] =>
        pure
          { itemCount := ← parseNatArg "itemCount" itemCount
          , iterations := defaultIterations
          }
    | [itemCount, iterations] =>
        pure
          { itemCount := ← parseNatArg "itemCount" itemCount
          , iterations := ← parseNatArg "iterations" iterations
          }
    | _ => throw <| IO.userError "usage: <itemCount> <iterations>"
  if cfg.iterations == 0 then
    throw <| IO.userError "iterations must be positive"
  return cfg

structure Timing where
  elapsedNs : Nat
  iterations : Nat
  processedBytes : Nat

def Timing.nsPerIteration (timing : Timing) : Nat :=
  timing.elapsedNs / timing.iterations

def Timing.bytesPerSecond (timing : Timing) : Nat :=
  if timing.elapsedNs == 0 then
    0
  else
    timing.processedBytes * 1_000_000_000 / timing.elapsedNs

def printTiming
    (name : String) (timing : Timing) (details : String) : IO Unit :=
  IO.println
    s!"{name}: elapsed_ns={timing.elapsedNs} ns_per_iteration={timing.nsPerIteration} processed_bytes={timing.processedBytes} bytes_per_second={timing.bytesPerSecond} {details}"

/--
Consume a constant number of bytes from a benchmark result. Keeping this
function out of line makes the result observable without adding an O(n)
checksum to every timed iteration.
-/
@[noinline]
def consumeBytes (bytes : ByteArray) : Nat :=
  if bytes.isEmpty then
    0
  else
    bytes.size + bytes[0]!.toNat + bytes[bytes.size - 1]!.toNat

end Test.Bench
