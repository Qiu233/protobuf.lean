import Protobuf.Encoding.Binary
import Test.Bench.Harness

open Binary
open Protobuf.Encoding
open Test.Bench

namespace Test.Bench.Wire

structure WireConfig where
  direction : String
  width : String
  valueCount : Nat
  iterations : Nat

def readWireConfig (args : List String) : IO WireConfig := do
  let cfg ←
    match args with
    | [] =>
        pure
          { direction := "decode"
          , width := "mixed"
          , valueCount := 100_000
          , iterations := 100
          }
    | [direction, width, valueCount, iterations] =>
        pure
          { direction
          , width
          , valueCount := ← parseNatArg "valueCount" valueCount
          , iterations := ← parseNatArg "iterations" iterations
          }
    | _ =>
        throw <| IO.userError
          "usage: <encode|decode> <one|five|ten|mixed> <valueCount> <iterations>"
  if cfg.direction != "encode" && cfg.direction != "decode" then
    throw <| IO.userError s!"unknown direction: {cfg.direction}"
  if cfg.width != "one" && cfg.width != "five" &&
      cfg.width != "ten" && cfg.width != "mixed" then
    throw <| IO.userError s!"unknown varint width: {cfg.width}"
  if cfg.valueCount == 0 then
    throw <| IO.userError "valueCount must be positive"
  if cfg.iterations == 0 then
    throw <| IO.userError "iterations must be positive"
  return cfg

private def mixedValues : Array Nat :=
  #[0, 1, 127, 128, 16_383, 16_384, (1 <<< 28) - 1, 1 <<< 28,
    (1 <<< 32) - 1, 1 <<< 63, (1 <<< 64) - 1]

private def tenByteValues : Array Nat :=
  #[1 <<< 63, (1 <<< 63) + 1, (1 <<< 64) - 2, (1 <<< 64) - 1]

def mkValues (width : String) (count : Nat) : Array Nat := Id.run do
  let mut values := Array.emptyWithCapacity count
  for i in [0:count] do
    let value :=
      match width with
      | "one" => (i * 17 + 3) % 128
      | "five" => (1 <<< 28) + (i % 1_048_573)
      | "ten" => tenByteValues[i % tenByteValues.size]!
      | _ => mixedValues[i % mixedValues.size]!
    values := values.push value
  return values

/-- The out-of-line boundary is also the Callgrind ROI for wire encode. -/
@[noinline]
def encodeVarints (values : Array Nat) : ByteArray :=
  Binary.Put.run do
    for value in values do
      put_varint value

private def getVarintChecksum (count : Nat) : Binary.Get UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:count] do
    checksum := checksum + UInt64.ofNat (← get_varint)
  if (← remaining) != 0 then
    Binary.fail "trailing bytes after the expected varints"
  return checksum

/-- The out-of-line boundary is also the Callgrind ROI for wire decode. -/
@[noinline]
def decodeVarints
    (bytes : ByteArray) (count : Nat) : Except Binary.DecodeError UInt64 :=
  (Binary.Get.run (getVarintChecksum count) bytes).toExcept

def runEncode (cfg : WireConfig) (values : Array Nat) : IO Unit := do
  let warmup := encodeVarints values
  -- Reading through an IO.Ref prevents the optimizer from hoisting this pure
  -- codec call out of the timed loop. The one O(1) read is negligible for the
  -- deliberately large per-iteration payload.
  let valuesRef ← IO.mkRef values
  let mut checksum := 0
  let mut totalBytes := 0
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let bytes := encodeVarints (← valuesRef.get)
    checksum := checksum + consumeBytes bytes
    totalBytes := totalBytes + bytes.size
  let stop ← IO.monoNanosNow
  printTiming "wire varint encode"
    { elapsedNs := stop - start
    , iterations := cfg.iterations
    , processedBytes := totalBytes
    }
    s!"width={cfg.width} values={cfg.valueCount} wire_bytes={warmup.size} checksum={checksum}"

def runDecode (cfg : WireConfig) (values : Array Nat) : IO Unit := do
  let bytes := encodeVarints values
  let warmup ← IO.ofExcept (decodeVarints bytes cfg.valueCount)
  let bytesRef ← IO.mkRef bytes
  let mut checksum : UInt64 := 0
  let start ← IO.monoNanosNow
  for _ in [0:cfg.iterations] do
    let input ← bytesRef.get
    checksum := checksum + (← IO.ofExcept (decodeVarints input cfg.valueCount))
  let stop ← IO.monoNanosNow
  printTiming "wire varint decode"
    { elapsedNs := stop - start
    , iterations := cfg.iterations
    , processedBytes := bytes.size * cfg.iterations
    }
    s!"width={cfg.width} values={cfg.valueCount} wire_bytes={bytes.size} warmup={warmup} checksum={checksum}"

end Test.Bench.Wire

def main (args : List String) : IO Unit := do
  let cfg ← Test.Bench.Wire.readWireConfig args
  let values := Test.Bench.Wire.mkValues cfg.width cfg.valueCount
  if cfg.direction == "encode" then
    Test.Bench.Wire.runEncode cfg values
  else
    Test.Bench.Wire.runDecode cfg values
