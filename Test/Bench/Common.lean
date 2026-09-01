import Protobuf
import Protobuf.Json
import Lean.Data.Json

import Protobuf.Notation
import Protobuf.Elab
import Test.Bench.Harness

open Lean
open Protobuf
open scoped Protobuf.Notation

#load_proto_file "Test/Bench/Perf.proto"

namespace Test.Bench

abbrev Meta := _root_.bench.perf.Meta
abbrev Item := _root_.bench.perf.Item
abbrev Batch := _root_.bench.perf.Batch

def ofProtoExcept {α} (e : Except Encoding.ProtoError α) : IO α :=
  IO.ofExcept e

def ofJsonExcept {α} (e : Except String α) : IO α :=
  IO.ofExcept e

instance : ToJson Meta where
  toJson v := json% {
    "source": $(v.source),
    "created_at": $(v.created_at),
    "active": $(v.active)
  }

instance : FromJson Meta where
  fromJson? j := do
    pure
      { source := ← Json.getObjValAs? j String "source"
      , created_at := ← Json.getObjValAs? j UInt64 "created_at"
      , active := ← Json.getObjValAs? j Bool "active"
      , «Unknown.Fields» := {}
      }

instance : ToJson Item where
  toJson v := json% {
    "id": $(v.id.toNat),
    "name": $(v.name),
    "scores": $(v.scores.map Int32.toInt),
    "payload": $(Protobuf.Base64.encode v.payload),
    "meta": $(v.«meta»),
    "tags": $(v.tags),
    "note": $(v.note)
  }

instance : FromJson Item where
  fromJson? j := do
    let id : Nat ← Json.getObjValAs? j Nat "id"
    let scores : Array Int ← Json.getObjValAs? j (Array Int) "scores"
    let payload64 : String ← Json.getObjValAs? j String "payload"
    let payload ←
      match Protobuf.Base64.decode payload64 with
      | .ok bs => pure bs
      | .error err => throw s!"invalid base64 bytes payload: {err}"
    pure
      { id := UInt32.ofNat id
      , name := ← Json.getObjValAs? j String "name"
      , scores := scores.map Int32.ofInt
      , payload := payload
      , «meta» := ← Json.getObjValAs? j Meta "meta"
      , tags := ← Json.getObjValAs? j (Array String) "tags"
      , note := ← Json.getObjValAs? j String "note"
      , «Unknown.Fields» := {}
      }

instance : ToJson Batch where
  toJson v := json% {
    "items": $(v.items),
    "label": $(v.label)
  }

instance : FromJson Batch where
  fromJson? j := do
    pure
      { items := ← Json.getObjValAs? j (Array Item) "items"
      , label := ← Json.getObjValAs? j String "label"
      , «Unknown.Fields» := {}
      }

def mkPayload (seed len : Nat) : ByteArray :=
  ByteArray.mk <| Id.run do
    let mut out := #[]
    for i in [0:len] do
      out := out.push <| UInt8.ofNat ((seed * 31 + i * 17 + 13) % 251)
    out

def mkMeta (i : Nat) : Meta :=
  { source := s!"source-{i % 11}"
  , created_at := UInt64.ofNat (1_700_000_000 + i * 17)
  , active := i % 2 == 0
  , «Unknown.Fields» := {}
  }

def mkScores (i : Nat) : Array Int32 :=
  Id.run do
    let mut out := #[]
    for j in [0:8] do
      out := out.push <| Int32.ofInt (Int.ofNat ((i + 1) * (j + 3)) - 19)
    out

def mkTags (i : Nat) : Array String :=
  #[
    s!"tag-{i % 5}",
    s!"group-{i % 9}",
    s!"bucket-{i % 13}",
    s!"region-{i % 7}"
  ]

def mkItem (i : Nat) : Item :=
  { id := UInt32.ofNat i
  , name := s!"item-{i}"
  , scores := mkScores i
  , payload := mkPayload i (48 + i % 16)
  , «meta» := mkMeta i
  , tags := mkTags i
  , note := s!"note-{i % 17}-{i * 3}"
  , «Unknown.Fields» := {}
  }

def mkBatch (itemCount : Nat) : Batch :=
  { items := Id.run do
      let mut out := #[]
      for i in [0:itemCount] do
        out := out.push (mkItem i)
      out
  , label := s!"batch-{itemCount}"
  , «Unknown.Fields» := {}
  }

def encodeProto (batch : Batch) : IO ByteArray :=
  ofProtoExcept <| Protobuf.encode batch

def decodeProto (bytes : ByteArray) : IO Batch :=
  ofProtoExcept <| Protobuf.decodeThe _root_.bench.perf.Batch bytes

def encodeLeanJson (batch : Batch) : String :=
  (toJson batch).compress

def decodeLeanJson (text : String) : IO Batch :=
  ofJsonExcept <| do
    let json ← Json.parse text
    fromJson? json

def encodeProtoJson (batch : Batch) : IO String := do
  IO.ofExcept (← Protobuf.Json.toJsonString batch)

def decodeProtoJson (text : String) : IO Batch := do
  IO.ofExcept (← Protobuf.Json.fromJsonString text Batch)

private abbrev fnvOffset : UInt64 := 14695981039346656037
private abbrev fnvPrime : UInt64 := 1099511628211

@[inline]
private def hashByte (hash : UInt64) (byte : UInt8) : UInt64 :=
  (hash ^^^ byte.toUInt64) * fnvPrime

private def hashUInt64 (hash value : UInt64) : UInt64 := Id.run do
  let mut hash := hash
  let mut value := value
  for _ in [0:8] do
    hash := hashByte hash value.toUInt8
    value := value >>> 8
  return hash

private def hashByteArray (hash : UInt64) (bytes : ByteArray) : UInt64 :=
  bytes.data.foldl hashByte (hashUInt64 hash (UInt64.ofNat bytes.size))

private def hashString (hash : UInt64) (text : String) : UInt64 :=
  hashByteArray hash text.toUTF8

/--
A stable, allocation-light content fingerprint used to verify every benchmark
implementation operates on the same logical message. It covers every known
field in `Perf.proto`; unknown fields are intentionally absent from this
workload.
-/
def batchContentHash (batch : Batch) : UInt64 := Id.run do
  let mut hash := hashString fnvOffset batch.label
  hash := hashUInt64 hash (UInt64.ofNat batch.items.size)
  for item in batch.items do
    hash := hashUInt64 hash item.id.toUInt64
    hash := hashString hash item.name
    hash := hashUInt64 hash (UInt64.ofNat item.scores.size)
    for score in item.scores do
      hash := hashUInt64 hash score.toUInt32.toUInt64
    hash := hashByteArray hash item.payload
    match item.«meta» with
    | none =>
        hash := hashByte hash 0
    | some metadata =>
        hash := hashByte hash 1
        hash := hashString hash metadata.source
        hash := hashUInt64 hash metadata.created_at
        hash := hashByte hash (if metadata.active then 1 else 0)
    hash := hashUInt64 hash (UInt64.ofNat item.tags.size)
    for tag in item.tags do
      hash := hashString hash tag
    hash := hashString hash item.note
  return hash

def byteArrayHash (bytes : ByteArray) : UInt64 :=
  bytes.data.foldl hashByte fnvOffset

def stringHash (text : String) : UInt64 :=
  byteArrayHash text.toUTF8

/-- O(1) consumer for the timed decode loop. -/
@[noinline]
def consumeBatch (batch : Batch) : Nat :=
  if batch.items.isEmpty then
    batch.label.length
  else
    batch.items.size +
      batch.items[0]!.id.toNat +
      batch.items[batch.items.size - 1]!.id.toNat +
      batch.label.length

/-- O(1) consumer for timed JSON encoding loops. -/
@[noinline]
def consumeString (text : String) : Nat :=
  text.utf8ByteSize

end Test.Bench
