import Protobuf
import Lean.Data.Json

import Protobuf.Notation
import Protobuf.Elab

open Lean
open Protobuf
open scoped Protobuf.Notation

#load_proto_file "Test/Bench/Perf.proto"

namespace Test.Bench

abbrev Meta := _root_.bench.perf.Meta
abbrev Item := _root_.bench.perf.Item
abbrev Batch := _root_.bench.perf.Batch

def ofProtoExcept {α} (e : Except Encoding.ProtoError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw <| IO.userError err.toString

def ofJsonExcept {α} (e : Except String α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw <| IO.userError err

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

def parseNatArg (name : String) (s : String) : IO Nat := do
  match s.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid {name}: {s}"

structure Config where
  itemCount : Nat
  iterations : Nat

def readConfig (args : List String) (defaultItems defaultIterations : Nat) : IO Config := do
  match args with
  | [] => pure { itemCount := defaultItems, iterations := defaultIterations }
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
  ofProtoExcept <| batch.encode

def decodeProto (bytes : ByteArray) : IO Batch :=
  ofProtoExcept <| _root_.bench.perf.Batch.decode bytes

def encodeJson (batch : Batch) : String :=
  (toJson batch).compress

def decodeJson (text : String) : IO Batch :=
  ofJsonExcept <| do
    let json ← Json.parse text
    fromJson? json

def batchChecksum (batch : Batch) : Nat :=
  batch.items.foldl (init := batch.label.length) fun acc item =>
    acc + item.id.toNat + item.name.length + item.note.length + item.payload.size + item.tags.size

end Test.Bench
