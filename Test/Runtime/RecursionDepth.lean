module

import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/Fixtures/Schemas/RecursionDepth.proto"

private def lengthDelimited (fieldNum : Nat) (payload : ByteArray) :
    ByteArray :=
  Binary.Put.run do
    put_varint ((fieldNum <<< 3) ||| 2)
    put_varint payload.size
    Binary.put_bytes payload

private def chain (fieldNum depth : Nat) : ByteArray :=
  (List.range depth).foldl
    (fun payload _ => lengthDelimited fieldNum payload) {}

private def group (fieldNum : Nat) (payload : ByteArray) : ByteArray :=
  Binary.Put.run do
    put_varint ((fieldNum <<< 3) ||| 3)
    Binary.put_bytes payload
    put_varint ((fieldNum <<< 3) ||| 4)

private def groupChain (depth : Nat) : ByteArray :=
  (List.range depth).foldl
    (fun payload _ => group 7 payload) {}

private def mapChainFrom (payload : ByteArray) (depth : Nat) : ByteArray :=
  (List.range depth).foldl
    (fun payload _ =>
      let entry := lengthDelimited 2 payload
      lengthDelimited 3 entry)
    payload

private def mapChain (depth : Nat) : ByteArray :=
  mapChainFrom {} depth

private def messageAndGroupChain
    (messageDepth groupDepth : Nat) : ByteArray :=
  (List.range messageDepth).foldl
    (fun payload _ => lengthDelimited 1 payload)
    (groupChain groupDepth)

private def repeatedSiblings (count : Nat) : ByteArray :=
  (List.range count).foldl
    (fun payload _ =>
      payload.append (lengthDelimited 2 {}))
    {}

private def parses (bytes : ByteArray) : Bool :=
  (Protobuf.decodeThe _root_.test.recursion_depth.Node bytes).isOk

private def fails (bytes : ByteArray) : Bool :=
  match Protobuf.decodeThe _root_.test.recursion_depth.Node bytes with
  | .error _ => true
  | .ok _ => false

private def mutualParses (bytes : ByteArray) : Bool :=
  (Protobuf.decodeThe _root_.test.recursion_depth.MutualA bytes).isOk

private def hitsRecursionLimit (bytes : ByteArray) : Bool :=
  match Protobuf.decodeThe _root_.test.recursion_depth.Node bytes with
  | .error (.userError errorMessage) =>
      errorMessage == "protobuf: message recursion limit exceeded"
  | _ => false

private def mutualHitsRecursionLimit (bytes : ByteArray) : Bool :=
  match Protobuf.decodeThe _root_.test.recursion_depth.MutualA bytes with
  | .error (.userError errorMessage) =>
      errorMessage == "protobuf: message recursion limit exceeded"
  | _ => false

/-- info: true -/
#guard_msgs (info) in
#eval parses (chain 1 100)

/-- info: true -/
#guard_msgs (info) in
#eval hitsRecursionLimit (chain 1 101)

/-- info: true -/
#guard_msgs (info) in
#eval parses (chain 2 100)

/-- info: true -/
#guard_msgs (info) in
#eval hitsRecursionLimit (chain 2 101)

/-- info: true -/
#guard_msgs (info) in
#eval parses (chain 4 100)

/-- info: true -/
#guard_msgs (info) in
#eval hitsRecursionLimit (chain 4 101)

/- A map link enters both the synthetic map-entry message and its message value. -/
/-- info: true -/
#guard_msgs (info) in
#eval parses (mapChain 50)

/-- info: true -/
#guard_msgs (info) in
#eval hitsRecursionLimit (mapChain 51)

/-
Message and legacy-group nesting share one budget in official runtimes. The
group is unknown to this schema, but its structural nesting still consumes the
remaining wire-parser recursion budget.
-/
/-- info: true -/
#guard_msgs (info) in
#eval parses (messageAndGroupChain 98 2)

/-- info: true -/
#guard_msgs (info) in
#eval fails (messageAndGroupChain 98 3)

/-- info: true -/
#guard_msgs (info) in
#eval parses (messageAndGroupChain 99 1)

/-- info: true -/
#guard_msgs (info) in
#eval fails (messageAndGroupChain 99 2)

/-- info: true -/
#guard_msgs (info) in
#eval parses (messageAndGroupChain 100 0)

/-- info: true -/
#guard_msgs (info) in
#eval fails (messageAndGroupChain 100 1)

/-- info: true -/
#guard_msgs (info) in
#eval parses (mapChainFrom (groupChain 2) 49)

/-- info: true -/
#guard_msgs (info) in
#eval fails (mapChainFrom (groupChain 3) 49)

/-- info: true -/
#guard_msgs (info) in
#eval mutualParses (chain 1 100)

/-- info: true -/
#guard_msgs (info) in
#eval mutualHitsRecursionLimit (chain 1 101)

/- Sibling repeated elements restore the budget after each embedded message. -/
/-- info: true -/
#guard_msgs (info) in
#eval parses (repeatedSiblings 1000)

/- Unknown LEN and bytes payloads are opaque, even if their contents look nested. -/
/-- info: true -/
#guard_msgs (info) in
#eval parses (chain 100 1000)

/-- info: true -/
#guard_msgs (info) in
#eval parses (lengthDelimited 6 (chain 1 1000))
