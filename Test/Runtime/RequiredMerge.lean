module

import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/Fixtures/Schemas/RequiredMergeProto2.proto"
#load_proto_file "Test/Fixtures/Schemas/RequiredMergeEditions.proto"

private def assert (condition : Bool) (detail : String) : IO Unit := do
  unless condition do
    throw (IO.userError detail)

private def assertMissingRequired
    (result : Except ProtoError α) (detail : String) : IO Unit := do
  match result with
  | .error (.missingRequiredField _) => pure ()
  | .error error =>
      throw (IO.userError s!"{detail}: expected missingRequiredField, got {error}")
  | .ok _ =>
      throw (IO.userError s!"{detail}: unexpectedly succeeded")

private def assertInvalidBuffer
    (result : Except ProtoError α) (detail : String) : IO Unit := do
  match result with
  | .error (.invalidBuffer _) => pure ()
  | .error error =>
      throw (IO.userError s!"{detail}: expected invalidBuffer, got {error}")
  | .ok _ =>
      throw (IO.userError s!"{detail}: unexpectedly succeeded")

private def assertTruncated
    (result : Except ProtoError α) (detail : String) : IO Unit := do
  match result with
  | .error .truncated => pure ()
  | .error error =>
      throw (IO.userError s!"{detail}: expected truncated, got {error}")
  | .ok _ =>
      throw (IO.userError s!"{detail}: unexpectedly succeeded")

private def splitChildWire : ByteArray :=
  ⟨#[0x0a, 0x02, 0x08, 0x01, 0x0a, 0x02, 0x10, 0x02]⟩

private def incompleteChildWire : ByteArray :=
  ⟨#[0x0a, 0x02, 0x08, 0x01]⟩

private def mapEntryMissingValueWire : ByteArray :=
  ⟨#[0x0a, 0x02, 0x08, 0x01]⟩

private def mapEntryEmptyValueWire : ByteArray :=
  ⟨#[0x0a, 0x04, 0x08, 0x01, 0x12, 0x00]⟩

private def mapIncompleteThenCompleteWire : ByteArray :=
  ⟨#[
    0x0a, 0x06, 0x08, 0x01, 0x12, 0x02, 0x08, 0x01,
    0x0a, 0x08, 0x08, 0x01, 0x12, 0x04, 0x08, 0x01, 0x10, 0x02
  ]⟩

private def mapCompleteThenIncompleteWire : ByteArray :=
  ⟨#[
    0x0a, 0x08, 0x08, 0x01, 0x12, 0x04, 0x08, 0x01, 0x10, 0x02,
    0x0a, 0x06, 0x08, 0x01, 0x12, 0x02, 0x08, 0x01
  ]⟩

private def mapSplitValueInOneEntryWire : ByteArray :=
  ⟨#[
    0x0a, 0x0a, 0x08, 0x01,
    0x12, 0x02, 0x08, 0x01,
    0x12, 0x02, 0x10, 0x02
  ]⟩

private def mapIncompleteEntriesDoNotMergeWire : ByteArray :=
  ⟨#[
    0x0a, 0x06, 0x08, 0x01, 0x12, 0x02, 0x08, 0x01,
    0x0a, 0x06, 0x08, 0x01, 0x12, 0x02, 0x10, 0x02
  ]⟩

private def mapWrongKeyWire : ByteArray :=
  ⟨#[
    0x0a, 0x0b,
    0x0d, 0x01, 0x00, 0x00, 0x00,
    0x12, 0x04, 0x08, 0x01, 0x10, 0x02
  ]⟩

private def mapWrongValueWire : ByteArray :=
  ⟨#[0x0a, 0x04, 0x08, 0x01, 0x10, 0x01]⟩

private def incompleteThenScalarWire : ByteArray :=
  ⟨#[0x0a, 0x02, 0x08, 0x01, 0x10, 0x07]⟩

private def scalarThenIncompleteWire : ByteArray :=
  ⟨#[0x10, 0x07, 0x0a, 0x02, 0x08, 0x01]⟩

private def invalidUtf8ThenScalarWire : ByteArray :=
  ⟨#[0x0a, 0x03, 0x1a, 0x01, 0xff, 0x10, 0x07]⟩

private def deferredErrorThenMapReplacementWire : ByteArray :=
  ⟨#[
    0x0a, 0x0b, 0x08, 0x01, 0x12, 0x07,
    0x0a, 0x00, 0x12, 0x03, 0x0a, 0x01, 0xff,
    0x0a, 0x04, 0x08, 0x01, 0x12, 0x00
  ]⟩

private def deferredErrorThenOneofScalarWire : ByteArray :=
  ⟨#[
    0x0a, 0x07, 0x0a, 0x00, 0x12, 0x03, 0x0a, 0x01, 0xff,
    0x10, 0x07
  ]⟩

private def testProto2 : IO Unit := do
  let optional ←
    match Protobuf.decodeThe _root_.test.required_merge.proto2.OptionalOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"proto2 optional split merge failed: {error}")
  let some child := optional.child
    | throw (IO.userError "proto2 optional split merge lost child presence")
  assert (child.a == some 1 && child.b == some 2)
    "proto2 optional split merge lost required child fields"

  let required ←
    match Protobuf.decodeThe _root_.test.required_merge.proto2.RequiredOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"proto2 required split merge failed: {error}")
  let some child := required.child
    | throw (IO.userError "proto2 required split merge lost child presence")
  assert (child.a == some 1 && child.b == some 2)
    "proto2 required split merge lost required child fields"

  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.OptionalOuter incompleteChildWire)
    "proto2 optional final child initialization"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.RequiredOuter incompleteChildWire)
    "proto2 required final child initialization"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.RepeatedOuter splitChildWire)
    "proto2 repeated child occurrences must remain distinct elements"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
      mapEntryMissingValueWire)
    "proto2 map entry with an absent message value"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
      mapEntryEmptyValueWire)
    "proto2 map entry with an explicit empty message value"
  let mapReplaced ←
    match Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
        mapIncompleteThenCompleteWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError
          s!"proto2 losing incomplete map value was not replaced: {error}")
  let some mapChild := mapReplaced.children[(1 : Int32)]?
    | throw (IO.userError "proto2 replacement map value is absent")
  assert (mapChild.a == some 1 && mapChild.b == some 2)
    "proto2 replacement map value changed"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
      mapCompleteThenIncompleteWire)
    "proto2 final incomplete duplicate map value"
  let mapMerged ←
    match Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
        mapSplitValueInOneEntryWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError
          s!"proto2 repeated value records in one map entry did not merge: {error}")
  let some mergedMapChild := mapMerged.children[(1 : Int32)]?
    | throw (IO.userError "proto2 merged map value is absent")
  assert (mergedMapChild.a == some 1 && mergedMapChild.b == some 2)
    "proto2 repeated value records in one map entry lost fields"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter
      mapIncompleteEntriesDoNotMergeWire)
    "proto2 duplicate map entries must replace rather than merge"
  assertTruncated
    (Protobuf.decodeThe _root_.test.required_merge.proto2.DeferredErrorMapOuter
      deferredErrorThenMapReplacementWire)
    "proto2 malformed losing duplicate map value"
  for (wire, detail) in #[
      (mapWrongKeyWire, "key"),
      (mapWrongValueWire, "value")
    ] do
    let decoded ←
      match Protobuf.decodeThe _root_.test.required_merge.proto2.MapOuter wire with
      | .ok value => pure value
      | .error error =>
          throw (IO.userError
            s!"proto2 map entry with wrong-wire inner {detail} failed: {error}")
    assert decoded.children.isEmpty
      s!"proto2 wrong-wire inner {detail} populated the map"
    assert (match decoded.«Unknown.Fields»[1]? with
      | some values =>
          values.size == 1 && values[0]!.isLEN
      | none => false)
      s!"proto2 wrong-wire inner {detail} did not retain the outer entry"

  let sameCase ←
    match Protobuf.decodeThe _root_.test.required_merge.proto2.OneofOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"proto2 oneof same-case split merge failed: {error}")
  match sameCase.choice with
  | some (.child child) =>
      assert (child.a == some 1 && child.b == some 2)
        "proto2 oneof same-case split merge lost required fields"
  | _ =>
      throw (IO.userError "proto2 oneof same-case split merge selected wrong case")

  let cleared ←
    match
      Protobuf.decodeThe _root_.test.required_merge.proto2.OneofOuter
        incompleteThenScalarWire
    with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"proto2 cleared incomplete oneof failed: {error}")
  match cleared.choice with
  | some (.scalar value) =>
      assert (value == 7) "proto2 cleared oneof scalar value changed"
  | _ =>
      throw (IO.userError "proto2 later oneof scalar did not clear incomplete message")

  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.proto2.OneofOuter scalarThenIncompleteWire)
    "proto2 final incomplete oneof message"
  assertTruncated
    (Protobuf.decodeThe _root_.test.required_merge.proto2.DeferredErrorOneofOuter
      deferredErrorThenOneofScalarWire)
    "proto2 malformed cleared oneof message"

  let merged :=
    _root_.test.required_merge.proto2.OneofOuter.«protobuf.internal».merge
      {
        choice := some (.child { a := some 1 })
      }
      {
        choice := some (.child { b := some 2 })
      }
  match merged.choice with
  | some (.child child) =>
      assert (child.a == some 1 && child.b == some 2)
        "proto2 MergeFrom did not recursively merge the same oneof message case"
  | _ =>
      throw (IO.userError "proto2 MergeFrom selected wrong oneof case")

  let replaced :=
    _root_.test.required_merge.proto2.OneofOuter.«protobuf.internal».merge merged {
      choice := some (.scalar 7)
    }
  match replaced.choice with
  | some (.scalar value) =>
      assert (value == 7) "proto2 MergeFrom changed later oneof scalar"
  | _ =>
      throw (IO.userError "proto2 MergeFrom did not replace a different oneof case")

private def testEditions : IO Unit := do
  let optional ←
    match Protobuf.decodeThe _root_.test.required_merge.editions.OptionalOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"Editions optional split merge failed: {error}")
  let some child := optional.child
    | throw (IO.userError "Editions optional split merge lost child presence")
  assert (child.a == some 1 && child.b == some 2)
    "Editions optional split merge lost required child fields"

  let required ←
    match Protobuf.decodeThe _root_.test.required_merge.editions.RequiredOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"Editions required split merge failed: {error}")
  let some child := required.child
    | throw (IO.userError "Editions required split merge lost child presence")
  assert (child.a == some 1 && child.b == some 2)
    "Editions required split merge lost required child fields"

  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.OptionalOuter incompleteChildWire)
    "Editions optional final child initialization"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.RequiredOuter incompleteChildWire)
    "Editions required final child initialization"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.RepeatedOuter splitChildWire)
    "Editions repeated child occurrences must remain distinct elements"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
      mapEntryMissingValueWire)
    "Editions map entry with an absent message value"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
      mapEntryEmptyValueWire)
    "Editions map entry with an explicit empty message value"
  let mapReplaced ←
    match Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
        mapIncompleteThenCompleteWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError
          s!"Editions losing incomplete map value was not replaced: {error}")
  let some mapChild := mapReplaced.children[(1 : Int32)]?
    | throw (IO.userError "Editions replacement map value is absent")
  assert (mapChild.a == some 1 && mapChild.b == some 2)
    "Editions replacement map value changed"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
      mapCompleteThenIncompleteWire)
    "Editions final incomplete duplicate map value"
  let mapMerged ←
    match Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
        mapSplitValueInOneEntryWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError
          s!"Editions repeated value records in one map entry did not merge: {error}")
  let some mergedMapChild := mapMerged.children[(1 : Int32)]?
    | throw (IO.userError "Editions merged map value is absent")
  assert (mergedMapChild.a == some 1 && mergedMapChild.b == some 2)
    "Editions repeated value records in one map entry lost fields"
  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter
      mapIncompleteEntriesDoNotMergeWire)
    "Editions duplicate map entries must replace rather than merge"
  assertTruncated
    (Protobuf.decodeThe _root_.test.required_merge.editions.DeferredErrorMapOuter
      deferredErrorThenMapReplacementWire)
    "Editions malformed losing duplicate map value"
  for (wire, detail) in #[
      (mapWrongKeyWire, "key"),
      (mapWrongValueWire, "value")
    ] do
    let decoded ←
      match Protobuf.decodeThe _root_.test.required_merge.editions.MapOuter wire with
      | .ok value => pure value
      | .error error =>
          throw (IO.userError
            s!"Editions map entry with wrong-wire inner {detail} failed: {error}")
    assert decoded.children.isEmpty
      s!"Editions wrong-wire inner {detail} populated the map"
    assert (match decoded.«Unknown.Fields»[1]? with
      | some values =>
          values.size == 1 && values[0]!.isLEN
      | none => false)
      s!"Editions wrong-wire inner {detail} did not retain the outer entry"

  let sameCase ←
    match Protobuf.decodeThe _root_.test.required_merge.editions.OneofOuter splitChildWire with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"Editions oneof same-case split merge failed: {error}")
  match sameCase.choice with
  | some (.child child) =>
      assert (child.a == some 1 && child.b == some 2)
        "Editions oneof same-case split merge lost required fields"
  | _ =>
      throw (IO.userError "Editions oneof same-case split merge selected wrong case")

  let cleared ←
    match
      Protobuf.decodeThe _root_.test.required_merge.editions.OneofOuter
        incompleteThenScalarWire
    with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"Editions cleared incomplete oneof failed: {error}")
  match cleared.choice with
  | some (.scalar value) =>
      assert (value == 7) "Editions cleared oneof scalar value changed"
  | _ =>
      throw (IO.userError "Editions later oneof scalar did not clear incomplete message")

  assertMissingRequired
    (Protobuf.decodeThe _root_.test.required_merge.editions.OneofOuter scalarThenIncompleteWire)
    "Editions final incomplete oneof message"
  assertInvalidBuffer
    (Protobuf.decodeThe _root_.test.required_merge.editions.OneofOuter
      invalidUtf8ThenScalarWire)
    "Editions invalid UTF-8 in a cleared oneof message"
  assertTruncated
    (Protobuf.decodeThe _root_.test.required_merge.editions.DeferredErrorOneofOuter
      deferredErrorThenOneofScalarWire)
    "Editions malformed cleared oneof message"

  let merged :=
    _root_.test.required_merge.editions.OneofOuter.«protobuf.internal».merge
      {
        choice := some (.child { a := some 1 })
      }
      {
        choice := some (.child { b := some 2 })
      }
  match merged.choice with
  | some (.child child) =>
      assert (child.a == some 1 && child.b == some 2)
        "Editions MergeFrom did not recursively merge the same oneof message case"
  | _ =>
      throw (IO.userError "Editions MergeFrom selected wrong oneof case")

  let replaced :=
    _root_.test.required_merge.editions.OneofOuter.«protobuf.internal».merge merged {
      choice := some (.scalar 7)
    }
  match replaced.choice with
  | some (.scalar value) =>
      assert (value == 7) "Editions MergeFrom changed later oneof scalar"
  | _ =>
      throw (IO.userError "Editions MergeFrom did not replace a different oneof case")

public def main : IO Unit := do
  testProto2
  testEditions

#eval! main
