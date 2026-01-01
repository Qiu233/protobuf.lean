import Protobuf.Desc
import Protobuf.Encoding
import Binary

open Protobuf
open Protobuf.Desc
open Protobuf.Encoding
open Binary
open System

def find? (xs : Array α) (p : α → Bool) : Option α :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | some _ => acc
    | none => if p x then some x else none

def hasName (name? : Option String) (expected : String) : Bool :=
  name? == some expected

def findFile (set : FileDescriptorSet) (name : String) : Option FileDescriptorProto :=
  find? set.file fun f => hasName f.name name

def findMessage (file : FileDescriptorProto) (name : String) : Option DescriptorProto :=
  find? file.message_type fun m => hasName m.name name

def findEnum (file : FileDescriptorProto) (name : String) : Option EnumDescriptorProto :=
  find? file.enum_type fun e => hasName e.name name

def findField (msg : DescriptorProto) (name : String) : Option FieldDescriptorProto :=
  find? msg.field fun f => hasName f.name name

def findNestedMessage (msg : DescriptorProto) (name : String) : Option DescriptorProto :=
  find? msg.nested_type fun m => hasName m.name name

def findNestedEnum (msg : DescriptorProto) (name : String) : Option EnumDescriptorProto :=
  find? msg.enum_type fun e => hasName e.name name

def findOneof (msg : DescriptorProto) (name : String) : Option OneofDescriptorProto :=
  find? msg.oneof_decl fun o => hasName o.name name

def findService (file : FileDescriptorProto) (name : String) : Option ServiceDescriptorProto :=
  find? file.service fun s => hasName s.name name

def findMethod (svc : ServiceDescriptorProto) (name : String) : Option MethodDescriptorProto :=
  find? svc.method fun m => hasName m.name name

def isLabelOptional (label? : Option FieldDescriptorProto.Label) : Bool :=
  match label? with
  | some .LABEL_OPTIONAL => true
  | _ => false

def isLabelRepeated (label? : Option FieldDescriptorProto.Label) : Bool :=
  match label? with
  | some .LABEL_REPEATED => true
  | _ => false

def isTypeInt32 (t? : Option FieldDescriptorProto.Type) : Bool :=
  match t? with
  | some .TYPE_INT32 => true
  | _ => false

def isTypeMessage (t? : Option FieldDescriptorProto.Type) : Bool :=
  match t? with
  | some .TYPE_MESSAGE => true
  | _ => false

def protoDecodeErrorToString : ProtoDecodeError → String
  | .truncated => "proto decode error: truncated input"
  | .invalidVarint => "proto decode error: invalid varint"
  | .invalidWireType err => s!"proto decode error: invalid wire type: {err}"
  | .invalidBuffer err => s!"proto decode error: invalid buffer: {err}"
  | .userError err => s!"proto decode error: {err}"

def ofProtoExcept {α} (e : Except ProtoDecodeError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw (IO.userError (protoDecodeErrorToString err))

def isEdition2023 (edition? : Option Edition) : Bool :=
  match edition? with
  | some .EDITION_2023 => true
  | _ => false

def isProto2Syntax (syntax? : Option String) : Bool :=
  syntax? == none || syntax? == some "proto2"

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectSome {α} (o : Option α) (msg : String) : IO α := do
  match o with
  | some v => pure v
  | none => throw (IO.userError msg)

def descriptorSetPath : FilePath :=
  FilePath.mk "Test/official/descriptor_set.bin"

def loadDescriptorSet : IO FileDescriptorSet := do
  let bytes ← IO.FS.readBinFile descriptorSetPath
  let r := Binary.Get.run (Binary.getThe Protobuf.Encoding.Message) bytes
  let msg ← ofProtoExcept (Encoding.protoDecodeParseResultExcept r.toExcept)
  let desc ← ofProtoExcept (FileDescriptorSet.fromMessage msg)
  return desc

def testDescriptorSet : IO Unit := do
  let set ← loadDescriptorSet

  let fdDescriptor ← expectSome (findFile set "google/protobuf/descriptor.proto")
    "missing descriptor.proto in FileDescriptorSet"
  let fdUnittest ← expectSome (findFile set "google/protobuf/unittest.proto")
    "missing unittest.proto in FileDescriptorSet"
  let fdUnittestProto3 ← expectSome (findFile set "google/protobuf/unittest_proto3.proto")
    "missing unittest_proto3.proto in FileDescriptorSet"

  assert (fdDescriptor.package == some "google.protobuf")
    "descriptor.proto package mismatch"
  assert (isProto2Syntax fdDescriptor.syntax)
    "descriptor.proto syntax mismatch"
  let _ ← expectSome (findMessage fdDescriptor "FileDescriptorSet")
    "descriptor.proto missing FileDescriptorSet message"
  let _ ← expectSome (findEnum fdDescriptor "Edition")
    "descriptor.proto missing Edition enum"

  assert (fdUnittest.package == some "proto2_unittest")
    "unittest.proto package mismatch"
  assert (isEdition2023 fdUnittest.edition)
    "unittest.proto edition mismatch"
  assert (fdUnittest.extension.size > 0)
    "unittest.proto expected to have extensions"

  let testAll ← expectSome (findMessage fdUnittest "TestAllTypes")
    "unittest.proto missing TestAllTypes"
  let _ ← expectSome (findNestedMessage testAll "NestedMessage")
    "TestAllTypes missing NestedMessage"
  let _ ← expectSome (findNestedEnum testAll "NestedEnum")
    "TestAllTypes missing NestedEnum"
  let _ ← expectSome (findOneof testAll "oneof_field")
    "TestAllTypes missing oneof_field"
  let optInt32 ← expectSome (findField testAll "optional_int32")
    "TestAllTypes missing optional_int32 field descriptor"
  assert (optInt32.number == some (1 : Int32))
    "optional_int32 number mismatch"
  assert (isLabelOptional optInt32.label)
    "optional_int32 label mismatch"
  assert (isTypeInt32 optInt32.type)
    "optional_int32 type mismatch"
  let repInt32 ← expectSome (findField testAll "repeated_int32")
    "TestAllTypes missing repeated_int32 field descriptor"
  assert (repInt32.number == some (31 : Int32))
    "repeated_int32 number mismatch"
  assert (isLabelRepeated repInt32.label)
    "repeated_int32 label mismatch"
  assert (isTypeInt32 repInt32.type)
    "repeated_int32 type mismatch"
  let optNested ← expectSome (findField testAll "optional_nested_message")
    "TestAllTypes missing optional_nested_message field descriptor"
  assert (isTypeMessage optNested.type)
    "optional_nested_message type mismatch"
  assert (optNested.type_name == some ".proto2_unittest.TestAllTypes.NestedMessage")
    "optional_nested_message type_name mismatch"

  let svc ← expectSome (findService fdUnittest "TestService")
    "unittest.proto missing TestService service"
  let _ ← expectSome (findMethod svc "Foo")
    "TestService missing Foo method"

  assert (fdUnittestProto3.package == some "proto3_unittest")
    "unittest_proto3.proto package mismatch"
  assert (fdUnittestProto3.syntax == some "proto3")
    "unittest_proto3.proto syntax mismatch"
  let _ ← expectSome (findMessage fdUnittestProto3 "TestAllTypes")
    "unittest_proto3.proto missing TestAllTypes"

#eval! testDescriptorSet
