module

public section

namespace Protobuf.Encoding

mutual

inductive ProtoVal where
  | VARINT (val : Nat)      -- 0
  | I64 (val : BitVec 64)   -- 1
  | LEN (data : ByteArray)  -- 2
  /-- `GROUPED` is not real wire type -/
  | GROUPED (subMessage : Message) -- 34
  | I32 (val : BitVec 32)   -- 5
deriving Inhabited

structure Record where
  fieldNum : Nat
  value : ProtoVal
deriving Inhabited

structure Message where
  records : Array Record
deriving Inhabited

end

@[always_inline]
def Message.combine : Message → Message → Message := fun a b => Message.mk (a.records ++ b.records)

@[always_inline]
def ProtoVal.isVARINT : ProtoVal → Bool
  | .VARINT .. => true
  | _ => false

@[always_inline]
def ProtoVal.isVARINT? : ProtoVal → Option Nat
  | .VARINT n => some n
  | _ => none

@[always_inline]
def ProtoVal.isI64 : ProtoVal → Bool
  | .I64 .. => true
  | _ => false

@[always_inline]
def ProtoVal.isI64? : ProtoVal → Option (BitVec 64)
  | .I64 x => some x
  | _ => none

@[always_inline]
def ProtoVal.isLEN : ProtoVal → Bool
  | .LEN .. => true
  | _ => false

@[always_inline]
def ProtoVal.isLEN? : ProtoVal → Option ByteArray
  | .LEN d => some d
  | _ => none

@[always_inline]
def ProtoVal.isI32 : ProtoVal → Bool
  | .I32 .. => true
  | _ => false

@[always_inline]
def ProtoVal.isI32? : ProtoVal → Option (BitVec 32)
  | .I32 x => some x
  | _ => none

@[always_inline]
def ProtoVal.isScalar : ProtoVal → Bool
  | .VARINT .. => true
  | .I64 .. => true
  | .I32 .. => true
  | _ => false

@[always_inline]
def ProtoVal.isGROUPED : ProtoVal → Bool
  | .GROUPED .. => true
  | _ => false

@[always_inline]
def Message.empty : Message := Message.mk Array.empty

@[always_inline]
def Message.emptyWithCapacity (capacity : Nat) : Message := Message.mk (Array.emptyWithCapacity capacity)

/-!
* We only derive the instances if `Repr ByteArray` is present.
* These instances are `scoped`, that is, only have effect when the namespace is opened.
-/
public section

mutual

variable [Repr ByteArray]

private unsafe instance instReprProtoValUnsafe : Repr ProtoVal where
  reprPrec x prec := match x with
      | ProtoVal.VARINT a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.VARINT" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.I64 a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.I64" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.LEN a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.LEN" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.GROUPED a =>
        have := instReprMessageUnsafe
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.GROUPED" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.I32 a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.I32" ++ Std.Format.line ++ reprArg a)).group
          prec

private unsafe instance instReprRecordUnsafe : Repr Record where
  reprPrec x prec :=
      have := instReprProtoValUnsafe
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "fieldNum" ++ Std.Format.text " := " ++
                    (Std.Format.nest 13 (repr x.fieldNum)).group ++
                  Std.Format.text "," ++
                Std.Format.line ++
              Std.Format.text "value" ++
            Std.Format.text " := " ++
          (Std.Format.nest 9 (repr x.value)).group)
        " }"

private unsafe instance instReprMessageUnsafe : Repr Message where
  reprPrec x prec :=
      have := instReprRecordUnsafe
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "records" ++ Std.Format.text " := " ++
          (Std.Format.nest 11 (repr x.records)).group)
        " }"

end

@[implemented_by instReprProtoValUnsafe, scoped instance]
opaque instReprProtoValOfReprByteArray [Repr ByteArray] : Repr ProtoVal := ⟨fun _ _ => ""⟩

@[implemented_by instReprRecordUnsafe, scoped instance]
opaque instReprRecordOfReprByteArray [Repr ByteArray] : Repr Record := ⟨fun _ _ => ""⟩

@[implemented_by instReprMessageUnsafe, scoped instance]
opaque instReprMessageOfReprByteArray [Repr ByteArray] : Repr Message := ⟨fun _ _ => ""⟩

end
