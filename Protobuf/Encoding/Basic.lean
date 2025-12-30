module

public section

namespace Protobuf.Encoding

inductive ProtoVal where
  | VARINT (val : Nat)      -- 0
  | I64 (val : BitVec 64)   -- 1
  | LEN (data : ByteArray)  -- 2
  | I32 (val : BitVec 32)   -- 5

structure Record where
  field_num : Nat
  value : ProtoVal

structure Message where
  records : Array Record

/-!
* We only derive the instances if `Repr ByteArray` is present.
* These instances are `scoped`, that is, only have effect when the namespace is opened.
-/
public section

variable [Repr ByteArray]

scoped instance : Repr ProtoVal where
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
      | ProtoVal.I32 a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.I32" ++ Std.Format.line ++ reprArg a)).group
          prec

scoped instance : Repr Record where
  reprPrec x prec :=
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "field_num" ++ Std.Format.text " := " ++
                    (Std.Format.nest 13 (repr x.field_num)).group ++
                  Std.Format.text "," ++
                Std.Format.line ++
              Std.Format.text "value" ++
            Std.Format.text " := " ++
          (Std.Format.nest 9 (repr x.value)).group)
        " }"

scoped instance : Repr Message where
  reprPrec x prec :=
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "records" ++ Std.Format.text " := " ++
          (Std.Format.nest 11 (repr x.records)).group)
        " }"

end
