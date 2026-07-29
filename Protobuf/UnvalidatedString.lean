module

public section

namespace Protobuf

/--
The byte representation of a protobuf `string` field whose
`utf8_validation` feature is `NONE`.

Lean's `String` is UTF-8-valid by construction, while protobuf permits these
fields to contain arbitrary bytes. Keeping a distinct nominal type prevents
accidental lossy conversion and distinguishes these fields from `bytes`.
-/
structure UnvalidatedString where
  bytes : ByteArray
deriving Inhabited, BEq, Hashable

instance : Repr UnvalidatedString where
  reprPrec value prec :=
    Repr.addAppParen
      (Std.Format.text "Protobuf.UnvalidatedString.ofBytes" ++
        Std.Format.line ++ reprArg value.bytes.data)
      prec

@[always_inline]
def UnvalidatedString.empty : UnvalidatedString := ⟨ByteArray.empty⟩

instance : EmptyCollection UnvalidatedString := ⟨UnvalidatedString.empty⟩

@[always_inline]
def UnvalidatedString.ofBytes (bytes : ByteArray) : UnvalidatedString := ⟨bytes⟩

@[always_inline]
def UnvalidatedString.ofString (value : String) : UnvalidatedString :=
  ⟨value.toUTF8⟩

instance : Coe String UnvalidatedString := ⟨UnvalidatedString.ofString⟩

@[always_inline]
def UnvalidatedString.toString? (value : UnvalidatedString) : Option String :=
  String.fromUTF8? value.bytes

@[always_inline]
def UnvalidatedString.isEmpty (value : UnvalidatedString) : Bool :=
  value.bytes.isEmpty

end Protobuf
