module

public import Std

public section

namespace Protobuf.Base64

private def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" |>.toList.toArray

@[always_inline]
private def encodeChar (i : Nat) : Char :=
  alphabet[i]!

@[always_inline]
private def isWhitespace (c : Char) : Bool :=
  if c = ' ' then true
  else if c = '\n' then true
  else if c = '\r' then true
  else if c = '\t' then true
  else false

@[always_inline]
private def decodeChar (c : Char) : Option Nat :=
  let n := c.toNat
  let upperA := ('A' : Char).toNat
  let upperZ := ('Z' : Char).toNat
  let lowerA := ('a' : Char).toNat
  let lowerZ := ('z' : Char).toNat
  let zero_ := ('0' : Char).toNat
  let nine := ('9' : Char).toNat
  if n >= upperA ∧ n <= upperZ then
    some (n - upperA)
  else if n >= lowerA ∧ n <= lowerZ then
    some (n - lowerA + 26)
  else if n >= zero_ ∧ n <= nine then
    some (n - zero_ + 52)
  else if c = '+' then
    some 62
  else if c = '/' then
    some 63
  else
    none

@[always_inline]
private def pushByte (out : ByteArray) (n : Nat) : ByteArray :=
  out.push (UInt8.ofNat n)

public def encode (bs : ByteArray) : String := runST fun σ => do
  let charsRef ← ST.mkRef (σ := σ)
    (Array.emptyWithCapacity (((bs.size + 2) / 3) * 4))
  let iRef ← ST.mkRef (σ := σ) 0
  while (← iRef.get) < bs.size do
    let i ← iRef.get
    let b0 := bs[i]!
    let b1 : UInt8 := if i + 1 < bs.size then bs[i + 1]! else 0
    let b2 : UInt8 := if i + 2 < bs.size then bs[i + 2]! else 0
    let n : Nat :=
      (b0.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b2.toNat
    let c0 := encodeChar ((n >>> 18) &&& 0x3F)
    let c1 := encodeChar ((n >>> 12) &&& 0x3F)
    let c2 := encodeChar ((n >>> 6) &&& 0x3F)
    let c3 := encodeChar (n &&& 0x3F)
    charsRef.modify (·.push c0 |>.push c1)
    if i + 1 < bs.size then
      charsRef.modify (·.push c2)
    else
      charsRef.modify (·.push '=')
    if i + 2 < bs.size then
      charsRef.modify (·.push c3)
    else
      charsRef.modify (·.push '=')
    iRef.modify (· + 3)
  return String.ofList (← charsRef.get).toList

private def decodeQuad (vals : Array (Option Nat)) (out : ByteArray) :
    Except String ByteArray := do
  if vals.size != 4 then
    throw "base64: internal error (quad size)"
  let v0? := vals[0]!
  let v1? := vals[1]!
  let v2? := vals[2]!
  let v3? := vals[3]!
  match v0?, v1?, v2?, v3? with
  | some v0, some v1, some v2, some v3 =>
    let n := (v0 <<< 18) ||| (v1 <<< 12) ||| (v2 <<< 6) ||| v3
    let out := pushByte out ((n >>> 16) &&& 0xFF)
    let out := pushByte out ((n >>> 8) &&& 0xFF)
    return pushByte out (n &&& 0xFF)
  | some v0, some v1, some v2, none =>
    let n := (v0 <<< 18) ||| (v1 <<< 12) ||| (v2 <<< 6)
    let out := pushByte out ((n >>> 16) &&& 0xFF)
    return pushByte out ((n >>> 8) &&& 0xFF)
  | some v0, some v1, none, none =>
    let n := (v0 <<< 18) ||| (v1 <<< 12)
    return pushByte out ((n >>> 16) &&& 0xFF)
  | _, _, _, _ =>
    throw "base64: invalid padding"

public def decode (s : String) : Except String ByteArray :=
  runEST fun σ => do
    let outRef ← ST.mkRef (σ := σ)
      (ByteArray.emptyWithCapacity ((s.length / 4) * 3))
    let bufRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity 4 : Array (Option Nat))
    let sawPaddingRef ← ST.mkRef (σ := σ) false
    for c in s.toList do
      if isWhitespace c then
        continue
      if (← sawPaddingRef.get) then
        throw "base64: trailing data after padding"
      if c = '=' then
        bufRef.modify (·.push none)
      else
        match decodeChar c with
        | some v => bufRef.modify (·.push (some v))
        | none => throw s!"base64: invalid character '{c}'"
      if (← bufRef.get).size == 4 then
        let out ← match decodeQuad (← bufRef.get) (← outRef.get) with
          | Except.ok r => pure r
          | Except.error e => throw e
        outRef.set out
        if (← bufRef.get).any (·.isNone) then
          sawPaddingRef.set true
        bufRef.set #[]
    if (← bufRef.get).size != 0 then
      throw "base64: invalid length"
    return (← outRef.get)

@[always_inline]
public def decodeBase64String (s : String) : Except String String := do
  let bs ← decode s
  match String.fromUTF8? bs with
  | some out => return out
  | none => throw s!"invalid UTF-8 default string literal"

@[always_inline]
public def decode! (s : String) : ByteArray :=
  match decode s with
  | .ok out => out
  | .error err => panic! s!"{decl_name%}: internal error: {err}"

@[always_inline]
public def decodeBase64String! (s : String) : String :=
  match decodeBase64String s with
  | .ok out => out
  | .error err => panic! s!"{decl_name%}: internal error: {err}"


end Base64
