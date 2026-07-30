module

public import Lean.Data.Json
public import Protobuf.Reflection

public section

namespace Protobuf.Json

open Protobuf.Reflection

inductive Error where
  | invalidJson (detail : String)
  | typeMismatch (path expected actual : String)
  | invalidValue (path detail : String)
  | unknownField (path name : String)
  | duplicateField (path name : String)
  | unresolvedType (typeName : String)
  | recursionLimit (path : String)
  | missingRequiredField (path fieldName : String)
  | reflection (error : ReflectionError)
deriving Repr

instance : ToString Error where
  toString
    | .invalidJson detail => s!"invalid JSON: {detail}"
    | .typeMismatch path expected actual =>
        s!"{path}: expected {expected}, got {actual}"
    | .invalidValue path detail => s!"{path}: {detail}"
    | .unknownField path name => s!"{path}: unknown field `{name}`"
    | .duplicateField path name =>
        s!"{path}: field `{name}` is specified more than once"
    | .unresolvedType name => s!"cannot resolve protobuf type `{name}`"
    | .recursionLimit path => s!"{path}: ProtoJSON recursion limit exceeded"
    | .missingRequiredField path name =>
        s!"{path}: required field `{name}` is absent"
    | .reflection error => toString error

structure PrintOptions where
  /-- Emit implicit-presence scalars with default values and empty collections. -/
  emitFieldsWithoutPresence : Bool := false
  useProtoFieldNames : Bool := false
  useEnumNumbers : Bool := false
  pretty : Bool := false
  lineWidth : Nat := 80
  allowPartial : Bool := false
  recursionLimit : Nat := 100
  extensions : Option ExtensionResolver := none
  types : Option TypeResolver := none

structure ParseOptions where
  discardUnknownFields : Bool := false
  allowPartial : Bool := false
  recursionLimit : Nat := 100
  extensions : Option ExtensionResolver := none
  types : Option TypeResolver := none

def PrintOptions.withGeneratedPool
    (options : PrintOptions := {}) : PrintOptions :=
  { options with
    extensions := some generatedExtensionResolver
    types := some generatedTypeResolver
  }

def ParseOptions.withGeneratedPool
    (options : ParseOptions := {}) : ParseOptions :=
  { options with
    extensions := some generatedExtensionResolver
    types := some generatedTypeResolver
  }

end Protobuf.Json
