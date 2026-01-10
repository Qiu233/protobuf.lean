module

public import Protobuf.Encoding
public import Protobuf.Internal.Desc

public section

namespace Protobuf
namespace Reflection

structure FieldDescriptor where

structure OneofDescriptor where

structure MessageDescriptor where
  proto : google.protobuf.DescriptorProto
  fields : Array FieldDescriptor
  nested_messages : Array MessageDescriptor
