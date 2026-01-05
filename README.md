# protobuf
`protobuf` is an implementation of google's protobuf in Lean 4, supporting `proto2`, `proto3`, and `edition`.

# Missing features

❌Won't support:

* Proto1 behaviors: e.g. option `message_set_wire_format` is forbidden.
* EGROUP/SGROUP: the delimited encoding of message is not allowed, though we are able to parse them from wire format. The `edition` `features` enabling this are forbidden.
* proto2 group fields: things like `repeated group Result = 1 { fields... }` are not allowed. Use nested message instead.


Work in progress:

1. Reflection API: e.g. function `descriptor : MsgType -> Descriptor`. The option `no_standard_descriptor_accessor` is currently ignored.
2. Json mapping: designing, likely to be an add-on after we have reflection API.
3. Service/RPC: we will need to think through frameworking issues first. Currently services are ignored.
