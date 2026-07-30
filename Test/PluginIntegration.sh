#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
plugin="$repo_root/.lake/build/bin/protoc-gen-lean4"
protoc_bin="${PROTOC:-protoc}"

if [[ ! -x "$plugin" ]]; then
  echo "plugin executable is missing: $plugin" >&2
  exit 1
fi
if ! command -v "$protoc_bin" >/dev/null 2>&1; then
  echo "protoc executable is missing: $protoc_bin" >&2
  exit 1
fi

output_root="$(mktemp -d)"
trap 'rm -rf -- "$output_root"' EXIT
mkdir -p "$output_root/PluginGenerated"

"$protoc_bin" \
  --plugin="protoc-gen-lean4=$plugin" \
  --lean4_out="$output_root/PluginGenerated" \
  --lean4_opt=lean4_prefix=PluginGenerated \
  --proto_path="$repo_root/Test/PluginIntegration" \
  --proto_path="$repo_root/Test" \
  dep/common.proto odd-dir/common-file.proto app/helper.proto app/main.proto \
  keywords/lean-keywords.proto editions/edition-2024.proto \
  editions/extension-options.proto \
  GroupProto2.proto GroupEditions.proto \
  NamingCollisionsProto3.proto NamingCollisionsProto2.proto \
  NamingCollisionsEditions.proto

test -f "$output_root/PluginGenerated/dep/common.lean"
test -f "$output_root/PluginGenerated/odd-dir/common-file.lean"
test -f "$output_root/PluginGenerated/app/helper.lean"
test -f "$output_root/PluginGenerated/app/main.lean"
test -f "$output_root/PluginGenerated/keywords/lean-keywords.lean"
test -f "$output_root/PluginGenerated/editions/edition-2024.lean"
test -f "$output_root/PluginGenerated/editions/extension-options.lean"
test -f "$output_root/PluginGenerated/GroupProto2.lean"
test -f "$output_root/PluginGenerated/GroupEditions.lean"
test -f "$output_root/PluginGenerated/NamingCollisionsProto3.lean"
test -f "$output_root/PluginGenerated/NamingCollisionsProto2.lean"
test -f "$output_root/PluginGenerated/NamingCollisionsEditions.lean"
grep -Fqx 'public import «PluginGenerated».«dep».«common»' \
  "$output_root/PluginGenerated/app/main.lean"
grep -Fqx 'public import «PluginGenerated».«odd-dir».«common-file»' \
  "$output_root/PluginGenerated/app/main.lean"
grep -Fqx 'public import «PluginGenerated».«app».«helper»' \
  "$output_root/PluginGenerated/app/main.lean"
grep -Fq 'protobuf: deprecated message' \
  "$output_root/PluginGenerated/odd-dir/common-file.lean"
grep -Fq 'protobuf: deprecated field' \
  "$output_root/PluginGenerated/odd-dir/common-file.lean"
grep -Fq '«old_value» = 100' \
  "$output_root/PluginGenerated/editions/extension-options.lean"
grep -Fq '«default» = 7' \
  "$output_root/PluginGenerated/editions/extension-options.lean"
grep -Fq '«deprecated» = true' \
  "$output_root/PluginGenerated/editions/extension-options.lean"
grep -Fq '«match»' \
  "$output_root/PluginGenerated/keywords/lean-keywords.lean"
grep -Fq '«structure»' \
  "$output_root/PluginGenerated/keywords/lean-keywords.lean"
grep -Fq '«choice_Type.protobuf.oneof»' \
  "$output_root/PluginGenerated/NamingCollisionsProto3.lean"
for generated in \
    NamingCollisionsProto3.lean \
    NamingCollisionsProto2.lean \
    NamingCollisionsEditions.lean; do
  grep -Fq 'rec.protobuf' \
    "$output_root/PluginGenerated/$generated"
  grep -Fq 'encode_Type' \
    "$output_root/PluginGenerated/$generated"
  grep -Fq 'rec.protobuf_Type' \
    "$output_root/PluginGenerated/$generated"
done

# A generation error must be carried by CodeGeneratorResponse.error.  Protoc
# reports that response as a normal generator diagnostic; it must not report
# that the plugin process itself failed.
mkdir -p "$output_root/ErrorResponse"
set +e
error_output="$("$protoc_bin" \
  --plugin="protoc-gen-lean4=$plugin" \
  --lean4_out="$output_root/ErrorResponse" \
  --proto_path="$repo_root/Test/PluginIntegration" \
  dep/common.proto 2>&1)"
error_status=$?
set -e
test "$error_status" -ne 0
grep -Fq -- '--lean4_out: lean4_prefix is not specified' <<<"$error_output"
if grep -Fq 'Plugin failed with status code' <<<"$error_output"; then
  echo "$error_output" >&2
  exit 1
fi

# Error responses must advertise the same feature bits and edition range as
# successful responses. protoc checks these fields before reporting
# CodeGeneratorResponse.error, so omitting them produces a false "plugin has
# not been updated" diagnostic that obscures the real generation error.
set +e
edition_error_output="$("$protoc_bin" \
  --plugin="protoc-gen-lean4=$plugin" \
  --lean4_out="$output_root/ErrorResponse" \
  --proto_path="$repo_root/Test" \
  GroupEditions.proto 2>&1)"
edition_error_status=$?
set -e
test "$edition_error_status" -ne 0
grep -Fq -- '--lean4_out: lean4_prefix is not specified' \
  <<<"$edition_error_output"
if grep -Fq "hasn't been updated to support editions" \
    <<<"$edition_error_output"; then
  echo "$edition_error_output" >&2
  exit 1
fi

set +e
optional_error_output="$("$protoc_bin" \
  --plugin="protoc-gen-lean4=$plugin" \
  --lean4_out="$output_root/ErrorResponse" \
  --proto_path="$repo_root/Test" \
  Proto3.proto 2>&1)"
optional_error_status=$?
set -e
test "$optional_error_status" -ne 0
grep -Fq -- '--lean4_out: lean4_prefix is not specified' \
  <<<"$optional_error_output"
if grep -Fq "hasn't been updated to support optional fields in proto3" \
    <<<"$optional_error_output"; then
  echo "$optional_error_output" >&2
  exit 1
fi

# Hand-crafted CodeGeneratorRequest values do not pass through protoc's schema
# validation. The plugin must apply the same whole-descriptor-set extension
# checks as #load_proto_file and report a generation error in its response.
"$protoc_bin" \
  --proto_path="$repo_root/proto" \
  --encode=google.protobuf.compiler.CodeGeneratorRequest \
  google/protobuf/compiler/plugin.proto \
  < "$repo_root/Test/PluginIntegration/forged-extension-request.textproto" \
  > "$output_root/forged-extension-request.bin"
"$plugin" \
  < "$output_root/forged-extension-request.bin" \
  > "$output_root/forged-extension-response.bin"
"$protoc_bin" \
  --proto_path="$repo_root/proto" \
  --decode=google.protobuf.compiler.CodeGeneratorResponse \
  google/protobuf/compiler/plugin.proto \
  < "$output_root/forged-extension-response.bin" \
  > "$output_root/forged-extension-response.textproto"
grep -Fq \
  'extension number 99 is outside every extension range of `forged.host.Host`' \
  "$output_root/forged-extension-response.textproto"

# Identifier validation must happen on the raw descriptor set, before a name
# containing Lean's closing identifier escape can reach syntax generation.
# As above, verify the real plugin protocol response rather than only calling
# the compiler helper in-process.
"$protoc_bin" \
  --proto_path="$repo_root/proto" \
  --encode=google.protobuf.compiler.CodeGeneratorRequest \
  google/protobuf/compiler/plugin.proto \
  < "$repo_root/Test/PluginIntegration/forged-identifier-request.textproto" \
  > "$output_root/forged-identifier-request.bin"
"$plugin" \
  < "$output_root/forged-identifier-request.bin" \
  > "$output_root/forged-identifier-response.bin"
"$protoc_bin" \
  --proto_path="$repo_root/proto" \
  --decode=google.protobuf.compiler.CodeGeneratorResponse \
  google/protobuf/compiler/plugin.proto \
  < "$output_root/forged-identifier-response.bin" \
  > "$output_root/forged-identifier-response.textproto"
grep -Fq 'invalid protobuf identifier' \
  "$output_root/forged-identifier-response.textproto"
grep -Fq 'bad\302\273' \
  "$output_root/forged-identifier-response.textproto"

run_forged_request() {
  local stem="$1"
  "$protoc_bin" \
    --proto_path="$repo_root/proto" \
    --encode=google.protobuf.compiler.CodeGeneratorRequest \
    google/protobuf/compiler/plugin.proto \
    < "$repo_root/Test/PluginIntegration/$stem-request.textproto" \
    > "$output_root/$stem-request.bin"
  "$plugin" \
    < "$output_root/$stem-request.bin" \
    > "$output_root/$stem-response.bin"
  "$protoc_bin" \
    --proto_path="$repo_root/proto" \
    --decode=google.protobuf.compiler.CodeGeneratorResponse \
    google/protobuf/compiler/plugin.proto \
    < "$output_root/$stem-response.bin" \
    > "$output_root/$stem-response.textproto"
  forged_response="$output_root/$stem-response.textproto"
}

run_forged_request forged-duplicate-target
grep -Fq 'file_to_generate `duplicate.proto` is listed more than once' \
  "$forged_response"
grep -Fqx 'supported_features: 3' "$forged_response"
grep -Fqx 'minimum_edition: 1000' "$forged_response"
grep -Fqx 'maximum_edition: 1001' "$forged_response"

run_forged_request forged-output-collision
grep -Fq 'map to the same Lean module' "$forged_response"

run_forged_request forged-source-mismatch
grep -Fq \
  'does not match its stripped proto_file descriptor' \
  "$forged_response"

run_forged_request forged-source-structure-mismatch
grep -Fq \
  'does not match its stripped proto_file descriptor' \
  "$forged_response"

run_forged_request forged-source-duplicate
grep -Fq \
  'source_file_descriptors entry `first.proto` is listed more than once' \
  "$forged_response"

run_forged_request forged-invalid-prefix
grep -Fq \
  'lean4_prefix must be a dot-separated ASCII Lean module name' \
  "$forged_response"

run_forged_request forged-unimportable-target
grep -Fq \
  'cannot represent protobuf path component' \
  "$forged_response"

# The source descriptor may add SOURCE-retention feature values while the
# stripped proto_file remains authoritative for the schema and runtime
# options.
run_forged_request forged-valid-source
if grep -q '^error:' "$forged_response"; then
  cat "$forged_response" >&2
  exit 1
fi
grep -Fq 'name: "valid-source.lean"' "$forged_response"

# Descriptor numeric defaults use DescriptorPool semantics, not `.proto`
# source-token semantics. In particular, a double default `"077"` is decimal
# 77 and must never be silently rewritten as source-level octal 63.
run_forged_request forged-numeric-default
if grep -q '^error:' "$forged_response"; then
  cat "$forged_response" >&2
  exit 1
fi
grep -Fq 'name: "numeric-default.lean"' "$forged_response"
grep -Fq '= 77 ];\n' "$forged_response"
grep -Fq '= 8 ];\n' "$forged_response"
grep -Fq '= 1 ];\n' "$forged_response"
grep -Fq '= 3 ];\n' "$forged_response"
grep -Fq 'protobuf_nan' "$forged_response"
grep -Fq '\302\253float\302\273 \302\253float_double_rounding\302\273 = 6 [ \302\253default\302\273 = 1 ];\n' "$forged_response"
if grep -Fq '= 63 ];\n' "$forged_response"; then
  cat "$forged_response" >&2
  exit 1
fi

lean_path="$(cd "$repo_root" && lake env printenv LEAN_PATH)"
(
  cd "$repo_root"
  export LEAN_PATH="$output_root:$lean_path"
  lean --root="$output_root" -o "$output_root/PluginGenerated/dep/common.olean" \
    "$output_root/PluginGenerated/dep/common.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/odd-dir/common-file.olean" \
    "$output_root/PluginGenerated/odd-dir/common-file.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/app/helper.olean" \
    "$output_root/PluginGenerated/app/helper.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/app/main.olean" \
    "$output_root/PluginGenerated/app/main.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/keywords/lean-keywords.olean" \
    "$output_root/PluginGenerated/keywords/lean-keywords.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/editions/edition-2024.olean" \
    "$output_root/PluginGenerated/editions/edition-2024.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/editions/extension-options.olean" \
    "$output_root/PluginGenerated/editions/extension-options.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/GroupProto2.olean" \
    "$output_root/PluginGenerated/GroupProto2.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/GroupEditions.olean" \
    "$output_root/PluginGenerated/GroupEditions.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/NamingCollisionsProto3.olean" \
    "$output_root/PluginGenerated/NamingCollisionsProto3.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/NamingCollisionsProto2.olean" \
    "$output_root/PluginGenerated/NamingCollisionsProto2.lean"
  lean --root="$output_root" -o "$output_root/PluginGenerated/NamingCollisionsEditions.olean" \
    "$output_root/PluginGenerated/NamingCollisionsEditions.lean"
)
