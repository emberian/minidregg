#!/bin/sh
# Execute the actual namespace receiving test outside the cargo build service.
set -eu
[ "$#" -eq 1 ] || { echo "usage: $0 COMPILED_SPK_HOST_TEST_ELF" >&2; exit 2; }
[ "$(id -u)" = 1001 ] || { echo 'namespace receiving requires operator uid 1001' >&2; exit 1; }
exec "$1" --exact resident_privilege::tests::tenancy_bootstrap_actual_zero_capabilities_namespace_refusal_and_eof_reap --nocapture
