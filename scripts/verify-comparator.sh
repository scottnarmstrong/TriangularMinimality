#!/usr/bin/env bash
set -euo pipefail

# A local verification procedure: judge the Solution against the Challenge with the
# `lake comparator` that ships in this project's own toolchain, replaying the proof through
# Lean's kernel and the toolchain's bundled independent kernels (NanoDa and con-ron), and
# require all three to accept. Nothing is built from a pin; everything that judges comes from
# `lean-toolchain`. This approximates the Palomar registry's check; it is not the registry's
# official verification, which runs its own protected tool versions under its own rules.
#
# The Solution imports the certificate library, so run `lake build SandierSerfatyCert`
# first (about 14 CPU-hours): the comparator then reuses the built files and only
# exports and replays them.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    exit 1
  fi
done

# The registry ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This generated
# copy does the same, so the local check uses the same kernels as the registry.
config=$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
lake comparator --config "$config"
