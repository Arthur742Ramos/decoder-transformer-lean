#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

lake build
lake env lean DecoderTransformer/Examples.lean
lake env lean Challenge.lean
lake env lean Solution.lean

if rg -n '\b(sorry|admit)\b' DecoderTransformer Solution.lean ||
   rg -n '^\s*axiom\b' DecoderTransformer Solution.lean; then
  echo "error: proof placeholders or extra axioms found in the proved surface" >&2
  exit 1
fi

ruby -e 'require "yaml"; d = YAML.safe_load(File.read("formalization.yaml"), aliases: false); abort "missing formalization metadata" unless d.is_a?(Hash) && d["version"] == "v0.4" && d.dig("project", "license") == "Apache-2.0"; puts "formalization.yaml: valid v0.4 metadata"'
echo "local verification: passed"
