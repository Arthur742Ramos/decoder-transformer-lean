#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_file in \
  lean-toolchain lake-manifest.json formalization.yaml Challenge.lean Solution.lean \
  comparator.json LICENSE; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (root / name).exists()]
if len(lakefiles) != 1:
    raise SystemExit(f"error: expected one Lakefile, found {lakefiles}")

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds the 100 KiB or 1,000-line cap")
imports = [line.split()[1] for line in challenge_text.splitlines() if line.startswith("import ")]
if any(not module.startswith("Mathlib.") for module in imports):
    raise SystemExit(f"error: Challenge.lean imports outside Mathlib: {imports}")

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is invalid: {error}")
required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
allowed = required | {"definition_names", "enable_nanoda"}
if not isinstance(comparator, dict) or set(comparator) - allowed or not required <= set(comparator):
    raise SystemExit("error: comparator.json has an invalid key set")
if comparator["challenge_module"] == comparator["solution_module"]:
    raise SystemExit("error: Challenge and Solution modules must differ")
if not comparator["theorem_names"]:
    raise SystemExit("error: comparator.json theorem_names must be nonempty")
if comparator.get("enable_nanoda") is not True:
    raise SystemExit("error: comparator.json must enable NanoDa")
if not set(comparator["permitted_axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
    raise SystemExit("error: comparator.json contains an unsupported axiom")

solution = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)", solution):
    raise SystemExit("error: Solution.lean contains a proof placeholder")
if re.search(r"^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: Solution.lean declares an axiom or unsafe definition")

for path in sorted((root / "DecoderTransformer").glob("*.lean")):
    text = path.read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)", text):
        raise SystemExit(f"error: proof placeholder found in {path.relative_to(root)}")
    if re.search(r"^\s*(axiom|unsafe)\b", text, re.MULTILINE):
        raise SystemExit(f"error: axiom or unsafe declaration found in {path.relative_to(root)}")

print(f"Palomar package shape passed: Challenge {challenge.stat().st_size} bytes")
PY

ruby -ryaml - "$repository_root/formalization.yaml" <<'RUBY'
path = ARGV.fetch(0)
data = YAML.safe_load(File.read(path), aliases: false)
abort "error: formalization.yaml must be a mapping" unless data.is_a?(Hash)
abort "error: metadata version must be v0.4" unless data["version"] == "v0.4"
project = data["project"]
abort "error: project metadata is incomplete" unless project.is_a?(Hash)
abort "error: project.name is missing" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "error: project.description is missing" unless project["description"].is_a?(String) && !project["description"].strip.empty?
abort "error: project.authors is empty" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "error: project.responsible_maintainers is empty" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "error: project.license must be Apache-2.0" unless project["license"] == "Apache-2.0"
classification = data["classification"]
abort "error: classification is incomplete" unless classification.is_a?(Hash) && classification["arxiv"].is_a?(Array) && classification["msc2020"].is_a?(Array)
sources = data["sources"]
abort "error: sources is empty" unless sources.is_a?(Array) && !sources.empty?
abort "error: automation metadata is incomplete" unless data["automation"].is_a?(Hash) && data["automation"]["methods"].is_a?(Array) && !data["automation"]["methods"].empty?
abort "error: review metadata is incomplete" unless data["review"].is_a?(Hash) && data["review"]["status"].is_a?(String)
puts "formalization.yaml shape passed."
RUBY

echo "Palomar package audit: passed"
