"""Fail unless every `#print axioms` in verify/Axioms.lean reports only the standard axioms.

Usage: lake env lean verify/Axioms.lean 2>&1 | python3 verify/check_axioms.py verify/Axioms.lean
"""
import re, sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
expected = len(re.findall(r"^#print axioms ", open(sys.argv[1], encoding="utf-8").read(), re.M))
output = sys.stdin.read()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
bad = [(name, ax) for name, ax in reports
       if not {a.strip() for a in ax.split(",") if a.strip()} <= ALLOWED]
for name, ax in bad:
    print(f"FAIL {name}: [{ax}]")
if len(reports) + len(clean) != expected:
    print(f"FAIL: expected {expected} axiom reports, got {len(reports) + len(clean)}")
    print(output)
    sys.exit(1)
if bad or "error" in output:
    sys.exit(1)
print(f"OK: {expected} theorems, axioms within {sorted(ALLOWED)}")
