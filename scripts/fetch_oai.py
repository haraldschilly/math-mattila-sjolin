"""Copy the OpenAI Lean files this project builds on into oai-src/.

Usage: python3 scripts/fetch_oai.py /path/to/openai-math-checkout
Only the transitive OAI import closure of the two solution modules is copied
(the closure depends on Mathlib only). The checkout must be at the pinned commit.
"""
import os, re, shutil, subprocess, sys

PINNED_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOLUTION_MODULES = [  # OpenAI modules reused by this project
    "OAI.MeasureTheory.Falconer.Measures.FrostmanDischarge",          # Frostman's lemma
    "OAI.MeasureTheory.Falconer.Fourier.FourierEnergy",               # Riesz energy, Fourier form
    "OAI.MeasureTheory.Falconer.Geometry.EuclideanRieszEnergy",       # energy finite from Frostman
    "OAI.MeasureTheory.Falconer.Fourier.EuclideanPolar",              # polar coordinates
    "OAI.MeasureTheory.Falconer.Angular.SphereProduct",               # sphere stationary phase
    "OAI.MeasureTheory.Falconer.Angular.GnomonicDischarge",           # discharges PublishedGnomonicSurface
    "OAI.MeasureTheory.Falconer.Estimates.QuadraticDischarge",        # discharges PublishedQuadraticStationary
    "OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryExpansion",  # circle stationary phase (d = 2)
    "OAI.MeasureTheory.Falconer.Angular.RotatedCircleIntegral",       # rotation of circle integrals
    "OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength",      # sourceDirection, angles
    "OAI.MeasureTheory.Falconer.Angular.StationaryArcLength",         # arc length over a period
    "OAI.MeasureTheory.Falconer.Angular.AngularStripMeasure",         # arc length of the full circle
]

math = os.path.abspath(sys.argv[1])
head = subprocess.run(["git", "-C", math, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
if head != PINNED_COMMIT:
    sys.exit(f"openai/math checkout is at {head or '?'}, expected {PINNED_COMMIT}")
src = os.path.join(math, "lean")
dst = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "oai-src")

def path(root, mod):
    return os.path.join(root, *mod.split(".")) + ".lean"

seen, stack, external = set(), list(SOLUTION_MODULES), set()
while stack:
    mod = stack.pop()
    if mod in seen:
        continue
    seen.add(mod)
    text = open(path(src, mod), encoding="utf-8").read()
    for imp in re.findall(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.«»]+)", text, re.M):
        (stack.append if imp.startswith("OAI") else external.add)(imp)
bad = {m.split(".")[0] for m in external} - {"Mathlib", "Lean", "Init", "Std"}
if bad:
    sys.exit(f"unexpected external dependencies: {sorted(bad)}")

shutil.rmtree(dst, ignore_errors=True)
for mod in sorted(seen):
    os.makedirs(os.path.dirname(path(dst, mod)), exist_ok=True)
    shutil.copy2(path(src, mod), path(dst, mod))
shutil.copy2(os.path.join(src, "LICENSE"), os.path.join(dst, "LICENSE"))
print(f"copied {len(seen)} OAI modules to {dst}")
