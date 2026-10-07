# The Mattila–Sjölin theorem in Lean 4

[![Lean build](https://github.com/haraldschilly/math-mattila-sjolin/actions/workflows/lean.yml/badge.svg)](https://github.com/haraldschilly/math-mattila-sjolin/actions/workflows/lean.yml)

A formal proof, in Lean 4 with Mathlib, of the **Mattila–Sjölin theorem** (P. Mattila, P. Sjölin,
*Regularity of distance measures and sets*, Math. Nachr. 204 (1999), 157–162):

> If `E ⊂ ℝ^d` is compact with Hausdorff dimension `dim_H E > (d+1)/2`, then its distance set
> `Δ(E) = {|x − y| : x, y ∈ E}` contains an interval.

## Status: proved

```lean
theorem MattilaSjolin.mattilaSjolin : MattilaSjolinStatement
-- where
def MattilaSjolinStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    ((d : ℝ≥0∞) + 1) / 2 < dimH E →
      (interior {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty
```

`#print axioms MattilaSjolin.mattilaSjolin` reports only `propext`, `Classical.choice`, `Quot.sound`.
CI enforces this, and it also fails on any warning, including a `sorry`.

The argument is uniform in the dimension. `mattilaSjolin_of_sphereDecay` shows that, for every
`d ≥ 2`, Fourier decay of the sphere measure (`SphereDecay d`, `|σ̌(η)| ≲ |η|^{−(d−1)/2}`) implies the
theorem in dimension `d`. The decay itself comes from OpenAI's stationary-phase expansions:
- `d ≥ 3`: `sphereDecay_add_three`, from the sphere expansion;
- `d = 2`: `sphereDecay_two`, from the full-circle expansion, after identifying the circle's sphere
  measure with arc length (`integral_sphereMeasure_two`).

## How the proof goes

See [BLUEPRINT.md](BLUEPRINT.md). In short:
1. take a Frostman measure `μ` on `E`;
2. its Riesz energy gives `∫ |μ̂(ξ)|² |ξ|^{−(d−1)/2} dξ < ∞`;
3. the distance measure `ν` satisfies `∫ φ dν = ∫ φ(t) f(t) dt` for smooth bumps `φ` on `(0,∞)`, with
   `f(t) = t^{d−1} ∫ |μ̂(ξ)|² σ̌(tξ) dξ` (Fourier inversion, polar coordinates, Fubini; convergence comes
   from the sphere decay `|σ̌(η)| ≲ |η|^{−(d−1)/2}`);
4. `f` is continuous and positive somewhere, so `Δ(E)` contains an interval.

| File | Content |
|---|---|
| `MattilaSjolin/Statement.lean` | the theorem statement |
| `MattilaSjolin/SphereDecay.lean` | `σ̌`, `SphereDecay`, decay for `d ≥ 3` |
| `MattilaSjolin/Circle/*.lean` | circle measure = arc length; decay for `d = 2` |
| `MattilaSjolin/Core/*.lean` | the argument above, one step per file |
| `MattilaSjolin/Core.lean` | assembly: `mattilaSjolin_of_sphereDecay`, `mattilaSjolin_of_three_le` |
| `MattilaSjolin/Main.lean` | the theorem: `mattilaSjolin` |

## Built on OpenAI's Lean library

This project reuses formal results from OpenAI's proof of the Falconer distance conjecture in
[github.com/openai/math](https://github.com/openai/math) (commit `adc7f12`, Apache-2.0):
- Frostman's lemma (`frostman_probability`)
- the Fourier form of the Riesz energy (`source_fourier_energy_identity`)
- the Fourier pairing for measures (`sourceFourier_integral_swap`, `sourceFourier_difference`)
- the stationary-phase expansions on spheres and on the circle (`sphere_stationary_expansion_unscaled`,
  `full_circle_stationary_expansion`)
- planar polar coordinates and arc length on the circle (`plane_polar_lintegral`, `sourceArcLength`)

Those files are **not** included here. `scripts/fetch_oai.py` copies the needed 347 files, which depend
only on Mathlib, from a checkout at the pinned commit into `oai-src/`. They are fully proved there,
with no extra hypotheses. Their correctness is checked by the same Lean build as ours.

## Build

Toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b`, the same pins as OpenAI's library.

```sh
git clone https://github.com/openai/math ../openai-math        # then check out commit adc7f12
python3 scripts/fetch_oai.py ../openai-math
lake exe cache get
lake build                                                       # Mathlib from cache, OpenAI files ~10 min
lake env lean verify/Axioms.lean
```

## Use of AI

The proof builds on AI-generated formal mathematics (OpenAI). This repository was written with
substantial assistance from Claude (Anthropic), including the Lean proofs. Lean checks the proofs;
humans should still check that the statement in `MattilaSjolin/Statement.lean` says what is claimed.

## License

Apache-2.0.
