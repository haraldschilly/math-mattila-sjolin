# Blueprint: a Lean proof of the Mattila–Sjölin theorem

**Theorem** (Mattila–Sjölin 1999). Let `d ≥ 2` and let `E ⊂ ℝ^d` be compact with
`dim_H E > (d+1)/2`. Then the distance set `Δ(E) = {|x−y| : x, y ∈ E}` has nonempty interior.

Notation: `μ̂(ξ) = ∫ e^{−2πi⟨x,ξ⟩} dμ(x)` (OpenAI: `sourceFourier`), `σ` the surface measure on
`S^{d−1}` (OpenAI: `sphereMeasure d = volume.toSphere`), and `σ̌(η) = ∫_S e^{2πi⟨w,η⟩} dσ(w)`.

## Design

The argument is split along one hypothesis, **sphere decay in dimension d**:

> `SphereDecay d`: there is `C` with `|σ̌(η)| ≤ C · |η|^{−(d−1)/2}` for all `|η| ≥ 1`.

* **Core** (all `d ≥ 2`): `SphereDecay d → Mattila–Sjölin in dimension d`.
* **d ≥ 3**: `SphereDecay (m+3)` from OpenAI's stationary-phase expansion
  (`sphere_stationary_expansion_unscaled` with `J = 1`, `B ≡ 1`; leading coefficient
  `actualStationaryCoefficient_zero`: `sphereStationaryConstant (m+2) * B e`).
* **d = 2**: `SphereDecay 2` from OpenAI's full-circle stationary-phase expansion
  (`full_circle_stationary_expansion`, one term, constant symbol) for `∫_{-π}^{π} e^{iλ cos θ} dθ`,
  after identifying `sphereMeasure 2` with arc length (`integral_sphereMeasure_two`) and rotating
  (`rotated_circle_integral`).

## Core argument

Fix `(d+1)/2 < s < dim_H E` and set `u = (d+1)/2` (so `u − d = −(d−1)/2` and `0 < u < d`).

1. **Frostman** (OpenAI `frostman_probability`): a probability measure `μ` with `μ(Eᶜ) = 0` and
   `μ(B(x,r)) ≤ C r^s`.
2. **Energy** (OpenAI `rieszEnergyOn_lt_top_of_frostman`, `source_fourier_energy_identity`,
   `sourceEnergyConstant_pos`): `∫ |μ̂(ξ)|² |ξ|^{−(d−1)/2} dξ < ∞`. Hence, with
   `w(ξ) = |μ̂(ξ)|² min(1, |ξ|^{−(d−1)/2})`, `w` is integrable (`|μ̂| ≤ 1` on `|ξ| ≤ 1`).
3. **Distance measure** `ν = (μ×μ)_*(x,y ↦ |x−y|)`. Then `ν(Δ(E)ᶜ) = 0`, and `ν({0}) = 0` because
   `μ` has no atoms (OpenAI `noAtoms_of_frostman`), so `ν((0,∞)) = 1`.
4. **Spectral identity.** For smooth `φ` with compact support in `(0,∞)`:
   `∫ φ dν = ∫_0^∞ φ(t) f(t) dt` with `f(t) = t^{d−1} ∫ |μ̂(ξ)|² σ̌(tξ) dξ`.
   * `ψ(z) = φ(|z|)` is smooth with compact support on `ℝ^d`.
   * `∫ φ dν = ∫ ψ d(μ ∗ μ̃)`, and `(μ ∗ μ̃)^ = |μ̂|²` (OpenAI `sourceFourier_difference`).
   * Fourier inversion `ψ = 𝓕(𝓕⁻ψ)` and OpenAI's `sourceFourier_integral_swap` give
     `∫ ψ d(μ∗μ̃) = ∫ 𝓕⁻ψ(ξ) |μ̂(ξ)|² dξ`.
   * Polar coordinates: `𝓕⁻ψ(ξ) = ∫_0^∞ φ(t) t^{d−1} σ̌(tξ) dt`.
   * Fubini, justified by `|φ(t) t^{d−1} σ̌(tξ)| |μ̂(ξ)|² ≤ K · 1_{[a,b]}(t) · w(ξ)` (sphere decay).
5. **Continuity.** `f` is continuous on `(0,∞)` (dominated convergence, same bound on compact
   `t`-intervals).
6. **Positivity somewhere.** Since `ν((0,∞)) > 0`, some bump `φ ≥ 0` has `∫ φ dν > 0`, hence
   `Re f(t₀) > 0` for some `t₀ > 0`, and `Re f > 0` on an interval `I ∋ t₀`.
7. **Interval in Δ(E).** If `t ∈ I` were not in the closed set `Δ(E)`, a bump `φ ≥ 0` around `t`
   supported in `I ∖ Δ(E)` gives `0 = ∫ φ dν = Re ∫ φ f > 0`. So `I ⊆ Δ(E)`.

## Status

| Step | Lean | Status |
|---|---|---|
| Statement | `MattilaSjolin.MattilaSjolinStatement` | done |
| SphereDecay (m+3) | `sphereDecay_add_three` | **done** |
| Core 1–7 | `mattilaSjolin_of_sphereDecay` (Core/*.lean) | **done** |
| SphereDecay 2 | `sphereDecay_two` (Circle/*.lean) | **done** |
| **Theorem** | `MattilaSjolin.mattilaSjolin` | **done** |
