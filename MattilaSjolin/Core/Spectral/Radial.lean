import MattilaSjolin.Core.Defs

/-! Step 4, parts S1–S2: the radial lift `ψ(z) = φ(|z|)` of a smooth bump `φ` supported in
`[a, b] ⊂ (0, ∞)` is smooth with compact support, hence Schwartz, so Fourier inversion applies. -/

open MeasureTheory Set Filter Topology OAI.Falconer
open scoped ENNReal NNReal ContDiff FourierTransform SchwartzMap

namespace MattilaSjolin

variable {d : ℕ}

theorem radial_eq_zero_of_lt {φ : ℝ → ℝ} {a b : ℝ} (hsupp : Function.support φ ⊆ Icc a b)
    {r : ℝ} (hr : r < a) : φ r = 0 := by
  by_contra h
  exact absurd (hsupp h).1 (not_le.2 hr)

theorem contDiff_radial {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support φ ⊆ Icc a b) : ContDiff ℝ ∞ (fun z : Space d => φ ‖z‖) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ‖z‖ < a
  · -- near `z` the function vanishes identically
    have hnhds : ∀ᶠ y in 𝓝 z, φ ‖y‖ = 0 := by
      have : Metric.ball z (a - ‖z‖) ∈ 𝓝 z := Metric.ball_mem_nhds z (by linarith)
      filter_upwards [this] with y hy
      apply radial_eq_zero_of_lt hsupp
      have := norm_le_norm_add_norm_sub' y z
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq hnhds
  · have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact hz ha
    exact hφ.contDiffAt.comp z (contDiffAt_norm ℝ hz0)

theorem hasCompactSupport_radial {φ : ℝ → ℝ} {a b : ℝ} (hsupp : Function.support φ ⊆ Icc a b) :
    HasCompactSupport (fun z : Space d => φ ‖z‖) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space d) b) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  by_contra h
  exact absurd (hsupp h).2 (not_le.2 hz)

/-- The complex radial lift as a Schwartz function. -/
noncomputable def radialSchwartz {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support φ ⊆ Icc a b) : 𝓢(Space d, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun z : Space d => ((φ ‖z‖ : ℝ) : ℂ))
    ((hasCompactSupport_radial hsupp).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (contDiff_radial hφ ha hsupp))

theorem radialSchwartz_apply {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support φ ⊆ Icc a b) (z : Space d) :
    radialSchwartz hφ ha hsupp z = ((φ ‖z‖ : ℝ) : ℂ) := rfl

/-- Fourier inversion for the radial lift: `𝓕 (𝓕⁻ ψ) = ψ`, and `𝓕⁻ ψ` is integrable. -/
theorem radial_fourier_inversion {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support φ ⊆ Icc a b) :
    Integrable (𝓕⁻ (fun z : Space d => ((φ ‖z‖ : ℝ) : ℂ))) ∧
      𝓕 (𝓕⁻ (fun z : Space d => ((φ ‖z‖ : ℝ) : ℂ))) = fun z => ((φ ‖z‖ : ℝ) : ℂ) := by
  set S := radialSchwartz (d := d) hφ ha hsupp
  have hS : (S : Space d → ℂ) = fun z => ((φ ‖z‖ : ℝ) : ℂ) := rfl
  refine ⟨?_, ?_⟩
  · rw [← hS, ← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ S).integrable
  · rw [← hS, ← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe]
    rw [FourierInvPair.fourier_fourierInv_eq S]

end MattilaSjolin
