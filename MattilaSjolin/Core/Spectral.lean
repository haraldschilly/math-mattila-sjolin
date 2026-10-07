import MattilaSjolin.Core.Continuity
import MattilaSjolin.Core.Spectral.Radial
import MattilaSjolin.Core.Spectral.DiffMeasure
import MattilaSjolin.Core.Spectral.Polar

/-! Step 4: the spectral identity `∫ φ dν = ∫ φ f`. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal ContDiff FourierTransform RealInnerProductSpace

namespace MattilaSjolin

variable {d : ℕ}

/-- **Step 4. The spectral identity.** For smooth `φ` supported in `[a, b] ⊂ (0, ∞)`,
`∫ φ dν = ∫_0^∞ φ(t) f(t) dt`. -/
theorem integral_distMeasure_eq (hd : 2 ≤ d) (hdec : SphereDecay d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (hw : Integrable (energyWeight μ)) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support φ ⊆ Icc a b) :
    ((∫ t, φ t ∂distMeasure μ : ℝ) : ℂ) = ∫ t in Ioi (0 : ℝ), (φ t : ℂ) * distDensity μ t := by
  set ψ : Space d → ℂ := fun z => ((φ ‖z‖ : ℝ) : ℂ) with hψ
  obtain ⟨hgint, hinv⟩ := radial_fourier_inversion (d := d) hφ ha hsupp
  set m : Space d → ℂ := fun ξ => ((‖sourceFourier μ ξ‖ ^ 2 : ℝ) : ℂ) with hm
  set F : Space d → ℝ → ℂ := fun ξ t =>
    ((t ^ (d - 1) * φ t : ℝ) : ℂ) * sphereCheck d (t • ξ) * m ξ with hF
  -- (1) `∫ φ dν = ∫ ψ dρ`
  have h1 : ((∫ t, φ t ∂distMeasure μ : ℝ) : ℂ) = ∫ z, ψ z ∂diffMeasure μ := by
    rw [integral_distMeasure_eq_diffMeasure μ φ hφ.continuous, ← integral_complex_ofReal]
  -- (2) Parseval with `ρ̂ = |μ̂|²`
  have h2 : ∫ z, ψ z ∂diffMeasure μ = ∫ ξ, 𝓕⁻ ψ ξ * m ξ := by
    calc ∫ z, ψ z ∂diffMeasure μ = ∫ z, 𝓕 (𝓕⁻ ψ) z ∂diffMeasure μ := by rw [hψ, hinv]
      _ = ∫ ξ, 𝓕⁻ ψ ξ * sourceFourier (diffMeasure μ) ξ :=
          (sourceFourier_integral_swap (diffMeasure μ) (𝓕⁻ ψ) hgint).symm
      _ = ∫ ξ, 𝓕⁻ ψ ξ * m ξ := by simp only [sourceFourier_diffMeasure, hm]
  -- (3) polar coordinates for `𝓕⁻ ψ`
  have hg : ∀ ξ, 𝓕⁻ ψ ξ =
      ∫ t in Ioi (0 : ℝ), ((t ^ (d - 1) * φ t : ℝ) : ℂ) * sphereCheck d (t • ξ) := by
    intro ξ
    rw [← integral_exp_radial_eq (by omega) φ hφ.continuous hsupp ξ, Real.fourierInv_eq']
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hψ, smul_eq_mul]
    congr 2
    push_cast; ring
  -- (4) Fubini
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    obtain ⟨C, hC0, hC⟩ := sphereCheck_le_of_sphereDecay hdec
    obtain ⟨K, hK0, hK⟩ := rpow_decay_bound (d := d) a ha
    have hφc : HasCompactSupport φ :=
      HasCompactSupport.intro isCompact_Icc fun x hx => by
        by_contra h; exact hx (hsupp h)
    obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
    set B : ℝ := b ^ (d - 1) * Mφ * C * K with hB
    have hbound : Integrable (fun p : Space d × ℝ => energyWeight μ p.1 * (Icc a b).indicator
        (fun _ => B) p.2) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      refine hw.mul_prod ?_
      refine (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const ?_)
      rw [Measure.restrict_apply measurableSet_Icc]
      exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_left)
    have hcont : Continuous (Function.uncurry F) := by
      have h1 := continuous_sphereCheck d
      have h2 := continuous_sourceFourier μ
      have h3 := hφ.continuous
      simp only [hF, hm, Function.uncurry_def]
      fun_prop
    refine hbound.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    obtain ⟨ξ, t⟩ := p
    simp only [Function.uncurry_apply_pair, hF, hm]
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht]
      have ht0 : 0 ≤ t := ha.le.trans ht.1
      have hpow : t ^ (d - 1) ≤ b ^ (d - 1) := pow_le_pow_left₀ ht0 ht.2 _
      have hσ : ‖sphereCheck d (t • ξ)‖ ≤ C * K * (1 + ‖ξ‖) ^ (-decayExp d) := by
        calc ‖sphereCheck d (t • ξ)‖ ≤ C * (1 + ‖t • ξ‖) ^ (-decayExp d) := hC _
          _ ≤ C * (K * (1 + ‖ξ‖) ^ (-decayExp d)) := by gcongr; exact hK t ht.1 ξ
          _ = C * K * (1 + ‖ξ‖) ^ (-decayExp d) := by ring
      have hφt : |φ t| ≤ Mφ := by simpa [Real.norm_eq_abs] using hMφ t
      have hw0 : 0 ≤ (1 + ‖ξ‖) ^ (-decayExp d) := by positivity
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg (by positivity), abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
      unfold energyWeight
      have hM0 : 0 ≤ Mφ := (abs_nonneg _).trans hφt
      calc t ^ (d - 1) * |φ t| * ‖sphereCheck d (t • ξ)‖ * ‖sourceFourier μ ξ‖ ^ 2
          ≤ b ^ (d - 1) * Mφ * (C * K * (1 + ‖ξ‖) ^ (-decayExp d)) * ‖sourceFourier μ ξ‖ ^ 2 := by
            have hb0 : 0 ≤ b := ht0.trans ht.2
            gcongr
        _ = ‖sourceFourier μ ξ‖ ^ 2 * (1 + ‖ξ‖) ^ (-decayExp d) * B := by rw [hB]; ring
    · rw [indicator_of_notMem ht, mul_zero]
      have : φ t = 0 := by
        by_contra h; exact ht (hsupp h)
      simp [this]
  have h4 : ∫ ξ, 𝓕⁻ ψ ξ * m ξ = ∫ t in Ioi (0 : ℝ), ∫ ξ, F ξ t := by
    simp_rw [hg, ← integral_mul_const]
    exact integral_integral_swap hint
  -- (5) identify with the density
  rw [h1, h2, h4]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hF, distDensity, hm]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  push_cast
  ring

end MattilaSjolin
