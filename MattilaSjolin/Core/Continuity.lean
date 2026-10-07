import MattilaSjolin.Core.Decay

/-! Step 5: continuity of the density. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal

namespace MattilaSjolin

variable {d : ℕ}

theorem continuous_sphereCheck (d : ℕ) : Continuous (sphereCheck d) := by
  unfold sphereCheck
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ ?_ ?_
  · intro η
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · intro η
    refine Eventually.of_forall fun w => ?_
    rw [Complex.norm_exp]
    simp
  · exact integrable_const _
  · exact Eventually.of_forall fun w => by fun_prop

theorem continuous_sourceFourier (μ : Measure (Space d)) [IsProbabilityMeasure μ] :
    Continuous (sourceFourier μ) := by
  unfold sourceFourier; fun_prop

theorem rpow_decay_bound (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, a ≤ t → ∀ ξ : Space d,
      (1 + ‖t • ξ‖) ^ (-decayExp d) ≤ K * (1 + ‖ξ‖) ^ (-decayExp d) := by
  rcases d with _ | d
  · refine ⟨1, zero_le_one, fun t _ ξ => ?_⟩
    have : ξ = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hp : 0 ≤ decayExp (d + 1) := by simp [decayExp]; positivity
    set c := min 1 a with hc
    have hc0 : 0 < c := lt_min one_pos ha
    refine ⟨c ^ (-decayExp (d + 1)), by positivity, fun t ht ξ => ?_⟩
    have ht0 : 0 < t := ha.trans_le ht
    have h1 : c * (1 + ‖ξ‖) ≤ 1 + ‖t • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, mul_add, mul_one]
      have : c * ‖ξ‖ ≤ t * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ht) (norm_nonneg _)
      linarith [min_le_left (1 : ℝ) a]
    calc (1 + ‖t • ξ‖) ^ (-decayExp (d + 1))
        ≤ (c * (1 + ‖ξ‖)) ^ (-decayExp (d + 1)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = c ^ (-decayExp (d + 1)) * (1 + ‖ξ‖) ^ (-decayExp (d + 1)) :=
          Real.mul_rpow hc0.le (by positivity)

/-- **Step 5.** The density is continuous on `(0, ∞)`. -/
theorem continuousOn_distDensity (hdec : SphereDecay d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (hw : Integrable (energyWeight μ)) :
    ContinuousOn (distDensity μ) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := sphereCheck_le_of_sphereDecay hdec
  have hsc := continuous_sphereCheck d
  have hsf := continuous_sourceFourier μ
  have hint : ContinuousOn (fun t : ℝ => ∫ ξ : Space d,
      ((‖sourceFourier μ ξ‖ ^ 2 : ℝ) : ℂ) * sphereCheck d (t • ξ)) (Ioi 0) := by
    intro t₀ ht₀
    have ht₀' : (0 : ℝ) < t₀ := ht₀
    obtain ⟨K, hK0, hK⟩ := rpow_decay_bound (d := d) (t₀ / 2) (by positivity)
    refine ContinuousAt.continuousWithinAt ?_
    refine continuousAt_of_dominated (bound := fun ξ => C * K * energyWeight μ ξ) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        (Continuous.aestronglyMeasurable (by fun_prop))
    · have hnhds : Ioi (t₀ / 2) ∈ 𝓝 t₀ := Ioi_mem_nhds (by linarith)
      filter_upwards [hnhds] with t ht
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      unfold energyWeight
      calc ‖sourceFourier μ ξ‖ ^ 2 * ‖sphereCheck d (t • ξ)‖
          ≤ ‖sourceFourier μ ξ‖ ^ 2 * (C * (K * (1 + ‖ξ‖) ^ (-decayExp d))) := by
            gcongr
            exact (hC _).trans (mul_le_mul_of_nonneg_left (hK t (le_of_lt ht) ξ) hC0)
        _ = C * K * (‖sourceFourier μ ξ‖ ^ 2 * (1 + ‖ξ‖) ^ (-decayExp d)) := by ring
    · exact hw.const_mul _
    · exact Eventually.of_forall fun ξ => by fun_prop
  unfold distDensity
  exact ((Complex.continuous_ofReal.comp (continuous_pow (d - 1))).continuousOn).mul hint

end MattilaSjolin
