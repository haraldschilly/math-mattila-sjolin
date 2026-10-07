import MattilaSjolin.Core.Defs
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! Step 2: integrability of the energy weight. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal

namespace MattilaSjolin

variable {d : ℕ}

/-- `μ̂` is continuous. -/
theorem sourceFourier_continuous (μ : Measure (Space d)) [IsFiniteMeasure μ] :
    Continuous (sourceFourier μ) := by
  unfold sourceFourier
  exact continuous_charFun.comp (continuous_const_smul _)

/-- `|μ̂| ≤ 1` for a probability measure. -/
theorem norm_sourceFourier_le_one (μ : Measure (Space d)) [IsProbabilityMeasure μ] (ξ : Space d) :
    ‖sourceFourier μ ξ‖ ≤ 1 := by
  unfold sourceFourier
  simpa using norm_charFun_le (μ := μ) ((-(2 * Real.pi)) • ξ)

theorem continuous_energyWeight (μ : Measure (Space d)) [IsFiniteMeasure μ] :
    Continuous (energyWeight μ) := by
  unfold energyWeight
  refine ((sourceFourier_continuous μ).norm.pow 2).mul ?_
  exact (continuous_const.add continuous_norm).rpow_const fun ξ =>
    Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (norm_nonneg ξ)))

/-- **Step 2.** For a Frostman measure of exponent `s > (d+1)/2`, the energy weight is
integrable. -/
theorem integrable_energyWeight (hd : 2 ≤ d) (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {s C : ℝ} (hs : ((d : ℝ) + 1) / 2 < s) (hb : FrostmanBallBound μ s C) :
    Integrable (energyWeight μ) := by
  set p := decayExp d with hp
  set u : ℝ := ((d : ℝ) + 1) / 2 with hu
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hu0 : 0 < u := by rw [hu]; linarith
  have hfin : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  have hud : u < (Module.finrank ℝ (Space d) : ℝ) := by rw [hfin, hu]; linarith
  have hexp : u - (Module.finrank ℝ (Space d) : ℝ) = -p := by
    rw [hfin, hu, hp, decayExp]; ring
  have hp0 : 0 ≤ p := by rw [hp, decayExp]; linarith
  -- finite Riesz energy and its Fourier form
  have hE := rieszEnergyOn_lt_top_of_frostman μ hu0 hs hb
  rw [source_fourier_energy_identity μ hu0 hud, hexp] at hE
  have hc := sourceEnergyConstant_pos hu0 hud
  have hI : ∫⁻ ξ : Space d, ENNReal.ofReal (‖sourceFourier μ ξ‖ ^ 2) *
      ENNReal.ofReal (‖ξ‖ ^ (-p)) < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne'] at hE
    exact lt_irrefl _ hE
  refine ⟨(continuous_energyWeight μ).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hI
  -- away from `ξ = 0`, `(1 + |ξ|)^{-p} ≤ |ξ|^{-p}`
  have hnull : ∀ᵐ ξ : Space d, ξ ≠ 0 := by
    have : Nontrivial (Space d) := by
      have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      infer_instance
    exact compl_mem_ae_iff.2 (measure_singleton (0 : Space d))
  filter_upwards [hnull] with ξ hξ
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hmono : (1 + ‖ξ‖) ^ (-p) ≤ ‖ξ‖ ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hξ0 (by linarith) (by linarith)
  rw [Real.enorm_eq_ofReal (by unfold energyWeight; positivity), energyWeight,
    ENNReal.ofReal_mul (by positivity)]
  gcongr

end MattilaSjolin
