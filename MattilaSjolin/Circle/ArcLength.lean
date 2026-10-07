import MattilaSjolin.SphereDecay
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength
import OAI.MeasureTheory.Falconer.Angular.StationaryArcLength
import OAI.MeasureTheory.Falconer.Angular.AngularStripMeasure

/-! The sphere measure on the unit circle is arc length:
`∫_{S¹} g dσ = ∫_{-π}^{π} g(cos θ, sin θ) dθ`. -/

open MeasureTheory Set OAI.Falconer OAI.PlanarFalconer
open scoped Pointwise ENNReal

namespace MattilaSjolin

/-- The obvious map from the planar unit circle to `Sphere 2`. -/
def unitCircleToSphereTwo (ω : UnitCircle) : Sphere 2 :=
  ⟨ω.1, by simp [ω.2]⟩

theorem continuous_unitCircleToSphereTwo : Continuous unitCircleToSphereTwo :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The open unit cone over a subset of the unit circle, written as a preimage. -/
theorem Ioo_smul_eq_cone (T : Set (Space 2)) (hT : T ⊆ Metric.sphere 0 1) :
    Ioo (0 : ℝ) 1 • T = {z | z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖z‖⁻¹ • z ∈ T} := by
  ext z
  simp only [Set.mem_smul, mem_Ioo, mem_ofPred_eq]
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, w, hw, rfl⟩
    have hw1 : ‖w‖ = 1 := by simpa using hT hw
    have hn : ‖r • w‖ = r := by rw [norm_smul, hw1, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    refine ⟨?_, by rw [hn]; exact hr1, ?_⟩
    · intro h; rw [h, norm_zero] at hn; linarith
    · rw [hn, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]; exact hw
  · rintro ⟨hz0, hz1, hzT⟩
    refine ⟨‖z‖, ⟨norm_pos_iff.2 hz0, hz1⟩, _, hzT, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz0), one_smul]

theorem lintegral_Ioo_zero_one_ofReal :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_id]
    norm_num
  · exact (continuous_id.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hr.1.le

theorem cone_volume (T : Set (Space 2)) (hT : T ⊆ Metric.sphere 0 1) (hTm : MeasurableSet T) :
    2 * volume (Ioo (0 : ℝ) 1 • T) =
      volume (sourceDirection ⁻¹' T ∩ Ioc 0 (2 * Real.pi)) := by
  rw [Ioo_smul_eq_cone T hT]
  set C : Set (Space 2) := {z | z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖z‖⁻¹ • z ∈ T} with hC
  have hCm : MeasurableSet C := by
    refine (measurableSet_singleton 0).compl.inter
      ((measurableSet_lt measurable_norm measurable_const).inter ?_)
    exact hTm.preimage (by fun_prop)
  have hTm' : MeasurableSet (sourceDirection ⁻¹' T) := hTm.preimage (by fun_prop)
  rw [← lintegral_indicator_one hCm]
  rw [← plane_polar_lintegral (C.indicator 1) (measurable_one.indicator hCm)]
  have hinner : ∀ θ, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * C.indicator 1 (r • sourceDirection θ))
      = (sourceDirection ⁻¹' T).indicator 1 θ * ENNReal.ofReal (1 / 2) := by
    intro θ
    have hpt : ∀ r ∈ Ioi (0:ℝ), ENNReal.ofReal r * C.indicator 1 (r • sourceDirection θ) =
        (sourceDirection ⁻¹' T).indicator 1 θ * (Iio 1).indicator (fun r => ENNReal.ofReal r) r := by
      intro r hr
      have hr0 : (0:ℝ) < r := hr
      have hn : ‖r • sourceDirection θ‖ = r := by
        rw [norm_smul, norm_sourceDirection, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
      have hmem : r • sourceDirection θ ∈ C ↔ r < 1 ∧ sourceDirection θ ∈ T := by
        simp only [hC, mem_ofPred_eq, hn]
        rw [smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h1, h2⟩
          intro h; rw [h, norm_zero] at hn; linarith
      by_cases h1 : r < 1 <;> by_cases h2 : sourceDirection θ ∈ T <;>
        simp [indicator, hmem, h1, h2]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _
      (ENNReal.measurable_ofReal.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, lintegral_Ioo_zero_one_ofReal]
  simp_rw [hinner]
  rw [lintegral_mul_const _ (measurable_one.indicator hTm'), lintegral_indicator_one hTm',
    Measure.restrict_apply hTm', ← mul_assoc, mul_comm (2 : ℝ≥0∞), mul_assoc]
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [h2, mul_one]

theorem sphereMeasure_two_eq :
    sphereMeasure 2 = sourceArcLength.map unitCircleToSphereTwo := by
  ext s hs
  rw [Measure.map_apply continuous_unitCircleToSphereTwo.measurable hs, sphereMeasure,
    Measure.toSphere_apply' _ hs, finrank_euclideanSpace_fin]
  have hT : ((↑) '' s : Set (Space 2)) ⊆ Metric.sphere 0 1 := by
    rintro _ ⟨w, -, rfl⟩; exact w.2
  have hTm : MeasurableSet ((↑) '' s : Set (Space 2)) :=
    MeasurableSet.subtype_image Metric.isClosed_sphere.measurableSet hs
  push_cast
  rw [cone_volume _ hT hTm, sourceArcLength,
    Measure.map_apply continuous_sourceUnitDirection.measurable
      (continuous_unitCircleToSphereTwo.measurable hs),
    Measure.restrict_apply' measurableSet_Ioc]
  congr 2
  ext θ
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨w, hw, hwe⟩
    convert hw
    exact Subtype.ext hwe.symm
  · intro h
    exact ⟨_, h, rfl⟩

/-- Integrals against `sphereMeasure 2 = volume.toSphere` are arc-length integrals. -/
theorem integral_sphereMeasure_two (g : Space 2 → ℂ) (hg : Continuous g) :
    ∫ w : Sphere 2, g w ∂sphereMeasure 2 =
      ∫ θ in (-Real.pi)..Real.pi, g (sourceDirection θ) := by
  rw [sphereMeasure_two_eq, integral_map (f := fun w : Sphere 2 => g w) continuous_unitCircleToSphereTwo.measurable.aemeasurable
    (hg.comp continuous_subtype_val).aestronglyMeasurable]
  exact sourceArcLength_integral_period
    ((hg.comp continuous_subtype_val).comp continuous_unitCircleToSphereTwo).aestronglyMeasurable

end MattilaSjolin
