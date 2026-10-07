import MattilaSjolin.Core.Defs

/-! Step 3: basic properties of the distance measure. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal

namespace MattilaSjolin

variable {d : ℕ}

/-- **Step 3.** The distance measure of a Frostman probability measure carried by `E` is a
probability measure, concentrated on `Δ(E)` and with no mass at `0`. -/
theorem distMeasure_properties {μ : Measure (Space d)} [IsProbabilityMeasure μ] {E : Set (Space d)}
    (hE : IsCompact E) (hμE : μ Eᶜ = 0) {s C : ℝ} (hs : 0 < s) (hb : FrostmanBallBound μ s C) :
    IsProbabilityMeasure (distMeasure μ) ∧
      distMeasure μ {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}ᶜ = 0 ∧
      0 < distMeasure μ (Ioi 0) := by
  have hm : Measurable (fun z : Space d × Space d => dist z.1 z.2) := continuous_dist.measurable
  have hP : IsProbabilityMeasure (distMeasure μ) := by unfold distMeasure; infer_instance
  refine ⟨hP, ?_, ?_⟩
  · have hD : {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} =
        (fun z : Space d × Space d => dist z.1 z.2) '' (E ×ˢ E) := by
      ext r; simp
    have hDc : IsCompact {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
      rw [hD]; exact (hE.prod hE).image continuous_dist
    unfold distMeasure
    rw [Measure.map_apply hm hDc.isClosed.measurableSet.compl]
    apply measure_mono_null (t := (Eᶜ ×ˢ univ) ∪ (univ ×ˢ Eᶜ))
    · intro z hz
      simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, not_exists, not_and] at hz
      by_contra h
      simp only [mem_union, mem_prod, mem_compl_iff, mem_univ, and_true, true_and, not_or,
        not_not] at h
      exact hz z.1 h.1 z.2 h.2 rfl
    · refine measure_union_null ?_ ?_ <;> simp [Measure.prod_prod, hμE]
  · have := noAtoms_of_frostman μ hs hb
    have h0 : distMeasure μ (Iic 0) = 0 := by
      unfold distMeasure
      rw [Measure.map_apply hm measurableSet_Iic,
        Measure.prod_apply (hm measurableSet_Iic)]
      have : ∀ x : Space d, (Prod.mk x ⁻¹' ((fun z : Space d × Space d => dist z.1 z.2) ⁻¹' Iic 0))
          = {x} := by
        intro x; ext y
        simp only [mem_preimage, mem_Iic, mem_singleton_iff]
        constructor
        · intro h; exact (dist_le_zero.mp h).symm
        · intro h; subst h; simp
      simp [this]
    have : Ioi (0:ℝ) = (Iic 0)ᶜ := by ext; simp
    rw [this, prob_compl_eq_one_sub measurableSet_Iic, h0]
    simp

end MattilaSjolin
