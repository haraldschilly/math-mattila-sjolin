import MattilaSjolin.Core.Energy
import MattilaSjolin.Core.DistMeasure
import MattilaSjolin.Core.Spectral
import MattilaSjolin.Core.Continuity
import MattilaSjolin.Core.Interval

/-!
# Core: sphere decay in dimension `d` implies Mattila–Sjölin in dimension `d`

See `BLUEPRINT.md` for the argument.
-/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal ContDiff

namespace MattilaSjolin

variable {d : ℕ}

/-- **Core theorem.** Sphere decay in dimension `d ≥ 2` implies the Mattila–Sjölin theorem in
dimension `d`. -/
theorem mattilaSjolin_of_sphereDecay (hd : 2 ≤ d) (hdec : SphereDecay d)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hE : IsCompact E)
    (hdim : ((d : ℝ≥0∞) + 1) / 2 < dimH E) :
    (interior {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty := by
  -- choose a Frostman exponent `s` with `(d+1)/2 < s < dimH E`
  obtain ⟨s, hs1, hs2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hdim
  have hsd : ((d : ℝ) + 1) / 2 < (s : ℝ) := by
    have h := hs1
    rw [show ((d : ℝ≥0∞) + 1) / 2 = ENNReal.ofReal (((d : ℝ) + 1) / 2) by
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]
      simp] at h
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top).1 h
  have hs0 : 0 < s := by
    have : (0 : ℝ) < s := lt_of_le_of_lt (by positivity) hsd
    exact_mod_cast this
  obtain ⟨μ, hμE, C, hC, hb⟩ := frostman_probability (by omega) E hE hs0 hs2
  have hw := integrable_energyWeight hd (μ : Measure (Space d)) hsd hb
  obtain ⟨hprob, hνS, hpos⟩ := distMeasure_properties hE hμE (by exact_mod_cast hs0) hb
  have hS : IsClosed {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
    have : {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} = (fun p : _ × _ => dist p.1 p.2) '' (E ×ˢ E) := by
      ext r; simp
    rw [this]
    exact ((hE.prod hE).image continuous_dist).isClosed
  exact interior_nonempty_of_spectral hS hνS hpos (continuousOn_distDensity hdec _ hw)
    (fun φ hφ a b ha hsupp => integral_distMeasure_eq hd hdec _ hw hφ ha hsupp)

/-- **Mattila–Sjölin for `d ≥ 3`.** -/
theorem mattilaSjolin_of_three_le {d : ℕ} (hd : 3 ≤ d)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hE : IsCompact E)
    (hdim : ((d : ℝ≥0∞) + 1) / 2 < dimH E) :
    (interior {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  exact mattilaSjolin_of_sphereDecay (by omega) (sphereDecay_add_three m) E hE hdim

end MattilaSjolin
