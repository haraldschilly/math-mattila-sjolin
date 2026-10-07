import MattilaSjolin.Core.Defs

/-! Step 0: sphere decay in the form `|σ̌(η)| ≤ C (1+|η|)^{-(d-1)/2}`. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal RealInnerProductSpace

namespace MattilaSjolin

variable {d : ℕ}

/-- **Step 0.** Sphere decay in the form `|σ̌(η)| ≤ C (1 + |η|)^{-(d-1)/2}` for all `η`. -/
theorem sphereCheck_le_of_sphereDecay (hdec : SphereDecay d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : Space d, ‖sphereCheck d η‖ ≤ C * (1 + ‖η‖) ^ (-decayExp d) := by
  obtain ⟨C₀, hC₀⟩ := hdec
  -- trivial bound by the total mass of the sphere
  set M := (sphereMeasure d).real univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  have htriv : ∀ η : Space d, ‖sphereCheck d η‖ ≤ M := fun η => by
    have h := norm_integral_le_of_norm_le_const (μ := sphereMeasure d) (C := 1)
      (f := fun w : Sphere d => Complex.exp (2 * Real.pi * Complex.I * (⟪(w : Space d), η⟫ : ℂ)))
      (Eventually.of_forall fun w => by
        rw [Complex.norm_exp]
        simp)
    simpa [sphereCheck, hM] using h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: `ℝ^0` is a point, so the unit sphere is empty and `σ̌ = 0`
    refine ⟨0, le_rfl, fun η => ?_⟩
    have hempty : IsEmpty (Sphere 0) := ⟨fun w => by
      have h1 : ‖(w : Space 0)‖ = 1 := by simp
      rw [Subsingleton.elim (w : Space 0) 0, norm_zero] at h1
      exact zero_ne_one h1⟩
    simp [sphereCheck, MeasureTheory.integral_of_isEmpty]
  set p := decayExp d with hp
  have hp0 : 0 ≤ p := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hp, decayExp]; linarith
  refine ⟨(|C₀| + M) * 2 ^ p, by positivity, fun η => ?_⟩
  have h1 : 0 < 1 + ‖η‖ := by positivity
  -- if `1 + ‖η‖ ≤ 2x` then `x^{-p} ≤ 2^p (1 + ‖η‖)^{-p}`
  have key : ∀ x : ℝ, 0 < x → 1 + ‖η‖ ≤ 2 * x → x ^ (-p) ≤ 2 ^ p * (1 + ‖η‖) ^ (-p) := by
    intro x hx hle
    have hpow : (1 + ‖η‖) ^ p ≤ 2 ^ p * x ^ p := by
      rw [← Real.mul_rpow two_pos.le hx.le]
      exact Real.rpow_le_rpow h1.le hle hp0
    have hpos : 0 < (1 + ‖η‖) ^ p := Real.rpow_pos_of_pos h1 p
    have h2p : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos two_pos p
    have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    rw [Real.rpow_neg hx.le, Real.rpow_neg h1.le]
    calc (x ^ p)⁻¹ = 2 ^ p * (2 ^ p * x ^ p)⁻¹ := by field_simp
      _ ≤ 2 ^ p * ((1 + ‖η‖) ^ p)⁻¹ := by gcongr
  have hbound : 0 ≤ 2 ^ p * (1 + ‖η‖) ^ (-p) := by positivity
  by_cases hη : 1 ≤ ‖η‖
  · have hη0 : 0 < ‖η‖ := lt_of_lt_of_le one_pos hη
    calc ‖sphereCheck d η‖ ≤ C₀ * ‖η‖ ^ (-p) := hC₀ η hη
      _ ≤ |C₀| * ‖η‖ ^ (-p) := by gcongr; exact le_abs_self C₀
      _ ≤ |C₀| * (2 ^ p * (1 + ‖η‖) ^ (-p)) := by gcongr; exact key _ hη0 (by linarith)
      _ ≤ (|C₀| + M) * 2 ^ p * (1 + ‖η‖) ^ (-p) := by nlinarith [abs_nonneg C₀]
  · push Not at hη
    have hone := key 1 one_pos (by linarith)
    rw [Real.one_rpow] at hone
    calc ‖sphereCheck d η‖ ≤ M := htriv η
      _ ≤ M * (2 ^ p * (1 + ‖η‖) ^ (-p)) := le_mul_of_one_le_right hM0 hone
      _ ≤ (|C₀| + M) * 2 ^ p * (1 + ‖η‖) ^ (-p) := by nlinarith [abs_nonneg C₀]

end MattilaSjolin
