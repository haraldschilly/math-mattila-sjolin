import MattilaSjolin.Circle.ArcLength
import OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryExpansion
import OAI.MeasureTheory.Falconer.Angular.RotatedCircleIntegral

/-!
# Fourier decay of the circle measure (`d = 2`)

`|σ̌(η)| ≤ C |η|^{-1/2}`. By `integral_sphereMeasure_two` and a rotation, `σ̌(η)` is the oscillatory
integral `∫_{-π}^{π} e^{iλ cos θ} dθ` with `λ = 2π|η|`; OpenAI's full-circle stationary-phase
expansion (`OAI.PlanarFalconer.full_circle_stationary_expansion`, one term, constant symbol `1`)
bounds it by `C λ^{-1/2}`.
-/

open MeasureTheory Set OAI.Falconer OAI.PlanarFalconer
open scoped ContDiff ComplexConjugate RealInnerProductSpace

namespace MattilaSjolin

/-- One-term stationary phase on the full circle for the constant symbol. -/
theorem cosineOscillator_integral_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ‖∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ * 1‖ ≤ K * Λ ^ (-1/2 : ℝ) := by
  obtain ⟨A, B, hA, hB, hexp⟩ := full_circle_stationary_expansion 0 1
  set w : ℂ := stationaryDerivativeExpansion (fun _ : ℝ => (1 : ℂ)) 0 1 with hw
  refine ⟨2 * Real.sqrt (2 * Real.pi) * ‖stationaryAmplitude (fun _ : ℝ => (1 : ℂ)) 0‖ +
    Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2) * A + B, by positivity, fun Λ hΛ => ?_⟩
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hderiv : ∀ k ≤ max (2*(0+1)+2) 1, ∀ x : ℝ,
      ‖iteratedDeriv k (fun _ : ℝ => (1 : ℂ)) x‖ ≤ 1 * 1 ^ k := by
    intro k _ x
    rcases k with _ | k
    · simp
    · simp [iteratedDeriv_const]
  have h := hexp (f := fun _ => (1 : ℂ)) contDiff_const (fun _ => rfl) hΛ0 zero_le_one le_rfl hderiv
  -- the leading term
  have hS : ∀ Λ' : ℝ, stationaryDerivativeExpansion (fun _ : ℝ => (1 : ℂ)) 0 Λ' =
      stationaryAmplitude (fun _ : ℝ => (1 : ℂ)) 0 := by
    intro Λ'; simp [stationaryDerivativeExpansion]
  have hconj : (fun θ : ℝ => conj ((fun _ : ℝ => (1 : ℂ)) (θ + Real.pi))) = fun _ => (1 : ℂ) := by
    funext θ; simp
  have hfres : ‖fresnelCoefficient (Λ / 2)‖ = Real.sqrt (2 * Real.pi) * Λ ^ (-1/2 : ℝ) := by
    rw [fresnelCoefficient_norm (by positivity), quadratic_scale_half hΛ0]; ring
  have hexpI : ‖Complex.exp (Complex.I * (Λ : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  set a := ‖stationaryAmplitude (fun _ : ℝ => (1 : ℂ)) 0‖
  have hE : ‖fullCircleStationaryExpansion Λ (fun _ => (1 : ℂ)) 0‖ ≤
      2 * Real.sqrt (2 * Real.pi) * a * Λ ^ (-1/2 : ℝ) := by
    unfold fullCircleStationaryExpansion
    rw [hconj, hS]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_conj, norm_mul, norm_mul, hexpI, hfres]
    nlinarith [Real.rpow_nonneg hΛ0.le (-1/2 : ℝ), norm_nonneg a, Real.sqrt_nonneg (2 * Real.pi)]
  -- the remainder
  have hR : ((Real.pi / (Λ / 2)) ^ (1/2 : ℝ) * ((Real.pi ^ 2 / (Λ / 2)) ^ (0+1) /
      ((Nat.factorial 0 : ℕ) : ℝ))) * (A * 1 * 1 ^ (2*(0+1)+2)) + B * 1 * 1 ^ 1 / Λ ^ 1 ≤
      (Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2) * A + B) * Λ ^ (-1/2 : ℝ) := by
    rw [quadratic_scale_half hΛ0]
    have hh : Λ ^ (-1/2 : ℝ) * Λ ^ (-1/2 : ℝ) = Λ⁻¹ := by
      rw [← Real.rpow_add hΛ0]; norm_num [Real.rpow_neg_one]
    have hinv : Λ⁻¹ ≤ Λ ^ (-1/2 : ℝ) := by
      rw [← hh]
      have : Λ ^ (-1/2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΛ (by norm_num)
      nlinarith [Real.rpow_nonneg hΛ0.le (-1/2 : ℝ)]
    have hq : Real.pi ^ 2 / (Λ / 2) = 2 * Real.pi ^ 2 * Λ⁻¹ := by field_simp
    simp only [hq, pow_one, one_pow, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, zero_add]
    have hs := Real.sqrt_nonneg (2 * Real.pi)
    have hp := Real.rpow_nonneg hΛ0.le (-1/2 : ℝ)
    have hB' : B / Λ ≤ B * Λ ^ (-1/2 : ℝ) := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv hB
    have hA' : Λ ^ (-1/2 : ℝ) * Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2 * Λ⁻¹) * A ≤
        Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2) * A * Λ ^ (-1/2 : ℝ) := by
      have hΛinv : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
      have h0 : 0 ≤ Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2) * A * Λ ^ (-1/2 : ℝ) := by positivity
      nlinarith [inv_nonneg.2 hΛ0.le]
    linarith
  calc ‖∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ * 1‖
      ≤ ‖fullCircleStationaryExpansion Λ (fun _ => (1 : ℂ)) 0‖ +
        ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ * 1) -
          fullCircleStationaryExpansion Λ (fun _ => (1 : ℂ)) 0‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ 2 * Real.sqrt (2 * Real.pi) * a * Λ ^ (-1/2 : ℝ) +
        (Real.sqrt (2 * Real.pi) * (2 * Real.pi ^ 2) * A + B) * Λ ^ (-1/2 : ℝ) :=
        add_le_add hE (h.trans hR)
    _ = _ := by ring

/-- `σ̌(η) = ∫_{-π}^{π} e^{i 2π|η| cos θ} dθ` in the plane. -/
theorem sphereCheck_two_eq {η : Space 2} (hη : η ≠ 0) :
    sphereCheck 2 η = ∫ θ in (-Real.pi)..Real.pi, cosineOscillator (2 * Real.pi * ‖η‖) θ * 1 := by
  obtain ⟨α, hα⟩ := displacement_has_angle hη
  unfold sphereCheck
  have hA := integral_sphereMeasure_two
    (fun z : Space 2 => Complex.exp (2 * Real.pi * Complex.I * (⟪z, η⟫ : ℂ))) (by fun_prop)
  rw [hA]
  rw [← rotated_circle_integral (2 * Real.pi * ‖η‖) α (f := fun _ => (1 : ℂ)) (fun _ => rfl)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [mul_one, cosineOscillator]
  congr 1
  conv_lhs => rw [hα]
  rw [inner_smul_right, inner_sourceDirection]
  push_cast
  ring

/-- **Sphere decay for `d = 2`.** -/
theorem sphereDecay_two : SphereDecay 2 := by
  obtain ⟨K, hK, hosc⟩ := cosineOscillator_integral_le
  refine ⟨K, fun η hη => ?_⟩
  have hη0 : η ≠ 0 := by rintro rfl; norm_num at hη
  have h2π : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hΛ : 1 ≤ 2 * Real.pi * ‖η‖ := by nlinarith [norm_nonneg η]
  rw [sphereCheck_two_eq hη0]
  refine (hosc _ hΛ).trans ?_
  have hexp : (-1/2 : ℝ) = -((((2 : ℕ) : ℝ) - 1) / 2) := by norm_num
  rw [hexp, Real.mul_rpow (by positivity) (norm_nonneg η)]
  have hfac : (2 * Real.pi) ^ (-((((2 : ℕ) : ℝ) - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2π (by norm_num)
  calc K * ((2 * Real.pi) ^ (-((((2 : ℕ) : ℝ) - 1) / 2)) * ‖η‖ ^ (-((((2 : ℕ) : ℝ) - 1) / 2)))
      ≤ K * (1 * ‖η‖ ^ (-((((2 : ℕ) : ℝ) - 1) / 2))) := by gcongr
    _ = K * ‖η‖ ^ (-((((2 : ℕ) : ℝ) - 1) / 2)) := by ring

end MattilaSjolin
