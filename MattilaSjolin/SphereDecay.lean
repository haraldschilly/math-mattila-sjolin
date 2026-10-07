import MattilaSjolin.Statement
import OAI.MeasureTheory.Falconer.Angular.SphereProduct
import OAI.MeasureTheory.Falconer.Angular.GnomonicDischarge
import OAI.MeasureTheory.Falconer.Estimates.QuadraticDischarge

/-!
# Fourier decay of the sphere measure

`sphereCheck d η = ∫_{S^{d-1}} e^{2πi⟨w,η⟩} dσ(w)` is the (inverse) Fourier transform of the surface
measure `σ = sphereMeasure d` on the unit sphere. `SphereDecay d` is the classical decay estimate
`|sphereCheck d η| ≤ C |η|^{-(d-1)/2}` for `|η| ≥ 1`.

For `d ≥ 3` it follows from OpenAI's stationary-phase expansion of sphere oscillatory integrals
(`OAI.Falconer.sphere_stationary_expansion_unscaled`, with one term and the constant symbol `1`),
whose leading coefficient is the explicit constant `sphereStationaryConstant (d-1)`
(`OAI.Falconer.actualStationaryCoefficient_zero`).
-/

open MeasureTheory OAI.Falconer
open scoped ContDiff RealInnerProductSpace

namespace MattilaSjolin

/-- `σ̌(η) = ∫_{S^{d-1}} e^{2πi⟨w,η⟩} dσ(w)`. -/
noncomputable def sphereCheck (d : ℕ) (η : Space d) : ℂ :=
  ∫ w : Sphere d, Complex.exp (2 * Real.pi * Complex.I * (⟪(w : Space d), η⟫ : ℂ)) ∂sphereMeasure d

/-- Fourier decay of the sphere measure in dimension `d`. -/
def SphereDecay (d : ℕ) : Prop :=
  ∃ C : ℝ, ∀ η : Space d, 1 ≤ ‖η‖ → ‖sphereCheck d η‖ ≤ C * ‖η‖ ^ (-(((d : ℝ) - 1) / 2))

/-- One-term stationary phase for the constant symbol on `S^{m+2} ⊂ ℝ^{m+3}`. -/
theorem sphereOscillation_one_le (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (e : Sphere (m+3)) (Λ : ℝ), 1 ≤ Λ →
      ‖sphereOscillation Λ e (fun _ => (1 : ℂ))‖ ≤ K * Λ ^ (-(((m+2 : ℕ) : ℝ) / 2)) := by
  obtain ⟨A, hA, hexp⟩ := sphere_stationary_expansion_unscaled published_gnomonic_surface
    published_quadratic_stationary m 1 le_rfl
  set c := sphereStationaryConstant (m+2)
  refine ⟨2 * ‖c‖ + A, by positivity, fun e Λ hΛ => ?_⟩
  have hderiv : ∀ j ≤ 2*1+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (fun _ : Space (m+3) => (1 : ℂ)) w‖ ≤ 1 * 1 ^ j := by
    intro j _ w
    rcases j with _ | j
    · simp
    · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
  have h := hexp e (fun _ => (1 : ℂ)) contDiff_const 1 1 zero_le_one le_rfl hderiv Λ hΛ
  set p : ℝ := ((m+2 : ℕ) : ℝ) / 2 with hp
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  -- the approximation is `Λ^{-p} (e^{iΛ} c + conj(e^{iΛ} c))`
  have happrox : ‖stationarySphereApprox m 1 Λ (fun _ => (1 : ℂ)) e‖ ≤ 2 * ‖c‖ * Λ ^ (-p) := by
    have hconj : antipodalConjugate (fun _ : Space (m+3) => (1 : ℂ)) = fun _ => 1 := by
      funext x; simp [antipodalConjugate]
    have hsum : directStationarySum m 1 Λ (fun _ => (1 : ℂ)) e = c := by
      simp [directStationarySum, c]
    have hexpI : ‖Complex.exp (Complex.I * (Λ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    unfold stationarySphereApprox
    rw [hconj, hsum]
    calc ‖((Λ ^ (-p) : ℝ) : ℂ) * (Complex.exp (Complex.I * (Λ : ℂ)) * c +
          star (Complex.exp (Complex.I * (Λ : ℂ)) * c))‖
        ≤ Λ ^ (-p) * (‖c‖ + ‖c‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_star, norm_mul, hexpI, one_mul]
      _ = 2 * ‖c‖ * Λ ^ (-p) := by ring
  have hrem : A * Λ ^ (-(1 : ℕ) - p : ℝ) * 1 * 1 ^ (2*1+(m+2)+1) ≤ A * Λ ^ (-p) := by
    simp only [one_pow, mul_one, Nat.cast_one]
    gcongr
    linarith
  have hrem' : ‖sphereOscillation Λ e (fun w => (1 : ℂ)) -
      stationarySphereApprox m 1 Λ (fun _ => (1 : ℂ)) e‖ ≤ A * Λ ^ (-p) := by
    refine le_trans ?_ hrem
    simpa [hp] using h
  calc ‖sphereOscillation Λ e (fun _ => (1 : ℂ))‖
      ≤ ‖stationarySphereApprox m 1 Λ (fun _ => (1 : ℂ)) e‖ +
        ‖sphereOscillation Λ e (fun w => (1 : ℂ)) -
          stationarySphereApprox m 1 Λ (fun _ => (1 : ℂ)) e‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ 2 * ‖c‖ * Λ ^ (-p) + A * Λ ^ (-p) := add_le_add happrox hrem'
    _ = (2 * ‖c‖ + A) * Λ ^ (-p) := by ring

/-- `σ̌(η)` as a sphere oscillation in the direction `η/‖η‖` with frequency `2π‖η‖`. -/
theorem sphereCheck_eq_sphereOscillation {d : ℕ} {η : Space d} (hη : η ≠ 0) :
    sphereCheck d η = sphereOscillation (2 * Real.pi * ‖η‖)
      ⟨‖η‖⁻¹ • η, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hη)]⟩
      (fun _ => (1 : ℂ)) := by
  unfold sphereCheck sphereOscillation
  congr 1
  funext w
  rw [mul_one]
  congr 1
  have hn : (‖η‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hη
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [real_inner_comm]
  field_simp
  push_cast
  ring

/-- **Sphere decay for `d ≥ 3`.** -/
theorem sphereDecay_add_three (m : ℕ) : SphereDecay (m+3) := by
  obtain ⟨K, hK, hosc⟩ := sphereOscillation_one_le m
  refine ⟨K, fun η hη => ?_⟩
  have hη0 : η ≠ 0 := by
    rintro rfl; norm_num at hη
  have h2π : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hΛ : 1 ≤ 2 * Real.pi * ‖η‖ := by nlinarith [norm_nonneg η]
  rw [sphereCheck_eq_sphereOscillation hη0]
  refine (hosc _ _ hΛ).trans ?_
  have hexp : (-(((m+2 : ℕ) : ℝ) / 2)) = -((((m+3 : ℕ) : ℝ) - 1) / 2) := by
    push_cast; ring
  rw [hexp, Real.mul_rpow (by positivity) (norm_nonneg η)]
  have hp : 0 ≤ (((m+3 : ℕ) : ℝ) - 1) / 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast; linarith
  have hfac : (2 * Real.pi) ^ (-((((m+3 : ℕ) : ℝ) - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2π (by linarith)
  calc K * ((2 * Real.pi) ^ (-((((m+3 : ℕ) : ℝ) - 1) / 2)) *
        ‖η‖ ^ (-((((m+3 : ℕ) : ℝ) - 1) / 2)))
      ≤ K * (1 * ‖η‖ ^ (-((((m+3 : ℕ) : ℝ) - 1) / 2))) := by
        gcongr
    _ = K * ‖η‖ ^ (-((((m+3 : ℕ) : ℝ) - 1) / 2)) := by ring

end MattilaSjolin
