import MattilaSjolin.SphereDecay

/-! Step 4, part S5: polar coordinates for the Fourier integral of a radial function. -/

open MeasureTheory Set Filter Topology OAI.Falconer
open scoped ENNReal NNReal RealInnerProductSpace

namespace MattilaSjolin

variable {d : ℕ}

/-- For `φ` continuous and supported in `[a, b]`:
`∫_{ℝ^d} e^{2πi⟨z,ξ⟩} φ(|z|) dz = ∫_0^∞ t^{d-1} φ(t) σ̌(tξ) dt`. -/
theorem integral_exp_radial_eq (hd : 1 ≤ d) (φ : ℝ → ℝ) (hφ : Continuous φ) {a b : ℝ}
    (hsupp : Function.support φ ⊆ Icc a b) (ξ : Space d) :
    ∫ z : Space d, Complex.exp (2 * Real.pi * Complex.I * (⟪z, ξ⟫ : ℂ)) * (φ ‖z‖ : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((t ^ (d - 1) * φ t : ℝ) : ℂ) * sphereCheck d (t • ξ) := by
  classical
  have hfin : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  have : Nontrivial (Space d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set F : Space d → ℂ := fun z =>
    Complex.exp (2 * Real.pi * Complex.I * (⟪z, ξ⟫ : ℂ)) * (φ ‖z‖ : ℂ) with hFdef
  set e := homeomorphUnitSphereProd (Space d) with he
  have hmp := (volume : Measure (Space d)).measurePreserving_homeomorphUnitSphereProd
  rw [hfin] at hmp
  -- integrability of `F`
  have hFcont : Continuous F := by
    simp only [hFdef]
    fun_prop
  have hFsupp : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space d) b) fun z hz => ?_
    have hzb : b < ‖z‖ := by simpa using hz
    have : φ ‖z‖ = 0 := by
      by_contra h
      exact absurd (hsupp h).2 (not_le.2 hzb)
    simp [F, this]
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFsupp
  -- the integrand in polar coordinates
  set G : Sphere d × Ioi (0 : ℝ) → ℂ := fun p => F (e.symm p : Space d) with hG
  have hGF : ∀ x : ({(0 : Space d)}ᶜ : Set (Space d)), G (e x) = F x := fun x => by
    simp [G]
  have hGint : Integrable G
      ((volume : Measure (Space d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : G ∘ e = F ∘ Subtype.val := funext hGF
    rw [this, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hFint.integrableOn
  have step1 : ∫ z, F z = ∫ p, G p
      ∂((volume : Measure (Space d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    calc ∫ z, F z
        = ∫ x : ({(0 : Space d)}ᶜ : Set (Space d)), F x ∂(volume.comap Subtype.val) := by
          rw [integral_subtype_comap (measurableSet_singleton _).compl F,
            restrict_compl_singleton]
      _ = ∫ x : ({(0 : Space d)}ᶜ : Set (Space d)), G (e x) ∂(volume.comap Subtype.val) := by
          simp_rw [hGF]
      _ = _ := hmp.integral_comp (Homeomorph.measurableEmbedding _) G
  have hGpt : ∀ (w : Sphere d) (r : Ioi (0 : ℝ)), G (w, r) =
      Complex.exp (2 * Real.pi * Complex.I * (⟪(w : Space d), r.1 • ξ⟫ : ℂ)) * (φ r.1 : ℂ) := by
    intro w r
    have hr : 0 < r.1 := r.2
    have hw : ‖(w : Space d)‖ = 1 := by simp
    simp only [G, F, he, homeomorphUnitSphereProd_symm_apply_coe, real_inner_smul_left,
      real_inner_smul_right, norm_smul, hw, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  set H : ℝ → ℂ := fun t => sphereCheck d (t • ξ) * (φ t : ℂ) with hH
  have step2 : ∀ r : Ioi (0 : ℝ), ∫ w, G (w, r) ∂(volume : Measure (Space d)).toSphere = H r.1 := by
    intro r
    simp_rw [hGpt]
    rw [integral_mul_const]
    rfl
  rw [show (∫ z : Space d, Complex.exp (2 * Real.pi * Complex.I * (⟪z, ξ⟫ : ℂ)) * (φ ‖z‖ : ℂ))
      = ∫ z, F z from rfl, step1, integral_prod_symm G hGint]
  simp_rw [step2]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ (d - 1)) • H a]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [H]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt ht) _), Complex.real_smul]
  push_cast
  ring

end MattilaSjolin
