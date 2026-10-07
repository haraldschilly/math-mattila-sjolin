import Mathlib

/-! Steps 6–7: from the spectral identity to an interval (abstract real analysis).

Note: `ContDiff ℝ ∞` (smooth). In current Mathlib `ContDiff ℝ ⊤` means *analytic* (`⊤ = ω`), and
an analytic function with compact support vanishes, which would make the hypothesis vacuous. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace MattilaSjolin

lemma exists_bump_ball (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x, 0 ≤ φ x) ∧ Function.support φ = Metric.ball c r ∧
      HasCompactSupport φ := by
  let β : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  exact ⟨β, β.contDiff, fun x => β.nonneg, β.support_eq, β.hasCompactSupport⟩

lemma integrableOn_bump_mul {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support φ ⊆ Icc a b) :
    IntegrableOn (fun t => (φ t : ℂ) * f t) (Ioi 0) := by
  have hK : IntegrableOn (fun t => (φ t : ℂ) * f t) (Icc a b) :=
    ((Complex.continuous_ofReal.comp hφ).continuousOn.mul
      (hf.mono fun x hx => lt_of_lt_of_le ha hx.1)).integrableOn_Icc
  refine hK.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro t ht
  have : φ t = 0 := by
    by_contra h
    exact ht.2 (hsupp h)
  simp [this]

lemma re_setIntegral_bump_mul {f : ℝ → ℂ} {φ : ℝ → ℝ}
    (hint : IntegrableOn (fun t => (φ t : ℂ) * f t) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), (φ t : ℂ) * f t).re = ∫ t in Ioi (0 : ℝ), φ t * (f t).re := by
  have := integral_re hint
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at this
  exact this.symm

theorem interior_nonempty_of_spectral {ν : Measure ℝ} [IsFiniteMeasure ν] {S : Set ℝ}
    (hS : IsClosed S) (hνS : ν Sᶜ = 0) (hpos : 0 < ν (Ioi 0)) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi 0))
    (hid : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ a b : ℝ, 0 < a → Function.support φ ⊆ Icc a b →
      ((∫ t, φ t ∂ν : ℝ) : ℂ) = ∫ t in Ioi (0 : ℝ), (φ t : ℂ) * f t) :
    (interior S).Nonempty := by
  -- Step 1: an interval `Ioo p q` with `0 < p` and positive mass.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < ν (Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
    by_contra h
    push Not at h
    have h0 : ν (⋃ n : ℕ, Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) = 0 :=
      measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)
    refine hpos.ne' (measure_mono_null ?_ h0)
    intro x (hx : 0 < x)
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
    refine mem_iUnion.2 ⟨n, ?_, ?_⟩
    · have h1 : 1 / x < n + 1 := by linarith [le_max_right x (1 / x)]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hx] at h1
      linarith
    · linarith [le_max_left x (1 / x)]
  set p : ℝ := 1 / ((n : ℝ) + 1) with hp_def
  set q : ℝ := (n : ℝ) + 1 with hq_def
  have hp : 0 < p := by positivity
  have hpq : p < q := by
    by_contra h
    push Not at h
    rw [Ioo_eq_empty (not_lt.2 h), measure_empty] at hn
    exact lt_irrefl _ hn
  obtain ⟨φ₀, hφ₀, hφ₀0, hφ₀s, hφ₀c⟩ :=
    exists_bump_ball ((p + q) / 2) (r := (q - p) / 2) (by linarith)
  have hball : Metric.ball ((p + q) / 2) ((q - p) / 2) = Ioo p q := by
    rw [Real.ball_eq_Ioo]; congr 1 <;> ring
  rw [hball] at hφ₀s
  have hsupp₀ : Function.support φ₀ ⊆ Icc p q := hφ₀s ▸ Ioo_subset_Icc_self
  have hνpos : 0 < ∫ t, φ₀ t ∂ν := by
    rw [integral_pos_iff_support_of_nonneg hφ₀0
      (hφ₀.continuous.integrable_of_hasCompactSupport hφ₀c), hφ₀s]
    exact hn
  -- Step 2: a point `t₀ ∈ (p, q)` where `Re f > 0`.
  obtain ⟨t₀, ht₀, hft₀⟩ : ∃ t₀ ∈ Ioo p q, 0 < (f t₀).re := by
    by_contra h
    push Not at h
    have hre := congrArg Complex.re (hid φ₀ hφ₀ p q hp hsupp₀)
    rw [Complex.ofReal_re] at hre
    rw [re_setIntegral_bump_mul (integrableOn_bump_mul hf hφ₀.continuous hp hsupp₀)] at hre
    have : ∫ t in Ioi (0 : ℝ), φ₀ t * (f t).re ≤ 0 := by
      refine integral_nonpos fun t => ?_
      by_cases ht : t ∈ Ioo p q
      · exact mul_nonpos_of_nonneg_of_nonpos (hφ₀0 t) (h t ht)
      · have : φ₀ t = 0 := by
          by_contra h'
          exact ht (hφ₀s ▸ h')
        simp [this]
    linarith
  have ht₀pos : 0 < t₀ := hp.trans ht₀.1
  -- Step 3: a neighbourhood of `t₀` on which `Re f > 0`.
  have hcont : ContinuousAt (fun t => (f t).re) t₀ :=
    Complex.continuous_re.continuousAt.comp (hf.continuousAt (Ioi_mem_nhds ht₀pos))
  have hev : ∀ᶠ t in 𝓝 t₀, 0 < t ∧ 0 < (f t).re :=
    Filter.Eventually.and (Ioi_mem_nhds ht₀pos) (hcont.eventually (Ioi_mem_nhds hft₀))
  obtain ⟨U, hUsub, hUo, ht₀U⟩ := mem_nhds_iff.1 hev
  -- Step 4: `U ⊆ S`.
  have hUS : U ⊆ S := by
    intro t htU
    by_contra htS
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (hUo.inter hS.isOpen_compl) t ⟨htU, htS⟩
    obtain ⟨φ, hφ, hφ0, hφs, -⟩ := exists_bump_ball t (half_pos hε)
    have hsub : Metric.ball t (ε / 2) ⊆ U ∩ Sᶜ :=
      (Metric.ball_subset_ball (by linarith)).trans hεsub
    have hapos : 0 < t - ε / 2 := by
      have : t - ε / 2 ∈ Metric.ball t ε := by
        rw [Real.ball_eq_Ioo]; constructor <;> linarith
      exact (hUsub (hεsub this).1).1
    have hsupp : Function.support φ ⊆ Icc (t - ε / 2) (t + ε / 2) := by
      rw [hφs, Real.ball_eq_Ioo]; exact Ioo_subset_Icc_self
    have hzero : ∫ s, φ s ∂ν = 0 := by
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun s hs => ?_) hνS
      exact (hsub (hφs ▸ (hs : φ s ≠ 0))).2
    have hint := integrableOn_bump_mul hf hφ.continuous hapos hsupp
    have hre := congrArg Complex.re (hid φ hφ _ _ hapos hsupp)
    rw [hzero, Complex.ofReal_zero, Complex.zero_re, re_setIntegral_bump_mul hint] at hre
    have hnn : 0 ≤ fun s => φ s * (f s).re := by
      intro s
      by_cases hs : φ s = 0
      · simp [hs]
      · exact mul_nonneg (hφ0 s) (hUsub (hsub (hφs ▸ hs)).1).2.le
    have hpos' : 0 < ∫ s in Ioi (0 : ℝ), φ s * (f s).re := by
      have hi : Integrable (fun s => φ s * (f s).re) (volume.restrict (Ioi 0)) := by
        have := hint.re
        simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at this
        exact this
      rw [integral_pos_iff_support_of_nonneg hnn hi]
      have hballsupp : Metric.ball t (ε / 2) ⊆ Function.support fun s => φ s * (f s).re := by
        intro s hs
        have h1 : φ s ≠ 0 := by rw [← Function.mem_support, hφs]; exact hs
        exact mul_ne_zero h1 (hUsub (hsub hs).1).2.ne'
      refine lt_of_lt_of_le ?_ (measure_mono hballsupp)
      rw [Measure.restrict_apply measurableSet_ball,
        inter_eq_left.2 (show Metric.ball t (ε / 2) ⊆ Ioi 0 from
          fun s hs => (hUsub (hsub hs).1).1)]
      exact Metric.measure_ball_pos _ _ (half_pos hε)
    linarith
  exact ⟨t₀, interior_maximal hUS hUo ht₀U⟩

end MattilaSjolin
