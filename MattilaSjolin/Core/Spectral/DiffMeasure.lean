import MattilaSjolin.Core.Defs

/-! Step 4, part S3: the difference measure `ρ = (μ × μ)_*(x, y ↦ x - y)`. Its Fourier transform is
`|μ̂|²`, and integrals against the distance measure are integrals of radial functions against `ρ`. -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal

namespace MattilaSjolin

variable {d : ℕ}

/-- The difference measure `ρ = (μ × μ)_*(x, y ↦ x - y)`. -/
noncomputable def diffMeasure (μ : Measure (Space d)) : Measure (Space d) :=
  (μ.prod μ).map (fun z => z.1 - z.2)

instance (μ : Measure (Space d)) [IsProbabilityMeasure μ] : IsProbabilityMeasure (diffMeasure μ) := by
  unfold diffMeasure
  infer_instance

lemma diffMeasure_eq_conv (μ : Measure (Space d)) [IsProbabilityMeasure μ] :
    diffMeasure μ = μ ∗ μ.map (fun x => -x) := by
  have h : μ.prod (μ.map (fun x => -x)) = (μ.prod μ).map (Prod.map id (fun x => -x)) := by
    have := Measure.map_prod_map μ μ measurable_id measurable_neg
    rwa [Measure.map_id] at this
  rw [diffMeasure, Measure.conv, h, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- `ρ̂ = |μ̂|²`. -/
theorem sourceFourier_diffMeasure (μ : Measure (Space d)) [IsProbabilityMeasure μ] (ξ : Space d) :
    sourceFourier (diffMeasure μ) ξ = ((‖sourceFourier μ ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [diffMeasure_eq_conv, sourceFourier_difference]
  push_cast
  rfl

/-- `∫ φ dν = ∫ φ(|z|) dρ`. -/
theorem integral_distMeasure_eq_diffMeasure (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ t, φ t ∂distMeasure μ = ∫ z, φ ‖z‖ ∂diffMeasure μ := by
  rw [distMeasure, diffMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable,
    integral_map (by fun_prop)
      (show Continuous (fun z : Space d => φ ‖z‖) by fun_prop).aestronglyMeasurable]
  simp only [dist_eq_norm]

end MattilaSjolin
