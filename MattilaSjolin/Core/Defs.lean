import MattilaSjolin.SphereDecay
import OAI.MeasureTheory.Falconer.Measures.FrostmanDischarge
import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy
import OAI.MeasureTheory.Falconer.Geometry.EuclideanRieszEnergy

/-! Definitions shared by the core argument (see `BLUEPRINT.md`). -/

open MeasureTheory Set Filter Topology OAI.Falconer OAI.PlanarFalconer
open scoped ENNReal NNReal

namespace MattilaSjolin

variable {d : ℕ}

/-- The decay exponent `(d-1)/2`. -/
noncomputable abbrev decayExp (d : ℕ) : ℝ := ((d : ℝ) - 1) / 2

/-- The energy weight `w(ξ) = |μ̂(ξ)|² (1 + |ξ|)^{-(d-1)/2}`. -/
noncomputable def energyWeight (μ : Measure (Space d)) (ξ : Space d) : ℝ :=
  ‖sourceFourier μ ξ‖ ^ 2 * (1 + ‖ξ‖) ^ (-decayExp d)

/-- The distance measure `ν = (μ × μ)_*(x, y ↦ |x - y|)`. -/
noncomputable def distMeasure (μ : Measure (Space d)) : Measure ℝ :=
  (μ.prod μ).map (fun z => dist z.1 z.2)

/-- The density `f(t) = t^{d-1} ∫ |μ̂(ξ)|² σ̌(tξ) dξ`. -/
noncomputable def distDensity (μ : Measure (Space d)) (t : ℝ) : ℂ :=
  ((t ^ (d - 1) : ℝ) : ℂ) * ∫ ξ : Space d, ((‖sourceFourier μ ξ‖ ^ 2 : ℝ) : ℂ) * sphereCheck d (t • ξ)

end MattilaSjolin
