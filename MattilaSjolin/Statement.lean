import Mathlib

/-!
# The Mattila–Sjölin theorem: statement

P. Mattila, P. Sjölin, *Regularity of distance measures and sets*, Math. Nachr. 204 (1999),
157–162: if `E ⊆ ℝ^d` (`d ≥ 2`) is compact with `dimH E > (d+1)/2`, then the distance set
`Δ(E) = {‖x - y‖ : x, y ∈ E}` has nonempty interior.

The proposition below is identical to `DistanceSimilarity.MattilaSjolinStatement` in
`github.com/haraldschilly/math-distance-set-similarity`.
-/

open scoped ENNReal

namespace MattilaSjolin

/-- The Mattila–Sjölin theorem, compact case. -/
def MattilaSjolinStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    ((d : ℝ≥0∞) + 1) / 2 < dimH E →
      (interior {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty

end MattilaSjolin
