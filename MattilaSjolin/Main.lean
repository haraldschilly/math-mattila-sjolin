import MattilaSjolin.Core
import MattilaSjolin.Circle.Decay

/-!
# The Mattila–Sjölin theorem

If `E ⊆ ℝ^d` (`d ≥ 2`) is compact with `dimH E > (d+1)/2`, then the distance set
`Δ(E) = {‖x - y‖ : x, y ∈ E}` has nonempty interior.
-/

namespace MattilaSjolin

/-- **The Mattila–Sjölin theorem.** -/
theorem mattilaSjolin : MattilaSjolinStatement := by
  intro d hd E hE hdim
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | h3
  · exact mattilaSjolin_of_sphereDecay le_rfl sphereDecay_two E hE hdim
  · exact mattilaSjolin_of_three_le h3 E hE hdim

end MattilaSjolin
