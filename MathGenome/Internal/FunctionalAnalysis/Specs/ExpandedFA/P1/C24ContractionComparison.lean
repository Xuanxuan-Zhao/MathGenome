import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import Mathlib.Logic.Function.Iterate

/-! Independent statement of `paper.tex`, Proposition `fa2:p1:c24:contraction-comparison` (lines 5159–5170).
The self-map and its iterates live on the closed-set subtype. Convergence and
all norm estimates below are stated in the original ambient Banach space.
No convexity or compactness hypothesis is imposed. Completeness is stated
using the accepted sequential Banach-space definition from Chapter 1.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C24ContractionComparison.Spec

universe u v

/-- A contraction on a nonempty closed subset of a real or complex Banach space
has a unique fixed point, attracts every orbit, and satisfies the stated
geometric error bound for every natural number, including zero. -/
def contractionComparison_type : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C01Banach.Spec.IsBanachSpaceValue E → ∀ (D : Set E),
    D.Nonempty → IsClosed D →
    ∀ (q : ℝ), 0 ≤ q → q < 1 →
    ∀ (T : D → D),
    (∀ x y : D, ‖(T x : E) - (T y : E)‖ ≤ q * ‖(x : E) - (y : E)‖) →
    ∃ xstar : D,
      T xstar = xstar ∧
      (∀ y : D, T y = y → y = xstar) ∧
      (∀ x : D, Tendsto (fun n : ℕ => ((T^[n]) x : E)) atTop (𝓝 (xstar : E))) ∧
      (∀ (x : D) (n : ℕ),
        ‖((T^[n]) x : E) - (xstar : E)‖ ≤
          q ^ n / (1 - q) * ‖(T x : E) - (x : E)‖)

end ExpandedFA.P1.C24ContractionComparison.Spec
