import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! The bounded-sequence conclusion of `d04:01:coordinate-estimates`.
The dimension ranges over all natural numbers, including zero. Boundedness
means one real upper bound for the Euclidean norms of all terms. -/

open Filter Topology

namespace Specs.D04.C01.BoundedSubsequence
open Specs.D04.C01.EuclideanInterfaces.Model

def bounded_subsequenceType : Prop :=
  ∀ {n : ℕ} (x : ℕ → E n), (∃ B : ℝ, ∀ k, ‖x k‖ ≤ B) →
    ∃ (s : ℕ → ℕ) (a : E n), StrictMono s ∧
      Tendsto (x ∘ s) atTop (𝓝 a)

end Specs.D04.C01.BoundedSubsequence
