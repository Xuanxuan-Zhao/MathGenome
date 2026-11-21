import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements of `chapters/01.tex`, `d04:01:lebesgue-number`.
The cover consists of subsets relatively open in K, using the shared
Euclidean objects. The index type, K, and the dimension may all be empty.
Only the tested subset S is required to be nonempty. -/

namespace Specs.D04.C01.LebesgueNumber
open Set
open Specs.D04.C01.EuclideanInterfaces.Model

def lebesgue_numberType : Prop :=
  ∀ {n : ℕ} {ι : Type*} (K : Set (E n)) (U : ι → Set (E n)),
    Compact K → (∀ i, RelativelyOpen K (U i)) → K ⊆ ⋃ i, U i →
    ∃ δ > 0, ∀ S : Set (E n), S.Nonempty → S ⊆ K →
      Metric.diam S < δ → ∃ i, S ⊆ U i

/-- The same Lebesgue number also controls all relative balls of radius
strictly between zero and δ/2, at every center in K. -/
def lebesgue_number_and_relative_ballsType : Prop :=
  ∀ {n : ℕ} {ι : Type*} (K : Set (E n)) (U : ι → Set (E n)),
    Compact K → (∀ i, RelativelyOpen K (U i)) → K ⊆ ⋃ i, U i →
    ∃ δ > 0,
      (∀ S : Set (E n), S.Nonempty → S ⊆ K →
        Metric.diam S < δ → ∃ i, S ⊆ U i) ∧
      (∀ r : ℝ, 0 < r → r < δ / 2 →
        ∀ x ∈ K, ∃ i, relativeBall K x r ⊆ U i)

end Specs.D04.C01.LebesgueNumber
