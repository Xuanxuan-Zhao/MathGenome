import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

/-!
Independent statements for K03.16.stone_real (paper.tex:3920–3930).
`K` has the subspace topology inherited from ℝ. `CompactSpace K` is
compactness of this subtype, equivalently `IsCompact K`. `Subalgebra ℝ`
contains all real constants through its algebra map. Separation is written
out pointwise, rather than assuming a density or approximation certificate.
The canonical norm on `C(K, ℝ)` is the sup norm, including norm zero on
empty K. There is no nonemptiness or two-point hypothesis on K, so the
empty and singleton cases are included. The nonunital, no-common-zero
variant in the following source paragraph is allocated separately.
-/
namespace Specs.SingleVariableAnalysis.Ch16.StoneReal

open scoped Topology

/-- The uniform closure is the whole continuous-function algebra. -/
def closureEqTop : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      A.topologicalClosure = ⊤

/-- The same conclusion with closure of the underlying set. -/
def uniformClosureEqUniv : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      closure (A : Set C(K, ℝ)) = Set.univ

/-- Arbitrary positive accuracy in the sup norm. -/
def uniformApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
        ∃ g ∈ A, ‖f - g‖ < ε

/-- Explicit uniform error at every point of the original real subset. -/
def pointwiseApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
        ∃ g ∈ A, ∀ x : K, |f x - g x| < ε

end Specs.SingleVariableAnalysis.Ch16.StoneReal
