import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.RealTietze
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-!
Independent statements for paper.tex, `d10:07:finite-coordinate-extension`.
Finite real powers carry the canonical product topology. Interval factors
are real subsets with the subspace topology: `OrdConnected` expresses that
all points between two members belong to the set. Together with closedness
and nonemptiness this describes the closed intervals, including singletons,
closed rays, and the whole real line. No T1 assumption is imposed on X.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch07.CoordinateExtensions

/-- Every finite real power is an extension target, including n = 0. -/
def finite_coordinate_extension : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ (A : Set X), IsClosed A → ∀ (n : ℕ) (f : A → (Fin n → ℝ)),
      Continuous f →
        ∃ F : X → (Fin n → ℝ), Continuous F ∧ ∀ x : A, F x = f x

/-- Extension into any indexed product of nonempty closed real intervals.
There is no nonemptiness assumption on A or on the index type. -/
def closed_interval_product_extension : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ (A : Set X), IsClosed A → ∀ {I : Type v} (J : I → Set ℝ),
      (∀ i, IsClosed (J i)) → (∀ i, OrdConnected (J i)) →
      (∀ i, (J i).Nonempty) →
      ∀ (f : A → (∀ i, J i)), Continuous f →
        ∃ F : X → (∀ i, J i), Continuous F ∧ ∀ x : A, F x = f x

end Specs.D10Topology.Ch07.CoordinateExtensions
