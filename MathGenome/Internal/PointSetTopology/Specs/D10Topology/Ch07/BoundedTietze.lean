import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:07:approximate-extension and
d10:07:tietze-bounded. Intervals and the closed subspace have their canonical
subtype topologies. Normality does not include T1. Neither the closed subset
nor the ambient space is required to be nonempty, and a singleton target
interval is allowed in bounded Tietze.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.BoundedTietze

/-- A continuous approximation with the source's two quantitative bounds. -/
def approximate_extension : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ (A : Set X), IsClosed A → ∀ (a : ℝ), 0 < a →
      ∀ (h : A → Icc (-a) a), Continuous h →
        ∃ g : X → Icc (-(a / 3)) (a / 3), Continuous g ∧
          ∀ x : A, |(h x : ℝ) - (g x : ℝ)| ≤ 2 * a / 3

/-- Every continuous map to a nonempty finite closed real interval extends
with the same target interval and the same values on the closed subspace. -/
def tietze_bounded : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], NormalSpace X →
    ∀ (A : Set X), IsClosed A → ∀ (a b : ℝ), a ≤ b →
      ∀ (f : A → Icc a b), Continuous f →
        ∃ F : X → Icc a b, Continuous F ∧ ∀ x : A, F x = f x

end Specs.D10Topology.Ch07.BoundedTietze
