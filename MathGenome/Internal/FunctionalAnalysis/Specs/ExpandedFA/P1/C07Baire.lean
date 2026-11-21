import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07Category
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Independent specification of Baire's complete-metric theorem

Theorem `fa2:p1:c07:baire`, paper.tex:1373–1379. Completeness refers
to the uniform structure of the given metric. The first assertion permits
the empty space; nonemptiness is required only for the closed-cover consequence.
The category predicates are those of the shared Chapter 7 specification.
-/

open Set TopologicalSpace

universe u v

namespace Specs.ExpandedFA.P1.C07Baire

/-- Every complete metric space is Baire, including the empty space. -/
def completeMetricBaire : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X], BaireSpace X

/-- Every countable closed cover of a nonempty complete metric space has
a member with nonempty interior. Finite and empty index types are allowed. -/
def closedCoverInterior : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type v} [Countable ι] (F : ι → Set X),
    (∀ i, IsClosed (F i)) → (⋃ i, F i) = univ →
    ∃ i, (interior (F i)).Nonempty

/-- Nonempty open sets are not meagre in the ambient complete metric space. -/
def openNonmeagre : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] (O : Set X),
    IsOpen O → O.Nonempty → ¬ IsMeagre O

end Specs.ExpandedFA.P1.C07Baire
