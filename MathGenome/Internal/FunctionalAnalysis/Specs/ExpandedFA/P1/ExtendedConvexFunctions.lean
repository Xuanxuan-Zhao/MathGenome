import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Order.WithBot

/-! Independent specifications for paper.tex, lines 1264–1274.
`WithTop ℝ` is precisely the real numbers with +∞ adjoined; it contains no −∞.
The domain topology is arbitrary, so the interface applies both to normed spaces
and to Hausdorff locally convex spaces without replacing their given topology. -/
namespace ExpandedFA.P1.ExtendedConvexFunctions

abbrev ExtendedFunction (E : Type*) := E → WithTop ℝ

namespace Spec

/-- The finite domain, retaining functions that take +∞ elsewhere. -/
def finiteDomainType := ∀ (E : Type*), ExtendedFunction E → Set E
def finiteDomainValue : finiteDomainType := fun _ φ => {x | φ x ≠ ⊤}

def ProperType := ∀ (E : Type*), ExtendedFunction E → Prop
def ProperValue : ProperType := fun E φ => (finiteDomainValue E φ).Nonempty

/-- Only real levels occur in the manuscript's lower semicontinuity convention. -/
def LowerSemicontinuousType :=
  ∀ (E : Type*) [TopologicalSpace E], ExtendedFunction E → Prop
def LowerSemicontinuousValue : LowerSemicontinuousType :=
  fun _ _ φ => ∀ r : ℝ, IsClosed {x | φ x ≤ (r : WithTop ℝ)}

/-- The second coordinate is real, not extended-real. -/
def realEpigraphType := ∀ (E : Type*), ExtendedFunction E → Set (E × ℝ)
def realEpigraphValue : realEpigraphType := fun _ φ => {p | φ p.1 ≤ (p.2 : WithTop ℝ)}

/-- The ordinary convex inequality on finite endpoints, including weights zero
and one. The finite right side also ensures convexity of the finite domain. -/
def ExtendedConvexType :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E], ExtendedFunction E → Prop
def ExtendedConvexValue : ExtendedConvexType := fun _ _ _ φ =>
  ∀ (x y : _) (r s a b : ℝ), φ x = (r : WithTop ℝ) → φ y = (s : WithTop ℝ) →
    0 ≤ a → 0 ≤ b → a + b = 1 →
    φ (a • x + b • y) ≤ ((a * r + b * s : ℝ) : WithTop ℝ)

def ProperIffFiniteValue : Prop :=
  ∀ (E : Type*) (φ : ExtendedFunction E),
    ProperValue E φ ↔ ∃ (x : E) (r : ℝ), φ x = (r : WithTop ℝ)

def LowerSemicontinuousIffClosedEpigraph : Prop :=
  ∀ (E : Type*) [TopologicalSpace E] (φ : ExtendedFunction E),
    LowerSemicontinuousValue E φ ↔ IsClosed (realEpigraphValue E φ)

def ConvexIffConvexEpigraph : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] (φ : ExtendedFunction E),
    ExtendedConvexValue E φ ↔ Convex ℝ (realEpigraphValue E φ)

/-- The finite domain of a convex extended function is convex, even when empty. -/
def ConvexFiniteDomain : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] (φ : ExtendedFunction E),
    ExtendedConvexValue E φ → Convex ℝ (finiteDomainValue E φ)

end Spec
end ExpandedFA.P1.ExtendedConvexFunctions
