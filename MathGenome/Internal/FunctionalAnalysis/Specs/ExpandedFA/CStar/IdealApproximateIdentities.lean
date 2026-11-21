import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient

/-! Closed complex two-sided ideals, without any initial star-closure assumption.
The index consists of finite subsets of the ideal and positive real tolerances;
its order increases the finite set and decreases the tolerance. -/
noncomputable section
namespace ExpandedFA.CStar.IdealApproximateIdentities.Spec
universe u
open Filter Topology

/-- Bundle closedness with the existing complex-linear two-sided ideal interface. -/
structure ClosedTwoSidedIdeal (A : Type u) [NonUnitalCStarAlgebra A]
    extends Submodule ℂ A where
  isClosed : IsClosed (toSubmodule : Set A)
  isTwoSided : Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient.IsTwoSidedIdeal toSubmodule

theorem ClosedTwoSidedIdeal.mul_mem_left {A : Type u} [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) (a x : A) (hx : x ∈ I.toSubmodule) :
    a * x ∈ I.toSubmodule := I.isTwoSided.1 a x hx

theorem ClosedTwoSidedIdeal.mul_mem_right {A : Type u} [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) (x a : A) (hx : x ∈ I.toSubmodule) :
    x * a ∈ I.toSubmodule := I.isTwoSided.2 x a hx

instance {A : Type u} [NonUnitalCStarAlgebra A] :
    SetLike (ClosedTwoSidedIdeal A) A where
  coe I := I.toSubmodule
  coe_injective := by
    intro I J h
    cases I; cases J
    congr
    exact SetLike.coe_injective h

@[simp] theorem mem_toSubmodule {A : Type u} [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) (a : A) : a ∈ I.toSubmodule ↔ a ∈ I := Iff.rfl

abbrev ApproximationIndex {A : Type u} [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) := Finset I × OrderDual (Set.Ioi (0 : ℝ))

def StarInvariant : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) (a : A), a ∈ I → star a ∈ I

def FiniteApproximation : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A) (F : Finset I) (ε : ℝ), 0 < ε →
    ∃ e : A, e ∈ I ∧ Conventions.Spec.PositiveValue A e ∧ ‖e‖ ≤ 1 ∧
      ∀ a ∈ F, ‖e * (a : A) - a‖ < ε ∧ ‖(a : A) * e - a‖ < ε

def ApproximateIdentity : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A), ∃ e : ApproximationIndex I → A,
    (∀ d, e d ∈ I ∧ Conventions.Spec.PositiveValue A (e d) ∧ ‖e d‖ ≤ 1) ∧
    (∀ d, ∀ (a : I), a ∈ d.1 →
      ‖e d * (a : A) - a‖ < ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ) ∧
      ‖(a : A) * e d - a‖ < ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ)) ∧
    ∀ a : I, Tendsto (fun d => e d * (a : A)) atTop (𝓝 (a : A)) ∧
      Tendsto (fun d => (a : A) * e d) atTop (𝓝 (a : A))

end ExpandedFA.CStar.IdealApproximateIdentities.Spec
