import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

noncomputable section

namespace Specs.CommutativeAlgebraNotes.OrderedValuationGroups

universe u v

/-- The source uses the additive order, so integral elements have nonnegative value. -/
abbrev valueGroup {K : Type u} [Field K] (V : ValuationSubring K) : Type u :=
  (Additive (V.ValueGroupˣ))ᵒᵈ

/-- The additive version of the intrinsic valuation, restricted to the field's units. -/
abbrev value {K : Type u} [Field K] (V : ValuationSubring K) :
    Additive Kˣ →+ valueGroup V :=
  MonoidHom.toAdditive (Units.map V.valuation.toMonoidWithZeroHom.toMonoidHom)

abbrev fieldUnitImage {K : Type u} [Field K] (V : ValuationSubring K) : Subgroup Kˣ :=
  (Units.map V.toSubring.subtype.toMonoidHom).range

/-- The inequality for a homomorphism defined on nonzero elements only. -/
def AddValuationInequality {K : Type u} [Field K] {Γ : Type v} [AddCommGroup Γ]
    [LinearOrder Γ] (f : Additive Kˣ →+ Γ) : Prop :=
  ∀ (a b : Kˣ) (h : (a : K) + (b : K) ≠ 0),
    min (f (Additive.ofMul a)) (f (Additive.ofMul b)) ≤
      f (Additive.ofMul (Units.mk0 ((a : K) + (b : K)) h))

def ValueGroupType :=
  ∀ {K : Type u} [Field K], ValuationSubring K → Type u

def ValueType :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K), Additive Kˣ →+ valueGroup V

def ValueSurjective : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K), Function.Surjective (value V)

def QuotientIdentification : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    ∃ e : Additive (Kˣ ⧸ fieldUnitImage V) ≃+ valueGroup V,
      ∀ a : Kˣ, e (Additive.ofMul (QuotientGroup.mk' (fieldUnitImage V) a)) =
        value V (Additive.ofMul a)

def ValueOrder : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (x y z : valueGroup V),
    (x ≤ y ∨ y ≤ x) ∧ (x + z ≤ y + z ↔ x ≤ y)

def Comparison : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (a b : Kˣ),
    value V (Additive.ofMul b) ≤ value V (Additive.ofMul a) ↔ (a : K) / (b : K) ∈ V

def SumInequality : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K), AddValuationInequality (value V)

def SumEquality : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K) (a b : Kˣ)
    (h : (a : K) + (b : K) ≠ 0),
    value V (Additive.ofMul a) ≠ value V (Additive.ofMul b) →
    value V (Additive.ofMul (Units.mk0 ((a : K) + (b : K)) h)) =
      min (value V (Additive.ofMul a)) (value V (Additive.ofMul b))

def Converse : Prop :=
  ∀ {K : Type u} [Field K] {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (f : Additive Kˣ →+ Γ), AddValuationInequality f →
    ∃ V : ValuationSubring K,
      (∀ x : K, x ∈ V ↔ x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ f (Additive.ofMul (Units.mk0 x h))) ∧
      ∃ e : valueGroup V ≃+o f.range, ∀ a : Additive Kˣ, e (value V a) = f.rangeRestrict a

end Specs.CommutativeAlgebraNotes.OrderedValuationGroups
