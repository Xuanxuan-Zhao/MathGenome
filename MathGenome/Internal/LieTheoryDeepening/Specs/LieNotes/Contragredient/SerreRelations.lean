import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient

/-! The Serre relations in the canonical Cartan-disjoint quotient. -/

namespace Specs.LieNotes.Contragredient.SerreRelations

open CartanData

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The integral Serre exponent is positive for distinct simple indices. -/
def ExponentPositive : Prop :=
  ∀ {I : Type u} [Finite I] {A : Matrix I I ℤ},
    IsGeneralizedCartanMatrix A → ∀ {i j : I}, i ≠ j → 0 < (1 - A i j).toNat

/-- The positive simple generators satisfy the Serre relations. -/
def PositiveSerre : Prop :=
  ∀ {I : Type u} [Finite I] {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) {i j : I}, i ≠ j →
      (LieAlgebra.ad ℂ (CartanQuotient.Algebra R) (CartanQuotient.e R i) ^
        (1 - A i j).toNat) (CartanQuotient.e R j) = 0

/-- The negative simple generators satisfy the Serre relations. -/
def NegativeSerre : Prop :=
  ∀ {I : Type u} [Finite I] {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) {i j : I}, i ≠ j →
      (LieAlgebra.ad ℂ (CartanQuotient.Algebra R) (CartanQuotient.f R i) ^
        (1 - A i j).toNat) (CartanQuotient.f R j) = 0

end Specs.LieNotes.Contragredient.SerreRelations
