import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.SerreRelations

/-! The Serre relations and local nilpotence on the Cartan-disjoint quotient. -/

namespace Specs.LieNotes.Contragredient.AdjointNilpotence

open CartanData

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse the two Serre identities on the same canonical quotient.
def PositiveSerre : Prop := SerreRelations.PositiveSerre.{u, v}

def NegativeSerre : Prop := SerreRelations.NegativeSerre.{u, v}

/-- Every vector is killed by some power of the adjoint of a positive simple generator. -/
def AdELocallyNilpotent : Prop :=
  ∀ {I : Type u} [Finite I] {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I) (x : CartanQuotient.Algebra R),
      ∃ n : ℕ, (LieAlgebra.ad ℂ (CartanQuotient.Algebra R) (CartanQuotient.e R i) ^ n) x = 0

/-- Every vector is killed by some power of the adjoint of a negative simple generator. -/
def AdFLocallyNilpotent : Prop :=
  ∀ {I : Type u} [Finite I] {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I) (x : CartanQuotient.Algebra R),
      ∃ n : ℕ, (LieAlgebra.ad ℂ (CartanQuotient.Algebra R) (CartanQuotient.f R i) ^ n) x = 0

end Specs.LieNotes.Contragredient.AdjointNilpotence
