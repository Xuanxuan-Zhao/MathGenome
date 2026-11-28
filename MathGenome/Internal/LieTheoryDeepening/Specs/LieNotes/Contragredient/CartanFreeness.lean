import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.Presentation

namespace Specs.LieNotes.Contragredient.CartanFreeness

open CartanData Presentation

universe u v

/-- The Cartan space injects into the universal algebra before the Cartan-disjoint quotient. -/
def CartanInjective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Function.Injective (cartan R)

/-- The negative Lie subalgebra is free on its given simple generators. -/
def NegativeIsFree : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    ∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ negative R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = f R i

/-- The positive Lie subalgebra is free on its given simple generators. -/
def PositiveIsFree : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    ∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ positive R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = e R i

end Specs.LieNotes.Contragredient.CartanFreeness
