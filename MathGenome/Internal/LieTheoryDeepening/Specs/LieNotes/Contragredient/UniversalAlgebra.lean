import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.Presentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.TriangularGrading

namespace Specs.LieNotes.Contragredient.UniversalAlgebra

open CartanData Presentation TriangularGrading
open scoped Classical

universe u v w

/-- The universal Lie algebra of a complex Cartan realization has free positive and negative
sides, a triangular decomposition, and the root-lattice grading by adjoint weight spaces. -/
def UniversalAlgebraBeforeQuotient : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v}
    [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), IsGeneralizedCartanMatrix A →
    Relations R (cartan R) (e R) (f R) ∧
    LieSubalgebra.lieSpan ℂ (Algebra R)
        (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) = ⊤ ∧
    (∀ {L : Type w} [LieRing L] [LieAlgebra ℂ L] (C : H →ₗ[ℂ] L) (E F : I → L),
      Relations R C E F → ∃! φ, Extends R C E F φ) ∧
    Function.Injective (cartan R) ∧
    (∃ S : (negative R × H × positive R) ≃ₗ[ℂ] Algebra R,
      S.toLinearMap = triangularAdd R) ∧
    (∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ negative R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = f R i) ∧
    (∃ ψ : FreeLieAlgebra ℂ I ≃ₗ⁅ℂ⁆ positive R,
      ∀ i, (ψ (FreeLieAlgebra.of ℂ i) : Algebra R) = e R i) ∧
    DirectSum.IsInternal (grade R) ∧
    (∀ h, cartan R h ∈ grade R 0) ∧
    (∀ i, e R i ∈ grade R (simpleDegree i)) ∧
    (∀ i, f R i ∈ grade R (-simpleDegree i)) ∧
    (∀ {q p : Q I} {x y : Algebra R},
      x ∈ grade R q → y ∈ grade R p → ⁅x, y⁆ ∈ grade R (q + p)) ∧
    (∀ (q : Q I) (x : Algebra R),
      x ∈ grade R q ↔ ∀ h : H, ⁅cartan R h, x⁆ = R.rootWeight q h • x) ∧
    grade R 0 = (cartan R).range ∧
    (⨆ q, ⨆ (_ : NegativeDegree q), grade R q) = (negative R).toSubmodule ∧
    (⨆ q, ⨆ (_ : PositiveDegree q), grade R q) = (positive R).toSubmodule

end Specs.LieNotes.Contragredient.UniversalAlgebra
