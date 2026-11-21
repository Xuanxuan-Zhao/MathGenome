import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.Corner
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaEvaluations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

universe u v

namespace RM03.Morita

/-- An idempotent is full when the two-sided ideal it generates is the whole ring. -/
def IsFull {R : Type u} [Ring R] (e : Idempotent R) : Prop :=
  TwoSidedIdeal.span ({e.val} : Set R) = ⊤

namespace FullGeneratorSpec

def fullIffSumType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    IsFull e ↔ ∃ (n : ℕ) (r s : Fin n → R), (∑ i, r i * e.val * s i) = 1

def generatorIffFullType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    P103.Morita.IsGenerator R (rightIdeal e) ↔ IsFull e

/-- Every right module, at an independent universe level, is a quotient of a sum of copies of eR. -/
def fullQuotientsType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R), IsFull e →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
      ∃ (J : Type (max u v)) (f : (J →₀ rightIdeal e) →ₗ[Rᵐᵒᵖ] M),
        Function.Surjective f

end FullGeneratorSpec
end RM03.Morita
