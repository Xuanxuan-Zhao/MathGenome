import Mathlib.Algebra.Module.Injective

/-! The enough-injectives assertion of paper.tex 361–383.
Rings are arbitrary associative unital rings, including the zero ring.
The module and ring may have different universe levels. Right modules are
left modules over the opposite ring, as in the source's global conventions.
-/

namespace P103.Specs.Ch02.EnoughInjectives

universe u v

/-- A linear embedding into an injective module, with the ambient module
in a universe large enough for both the ring and the original module.
The group and action structures on the witness are explicitly quantified. -/
def EmbedsInInjective (R : Type u) (M : Type v) [Ring R]
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ (E : Type (max u v)) (_ : AddCommGroup E) (_ : Module R E)
    (i : M →ₗ[R] E), Function.Injective i ∧ Module.Injective R E

def leftEmbeddingType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    EmbedsInInjective R M

def rightEmbeddingType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M],
    EmbedsInInjective Rᵐᵒᵖ M

end P103.Specs.Ch02.EnoughInjectives
