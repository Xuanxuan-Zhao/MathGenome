import Mathlib.Algebra.Module.FinitePresentation

/-! Finite-presentation assertions of paper.tex, lines 331–355.
All rings are associative and unital; neither commutativity nor nontriviality
is assumed. Finite powers include rank zero. For finite index sets these powers
are the finite-support free modules of Chapter 1. A cokernel is represented by
the quotient by the range. Right modules use the source's opposite-ring convention.
-/

universe u v w

namespace P103.Specs.Ch02.FinitePresentation

/-- The kernel criterion for existence of a finite free cover. -/
def finite_free_cover_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M ↔
      ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M),
        Function.Surjective f ∧ (LinearMap.ker f).FG

/-- The source definition by a right exact sequence of finite free modules. -/
def finite_free_presentation_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M ↔
      ∃ (n m : ℕ) (f : (Fin n → R) →ₗ[R] M)
        (g : (Fin m → R) →ₗ[R] (Fin n → R)),
        Function.Surjective f ∧ Function.Exact g f

/-- Explicit bridge from cokernels of finite free maps to the library predicate. -/
def finite_free_cokernel_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M ↔
      ∃ (n m : ℕ) (g : (Fin m → R) →ₗ[R] (Fin n → R)),
        Nonempty (((Fin n → R) ⧸ LinearMap.range g) ≃ₗ[R] M)

/-- Independence of the cover; in fact every finitely generated source suffices. -/
def kernel_finitely_generatedType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M →
      ∀ (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P]
        (f : P →ₗ[R] M), Function.Surjective f → (LinearMap.ker f).FG

/-- The kernel criterion for existence of a finite free cover. Right-module version. -/
def right_finite_free_cover_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    Module.FinitePresentation Rᵐᵒᵖ M ↔
      ∃ (n : ℕ) (f : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
        Function.Surjective f ∧ (LinearMap.ker f).FG

/-- The source definition by a right exact sequence of finite free modules. Right-module version. -/
def right_finite_free_presentation_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    Module.FinitePresentation Rᵐᵒᵖ M ↔
      ∃ (n m : ℕ) (f : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M)
        (g : (Fin m → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)),
        Function.Surjective f ∧ Function.Exact g f

/-- Explicit bridge from cokernels of finite free maps to the library predicate. Right-module version. -/
def right_finite_free_cokernel_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    Module.FinitePresentation Rᵐᵒᵖ M ↔
      ∃ (n m : ℕ) (g : (Fin m → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)),
        Nonempty (((Fin n → Rᵐᵒᵖ) ⧸ LinearMap.range g) ≃ₗ[Rᵐᵒᵖ] M)

/-- Independence of the cover; in fact every finitely generated source suffices. Right-module version. -/
def right_kernel_finitely_generatedType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    Module.FinitePresentation Rᵐᵒᵖ M →
      ∀ (P : Type w) [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P]
        (f : P →ₗ[Rᵐᵒᵖ] M), Function.Surjective f → (LinearMap.ker f).FG

/-- Zero modules are finitely presented, and a rank-zero free cover exists
exactly when its target is zero. No nonzero-ring assumption is imposed. -/
def boundary_casesType : Prop :=
  (∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M], Module.FinitePresentation R M) ∧
  (∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (f : (Fin 0 → R) →ₗ[R] M), Function.Surjective f ↔ Subsingleton M)

end P103.Specs.Ch02.FinitePresentation
