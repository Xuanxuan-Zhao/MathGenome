import Mathlib.Algebra.Module.Projective
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.FreeModules
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.SplitSequences
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.HomTensorExactness

/-! Projective modules: paper.tex, Theorem 2.1, lines 284–301.
Rings need not be commutative or nonzero. All free bases are arbitrary types.
The extra universe `w` allows the test modules and free bases to be arbitrarily
large relative to R and P; no finiteness or smallness assumption is imposed.
Right modules mean modules over the opposite ring, as in the source conventions.
Hom is an abelian group, rather than an R-module over a noncommutative ring. -/

universe u v w x

namespace P103.Specs.Ch02.Projective

open P103.Ch01 P103.HomTensorExactness

variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]

/-- Every map out of P lifts along every surjective linear map. -/
def LiftingProperty : Prop :=
  ∀ (M N : Type (max u v w)) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
    Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g

/-- Every short exact sequence with last nonzero term P has a linear section. -/
def SplittingProperty : Prop :=
  ∀ (A B : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (i : A →ₗ[R] B) (p : B →ₗ[R] P),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∃ s : P →ₗ[R] B, p.comp s = LinearMap.id

/-- An actual direct sum decomposition of a free module with P as a summand.
A product of two modules represents their finite direct sum. -/
def FreeSummand : Prop :=
  ∃ (X Q : Type (max u v w)) (_ : AddCommGroup Q) (_ : Module R Q),
    Nonempty ((P × Q) ≃ₗ[R] FreeModule R X)

/-- Exactness of Hom on every short exact sequence, including both endpoint
conditions. This is the usual exactness of the covariant additive functor. -/
def HomExact : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    Function.Injective (post (P := P) i) ∧
      Function.Exact (post (P := P) i) (post (P := P) p) ∧
      Function.Surjective (post (P := P) p)

def projective_iff_liftingType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P],
    Module.Projective R P ↔ LiftingProperty.{u,v,w} R P

def projective_iff_splittingType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P],
    Module.Projective R P ↔ SplittingProperty.{u,v,w} R P

def projective_iff_freeSummandType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P],
    Module.Projective R P ↔ FreeSummand.{u,v,w} R P

def projective_iff_homExactType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P],
    Module.Projective R P ↔ HomExact.{u,v,w} R P

/-- Also state lifting with independently sized source and target modules. -/
def liftingType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Projective R P] (M : Type w) (N : Type x)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (g : P →ₗ[R] N),
    Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g

def free_projectiveType : Prop :=
  ∀ (R : Type u) (X : Type v) [Ring R], Module.Projective R (FreeModule R X)

/-- Every retract of a free module of any rank is projective. -/
def free_retract_projectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) (X : Type w)
    [AddCommGroup P] [Module R P]
    (i : P →ₗ[R] FreeModule R X) (r : FreeModule R X →ₗ[R] P),
    r.comp i = LinearMap.id → Module.Projective R P

def right_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    (Module.Projective Rᵐᵒᵖ P ↔ LiftingProperty.{u,v,w} Rᵐᵒᵖ P) ∧
    (Module.Projective Rᵐᵒᵖ P ↔ SplittingProperty.{u,v,w} Rᵐᵒᵖ P) ∧
    (Module.Projective Rᵐᵒᵖ P ↔ FreeSummand.{u,v,w} Rᵐᵒᵖ P) ∧
    (Module.Projective Rᵐᵒᵖ P ↔ HomExact.{u,v,w} Rᵐᵒᵖ P)

end P103.Specs.Ch02.Projective
