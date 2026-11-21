import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-!
Flatness tests and the projectivity consequences of Theorem 2.5, paper.tex
412–444 and 466–483. Rings are arbitrary unital rings, including the zero ring.
The filtered-colimit equivalence is allocated separately to GovorovLazard.

`Flat` tests all right modules in an arbitrary enlarged universe. The additional
universe parameter is unrestricted. Tensor arrows are characterized on elementary
tensors, using the common balanced tensor, without importing its implementation.
Right modules are left modules over the opposite ring, as in the source.
-/

universe u v w

namespace P103.Specs.Ch02.FlatnessTests

open P103.BalancedTensor

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensoring with M preserves every injective map of right modules. -/
def Flat : Prop :=
  ∀ (A B : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] (f : A →ₗ[Rᵐᵒᵖ] B),
    Function.Injective f → ∀ (F : Tensor R A M →+ Tensor R B M),
    (∀ a m, F (tmul R a m) = tmul R (f a) m) → Function.Injective F

/-- Preservation of short exact sequences, including both endpoints. -/
def TensorExact : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
    (i : A →ₗ[Rᵐᵒᵖ] B) (p : B →ₗ[Rᵐᵒᵖ] C),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∀ (F : Tensor R A M →+ Tensor R B M) (G : Tensor R B M →+ Tensor R C M),
    (∀ a m, F (tmul R a m) = tmul R (i a) m) →
    (∀ b m, G (tmul R b m) = tmul R (p b) m) →
    Function.Injective F ∧ Function.Exact F G ∧ Function.Surjective G

/-- It suffices to test inclusions of finitely generated right ideals. -/
def IdealTest : Prop :=
  ∀ I : Submodule Rᵐᵒᵖ R, I.FG →
    ∀ (F : Tensor R I M →+ Tensor R R M),
    (∀ (i : I) m, F (tmul R i m) = tmul R (i : R) m) → Function.Injective F

/-- Simultaneous finite relations. The product order r*s is essential. -/
def FiniteRelations : Prop :=
  ∀ (n k : ℕ) (x : Fin n → M) (r : Fin k → Fin n → R),
    (∀ j, ∑ i, r j i • x i = 0) →
    ∃ (l : ℕ) (y : Fin l → M) (s : Fin n → Fin l → R),
      (∀ i, x i = ∑ a, s i a • y a) ∧
      (∀ j a, ∑ i, r j i * s i a = 0)

/-- The right-module coefficient order, explicitly in R rather than Rᵐᵒᵖ. -/
def RightFiniteRelations (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M] : Prop :=
  ∀ (n k : ℕ) (x : Fin n → M) (r : Fin k → Fin n → R),
    (∀ j, ∑ i, MulOpposite.op (r j i) • x i = 0) →
    ∃ (l : ℕ) (y : Fin l → M) (s : Fin n → Fin l → R),
      (∀ i, x i = ∑ a, MulOpposite.op (s i a) • y a) ∧
      (∀ j a, ∑ i, s i a * r j i = 0)

/-- The original right-module tensor orientation M⊗_R−. -/
def RightFlat (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M] : Prop :=
  ∀ (A B : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B),
    Function.Injective f → ∀ (F : Tensor R M A →+ Tensor R M B),
    (∀ m a, F (tmul R m a) = tmul R m (f a)) → Function.Injective F

/-- Canonical action of the double opposite ring, used when flipping tensors. -/
abbrev doubleOppositeModule (R : Type*) [Ring R] (A : Type*) [AddCommGroup A]
    [Module R A] : Module Rᵐᵒᵖᵐᵒᵖ A :=
  Module.compHom A (RingEquiv.opOp R).symm.toRingHom

/-- The opposite-ring convention agrees with the original right tensor functor. -/
def rightFlat_iff_oppositeType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    RightFlat.{u,v,w} R M ↔ Flat.{u,v,w} Rᵐᵒᵖ M

def flat_iff_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M ↔ TensorExact.{u,v,w} R M

/-- Exactness at the middle without endpoint hypotheses. -/
def flat_preserves_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M →
    ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
      [AddCommGroup C] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
      (i : A →ₗ[Rᵐᵒᵖ] B) (p : B →ₗ[Rᵐᵒᵖ] C), Function.Exact i p →
      ∀ (F : Tensor R A M →+ Tensor R B M) (G : Tensor R B M →+ Tensor R C M),
      (∀ a m, F (tmul R a m) = tmul R (i a) m) →
      (∀ b m, G (tmul R b m) = tmul R (p b) m) → Function.Exact F G

def flat_iff_idealTestType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M ↔ IdealTest R M

def flat_iff_finiteRelationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M ↔ FiniteRelations R M

def projective_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.Projective R M → Flat.{u,v,w} R M

def free_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (X : Type v), Flat.{u,max u v,w} R (X →₀ R)

def finitelyPresented_flat_projectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M → Flat.{u,v,w} R M → Module.Projective R M

/-- Flatness over Rᵐᵒᵖ is the right-module version. The tested right ideals
of Rᵐᵒᵖ are the left ideals of R. Reversing the tensor factors gives M⊗_R−. -/
def right_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    (Flat.{u,v,w} Rᵐᵒᵖ M ↔ TensorExact.{u,v,w} Rᵐᵒᵖ M) ∧
    (Flat.{u,v,w} Rᵐᵒᵖ M ↔ IdealTest Rᵐᵒᵖ M) ∧
    (Flat.{u,v,w} Rᵐᵒᵖ M ↔ RightFiniteRelations R M)

def right_projectivityType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    (Module.Projective Rᵐᵒᵖ M → Flat.{u,v,w} Rᵐᵒᵖ M) ∧
    (Module.FinitePresentation Rᵐᵒᵖ M → Flat.{u,v,w} Rᵐᵒᵖ M →
      Module.Projective Rᵐᵒᵖ M)

/-- Right-module results in the original tensor orientation, with the
opposite-ring ideal test representing left ideals of the original ring. -/
def right_tensor_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    (RightFlat.{u,v,w} R M ↔ TensorExact.{u,v,w} Rᵐᵒᵖ M) ∧
    (RightFlat.{u,v,w} R M ↔ IdealTest Rᵐᵒᵖ M) ∧
    (RightFlat.{u,v,w} R M ↔ RightFiniteRelations R M) ∧
    (Module.Projective Rᵐᵒᵖ M → RightFlat.{u,v,w} R M) ∧
    (Module.FinitePresentation Rᵐᵒᵖ M → RightFlat.{u,v,w} R M →
      Module.Projective Rᵐᵒᵖ M)

/-- Comparison is with Mathlib's flatness predicate on the same module. -/
def commutative_flat_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M ↔ Module.Flat R M

end P103.Specs.Ch02.FlatnessTests
