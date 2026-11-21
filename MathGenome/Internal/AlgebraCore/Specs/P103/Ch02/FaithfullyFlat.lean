import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests

/-!
Proposition 2.6, paper.tex 485–505. No commutativity or nonzero-ring
hypothesis is imposed. Maximal left ideals are coatoms of `Submodule R R`.
The enlarged testing universe is arbitrary, as in the upstream flatness Spec.
The left-module statement is also given in the A ⊗[R] M orientation.
Its opposite-ring transport is made explicit by `left_orientationType`.
-/
universe u v w
namespace P103.Specs.Ch02.FaithfullyFlat
open P103.BalancedTensor P103.Specs.Ch02.FlatnessTests

variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Nonzero modules have nonzero tensor. -/
def Detects : Prop :=
  ∀ (A : Type (max u v w)) [AddCommGroup A] [Module R A],
    Nontrivial A → Nontrivial (Tensor R P A)

/-- No assumption that the original maps form a complex is made. -/
def ReflectsExact : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (F : Tensor R P A →+ Tensor R P B) (G : Tensor R P B →+ Tensor R P C),
    (∀ p a, F (tmul R p a) = tmul R p (f a)) →
    (∀ p b, G (tmul R p b) = tmul R p (g b)) →
    Function.Exact F G → Function.Exact f g

/-- The test is vacuous for the zero ring. Ideals are one-sided. -/
def MaximalTest : Prop :=
  ∀ I : Submodule R R, IsCoatom I → Nontrivial (Tensor R P (R ⧸ I))

/-- Faithfulness on every Hom set. -/
def Faithful : Prop :=
  ∀ (A B : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f g : A →ₗ[R] B)
    (F G : Tensor R P A →+ Tensor R P B),
    (∀ p a, F (tmul R p a) = tmul R p (f a)) →
    (∀ p a, G (tmul R p a) = tmul R p (g a)) → F = G → f = g

/-- Preservation and reflection of exactness at an arbitrary middle term. -/
def ExactTensor : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (F : Tensor R P A →+ Tensor R P B) (G : Tensor R P B →+ Tensor R P C),
    (∀ p a, F (tmul R p a) = tmul R p (f a)) →
    (∀ p b, G (tmul R p b) = tmul R p (g b)) →
    (Function.Exact f g ↔ Function.Exact F G)

def right_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    RightFlat.{u,v,w} R P →
    (Detects.{u,v,w} R P ↔ ReflectsExact.{u,v,w} R P) ∧
    (Detects.{u,v,w} R P ↔ MaximalTest R P) ∧
    (Detects.{u,v,w} R P → Faithful.{u,v,w} R P ∧ ExactTensor.{u,v,w} R P)

/-- Over Rᵐᵒᵖ the maximal left ideals are precisely maximal right ideals of R.
The first factor M is the given left R-module, viewed as a right Rᵐᵒᵖ-module. -/
def opposite_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    letI := doubleOppositeModule R M
    Flat.{u,v,w} R M →
    (Detects.{u,v,w} Rᵐᵒᵖ M ↔ ReflectsExact.{u,v,w} Rᵐᵒᵖ M) ∧
    (Detects.{u,v,w} Rᵐᵒᵖ M ↔ MaximalTest Rᵐᵒᵖ M) ∧
    (Detects.{u,v,w} Rᵐᵒᵖ M → Faithful.{u,v,w} Rᵐᵒᵖ M ∧ ExactTensor.{u,v,w} Rᵐᵒᵖ M)

/-- The left-module criterion in the original A ⊗[R] M orientation. -/
def LeftDetects (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (A : Type (max u v w)) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    Nontrivial A → Nontrivial (Tensor R A M)

def LeftMaximalTest (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ I : Submodule Rᵐᵒᵖ Rᵐᵒᵖ, IsCoatom I → Nontrivial (Tensor R (Rᵐᵒᵖ ⧸ I) M)

def LeftReflectsExact (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (F : Tensor R A M →+ Tensor R B M) (G : Tensor R B M →+ Tensor R C M),
    (∀ a m, F (tmul R a m) = tmul R (f a) m) →
    (∀ b m, G (tmul R b m) = tmul R (g b) m) →
    Function.Exact F G → Function.Exact f g

def LeftFaithful (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (A B : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] (f g : A →ₗ[Rᵐᵒᵖ] B)
    (F G : Tensor R A M →+ Tensor R B M),
    (∀ a m, F (tmul R a m) = tmul R (f a) m) →
    (∀ a m, G (tmul R a m) = tmul R (g a) m) → F = G → f = g

def LeftExactTensor (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (A B C : Type (max u v w)) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (F : Tensor R A M →+ Tensor R B M) (G : Tensor R B M →+ Tensor R C M),
    (∀ a m, F (tmul R a m) = tmul R (f a) m) →
    (∀ b m, G (tmul R b m) = tmul R (g b) m) →
    (Function.Exact f g ↔ Function.Exact F G)

def left_characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Flat.{u,v,w} R M →
    (LeftDetects.{u,v,w} R M ↔ LeftReflectsExact.{u,v,w} R M) ∧
    (LeftDetects.{u,v,w} R M ↔ LeftMaximalTest R M) ∧
    (LeftDetects.{u,v,w} R M → LeftFaithful.{u,v,w} R M ∧ LeftExactTensor.{u,v,w} R M)

/-- This identifies the opposite-ring orientation in the left criterion,
including the tensors of the maximal right-ideal quotients, with A ⊗[R] M. -/
def left_orientationType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    letI := doubleOppositeModule R M
    ∃ e : Tensor R A M ≃+ Tensor Rᵐᵒᵖ M A,
      ∀ a m, e (tmul R a m) = tmul Rᵐᵒᵖ m a

end P103.Specs.Ch02.FaithfullyFlat
