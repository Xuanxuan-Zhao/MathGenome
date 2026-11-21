import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.DualBasis
import Mathlib.Algebra.Module.LinearMap.Basic

noncomputable section
universe u v w
namespace P103.Morita
open MulOpposite
variable (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
abbrev S := Module.End Rᵐᵒᵖ P
/-- The regular right R-module is R with its standard opposite-ring action. -/
abbrev Q := P →ₗ[Rᵐᵒᵖ] R

/-- Every right module in the ambient universe is a quotient of a sum of copies of P.
The conclusion below also constructs such quotients in any larger universe. -/
def IsGenerator : Prop :=
  ∀ (M : Type (max u v)) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    ∃ (J : Type (max u v)) (f : (J →₀ P) →ₗ[Rᵐᵒᵖ] M), Function.Surjective f

instance dualRightModule : Module (S R P)ᵐᵒᵖ (Q R P) where
  smul s q := q.comp s.unop
  one_smul q := by ext x; rfl
  mul_smul s t q := by ext x; rfl
  smul_zero s := by ext x; rfl
  smul_add s q q' := by ext x; rfl
  add_smul s t q := by ext x; exact q.map_add _ _
  zero_smul q := by ext x; exact q.map_zero

@[simp] theorem dual_right_apply (s : (S R P)ᵐᵒᵖ) (q : Q R P) (x : P) :
    (s • q) x = q (s.unop x) := rfl
@[simp] theorem dual_left_apply (r : R) (q : Q R P) (x : P) :
    (r • q) x = r * q x := rfl

instance dual_commute : SMulCommClass R (S R P)ᵐᵒᵖ (Q R P) where
  smul_comm r s q := by ext x; rfl

instance dual_commute' : SMulCommClass (S R P)ᵐᵒᵖ R (Q R P) where
  smul_comm s r q := by ext x; rfl

instance end_commute : SMulCommClass (S R P) Rᵐᵒᵖ P where
  smul_comm s r x := s.map_smul r x

/-- Rank-one right-linear endomorphism, with coefficient on the right. -/
def theta (p : P) (q : Q R P) : S R P where
  toFun x := op (q x) • p
  map_add' x y := by simp [map_add, add_smul]
  map_smul' r x := by
    change op (q (r • x)) • p = r • (op (q x) • p)
    rw [q.map_smul]
    simp [smul_smul]

@[simp] theorem theta_apply (p : P) (q : Q R P) (x : P) :
    theta R P p q x = op (q x) • p := rfl

/-- Full conclusion, including both outer actions and inverse maps.
Actions on the tensor products are characterized on elementary tensors, so the
statement does not depend on an implementation of tensor scalar descent. -/
def Evaluations : Prop :=
  ∃ (lS : Module (S R P) (P103.BalancedTensor.Tensor R P (Q R P)))
    (rS : Module (S R P)ᵐᵒᵖ (P103.BalancedTensor.Tensor R P (Q R P)))
    (lR : Module R (P103.BalancedTensor.Tensor (S R P) (Q R P) P))
    (rR : Module Rᵐᵒᵖ (P103.BalancedTensor.Tensor (S R P) (Q R P) P)),
    letI := lS; letI := rS; letI := lR; letI := rR
    SMulCommClass (S R P) (S R P)ᵐᵒᵖ (P103.BalancedTensor.Tensor R P (Q R P)) ∧
    SMulCommClass R Rᵐᵒᵖ (P103.BalancedTensor.Tensor (S R P) (Q R P) P) ∧
    (∀ (s : S R P) (p : P) (q : Q R P), s • P103.BalancedTensor.tmul R p q =
      P103.BalancedTensor.tmul R (s • p) q) ∧
    (∀ (s : (S R P)ᵐᵒᵖ) (p : P) (q : Q R P), s • P103.BalancedTensor.tmul R p q =
      P103.BalancedTensor.tmul R p (s • q)) ∧
    (∀ (r : R) (q : Q R P) (p : P), r • P103.BalancedTensor.tmul (S R P) q p =
      P103.BalancedTensor.tmul (S R P) (r • q) p) ∧
    (∀ (r : Rᵐᵒᵖ) (q : Q R P) (p : P), r • P103.BalancedTensor.tmul (S R P) q p =
      P103.BalancedTensor.tmul (S R P) q (r • p)) ∧
    ∃ (e : P103.BalancedTensor.Tensor R P (Q R P) ≃+ S R P)
      (f : P103.BalancedTensor.Tensor (S R P) (Q R P) P ≃+ R),
      (∀ p q, e (P103.BalancedTensor.tmul R p q) = theta R P p q) ∧
      (∀ q p, f (P103.BalancedTensor.tmul (S R P) q p) = q p) ∧
      (∀ (s : S R P) z, e (s • z) = s * e z) ∧
      (∀ (s : (S R P)ᵐᵒᵖ) z, e (s • z) = e z * s.unop) ∧
      (∀ (r : R) z, f (r • z) = r * f z) ∧
      (∀ (r : Rᵐᵒᵖ) z, f (r • z) = f z * r.unop)

/-- Universe-independent form of the generator convention. -/
def generatorQuotientsType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    IsGenerator R P →
    ∀ (M : Type w) [AddCommGroup M] [Module Rᵐᵒᵖ M],
      ∃ (J : Type (max u v w)) (f : (J →₀ P) →ₗ[Rᵐᵒᵖ] M), Function.Surjective f

def evaluationsType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P],
    IsGenerator R P → Evaluations R P

end P103.Morita
