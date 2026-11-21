import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.ModuleExactness
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-! Exactness of Hom and balanced tensor, paper.tex 245–277.
No commutativity or nontriviality is assumed. Right module statements use the
opposite ring. Hom groups are abelian groups, not implicitly R-modules.
-/
namespace P103.HomTensorExactness

set_option linter.unusedVariables false

universe u v w x y

section Hom
variable {R : Type u} [Ring R]
variable {L M N P Q : Type*}
variable [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup P] [AddCommGroup Q]
variable [Module R L] [Module R M] [Module R N] [Module R P] [Module R Q]

/-- The covariant Hom arrow, over an arbitrary ring. -/
def post (f : M →ₗ[R] N) : (P →ₗ[R] M) →+ (P →ₗ[R] N) where
  toFun h := f.comp h
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- The contravariant Hom arrow reverses the original arrow. -/
def pre (f : L →ₗ[R] M) : (M →ₗ[R] Q) →+ (L →ₗ[R] Q) where
  toFun h := h.comp f
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

end Hom

namespace Specification

def HomCovariant : Prop :=
  ∀ (R L M N P : Type*) [Ring R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R L] [Module R M] [Module R N] [Module R P]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N),
    Function.Injective i → Function.Exact i p →
    Function.Injective (post (P := P) i) ∧
      Function.Exact (post (P := P) i) (post (P := P) p)

def HomContravariant : Prop :=
  ∀ (R L M N Q : Type*) [Ring R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module R L] [Module R M] [Module R N] [Module R Q]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N),
    Function.Exact i p → Function.Surjective p →
    Function.Injective (pre (Q := Q) p) ∧
      Function.Exact (pre (Q := Q) p) (pre (Q := Q) i)

/-- Equivariance of the Hom factorizations. On Hom, an action on the target
acts by postcomposition and an action on the source by precomposition. This
states both possibilities without requiring a central R action on Hom. -/
def HomFactorEquivariance : Prop :=
  ∀ (R S L M N P : Type*) [Ring R] [Ring S]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R L] [Module R M] [Module R N] [Module R P]
    [Module S L] [Module S M] [Module S N] [Module S P]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : ∀ (s : S) l, i (s • l) = s • i l)
    (hp : ∀ (s : S) m, p (s • m) = s • p m),
    (∀ (h : P →ₗ[R] M) (k : P →ₗ[R] L),
      Function.Injective i → i.comp k = h →
      (∀ (s : S) x, h (s • x) = s • h x) → ∀ (s : S) x, k (s • x) = s • k x) ∧
    (∀ (h : M →ₗ[R] P) (k : N →ₗ[R] P),
      Function.Surjective p → k.comp p = h →
      (∀ (s : S) x, h (s • x) = s • h x) → ∀ (s : S) x, k (s • x) = s • k x)

/-- Hom arrows preserve postcomposition and precomposition by every commuting
outer scalar action. The two input endomorphisms can be the corresponding
scalar endomorphisms; no commutativity of the base ring is needed. -/
def HomNaturality : Prop :=
  ∀ (R L M N : Type*) [Ring R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (h : L →ₗ[R] M) (a : L →ₗ[R] L) (b : N →ₗ[R] N),
    post f (h.comp a) = (post f h).comp a ∧
      pre h (b.comp f) = b.comp (pre h f)

end Specification

/-- The maps in the integer short exact sequence. -/
def double : ℤ →ₗ[ℤ] ℤ := 2 • LinearMap.id

def modTwo : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap

namespace Specification

def IntegerSequence : Prop :=
  Function.Injective double ∧ Function.Exact double modTwo ∧ Function.Surjective modTwo

def HomNoLift : Prop :=
  ¬ ∃ h : ZMod 2 →ₗ[ℤ] ℤ, modTwo.comp h = LinearMap.id

def HomRestriction : Prop :=
  (∀ h : ℤ →ₗ[ℤ] ℤ, pre double h = 2 • h) ∧
    ¬ Function.Surjective (pre (Q := ℤ) double)

end Specification
open P103.BalancedTensor

namespace Specification

/-- Tensoring an exact sequence of right modules preserves exactness at the
middle and the final surjection, for the canonical elementary-tensor maps. -/
def TensorFirstRightExact : Prop :=
  ∀ (R L A C B : Type*) [Ring R]
    [AddCommGroup L] [AddCommGroup A] [AddCommGroup C] [AddCommGroup B]
    [Module Rᵐᵒᵖ L] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ C] [Module R B]
    (i : L →ₗ[Rᵐᵒᵖ] A) (p : A →ₗ[Rᵐᵒᵖ] C),
    Function.Exact i p → Function.Surjective p →
    ∀ (F : Tensor R L B →+ Tensor R A B),
    (∀ l b, F (tmul R l b) = tmul R (i l) b) →
    ∀ (G : Tensor R A B →+ Tensor R C B),
    (∀ a b, G (tmul R a b) = tmul R (p a) b) →
    Function.Exact F G ∧ Function.Surjective G

/-- The canonical cokernel comparison in the first variable, including the
formulas for both directions. -/
def TensorFirstQuotient : Prop :=
  ∀ (R A B : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module R B] (U : Submodule Rᵐᵒᵖ A)
    (F : Tensor R U B →+ Tensor R A B),
    (∀ (u : U) b, F (tmul R u b) = tmul R (u : A) b) →
    ∃ e : Tensor R (A ⧸ U) B ≃+ ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap),
      (∀ a b, e (tmul R (U.mkQ a) b) =
        (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) ∧
      (∀ a b, e.symm ((LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) =
        tmul R (U.mkQ a) b)

end Specification

namespace Specification
open P103.BalancedTensor

/-- Right exactness of the balanced tensor in the second variable, for every
unital ring and every right module in the fixed variable. The induced maps are
specified by their elementary tensor formulas. -/
def TensorRightExactSecond : Prop :=
  ∀ (R A B B' B'' : Type*) [Ring R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup B'] [AddCommGroup B'']
    [Module Rᵐᵒᵖ A] [Module R B] [Module R B'] [Module R B'']
    (f : B →ₗ[R] B') (g : B' →ₗ[R] B''),
    Function.Exact f g → Function.Surjective g →
    ∀ (F : Tensor R A B →+ Tensor R A B')
      (G : Tensor R A B' →+ Tensor R A B''),
      (∀ a b, F (tmul R a b) = tmul R a (f b)) →
      (∀ a b, G (tmul R a b) = tmul R a (g b)) →
      Function.Exact F G ∧ Function.Surjective G

/-- Quotient in the second variable is the cokernel of tensoring the submodule
inclusion; the isomorphism and its inverse have the canonical formulas. -/
def TensorQuotientSecond : Prop :=
  ∀ (R A B : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module R B] (V : Submodule R B)
    (F : Tensor R A V →+ Tensor R A B),
    (∀ a v, F (tmul R a v) = tmul R a (v : B)) →
    ∃ e : Tensor R A (B ⧸ V) ≃+
        (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap),
      (∀ a b, e (tmul R a (V.mkQ b)) =
        (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) ∧
      (∀ a b, e.symm ((LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) =
        tmul R a (V.mkQ b))

end Specification

namespace Specification
open P103.BalancedTensor
/-- Tensoring the integer short exact sequence by `ZMod 2` kills the induced
multiplication-by-two map on a tensor group containing a nonzero simple tensor. -/
def TensorCounterexample : Prop :=
  ∃ F : Tensor ℤ ℤ (ZMod 2) →+ Tensor ℤ ℤ (ZMod 2),
    (∀ z b, F (tmul ℤ z b) = tmul ℤ (double z) b) ∧
    F = 0 ∧ tmul ℤ (1 : ℤ) (1 : ZMod 2) ≠ 0 ∧ ¬ Function.Injective F

end Specification

namespace Specification
open P103.BalancedTensor

/-- Any specified first-factor outer actions are preserved by the induced map.
The tensor actions are characterized by their elementary-tensor formulas. -/
def TensorMapFirstEquivariance : Prop :=
  ∀ (R S A B A' B' : Type*) [Ring R] [Ring S]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module R B] [Module Rᵐᵒᵖ A'] [Module R B']
    [Module S A] [Module S A']
    [Module S (Tensor R A B)] [Module S (Tensor R A' B')]
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (F : Tensor R A B →+ Tensor R A' B'),
    (∀ a b, F (tmul R a b) = tmul R (f a) (g b)) →
    (∀ (s : S) a, f (s • a) = s • f a) →
    (∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b) →
    (∀ (s : S) (a : A') (b : B'), s • tmul R a b = tmul R (s • a) b) →
    ∀ (s : S) z, F (s • z) = s • F z

/-- The same preservation statement for an outer action on the second factor;
`S` may itself be an opposite ring, giving an unused right action. -/
def TensorMapSecondEquivariance : Prop :=
  ∀ (R S A B A' B' : Type*) [Ring R] [Ring S]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module R B] [Module Rᵐᵒᵖ A'] [Module R B']
    [Module S B] [Module S B']
    [Module S (Tensor R A B)] [Module S (Tensor R A' B')]
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (F : Tensor R A B →+ Tensor R A' B'),
    (∀ a b, F (tmul R a b) = tmul R (f a) (g b)) →
    (∀ (s : S) b, g (s • b) = s • g b) →
    (∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R a (s • b)) →
    (∀ (s : S) (a : A') (b : B'), s • tmul R a b = tmul R a (s • b)) →
    ∀ (s : S) z, F (s • z) = s • F z

/-- Stable submodules admit the projected outer action, independently of the
ring used to present the submodule. -/
def QuotientOuterActions : Prop :=
  ∀ (R S X : Type*) [Ring R] [Ring S] [AddCommGroup X]
    [Module R X] [Module S X] (U : Submodule R X),
    (∀ (s : S) x, x ∈ U → s • x ∈ U) →
    ∃ m : Module S (X ⧸ U), letI := m
      ∀ (s : S) x, U.mkQ (s • x) = s • U.mkQ x

/-- Equivariant maps have outer-stable images, as needed for the tensor
cokernel quotients. -/
def ImageOuterStability : Prop :=
  ∀ (S X Y : Type*) [Ring S] [AddCommGroup X] [AddCommGroup Y]
    [Module S X] [Module S Y] (F : X →+ Y),
    (∀ (s : S) x, F (s • x) = s • F x) →
    ∀ (s : S) y, y ∈ LinearMap.range F.toIntLinearMap →
      s • y ∈ LinearMap.range F.toIntLinearMap

/-- Independently descended commuting actions still commute. -/
def QuotientOuterCommutation : Prop :=
  ∀ (R S T X : Type*) [Ring R] [Ring S] [Ring T] [AddCommGroup X]
    [Module R X] [Module S X] [Module T X] [SMulCommClass S T X]
    (U : Submodule R X) [Module S (X ⧸ U)] [Module T (X ⧸ U)],
    (∀ (s : S) x, U.mkQ (s • x) = s • U.mkQ x) →
    (∀ (t : T) x, U.mkQ (t • x) = t • U.mkQ x) →
    SMulCommClass S T (X ⧸ U)

end Specification

/-- Precomposition by a commuting source action makes Hom a right module over
that outer ring. The opposite scalar order accounts for contravariance. -/
@[instance_reducible] def homSourceModule (R S P M : Type*) [Ring R] [Ring S]
    [AddCommGroup P] [AddCommGroup M] [Module R P] [Module R M]
    [Module S P] [SMulCommClass S R P] : Module Sᵐᵒᵖ (P →ₗ[R] M) where
  smul s h := h.comp (DistribSMul.toLinearMap R P s.unop)
  one_smul h := by ext x; change h ((1 : S) • x) = h x; simp
  mul_smul s t h := by
    ext x
    change h ((s * t).unop • x) = h (t.unop • (s.unop • x))
    simp [mul_smul]
  smul_zero s := by ext x; change (0 : P →ₗ[R] M) (s.unop • x) = 0; rfl
  smul_add s h k := by
    ext x
    change (h + k) (s.unop • x) = h (s.unop • x) + k (s.unop • x)
    rfl
  add_smul s t h := by
    ext x
    change h ((s + t).unop • x) = h (s.unop • x) + h (t.unop • x)
    simp [add_smul]
  zero_smul h := by ext x; change h ((0 : S) • x) = 0; simp


namespace Specification

/-- All four outer Hom actions are preserved. Target actions give left modules;
source actions give right modules. The commuting assumptions ensure scalar
endomorphisms are R-linear, over arbitrary possibly noncommutative rings. -/
def HomOuterActions : Prop :=
  (∀ (R S M N P : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module S M] [Module S N] [SMulCommClass R S M] [SMulCommClass R S N]
    (f : M →ₗ[R] N) (hf : ∀ (s : S) x, f (s • x) = s • f x),
    ∀ (s : S) (h : P →ₗ[R] M), post f (s • h) = s • post f h) ∧
  (∀ (R S M N P : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module S P] [SMulCommClass S R P] (f : M →ₗ[R] N),
    letI := homSourceModule R S P M
    letI := homSourceModule R S P N
    ∀ (s : Sᵐᵒᵖ) (h : P →ₗ[R] M), post f (s • h) = s • post f h) ∧
  (∀ (R S L M Q : Type*) [Ring R] [Ring S]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup Q]
    [Module R L] [Module R M] [Module R Q]
    [Module S Q] [SMulCommClass R S Q] (f : L →ₗ[R] M),
    ∀ (s : S) (h : M →ₗ[R] Q), pre f (s • h) = s • pre f h) ∧
  (∀ (R S L M Q : Type*) [Ring R] [Ring S]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup Q]
    [Module R L] [Module R M] [Module R Q]
    [Module S L] [Module S M] [SMulCommClass S R L] [SMulCommClass S R M]
    (f : L →ₗ[R] M) (hf : ∀ (s : S) x, f (s • x) = s • f x),
    letI := homSourceModule R S M Q
    letI := homSourceModule R S L Q
    ∀ (s : Sᵐᵒᵖ) (h : M →ₗ[R] Q), pre f (s • h) = s • pre f h)

end Specification

namespace Specification

/-- The canonical quotient comparison respects the unused action on the
first factor and its induced actions on the two quotients. -/
def TensorFirstQuotientFirstAction : Prop :=
  ∀ (R S A B : Type*) [Ring R] [Ring S] [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module R B] (U : Submodule Rᵐᵒᵖ A)
    (F : Tensor R U B →+ Tensor R A B)
    [Module S A] [Module S (A ⧸ U)]
    [Module S (Tensor R A B)] [Module S (Tensor R (A ⧸ U) B)]
    [Module S ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap)]
    (hqA : ∀ (s : S) (a : A), U.mkQ (s • a) = s • U.mkQ a)
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b)
    (hY : ∀ (s : S) (a : A ⧸ U) (b : B), s • tmul R a b = tmul R (s • a) b)
    (hqX : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R (A ⧸ U) B ≃+ ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R (U.mkQ a) b) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)),
    (∀ (s : S) z, e (s • z) = s • e z) ∧
    (∀ (s : S) z, e.symm (s • z) = s • e.symm z)

/-- The canonical first quotient comparison also respects the unused action
on the second factor. -/
def TensorFirstQuotientSecondAction : Prop :=
  ∀ (R S A B : Type*) [Ring R] [Ring S] [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module R B] (U : Submodule Rᵐᵒᵖ A)
    (F : Tensor R U B →+ Tensor R A B)
    [Module S B] [Module S (Tensor R A B)] [Module S (Tensor R (A ⧸ U) B)]
    [Module S ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap)]
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))
    (hY : ∀ (s : S) (a : A ⧸ U) (b : B), s • tmul R a b = tmul R a (s • b))
    (hqX : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R (A ⧸ U) B ≃+ ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R (U.mkQ a) b) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)),
    (∀ (s : S) z, e (s • z) = s • e z) ∧
    (∀ (s : S) z, e.symm (s • z) = s • e.symm z)

end Specification

namespace Specification
open P103.BalancedTensor

def TensorQuotientSecondFirstEquivariance : Prop :=
  ∀ (R S A B : Type*) [Ring R] [Ring S]
    [AddCommGroup A] [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module R B]
    (V : Submodule R B) (F : Tensor R A V →+ Tensor R A B)
    [Module S A] [Module S (Tensor R A B)] [Module S (Tensor R A (B ⧸ V))]
    [Module S (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap)]
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b)
    (hY : ∀ (s : S) (a : A) (b : B ⧸ V), s • tmul R a b = tmul R (s • a) b)
    (hQ : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R A (B ⧸ V) ≃+
      (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R a (V.mkQ b)) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)),
    (∀ (s : S) z, e (s • z) = s • e z) ∧
      (∀ (s : S) z, e.symm (s • z) = s • e.symm z)

def TensorQuotientSecondSecondEquivariance : Prop :=
  ∀ (R S A B : Type*) [Ring R] [Ring S]
    [AddCommGroup A] [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module R B]
    (V : Submodule R B) (F : Tensor R A V →+ Tensor R A B)
    [Module S B] [Module S (B ⧸ V)] [Module S (Tensor R A B)]
    [Module S (Tensor R A (B ⧸ V))]
    [Module S (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap)]
    (hB : ∀ (s : S) b, V.mkQ (s • b) = s • V.mkQ b)
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))
    (hY : ∀ (s : S) (a : A) (b : B ⧸ V), s • tmul R a b = tmul R a (s • b))
    (hQ : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R A (B ⧸ V) ≃+
      (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R a (V.mkQ b)) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)),
    (∀ (s : S) z, e (s • z) = s • e z) ∧
      (∀ (s : S) z, e.symm (s • z) = s • e.symm z)

end Specification

namespace Specification
/-- An outer-stable submodule inherits the outer module structure, including
commutation with the original scalar action. -/
def SubmoduleOuterActions : Prop :=
  ∀ (R S X : Type*) [Ring R] [Ring S] [AddCommGroup X]
    [Module R X] [Module S X] [SMulCommClass S R X] (U : Submodule R X),
    (∀ (s : S) x, x ∈ U → s • x ∈ U) →
    ∃ m : Module S U, letI := m
      (∀ (s : S) (u : U), ((s • u : U) : X) = s • (u : X)) ∧
      SMulCommClass S R U
end Specification

end P103.HomTensorExactness
