import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Map

namespace P103.BalancedTensor

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u v w x
variable {R : Type u} [Ring R]
variable {A : Type v} {B : Type w} {C : Type x}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module Rᵐᵒᵖ A] [Module R B]

@[simp] theorem zero_tmul (b : B) : tmul R (0 : A) b = 0 := by
  simp [tmul]

@[simp] theorem tmul_zero (a : A) : tmul R a (0 : B) = 0 := by
  simp [tmul]

theorem add_tmul (a a' : A) (b : B) :
    tmul R (a + a') b = tmul R a b + tmul R a' b := by
  simp [tmul, TensorProduct.add_tmul]

theorem tmul_add (a : A) (b b' : B) :
    tmul R a (b + b') = tmul R a b + tmul R a b' := by
  simp [tmul, TensorProduct.tmul_add]

theorem balance (r : R) (a : A) (b : B) :
    tmul R (MulOpposite.op r • a) b = tmul R a (r • b) := by
  apply sub_eq_zero.mp
  change (relations R A B).mkQ _ - (relations R A B).mkQ _ = 0
  rw [← map_sub]
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨r, a, b, rfl⟩

theorem pairLaws : Specification.PairLaws R (A := A) (B := B) :=
  ⟨add_tmul, tmul_add, zero_tmul, tmul_zero, balance⟩

/-- The balanced canonical pairing, bundled for the universal property. -/
def pairing : Pairing R (A := A) (B := B) (Tensor R A B) where
  toBiadditive := {
    toFun := fun a =>
      { toFun := tmul R a
        map_zero' := tmul_zero a
        map_add' := tmul_add a }
    map_zero' := by ext b; exact zero_tmul b
    map_add' := by intros; ext b; apply add_tmul }
  balance := balance

@[simp] theorem pairing_apply (a : A) (b : B) :
    pairing.toBiadditive a b = tmul R a b := rfl

/-- Every tensor is a finite sum of elementary tensors. Negatives can be absorbed
in the first factor, so a separate subtraction step is unnecessary. -/
@[elab_as_elim] theorem induction_on (z : Tensor R A B)
    {P : Tensor R A B → Prop} (h0 : P 0)
    (ht : ∀ a b, P (tmul R a b))
    (ha : ∀ x y, P x → P y → P (x + y)) : P z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using TensorProduct.inductionOn with
    | tmul a b => exact ht a b
    | add z z' hz hz' => exact ha _ _ hz hz'

theorem generation : Specification.Generation R (A := A) (B := B) := by
  intro P h0 ht ha z
  exact induction_on z h0 ht ha

@[ext] theorem hom_ext {f g : Tensor R A B →+ C}
    (h : ∀ a b, f (tmul R a b) = g (tmul R a b)) : f = g := by
  apply AddMonoidHom.ext
  intro z
  induction z using induction_on with
  | h0 => simp
  | ht a b => exact h a b
  | ha z z' hz hz' => simp [hz, hz']

/-- Integer bilinearity of any biadditive pairing. -/
private def intLift (f : Pairing R (A := A) (B := B) C) :
    TensorProduct ℤ A B →ₗ[ℤ] C :=
  (TensorProduct.liftAddHom f.toBiadditive
    (fun r a b => by simp)).toIntLinearMap

private theorem relations_le_ker (f : Pairing R (A := A) (B := B) C) :
    relations R A B ≤ LinearMap.ker (intLift f) := by
  apply Submodule.span_le.mpr
  rintro z ⟨r, a, b, rfl⟩
  change intLift f _ = 0
  simp only [map_sub, intLift, AddMonoidHom.coe_toIntLinearMap,
    TensorProduct.liftAddHom_tmul, sub_eq_zero]
  exact f.balance r a b

/-- The unique homomorphism induced by a balanced biadditive pairing. -/
def lift (f : Pairing R (A := A) (B := B) C) : Tensor R A B →+ C :=
  ((relations R A B).liftQ (intLift f) (relations_le_ker f)).toAddMonoidHom

@[simp] theorem lift_tmul (f : Pairing R (A := A) (B := B) C) (a : A) (b : B) :
    lift f (tmul R a b) = f.toBiadditive a b := rfl

theorem universal : Specification.Universal R (A := A) (B := B) C := by
  intro f
  refine ⟨lift f, lift_tmul f, ?_⟩
  intro g hg
  apply hom_ext
  intro a b
  exact (hg a b).trans (lift_tmul f a b).symm

/-- Build a pairing from its addition and balance formulas. -/
def Pairing.ofFun (f : A → B → C)
    (hA : ∀ a a' b, f (a + a') b = f a b + f a' b)
    (hB : ∀ a b b', f a (b + b') = f a b + f a b')
    (hR : ∀ (r : R) (a : A) (b : B), f (MulOpposite.op r • a) b = f a (r • b)) :
    Pairing R (A := A) (B := B) C where
  toBiadditive := AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (f a) (hB a))
    (fun a a' => AddMonoidHom.ext (hA a a'))
  balance := hR

section Maps
variable {A' : Type*} {B' : Type*} {A'' : Type*} {B'' : Type*}
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup A''] [AddCommGroup B'']
variable [Module Rᵐᵒᵖ A'] [Module R B'] [Module Rᵐᵒᵖ A''] [Module R B'']

/-- Functoriality on module homomorphisms. -/
def map (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') :
    Tensor R A B →+ Tensor R A' B' :=
  lift <| Pairing.ofFun (fun a b => tmul R (f a) (g b))
    (by intros; simp [add_tmul]) (by intros; simp [tmul_add])
    (by intros; simp [balance])

@[simp] theorem map_tmul (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') (a : A) (b : B) :
    map f g (tmul R a b) = tmul R (f a) (g b) := rfl

@[simp] theorem map_id :
    map (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (LinearMap.id : B →ₗ[R] B) =
      AddMonoidHom.id (Tensor R A B) := by
  apply hom_ext
  intros
  rfl

theorem map_comp (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (f' : A' →ₗ[Rᵐᵒᵖ] A'') (g' : B' →ₗ[R] B'') :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) := by
  apply hom_ext
  intros
  rfl

@[simp] theorem map_zero_left (g : B →ₗ[R] B') :
    map (0 : A →ₗ[Rᵐᵒᵖ] A') g = 0 := by
  apply hom_ext
  intros
  simp

@[simp] theorem map_zero_right (f : A →ₗ[Rᵐᵒᵖ] A') :
    map f (0 : B →ₗ[R] B') = 0 := by
  apply hom_ext
  intros
  simp

theorem map_add_left (f f' : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') :
    map (f + f') g = map f g + map f' g := by
  apply hom_ext
  intros
  simp [add_tmul]

theorem map_add_right (f : A →ₗ[Rᵐᵒᵖ] A') (g g' : B →ₗ[R] B') :
    map f (g + g') = map f g + map f g' := by
  apply hom_ext
  intros
  simp [tmul_add]

end Maps

section Units

/-- Evaluation against the right regular module. -/
def rightUnit : Tensor R A R ≃+ A := by
  let f : Tensor R A R →+ A := lift <| Pairing.ofFun
    (fun a r => MulOpposite.op r • a)
    (by intros; simp [smul_add]) (by intros; simp [add_smul])
    (by intros; simp [smul_smul])
  let g : A →+ Tensor R A R := pairing.toBiadditive.flip 1
  exact {
    f with
    invFun := g
    left_inv := fun z => by
      change g (f z) = z
      induction z using induction_on with
      | h0 => simp
      | ht a r =>
        change tmul R (MulOpposite.op r • a) 1 = tmul R a r
        simpa using balance r a (1 : R)
      | ha z z' hz hz' => simp [hz, hz']
    right_inv := fun a => by change MulOpposite.op (1 : R) • a = a; simp }

@[simp] theorem rightUnit_tmul (a : A) (r : R) :
    rightUnit (tmul R a r) = MulOpposite.op r • a := rfl

@[simp] theorem rightUnit_symm (a : A) :
    rightUnit.symm a = tmul R a (1 : R) := rfl

/-- Evaluation against the left regular module. Its right action is multiplication
in `R`, encoded by the standard `Rᵐᵒᵖ` action. -/
def leftUnit : Tensor R R B ≃+ B := by
  let f : Tensor R R B →+ B := lift <| Pairing.ofFun
    (fun r b => r • b)
    (by intros; simp [add_smul]) (by intros; simp [smul_add])
    (by intros; simp [smul_smul])
  let g : B →+ Tensor R R B := pairing.toBiadditive 1
  exact {
    f with
    invFun := g
    left_inv := fun z => by
      change g (f z) = z
      induction z using induction_on with
      | h0 => simp
      | ht r b =>
        change tmul R (1 : R) (r • b) = tmul R r b
        simpa using (balance r (1 : R) b).symm
      | ha z z' hz hz' => simp [hz, hz']
    right_inv := fun b => by change (1 : R) • b = b; simp }

@[simp] theorem leftUnit_tmul (r : R) (b : B) :
    leftUnit (tmul R r b) = r • b := rfl

@[simp] theorem leftUnit_symm (b : B) :
    leftUnit.symm b = tmul R (1 : R) b := rfl

variable {A' B' : Type*} [AddCommGroup A'] [AddCommGroup B']
variable [Module Rᵐᵒᵖ A'] [Module R B']

theorem rightUnit_natural (f : A →ₗ[Rᵐᵒᵖ] A') (z : Tensor R A R) :
    rightUnit (map f LinearMap.id z) = f (rightUnit z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a r => simp
  | ha z z' hz hz' => simp [hz, hz']

theorem leftUnit_natural (g : B →ₗ[R] B') (z : Tensor R R B) :
    leftUnit (map LinearMap.id g z) = g (leftUnit z) := by
  induction z using induction_on with
  | h0 => simp
  | ht r b => simp
  | ha z z' hz hz' => simp [hz, hz']

end Units

section OuterActions
variable {S T : Type*} [Ring S] [Ring T]

/-- Descending a commuting action on the first factor. -/
def leftScale [Module S A] [SMulCommClass S Rᵐᵒᵖ A] (s : S) :
    Tensor R A B →+ Tensor R A B :=
  lift <| Pairing.ofFun (fun a b => tmul R (s • a) b)
    (by intros; simp [smul_add, add_tmul])
    (by intros; simp [tmul_add])
    (by intros; rw [smul_comm, balance])

@[simp] theorem leftScale_tmul [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    (s : S) (a : A) (b : B) :
    leftScale s (tmul R a b) = tmul R (s • a) b := rfl

/-- Explicit, rather than global, instance: both factors may carry actions of
one and the same ring, and those two actions need not agree. -/
@[instance_reducible] def leftModule [Module S A] [SMulCommClass S Rᵐᵒᵖ A] : Module S (Tensor R A B) where
  smul := fun s z => leftScale s z
  one_smul := fun z => by
    change leftScale (1 : S) z = z
    induction z using induction_on with
    | h0 => exact map_zero _
    | ht a b => simp
    | ha z z' hz hz' => simp [map_add, hz, hz']
  mul_smul := fun s t z => by
    change leftScale (s * t) z = leftScale s (leftScale t z)
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp [mul_smul]
    | ha z z' hz hz' => simp [map_add, hz, hz']
  smul_zero := fun s => map_zero (leftScale s)
  smul_add := fun s => map_add (leftScale s)
  add_smul := fun s t z => by
    change leftScale (s + t) z = leftScale s z + leftScale t z
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp [add_smul, add_tmul]
    | ha z z' hz hz' => simp [map_add, hz, hz', add_add_add_comm]
  zero_smul := fun z => by
    change leftScale (0 : S) z = 0
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp
    | ha z z' hz hz' => simp [map_add, hz, hz']

/-- Descending a commuting action on the second factor. Taking `S` to be an
opposite ring gives precisely an unused right action. -/
def rightScale [Module S B] [SMulCommClass S R B] (s : S) :
    Tensor R A B →+ Tensor R A B :=
  lift <| Pairing.ofFun (fun a b => tmul R a (s • b))
    (by intros; simp [add_tmul])
    (by intros; simp [smul_add, tmul_add])
    (by intros; rw [balance, smul_comm s])

@[simp] theorem rightScale_tmul [Module S B] [SMulCommClass S R B]
    (s : S) (a : A) (b : B) :
    rightScale s (tmul R a b) = tmul R a (s • b) := rfl

@[instance_reducible] def rightModule [Module S B] [SMulCommClass S R B] : Module S (Tensor R A B) where
  smul := fun s z => rightScale s z
  one_smul := fun z => by
    change rightScale (1 : S) z = z
    induction z using induction_on with
    | h0 => exact map_zero _
    | ht a b => simp
    | ha z z' hz hz' => simp [map_add, hz, hz']
  mul_smul := fun s t z => by
    change rightScale (s * t) z = rightScale s (rightScale t z)
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp [mul_smul]
    | ha z z' hz hz' => simp [map_add, hz, hz']
  smul_zero := fun s => map_zero (rightScale s)
  smul_add := fun s => map_add (rightScale s)
  add_smul := fun s t z => by
    change rightScale (s + t) z = rightScale s z + rightScale t z
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp [add_smul, tmul_add]
    | ha z z' hz hz' => simp [map_add, hz, hz', add_add_add_comm]
  zero_smul := fun z => by
    change rightScale (0 : S) z = 0
    induction z using induction_on with
    | h0 => simp
    | ht a b => simp
    | ha z z' hz hz' => simp [map_add, hz, hz']

theorem outer_commute [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    [Module T B] [SMulCommClass T R B] (s : S) (t : T) (z : Tensor R A B) :
    leftScale s (rightScale t z) = rightScale t (leftScale s z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => rfl
  | ha z z' hz hz' => simp [hz, hz']

theorem lift_leftScale [Module S A] [SMulCommClass S Rᵐᵒᵖ A] [Module S C]
    (f : Pairing R (A := A) (B := B) C)
    (hf : ∀ (s : S) (a : A) (b : B), f.toBiadditive (s • a) b = s • f.toBiadditive a b)
    (s : S) (z : Tensor R A B) : lift f (leftScale s z) = s • lift f z := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hf]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

theorem lift_rightScale [Module S B] [SMulCommClass S R B] [Module S C]
    (f : Pairing R (A := A) (B := B) C)
    (hf : ∀ (s : S) (a : A) (b : B), f.toBiadditive a (s • b) = s • f.toBiadditive a b)
    (s : S) (z : Tensor R A B) : lift f (rightScale s z) = s • lift f z := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hf]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

variable {A' B' : Type*} [AddCommGroup A'] [AddCommGroup B']
variable [Module Rᵐᵒᵖ A'] [Module R B']

theorem map_leftScale [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    [Module S A'] [SMulCommClass S Rᵐᵒᵖ A']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (hf : ∀ (s : S) a, f (s • a) = s • f a) (s : S) (z : Tensor R A B) :
    map f g (leftScale s z) = leftScale s (map f g z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hf]
  | ha z z' hz hz' => simp [hz, hz']

theorem map_rightScale [Module S B] [SMulCommClass S R B]
    [Module S B'] [SMulCommClass S R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (hg : ∀ (s : S) b, g (s • b) = s • g b) (s : S) (z : Tensor R A B) :
    map f g (rightScale s z) = rightScale s (map f g z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hg]
  | ha z z' hz hz' => simp [hz, hz']

end OuterActions

section Associativity
variable {S : Type*} [Ring S] [Module Sᵐᵒᵖ B] [Module S C]
variable [Module Sᵐᵒᵖ (Tensor R A B)] [Module R (Tensor S B C)]
variable (hRight : ∀ (s : S) (a : A) (b : B),
  MulOpposite.op s • tmul R a b = tmul R a (MulOpposite.op s • b))
variable (hLeft : ∀ (r : R) (b : B) (c : C),
  r • tmul S b c = tmul S (r • b) c)

private def assocInner (c : C) : Tensor R A B →+ Tensor R A (Tensor S B C) :=
  lift <| Pairing.ofFun (fun a b => tmul R a (tmul S b c))
    (by intros; simp [add_tmul])
    (by intros; simp [add_tmul, tmul_add])
    (by intros; rw [balance, hLeft])

omit [Module Sᵐᵒᵖ (Tensor R A B)] in
@[simp] private theorem assocInner_tmul (a : A) (b : B) (c : C) :
    assocInner hLeft c (tmul R a b) = tmul R a (tmul S b c) := rfl

private def assocForward : Tensor S (Tensor R A B) C →+ Tensor R A (Tensor S B C) :=
  lift <| Pairing.ofFun (fun z c => assocInner hLeft c z)
    (by intros; exact map_add _ _ _)
    (by
      intro z c c'
      induction z using induction_on with
      | h0 => simp
      | ht a b => simp [tmul_add]
      | ha z z' hz hz' => simp [hz, hz', add_add_add_comm])
    (by
      intro s z c
      induction z using induction_on with
      | h0 => simp
      | ht a b => simp [hRight, balance]
      | ha z z' hz hz' => simp [smul_add, hz, hz'])

@[simp] private theorem assocForward_tmul (a : A) (b : B) (c : C) :
    assocForward hRight hLeft (tmul S (tmul R a b) c) = tmul R a (tmul S b c) := rfl

private def assocBackInner (a : A) : Tensor S B C →+ Tensor S (Tensor R A B) C :=
  lift <| Pairing.ofFun (fun b c => tmul S (tmul R a b) c)
    (by intros; simp [tmul_add, add_tmul])
    (by intros; simp [tmul_add])
    (by intros; rw [← hRight, balance])

omit [Module R (Tensor S B C)] in
@[simp] private theorem assocBackInner_tmul (a : A) (b : B) (c : C) :
    assocBackInner hRight a (tmul S b c) = tmul S (tmul R a b) c := rfl

private def assocBackward : Tensor R A (Tensor S B C) →+ Tensor S (Tensor R A B) C :=
  lift <| Pairing.ofFun (fun a z => assocBackInner hRight a z)
    (by
      intro a a' z
      induction z using induction_on with
      | h0 => simp
      | ht b c => simp [add_tmul]
      | ha z z' hz hz' => simp [hz, hz', add_add_add_comm])
    (by intros; exact map_add _ _ _)
    (by
      intro r a z
      induction z using induction_on with
      | h0 => simp
      | ht b c => simp [hLeft, balance]
      | ha z z' hz hz' => simp [smul_add, hz, hz'])

@[simp] private theorem assocBackward_tmul (a : A) (b : B) (c : C) :
    assocBackward hRight hLeft (tmul R a (tmul S b c)) = tmul S (tmul R a b) c := rfl

/-- Associativity for any descended actions having the elementary-tensor
formulas. Thus the result is independent of how the actions were constructed. -/
def assocWith : Tensor S (Tensor R A B) C ≃+ Tensor R A (Tensor S B C) := {
  assocForward hRight hLeft with
  invFun := assocBackward hRight hLeft
  left_inv := fun z => by
    change assocBackward hRight hLeft (assocForward hRight hLeft z) = z
    induction z using induction_on with
    | h0 => simp
    | ht x c =>
      induction x using induction_on with
      | h0 => simp
      | ht a b => simp
      | ha x x' hx hx' => simp [add_tmul, hx, hx']
    | ha z z' hz hz' => simp [hz, hz']
  right_inv := fun z => by
    change assocForward hRight hLeft (assocBackward hRight hLeft z) = z
    induction z using induction_on with
    | h0 => simp
    | ht a x =>
      induction x using induction_on with
      | h0 => simp
      | ht b c => simp
      | ha x x' hx hx' => simp [tmul_add, hx, hx']
    | ha z z' hz hz' => simp [hz, hz'] }

@[simp] theorem assocWith_tmul (a : A) (b : B) (c : C) :
    assocWith hRight hLeft (tmul S (tmul R a b) c) = tmul R a (tmul S b c) := rfl

@[simp] theorem assocWith_symm_tmul (a : A) (b : B) (c : C) :
    (assocWith hRight hLeft).symm (tmul R a (tmul S b c)) =
      tmul S (tmul R a b) c := rfl

end Associativity

section DirectSums
open DirectSum
variable {ι : Type*} [DecidableEq ι]
variable {D : Type*} [AddCommGroup D]

/-- Postcomposition of a balanced pairing. -/
def Pairing.post (f : Pairing R (A := A) (B := B) C) (h : C →+ D) :
    Pairing R (A := A) (B := B) D :=
  Pairing.ofFun (fun a b => h (f.toBiadditive a b))
    (by intros; simp) (by intros; simp) (by intros; rw [f.balance])

variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]

private def sumLeftInner (f : ∀ i, Pairing R (A := M i) (B := B) C) (b : B) :
    (⨁ i, M i) →+ C :=
  DirectSum.toAddMonoid (fun i => (f i).toBiadditive.flip b)

@[simp] private theorem sumLeftInner_of (f : ∀ i, Pairing R (A := M i) (B := B) C)
    (i : ι) (a : M i) (b : B) :
    sumLeftInner f b (DirectSum.of M i a) = (f i).toBiadditive a b := by
  simp [sumLeftInner]

/-- Assemble balanced pairings from an arbitrary direct sum in the first slot. -/
def Pairing.sumLeft (f : ∀ i, Pairing R (A := M i) (B := B) C) :
    Pairing R (A := ⨁ i, M i) (B := B) C :=
  Pairing.ofFun (fun a b => sumLeftInner f b a)
    (by intros; exact map_add _ _ _)
    (by
      intro a b b'
      induction a using DirectSum.induction_on with
      | zero => simp
      | of i a => simp
      | add a a' ha ha' => simp [ha, ha', add_add_add_comm])
    (by
      intro r a b
      induction a using DirectSum.induction_on with
      | zero => simp
      | of i a => simp [← DirectSum.of_smul, (f i).balance]
      | add a a' ha ha' => simp [smul_add, ha, ha'])

@[simp] theorem Pairing.sumLeft_of (f : ∀ i, Pairing R (A := M i) (B := B) C)
    (i : ι) (a : M i) (b : B) :
    (Pairing.sumLeft f).toBiadditive (DirectSum.of M i a) b =
      (f i).toBiadditive a b := sumLeftInner_of f i a b

private def leftSumForward : Tensor R (⨁ i, M i) B →+ ⨁ i, Tensor R (M i) B :=
  lift <| Pairing.sumLeft fun i => pairing.post (DirectSum.of (fun i => Tensor R (M i) B) i)

@[simp] private theorem leftSumForward_of (i : ι) (a : M i) (b : B) :
    leftSumForward (tmul R (DirectSum.of M i a) b) =
      DirectSum.of (fun i => Tensor R (M i) B) i (tmul R a b) := by
  simp only [leftSumForward, lift_tmul, Pairing.sumLeft_of]
  rfl

private def leftSumBackward : (⨁ i, Tensor R (M i) B) →+ Tensor R (⨁ i, M i) B :=
  DirectSum.toAddMonoid fun i => map (DirectSum.lof Rᵐᵒᵖ ι M i) LinearMap.id

@[simp] private theorem leftSumBackward_of (i : ι) (z : Tensor R (M i) B) :
    leftSumBackward (DirectSum.of (fun i => Tensor R (M i) B) i z) =
      map (DirectSum.lof Rᵐᵒᵖ ι M i) LinearMap.id z := by
  simp [leftSumBackward]

/-- Distribution over arbitrary, possibly empty, direct sums in the right-module
variable. There is no finiteness hypothesis on the index set. -/
def directSumLeft : Tensor R (⨁ i, M i) B ≃+ ⨁ i, Tensor R (M i) B := {
  leftSumForward with
  invFun := leftSumBackward
  left_inv := fun z => by
    change leftSumBackward (leftSumForward z) = z
    induction z using induction_on with
    | h0 => simp
    | ht a b =>
      induction a using DirectSum.induction_on with
      | zero => simp
      | of i a => simp [DirectSum.lof_eq_of]
      | add a a' ha ha' => simp [add_tmul, ha, ha']
    | ha z z' hz hz' => simp [hz, hz']
  right_inv := fun z => by
    change leftSumForward (leftSumBackward z) = z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of i z =>
      rw [leftSumBackward_of]
      induction z using induction_on with
      | h0 => simp
      | ht a b => simp [DirectSum.lof_eq_of]
      | ha z z' hz hz' => simp [hz, hz']
    | add z z' hz hz' => simp [hz, hz'] }

@[simp] theorem directSumLeft_tmul_of (i : ι) (a : M i) (b : B) :
    directSumLeft (tmul R (DirectSum.of M i a) b) =
      DirectSum.of (fun i => Tensor R (M i) B) i (tmul R a b) := leftSumForward_of i a b

@[simp] theorem directSumLeft_symm_of (i : ι) (z : Tensor R (M i) B) :
    directSumLeft.symm (DirectSum.of (fun i => Tensor R (M i) B) i z) =
      map (DirectSum.lof Rᵐᵒᵖ ι M i) LinearMap.id z := leftSumBackward_of i z

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

private def sumRightInner (f : ∀ i, Pairing R (A := A) (B := N i) C) (a : A) :
    (⨁ i, N i) →+ C :=
  DirectSum.toAddMonoid (fun i => (f i).toBiadditive a)

@[simp] private theorem sumRightInner_of (f : ∀ i, Pairing R (A := A) (B := N i) C)
    (i : ι) (a : A) (b : N i) :
    sumRightInner f a (DirectSum.of N i b) = (f i).toBiadditive a b := by
  simp [sumRightInner]

/-- Assemble pairings from an arbitrary direct sum in the second slot. -/
def Pairing.sumRight (f : ∀ i, Pairing R (A := A) (B := N i) C) :
    Pairing R (A := A) (B := ⨁ i, N i) C :=
  Pairing.ofFun (fun a b => sumRightInner f a b)
    (by
      intro a a' b
      induction b using DirectSum.induction_on with
      | zero => simp
      | of i b => simp
      | add b b' hb hb' => simp [hb, hb', add_add_add_comm])
    (by intros; exact map_add _ _ _)
    (by
      intro r a b
      induction b using DirectSum.induction_on with
      | zero => simp
      | of i b => simp [← DirectSum.of_smul, (f i).balance]
      | add b b' hb hb' => simp [smul_add, hb, hb'])

@[simp] theorem Pairing.sumRight_of (f : ∀ i, Pairing R (A := A) (B := N i) C)
    (i : ι) (a : A) (b : N i) :
    (Pairing.sumRight f).toBiadditive a (DirectSum.of N i b) =
      (f i).toBiadditive a b := sumRightInner_of f i a b

private def rightSumForward : Tensor R A (⨁ i, N i) →+ ⨁ i, Tensor R A (N i) :=
  lift <| Pairing.sumRight fun i => pairing.post (DirectSum.of (fun i => Tensor R A (N i)) i)

@[simp] private theorem rightSumForward_of (i : ι) (a : A) (b : N i) :
    rightSumForward (tmul R a (DirectSum.of N i b)) =
      DirectSum.of (fun i => Tensor R A (N i)) i (tmul R a b) := by
  simp only [rightSumForward, lift_tmul, Pairing.sumRight_of]
  rfl

private def rightSumBackward : (⨁ i, Tensor R A (N i)) →+ Tensor R A (⨁ i, N i) :=
  DirectSum.toAddMonoid fun i => map LinearMap.id (DirectSum.lof R ι N i)

@[simp] private theorem rightSumBackward_of (i : ι) (z : Tensor R A (N i)) :
    rightSumBackward (DirectSum.of (fun i => Tensor R A (N i)) i z) =
      map LinearMap.id (DirectSum.lof R ι N i) z := by
  simp [rightSumBackward]

/-- Distribution over arbitrary direct sums in the left-module variable. -/
def directSumRight : Tensor R A (⨁ i, N i) ≃+ ⨁ i, Tensor R A (N i) := {
  rightSumForward with
  invFun := rightSumBackward
  left_inv := fun z => by
    change rightSumBackward (rightSumForward z) = z
    induction z using induction_on with
    | h0 => simp
    | ht a b =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | of i b => simp [DirectSum.lof_eq_of]
      | add b b' hb hb' => simp [tmul_add, hb, hb']
    | ha z z' hz hz' => simp [hz, hz']
  right_inv := fun z => by
    change rightSumForward (rightSumBackward z) = z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of i z =>
      rw [rightSumBackward_of]
      induction z using induction_on with
      | h0 => simp
      | ht a b => simp [DirectSum.lof_eq_of]
      | ha z z' hz hz' => simp [hz, hz']
    | add z z' hz hz' => simp [hz, hz'] }

@[simp] theorem directSumRight_tmul_of (i : ι) (a : A) (b : N i) :
    directSumRight (tmul R a (DirectSum.of N i b)) =
      DirectSum.of (fun i => Tensor R A (N i)) i (tmul R a b) := rightSumForward_of i a b

@[simp] theorem directSumRight_symm_of (i : ι) (z : Tensor R A (N i)) :
    directSumRight.symm (DirectSum.of (fun i => Tensor R A (N i)) i z) =
      map LinearMap.id (DirectSum.lof R ι N i) z := rightSumBackward_of i z

end DirectSums

section CommutativeComparison
variable {K : Type*} [CommRing K]
variable [Module K A] [Module K B] [Module Kᵐᵒᵖ A] [IsCentralScalar K A]

private def commForward : Tensor K A B →+ TensorProduct K A B :=
  lift <| Pairing.ofFun (TensorProduct.tmul K)
    TensorProduct.add_tmul TensorProduct.tmul_add
    (by intros; rw [op_smul_eq_smul, TensorProduct.smul_tmul])

@[simp] private theorem commForward_tmul (a : A) (b : B) :
    commForward (tmul K a b) = TensorProduct.tmul K a b := rfl

private def commBackward : TensorProduct K A B →+ Tensor K A B :=
  TensorProduct.liftAddHom pairing.toBiadditive
    (fun r a b => by
      change tmul K (r • a) b = tmul K a (r • b)
      rw [← op_smul_eq_smul r a]
      exact balance r a b)

@[simp] private theorem commBackward_tmul (a : A) (b : B) :
    commBackward (TensorProduct.tmul K a b) = tmul K a b := rfl

/-- The balanced construction agrees canonically with Mathlib's tensor. -/
def commAddEquiv : Tensor K A B ≃+ TensorProduct K A B := {
  commForward with
  invFun := commBackward
  left_inv := fun z => by
    change commBackward (commForward z) = z
    induction z using induction_on with
    | h0 => simp
    | ht a b => rfl
    | ha z z' hz hz' => simp [hz, hz']
  right_inv := fun z => by
    change commForward (commBackward z) = z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add z z' hz hz' => simp [hz, hz'] }

@[simp] theorem commAddEquiv_tmul (a : A) (b : B) :
    commAddEquiv (tmul K a b) = TensorProduct.tmul K a b := rfl

@[simp] theorem commAddEquiv_symm_tmul (a : A) (b : B) :
    commAddEquiv.symm (TensorProduct.tmul K a b) = tmul K a b := rfl

theorem commAddEquiv_rightScale (r : K) (z : Tensor K A B) :
    commAddEquiv (rightScale r z) = r • commAddEquiv z := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [TensorProduct.tmul_smul]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

theorem commAddEquiv_leftScale [SMulCommClass K Kᵐᵒᵖ A] (r : K) (z : Tensor K A B) :
    commAddEquiv (leftScale r z) = r • commAddEquiv z := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [← TensorProduct.smul_tmul']
  | ha z z' hz hz' => simp [hz, hz', smul_add]

/-- The comparison preserves the inherited commutative scalar action. -/
def commLinearEquiv :
    letI : Module K (Tensor K A B) := rightModule
    Tensor K A B ≃ₗ[K] TensorProduct K A B := by
  letI : Module K (Tensor K A B) := rightModule
  exact { commAddEquiv with map_smul' := commAddEquiv_rightScale }

variable {A' B' : Type*} [AddCommGroup A'] [AddCommGroup B']
variable [Module K A'] [Module K B'] [Module Kᵐᵒᵖ A'] [IsCentralScalar K A']

theorem commAddEquiv_natural (f : A →ₗ[Kᵐᵒᵖ] A') (g : B →ₗ[K] B')
    (fK : A →ₗ[K] A') (hf : ∀ a, fK a = f a) (z : Tensor K A B) :
    commAddEquiv (map f g z) = TensorProduct.map fK g (commAddEquiv z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hf]
  | ha z z' hz hz' => simp [hz, hz']

end CommutativeComparison

section LinearOuterMaps
variable {S T : Type*} [Ring S] [Ring T]
variable {A' B' : Type*} [AddCommGroup A'] [AddCommGroup B']
variable [Module Rᵐᵒᵖ A'] [Module R B']

/-- Induced maps are linear for a specified commuting first-factor action. -/
def mapLeftLinear [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    [Module S A'] [SMulCommClass S Rᵐᵒᵖ A']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (hf : ∀ (s : S) a, f (s • a) = s • f a) :
    letI : Module S (Tensor R A B) := leftModule
    letI : Module S (Tensor R A' B') := leftModule
    Tensor R A B →ₗ[S] Tensor R A' B' := by
  letI : Module S (Tensor R A B) := leftModule
  letI : Module S (Tensor R A' B') := leftModule
  exact { map f g with map_smul' := map_leftScale f g hf }

/-- Induced maps are linear for a specified commuting second-factor action. -/
def mapRightLinear [Module S B] [SMulCommClass S R B]
    [Module S B'] [SMulCommClass S R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (hg : ∀ (s : S) b, g (s • b) = s • g b) :
    letI : Module S (Tensor R A B) := rightModule
    letI : Module S (Tensor R A' B') := rightModule
    Tensor R A B →ₗ[S] Tensor R A' B' := by
  letI : Module S (Tensor R A B) := rightModule
  letI : Module S (Tensor R A' B') := rightModule
  exact { map f g with map_smul' := map_rightScale f g hg }

/-- The two independently descended outer actions commute. -/
theorem outerCommClass [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    [Module T B] [SMulCommClass T R B] :
    letI : Module S (Tensor R A B) := leftModule
    letI : Module T (Tensor R A B) := rightModule
    SMulCommClass S T (Tensor R A B) := by
  letI : Module S (Tensor R A B) := leftModule
  letI : Module T (Tensor R A B) := rightModule
  exact ⟨outer_commute⟩

theorem rightUnit_leftScale [Module S A] [SMulCommClass S Rᵐᵒᵖ A]
    (s : S) (z : Tensor R A R) : rightUnit (leftScale s z) = s • rightUnit z := by
  induction z using induction_on with
  | h0 => simp
  | ht a r => simp [smul_comm s]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

theorem rightUnit_rightScale (r : Rᵐᵒᵖ) (z : Tensor R A R) :
    rightUnit (rightScale r z) = r • rightUnit z := by
  induction z using induction_on with
  | h0 => simp
  | ht a s => simp [smul_smul]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

theorem leftUnit_leftScale (r : R) (z : Tensor R R B) :
    leftUnit (leftScale r z) = r • leftUnit z := by
  induction z using induction_on with
  | h0 => simp
  | ht s b => simp [smul_smul]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

theorem leftUnit_rightScale [Module S B] [SMulCommClass S R B]
    (s : S) (z : Tensor R R B) : leftUnit (rightScale s z) = s • leftUnit z := by
  induction z using induction_on with
  | h0 => simp
  | ht r b => simp [smul_comm s]
  | ha z z' hz hz' => simp [hz, hz', smul_add]

end LinearOuterMaps

section AssociativityNaturality
variable {S : Type*} [Ring S] [Module Sᵐᵒᵖ B] [Module S C]
variable [Module Sᵐᵒᵖ (Tensor R A B)] [Module R (Tensor S B C)]
variable (hRight : ∀ (s : S) (a : A) (b : B),
  MulOpposite.op s • tmul R a b = tmul R a (MulOpposite.op s • b))
variable (hLeft : ∀ (r : R) (b : B) (c : C),
  r • tmul S b c = tmul S (r • b) c)
variable {A' B' C' : Type*} [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module Rᵐᵒᵖ A'] [Module R B'] [Module Sᵐᵒᵖ B'] [Module S C']
variable [Module Sᵐᵒᵖ (Tensor R A' B')] [Module R (Tensor S B' C')]
variable (hRight' : ∀ (s : S) (a : A') (b : B'),
  MulOpposite.op s • tmul R a b = tmul R a (MulOpposite.op s • b))
variable (hLeft' : ∀ (r : R) (b : B') (c : C'),
  r • tmul S b c = tmul S (r • b) c)

/-- Naturality for all three module maps. `F` and `G` are their induced inner
maps, with the commuting scalar actions retained. -/
theorem assocWith_natural (f : A →ₗ[Rᵐᵒᵖ] A') (g : B → B') (h : C →ₗ[S] C')
    (F : Tensor R A B →ₗ[Sᵐᵒᵖ] Tensor R A' B')
    (G : Tensor S B C →ₗ[R] Tensor S B' C')
    (hF : ∀ a b, F (tmul R a b) = tmul R (f a) (g b))
    (hG : ∀ b c, G (tmul S b c) = tmul S (g b) (h c))
    (z : Tensor S (Tensor R A B) C) :
    assocWith hRight' hLeft' (map F h z) = map f G (assocWith hRight hLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hF, hG]
    | ha x x' hx hx' =>
      simp only [map_tmul] at hx hx'
      simp [add_tmul, hx, hx']
  | ha z z' hz hz' => simp [hz, hz']

variable {T : Type*} [Ring T]

theorem assocWith_leftScale [Module T A] [SMulCommClass T Rᵐᵒᵖ A]
    [Module T (Tensor R A B)] [SMulCommClass T Sᵐᵒᵖ (Tensor R A B)]
    (hT : ∀ (t : T) (a : A) (b : B), t • tmul R a b = tmul R (t • a) b)
    (t : T) (z : Tensor S (Tensor R A B) C) :
    assocWith hRight hLeft (leftScale t z) = leftScale t (assocWith hRight hLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hT]
    | ha x x' hx hx' =>
      simp only [leftScale_tmul] at hx hx'
      simp [add_tmul, hx, hx']
  | ha z z' hz hz' => simp [hz, hz']

theorem assocWith_rightScale [Module T C] [SMulCommClass T S C]
    [Module T (Tensor S B C)] [SMulCommClass T R (Tensor S B C)]
    (hT : ∀ (t : T) (b : B) (c : C), t • tmul S b c = tmul S b (t • c))
    (t : T) (z : Tensor S (Tensor R A B) C) :
    assocWith hRight hLeft (rightScale t z) = rightScale t (assocWith hRight hLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hT]
    | ha x x' hx hx' =>
      simp only [rightScale_tmul] at hx hx'
      simp [add_tmul, hx, hx']
  | ha z z' hz hz' => simp [hz, hz']

end AssociativityNaturality

section SumNaturality
open DirectSum
variable {ι : Type*} [DecidableEq ι]
variable {M M' : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (M' i)]
variable {S : Type*} [Ring S] [∀ i, Module S (M i)] [∀ i, Module S (M' i)]

/-- The homomorphism of arbitrary direct sums induced by a family of maps. -/
def sumMap (f : ∀ i, M i →ₗ[S] M' i) : (⨁ i, M i) →ₗ[S] ⨁ i, M' i :=
  DirectSum.toModule S ι _ (fun i => (DirectSum.lof S ι M' i).comp (f i))

@[simp] theorem sumMap_of (f : ∀ i, M i →ₗ[S] M' i) (i : ι) (a : M i) :
    sumMap f (DirectSum.of M i a) = DirectSum.of M' i (f i a) := by
  unfold sumMap
  change (DirectSum.toModule S ι _ _) (DirectSum.lof S ι M i a) = _
  rw [DirectSum.toModule_lof]
  rfl

variable [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, Module Rᵐᵒᵖ (M' i)]
variable {B' : Type*} [AddCommGroup B'] [Module R B']

theorem directSumLeft_natural (f : ∀ i, M i →ₗ[Rᵐᵒᵖ] M' i) (g : B →ₗ[R] B')
    (z : Tensor R (⨁ i, M i) B) :
    directSumLeft (map (sumMap f) g z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (map (f i) g))
        (directSumLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => simp
    | add a a' ha ha' =>
      simp only [map_tmul] at ha ha'
      simp [add_tmul, ha, ha']
  | ha z z' hz hz' => simp [hz, hz']

variable {N N' : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, AddCommGroup (N' i)]
variable [∀ i, Module R (N i)] [∀ i, Module R (N' i)]
variable {A' : Type*} [AddCommGroup A'] [Module Rᵐᵒᵖ A']

theorem directSumRight_natural (f : A →ₗ[Rᵐᵒᵖ] A') (g : ∀ i, N i →ₗ[R] N' i)
    (z : Tensor R A (⨁ i, N i)) :
    directSumRight (map f (sumMap g) z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (map f (g i)))
        (directSumRight z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => simp
    | add b b' hb hb' =>
      simp only [map_tmul] at hb hb'
      simp [tmul_add, hb, hb']
  | ha z z' hz hz' => simp [hz, hz']

end SumNaturality


section SumOuterActions
open DirectSum
variable {ι T : Type*} [DecidableEq ι] [Ring T]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module Rᵐᵒᵖ (M i)]

theorem directSumLeft_leftScale [∀ i, Module T (M i)]
    [∀ i, SMulCommClass T Rᵐᵒᵖ (M i)] (t : T) (z : Tensor R (⨁ i, M i) B) :
    directSumLeft (leftScale t z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (leftScale t))
        (directSumLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => simp [← DirectSum.of_smul]
    | add a a' ha ha' =>
      simp only [leftScale_tmul] at ha ha'
      simp [add_tmul, ha, ha']
  | ha z z' hz hz' => simp [hz, hz']

theorem directSumLeft_rightScale [Module T B] [SMulCommClass T R B]
    (t : T) (z : Tensor R (⨁ i, M i) B) :
    directSumLeft (rightScale t z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (rightScale t))
        (directSumLeft z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => simp
    | add a a' ha ha' =>
      simp only [rightScale_tmul] at ha ha'
      simp [add_tmul, ha, ha']
  | ha z z' hz hz' => simp [hz, hz']

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem directSumRight_leftScale [Module T A] [SMulCommClass T Rᵐᵒᵖ A]
    (t : T) (z : Tensor R A (⨁ i, N i)) :
    directSumRight (leftScale t z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (leftScale t))
        (directSumRight z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => simp
    | add b b' hb hb' =>
      simp only [leftScale_tmul] at hb hb'
      simp [tmul_add, hb, hb']
  | ha z z' hz hz' => simp [hz, hz']

theorem directSumRight_rightScale [∀ i, Module T (N i)] [∀ i, SMulCommClass T R (N i)]
    (t : T) (z : Tensor R A (⨁ i, N i)) :
    directSumRight (rightScale t z) =
      DirectSum.toAddMonoid (fun i => (DirectSum.of _ i).comp (rightScale t))
        (directSumRight z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => simp [← DirectSum.of_smul]
    | add b b' hb hb' =>
      simp only [rightScale_tmul] at hb hb'
      simp [tmul_add, hb, hb']
  | ha z z' hz hz' => simp [hz, hz']

end SumOuterActions

/-- Zero factors are included, without an extra nontriviality hypothesis. -/
theorem eq_zero_of_subsingleton_left [Subsingleton A] (z : Tensor R A B) : z = 0 :=
  Subsingleton.elim _ _

theorem eq_zero_of_subsingleton_right [Subsingleton B] (z : Tensor R A B) : z = 0 :=
  Subsingleton.elim _ _

theorem eq_zero_of_zero_ring [Subsingleton R] (z : Tensor R A B) : z = 0 := by
  letI : Subsingleton B := Module.subsingleton R B
  exact eq_zero_of_subsingleton_right z

/-! Closed witnesses for the independent specifications. -/
open DirectSum

theorem satisfiesPairLaws : Specification.ExpectedPairLaws := by
  intro R _ A B _ _ _ _
  exact pairLaws

theorem satisfiesUniversal : Specification.ExpectedUniversal := by
  intro R _ A B C _ _ _ _ _
  exact universal

theorem satisfiesGeneration : Specification.ExpectedGeneration := by
  intro R _ A B _ _ _ _
  exact generation

theorem satisfiesMaps : Specification.ExpectedMaps := by
  intro R _ A B A' B' _ _ _ _ _ _ _ _ f g
  refine ⟨map f g, map_tmul f g, ?_⟩
  intro F hF
  apply hom_ext
  intro a b
  exact (hF a b).trans (map_tmul f g a b).symm

theorem satisfiesRightUnit : Specification.ExpectedRightUnit := by
  intro R _ A _ _
  exact ⟨rightUnit, rightUnit_tmul, rightUnit_symm⟩

theorem satisfiesLeftUnit : Specification.ExpectedLeftUnit := by
  intro R _ B _ _
  exact ⟨leftUnit, leftUnit_tmul, leftUnit_symm⟩

theorem satisfiesLeftScalars : Specification.ExpectedLeftScalars := by
  intro R _ A B _ _ _ _ S _ _ _
  exact ⟨leftModule, fun _ _ _ => rfl⟩

theorem satisfiesRightScalars : Specification.ExpectedRightScalars := by
  intro R _ A B _ _ _ _ S _ _ _
  exact ⟨rightModule, fun _ _ _ => rfl⟩

theorem satisfiesAssociativity : (
∀ (R : Type u) [Ring R] (S : Type*) [Ring S]
    (A : Type v) (B : Type w) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module S C]
    [SMulCommClass Sᵐᵒᵖ R B],
    ∃ (mS : Module Sᵐᵒᵖ (Tensor R A B)) (mR : Module R (Tensor S B C)),
      letI := mS
      letI := mR
      (∀ (s : S) (a : A) (b : B), MulOpposite.op s • tmul R a b = tmul R a (MulOpposite.op s • b)) ∧
      (∀ (r : R) (b : B) (c : C), r • tmul S b c = tmul S (r • b) c) ∧
      ∃ e : Tensor S (Tensor R A B) C ≃+ Tensor R A (Tensor S B C),
        (∀ a b c, e (tmul S (tmul R a b) c) = tmul R a (tmul S b c)) ∧
        (∀ a b c, e.symm (tmul R a (tmul S b c)) = tmul S (tmul R a b) c)
) := by
  intro R _ S _ A B C _ _ _ _ _ _ _ _
  letI : SMulCommClass R Sᵐᵒᵖ B := SMulCommClass.symm _ _ _
  letI mS : Module Sᵐᵒᵖ (Tensor R A B) := rightModule
  letI mR : Module R (Tensor S B C) := leftModule
  have hS : ∀ (s : S) (a : A) (b : B),
      MulOpposite.op s • tmul R a b = tmul R a (MulOpposite.op s • b) := fun _ _ _ => rfl
  have hR : ∀ (r : R) (b : B) (c : C),
      r • tmul S b c = tmul S (r • b) c := fun _ _ _ => rfl
  exact ⟨mS, mR, hS, hR, assocWith hS hR,
    assocWith_tmul hS hR, assocWith_symm_tmul hS hR⟩

theorem satisfiesDirectSumLeft : (
by
  classical
  exact ∀ (R : Type u) [Ring R] (ι : Type*) (M : ι → Type v) (B : Type w)
    [∀ i, AddCommGroup (M i)] [AddCommGroup B]
    [∀ i, Module Rᵐᵒᵖ (M i)] [Module R B],
    ∃ e : Tensor R (⨁ i, M i) B ≃+ ⨁ i, Tensor R (M i) B,
      (∀ i a b, e (tmul R (DirectSum.of M i a) b) =
        DirectSum.of (fun i => Tensor R (M i) B) i (tmul R a b)) ∧
      (∀ i a b, e.symm (DirectSum.of (fun i => Tensor R (M i) B) i (tmul R a b)) =
        tmul R (DirectSum.of M i a) b)
) := by
  classical
  intro R _ ι M B _ _ _ _
  refine ⟨directSumLeft, directSumLeft_tmul_of, ?_⟩
  intro i a b
  simp [DirectSum.lof_eq_of]

theorem satisfiesDirectSumRight : (
by
  classical
  exact ∀ (R : Type u) [Ring R] (ι : Type*) (A : Type v) (N : ι → Type w)
    [AddCommGroup A] [∀ i, AddCommGroup (N i)]
    [Module Rᵐᵒᵖ A] [∀ i, Module R (N i)],
    ∃ e : Tensor R A (⨁ i, N i) ≃+ ⨁ i, Tensor R A (N i),
      (∀ i a b, e (tmul R a (DirectSum.of N i b)) =
        DirectSum.of (fun i => Tensor R A (N i)) i (tmul R a b)) ∧
      (∀ i a b, e.symm (DirectSum.of (fun i => Tensor R A (N i)) i (tmul R a b)) =
        tmul R a (DirectSum.of N i b))
) := by
  classical
  intro R _ ι A N _ _ _ _
  refine ⟨directSumRight, directSumRight_tmul_of, ?_⟩
  intro i a b
  simp [DirectSum.lof_eq_of]

theorem satisfiesCommutativeComparison : Specification.ExpectedCommutativeComparison := by
  intro K _ A B _ _ _ _
  letI := commRightModule K A
  letI : IsCentralScalar K A := ⟨fun _ _ => rfl⟩
  letI m : Module K (Tensor K A B) := rightModule
  refine ⟨m, (fun _ _ _ => rfl), ?_, commLinearEquiv,
    commAddEquiv_tmul, commAddEquiv_symm_tmul⟩
  intro r a b
  exact (balance r a b).symm


theorem satisfiesBimoduleActions : (
∀ (R : Type*) [Ring R] (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module R B] (S T : Type*) [Ring S] [Ring T]
    [Module S A] [Module T B] [SMulCommClass S Rᵐᵒᵖ A] [SMulCommClass T R B],
    ∃ (mS : Module S (Tensor R A B)) (mT : Module T (Tensor R A B)),
      letI := mS
      letI := mT
      SMulCommClass S T (Tensor R A B) ∧
      (∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b) ∧
      (∀ (t : T) (a : A) (b : B), t • tmul R a b = tmul R a (t • b))
) := by
  intro R _ A B _ _ _ _ S T _ _ _ _ _ _
  letI mS : Module S (Tensor R A B) := leftModule
  letI mT : Module T (Tensor R A B) := rightModule
  exact ⟨mS, mT, outerCommClass, (fun _ _ _ => rfl), (fun _ _ _ => rfl)⟩

theorem satisfiesLeftLinearity : (
∀ (R S : Type*) [Ring R] [Ring S] (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module S A] [Module S C]
    [Module S (Tensor R A B)]
    (hT : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b)
    (f : Pairing R (A := A) (B := B) C)
    (hf : ∀ (s : S) (a : A) (b : B), f.toBiadditive (s • a) b = s • f.toBiadditive a b)
    (g : Tensor R A B →+ C) (hg : ∀ a b, g (tmul R a b) = f.toBiadditive a b),
    ∀ (s : S) z, g (s • z) = s • g z
) := by
  intro R S _ _ A B C _ _ _ _ _ _ _ _ hT f hf g hg s z
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hT, hg, hf]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesRightLinearity : (
∀ (R S : Type*) [Ring R] [Ring S] (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module R B] [Module S B] [Module S C]
    [Module S (Tensor R A B)]
    (hT : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))
    (f : Pairing R (A := A) (B := B) C)
    (hf : ∀ (s : S) (a : A) (b : B), f.toBiadditive a (s • b) = s • f.toBiadditive a b)
    (g : Tensor R A B →+ C) (hg : ∀ a b, g (tmul R a b) = f.toBiadditive a b),
    ∀ (s : S) z, g (s • z) = s • g z
) := by
  intro R S _ _ A B C _ _ _ _ _ _ _ _ hT f hf g hg s z
  induction z using induction_on with
  | h0 => simp
  | ht a b => simp [hT, hg, hf]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesRightUnitNaturality : (
∀ (R : Type*) [Ring R] (A A' : Type*) [AddCommGroup A] [AddCommGroup A']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] (f : A →ₗ[Rᵐᵒᵖ] A')
    (F : Tensor R A R →+ Tensor R A' R)
    (hF : ∀ a r, F (tmul R a r) = tmul R (f a) r)
    (e : Tensor R A R →+ A) (he : ∀ a r, e (tmul R a r) = MulOpposite.op r • a)
    (e' : Tensor R A' R →+ A') (he' : ∀ a r, e' (tmul R a r) = MulOpposite.op r • a),
    ∀ z, e' (F z) = f (e z)
) := by
  intro R _ A A' _ _ _ _ f F hF e he e' he' z
  induction z using induction_on with
  | h0 => simp
  | ht a r => simp [hF, he, he']
  | ha z z' hz hz' => simp [hz, hz']

theorem satisfiesLeftUnitNaturality : (
∀ (R : Type*) [Ring R] (B B' : Type*) [AddCommGroup B] [AddCommGroup B']
    [Module R B] [Module R B'] (g : B →ₗ[R] B')
    (F : Tensor R R B →+ Tensor R R B')
    (hF : ∀ r b, F (tmul R r b) = tmul R r (g b))
    (e : Tensor R R B →+ B) (he : ∀ r b, e (tmul R r b) = r • b)
    (e' : Tensor R R B' →+ B') (he' : ∀ r b, e' (tmul R r b) = r • b),
    ∀ z, e' (F z) = g (e z)
) := by
  intro R _ B B' _ _ _ _ g F hF e he e' he' z
  induction z using induction_on with
  | h0 => simp
  | ht r b => simp [hF, he, he']
  | ha z z' hz hz' => simp [hz, hz']

theorem satisfiesAssociativityNaturality : (
∀ (R S : Type*) [Ring R] [Ring S] (A B C A' B' C' : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module Rᵐᵒᵖ A] [Module R B] [Module Sᵐᵒᵖ B] [Module S C]
    [Module Rᵐᵒᵖ A'] [Module R B'] [Module Sᵐᵒᵖ B'] [Module S C']
    [Module Sᵐᵒᵖ (Tensor R A B)] [Module R (Tensor S B C)]
    [Module Sᵐᵒᵖ (Tensor R A' B')] [Module R (Tensor S B' C')]
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →+ B') (h : C →ₗ[S] C')
    (e : Tensor S (Tensor R A B) C →+ Tensor R A (Tensor S B C))
    (he : ∀ a b c, e (tmul S (tmul R a b) c) = tmul R a (tmul S b c))
    (e' : Tensor S (Tensor R A' B') C' →+ Tensor R A' (Tensor S B' C'))
    (he' : ∀ a b c, e' (tmul S (tmul R a b) c) = tmul R a (tmul S b c))
    (H : Tensor S (Tensor R A B) C →+ Tensor S (Tensor R A' B') C')
    (hH : ∀ a b c, H (tmul S (tmul R a b) c) = tmul S (tmul R (f a) (g b)) (h c))
    (K : Tensor R A (Tensor S B C) →+ Tensor R A' (Tensor S B' C'))
    (hK : ∀ a b c, K (tmul R a (tmul S b c)) = tmul R (f a) (tmul S (g b) (h c))),
    ∀ z, e' (H z) = K (e z)
) := by
  intro R S _ _ A B C A' B' C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g h e he e' he' H hH K hK z
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hH, he, he', hK]
    | ha x x' hx hx' => simp [add_tmul, hx, hx']
  | ha z z' hz hz' => simp [hz, hz']

theorem satisfiesDirectSumLeftNaturality : (
by
  classical
  exact ∀ (R : Type*) [Ring R] (ι : Type*) (M M' : ι → Type*) (B B' : Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (M' i)] [AddCommGroup B] [AddCommGroup B']
    [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, Module Rᵐᵒᵖ (M' i)] [Module R B] [Module R B']
    (f : ∀ i, M i →ₗ[Rᵐᵒᵖ] M' i) (g : B →ₗ[R] B')
    (e : Tensor R (⨁ i, M i) B →+ ⨁ i, Tensor R (M i) B)
    (he : ∀ i a b, e (tmul R (DirectSum.of M i a) b) = DirectSum.of _ i (tmul R a b))
    (e' : Tensor R (⨁ i, M' i) B' →+ ⨁ i, Tensor R (M' i) B')
    (he' : ∀ i a b, e' (tmul R (DirectSum.of M' i a) b) = DirectSum.of _ i (tmul R a b))
    (H : Tensor R (⨁ i, M i) B →+ Tensor R (⨁ i, M' i) B')
    (hH : ∀ i a b, H (tmul R (DirectSum.of M i a) b) =
      tmul R (DirectSum.of M' i (f i a)) (g b))
    (D : (⨁ i, Tensor R (M i) B) →+ ⨁ i, Tensor R (M' i) B')
    (hD : ∀ i a b, D (DirectSum.of _ i (tmul R a b)) =
      DirectSum.of _ i (tmul R (f i a) (g b))),
    ∀ z, e' (H z) = D (e z)
) := by
  classical
  intro R _ ι M M' B B' _ _ _ _ _ _ _ _ f g e he e' he' H hH D hD z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => simp [hH, he, he', hD]
    | add a a' ha ha' => simp [add_tmul, ha, ha']
  | ha z z' hz hz' => simp [hz, hz']

theorem satisfiesDirectSumRightNaturality : (
by
  classical
  exact ∀ (R : Type*) [Ring R] (ι : Type*) (A A' : Type*) (N N' : ι → Type*)
    [AddCommGroup A] [AddCommGroup A'] [∀ i, AddCommGroup (N i)] [∀ i, AddCommGroup (N' i)]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [∀ i, Module R (N i)] [∀ i, Module R (N' i)]
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : ∀ i, N i →ₗ[R] N' i)
    (e : Tensor R A (⨁ i, N i) →+ ⨁ i, Tensor R A (N i))
    (he : ∀ i a b, e (tmul R a (DirectSum.of N i b)) = DirectSum.of _ i (tmul R a b))
    (e' : Tensor R A' (⨁ i, N' i) →+ ⨁ i, Tensor R A' (N' i))
    (he' : ∀ i a b, e' (tmul R a (DirectSum.of N' i b)) = DirectSum.of _ i (tmul R a b))
    (H : Tensor R A (⨁ i, N i) →+ Tensor R A' (⨁ i, N' i))
    (hH : ∀ i a b, H (tmul R a (DirectSum.of N i b)) =
      tmul R (f a) (DirectSum.of N' i (g i b)))
    (D : (⨁ i, Tensor R A (N i)) →+ ⨁ i, Tensor R A' (N' i))
    (hD : ∀ i a b, D (DirectSum.of _ i (tmul R a b)) =
      DirectSum.of _ i (tmul R (f a) (g i b))),
    ∀ z, e' (H z) = D (e z)
) := by
  classical
  intro R _ ι A A' N N' _ _ _ _ _ _ _ _ f g e he e' he' H hH D hD z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => simp [hH, he, he', hD]
    | add b b' hb hb' => simp [tmul_add, hb, hb']
  | ha z z' hz hz' => simp [hz, hz']

theorem satisfiesDirectSumLeftFirstLinearity :
    Specification.ExpectedDirectSumLeftFirstLinearity := by
  classical
  intro R T _ _ ι M B _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => rw [hSource, he, he, hTarget]
    | add a a' ha ha' => simp [add_tmul, smul_add, ha, ha']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesDirectSumLeftSecondLinearity :
    Specification.ExpectedDirectSumLeftSecondLinearity := by
  classical
  intro R T _ _ ι M B _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i a => rw [hSource, he, he, hTarget]
    | add a a' ha ha' => simp [add_tmul, smul_add, ha, ha']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesDirectSumRightFirstLinearity :
    Specification.ExpectedDirectSumRightFirstLinearity := by
  classical
  intro R T _ _ ι A N _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => rw [hSource, he, he, hTarget]
    | add b b' hb hb' => simp [tmul_add, smul_add, hb, hb']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesDirectSumRightSecondLinearity :
    Specification.ExpectedDirectSumRightSecondLinearity := by
  classical
  intro R T _ _ ι A N _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of i b => rw [hSource, he, he, hTarget]
    | add b b' hb hb' => simp [tmul_add, smul_add, hb, hb']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesRightUnitLeftLinearity : Specification.ExpectedRightUnitLeftLinearity := by
  intro R S _ _ A _ _ _ _ _ hT e he s z
  induction z using induction_on with
  | h0 => simp
  | ht a r => simp [hT, he, smul_comm s]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesRightUnitRightLinearity : Specification.ExpectedRightUnitRightLinearity := by
  intro R _ A _ _ _ hT e he s z
  induction z using induction_on with
  | h0 => simp
  | ht a r => simp [hT, he, smul_smul]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesLeftUnitLeftLinearity : Specification.ExpectedLeftUnitLeftLinearity := by
  intro R _ B _ _ _ hT e he r z
  induction z using induction_on with
  | h0 => simp
  | ht s b => simp [hT, he, smul_smul]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesLeftUnitRightLinearity : Specification.ExpectedLeftUnitRightLinearity := by
  intro R S _ _ B _ _ _ _ _ hT e he s z
  induction z using induction_on with
  | h0 => simp
  | ht r b => simp [hT, he, smul_comm s]
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesAssociativityLeftEquivariance :
    Specification.ExpectedAssociativityLeftEquivariance := by
  intro R S T _ _ _ A B C _ _ _ _ _ _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hSource, he, hTarget]
    | ha x x' hx hx' => simp [add_tmul, smul_add, hx, hx']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

theorem satisfiesAssociativityRightEquivariance :
    Specification.ExpectedAssociativityRightEquivariance := by
  intro R S T _ _ _ A B C _ _ _ _ _ _ _ _ _ _ _ _ hSource hTarget e he t z
  induction z using induction_on with
  | h0 => simp
  | ht x c =>
    induction x using induction_on with
    | h0 => simp
    | ht a b => simp [hSource, he, hTarget]
    | ha x x' hx hx' => simp [add_tmul, smul_add, hx, hx']
  | ha z z' hz hz' => simp [smul_add, hz, hz']

end P103.BalancedTensor
