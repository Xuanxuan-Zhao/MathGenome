import MathGenome.Internal.Specs.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
import Mathlib.Algebra.Module.RingHom

/-!
The operator/polynomial-module correspondence, without any finiteness
assumption. Polynomial evaluation takes values in the generally
noncommutative ring of F-linear endomorphisms. Its coefficient map is
central because those endomorphisms are F-linear.
-/

universe u v w

namespace D07.Ch16.OperatorBridgePolynomialModuleCorrespondence

open Polynomial
open Specs.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

/-- Pull back the natural endomorphism action along evaluation at T. -/
noncomputable abbrev evaluatedModule (T : Module.End F V) : Module (Polynomial F) V :=
  Module.compHom V (aeval T).toRingHom

lemma evaluatedModule_smul (T : Module.End F V) (f : Polynomial F) (x : V) :
    (evaluatedModule T).smul f x = (aeval T f) x := rfl

lemma evaluatedModule_compatible (T : Module.End F V) :
    CompatibleAction F V (evaluatedModule T) := by
  intro a x
  rw [evaluatedModule_smul, aeval_C]
  rfl

lemma evaluatedModule_X (T : Module.End F V) (x : V) :
    (evaluatedModule T).smul X x = T x := by
  rw [evaluatedModule_smul, aeval_X]

omit [Module F V] in
/-- Polynomial actions are determined by constants and the generator. -/
lemma action_ext (m n : Module (Polynomial F) V)
    (hC : ∀ (a : F) (x : V), m.smul (C a) x = n.smul (C a) x)
    (hX : ∀ x : V, m.smul X x = n.smul X x) : m = n := by
  apply Module.ext'
  intro f
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    intro x
    exact (m.add_smul f g x).trans ((congrArg₂ (· + ·) (hf x) (hg x)).trans
      (n.add_smul f g x).symm)
  | monomial k a hk =>
    intro x
    rw [pow_succ, ← mul_assoc]
    exact (m.mul_smul _ _ x).trans ((hk _).trans
      ((congrArg (n.smul (C a * X ^ k)) (hX x)).trans (n.mul_smul _ _ x).symm))

theorem operatorToModule : OperatorToModule.{u, v} := by
  intro F _ V _ _ T
  refine ⟨evaluatedModule T, ⟨evaluatedModule_compatible T, evaluatedModule_X T⟩, ?_⟩
  intro m hm
  exact action_ext m (evaluatedModule T)
    (fun a x => (hm.1 a x).trans (evaluatedModule_compatible T a x).symm)
    (fun x => (hm.2 x).trans (evaluatedModule_X T x).symm)

/-- X acts F-linearly because it commutes with every constant polynomial. -/
noncomputable def generatorOperator (m : Module (Polynomial F) V) (hm : CompatibleAction F V m) :
    Module.End F V where
  toFun := m.smul X
  map_add' x y := m.smul_add X x y
  map_smul' a x := by
    change m.smul X (a • x) = a • m.smul X x
    calc
      m.smul X (a • x) = m.smul X (m.smul (C a) x) :=
        congrArg (m.smul X) (hm a x).symm
      _ = m.smul (X * C a) x := (m.mul_smul X (C a) x).symm
      _ = m.smul (C a * X) x := by rw [X_mul_C]
      _ = m.smul (C a) (m.smul X x) := m.mul_smul (C a) X x
      _ = a • m.smul X x := hm a _

theorem moduleToOperator : ModuleToOperator.{u, v} := by
  intro F _ V _ _ m hm
  refine ⟨generatorOperator m hm, fun _ => rfl, ?_⟩
  intro T hT
  ext x
  exact hT x

theorem actionFormula : ActionFormula.{u, v} := by
  intro F _ V _ _ T m hm hX f x
  have heq : m = evaluatedModule T := action_ext m (evaluatedModule T)
    (fun a y => (hm a y).trans (evaluatedModule_compatible T a y).symm)
    (fun y => (hX y).trans (evaluatedModule_X T y).symm)
  rw [heq]
  rfl

variable {W : Type w} [AddCommGroup W] [Module F W]

/-- Intertwining X and preserving field scalars forces preservation of
all polynomial actions, by the finite polynomial expansion. -/
lemma intertwiner_smul (T : Module.End F V) (S : Module.End F W)
    (m : Module (Polynomial F) V) (n : Module (Polynomial F) W)
    (hm : CompatibleAction F V m) (hn : CompatibleAction F W n)
    (hX : ∀ x : V, m.smul X x = T x) (hY : ∀ y : W, n.smul X y = S y)
    (e : V →ₗ[F] W) (he : ∀ x : V, e (T x) = S (e x))
    (f : Polynomial F) : ∀ x : V, e (m.smul f x) = n.smul f (e x) := by
  induction f using Polynomial.induction_on with
  | C a =>
    intro x
    rw [hm, hn, e.map_smul]
  | add f g hf hg =>
    intro x
    calc
      e (m.smul (f + g) x) = e (m.smul f x + m.smul g x) :=
        congrArg e (m.add_smul f g x)
      _ = e (m.smul f x) + e (m.smul g x) := e.map_add _ _
      _ = n.smul f (e x) + n.smul g (e x) := congrArg₂ (· + ·) (hf x) (hg x)
      _ = n.smul (f + g) (e x) := (n.add_smul f g (e x)).symm
  | monomial k a hk =>
    intro x
    rw [pow_succ, ← mul_assoc]
    calc
      e (m.smul ((C a * X ^ k) * X) x) =
          e (m.smul (C a * X ^ k) (m.smul X x)) := congrArg e (m.mul_smul _ _ x)
      _ = n.smul (C a * X ^ k) (e (m.smul X x)) := hk _
      _ = n.smul (C a * X ^ k) (n.smul X (e x)) := by rw [hX, he, hY]
      _ = n.smul ((C a * X ^ k) * X) (e x) := (n.mul_smul _ _ (e x)).symm

theorem equivalenceCharacterization : EquivalenceCharacterization.{u, v, w} := by
  intro F _ V _ _ W _ _ T S m n hm hn hX hY h
  let : Module (Polynomial F) V := m
  let : Module (Polynomial F) W := n
  constructor
  · rintro ⟨e, he⟩
    let eF : V ≃ₗ[F] W := {
      e.toAddEquiv with
      map_smul' := fun a x => by
        change e (a • x) = a • e x
        rw [← hm a x, ← hn a (e x)]
        exact e.map_smul (C a) x }
    refine ⟨eF, he, ?_⟩
    intro x
    change e (T x) = S (e x)
    rw [← hX, ← hY]
    exact e.map_smul X x
  · rintro ⟨e, he, hi⟩
    let eP : V ≃ₗ[Polynomial F] W := {
      e.toAddEquiv with
      map_smul' := fun f x =>
        intertwiner_smul T S m n hm hn hX hY e.toLinearMap hi f x }
    exact ⟨eP, he⟩

end D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
