import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedSlTwo
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Trace duality, matrix conjugacy, and transport for the reduced algebras of `sl₂`. -/

namespace Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping
  (reducedEnvelopingValue quotientMapValue)
open _root_.Shared.Lie (inclusion)

universe u

abbrev Mat₂ (k : Type u) := Matrix (Fin 2) (Fin 2) k

/-- The trace functional of a fixed traceless matrix. -/
def tracePairingValue {k : Type u} [Field k] (X : Model k) : Model k →ₗ[k] k where
  toFun Y := Matrix.trace (X.val * Y.val)
  map_add' Y Z := by change Matrix.trace (X.val * (Y.val + Z.val)) = _; rw [mul_add, Matrix.trace_add]
  map_smul' b Y := by
    change Matrix.trace (X.val * (b • Y.val)) = b * Matrix.trace (X.val * Y.val)
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

def tracePairingType := ∀ {k : Type u} [Field k], Model k → (Model k →ₗ[k] k)

/-- Conjugation in the indicated direction, with the matrix unit acting on the left. -/
def IsMatrixConjugation {k : Type u} [Field k] (P : (Mat₂ k)ˣ)
    (c : Model k ≃ₗ⁅k⁆ Model k) : Prop :=
  ∀ X, (c X).val = (P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)

def traceDualityType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p], 2 < p →
    Function.Bijective (tracePairingValue (k := k))

def conjugationType : Prop :=
  ∀ {k : Type u} [Field k] (P : (Mat₂ k)ˣ),
    ∃ c : Model k ≃ₗ⁅k⁆ Model k, IsMatrixConjugation P c

/-- The two conjugacy types of a nonzero character, with their matrix spectra. -/
def characterNormalFormsType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p], 2 < p →
    ∀ χ : Model k →ₗ[k] k, χ ≠ 0 →
      ∃ (X : Model k) (P : (Mat₂ k)ˣ) (c : Model k ≃ₗ⁅k⁆ Model k),
        χ = tracePairingValue X ∧ IsMatrixConjugation P c ∧
        let χ' := χ.comp c.symm.toLinearEquiv.toLinearMap
        χ' = tracePairingValue (c X) ∧
          ((∃ a : k, a ≠ 0 ∧ a ≠ -a ∧ (c X).val = Matrix.diagonal ![a, -a] ∧
            X.val.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C (-a)) ∧
            χ' (E k) = 0 ∧ χ' (F k) = 0 ∧ χ' (H k) = 2 * a ∧ χ' (H k) ≠ 0) ∨
          ((c X) = E k ∧ X.val.charpoly = Polynomial.X ^ 2 ∧
            χ' (E k) = 0 ∧ χ' (H k) = 0 ∧ χ' (F k) = 1))

/-- Conjugation induces an isomorphism on the actual reduced quotients, given on generators. -/
def reducedConjugationType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    (power : restrictedPowerValue k p (Model k)),
    (∀ X, (power.val X).val = X.val ^ p) →
    ∀ (P : (Mat₂ k)ˣ) (c : Model k ≃ₗ⁅k⁆ Model k), IsMatrixConjugation P c →
      ∀ χ : Model k →ₗ[k] k,
        let χ' := χ.comp c.symm.toLinearEquiv.toLinearMap
        ∃ f : reducedEnvelopingValue power χ ≃ₐ[k] reducedEnvelopingValue power χ',
          ∀ X, f (quotientMapValue power χ (inclusion k (Model k) X)) =
            quotientMapValue power χ' (inclusion k (Model k) (c X))


section ModuleTransport

universe v
variable {k : Type u} [Field k] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- A module for a `k`-algebra, recorded as its action on a bundled `k`-vector space. -/
def AlgebraModule (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] :=
  Σ V : ModuleCat.{v} k, A →ₐ[k] Module.End k V

/-- Encode an ordinary compatible module by its action. -/
def AlgebraModule.ofModule (V : Type v) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] : AlgebraModule.{u, v} k A :=
  ⟨ModuleCat.of k V, Algebra.lsmul k k V⟩

/-- Pull back an action along a map of algebras, keeping its underlying vector space. -/
def pullback (f : A →ₐ[k] B) (M : AlgebraModule.{u, v} k B) : AlgebraModule.{u, v} k A :=
  ⟨M.1, M.2.comp f⟩

/-- Ordinary module isomorphism for the actions. -/
def ModuleIsomorphic (M N : AlgebraModule.{u, v} k A) : Prop :=
  ∃ e : M.1 ≃ₗ[k] N.1, ∀ (a : A) (m : M.1), e (M.2 a m) = N.2 a (e m)

def moduleIsoSetoid : Setoid (AlgebraModule.{u, v} k A) where
  r := ModuleIsomorphic
  iseqv := {
    refl M := ⟨LinearEquiv.refl k M.1, fun _ _ => rfl⟩
    symm := by
      rintro M N ⟨e, he⟩
      refine ⟨e.symm, fun a n => e.injective ?_⟩
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    trans := by
      rintro M N L ⟨e, he⟩ ⟨f, hf⟩
      refine ⟨e.trans f, fun a m => ?_⟩
      change f (e (M.2 a m)) = L.2 a (f (e m))
      rw [he, hf] }

abbrev ModuleClass (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] :=
  Quotient (moduleIsoSetoid (k := k) (A := A))

/-- Simplicity of the ordinary module defined by the recorded action. -/
def Simple (M : AlgebraModule.{u, v} k A) : Prop :=
  letI : Module A M.1 := Module.compHom M.1 M.2.toRingHom
  IsSimpleModule A M.1

/-- Transport acts on isomorphism classes in both directions and preserves
simplicity and the dimension of each underlying vector space. -/
def moduleTransportType : Prop :=
  ∀ {k : Type u} [Field k] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : A ≃ₐ[k] B),
    ∃ T : ModuleClass.{u, v} k A ≃ ModuleClass.{u, v} k B,
      (∀ M : AlgebraModule.{u, v} k A,
        T (Quotient.mk _ M) = Quotient.mk _ (pullback f.symm.toAlgHom M) ∧
        (Simple (pullback f.symm.toAlgHom M) ↔ Simple M) ∧
        Module.finrank k (pullback f.symm.toAlgHom M).1 = Module.finrank k M.1) ∧
      (∀ N : AlgebraModule.{u, v} k B,
        T.symm (Quotient.mk _ N) = Quotient.mk _ (pullback f.toAlgHom N) ∧
        (Simple (pullback f.toAlgHom N) ↔ Simple N) ∧
        Module.finrank k (pullback f.toAlgHom N).1 = Module.finrank k N.1)

end ModuleTransport

end Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms
