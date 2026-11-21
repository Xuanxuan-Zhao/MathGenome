import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M05.DetInvertible
import Mathlib.LinearAlgebra.Determinant
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification for K05.05.orientation, paper.tex:905–906.
An ordered basis is indexed by `Fin n`; its existence already implies finite
dimension, so no extra finite-dimensional or nonzero-dimensional assumption
is imposed. `changeMatrix_value b c` has the vectors of `c` as columns in `b`.
Classes are the quotient of ordered bases by positive conversion determinant.
In particular this quotient has ONE element for n = 0 (unlike the two rays in
Mathlib's alternating-form `Orientation` type).
-/

noncomputable section

namespace Specs.D05.M05.Orientation

open Specs.D05.M04.ChangeBasis _root_.D05.M05

universe u

def sameOrientation_type : Type (u + 1) :=
  {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n : ℕ} →
    Module.Basis (Fin n) ℝ V → Module.Basis (Fin n) ℝ V → Prop

noncomputable def sameOrientation_value : sameOrientation_type.{u} :=
  fun b c => 0 < determinant (changeMatrix_value b c)

def classes_type : Type (u + 1) :=
  (V : Type u) → [AddCommGroup V] → [Module ℝ V] → ℕ → Type u

/-- `Quot` constructs the relation quotient without assuming its equivalence
properties; those, and exactness of class equality, are proof obligations. -/
def classes_value : classes_type.{u} :=
  fun V _ _ n => Quot (@sameOrientation_value V _ _ n)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- Class of a specified ordered basis. -/
def classOf_value (b : Module.Basis (Fin n) ℝ V) : classes_value V n :=
  Quot.mk _ b

/-- The conversion determinant is exactly the determinant of the new basis
in the old one, using the upstream Leibniz determinant and matrix convention. -/
def conversion_det_basis : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    determinant (changeMatrix_value b c) = b.det c

def conversion_det_self : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V), determinant (changeMatrix_value b b) = 1

def conversion_det_ne_zero : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V), determinant (changeMatrix_value b c) ≠ 0

def conversion_det_comp : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c d : Module.Basis (Fin n) ℝ V),
    determinant (changeMatrix_value b c) * determinant (changeMatrix_value c d) =
      determinant (changeMatrix_value b d)

def conversion_det_inverse : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    determinant (changeMatrix_value c b) = (determinant (changeMatrix_value b c))⁻¹

/-- Reflexivity, symmetry, and transitivity, with no extra premise. -/
def sameOrientation_equivalence : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] (n : ℕ),
    Equivalence (@sameOrientation_value V _ _ n)

def class_eq_iff : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    classOf_value b = classOf_value c ↔ sameOrientation_value b c

def sign_dichotomy : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    0 < determinant (changeMatrix_value b c) ∨ determinant (changeMatrix_value b c) < 0

def different_iff_det_neg : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    classOf_value b ≠ classOf_value c ↔ determinant (changeMatrix_value b c) < 0

/-- The constructed basis negates exactly the chosen vector; in particular,
this provides the sign-changing operation when n = 1. -/
def negate_one_apply : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (i j : Fin n),
    b.unitsSMul (Function.update 1 i (-1)) j = if j = i then -b j else b j

def negate_one_det : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (i : Fin n),
    determinant (changeMatrix_value b (b.unitsSMul (Function.update 1 i (-1)))) = -1

/-- Interchanging any two distinct positions reverses the sign. Such indices
exist precisely when n ≥ 2; no such premise is imposed for n = 1. -/
def swap_det : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (i j : Fin n), i ≠ j →
    determinant (changeMatrix_value b (b.reindex (Equiv.swap i j))) = -1

/-- Concrete representatives of both classes, with an exhaustive alternative. -/
def two_classes_representatives : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (i : Fin n),
    classOf_value b ≠ classOf_value (b.unitsSMul (Function.update 1 i (-1))) ∧
    ∀ o : classes_value V n,
      o = classOf_value b ∨ o = classOf_value (b.unitsSMul (Function.update 1 i (-1)))

/-- Every positive-dimensional real space has exactly two classes. The
specified basis expresses its dimension n without choosing coordinates anew. -/
def exactly_two_classes : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (_b : Module.Basis (Fin n) ℝ V), 0 < n → Nat.card (classes_value V n) = 2

def zero_unique_basis : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b c : Module.Basis (Fin 0) ℝ V), b = c

def zero_one_class : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (_b : Module.Basis (Fin 0) ℝ V), Nat.card (classes_value V 0) = 1

/-- A formulation for every finite-dimensional real space, without a basis
as an input. The canonical finite basis is used only in the proof. -/
def dimension_class_count : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
    Nat.card (classes_value V (Module.finrank ℝ V)) =
      if Module.finrank ℝ V = 0 then 1 else 2

/-- Includes singular-free zero dimension, where the conversion determinant
and the endomorphism determinant are both one. -/
def conversion_map_det : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V ≃ₗ[ℝ] V),
    determinant (changeMatrix_value b (b.map T)) = LinearMap.det T.toLinearMap

def preserves_iff_det_pos : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V ≃ₗ[ℝ] V),
    classOf_value (b.map T) = classOf_value b ↔ 0 < LinearMap.det T.toLinearMap

def reverses_iff_det_neg : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V ≃ₗ[ℝ] V),
    classOf_value (b.map T) ≠ classOf_value b ↔ LinearMap.det T.toLinearMap < 0

/-- The sign criterion is uniform over all bases, so preservation is a
property of the operator, independent of a chosen reference orientation. -/
def preserves_all_iff_det_pos : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (_b : Module.Basis (Fin n) ℝ V) (T : V ≃ₗ[ℝ] V),
    (∀ c : Module.Basis (Fin n) ℝ V, classOf_value (c.map T) = classOf_value c) ↔
      0 < LinearMap.det T.toLinearMap

def reverses_all_iff_det_neg : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (_b : Module.Basis (Fin n) ℝ V) (T : V ≃ₗ[ℝ] V),
    (∀ c : Module.Basis (Fin n) ℝ V, classOf_value (c.map T) ≠ classOf_value c) ↔
      LinearMap.det T.toLinearMap < 0

end Specs.D05.M05.Orientation
