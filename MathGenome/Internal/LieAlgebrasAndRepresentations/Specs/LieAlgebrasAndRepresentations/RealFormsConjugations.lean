import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Quotients
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.Complex.Module

/-! The general part of LA-J03 (source lines 4695–4714).
No finite-dimensionality or semisimplicity assumption is used. -/

open scoped TensorProduct

universe u v
namespace LieAlgebrasAndRepresentations.RealForms

instance complexLieAlgebraReal (L : Type u) [LieRing L] [LieAlgebra ℂ L] :
    LieAlgebra ℝ L where
  lie_smul t x y := lie_smul (t : ℂ) x y

variable (L : Type u) [LieRing L] [LieAlgebra ℂ L]

/-- A conjugate-linear, bracket-preserving involution. -/
structure Conjugation where
  map : L →ₗ⁅ℝ⁆ L
  antilinear : ∀ (a : ℂ) (x : L), map (a • x) = star a • map x
  involutive : Function.Involutive map

variable {L}

/-- The fixed algebra, with real scalars. -/
def Conjugation.fixed (σ : Conjugation L) : LieSubalgebra ℝ L where
  carrier := {x | σ.map x = x}
  add_mem' {x y} hx hy := by
    change σ.map x = x at hx
    change σ.map y = y at hy
    change σ.map (x + y) = x + y
    rw [map_add, hx, hy]
  zero_mem' := map_zero σ.map
  smul_mem' a x hx := by
    change σ.map x = x at hx
    change σ.map (a • x) = a • x
    rw [map_smul, hx]
  lie_mem' {x y} hx hy := by
    change σ.map x = x at hx
    change σ.map y = y at hy
    change σ.map ⁅x, y⁆ = ⁅x, y⁆
    rw [σ.map.map_lie, hx, hy]

/-- Evaluation of the complexification of a real subalgebra in the ambient algebra. -/
noncomputable def complexifyMap (S : LieSubalgebra ℝ L) : ℂ ⊗[ℝ] S →ₗ⁅ℂ⁆ L :=
  { TensorProduct.AlgebraTensorModule.lift
      { toFun := fun a => a • S.toSubmodule.subtype
        map_add' := by intros; ext; simp [add_smul]
        map_smul' := by intros; ext; simp [smul_smul] } with
    map_lie' := by
      intro x y
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | tmul b y => simp [LieAlgebra.ExtendScalars.bracket_tmul, smul_lie, lie_smul, smul_smul, mul_comm] ; rfl
        | add y z hy hz => simp_all [lie_add]
      | add x y hx hy => simp_all [add_lie] }

/-- The usual embedded real form: its scalar-extension map is bijective. -/
def IsRealForm (S : LieSubalgebra ℝ L) : Prop := Function.Bijective (complexifyMap S)

/-- Coefficient conjugation on an arbitrary complexification. -/
def coefficientConjugationMap (A : Type u) [LieRing A] [LieAlgebra ℝ A] :
    ℂ ⊗[ℝ] A →ₗ⁅ℝ⁆ ℂ ⊗[ℝ] A :=
  LieAlgebra.ExtendScalars.map Complex.conjAe.toAlgHom (LieHom.id : A →ₗ⁅ℝ⁆ A)


variable {H : Type v} [LieRing H] [LieAlgebra ℂ H]

/-- A complex isomorphism intertwines the two conjugations. -/
def Intertwines (σ : Conjugation L) (τ : Conjugation H) (a : L ≃ₗ⁅ℂ⁆ H) : Prop :=
  ∀ x, τ.map (a x) = a (σ.map x)

end LieAlgebrasAndRepresentations.RealForms

namespace Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
open LieAlgebrasAndRepresentations.RealForms
open Complex

/-- The two parts in the source formula, and their reconstruction identity. -/
def fixed_parts_formula_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L) (x : L),
    ∃ u v : σ.fixed,
      (u : L) = (2 : ℂ)⁻¹ • (x + σ.map x) ∧
      (v : L) = ((2 : ℂ) * I)⁻¹ • (x - σ.map x) ∧
      (u : L) + I • (v : L) = x

def fixed_isRealForm_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L),
    IsRealForm σ.fixed

def fixed_complexification_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L),
    ∃ e : (ℂ ⊗[ℝ] σ.fixed) ≃ₗ⁅ℂ⁆ L,
      ∀ a x, e (a ⊗ₜ[ℝ] x) = a • (x : L)

def coefficient_converse_type : Prop :=
  ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A],
    ∃ ρ : Conjugation (ℂ ⊗[ℝ] A),
      ρ.map = coefficientConjugationMap A ∧
      ∃ e : A ≃ₗ⁅ℝ⁆ ρ.fixed,
        ∀ x, (e x : ℂ ⊗[ℝ] A) = (1 : ℂ) ⊗ₜ[ℝ] x

def coefficient_fixed_iff_type : Prop :=
  ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A] (z : ℂ ⊗[ℝ] A),
    coefficientConjugationMap A z = z ↔ ∃ x : A, (1 : ℂ) ⊗ₜ[ℝ] x = z

def real_form_converse_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (S : LieSubalgebra ℝ L), IsRealForm S →
    ∃ τ : Conjugation L, τ.fixed = S ∧
      ∃ e : (ℂ ⊗[ℝ] S) ≃ₗ⁅ℂ⁆ L,
        (∀ a x, e (a ⊗ₜ[ℝ] x) = a • (x : L)) ∧
        ∀ z, τ.map (e z) = e (coefficientConjugationMap S z)

def real_form_iff_conjugation_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (S : LieSubalgebra ℝ L),
    IsRealForm S ↔ ∃! ρ : Conjugation L, ρ.fixed = S

def extend_real_isomorphism_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L)
    {H : Type v} [LieRing H] [LieAlgebra ℂ H] (τ : Conjugation H)
    (e : σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed),
    ∃! a : L ≃ₗ⁅ℂ⁆ H,
      (∀ x : σ.fixed, a (x : L) = (e x : H)) ∧ Intertwines σ τ a

def restrict_complex_isomorphism_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L)
    {H : Type v} [LieRing H] [LieAlgebra ℂ H] (τ : Conjugation H)
    (a : L ≃ₗ⁅ℂ⁆ H), Intertwines σ τ a →
    ∃ e : σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed,
      ∀ x : σ.fixed, (e x : H) = a (x : L)

def forms_isomorphic_iff_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L)
    {H : Type v} [LieRing H] [LieAlgebra ℂ H] (τ : Conjugation H),
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed) ↔
      ∃ a : L ≃ₗ⁅ℂ⁆ H, Intertwines σ τ a

end Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
