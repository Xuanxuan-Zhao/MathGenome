import MathGenome.Internal.Specs.D05.M09.RealComplexBridge
import MathGenome.Internal.Specs.D05.M12.InnerProduct

/-!
The inner-product extension in K05.09.real_complex_bridge, paper.tex:1372–1377.
The real form is arbitrary and carries only its algebraic vector-space operations.
`D05.IsFirstInnerProduct` is the shared, first-slot-linear definition; in particular
this is a sesquilinear positive definite form, with no dimension or completeness
assumption. The complex scalar action is the prerequisite pair-model action.
-/
namespace Specs.D05.M09.RealComplexBridge.InnerExtension

open Specs.D05.M09.RealComplexBridge
open Complexification

universe u

/-- The displayed first-slot-linear extension, for an arbitrary real form b. -/
def extendedInner {W : Type u} (b : W → W → ℝ)
    (z w : Complexification W) : ℂ :=
  ((b (re z) (re w) + b (im z) (im w) : ℝ) : ℂ) +
    Complex.I * ((b (im z) (re w) - b (re z) (im w) : ℝ) : ℂ)

/-- The canonical conjugation x + iy ↦ x - iy. -/
def conjugation {W : Type u} [Neg W] (z : Complexification W) : Complexification W :=
  pair (re z) (-im z)

def extendedInner_type : Type (u + 1) :=
  {W : Type u} → (W → W → ℝ) → Complexification W → Complexification W → ℂ

def extendedInner_value : extendedInner_type.{u} := @extendedInner

def conjugation_type : Type (u + 1) :=
  {W : Type u} → [Neg W] → Complexification W → Complexification W

def conjugation_value : conjugation_type.{u} := @conjugation

/-- Existence with all four shared inner-product axioms. -/
def extension_axioms : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → _root_.D05.IsFirstInnerProduct (extendedInner b)

def extends_real : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → ∀ x u : W,
      extendedInner b (pair x 0) (pair u 0) = (b x u : ℂ)

/-- The conjugate-linearity rule, rather than complex bilinearity. -/
def second_slot : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → ∀ (a c : ℂ) (z w t : Complexification W),
      extendedInner b z (a • w + c • t) =
        starRingEnd ℂ a * extendedInner b z w + starRingEnd ℂ c * extendedInner b z t

/-- Exact diagonal formula, its strict positivity, and its zero case. -/
def diagonal : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → ∀ x y : W,
      extendedInner b (pair x y) (pair x y) = ((b x x + b y y : ℝ) : ℂ) ∧
      (0 < b x x + b y y ↔ pair x y ≠ (0 : Complexification W)) ∧
      (extendedInner b (pair x y) (pair x y) = 0 ↔ x = 0 ∧ y = 0)

/-- Any inner product agreeing on W is forced to have the displayed formula. -/
def forced_formula : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → ∀ h : Complexification W → Complexification W → ℂ,
      _root_.D05.IsFirstInnerProduct h →
      (∀ x u : W, h (pair x 0) (pair u 0) = (b x u : ℂ)) →
      ∀ x y u v : W, h (pair x y) (pair u v) =
        ((b x u + b y v : ℝ) : ℂ) + Complex.I * ((b y u - b x v : ℝ) : ℂ)

/-- Uniqueness among all complex inner products, assuming agreement only on W. -/
def unique_extension : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b →
      ∃! h : Complexification W → Complexification W → ℂ,
        _root_.D05.IsFirstInnerProduct h ∧
          ∀ x u : W, h (pair x 0) (pair u 0) = (b x u : ℂ)

/-- The conjugation used in antiunitarity is additive, conjugate-linear, involutive. -/
def conjugation_laws : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W]
    (z w : Complexification W) (a : ℂ),
    conjugation (z + w) = conjugation z + conjugation w ∧
    conjugation (a • z) = starRingEnd ℂ a • conjugation z ∧
    conjugation (conjugation z) = z

def antiunitary : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b → ∀ z w : Complexification W,
      extendedInner b (conjugation z) (conjugation w) =
        starRingEnd ℂ (extendedInner b z w) ∧
      extendedInner b (conjugation z) (conjugation w) = extendedInner b w z

/-- Bridge to Mathlib's algebraic inner product on exactly the same complex module. -/
def extension_core : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (b : W → W → ℝ),
    _root_.D05.IsFirstInnerProduct b →
      ∃ c : InnerProductSpace.Core ℂ (Complexification W),
        ∀ z w, c.inner w z = extendedInner b z w

end Specs.D05.M09.RealComplexBridge.InnerExtension
