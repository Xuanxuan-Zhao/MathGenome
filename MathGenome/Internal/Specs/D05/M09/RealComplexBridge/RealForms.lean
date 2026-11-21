import MathGenome.Internal.Specs.D05.M09.RealComplexBridge
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
Real forms, paper.tex:1367–1372.  Only the dimension conclusions assume
finite dimension.  The real action on a complex space is restriction of scalars.
The complexification is the upstream canonical pair model, with no chosen basis.
-/
namespace Specs.D05.M09.RealComplexBridge.RealForms

open Specs.D05.M09.RealComplexBridge
open Complexification

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- An additive conjugate-linear involution, with no topology or metric. -/
structure Conjugation (V : Type u) [AddCommGroup V] [Module ℂ V] where
  toMap : V →ₗ⋆[ℂ] V
  involutive : Function.Involutive toMap

instance : CoeFun (Conjugation V) (fun _ => V → V) := ⟨fun J => J.toMap⟩

/-- The fixed vectors form a real subspace with the inherited operations. -/
def fixedSpace (J : Conjugation V) : Submodule ℝ V where
  carrier := {v | J v = v}
  zero_mem' := J.toMap.map_zero
  add_mem' {x y} hx hy := by
    change J.toMap x = x at hx
    change J.toMap y = y at hy
    change J.toMap (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' a v hv := by
    change J.toMap v = v at hv
    change J.toMap ((a : ℂ) • v) = (a : ℂ) • v
    rw [J.toMap.map_smulₛₗ]
    change star (a : ℂ) • J.toMap v = (a : ℂ) • v
    rw [Complex.star_def, Complex.conj_ofReal, hv]

/-- The actual natural map, (x,y) ↦ x + iy, for any real subspace. -/
def naturalMap (W : Submodule ℝ V) : Complexification W →ₗ[ℂ] V where
  toFun p := ((re p : W) : V) + Complex.I • ((im p : W) : V)
  map_add' p q := by
    change (((re p : W) : V) + (re q : W)) + Complex.I • (((im p : W) : V) + (im q : W)) = _
    module
  map_smul' z p := by
    change ((z.re • re p - z.im • im p : W) : V) +
      Complex.I • ((z.im • re p + z.re • im p : W) : V) = _
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      ← Complex.coe_smul]
    conv_rhs => rw [← z.re_add_im]
    simp only [RingHom.id_apply]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-- Real form means unique decomposition in actual elements of W. -/
def IsRealForm (W : Submodule ℝ V) : Prop :=
  ∀ v : V, ∃! p : W × W, (p.1 : V) + Complex.I • (p.2 : V) = v

/-- Multiplication by i, viewed as a real-linear map. -/
def multiplyI : V →ₗ[ℝ] V := (Complex.I • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℝ

/-- The subspace iW, as an image under the specified map. -/
def imaginarySpace (W : Submodule ℝ V) : Submodule ℝ V := W.map multiplyI

/-- The exact two projection formulas in the source. -/
def decomposition_formulas : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (J : Conjugation V) (v : V),
    let x := (2 : ℂ)⁻¹ • (v + J v)
    let y := (2 * Complex.I : ℂ)⁻¹ • (v - J v)
    x ∈ fixedSpace J ∧ y ∈ fixedSpace J ∧ v = x + Complex.I • y

def fixed_real_form : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (J : Conjugation V),
    IsRealForm (fixedSpace J)

def real_form_iff_bijective : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (W : Submodule ℝ V),
    IsRealForm W ↔ Function.Bijective (naturalMap W)

/-- The isomorphism has precisely the natural summation values. -/
def natural_isomorphism : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (W : Submodule ℝ V),
    IsRealForm W → ∃ e : Complexification W ≃ₗ[ℂ] V,
      ∀ x y : W, e (pair x y) = (x : V) + Complex.I • (y : V)

def internal_direct_sum : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (W : Submodule ℝ V),
    IsRealForm W → W ⊔ imaginarySpace W = ⊤ ∧ W ⊓ imaginarySpace W = ⊥

/-- Existence, the x-iy formula, and uniqueness among all conjugations fixing W. -/
def conjugation_of_real_form : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (W : Submodule ℝ V),
    IsRealForm W → ∃ J : Conjugation V,
      (∀ x y : W, J ((x : V) + Complex.I • (y : V)) =
        (x : V) - Complex.I • (y : V)) ∧
      fixedSpace J = W ∧
      ∀ J' : Conjugation V, (∀ x : W, J' x = x) → J' = J

/-- Any specified real basis works. In fact no finite-dimension hypothesis is needed. -/
def basis_criterion : Prop :=
  ∀ {V : Type u} {ι : Type w} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℝ V) (b : Module.Basis ι ℝ W),
    IsRealForm W ↔ ∃ B : Module.Basis ι ℂ V, ∀ i, B i = (b i : V)

/-- Finiteness of W yields finiteness of V and equality of the stated dimensions. -/
def dimension_from_real_form : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (W : Submodule ℝ V)
    [FiniteDimensional ℝ W], IsRealForm W →
      FiniteDimensional ℂ V ∧ Module.finrank ℝ W = Module.finrank ℂ V

/-- Also records the conclusion when the ambient complex space is finite. -/
def dimension_of_fixed_space : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (J : Conjugation V), Module.finrank ℝ (fixedSpace J) = Module.finrank ℂ V

def preserves_iff_commutes : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (J : Conjugation V)
    (T : V →ₗ[ℂ] V),
    (∀ v ∈ fixedSpace J, T v ∈ fixedSpace J) ↔ ∀ v, T (J v) = J (T v)

end Specs.D05.M09.RealComplexBridge.RealForms
