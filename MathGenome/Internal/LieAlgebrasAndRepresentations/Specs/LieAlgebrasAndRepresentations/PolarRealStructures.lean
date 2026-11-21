import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.Algebra.Lie.Killing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The polar reduction and bijection of LA-J04, source lines 4747–4794.
The fixed-algebra and signature conclusions are allocated to LA-J04. -/

universe u

namespace Specs.LieAlgebrasAndRepresentations.PolarRealStructures

open LieAlgebrasAndRepresentations.RealForms

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

def IsCompact (ω : Conjugation L) : Prop :=
  ∀ x : ω.fixed, x ≠ 0 → killingForm ℝ ω.fixed x x < 0

/-- The Hermitian extension of the negative Killing form, conjugate-linear
in its first argument by the inner product convention in Lean. -/
noncomputable def hermitian (ω : Conjugation L) (x y : L) : ℂ :=
  -killingForm ℂ L (ω.map x) y

/-- The conjugation associated to an involution of the compact form, using
its complex-linear extension. -/
def involutionConjugation (ω : Conjugation L) (θ : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω θ) (hinv : Function.Involutive θ) : Conjugation L where
  map := LieHom.comp
    { (θ.toLinearEquiv.restrictScalars ℝ).toLinearMap with map_lie' := θ.map_lie _ _ } ω.map
  antilinear a x := by
    change θ (ω.map (a • x)) = _
    rw [ω.antilinear, map_smul]
    rfl
  involutive x := by
    change θ (ω.map (θ (ω.map x))) = x
    rw [hcomm, ω.involutive, hinv]

/-- The spectral power of the absolute value, prescribed on each real
eigenspace. The zero vector imposes no restriction. -/
def IsAbsolutePower (a p : L ≃ₗ⁅ℂ⁆ L) (t : ℝ) : Prop :=
  ∀ (r : ℝ) (x : L), a x = (r : ℂ) • x → p x = ((|r| ^ t : ℝ) : ℂ) • x

def adjoint_identity_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L) (x y : L),
    hermitian ω (a x) y = hermitian ω x (ω.map (a.symm (ω.map y)))

def absolute_power_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ a : L ≃ₗ⁅ℂ⁆ L, (∀ x y, hermitian ω (a x) y = hermitian ω x (a y)) →
    ∀ t : ℝ, ∃! p : L ≃ₗ⁅ℂ⁆ L, IsAbsolutePower a p t

/-- The usual positive spectral powers of the adjoint product of any
complex Lie automorphism are Lie automorphisms. -/
def adjoint_product_power_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L) (t : ℝ), ∃! p : L ≃ₗ⁅ℂ⁆ L,
      ∀ (r : ℝ) (z : L), ω.map (a.symm (ω.map (a z))) = (r : ℂ) • z →
        p z = ((r ^ t : ℝ) : ℂ) • z

def compact_involution_extension_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (ω : Conjugation L)
    (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed), Function.Involutive θ →
    ∃! a : L ≃ₗ⁅ℂ⁆ L, (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Intertwines ω ω a ∧ Function.Involutive a

def polar_reduction_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ σ : Conjugation L,
    ∃ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a : L ≃ₗ⁅ℂ⁆ L)
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a)
      (p : L ≃ₗ⁅ℂ⁆ L),
      Function.Involutive θ ∧ (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Intertwines σ (involutionConjugation ω a hcomm hinv) p

def compact_involutions_classify_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ (θ θ' : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a a' : L ≃ₗ⁅ℂ⁆ L)
      (hcomm : Intertwines ω ω a) (hcomm' : Intertwines ω ω a')
      (hinv : Function.Involutive a) (hinv' : Function.Involutive a'),
      (∀ x : ω.fixed, a (x : L) = (θ x : L)) →
      (∀ x : ω.fixed, a' (x : L) = (θ' x : L)) →
      (Nonempty ((involutionConjugation ω a hcomm hinv).fixed ≃ₗ⁅ℝ⁆
        (involutionConjugation ω a' hcomm' hinv').fixed) ↔
        ∃ v : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed, ∀ x, θ' (v x) = v (θ x))

/-- Every embedded real form is isomorphic to one obtained from a compact
involution. Together with the conjugacy criterion this gives the bijection. -/
def real_form_reduction_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L), IsCompact ω →
    ∀ S : LieSubalgebra ℝ L, IsRealForm S →
      ∃ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a : L ≃ₗ⁅ℂ⁆ L)
        (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
        Function.Involutive θ ∧ (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
        Nonempty (S ≃ₗ⁅ℝ⁆ (involutionConjugation ω a hcomm hinv).fixed)

end Specs.LieAlgebrasAndRepresentations.PolarRealStructures
