import MathGenome.Internal.Specs.D05.M11.HermitianDiagonal
import MathGenome.Internal.Specs.D05.M11.Inertia.MaximalPositive

/-! K05.11.hermitian_inertia (paper.tex:1767–1775).
Forms are linear in the first slot and conjugate-linear in the second.
No positivity or nondegeneracy is required. All dimensions are complex dimensions.
The coordinate predicate is the full pairing formula for diag(I_p,-I_q,0_r),
not a hypothesis that supplies an inertia certificate. -/
namespace Specs.D05.M11.HermitianInertia
open Module
open Specs.D05.M11.Inertia.MaximalPositive

/-- Existence of an actual change of coordinates giving the full normal pairing. -/
def normal_form_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V), Hermitian.isHermitian_value B →
    ∃ (p q r : ℕ) (e : V ≃ₗ[ℂ] Coordinates ℂ p q r), IsNormalForm B e

/-- The ordered block basis has literally the stated diagonal matrix. -/
def matrix_normal_form_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V), Hermitian.isHermitian_value B →
    ∃ (p q r : ℕ) (e : V ≃ₗ[ℂ] Coordinates ℂ p q r),
      LinearMap.toMatrix₂ (normalBasis e) (normalBasis e) B = normalMatrix ℂ p q r

/-- Uniqueness of the three integers, with no positive-dimension exception. -/
def normal_form_unique : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V) {p q r p' q' r' : ℕ}
    (e : V ≃ₗ[ℂ] Coordinates ℂ p q r) (f : V ≃ₗ[ℂ] Coordinates ℂ p' q' r'),
    IsNormalForm B e → IsNormalForm B f → p = p' ∧ q = q' ∧ r = r'

/-- Intrinsic interpretation by attained maxima and the radical dimension. -/
def intrinsic_dimensions : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V) {p q r : ℕ} (e : V ≃ₗ[ℂ] Coordinates ℂ p q r),
    IsNormalForm B e →
    IsGreatest {d : ℕ | ∃ U : Submodule ℂ V, PositiveOn B U ∧ finrank ℂ U = d} p ∧
    IsGreatest {d : ℕ | ∃ U : Submodule ℂ V, PositiveOn (-B) U ∧ finrank ℂ U = d} q ∧
    finrank ℂ (radical B) = r

/-- Full classification, combining existence and uniqueness of the triple. -/
def inertia : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V), Hermitian.isHermitian_value B →
    ∃! t : ℕ × ℕ × ℕ,
      ∃ e : V ≃ₗ[ℂ] Coordinates ℂ t.1 t.2.1 t.2.2, IsNormalForm B e

end Specs.D05.M11.HermitianInertia
