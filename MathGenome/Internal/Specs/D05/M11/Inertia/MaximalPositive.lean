import MathGenome.Internal.Specs.D05.M11.Hermitian
import MathGenome.Internal.Specs.D05.M11.Radicals
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Prod

/-! The maximal-dimension stage of inertia (paper.tex:1699–1708 and
1767–1776). A displayed normal form is a coordinate equivalence with the full
pairing formula, so no existence or spectral theorem is assumed here.
For `K = ℝ` conjugation is the identity; for `K = ℂ` it is complex conjugation.
All dimensions below are over `K`, including the complex case. -/
noncomputable section
namespace Specs.D05.M11.Inertia.MaximalPositive
open scoped BigOperators
open Module

abbrev Form (K V : Type*) [RCLike K] [AddCommGroup V] [Module K V] :=
  Specs.D05.M11.Hermitian.sesquilinearForm_value K V

abbrev Coordinates (K : Type*) (p q r : ℕ) :=
  (Fin p → K) × (Fin q → K) × (Fin r → K)

/-- Exactly the full pairing with matrix diag(I_p,-I_q,0_r). -/
def IsNormalForm {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r) : Prop :=
  ∀ x y, B x y = (∑ i, (e x).1 i * star ((e y).1 i)) -
    ∑ j, (e x).2.1 j * star ((e y).2.1 j)

/-- Positivity of the restriction, evaluated on every nonzero vector in U. -/
def PositiveOn {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) (U : Submodule K V) : Prop :=
  ∀ x ∈ U, x ≠ 0 → 0 < RCLike.re (B x x)

/-- First-slot radical; for a Hermitian form this is also the right radical. -/
abbrev radical {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) : Submodule K V := LinearMap.ker B

/-- The coordinate bound uses intersection dimensions and includes p=0. -/
def positive_dimension_bound : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r), IsNormalForm B e →
    ∀ U : Submodule K V, PositiveOn B U → finrank K U ≤ p

/-- Both bounds are attained, so these are actual maxima, not just suprema. -/
def maximal_dimensions : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r), IsNormalForm B e →
    IsGreatest {d : ℕ | ∃ U : Submodule K V, PositiveOn B U ∧ finrank K U = d} p ∧
    IsGreatest {d : ℕ | ∃ U : Submodule K V, PositiveOn (-B) U ∧ finrank K U = d} q

/-- The zero block is exactly the radical, of dimension r. -/
def radical_dimension : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Form K V) {p q r : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r), IsNormalForm B e →
    finrank K (radical B) = r

/-- Two displayed normal forms of the same form have the same full triple. -/
def unique_triple : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Form K V) {p q r p' q' r' : ℕ}
    (e : V ≃ₗ[K] Coordinates K p q r)
    (f : V ≃ₗ[K] Coordinates K p' q' r'),
    IsNormalForm B e → IsNormalForm B f → p = p' ∧ q = q' ∧ r = r'

/-- Ordinary real bilinear forms are included by an equality of their values;
this bridge also identifies the pre-existing radical with the kernel above. -/
def real_bilinear_bridge : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    ∃ S : Form ℝ V, (∀ x y, S x y = B x y) ∧
      (Specs.D05.M11.Hermitian.isHermitian_value S ↔ B.IsSymm) ∧
      radical S = Specs.D05.M11.Radicals.leftRadical_value B

/-- The displayed pairing is Hermitian, and its first and second-slot radicals
coincide. This also justifies testing positivity with the real part. -/
def normal_form_hermitian : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r),
    IsNormalForm B e → Specs.D05.M11.Hermitian.isHermitian_value B ∧
      ∀ x, x ∈ radical B ↔ ∀ y, B y x = 0

/-- The real bilinear specialization, with ordinary real inequalities and the
previously fixed real bilinear radical. -/
def real_invariants : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r),
    (∀ x y, B x y = (∑ i, (e x).1 i * (e y).1 i) -
      ∑ j, (e x).2.1 j * (e y).2.1 j) →
    IsGreatest {d : ℕ | ∃ U : Submodule ℝ V,
      (∀ x ∈ U, x ≠ 0 → 0 < B x x) ∧ finrank ℝ U = d} p ∧
    IsGreatest {d : ℕ | ∃ U : Submodule ℝ V,
      (∀ x ∈ U, x ≠ 0 → B x x < 0) ∧ finrank ℝ U = d} q ∧
    finrank ℝ (Specs.D05.M11.Radicals.leftRadical_value B) = r

/-- The actual ordered block basis, transported from coordinate space. -/
def blockBasis (K : Type*) [RCLike K] (p q r : ℕ) :
    Basis (Fin p ⊕ Fin q ⊕ Fin r) K (Coordinates K p q r) :=
  (Pi.basisFun K (Fin p)).prod
    ((Pi.basisFun K (Fin q)).prod (Pi.basisFun K (Fin r)))

def normalBasis {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r) :
    Basis (Fin p ⊕ Fin q ⊕ Fin r) K V := (blockBasis K p q r).map e.symm

/-- This is literally diag(I_p,-I_q,0_r), with the three finite index blocks. -/
def normalMatrix (K : Type*) [RCLike K] (p q r : ℕ) :
    Matrix (Fin p ⊕ Fin q ⊕ Fin r) (Fin p ⊕ Fin q ⊕ Fin r) K :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (Sum.elim (fun _ => -1) (fun _ => 0)))

/-- Equivalence with the actual form matrix, in both directions. No maximum
or radical certificate is included in the normal-form premise. -/
def normal_form_matrix : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r),
    IsNormalForm B e ↔
      LinearMap.toMatrix₂ (normalBasis e) (normalBasis e) B = normalMatrix K p q r

end Specs.D05.M11.Inertia.MaximalPositive
