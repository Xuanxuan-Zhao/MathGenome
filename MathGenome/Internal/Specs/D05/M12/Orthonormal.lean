import MathGenome.Internal.Specs.D05.M02.Independence
import MathGenome.Internal.Specs.D05.M12.Norm
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Independent statements for K05.12.orthonormal, paper.tex:1956–1965.
The shared first-slot-linear inner product is used throughout. Families are
indexed functions, retaining repeated occurrences. Neither completeness nor
finite dimension is assumed. The normalization theorem is proved even for
arbitrary index types; its finite-family specialization is recorded explicitly.
-/

noncomputable section

namespace D05

/-- The paper's Kronecker-delta definition, in its first-slot-linear convention. -/
def orthonormalFamily {F V J : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (e : J → V) : Prop := by
  classical
  exact ∀ j k, firstInner (F := F) (e j) (e k) = if j = k then 1 else 0

/-- Orthogonality alone does not exclude zero entries. -/
def orthogonalFamily {F V J : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (e : J → V) : Prop :=
  ∀ j k, j ≠ k → firstInner (F := F) (e j) (e k) = 0

/-- Division by the real norm, embedded in the scalar field. At zero this is
zero, and the normalization theorems explicitly require nonzero input. -/
def normalizeVector {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (v : V) : V := ((‖v‖⁻¹ : ℝ) : F) • v

end D05

namespace Specs.D05.M12.Orthonormal

universe u v w

def orthonormal_type : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  {F : Type u} → {V : Type v} → {J : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [InnerProductSpace F V] → (J → V) → Prop

def orthonormal_value : orthonormal_type.{u, v, w} := by
  classical
  exact fun {F} _ _ _ _ _ e =>
    ∀ j k, _root_.D05.firstInner (F := F) (e j) (e k) = if j = k then 1 else 0

def orthogonal_type : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  {F : Type u} → {V : Type v} → {J : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [InnerProductSpace F V] → (J → V) → Prop

def orthogonal_value : orthogonal_type.{u, v, w} :=
  fun {F} _ _ _ _ _ e =>
    ∀ j k, j ≠ k → _root_.D05.firstInner (F := F) (e j) (e k) = 0

def normalizeVector_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → V → V

def normalizeVector_value : normalizeVector_type.{u, v} :=
  fun {F} _ _ _ _ v => ((‖v‖⁻¹ : ℝ) : F) • v

/-- A convention bridge, rather than an assumption identifying the predicates. -/
def orthonormal_iff_mathlib : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthonormalFamily (F := F) e ↔ Orthonormal F e

def orthogonal_iff_pairwise : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthogonalFamily (F := F) e ↔
      Pairwise (fun j k => inner F (e j) (e k) = 0)

def orthonormal_iff_orthogonal_norm_one : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthonormalFamily (F := F) e ↔
      _root_.D05.orthogonalFamily (F := F) e ∧ ∀ j, ‖e j‖ = 1

def orthonormal_linearIndependent : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthonormalFamily (F := F) e → LinearIndependent F e

/-- The coefficient, without conjugation, selected in the paper's proof. -/
def coefficient_finite_sum : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (s : Finset J) (a : J → F) (k : J), k ∈ s →
      _root_.D05.firstInner (∑ j ∈ s, a j • e j) (e k) = a k

def orthonormal_ne_zero : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthonormalFamily (F := F) e → ∀ j, e j ≠ 0

def normalization_denominator_pos : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (v : V), v ≠ 0 → 0 < ‖v‖

/-- The norm used for division is the square-root norm previously constructed. -/
def normalizeVector_eq_inducedNorm : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (v : V), _root_.D05.normalizeVector (F := F) v =
      (((_root_.D05.inducedNorm (_root_.D05.firstInner (F := F)) v)⁻¹ : ℝ) : F) • v

def normalizeVector_norm : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (v : V), v ≠ 0 → ‖_root_.D05.normalizeVector (F := F) v‖ = 1

def normalize_orthogonal : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V), _root_.D05.orthogonalFamily (F := F) e → (∀ j, e j ≠ 0) →
      _root_.D05.orthonormalFamily (F := F)
        (fun j => _root_.D05.normalizeVector (F := F) (e j))

def normalize_finite_orthogonal : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Finite J] (e : J → V),
    _root_.D05.orthogonalFamily (F := F) e → (∀ j, e j ≠ 0) →
      _root_.D05.orthonormalFamily (F := F)
        (fun j => _root_.D05.normalizeVector (F := F) (e j))

/-- The zero vector does not acquire unit norm through division by its norm. -/
def normalizeVector_zero : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V],
    _root_.D05.normalizeVector (F := F) (0 : V) = 0 ∧
      ‖_root_.D05.normalizeVector (F := F) (0 : V)‖ ≠ 1

def not_independent_of_zero_entry : Prop :=
  ∀ {F V J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (e : J → V) (j : J), e j = 0 → ¬ LinearIndependent F e

end Specs.D05.M12.Orthonormal
