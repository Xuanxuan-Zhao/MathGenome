import MathGenome.Internal.Specs.D05.M11.Inertia.MaximalPositive
import MathGenome.Internal.Specs.D05.M11.Nondegenerate

/-! Sylvester's law for real symmetric bilinear forms, paper.tex:1699–1708.
The coordinate predicate contains only the full pairing identity. It contains no
existence, dimension, radical, or uniqueness certificate. All blocks may be empty.
-/
noncomputable section
namespace Specs.D05.M11.Inertia
open Module
open scoped BigOperators
open MaximalPositive (Coordinates normalMatrix normalBasis)

/-- The real bilinear specialization of the shared signed-block convention. -/
def IsNormalForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r) : Prop :=
  ∀ x y, B x y = (∑ i, (e x).1 i * (e y).1 i) -
    ∑ j, (e x).2.1 j * (e y).2.1 j

/-- The literal matrix diag(I_p,-I_q,0_r) in an arbitrary block-indexed basis. -/
def HasNormalMatrix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (b : Basis (Fin p ⊕ Fin q ⊕ Fin r) ℝ V) : Prop :=
  LinearMap.toMatrix₂ b b B = normalMatrix ℝ p q r

/-- Full existence, without nondegeneracy or positivity assumptions. -/
def normal_form_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V), B.IsSymm →
    ∃ p q r : ℕ, ∃ e : V ≃ₗ[ℝ] Coordinates ℝ p q r, IsNormalForm B e

/-- Coordinate and actual matrix descriptions agree for every basis. -/
def matrix_iff_coordinates : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (b : Basis (Fin p ⊕ Fin q ⊕ Fin r) ℝ V),
    HasNormalMatrix B b ↔ IsNormalForm B
      (b.equivFun.trans (MaximalPositive.blockBasis ℝ p q r).equivFun.symm)

/-- The source's actual basis-and-matrix existence conclusion. -/
def matrix_normal_form_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V), B.IsSymm →
    ∃ p q r : ℕ, ∃ b : Basis (Fin p ⊕ Fin q ⊕ Fin r) ℝ V, HasNormalMatrix B b

/-- Maximal positive and negative dimensions, radical dimension, total dimension,
and rank, all in the original real vector space. -/
def intrinsic_invariants : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r), IsNormalForm B e →
    IsGreatest {d : ℕ | ∃ U : Submodule ℝ V,
      (∀ x ∈ U, x ≠ 0 → 0 < B x x) ∧ finrank ℝ U = d} p ∧
    IsGreatest {d : ℕ | ∃ U : Submodule ℝ V,
      (∀ x ∈ U, x ≠ 0 → B x x < 0) ∧ finrank ℝ U = d} q ∧
    finrank ℝ (Radicals.leftRadical_value B) = r ∧
    finrank ℝ V = p + q + r ∧ Nondegenerate.rank_value B = p + q

/-- The triple, rather than a choice of basis, is unique. -/
def unique_triple : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r p' q' r' : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r)
    (f : V ≃ₗ[ℝ] Coordinates ℝ p' q' r'),
    IsNormalForm B e → IsNormalForm B f → p = p' ∧ q = q' ∧ r = r'

/-- Uniqueness for arbitrary bases exhibiting the displayed matrices. -/
def unique_matrix_triple : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r p' q' r' : ℕ}
    (b : Basis (Fin p ⊕ Fin q ⊕ Fin r) ℝ V)
    (c : Basis (Fin p' ⊕ Fin q' ⊕ Fin r') ℝ V),
    HasNormalMatrix B b → HasNormalMatrix B c → p = p' ∧ q = q' ∧ r = r'

/-- Congruence is an invertible change in both input slots. -/
def congruence_classification : Prop :=
  ∀ {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    {p q r p' q' r' : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r)
    (f : W ≃ₗ[ℝ] Coordinates ℝ p' q' r'),
    IsNormalForm B e → IsNormalForm C f →
    ((∃ g : V ≃ₗ[ℝ] W, ∀ x y, B x y = C (g x) (g y)) ↔
      p = p' ∧ q = q' ∧ r = r')

/-- Even in one fixed dimension, signature p-q alone misses the radical:
(1,1,0) and (0,0,2) have equal signature and are not congruent. -/
def signature_does_not_classify : Prop :=
  ∃ B C : LinearMap.BilinForm ℝ (Coordinates ℝ 1 1 0),
    B.IsSymm ∧ C.IsSymm ∧
    IsNormalForm B (LinearEquiv.refl ℝ _) ∧
    (∃ f : Coordinates ℝ 1 1 0 ≃ₗ[ℝ] Coordinates ℝ 0 0 2, IsNormalForm C f) ∧
    ((1 : ℤ) - 1 = (0 : ℤ) - 0) ∧
    ¬ ∃ g : Coordinates ℝ 1 1 0 ≃ₗ[ℝ] Coordinates ℝ 1 1 0,
      ∀ x y, B x y = C (g x) (g y)

end Specs.D05.M11.Inertia
