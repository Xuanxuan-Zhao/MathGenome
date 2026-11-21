import MathGenome.Internal.Specs.D05.M11.Inertia
import MathGenome.Internal.Specs.D05.M11.HermitianInertia

/-! K05.11.definiteness, paper.tex:1777–1778.
Predicates are on the underlying function, so the same definitions apply to real
bilinear and complex sesquilinear forms. For Hermitian forms the diagonal is real;
`re` expresses its real order, not an order on complex numbers. -/
noncomputable section
namespace Specs.D05.M11.Definiteness
open scoped BigOperators
open Inertia.MaximalPositive

universe u v

def signPredicate_type :=
  {K : Type u} → {V : Type v} → [RCLike K] → [Zero V] → (V → V → K) → Prop

def positiveDefinite_value : signPredicate_type := fun B =>
  ∀ x, x ≠ 0 → 0 < RCLike.re (B x x)

def positiveSemidefinite_value : signPredicate_type := fun B =>
  ∀ x, 0 ≤ RCLike.re (B x x)

def negativeDefinite_value : signPredicate_type := fun B => positiveDefinite_value (-B)
def negativeSemidefinite_value : signPredicate_type := fun B => positiveSemidefinite_value (-B)
def indefinite_value : signPredicate_type := fun B =>
  (∃ x, 0 < RCLike.re (B x x)) ∧ (∃ y, RCLike.re (B y y) < 0)

def isotropic_type :=
  {K : Type u} → {V : Type v} → [RCLike K] → [Zero V] → (V → V → K) → V → Prop

def isotropic_value : isotropic_type := fun B x => x ≠ 0 ∧ B x x = 0

/-- Each criterion is for the full signed normal pairing, with empty blocks allowed. -/
def normal_form_criteria : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : Form K V) {p q r : ℕ} (e : V ≃ₗ[K] Coordinates K p q r),
    IsNormalForm B e →
    (positiveDefinite_value (fun x y => B x y) ↔ q = 0 ∧ r = 0) ∧
    (positiveSemidefinite_value (fun x y => B x y) ↔ q = 0) ∧
    (negativeDefinite_value (fun x y => B x y) ↔ p = 0 ∧ r = 0) ∧
    (negativeSemidefinite_value (fun x y => B x y) ↔ p = 0) ∧
    (indefinite_value (fun x y => B x y) ↔ 0 < p ∧ 0 < q)

/-- Ordinary real bilinear forms use ordinary real inequalities. -/
def real_normal_form_criteria : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r), Inertia.IsNormalForm B e →
    (positiveDefinite_value (fun x y => B x y) ↔ q = 0 ∧ r = 0) ∧
    (positiveSemidefinite_value (fun x y => B x y) ↔ q = 0) ∧
    (negativeDefinite_value (fun x y => B x y) ↔ p = 0 ∧ r = 0) ∧
    (negativeSemidefinite_value (fun x y => B x y) ↔ p = 0) ∧
    (indefinite_value (fun x y => B x y) ↔ 0 < p ∧ 0 < q)

/-- No normal form is assumed in either final semidefinite theorem. -/
def real_semidefinite_radical : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V), B.IsSymm →
    positiveSemidefinite_value (fun x y => B x y) →
    ∀ x, B x x = 0 ↔ x ∈ Radicals.leftRadical_value B ∧ x ∈ Radicals.rightRadical_value B

def complex_semidefinite_radical : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : Form ℂ V), Hermitian.isHermitian_value B →
    positiveSemidefinite_value (fun x y => B x y) →
    ∀ x, B x x = 0 ↔ (∀ y, B x y = 0) ∧ (∀ y, B y x = 0)

/-- The literal two by two matrix and the literal vector (1,1). -/
def isotropy_counterexample : Prop :=
  ∃ B : LinearMap.BilinForm ℝ (Fin 2 → ℝ),
    LinearMap.toMatrix₂ (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2)) B =
      !![1, 0; 0, -1] ∧ B.IsSymm ∧ Nondegenerate.nondegenerate_value B ∧
    Radicals.leftRadical_value B = ⊥ ∧ Radicals.rightRadical_value B = ⊥ ∧
    isotropic_value (fun x y => B x y) ![1, 1] ∧
    ![1, 1] ∉ Radicals.leftRadical_value B

/-- The universal definition includes every form on a zero-dimensional space. -/
def zero_dimensional_positive_definite : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : V → V → K), Module.finrank K V = 0 →
    positiveDefinite_value B

end Specs.D05.M11.Definiteness
