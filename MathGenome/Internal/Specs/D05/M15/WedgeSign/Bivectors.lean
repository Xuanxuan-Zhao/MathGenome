import MathGenome.Internal.Specs.D05.M15.WedgeSign.BivectorNormalForm
import MathGenome.Internal.Specs.D05.M11.Nondegenerate

/-! K05.15.wedge_sign, paper.tex:2937–2955. All bivectors and their
products are in the canonical exterior quotient. Zero is decomposable.
The operator bridge is for finite-dimensional symmetric bilinear metrics,
without positivity or a splitting hypothesis. -/
noncomputable section
namespace Specs.D05.M15.WedgeSign.Bivectors
open Module
open BivectorNormalForm
open scoped BigOperators
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

def Decomposable (z : ⋀[K]^2 V) : Prop := ∃ u v : V, z = wedge u v

/-- The square is the ordinary quotient product, with no divided powers. -/
abbrev square (z : ⋀[K]^2 V) : ExteriorAlgebra K V :=
  (z : ExteriorAlgebra K V) * (z : ExteriorAlgebra K V)

def decomposable_iff_rank : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V),
    Decomposable z ↔ finrank K (LinearMap.range (form z)) ≤ 2

def decomposable_iff_matrix_rank : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (z : ⋀[K]^2 V),
    Decomposable z ↔ (matrix b z).rank ≤ 2

def nonzero_iff_rank_two : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V), z ≠ 0 →
    (Decomposable z ↔ finrank K (LinearMap.range (form z)) = 2)

/-- The cross-term formula is valid in every characteristic. -/
def square_normal_sum : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (r : ℕ) (u v : Fin r → V),
    square (∑ i, wedge (u i) (v i)) =
      (2 : K) • ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (wedge (K := K) (u i) (v i) : ExteriorAlgebra K V) *
        (wedge (K := K) (u j) (v j) : ExteriorAlgebra K V)

def square_criterion : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], (2 : K) ≠ 0 → ∀ z : ⋀[K]^2 V,
    square z = 0 ↔ Decomposable z

def square_characteristic_two : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], (2 : K) = 0 → ∀ z : ⋀[K]^2 V, square z = 0

/-- In characteristic two the square test fails already in dimension four. -/
def characteristic_two_counterexample : Prop :=
  ∀ {K : Type u} [Field K], (2 : K) = 0 →
    ∃ z : ⋀[K]^2 (Fin 4 → K), square z = 0 ∧ ¬ Decomposable z ∧
      finrank K (LinearMap.range (form z)) = 4

/-- The usual skew-adjoint space, for the named bilinear metric. -/
def skewOperators (b : LinearMap.BilinForm K V) : Submodule K (V →ₗ[K] V) where
  carrier := {T | ∀ x y, b (T x) y = -b x (T y)}
  zero_mem' := by simp
  add_mem' := by
    intro S T hS hT x y
    simp only [LinearMap.add_apply, map_add, hS x y, hT x y, neg_add]
  smul_mem' := by
    intro a T hT x y
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul, hT x y,
      mul_neg]

/-- This is the correct target in characteristic two as well. -/
def alternatingOperators (b : LinearMap.BilinForm K V) : Submodule K (V →ₗ[K] V) where
  carrier := {T | ∀ x, b (T x) x = 0}
  zero_mem' := by simp
  add_mem' := by intro S T hS hT x; simp [hS x, hT x]
  smul_mem' := by intro a T hT x; simp [hT x]

def skew_iff_alternating : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (b : LinearMap.BilinForm K V), b.IsSymm → (2 : K) ≠ 0 →
    skewOperators b = alternatingOperators b

/-- The generator formula fixes the sign and the entire linear equivalence. -/
def alternating_operator_bridge : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (b : LinearMap.BilinForm K V), b.IsSymm → b.Nondegenerate →
    ∃ E : (⋀[K]^2 V) ≃ₗ[K] alternatingOperators b,
      (∀ u v x, (E (wedge u v)).val x = b u x • v - b v x • u) ∧
      (∀ z x y, b ((E z).val x) y = form z (b x) (b y))

def skew_operator_bridge : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (b : LinearMap.BilinForm K V), b.IsSymm → b.Nondegenerate →
    (2 : K) ≠ 0 →
    ∃ E : (⋀[K]^2 V) ≃ₗ[K] skewOperators b,
      (∀ u v x, (E (wedge u v)).val x = b u x • v - b v x • u) ∧
      (∀ z x y, b ((E z).val x) y = form z (b x) (b y))

def skew_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (b : LinearMap.BilinForm K V), b.IsSymm → b.Nondegenerate →
    (2 : K) ≠ 0 → finrank K (skewOperators b) = (finrank K V).choose 2

/-- Skew-adjointness by itself admits a nonalternating operator in characteristic two. -/
def characteristic_two_skew_counterexample : Prop :=
  ∀ {K : Type u} [Field K], (2 : K) = 0 →
    ∃ (b : LinearMap.BilinForm K K) (T : K →ₗ[K] K),
      b.IsSymm ∧ b.Nondegenerate ∧ T ∈ skewOperators b ∧ T ∉ alternatingOperators b

end Specs.D05.M15.WedgeSign.Bivectors
