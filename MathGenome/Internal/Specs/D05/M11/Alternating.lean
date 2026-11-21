import MathGenome.Internal.Specs.D05.M11.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
Independent statements for K05.11.alternating, paper.tex:1713–1722.

Forms are the canonical `LinearMap.BilinForm`. The elementary results hold
without finite dimension, hence cover the paper's finite-dimensional spaces,
including the zero space. `IsAlt` means diagonal vanishing in every characteristic;
skew-symmetry is stated as an explicit slot identity. The hypothesis `(2 : K) ≠ 0`
is used only for the converse, decomposition, and uniqueness results.
-/

namespace Specs.D05.M11.Alternating

universe u v

/-- The paper's symmetric part, constructed inside the space of bilinear forms. -/
def symmetricPart {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : LinearMap.BilinForm K V :=
  (2 : K)⁻¹ • (B + B.flip)

/-- The paper's alternating part. The formula is defined even when two vanishes;
the assertion that the two parts sum to B requires two to be nonzero. -/
def alternatingPart {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : LinearMap.BilinForm K V :=
  (2 : K)⁻¹ • (B - B.flip)

/-- Alternation is precisely vanishing on every diagonal input. -/
def alternating_iff_diagonal : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsAlt ↔ ∀ v, B v v = 0

/-- Expanding the diagonal at u+v proves skew-symmetry in every characteristic. -/
def alternating_implies_skew : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsAlt → ∀ u v, B u v = -B v u

/-- Skew-symmetry always gives twice each diagonal value equal to zero. -/
def skew_diagonal_two_mul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), (∀ u v, B u v = -B v u) →
      ∀ v, (2 : K) * B v v = 0

/-- The converse needs exactly the invertibility of two. -/
def alternating_iff_skew : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V),
    B.IsAlt ↔ ∀ u v, B u v = -B v u

/-- Over every characteristic-two field, multiplication on the one-dimensional
space K is skew-symmetric but is not alternating. -/
def characteristic_two_counterexample : Prop :=
  ∀ {K : Type*} [Field K], (2 : K) = 0 →
    ∃ B : LinearMap.BilinForm K K,
      Module.finrank K K = 1 ∧ (∀ x y, B x y = x * y) ∧
      (∀ x y, B x y = -B y x) ∧ B 1 1 = 1 ∧ ¬ B.IsAlt

/-- The bundled parts are bilinear and have exactly the displayed scalar values. -/
def part_formulas : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (u v : V),
    symmetricPart B u v = (B u v + B v u) / 2 ∧
    alternatingPart B u v = (B u v - B v u) / 2

/-- Swapping slots fixes the symmetric part, and the alternating part vanishes
on the diagonal and is skew-symmetric. -/
def part_properties : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V),
    (symmetricPart B).IsSymm ∧ (alternatingPart B).IsAlt ∧
      (∀ u v, alternatingPart B u v = -alternatingPart B v u)

/-- These explicitly constructed parts add to the original form. -/
def decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V),
    B = symmetricPart B + alternatingPart B

/-- The intersection of the symmetric and alternating spaces is zero. -/
def symmetric_alternating_eq_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V),
    B.IsSymm → B.IsAlt → B = 0

/-- Every symmetric/alternating decomposition equals the displayed formulas. -/
def decomposition_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B S A : LinearMap.BilinForm K V),
    S.IsSymm → A.IsAlt → B = S + A →
      S = symmetricPart B ∧ A = alternatingPart B

/-- Existence and uniqueness of the pair, not just uniqueness of one part. -/
def exists_unique_decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V),
    ∃! p : LinearMap.BilinForm K V × LinearMap.BilinForm K V,
      p.1.IsSymm ∧ p.2.IsAlt ∧ B = p.1 + p.2

/-- The alternating part contributes nothing to the diagonal quadratic function. -/
def diagonal_eq_symmetricPart : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (v : V),
    B v v = symmetricPart B v v

/-- Every bilinear representative of a diagonal quadratic function has exactly
one symmetric representative with that same diagonal function. -/
def exists_unique_symmetric_representative : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V),
    ∃! S : LinearMap.BilinForm K V, S.IsSymm ∧ ∀ v, S v v = B v v

end Specs.D05.M11.Alternating
