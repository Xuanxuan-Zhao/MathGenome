import MathGenome.Internal.Specs.D05.M11.SymmetricQuadratic

/-!
Independent interface for K05.11.polarization, paper.tex:1678–1686.

The polar function is the full difference, as in the upstream interface. Its
half is an actual bilinear form, constructed by scalar multiplication. Over a
field, `(2 : K) ≠ 0` expresses precisely the characteristic-not-two condition.
The statements are proved in arbitrary dimension, and thus include all the
finite-dimensional spaces of this chapter, including the zero space.
-/

namespace Specs.D05.M11.Polarization

universe u v

/-- The normalized polar form of a quadratic form. -/
def polarForm_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    QuadraticForm K V → LinearMap.BilinForm K V

def polarForm_value : polarForm_type.{u, v} :=
  fun {K _} [_] [_] [_] Q => (2 : K)⁻¹ • Q.polarBilin

/-- The normalization is division of the full polar function by two. -/
def polarForm_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V),
    polarForm_value Q x y = (Q (x + y) - Q x - Q y) / 2

/-- The constructed form is bilinear by its type and symmetric by slot interchange. -/
def polarForm_symmetric : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V), (polarForm_value Q).IsSymm

/-- Polarization recovers every symmetric bilinear form from its diagonal. -/
def polarization_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (_hB : B.IsSymm) (x y : V),
    B x y = (B (x + y) (x + y) - B x x - B y y) / 2

/-- One inverse identity, using the canonical upstream diagonal construction. -/
def diagonal_polarForm : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (Q : QuadraticForm K V),
    SymmetricQuadratic.diagonal_value (polarForm_value Q) = Q

/-- The other inverse identity requires symmetry of the original form. -/
def polarForm_diagonal : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (_hB : B.IsSymm),
    polarForm_value (SymmetricQuadratic.diagonal_value B) = B

/-- Each quadratic form has exactly one symmetric bilinear representation. -/
def exists_unique_symmetric : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (Q : QuadraticForm K V),
    ∃! B : LinearMap.BilinForm K V, B.IsSymm ∧ ∀ x, B x x = Q x

/-- The weak hypotheses already make half the polar form symmetric with diagonal
q, and force full degree-two homogeneity. No quadratic structure on q is assumed. -/
def weak_polarization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (q : V → K) (P : LinearMap.BilinForm K V)
    (_hP : ∀ x y, P x y = q (x + y) - q x - q y)
    (_hDouble : ∀ x, q ((2 : K) • x) = 4 * q x),
    ((2 : K)⁻¹ • P).IsSymm ∧
      (∀ x, ((2 : K)⁻¹ • P) x x = q x) ∧
      (∀ (a : K) (x : V), q (a • x) = a ^ 2 * q x)

/-- The paper's weaker-hypothesis characterization, for arbitrary raw functions. -/
def quadratic_iff_weak_axioms : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (_hTwo : (2 : K) ≠ 0) (q : V → K),
    (∃ Q : QuadraticForm K V, ∀ x, Q x = q x) ↔
      (∀ x, q ((2 : K) • x) = 4 * q x) ∧
      (∃ P : LinearMap.BilinForm K V, ∀ x y, P x y = q (x + y) - q x - q y)

end Specs.D05.M11.Polarization
