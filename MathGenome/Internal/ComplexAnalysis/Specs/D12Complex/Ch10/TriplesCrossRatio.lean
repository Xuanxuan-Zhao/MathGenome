import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Mobius

/-! Ordered triples and cross ratios, paper.tex:2331–2341.
Uniqueness concerns sphere maps, not matrix representatives. The homogeneous
formulas evaluate at poles as infinity, never as complex division by zero. -/
noncomputable section
open scoped Classical
namespace D12Complex.Mobius

/-- A sphere map represented by a nonsingular two-by-two complex matrix. -/
def IsMobiusTransformation (F : RiemannSphere → RiemannSphere) : Prop :=
  ∃ M : Coefficients, Regular M ∧ F = mobiusMap M

/-- Matrix of the normalized map taking the distinct points p,q,r to 0,1,∞.
The values on repeated triples are harmless total-function fillers. -/
def normalizedCoefficients (p q r : RiemannSphere) : Coefficients :=
  let P := finiteCoordinate p
  let Q := finiteCoordinate q
  let R := finiteCoordinate r
  if r = sphereInfty then !![1, -P; 0, Q-P]
  else if p = sphereInfty then !![0, Q-R; 1, -R]
  else if q = sphereInfty then !![1, -P; 1, -R]
  else !![Q-R, -P*(Q-R); Q-P, -R*(Q-P)]

/-- The sphere-valued cross ratio [z,p;q,r], with the normalization 0,1,∞. -/
def crossRatio (z p q r : RiemannSphere) : RiemannSphere :=
  mobiusMap (normalizedCoefficients p q r) z

end D12Complex.Mobius

namespace Specs.D12Complex.Ch10.TriplesCrossRatio
open _root_.D12Complex _root_.D12Complex.Mobius

def IsMobiusTransformation_type := (RiemannSphere → RiemannSphere) → Prop
def IsMobiusTransformation_value : IsMobiusTransformation_type :=
  fun F => ∃ M : Coefficients, Regular M ∧ F = mobiusMap M

def normalizedCoefficients_type := RiemannSphere → RiemannSphere → RiemannSphere → Coefficients
def normalizedCoefficients_value : normalizedCoefficients_type := fun p q r =>
  let P := finiteCoordinate p
  let Q := finiteCoordinate q
  let R := finiteCoordinate r
  if r = sphereInfty then !![1, -P; 0, Q-P]
  else if p = sphereInfty then !![0, Q-R; 1, -R]
  else if q = sphereInfty then !![1, -P; 1, -R]
  else !![Q-R, -P*(Q-R); Q-P, -R*(Q-P)]

def crossRatio_type := RiemannSphere → RiemannSphere → RiemannSphere → RiemannSphere → RiemannSphere
def crossRatio_value : crossRatio_type := fun z p q r =>
  mobiusMap (normalizedCoefficients p q r) z

def normalizedCoefficients_regular_type : Prop :=
  ∀ p q r : RiemannSphere, p ≠ q → p ≠ r → q ≠ r →
    Regular (normalizedCoefficients p q r)

def crossRatio_normalizes_type : Prop :=
  ∀ p q r : RiemannSphere, p ≠ q → p ≠ r → q ≠ r →
    crossRatio p p q r = sphereFinite 0 ∧
    crossRatio q p q r = sphereFinite 1 ∧
    crossRatio r p q r = sphereInfty

def mobius_triples_existsUnique_type : Prop :=
  ∀ p q r P Q R : RiemannSphere,
    p ≠ q → p ≠ r → q ≠ r → P ≠ Q → P ≠ R → Q ≠ R →
    ∃! F : RiemannSphere → RiemannSphere,
      IsMobiusTransformation F ∧ F p = P ∧ F q = Q ∧ F r = R

/-- Finite entries, including z=r (a sphere pole). -/
def crossRatio_finite_type : Prop :=
  ∀ z p q r : ℂ, p ≠ q → p ≠ r → q ≠ r →
    crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      spherePair ((z-p)*(q-r)) ((z-r)*(q-p))

/-- The usual complex quotient at a finite non-pole. -/
def crossRatio_finite_quotient_type : Prop :=
  ∀ z p q r : ℂ, p ≠ q → p ≠ r → q ≠ r → z ≠ r →
    crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      sphereFinite (((z-p)*(q-r))/((z-r)*(q-p)))

/-- All three possible infinity entries in a distinct normalizing triple. -/
def crossRatio_infinity_entries_type : Prop :=
  ∀ z p q : ℂ, p ≠ q →
    (crossRatio (sphereFinite z) (sphereFinite p) (sphereFinite q) sphereInfty =
      spherePair (z-p) (q-p)) ∧
    (crossRatio (sphereFinite z) sphereInfty (sphereFinite p) (sphereFinite q) =
      spherePair (p-q) (z-q)) ∧
    (crossRatio (sphereFinite z) (sphereFinite p) sphereInfty (sphereFinite q) =
      spherePair (z-p) (z-q))

def crossRatio_infty_type : Prop :=
  ∀ p q r : ℂ, p ≠ q → p ≠ r → q ≠ r →
    crossRatio sphereInfty (sphereFinite p) (sphereFinite q) (sphereFinite r) =
      sphereFinite ((q-r)/(q-p))

/-- Invariance for every z, including poles and infinity. -/
def crossRatio_invariant_type : Prop :=
  ∀ (M : Coefficients) (z p q r : RiemannSphere),
    Regular M → p ≠ q → p ≠ r → q ≠ r →
    crossRatio (mobiusMap M z) (mobiusMap M p) (mobiusMap M q) (mobiusMap M r) =
      crossRatio z p q r

/-- The sphere interpretation is continuous across poles and infinity. -/
def crossRatio_continuous_type : Prop :=
  ∀ p q r : RiemannSphere, p ≠ q → p ≠ r → q ≠ r →
    Continuous (fun z => crossRatio z p q r)

/-- Explicit expression in the reciprocal source chart, valid also at w=0. -/
def crossRatio_reciprocal_source_type : Prop :=
  ∀ (p q r : RiemannSphere) (w : ℂ),
    crossRatio (infinityParametrization w) p q r =
      spherePair
        (normalizedCoefficients p q r 0 0 + normalizedCoefficients p q r 0 1 * w)
        (normalizedCoefficients p q r 1 0 + normalizedCoefficients p q r 1 1 * w)

end Specs.D12Complex.Ch10.TriplesCrossRatio
