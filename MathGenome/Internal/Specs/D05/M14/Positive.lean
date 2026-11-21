import MathGenome.Internal.Specs.D05.M13.SelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Independent specifications for K05.14.positive, paper.tex:2394–2398.
The paper's `firstInner u v = inner F v u` is linear in its first slot.
Inequalities are expressed on the real part; self-adjointness is an explicit
conjunct, and the real-valuedness theorem below justifies this interpretation.
No nonzero-dimension or completeness hypothesis is imposed.
-/

noncomputable section

namespace D05

/-- Positive semidefiniteness, including self-adjointness over both fields. -/
def positiveSemidefinite {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  selfAdjoint T ∧ ∀ v : V, 0 ≤ RCLike.re (firstInner (F := F) (T v) v)

/-- Strict positivity is required only away from zero, also on the zero space. -/
def positiveDefinite {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  selfAdjoint T ∧ ∀ v : V, v ≠ 0 → 0 < RCLike.re (firstInner (F := F) (T v) v)

/-- The source's real-plane counterexample, using the already fixed rotation J. -/
def identityPlusRotation : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.id + planeRotation

end D05

namespace Specs.D05.M14.Positive

universe u v

def positiveSemidefinite_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] → (V →ₗ[F] V) → Prop

def positiveSemidefinite_value : positiveSemidefinite_type.{u, v} :=
  fun {F} _ _ _ _ _ T => T = LinearMap.adjoint T ∧
    ∀ v, 0 ≤ RCLike.re (_root_.D05.firstInner (F := F) (T v) v)

def positiveDefinite_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] → (V →ₗ[F] V) → Prop

def positiveDefinite_value : positiveDefinite_type.{u, v} :=
  fun {F} _ _ _ _ _ T => T = LinearMap.adjoint T ∧
    ∀ v, v ≠ 0 → 0 < RCLike.re (_root_.D05.firstInner (F := F) (T v) v)

def identityPlusRotation_type :=
  EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)

def identityPlusRotation_value : identityPlusRotation_type :=
  LinearMap.id + _root_.D05.planeRotation

/-- The full chain of equalities explaining real-valuedness in the manuscript. -/
def selfAdjoint_diagonal_conjugate : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T → ∀ v,
    _root_.D05.firstInner (F := F) (T v) v = _root_.D05.firstInner (F := F) v (T v) ∧
    _root_.D05.firstInner (F := F) (T v) v =
      starRingEnd F (_root_.D05.firstInner (F := F) (T v) v)

/-- Real-valuedness is proved, rather than included as an extra assumption. -/
def selfAdjoint_diagonal_real : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T → ∀ v,
    RCLike.im (_root_.D05.firstInner (F := F) (T v) v) = 0 ∧
    (RCLike.re (_root_.D05.firstInner (F := F) (T v) v) : F) = _root_.D05.firstInner (F := F) (T v) v

/-- Bridge to the library positivity predicate on the same ordinary linear map. -/
def positiveSemidefinite_iff_mathlib : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.positiveSemidefinite T ↔ T.IsPositive

def positiveDefinite_implies_semidefinite : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.positiveDefinite T → _root_.D05.positiveSemidefinite T

/-- On the zero space both universal definitions hold for its unique map. -/
def zero_space : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] [Subsingleton V]
    (T : V →ₗ[F] V),
    _root_.D05.positiveSemidefinite T ∧ _root_.D05.positiveDefinite T

/-- The skew part contributes zero to the real quadratic form. -/
def rotation_quadratic_zero : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 2),
    _root_.D05.firstInner (F := ℝ) (_root_.D05.planeRotation v) v = 0

def identityPlusRotation_quadratic : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 2),
    _root_.D05.firstInner (F := ℝ) (_root_.D05.identityPlusRotation v) v = ‖v‖ ^ 2

/-- Even strict quadratic positivity does not repair the failed real implication. -/
def identityPlusRotation_strict_quadratic : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 →
    0 < _root_.D05.firstInner (F := ℝ) (_root_.D05.identityPlusRotation v) v

def identityPlusRotation_adjoint : Prop :=
  LinearMap.adjoint _root_.D05.identityPlusRotation =
    LinearMap.id - _root_.D05.planeRotation

def identityPlusRotation_not_selfAdjoint : Prop :=
  ¬ _root_.D05.selfAdjoint _root_.D05.identityPlusRotation

def identityPlusRotation_not_positive : Prop :=
  ¬ _root_.D05.positiveSemidefinite _root_.D05.identityPlusRotation ∧
  ¬ _root_.D05.positiveDefinite _root_.D05.identityPlusRotation

/-- The original nonnegative-quadratic counterexample, with the stronger strict
quadratic property recorded as well. -/
def real_quadratic_counterexample : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
    (∀ v, _root_.D05.firstInner (F := ℝ) (T v) v = ‖v‖ ^ 2) ∧
    (∀ v, 0 ≤ _root_.D05.firstInner (F := ℝ) (T v) v) ∧
    (∀ v, v ≠ 0 → 0 < _root_.D05.firstInner (F := ℝ) (T v) v) ∧
    ¬ _root_.D05.selfAdjoint T ∧
    ¬ _root_.D05.positiveSemidefinite T ∧ ¬ _root_.D05.positiveDefinite T

end Specs.D05.M14.Positive
