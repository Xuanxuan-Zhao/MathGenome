import MathGenome.Internal.LinearPDE.P201Specs.Heat.OrderedTraceChain
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent specifications for paper.tex, pde:heat-weak-comparison.
Matrices act on the finite-dimensional Euclidean space as continuous linear
maps. No symmetry is imposed. All bulk and boundary orders are a.e. orders of
the physical quotient classes. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology
namespace P201Specs.Heat.WeakComparison
open OrderedTraceChain

abbrev Coefficient (n : ℕ) := ℝ → Space n → Space n →L[ℝ] Space n

/-- A common space-time exceptional set for boundedness and ellipticity,
including all vectors simultaneously. Joint a.e. measurability suffices. -/
def BoundedElliptic {n : ℕ} (Ω : Domain n) (T : ℝ)
    (A : Coefficient n) (ν : ℝ) : Prop :=
  0 < ν ∧
  AEStronglyMeasurable (Function.uncurry A) ((timeMeasure T).prod (domainMeasure Ω)) ∧
  ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ z ∂(timeMeasure T).prod (domainMeasure Ω),
    ‖A z.1 z.2‖ ≤ M ∧ ∀ ξ : Space n,
      ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A z.1 z.2 ξ) ξ

/-- The actual local divergence form on full-norm H¹, not an abstract form. -/
def form {n : ℕ} (Ω : Domain n) (A : Space n → Space n →L[ℝ] Space n)
    (u v : H ℝ Ω 1) : ℝ :=
  ∫ x, inner ℝ (A x (hGradient u x)) (hGradient v x) ∂domainMeasure Ω

/-- The standard finite-dimensional matrix action. -/
def matrixAction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Space n →L[ℝ] Space n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

def MatrixFormStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (u v : H ℝ Ω 1),
    form Ω (fun x => matrixAction (A x)) u v = ellipticEnergyForm Ω A u v

/-- Energy regularity with a separate, compatible continuous L² representative.
The H¹-valued path is not required to have zero trace. -/
structure EnergyPath {n : ℕ} (Ω : Domain n) (T : ℝ)
    (u : ℝ → H ℝ Ω 1) (du : ℝ → Hminus1 ℝ Ω) (U : ℝ → Lp ℝ Ω 2) : Prop where
  spatial : MemLp u 2 (timeMeasure T)
  derivative : MemLp du 2 (timeMeasure T)
  continuous : ContinuousOn U (Icc 0 T)
  representative : ∀ᵐ t ∂timeMeasure T, U t = hUnderlying Ω 1 (u t)
  distributional : HasBulkTimeDerivative Ω T U du

def Nonnegative {n : ℕ} (Ω : Domain n) (η : H10 ℝ Ω) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, 0 ≤ hZeroUnderlying Ω η x

def BulkOrder {n : ℕ} (Ω : Domain n) (U V : Lp ℝ Ω 2) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω, U x ≤ V x

def LateralOrder {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (T : ℝ)
    (u v : ℝ → H ℝ Ω 1) : Prop :=
  ∀ᵐ t ∂timeMeasure T, ∀ᵐ x ∂boundaryMeasure Ω,
    Trace.inclusion Ω hΩ (tr (u t)) x ≤ Trace.inclusion Ω hΩ (tr (v t)) x

/-- The dual-cone inequality with one exceptional set independent of the test. -/
def ConeInequality {n : ℕ} (Ω : Domain n) (T : ℝ) (A : Coefficient n)
    (w : ℝ → H ℝ Ω 1) (dw : ℝ → Hminus1 ℝ Ω) : Prop :=
  ∀ᵐ t ∂timeMeasure T, ∀ η : H10 ℝ Ω, Nonnegative Ω η →
    dw t η + form Ω (A t) (w t) η.val ≤ 0

/-- This formulation initially allows a test-dependent exceptional set. -/
def FixedTestInequality {n : ℕ} (Ω : Domain n) (T : ℝ) (A : Coefficient n)
    (w : ℝ → H ℝ Ω 1) (dw : ℝ → Hminus1 ℝ Ω) : Prop :=
  ∀ η : H10 ℝ Ω, Nonnegative Ω η → ∀ᵐ t ∂timeMeasure T,
    dw t η + form Ω (A t) (w t) η.val ≤ 0

def CommonExceptionalSetStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (T : ℝ) (A : Coefficient n) (ν : ℝ),
    BoundedElliptic Ω T A ν →
    ∀ (w : ℝ → H ℝ Ω 1) (dw : ℝ → Hminus1 ℝ Ω),
      FixedTestInequality Ω T A w dw ↔ ConeInequality Ω T A w dw

/-- Equivalent difference formulation, with every endpoint time included. -/
def DifferenceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T → ∀ (A : Coefficient (m + 1)) (ν : ℝ),
    BoundedElliptic Ω T A ν →
    ∀ (w : ℝ → H ℝ Ω 1) (dw : ℝ → Hminus1 ℝ Ω) (W : ℝ → Lp ℝ Ω 2),
    EnergyPath Ω T w dw W → NonpositiveTrace Ω hΩ tr w T →
    (∀ᵐ x ∂domainMeasure Ω, W 0 x ≤ 0) → ConeInequality Ω T A w dw →
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂domainMeasure Ω, W t x ≤ 0

def ComparisonStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T → ∀ (A : Coefficient (m + 1)) (ν : ℝ),
    BoundedElliptic Ω T A ν →
    ∀ (u v : ℝ → H ℝ Ω 1) (du dv : ℝ → Hminus1 ℝ Ω)
      (U V : ℝ → Lp ℝ Ω 2),
    EnergyPath Ω T u du U → EnergyPath Ω T v dv V →
    BulkOrder Ω (U 0) (V 0) → LateralOrder Ω hΩ tr T u v →
    ConeInequality Ω T A (u - v) (du - dv) →
    ∀ t ∈ Icc 0 T, BulkOrder Ω (U t) (V t)

def FixedTestComparisonStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T → ∀ (A : Coefficient (m + 1)) (ν : ℝ),
    BoundedElliptic Ω T A ν →
    ∀ (u v : ℝ → H ℝ Ω 1) (du dv : ℝ → Hminus1 ℝ Ω)
      (U V : ℝ → Lp ℝ Ω 2),
    EnergyPath Ω T u du U → EnergyPath Ω T v dv V →
    BulkOrder Ω (U 0) (V 0) → LateralOrder Ω hΩ tr T u v →
    FixedTestInequality Ω T A (u - v) (du - dv) →
    ∀ t ∈ Icc 0 T, BulkOrder Ω (U t) (V t)

/-- Ordered sources are elements of the positive dual cone. The equations
are tested on all H¹₀ tests and allow arbitrary Sobolev lateral data. -/
def OrderedSourcesStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T → ∀ (A : Coefficient (m + 1)) (ν : ℝ),
    BoundedElliptic Ω T A ν →
    ∀ (u v : ℝ → H ℝ Ω 1) (du dv f g : ℝ → Hminus1 ℝ Ω)
      (U V : ℝ → Lp ℝ Ω 2),
    EnergyPath Ω T u du U → EnergyPath Ω T v dv V →
    BulkOrder Ω (U 0) (V 0) → LateralOrder Ω hΩ tr T u v →
    (∀ᵐ t ∂timeMeasure T, ∀ η : H10 ℝ Ω,
      du t η + form Ω (A t) (u t) η.val = f t η) →
    (∀ᵐ t ∂timeMeasure T, ∀ η : H10 ℝ Ω,
      dv t η + form Ω (A t) (v t) η.val = g t η) →
    (∀ᵐ t ∂timeMeasure T, ∀ η : H10 ℝ Ω, Nonnegative Ω η → f t η ≤ g t η) →
    ∀ t ∈ Icc 0 T, BulkOrder Ω (U t) (V t)

end P201Specs.Heat.WeakComparison
