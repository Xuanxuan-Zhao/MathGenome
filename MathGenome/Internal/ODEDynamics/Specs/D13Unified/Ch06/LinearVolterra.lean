import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.Gronwall
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.Matrix.Normed

/-! Independent statements for paper.tex, Lemma d13:06:linear-volterra.

The main statements use a complete real normed space and bounded linear
coefficients. This includes arbitrary finite matrix spaces and arbitrary fixed
norms. The matrix statements below retain actual matrix multiplication. The
coefficient bound is the operator norm of left multiplication on the
state space; thus no entrywise norm is mistaken for an operator norm.

Ambient representatives are unique only on their actual closed interval.
Neither their values nor their regularity outside that interval are prescribed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Elementwise

namespace D13Unified.Ch06.LinearVolterra

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous Volterra equation on the entire closed interval. -/
def IsIntegralSolution (a b s : ℝ) (A : ℝ → E →L[ℝ] E) (B : ℝ → E)
    (ξ : E) (Y : ℝ → E) : Prop :=
  ContinuousOn Y (Icc a b) ∧
    ∀ t ∈ Icc a b, Y t = ξ + ∫ r in s..t, (A r (Y r) + B r)

/-- The classical IVP with within derivatives at both included endpoints. -/
def IsDifferentialSolution (a b s : ℝ) (A : ℝ → E →L[ℝ] E) (B : ℝ → E)
    (ξ : E) (Y : ℝ → E) : Prop :=
  ContinuousOn Y (Icc a b) ∧ Y s = ξ ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt Y (A t (Y t) + B t) (Icc a b) t

/-- Left multiplication by an actual matrix, as an operator on the canonical
matrix state space. Other normed realizations are covered by transport below. -/
def matrixAction {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → Fin r → ℝ) →L[ℝ] (Fin n → Fin r → ℝ) :=
  (mulLeftLinearMap (Fin r) ℝ A).toContinuousLinearMap

/-- The matrix action in any normed realization of its finite-dimensional state
space. A continuous linear equivalence need not preserve norms. -/
def matrixActionIn {n r : ℕ} (e : Matrix (Fin n) (Fin r) ℝ ≃L[ℝ] E)
    (A : Matrix (Fin n) (Fin n) ℝ) : E →L[ℝ] E :=
  e.toContinuousLinearMap.comp ((matrixAction A).comp e.symm.toContinuousLinearMap)

end D13Unified.Ch06.LinearVolterra

namespace Specs.D13Unified.Ch06.LinearVolterra

open _root_.D13Unified.Ch06.LinearVolterra
universe u

/-- Existence and uniqueness on the full interval, including a singleton. -/
def Existence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b s : ℝ) (A : ℝ → E →L[ℝ] E) (B : ℝ → E) (ξ : E),
    s ∈ Icc a b → ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) →
    ∃ Y : ℝ → E, IsIntegralSolution a b s A B ξ Y ∧
      ∀ Z : ℝ → E, IsIntegralSolution a b s A B ξ Z → EqOn Z Y (Icc a b)

/-- The integral/differential bridge includes both time directions and endpoints. -/
def DifferentialEquivalence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b s : ℝ) (A : ℝ → E →L[ℝ] E) (B : ℝ → E) (ξ : E) (Y : ℝ → E),
    s ∈ Icc a b → ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) →
    (IsIntegralSolution a b s A B ξ Y ↔ IsDifferentialSolution a b s A B ξ Y)

/-- The sharp inhomogeneous bound uses the upstream continuous extension at L=0. -/
def GrowthBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b s : ℝ) (A : ℝ → E →L[ℝ] E) (B : ℝ → E) (ξ : E) (Y : ℝ → E)
    (L M : ℝ), s ∈ Icc a b →
    ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) →
    0 ≤ L → 0 ≤ M → (∀ t ∈ Icc a b, ‖A t‖ ≤ L) →
    (∀ t ∈ Icc a b, ‖B t‖ ≤ M) → IsIntegralSolution a b s A B ξ Y →
    ∀ t ∈ Icc a b,
      ‖Y t‖ ≤ ‖ξ‖ * Real.exp (L * |t-s|) + M * Ch05.Gronwall.EValue L |t-s|

/-- Quantitative dependence, useful also without assuming existence as an axiom.
The reference solution is bounded by R; only A needs a uniform operator bound. -/
def PerturbationBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b s : ℝ) (A C : ℝ → E →L[ℝ] E) (B D : ℝ → E)
    (ξ η : E) (Y Z : ℝ → E) (L R δA δB : ℝ), s ∈ Icc a b →
    ContinuousOn A (Icc a b) → ContinuousOn C (Icc a b) →
    ContinuousOn B (Icc a b) → ContinuousOn D (Icc a b) →
    0 ≤ L → 0 ≤ R → 0 ≤ δA → 0 ≤ δB →
    (∀ t ∈ Icc a b, ‖A t‖ ≤ L) → (∀ t ∈ Icc a b, ‖Z t‖ ≤ R) →
    (∀ t ∈ Icc a b, ‖A t - C t‖ ≤ δA) →
    (∀ t ∈ Icc a b, ‖B t - D t‖ ≤ δB) →
    IsIntegralSolution a b s A B ξ Y → IsIntegralSolution a b s C D η Z →
    ∀ t ∈ Icc a b,
      ‖Y t - Z t‖ ≤ ‖ξ-η‖ * Real.exp (L * |t-s|) +
        (δA * R + δB) * Ch05.Gronwall.EValue L |t-s|

/-- Uniform convergence of coefficients and initial data gives uniform convergence
of the solutions on the same fixed interval. No varying-domain assertion is used. -/
def UniformDependence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b s : ℝ) (A : ℕ → ℝ → E →L[ℝ] E) (B Y : ℕ → ℝ → E)
    (ξ : ℕ → E) (A₀ : ℝ → E →L[ℝ] E) (B₀ Y₀ : ℝ → E) (ξ₀ : E),
    s ∈ Icc a b → (∀ k, ContinuousOn (A k) (Icc a b)) →
    (∀ k, ContinuousOn (B k) (Icc a b)) →
    ContinuousOn A₀ (Icc a b) → ContinuousOn B₀ (Icc a b) →
    (∀ k, IsIntegralSolution a b s (A k) (B k) (ξ k) (Y k)) →
    IsIntegralSolution a b s A₀ B₀ ξ₀ Y₀ →
    TendstoUniformlyOn A A₀ atTop (Icc a b) →
    TendstoUniformlyOn B B₀ atTop (Icc a b) → Tendsto ξ atTop (𝓝 ξ₀) →
    TendstoUniformlyOn Y Y₀ atTop (Icc a b)

/-- Jointly continuous coefficient families have jointly continuous solutions.
The parameter space may be arbitrary; in particular it may be an open subset of
any finite-dimensional real space as in the paper. -/
def JointDependence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type} [TopologicalSpace P]
    (a b s : ℝ) (A : P → ℝ → E →L[ℝ] E) (B : P → ℝ → E) (ξ : P → E),
    s ∈ Icc a b →
    Continuous (fun q : P × Icc a b => A q.1 q.2) →
    Continuous (fun q : P × Icc a b => B q.1 q.2) → Continuous ξ →
    ∃ Y : P → ℝ → E, (∀ p, IsIntegralSolution a b s (A p) (B p) (ξ p) (Y p)) ∧
      Continuous (fun q : P × Icc a b => Y q.1 q.2)

/-- Actual matrix existence statement in its canonical finite-dimensional topology. -/
def MatrixExistence : Prop :=
  ∀ (n r : ℕ)
    (a b s : ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ : Matrix (Fin n) (Fin r) ℝ),
    s ∈ Icc a b →
    (∀ i j, ContinuousOn (fun t => A t i j) (Icc a b)) →
    ContinuousOn B (Icc a b) →
    ∃ Y : ℝ → Matrix (Fin n) (Fin r) ℝ,
      (ContinuousOn Y (Icc a b) ∧
        ∀ t ∈ Icc a b, Y t = ξ + ∫ u in s..t, (A u * Y u + B u)) ∧
      ∀ Z : ℝ → Matrix (Fin n) (Fin r) ℝ,
        (ContinuousOn Z (Icc a b) ∧
          ∀ t ∈ Icc a b, Z t = ξ + ∫ u in s..t, (A u * Z u + B u)) →
        EqOn Z Y (Icc a b)

/-- Changing normed realization preserves the actual matrix integral equation. -/
def MatrixIntegralBridge : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (e : Matrix (Fin n) (Fin r) ℝ ≃L[ℝ] E)
    (a b s : ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B Y : ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ : Matrix (Fin n) (Fin r) ℝ),
    s ∈ Icc a b → ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) →
    ContinuousOn Y (Icc a b) →
    (IsIntegralSolution a b s (fun t => matrixActionIn e (A t)) (fun t => e (B t))
      (e ξ) (fun t => e (Y t)) ↔
      ∀ t ∈ Icc a b, Y t = ξ + ∫ u in s..t, (A u * Y u + B u))

/-- Matrix growth in every fixed norm, expressed by a normed realization e.
The norm of A is its induced action on that same space. -/
def MatrixGrowthBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (e : Matrix (Fin n) (Fin r) ℝ ≃L[ℝ] E)
    (a b s : ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B Y : ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ : Matrix (Fin n) (Fin r) ℝ)
    (L M : ℝ), s ∈ Icc a b → ContinuousOn A (Icc a b) →
    ContinuousOn B (Icc a b) → ContinuousOn Y (Icc a b) →
    (∀ t ∈ Icc a b, Y t = ξ + ∫ u in s..t, (A u * Y u + B u)) →
    0 ≤ L → 0 ≤ M → (∀ t ∈ Icc a b, ‖matrixActionIn e (A t)‖ ≤ L) →
    (∀ t ∈ Icc a b, ‖e (B t)‖ ≤ M) →
    ∀ t ∈ Icc a b, ‖e (Y t)‖ ≤ ‖e ξ‖ * Real.exp (L * |t-s|) +
      M * Ch05.Gronwall.EValue L |t-s|

/-- Uniform variation for the original matrix coefficients and matrix solutions. -/
def MatrixUniformDependence : Prop :=
  ∀ (n r : ℕ) (a b s : ℝ)
    (A : ℕ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B Y : ℕ → ℝ → Matrix (Fin n) (Fin r) ℝ)
    (ξ : ℕ → Matrix (Fin n) (Fin r) ℝ)
    (A₀ : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B₀ Y₀ : ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ₀ : Matrix (Fin n) (Fin r) ℝ),
    s ∈ Icc a b → (∀ k, ContinuousOn (A k) (Icc a b)) →
    (∀ k, ContinuousOn (B k) (Icc a b)) → ContinuousOn A₀ (Icc a b) →
    ContinuousOn B₀ (Icc a b) → (∀ k, ContinuousOn (Y k) (Icc a b)) →
    ContinuousOn Y₀ (Icc a b) →
    (∀ k t, t ∈ Icc a b → Y k t = ξ k + ∫ u in s..t, (A k u * Y k u + B k u)) →
    (∀ t ∈ Icc a b, Y₀ t = ξ₀ + ∫ u in s..t, (A₀ u * Y₀ u + B₀ u)) →
    TendstoUniformlyOn A A₀ atTop (Icc a b) →
    TendstoUniformlyOn B B₀ atTop (Icc a b) → Tendsto ξ atTop (𝓝 ξ₀) →
    TendstoUniformlyOn Y Y₀ atTop (Icc a b)

/-- Joint parameter continuity for actual matrix equations. -/
def MatrixJointDependence : Prop :=
  ∀ {P : Type} [TopologicalSpace P] (n r : ℕ) (a b s : ℝ)
    (A : P → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B : P → ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ : P → Matrix (Fin n) (Fin r) ℝ),
    s ∈ Icc a b → Continuous (fun q : P × Icc a b => A q.1 q.2) →
    Continuous (fun q : P × Icc a b => B q.1 q.2) → Continuous ξ →
    ∃ Y : P → ℝ → Matrix (Fin n) (Fin r) ℝ,
      (∀ p, ContinuousOn (Y p) (Icc a b) ∧
        ∀ t ∈ Icc a b, Y p t = ξ p + ∫ u in s..t, (A p u * Y p u + B p u)) ∧
      Continuous (fun q : P × Icc a b => Y q.1 q.2)

/-- Endpoint-aware classical formulation for actual matrix solutions. -/
def MatrixDifferentialEquivalence : Prop :=
  ∀ (n r : ℕ) (a b s : ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B Y : ℝ → Matrix (Fin n) (Fin r) ℝ) (ξ : Matrix (Fin n) (Fin r) ℝ),
    s ∈ Icc a b → ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) →
    ((ContinuousOn Y (Icc a b) ∧
        ∀ t ∈ Icc a b, Y t = ξ + ∫ u in s..t, (A u * Y u + B u)) ↔
      ContinuousOn Y (Icc a b) ∧ Y s = ξ ∧
        ∀ t ∈ Icc a b, HasDerivWithinAt Y (A t * Y t + B t) (Icc a b) t)

universe v

/-- The compatible operator-norm version for rectangular operator matrices.
Here A acts on the row space F, while Y and B map the column space G to F.
Thus the coefficient bound is ‖A‖ itself, with no dimension factor. -/
def OperatorGrowthBound : Prop :=
  ∀ {F : Type u} {G : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a b s : ℝ) (A : ℝ → F →L[ℝ] F) (B Y : ℝ → G →L[ℝ] F)
    (ξ : G →L[ℝ] F) (L M : ℝ), s ∈ Icc a b →
    ContinuousOn A (Icc a b) → ContinuousOn B (Icc a b) → ContinuousOn Y (Icc a b) →
    (∀ t ∈ Icc a b, Y t = ξ + ∫ u in s..t, ((A u).comp (Y u) + B u)) →
    0 ≤ L → 0 ≤ M → (∀ t ∈ Icc a b, ‖A t‖ ≤ L) →
    (∀ t ∈ Icc a b, ‖B t‖ ≤ M) →
    ∀ t ∈ Icc a b, ‖Y t‖ ≤ ‖ξ‖ * Real.exp (L*|t-s|) +
      M * Ch05.Gronwall.EValue L |t-s|

end Specs.D13Unified.Ch06.LinearVolterra
