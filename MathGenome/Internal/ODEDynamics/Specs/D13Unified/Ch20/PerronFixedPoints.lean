import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Dichotomy
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent interface for the existence, uniqueness and weighted estimate
clauses of paper.tex, Lemma d13:20:perron. Parameter differentiability is a
separate obligation. All matrix norms are induced by the given state norm. -/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace D13Unified.Ch20

abbrev HalfLine := Set.Ici (0 : ℝ)

/-- A weighted path is stored in weighted coordinates. Its actual values are
`WeightedPath.eval`, not the stored bounded continuous function. This encodes
exactly the paths for which `sup (exp (β*t) * ‖w(t)‖)` is finite. -/
structure WeightedPath (β : ℝ) (E : Type*) [NormedAddCommGroup E] where
  weighted : HalfLine →ᵇ E

namespace WeightedPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ}

def coordinates (β : ℝ) (E : Type*) [NormedAddCommGroup E] :
    WeightedPath β E ≃ (HalfLine →ᵇ E) where
  toFun := weighted
  invFun := mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : NormedAddCommGroup (WeightedPath β E) :=
  (coordinates β E).normedAddCommGroup

instance : Module ℝ (WeightedPath β E) :=
  (coordinates β E).addEquiv.module ℝ

instance : NormedSpace ℝ (WeightedPath β E) :=
  (coordinates β E).addEquiv.normedSpace ℝ

/-- Actual unweighted values on the half-line. -/
def eval (w : WeightedPath β E) (t : HalfLine) : E :=
  Real.exp (-β * (t : ℝ)) • w.weighted t

/-- An ambient representative used only under `0 ≤ t`, and in integrals over
nonnegative times. Values outside the original domain do not assert an ODE. -/
def atReal (w : WeightedPath β E) (t : ℝ) : E :=
  if ht : 0 ≤ t then w.eval ⟨t, ht⟩ else 0

/-- Encoding an arbitrary continuous path with a finite weighted bound. -/
def ofPath (β : ℝ) (w : HalfLine → E) (hw : Continuous w)
    (C : ℝ) (hC : ∀ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w t‖ ≤ C) :
    WeightedPath β E :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : HalfLine => Real.exp (β * (t : ℝ)) • w t)
    (by fun_prop) C (by
      intro t
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hC t)⟩

end WeightedPath
end D13Unified.Ch20

namespace Specs.D13Unified.Ch20.PerronFixedPoints
open _root_.D13Unified.Ch20 _root_.D13Unified.Ch07
open Specs.D13Unified.Ch07.MatrixExponential
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.Dichotomy
universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The same canonical projections, transported to the chosen normed space. -/
def projection (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (stable : Bool) : E →L[ℝ] E :=
  matrixOperatorEquiv b (projectionMatrix A stable)

def evolution (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (t : ℝ) : E →L[ℝ] E :=
  matrixOperatorEquiv b (exponentialValue A t)

def dichotomyBounds (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (K α : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    matrixOperatorNorm b (exponentialValue A t * projectionMatrix A true) ≤
      K * Real.exp (-α * t) ∧
    matrixOperatorNorm b (exponentialValue A (-t) * projectionMatrix A false) ≤
      K * Real.exp (-α * t)

/-- The contraction constant, with both the stable and unstable contributions. -/
def contractionRate (K α β δ : ℝ) : ℝ :=
  K * δ * ((α - β)⁻¹ + (α + β)⁻¹)

def kernel (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (r : E → E)
    (β : ℝ) (w : WeightedPath β E) (stable : Bool) (t s : ℝ) : E :=
  evolution b A (t - s) (projection b A stable (r (w.atReal s)))

/-- Absolute convergence accompanies the integral identity: an undefined
Bochner integral, whose totalized value is zero, cannot qualify as a solution. -/
def PerronEquation (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (r : E → E) (β : ℝ) (ξ : E) (w : WeightedPath β E) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    IntervalIntegrable (kernel b A r β w true t) volume 0 t ∧
    IntegrableOn (kernel b A r β w false t) (Ici t) ∧
    w.atReal t = evolution b A t ξ +
      (∫ s in (0 : ℝ)..t, kernel b A r β w true t s) -
      ∫ s in Ici t, kernel b A r β w false t s

/-- Complete original fixed-point conclusion, in arbitrary finite dimension
and arbitrary fixed norm. Empty coordinate types and zero spectral spaces are
allowed. A globally Lipschitz zero-preserving remainder suffices; hence every
cutoff supplied upstream is covered, without assuming a fixed point. -/
def fixedPointsExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ K α β δ : ℝ, 1 ≤ K → 0 < α → dichotomyBounds b A K α →
      0 < β → β < α → 0 ≤ δ →
      contractionRate K α β δ < 1 →
      ∀ r : E → E, r 0 = 0 → (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) →
      ∀ ξ : E, b.equivFun ξ ∈ stableSpaceValue A →
      ∃ w : WeightedPath β E,
        PerronEquation b A r β ξ w ∧
        (∀ v : WeightedPath β E, PerronEquation b A r β ξ v → v = w) ∧
        (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt w.atReal
          (matrixOperatorEquiv b A (w.atReal t) + r (w.atReal t)) (Ici 0) t) ∧
        projection b A true (w.atReal 0) = ξ ∧
        ‖w‖ ≤ K * ‖ξ‖ / (1 - contractionRate K α β δ)

/-- The weighted norm is the actual supremum of weighted path norms. -/
def weightedNormExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (w : WeightedPath β E),
    Continuous w.eval ∧
    ‖w‖ = ⨆ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w.eval t‖

/-- Every continuous path with a finite weighted bound is represented exactly. -/
def weightedRepresentationExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (w : HalfLine → E) (hw : Continuous w)
    (C : ℝ) (hC : ∀ t : HalfLine, Real.exp (β * (t : ℝ)) * ‖w t‖ ≤ C),
    (WeightedPath.ofPath β w hw C hC).eval = w

def weightedCompleteExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (β : ℝ), CompleteSpace (WeightedPath β E)

end Specs.D13Unified.Ch20.PerronFixedPoints
