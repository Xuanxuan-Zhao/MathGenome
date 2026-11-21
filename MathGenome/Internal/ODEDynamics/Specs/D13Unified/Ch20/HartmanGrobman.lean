import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.BoundedNonlinearConjugacy
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Cutoff
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for paper.tex, Theorem d13:20:hartman-grobman.
A global homeomorphism for a bounded extension is restricted by the open sets
V,W. The original field is only C¹ on U, and the conjugacy keeps real time.
No regularity of the homeomorphism beyond continuity in both directions is
imposed. Arbitrary finite-dimensional real norms and zero dimension are allowed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal

namespace Specs.D13Unified.Ch20.HartmanGrobman
open _root_.D13Unified.Ch07 _root_.D13Unified.Ch20.Green
open _root_.D13Unified.Ch20.BoundedNonlinearConjugacy
open Specs.D13Unified.Ch07.MatrixExponential
open Specs.D13Unified.Ch20.HyperbolicSplitting
universe u v

/-- Uniform exponential control of both improper tails, for every bounded
forcing with the same norm bound. In particular the estimate is uniform in
the initial state and in the finite Picard iterates. -/
def tailsExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (K α : ℝ),
    DichotomyBounds b A K α → ∀ (M t R : ℝ), 0 ≤ R →
      ∀ g : ℝ →ᵇ E, ‖g‖ ≤ M →
        ‖∫ s in Iic (t-R), kernel b A true g t s‖ +
          ‖∫ s in Ioi (t+R), kernel b A false g t s‖ ≤
          (2*K/α)*M*Real.exp (-α*R)

/-- Continuity of both bounded-correction maps for any complete continuous
flow of the small bounded extension. Compact-time convergence is included. -/
def completeConjugacyExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ (K α : ℝ), DichotomyBounds b A K α →
    ∀ (r : E →ᵇ E) (L : ℝ≥0),
      ContDiff ℝ 1 (r : E → E) → r 0 = 0 → LipschitzWith L r →
      (2*K/α)*(L : ℝ) < 1 →
    ∀ φ : ℝ → E → E, Continuous (Function.uncurry φ) →
      (∀ y, φ 0 y = y) →
      (∀ y t, HasDerivAt (fun s => φ s y)
        (matrixOperatorEquiv b A (φ t y) + r (φ t y)) t) →
      ∃ (z : E → (ℝ →ᵇ E)) (H : E ≃ₜ E),
        (∀ x, IsCorrection b A r x (z x) ∧
          (∀ w, IsCorrection b A r x w → w = z x)) ∧
        (∀ x, ‖z x‖ ≤ (2*K/α)*‖r‖) ∧
        (∀ x, H x = x + z x 0) ∧ H 0 = 0 ∧
        (∀ t x, H (matrixOperatorEquiv b (exponentialValue A t) x) = φ t (H x)) ∧
        Continuous (fun q : ℝ × E => z q.2 q.1) ∧
        (∀ x (J : Set ℝ), IsCompact J →
          TendstoUniformlyOn (fun y t => z y t) (fun t => z x t) (𝓝 x) J) ∧
        (∀ y, ∃ g : ℝ →ᵇ E, (∀ t, g t = r (φ t y)) ∧
          H.symm y = y - greenValue b A g 0)

/-- A time-preserving conjugacy on actual neighborhoods. The second clause
compares every original solution on any open interval with any starting time;
its values must stay in W, and equality is asserted whenever the corresponding
linear trajectory stays in V. The first clause also constructs the nonlinear
trajectory directly from every linear segment remaining in V. -/
def localConjugacyExpected : Prop :=
  ∀ {n : Type u} {E : Type v} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (U : Set E) (f : E → E) (p : E),
    IsOpen U → p ∈ U → ContDiffOn ℝ 1 f U → f p = 0 →
    HasFDerivAt f (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∃ (H : E ≃ₜ E) (V W : Set E),
      IsOpen V ∧ IsOpen W ∧ (0 : E) ∈ V ∧ p ∈ W ∧ W ⊆ U ∧
      H 0 = p ∧ H '' V = W ∧
      (∀ x ∈ V, ∀ (s : ℝ) (J : Set ℝ), IsOpen J →
        (∀ t ∈ J, matrixOperatorEquiv b (exponentialValue A (t-s)) x ∈ V) →
        ∀ t ∈ J, H (matrixOperatorEquiv b (exponentialValue A (t-s)) x) ∈ W ∧
          HasDerivAt (fun q => H (matrixOperatorEquiv b (exponentialValue A (q-s)) x))
            (f (H (matrixOperatorEquiv b (exponentialValue A (t-s)) x))) t) ∧
      (∀ (J : Set ℝ), IsOpen J → OrdConnected J →
        ∀ s ∈ J, ∀ y : ℝ → E, (∀ t ∈ J, y t ∈ W) →
          (∀ t ∈ J, HasDerivAt y (f (y t)) t) →
          ∀ t ∈ J,
            matrixOperatorEquiv b (exponentialValue A (t-s)) (H.symm (y s)) ∈ V →
            H (matrixOperatorEquiv b (exponentialValue A (t-s)) (H.symm (y s))) = y t)

end Specs.D13Unified.Ch20.HartmanGrobman
