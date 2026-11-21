import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveDistributions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLimits
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Function

/-! Independent statements for `fa2:p4:convex-distribution-hessian`.
An ambient representative `f` is required to be continuous only on Ω. Its
values off Ω do not enter the test pairings or convexity. Thus this presentation
includes every continuous real function on the open subspace Ω. No dimension,
nonemptiness, boundedness, or global integrability hypothesis is imposed. -/

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ContDiff Topology

namespace ExpandedFA.PartIV.DistributionHessian
open ExpandedFA.Distributions
open Specs.ExpandedFA.Distributions.DistributionCalculus

variable {d : ℕ} {Ω : Opens (Domain d)}

/-- The regular distribution with Lebesgue density f. Continuity on Ω will
guarantee local integrability whenever its integral formula is used. -/
noncomputable def functionDistribution (f : Domain d → ℝ) : ScalarDistribution ℝ Ω :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume f

/-- The original coordinate second distribution derivatives, with the exact
transpose sign supplied by the upstream word derivative. -/
noncomputable def hessianEntry (u : ScalarDistribution ℝ Ω) (i j : Fin d) :
    ScalarDistribution ℝ Ω := derivativeValue ℝ d Ω [i, j] u

/-- The scalar direction test, including the zero direction and d = 0. -/
noncomputable def directionalSecond (u : ScalarDistribution ℝ Ω) (a : Domain d) :
    ScalarDistribution ℝ Ω := ∑ i, ∑ j, (a i * a j) • hessianEntry u i j

/-- Pair the entire Hessian with one scalar test. Positivity is to be checked
for every nonnegative real test, not just for coordinate directions. -/
noncomputable def pairedHessian (u : ScalarDistribution ℝ Ω) (φ : Tests ℝ Ω) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => hessianEntry u i j φ

end ExpandedFA.PartIV.DistributionHessian

namespace Specs.ExpandedFA.PartIV.DistributionHessian
open _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.PartIV.DistributionHessian
open _root_.ExpandedFA.PartIV.PositiveDistributions

/-- Full principal equivalence from the source. -/
def convexityType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d)) (f : Domain d → ℝ),
  Convex ℝ (Ω : Set (Domain d)) → ContinuousOn f Ω →
    (ConvexOn ℝ (Ω : Set (Domain d)) f ↔
      ∀ a : Domain d, IsPositive (directionalSecond (functionDistribution (Ω := Ω) f) a))

/-- Exact meaning of ∂²_a, rather than an unrelated family of quadratic forms. -/
def directionFormulaType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (u : ScalarDistribution ℝ Ω) (a : Domain d),
  directionalSecond u a =
    (u.comp (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a)).comp (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a)

/-- The actual distribution pairing is the integral of f against the stated
second derivative of the test. Only local continuity is assumed. -/
def pairingType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d)) (f : Domain d → ℝ),
  ContinuousOn f Ω → ∀ (a : Domain d) (φ : Tests ℝ Ω),
    directionalSecond (functionDistribution (Ω := Ω) f) a φ =
      ∫ x, f x *
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ)) x

/-- All scalar tests are exactly positive semidefiniteness of the paired
matrix, using the native matrix predicate (which includes symmetry). -/
def matrixMeaningType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (u : ScalarDistribution ℝ Ω),
  (∀ a : Domain d, IsPositive (directionalSecond u a)) ↔
    ∀ φ : Tests ℝ Ω, (∀ x, 0 ≤ φ x) → (pairedHessian u φ).PosSemidef

/-- Dimension one reduces exactly to the unique positive, locally finite
Radon representation of the coordinate second distribution derivative. -/
def oneDimensionalBridgeType : Prop := ∀ (Ω : Opens (Domain 1))
    (u : ScalarDistribution ℝ Ω),
  (∀ a : Domain 1, IsPositive (directionalSecond u a)) ↔
    ∃! μ : Measure Ω, Represents μ (hessianEntry u 0 0)

/-- The complete one-dimensional convexity/measure assertion in the source;
total mass is not required to be finite. -/
def oneDimensionalConvexityType : Prop := ∀ (Ω : Opens (Domain 1)) (f : Domain 1 → ℝ),
  Convex ℝ (Ω : Set (Domain 1)) → ContinuousOn f Ω →
    (ConvexOn ℝ (Ω : Set (Domain 1)) f ↔
      ∃! μ : Measure Ω, Represents μ (hessianEntry (functionDistribution (Ω := Ω) f) 0 0))

/-- Local uniform convergence of continuous densities suffices for weak
convergence of their regular distributions. No global bound is assumed. -/
def densityLimitType : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (f : ℕ → Domain d → ℝ) (g : Domain d → ℝ),
  (∀ n, ContinuousOn (f n) Ω) → ContinuousOn g Ω →
  (∀ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω →
    TendstoUniformlyOn f g atTop K) →
  DistributionConverges (fun n => functionDistribution (Ω := Ω) (f n))
    (functionDistribution (Ω := Ω) g)

end Specs.ExpandedFA.PartIV.DistributionHessian
