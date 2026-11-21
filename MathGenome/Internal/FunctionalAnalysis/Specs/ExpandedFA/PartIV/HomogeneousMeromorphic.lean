import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions

/-! Independent objects and the full construction obligation for
`paper.tex`, `fa2:p4:homogeneous-extension`, meromorphic-family stage.

The value of a kernel at zero is immaterial: every integrand is explicitly
zero there. In particular no positivity assumption on the dimension is added.
All duals below are the existing continuous complex-linear Schwartz duals.
No existence or continuity of the desired family is assumed in these objects.
-/

open MeasureTheory
open scoped SchwartzMap ContDiff Topology

noncomputable section

namespace ExpandedFA.PartIV.HomogeneousMeromorphic

open ExpandedFA.Fourier

abbrev MultiIndex (d : ℕ) := Fin d → ℕ

def order {d : ℕ} (α : MultiIndex d) : ℕ := ∑ i, α i

def multiFactorial {d : ℕ} (α : MultiIndex d) : ℕ := ∏ i, (α i).factorial

def multiMonomial {d : ℕ} (α : MultiIndex d) (x : Euclidean d) : ℝ :=
  ∏ i, x i ^ α i

/-- Every index appears exactly once, including the zero-dimensional case. -/
def indices (d m : ℕ) : Finset (MultiIndex d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (m + 1)).filter (fun α => order α = m)

/-- Coordinate partial derivatives, listed in increasing coordinate order. -/
def derivativeWord {d : ℕ} (α : MultiIndex d) : List (Fin d) :=
  (List.ofFn fun i : Fin d => List.replicate (α i) i).flatten

def wordDerivative {d : ℕ} : List (Fin d) → Schwartz ℂ d →L[ℂ] Schwartz ℂ d
  | [] => ContinuousLinearMap.id ℂ _
  | i :: w => (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)).comp
      (wordDerivative w)

def partialDerivative {d : ℕ} (α : MultiIndex d) :
    Schwartz ℂ d →L[ℂ] Schwartz ℂ d := wordDerivative (derivativeWord α)

def evaluation {d : ℕ} (x : Euclidean d) : Tempered ℂ d :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Euclidean d) ℂ)

def jet {d : ℕ} (α : MultiIndex d) : Tempered ℂ d :=
  (evaluation 0).comp (partialDerivative α)

/-- This is `∂^α δ₀`, with the distributional derivative sign. -/
def deltaDerivative {d : ℕ} (α : MultiIndex d) : Tempered ℂ d :=
  (-1 : ℂ) ^ order α • jet α

abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Euclidean d) 1

/-- Unnormalized Euclidean surface measure: mass is `d * volume (ball 0 1)`. -/
def surfaceMeasure (d : ℕ) : Measure (UnitSphere d) :=
  (volume : Measure (Euclidean d)).toSphere

def moment {d : ℕ} (k : Euclidean d → ℂ) (α : MultiIndex d) : ℂ :=
  ∫ θ : UnitSphere d, k θ * (multiMonomial α θ : ℂ) ∂surfaceMeasure d

/-- The residue in the source's multi-index and delta-derivative notation. -/
def residue {d : ℕ} (k : Euclidean d → ℂ) (m : ℕ) : Tempered ℂ d :=
  ∑ α ∈ indices d m,
    (((-1 : ℂ) ^ m / (multiFactorial α : ℂ)) * moment k α) • deltaDerivative α

/-- The coefficient of the Taylor polynomial after angular integration. -/
def taylorCoefficient {d : ℕ} (k : Euclidean d → ℂ) (m : ℕ) : Tempered ℂ d :=
  ∑ α ∈ indices d m, (moment k α / (multiFactorial α : ℂ)) • jet α

def taylorPolynomial {d : ℕ} (N : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) : ℂ :=
  ∑ m ∈ Finset.range N, ∑ α ∈ indices d m,
    jet α φ / (multiFactorial α : ℂ) * (multiMonomial α x : ℂ)

/-- Only the source hypotheses, with no data about a distributional extension. -/
def SmoothHomogeneous {d : ℕ} (k : Euclidean d → ℂ) (lam : ℂ) : Prop :=
  ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      k (a • x) = (a : ℂ) ^ lam * k x

def kernelWeight {d : ℕ} (k : Euclidean d → ℂ) (lam z : ℂ) (x : Euclidean d) : ℂ :=
  if x = 0 then 0 else k x * (‖x‖ : ℂ) ^ (z - lam)

def initialPairing {d : ℕ} (k : Euclidean d → ℂ) (lam z : ℂ)
    (φ : Schwartz ℂ d) : ℂ := ∫ x, kernelWeight k lam z x * φ x

def innerIntegrand {d : ℕ} (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ) (z : ℂ)
    (φ : Schwartz ℂ d) (x : Euclidean d) : ℂ :=
  kernelWeight k lam z x * (φ x - taylorPolynomial N φ x)

def outerIntegrand {d : ℕ} (k : Euclidean d → ℂ) (lam z : ℂ)
    (φ : Schwartz ℂ d) (x : Euclidean d) : ℂ := kernelWeight k lam z x * φ x

def taylorRemainder {d : ℕ} (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ) (z : ℂ)
    (φ : Schwartz ℂ d) : ℂ :=
  (∫ x in Metric.closedBall (0 : Euclidean d) 1, innerIntegrand k lam N z φ x) +
    ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ, outerIntegrand k lam z φ x

def pole (d m : ℕ) : ℂ := -(d : ℂ) - (m : ℂ)

def polarPart {d : ℕ} (k : Euclidean d → ℂ) (N : ℕ) (z : ℂ) : Tempered ℂ d :=
  ∑ m ∈ Finset.range N, (z - pole d m)⁻¹ • taylorCoefficient k m

def halfPlane (d N : ℕ) : Set ℂ := {z | -(d : ℝ) - (N : ℝ) < z.re}

def regularSet (d : ℕ) : Set ℂ := {z | ∀ m : ℕ, z ≠ pole d m}

def schwartzBound {d : ℕ} (M : ℕ) (φ : Schwartz ℂ d) : ℝ :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
    SchwartzMap.seminorm ℂ i j φ

/-- A locally uniform bound by finitely many actual Schwartz seminorms. -/
def LocallyUniformBound {d : ℕ} (E : ℂ → Tempered ℂ d) (U : Set ℂ) : Prop :=
  ∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
    ∀ z ∈ V, ∀ φ : Schwartz ℂ d, ‖E z φ‖ ≤ C * schwartzBound M φ

def scalingEquiv {d : ℕ} (a : ℝ) (ha : a ≠ 0) : Euclidean d ≃L[ℝ] Euclidean d where
  __ := LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha
  continuous_toFun := continuous_const_smul a
  continuous_invFun := continuous_const_smul a⁻¹

/-- The source's test function `φ(·/a)` as a continuous Schwartz operator. -/
def testDilation {d : ℕ} (a : ℝ) (ha : 0 < a) :
    Schwartz ℂ d →L[ℂ] Schwartz ℂ d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scalingEquiv a⁻¹ (inv_ne_zero ha.ne'))

def dilation {d : ℕ} (a : ℝ) (ha : 0 < a) (u : Tempered ℂ d) : Tempered ℂ d :=
  ((a : ℂ) ^ d)⁻¹ • u.comp (testDilation a ha)

/-- The full constructive Taylor-subtraction conclusion. E_N is not an input
certificate: its existence, its integral formula, and its analytic estimates are
part of the proposition that must be proved. I at poles has no assigned value;
the Laurent identity is asserted on a punctured neighborhood. -/
def Construction {d : ℕ} (k : Euclidean d → ℂ) (lam : ℂ) : Prop :=
  ∃ (I : ℂ → Tempered ℂ d) (E : ℕ → ℂ → Tempered ℂ d),
    (∀ z ∈ halfPlane d 0, ∀ φ : Schwartz ℂ d,
      Integrable (fun x => kernelWeight k lam z x * φ x) ∧
        I z φ = initialPairing k lam z φ) ∧
    (∀ N z, z ∈ halfPlane d N → ∀ φ : Schwartz ℂ d,
      IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) ∧
      IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ ∧
      E N z φ = taylorRemainder k lam N z φ) ∧
    (∀ N, (∀ φ : Schwartz ℂ d,
      AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N)) ∧
      LocallyUniformBound (E N) (halfPlane d N)) ∧
    (∀ N z, z ∈ halfPlane d N → z ∈ regularSet d →
      I z = polarPart k N z + E N z) ∧
    (∀ φ : Schwartz ℂ d, AnalyticOnNhd ℂ (fun z => I z φ) (regularSet d)) ∧
    (∀ m, ∃ (V : Set ℂ) (H : ℂ → Tempered ℂ d),
      V ∈ nhds (pole d m) ∧
      (∀ φ : Schwartz ℂ d, AnalyticOnNhd ℂ (fun z => H z φ) V) ∧
      LocallyUniformBound H V ∧
      ∀ z ∈ V, z ≠ pole d m → I z = (z - pole d m)⁻¹ • residue k m + H z) ∧
    (∀ (a : ℝ) (ha : 0 < a) z, z ∈ regularSet d →
      dilation a ha (I z) = (a : ℂ) ^ z • I z)

end ExpandedFA.PartIV.HomogeneousMeromorphic

namespace Specs.ExpandedFA.PartIV.HomogeneousMeromorphic

open _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.PartIV.HomogeneousMeromorphic

def constructionType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam : ℂ),
  SmoothHomogeneous k lam → Construction k lam

def residueFormulaType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (m : ℕ)
    (φ : Schwartz ℂ d),
  residue k m φ = ∑ α ∈ indices d m,
    (moment k α / (multiFactorial α : ℂ)) * jet α φ

def testDilationFormulaType : Prop := ∀ (d : ℕ) (a : ℝ) (ha : 0 < a)
    (φ : Schwartz ℂ d) (x : Euclidean d),
  testDilation a ha φ x = φ (a⁻¹ • x)

def dilationFormulaType : Prop := ∀ (d : ℕ) (a : ℝ) (ha : 0 < a)
    (u : Tempered ℂ d) (φ : Schwartz ℂ d),
  dilation a ha u φ = ((a : ℂ) ^ d)⁻¹ * u (testDilation a ha φ)

def kernelScalingType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam z : ℂ),
  SmoothHomogeneous k lam → ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d,
    kernelWeight k lam z (a • x) = (a : ℂ) ^ z * kernelWeight k lam z x

def initialDilationType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam z : ℂ),
  SmoothHomogeneous k lam → ∀ (a : ℝ) (ha : 0 < a) (φ : Schwartz ℂ d),
    ((a : ℂ) ^ d)⁻¹ * initialPairing k lam z (testDilation a ha φ) =
      (a : ℂ) ^ z * initialPairing k lam z φ

def zeroDimensionType : Prop := ∀ (k : Euclidean 0 → ℂ) (lam : ℂ), Construction k lam

def initialIntegrableType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam z : ℂ),
  SmoothHomogeneous k lam → z ∈ halfPlane d 0 → ∀ φ : Schwartz ℂ d,
    Integrable (fun x => kernelWeight k lam z x * φ x)

def momentIntegrableType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam : ℂ),
  SmoothHomogeneous k lam → ∀ α : MultiIndex d,
    Integrable (fun θ : UnitSphere d => k θ * (multiMonomial α θ : ℂ)) (surfaceMeasure d)

def outerIntegrableType : Prop := ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam z : ℂ),
  SmoothHomogeneous k lam → ∀ φ : Schwartz ℂ d,
    IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ

end Specs.ExpandedFA.PartIV.HomogeneousMeromorphic
