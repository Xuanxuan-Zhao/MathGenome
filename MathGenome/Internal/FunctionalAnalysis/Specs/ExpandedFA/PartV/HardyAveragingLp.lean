import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Independent specification of the complex Lp clauses of
`paper.tex`, Theorem `fa2:p5:hardy-averaging`, lines 22564–22645.

The measure is Lebesgue measure restricted to the open unit interval. The
exponent is a finite ENNReal strictly greater than one. All formulas involving
Lp functions mean equality almost everywhere, and no continuity of a chosen
representative is assumed. The inverse formula below is for Q - z I.

We specify existence of the bounded operator through its integral formula;
there is no assumed boundedness certificate or assumed operator construction.
The weighted operators are exposed as an intermediate analytic interface.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ExpandedFA.PartV.HardyAveragingLp.Spec

def intervalMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

abbrev Space (p : ℝ≥0∞) := Lp ℂ p intervalMeasure

/-- Reciprocal of the conjugate exponent: 1/p' = 1 - 1/p. -/
def threshold (p : ℝ≥0∞) : ℝ := 1 - 1 / p.toReal

def conjugateExponent (p : ℝ≥0∞) : ℝ := (threshold p)⁻¹

def average (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..x, f t

def weightedAverage (a : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (a - 1) * ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (-a) * f t

def powerProfile (z : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (z⁻¹ - 1)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def IsHardy (Q : Space p →L[ℂ] Space p) : Prop :=
  ∀ f : Space p,
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable (f : ℝ → ℂ) volume 0 x) ∧
    (Q f : ℝ → ℂ) =ᵐ[intervalMeasure] average (f : ℝ → ℂ)

def IsWeightedHardy (a : ℂ) (H : Space p →L[ℂ] Space p) : Prop :=
  ∀ f : Space p,
    (∀ x ∈ Ioc (0 : ℝ) 1,
      IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-a) * f t) volume 0 x) ∧
    (H f : ℝ → ℂ) =ᵐ[intervalMeasure] weightedAverage a (f : ℝ → ℂ)

def OperatorExistence : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ Q : Space p →L[ℂ] Space p, IsHardy Q ∧ ‖Q‖ ≤ conjugateExponent p

def WeightedOperatorExistence : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : ℂ, a.re < threshold p →
      ∃ H : Space p →L[ℂ] Space p,
        IsWeightedHardy a H ∧ ‖H‖ ≤ 1 / (threshold p - a.re)

def PowerMembership (p : ℝ≥0∞) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    (MemLp (powerProfile z) p intervalMeasure ↔ threshold p < (z⁻¹).re)

def PowerEigenfunctions (Q : Space p →L[ℂ] Space p) : Prop :=
  ∀ (z : ℂ), z ≠ 0 → ∀ f : Space p, f ≠ 0 →
    (Q f = z • f ↔ threshold p < (z⁻¹).re ∧
      ∃ c : ℂ, c ≠ 0 ∧
        (f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => c * powerProfile z x)

def EigenvalueDisk (Q : Space p →L[ℂ] Space p) : Prop :=
  {z : ℂ | ∃ f : Space p, f ≠ 0 ∧ Q f = z • f} =
    {z : ℂ | ‖z - (conjugateExponent p / 2 : ℝ)‖ < conjugateExponent p / 2}

def ExteriorResolvent (Q : Space p →L[ℂ] Space p) : Prop :=
  ∀ z : ℂ, z ≠ 0 → (z⁻¹).re < threshold p →
    ∃ R : Space p →L[ℂ] Space p,
      (∀ f, R (Q f - z • f) = f) ∧
      (∀ f, Q (R f) - z • R f = f) ∧
      (∀ f : Space p,
        (∀ x ∈ Ioc (0 : ℝ) 1,
          IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-z⁻¹) * f t) volume 0 x) ∧
        (R f : ℝ → ℂ) =ᵐ[intervalMeasure]
          fun x => -z⁻¹ * f x - z⁻¹ ^ 2 * weightedAverage z⁻¹ (f : ℝ → ℂ) x) ∧
      ‖R‖ ≤ ‖z⁻¹‖ + ‖z⁻¹‖ ^ 2 / (threshold p - (z⁻¹).re)

def SpectrumDisk (Q : Space p →L[ℂ] Space p) : Prop :=
  spectrum ℂ Q =
    {z : ℂ | ‖z - (conjugateExponent p / 2 : ℝ)‖ ≤ conjugateExponent p / 2}

def NormExact (Q : Space p →L[ℂ] Space p) : Prop := ‖Q‖ = conjugateExponent p

def NoZeroEigenvalue (Q : Space p →L[ℂ] Space p) : Prop := Function.Injective Q

def Noncompact (Q : Space p →L[ℂ] Space p) : Prop := ¬ IsCompactOperator Q

/-- All original Lp conclusions, including the actual integral operator.
The power membership assertion is independent of the chosen bounded operator. -/
def FullResult : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    PowerMembership p ∧ ∃ Q : Space p →L[ℂ] Space p,
      IsHardy Q ∧ NormExact Q ∧ PowerEigenfunctions Q ∧ EigenvalueDisk Q ∧
        NoZeroEigenvalue Q ∧ ExteriorResolvent Q ∧ SpectrumDisk Q ∧ Noncompact Q

/-- Analytic eigenfunction interface, for every operator with the integral
formula, rather than for an independently chosen or postulated operator. -/
def EigenfunctionTheorem : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ Q : Space p →L[ℂ] Space p, IsHardy Q →
      NoZeroEigenvalue Q ∧ PowerEigenfunctions Q ∧ EigenvalueDisk Q

def ExteriorResolventTheorem : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ Q : Space p →L[ℂ] Space p, IsHardy Q → ExteriorResolvent Q

/-- The two Fubini identities for the source's weighted averaging integral.
These are analytic claims to prove, not certificates used to define Q or H. -/
def WeightedCompositionTheorem : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (a : ℂ), a ≠ 0 → a.re < threshold p →
      ∀ (Q H : Space p →L[ℂ] Space p), IsHardy Q → IsWeightedHardy a H →
        ∀ f : Space p,
          a • Q (H f) = H f - Q f ∧ a • H (Q f) = H f - Q f

def PowerMembershipTheorem : Prop :=
  ∀ {p : ℝ≥0∞}, 1 < p → p ≠ ∞ → PowerMembership p

/-- A continuation interface only. It does not assert any of its three
analytic hypotheses; the original obligation remains `FullResult`. -/
def Assembly : Prop :=
  OperatorExistence → EigenfunctionTheorem → ExteriorResolventTheorem → FullResult

def AnalyticAssembly : Prop :=
  (OperatorExistence ∧ WeightedOperatorExistence) →
    EigenfunctionTheorem → WeightedCompositionTheorem → FullResult

/-- A reduced continuation interface. The construction and weighted norm bound
are an explicit unproved input, not part of the definition of the operator. -/
def WeightedAssembly : Prop := WeightedOperatorExistence → FullResult

def ExteriorFromWeighted : Prop :=
  WeightedOperatorExistence → ExteriorResolventTheorem

def WeightedPrimitiveIntegrability : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ a : ℂ, a.re < threshold p → ∀ f : Space p,
      ∀ x ∈ Ioc (0 : ℝ) 1,
        IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-a) * f t) volume 0 x

/-! The same integral on the original real Lp space. -/
abbrev RealSpace (p : ℝ≥0∞) := Lp ℝ p intervalMeasure

def IsRealHardy {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : RealSpace p →L[ℝ] RealSpace p) : Prop :=
  ∀ f : RealSpace p,
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable (f : ℝ → ℝ) volume 0 x) ∧
    (Q f : ℝ → ℝ) =ᵐ[intervalMeasure] fun x => x⁻¹ * ∫ t in (0 : ℝ)..x, f t

def RealFullResult : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ Q : RealSpace p →L[ℝ] RealSpace p,
      IsRealHardy Q ∧ ‖Q‖ = conjugateExponent p ∧
      spectrum ℝ Q = Icc (0 : ℝ) (conjugateExponent p) ∧
      {z : ℝ | ∃ f : RealSpace p, f ≠ 0 ∧ Q f = z • f} =
        Ioo (0 : ℝ) (conjugateExponent p) ∧
      Function.Injective Q ∧ ¬ IsCompactOperator Q ∧
      ∀ U : RealSpace p →L[ℝ] RealSpace p, IsRealHardy U → U = Q


end ExpandedFA.PartV.HardyAveragingLp.Spec
