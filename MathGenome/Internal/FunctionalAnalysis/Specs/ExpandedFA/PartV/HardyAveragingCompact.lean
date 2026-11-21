import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingLp
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Compactness clauses of `fa2:p5:hardy-averaging`, paper.tex 22582–22584
and 22632–22641. All exponents are ENNReal, with finiteness explicit.
The integral formula identifies the actual averaging operator on equivalence
classes; no compactness or boundedness certificate is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal unitInterval Topology
namespace ExpandedFA.PartV.HardyAveragingCompact.Spec

abbrev μ := HardyAveragingLp.Spec.intervalMeasure
abbrev Space := HardyAveragingLp.Spec.Space
abbrev CSpace := HardyAveragingContinuous.Spec.Space

def IsHardyTo {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (T : Space p →L[ℂ] Space q) : Prop :=
  ∀ f : Space p,
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable (f : ℝ → ℂ) volume 0 x) ∧
    (T f : ℝ → ℂ) =ᵐ[μ] HardyAveragingLp.Spec.average (f : ℝ → ℂ)

def IsContinuousHardyTo {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : CSpace →L[ℂ] Space q) : Prop :=
  ∀ f : CSpace, (T f : ℝ → ℂ) =ᵐ[μ]
    HardyAveragingContinuous.Spec.extension (HardyAveragingContinuous.Spec.operatorValue f)

def LpCompactness : Prop :=
  ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    q < p → p ≠ ∞ → ∃ T : Space p →L[ℂ] Space q,
      IsHardyTo T ∧ IsCompactOperator T

def ContinuousCompactness : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
    ∃ T : CSpace →L[ℂ] Space q, IsContinuousHardyTo T ∧ IsCompactOperator T

/-- The discarded output strip, measured in the weaker target norm. -/
def LpStripEstimate : Prop :=
  ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    q < p → p ≠ ∞ → ∀ Q : Space p →L[ℂ] Space p,
    HardyAveragingLp.Spec.IsHardy Q →
    ‖Q‖ ≤ HardyAveragingLp.Spec.conjugateExponent p →
    ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 1 → ∀ f : Space p,
      (eLpNorm (Q f : ℝ → ℂ) q (μ.restrict (Ioo 0 δ))).toReal ≤
        HardyAveragingLp.Spec.conjugateExponent p *
          δ ^ (1 / q.toReal - 1 / p.toReal) * ‖f‖

def ContinuousStripEstimate : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
    ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 1 → ∀ f : CSpace,
      (eLpNorm
        (HardyAveragingContinuous.Spec.extension
          (HardyAveragingContinuous.Spec.operatorValue f))
        q (μ.restrict (Ioo 0 δ))).toReal ≤ δ ^ (1 / q.toReal) * ‖f‖

/-! The compactness assertions also hold over the real scalar field. -/
abbrev RealSpace (p : ℝ≥0∞) := Lp ℝ p μ
abbrev RealCSpace := C(I, ℝ)

def IsRealHardyTo {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (T : RealSpace p →L[ℝ] RealSpace q) : Prop :=
  ∀ f : RealSpace p,
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable (f : ℝ → ℝ) volume 0 x) ∧
    (T f : ℝ → ℝ) =ᵐ[μ] fun x => x⁻¹ * ∫ t in (0 : ℝ)..x, f t

def IsRealContinuousHardyTo {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (T : RealCSpace →L[ℝ] RealSpace q) : Prop :=
  ∀ f : RealCSpace, (T f : ℝ → ℝ) =ᵐ[μ]
    fun x => x⁻¹ * ∫ t in (0 : ℝ)..x, ContinuousMap.IccExtendCM f t

def RealLpCompactness : Prop :=
  ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    q < p → p ≠ ∞ → ∃ T : RealSpace p →L[ℝ] RealSpace q,
      IsRealHardyTo T ∧ IsCompactOperator T

def RealContinuousCompactness : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
    ∃ T : RealCSpace →L[ℝ] RealSpace q, IsRealContinuousHardyTo T ∧ IsCompactOperator T

def RealLpStripEstimate : Prop :=
  ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    q < p → p ≠ ∞ → ∀ Q : RealSpace p →L[ℝ] RealSpace p,
    IsRealHardyTo Q → ‖Q‖ ≤ HardyAveragingLp.Spec.conjugateExponent p →
    ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 1 → ∀ f : RealSpace p,
      (eLpNorm (Q f : ℝ → ℝ) q (μ.restrict (Ioo 0 δ))).toReal ≤
        HardyAveragingLp.Spec.conjugateExponent p *
          δ ^ (1 / q.toReal - 1 / p.toReal) * ‖f‖

def RealContinuousStripEstimate : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
    ∀ T : RealCSpace →L[ℝ] RealSpace q, IsRealContinuousHardyTo T →
    ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 1 → ∀ f : RealCSpace,
      (eLpNorm (T f : ℝ → ℝ) q (μ.restrict (Ioo 0 δ))).toReal ≤
        δ ^ (1 / q.toReal) * ‖f‖

end ExpandedFA.PartV.HardyAveragingCompact.Spec
