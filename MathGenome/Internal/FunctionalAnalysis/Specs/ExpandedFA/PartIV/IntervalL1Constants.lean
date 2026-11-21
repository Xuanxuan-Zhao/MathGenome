import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel

/-! The L¹ clauses of `fa2:p4:sharp-interval-poincare`, paper.tex:19933–19970.
The norms below are the ordinary norms of the continuous AC representative:
closed-interval supremum and Lebesgue integral on (0,1). No differentiability
beyond the accepted Sobolev/primitive interface is imposed. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.PartIV.IntervalL1
open ExpandedFA.Sobolev.OneDimensional

abbrev unitInterval : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
abbrev W11 (𝕜 : Type) [RCLike 𝕜] := W1p 𝕜 unitInterval 1

/-- The genuine closure-defined W¹,¹₀, not an assumed endpoint certificate. -/
def ZeroTrace {𝕜 : Type} [RCLike 𝕜] (u : W11 𝕜) : Prop :=
  u ∈ Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroSpaceValue
    𝕜 1 (lineDomain unitInterval) 1 1 (by norm_num)

def mean {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : 𝕜 := ∫ x in (0 : ℝ)..1, f x

def supNorm {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : ℝ :=
  sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1)

def l1Norm {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : ℝ := ∫ x in (0 : ℝ)..1, ‖f x‖

def Nonconstant {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) : Prop :=
  ∃ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1, f x ≠ f y

/-- Unimodal AC tents may have flat parts or nonlinear sides. Absolute
continuity is supplied by PrimitiveRepresentative in the theorem. -/
def NonnegativeUnimodalTent (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ f 1 = 0 ∧ (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) ∧
    (∃ x ∈ Icc (0 : ℝ) 1, f x ≠ 0) ∧
    ∃ c ∈ Icc (0 : ℝ) 1, MonotoneOn f (Icc 0 c) ∧ AntitoneOn f (Icc c 1)

end ExpandedFA.PartIV.IntervalL1

namespace Specs.ExpandedFA.PartIV.IntervalL1Constants
open _root_.ExpandedFA.PartIV.IntervalL1 _root_.ExpandedFA.Sobolev.OneDimensional

/-- The closed-interval norm is also exactly the essential supremum on the
open interval; recording this avoids an implicit change of norm. -/
def SupNormIdentification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) = ENNReal.ofReal (supNorm f)

def MeanSupBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    supNorm (fun x => f x - mean f) ≤ ‖derivativeLp u‖

def MeanL1Bound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    l1Norm (fun x => f x - mean f) ≤ (1 / 2 : ℝ) * ‖derivativeLp u‖

def MeanSupStrict : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → Nonconstant f →
    supNorm (fun x => f x - mean f) < ‖derivativeLp u‖

def MeanL1Strict : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → Nonconstant f →
    l1Norm (fun x => f x - mean f) < (1 / 2 : ℝ) * ‖derivativeLp u‖

/-- Existence of counterexamples to every smaller constant, for both scalar
fields. Positive derivative norm excludes the vacuous constant function. -/
def MeanSupSharp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (C : ℝ), C < 1 →
    ∃ (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f ∧
      0 < ‖derivativeLp u‖ ∧ C * ‖derivativeLp u‖ < supNorm (fun x => f x - mean f)

def MeanL1Sharp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (C : ℝ), C < 1 / 2 →
    ∃ (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f ∧
      0 < ‖derivativeLp u‖ ∧ C * ‖derivativeLp u‖ < l1Norm (fun x => f x - mean f)

def ZeroSupBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f → ZeroTrace u →
    supNorm f ≤ (1 / 2 : ℝ) * ‖derivativeLp u‖

def ZeroSupSharp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (C : ℝ), C < 1 / 2 →
    ∃ (u : W11 𝕜) (f : ℝ → 𝕜), PrimitiveRepresentative u f ∧ ZeroTrace u ∧
      0 < ‖derivativeLp u‖ ∧ C * ‖derivativeLp u‖ < supNorm f

/-- Every specified optimizer, not just one triangular example. The endpoints
also certify membership in the original W₀ closure, by the accepted trace result. -/
def TentEquality : Prop := ∀ (u : W11 ℝ) (f : ℝ → ℝ),
    PrimitiveRepresentative u f → NonnegativeUnimodalTent f →
    ZeroTrace u ∧ 0 < ‖derivativeLp u‖ ∧ supNorm f = (1 / 2 : ℝ) * ‖derivativeLp u‖

end Specs.ExpandedFA.PartIV.IntervalL1Constants
