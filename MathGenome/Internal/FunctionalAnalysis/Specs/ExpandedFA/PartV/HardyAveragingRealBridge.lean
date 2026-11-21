import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! Independent real-form interface for the real Hardy averaging conclusions in
`fa2:p5:hardy-averaging`. No spectral or invertibility conclusion is assumed.
The spaces may be zero, nonseparable, or carry any compatible Banach norm. -/

namespace ExpandedFA.PartV.HardyAveragingRealBridge

universe u v

/-- A concrete real form, with bounded real and imaginary coordinate maps. -/
structure RealForm (XR : Type u) (XC : Type v)
    [NormedAddCommGroup XR] [NormedSpace ℝ XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC]
    where
  inclusion : XR →ₗᵢ[ℝ] XC
  re : XC →L[ℝ] XR
  im : XC →L[ℝ] XR
  re_inclusion : ∀ x, re (inclusion x) = x
  im_inclusion : ∀ x, im (inclusion x) = 0
  re_I_inclusion : ∀ x, re (Complex.I • inclusion x) = 0
  im_I_inclusion : ∀ x, im (Complex.I • inclusion x) = x
  reconstruct : ∀ z, z = inclusion (re z) + Complex.I • inclusion (im z)

/-- Bounded inverses are represented by bounded maps, with both inverse laws. -/
def TwoSidedInverse {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A S : X →L[𝕜] X) : Prop :=
  (∀ x, S (A x) = x) ∧ (∀ x, A (S x) = x)

namespace Spec

def ExtendInverse : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    ∀ (t : ℝ) (SR : XR →L[ℝ] XR),
      TwoSidedInverse (TR - t • 1) SR →
      ∃ SC : XC →L[ℂ] XC, TwoSidedInverse (TC - (t : ℂ) • 1) SC ∧
        ∀ z, SC z = F.inclusion (SR (F.re z)) +
          Complex.I • F.inclusion (SR (F.im z))

def RestrictInverse : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    ∀ (t : ℝ) (SC : XC →L[ℂ] XC),
      TwoSidedInverse (TC - (t : ℂ) • 1) SC →
      ∃ SR : XR →L[ℝ] XR, TwoSidedInverse (TR - t • 1) SR ∧
        (∀ x, F.inclusion (SR x) = SC (F.inclusion x)) ∧
        (∀ x, SR x = F.re (SC (F.inclusion x)))

def InverseEquivalence : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    ∀ t : ℝ,
      (∃ SR : XR →L[ℝ] XR, TwoSidedInverse (TR - t • 1) SR) ↔
      (∃ SC : XC →L[ℂ] XC, TwoSidedInverse (TC - (t : ℂ) • 1) SC)

def SpectrumTransport : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    spectrum ℝ TR = {t : ℝ | (t : ℂ) ∈ spectrum ℂ TC}

def EigenvalueTransport : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    ∀ t : ℝ, (∃ x : XR, x ≠ 0 ∧ TR x = t • x) ↔
      (∃ z : XC, z ≠ 0 ∧ TC z = (t : ℂ) • z)

def CompactTransport : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    (IsCompactOperator TR ↔ IsCompactOperator TC)

def NormBounds : Prop :=
  ∀ {XR : Type u} {XC : Type v}
    [NormedAddCommGroup XR] [NormedSpace ℝ XR] [CompleteSpace XR]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [CompleteSpace XC]
    (F : RealForm XR XC) (TR : XR →L[ℝ] XR) (TC : XC →L[ℂ] XC),
    (∀ x, TC (F.inclusion x) = F.inclusion (TR x)) →
    ‖TR‖ ≤ ‖TC‖ ∧ ‖TC‖ ≤ (‖F.re‖ + ‖F.im‖) * ‖TR‖

end Spec
end ExpandedFA.PartV.HardyAveragingRealBridge
