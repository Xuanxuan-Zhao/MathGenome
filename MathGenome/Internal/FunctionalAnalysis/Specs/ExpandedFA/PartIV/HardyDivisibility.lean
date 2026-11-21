import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCommutant
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Beurling

/-! The complete divisibility conclusions of `fa2:p4:hardy-divisibility`.
All quotients are bounded holomorphic functions on the whole open disk.
The zero-pair clause uses the adopted correction at paper.tex:19056–19087. -/
noncomputable section
open MeasureTheory
namespace ExpandedFA.PartIV.HardyDivisibility
open HardyDiskSpec BeurlingSpec

/-- The H² vector with the prescribed bounded analytic values. -/
def boundedVector (b : HInfinity) : H2 :=
  HardyDisk.multiplier b (lp.single 2 0 (1 : ℂ))

def IsZero (b : HInfinity) : Prop := ∀ z : Disk, b.val z = 0

def Divides (a b : HInfinity) : Prop :=
  ∃ q : HInfinity, ∀ z : Disk, b.val z = a.val z * q.val z

def InnerDivides (θ : H2) (b : HInfinity) : Prop :=
  ∃ q : HInfinity, ∀ z : Disk, b.val z = eval θ z * q.val z

def InnerDividesInner (θ η : H2) : Prop :=
  ∃ q : HInfinity, ∀ z : Disk, eval η z = eval θ z * q.val z

def multiplierRange (b : HInfinity) : Submodule ℂ H2 :=
  LinearMap.range (HardyDisk.multiplier b).toLinearMap

def closedSum (b c : HInfinity) : Submodule ℂ H2 :=
  (multiplierRange b ⊔ multiplierRange c).topologicalClosure

def BoundaryQuotientBounded (b O : HInfinity) : Prop :=
  ∃ C : ℝ, ∀ᵐ t ∂AddCircle.haarAddCircle,
    ‖boundary (boundedVector b) t / boundary (boundedVector O) t‖ ≤ C

def IsGreatestCommonInnerDivisor (b c : HInfinity) (θ : H2) : Prop :=
  IsInner θ ∧ InnerDivides θ b ∧ InnerDivides θ c ∧
    ∀ η : H2, IsInner η → InnerDivides η b → InnerDivides η c →
      InnerDividesInner η θ

namespace Spec

def Commutant : Prop := HardyCommutantSpec.ShiftCommutant

def InnerCriterion : Prop := ∀ θ : H2, IsInner θ → ∀ b : HInfinity,
  InnerDivides θ b ↔ (multiplierRange b : Set H2) ⊆ ProductRange θ

def OuterCriterion : Prop := ∀ O : HInfinity, IsOuter (boundedVector O) →
  ∀ b : HInfinity, Divides O b ↔ BoundaryQuotientBounded b O

/-- The closed sum itself supplies a GCD for every pair not both zero. -/
def GreatestCommonDivisor : Prop := ∀ b c : HInfinity,
  (¬IsZero b ∨ ¬IsZero c) → ∃ θ : H2,
    IsGreatestCommonInnerDivisor b c θ ∧
    (closedSum b c : Set H2) = ProductRange θ

/-- Every GCD is this Beurling generator. -/
def GeneratorCharacterization : Prop := ∀ (b c : HInfinity) (θ : H2),
  IsGreatestCommonInnerDivisor b c θ →
    (closedSum b c : Set H2) = ProductRange θ

def Uniqueness : Prop := ∀ (b c : HInfinity) (θ η : H2),
  IsGreatestCommonInnerDivisor b c θ → IsGreatestCommonInnerDivisor b c η →
    ∃ a : ℂ, ‖a‖ = 1 ∧ η = a • θ

def ZeroPair : Prop := ∀ b c : HInfinity, IsZero b → IsZero c →
  closedSum b c = ⊥ ∧
    (¬∃ θ : H2, IsInner θ ∧ (closedSum b c : Set H2) = ProductRange θ) ∧
    (¬∃ θ : H2, IsGreatestCommonInnerDivisor b c θ)

end Spec
/-- Anchor the exported multiplier used by both `boundedVector` and
`multiplierRange` to actual analytic multiplication. The evaluation-injectivity
contract upstream then makes this operator and its vector at 1 unique. -/
def Spec.MultiplierEvaluation : Prop := ∀ (b : HInfinity) (f : H2) (z : Disk),
  eval (HardyDisk.multiplier b f) z = b.val z * eval f z


end ExpandedFA.PartIV.HardyDivisibility
