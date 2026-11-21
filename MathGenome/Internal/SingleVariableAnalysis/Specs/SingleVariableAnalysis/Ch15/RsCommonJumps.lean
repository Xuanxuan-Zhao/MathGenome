import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.MonotoneLimits
import Mathlib.Topology.Order.LiminfLimsup

/-! K03.15.rs_common_jumps, paper.tex:3766–3780.
The infimum/supremum below are the finite one-sided limits on the indicated
closed interval; their limit identities are separate obligations. Right-hand
statements allow c = a, and left-hand statements allow c = b. The limsup is
of the absolute deviation from the actual point value, so no existence of a
one-sided limit of the bounded integrand is assumed. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsCommonJumps
open Set Filter
open scoped Topology
namespace D
export Specs.SingleVariableAnalysis.Ch08.DarbouxSums (boundedOnIntervalValue)
end D
namespace S
export Specs.SingleVariableAnalysis.Ch15.RsSums (integralValue)
end S

noncomputable def rightValue (α : ℝ → ℝ) (c b : ℝ) : ℝ := sInf (α '' Ioc c b)
noncomputable def leftValue (α : ℝ → ℝ) (a c : ℝ) : ℝ := sSup (α '' Ico a c)

def rightLimitIdentity : Prop := ∀ (a b c : ℝ) (α : ℝ → ℝ),
  a ≤ c → c < b → MonotoneOn α (Icc a b) →
  Tendsto α (𝓝[>] c) (𝓝 (rightValue α c b)) ∧
    α c ≤ rightValue α c b

def leftLimitIdentity : Prop := ∀ (a b c : ℝ) (α : ℝ → ℝ),
  a < c → c ≤ b → MonotoneOn α (Icc a b) →
  Tendsto α (𝓝[<] c) (𝓝 (leftValue α a c)) ∧
    leftValue α a c ≤ α c

def rightObstruction : Prop := ∀ (a b c : ℝ) (f α : ℝ → ℝ),
  a ≤ c → c < b → D.boundedOnIntervalValue f a b →
  MonotoneOn α (Icc a b) → 0 < rightValue α c b - α c →
  0 < limsup (fun x => |f x - f c|) (𝓝[>] c) →
  ¬ ∃ I : ℝ, S.integralValue a b f α I

def leftObstruction : Prop := ∀ (a b c : ℝ) (f α : ℝ → ℝ),
  a < c → c ≤ b → D.boundedOnIntervalValue f a b →
  MonotoneOn α (Icc a b) → 0 < α c - leftValue α a c →
  0 < limsup (fun x => |f x - f c|) (𝓝[<] c) →
  ¬ ∃ I : ℝ, S.integralValue a b f α I

/-- Common nonzero same-sided jumps are a special case; the integrand's
one-sided limit may be on either side of its actual value. -/
def rightCommonJump : Prop := ∀ (a b c L : ℝ) (f α : ℝ → ℝ),
  a ≤ c → c < b → D.boundedOnIntervalValue f a b →
  MonotoneOn α (Icc a b) → 0 < rightValue α c b - α c →
  Tendsto f (𝓝[>] c) (𝓝 L) → L ≠ f c →
  ¬ ∃ I : ℝ, S.integralValue a b f α I

def leftCommonJump : Prop := ∀ (a b c L : ℝ) (f α : ℝ → ℝ),
  a < c → c ≤ b → D.boundedOnIntervalValue f a b →
  MonotoneOn α (Icc a b) → 0 < α c - leftValue α a c →
  Tendsto f (𝓝[<] c) (𝓝 L) → L ≠ f c →
  ¬ ∃ I : ℝ, S.integralValue a b f α I

/-- This witness distinguishes opposite-sided jumps. The more extensive mesh
counterexample is a separate source entry and is not assumed here. -/
def oppositeSided : Prop :=
  let α : ℝ → ℝ := fun x => if 0 < x then 1 else 0
  let f : ℝ → ℝ := fun x => if 0 ≤ x then 1 else 0
  MonotoneOn α (Icc (-1) 1) ∧ D.boundedOnIntervalValue f (-1) 1 ∧
  rightValue α 0 1 - α 0 = 1 ∧ f 0 - leftValue f (-1) 0 = 1 ∧
  S.integralValue (-1) 1 f α 1
end Specs.SingleVariableAnalysis.Ch15.RsCommonJumps
