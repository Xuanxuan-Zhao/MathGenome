import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specification of K03.12.interchange_limits, paper.tex:1236–1244.
Functions on a subset E of ℝ are represented by ambient functions tested only
on E. The shared RealApproach covers punctured, right, left, +∞, and −∞
approaches. Its nontriviality condition means accumulation in the specified
direction (directional unboundedness at infinity). All output limits are finite
in the canonical scalar field. No continuity or boundedness is required.

The neighborhood version assumes uniformity only on E ∩ ApproachRegion q r₀
for ONE fixed positive r₀, independent of the error and sequence index. The
whole-domain version assumes uniformity on E. The limit pair f and b represents
the two inner limits. The last conjunct explicitly identifies any two outer
limit values, so the displayed equality of iterated limits is included without
using a total/default limit operator. Indices use the upstream shift n ↦ n+1.
-/

namespace Specs.SingleVariableAnalysis.Ch12.InterchangeLimits

open _root_.SingleVariableAnalysis
open Ch01.SequenceLimit Ch02.OneSided

def realInterchangeLimitsOnApproachNeighborhood : Prop :=
  ∀ (E : Set ℝ) (q : RealApproach) (r₀ : ℝ), 0 < r₀ →
    ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (b : ℕ → ℝ),
      approachNontrivialValue E q →
      Uniform.realUniformConvergesValue
        (fun n (x : ↥(E ∩ approachRegionValue q r₀)) => F n x) (fun x => f x) →
      (∀ n, finiteApproachLimitValue (F n) E q (b n)) →
      ∃ B : ℝ, realSequenceConvergesValue b B ∧
        finiteApproachLimitValue f E q B ∧
        ∀ B₁ B₂ : ℝ, finiteApproachLimitValue f E q B₁ →
          realSequenceConvergesValue b B₂ → B₁ = B₂

def realInterchangeLimits : Prop :=
  ∀ (E : Set ℝ) (q : RealApproach),
    ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (b : ℕ → ℝ),
      approachNontrivialValue E q →
      Uniform.realUniformConvergesValue
        (fun n (x : E) => F n x) (fun x => f x) →
      (∀ n, finiteApproachLimitValue (F n) E q (b n)) →
      ∃ B : ℝ, realSequenceConvergesValue b B ∧
        finiteApproachLimitValue f E q B ∧
        ∀ B₁ B₂ : ℝ, finiteApproachLimitValue f E q B₁ →
          realSequenceConvergesValue b B₂ → B₁ = B₂

def complexInterchangeLimitsOnApproachNeighborhood : Prop :=
  ∀ (E : Set ℝ) (q : RealApproach) (r₀ : ℝ), 0 < r₀ →
    ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (b : ℕ → ℂ),
      approachNontrivialValue E q →
      Uniform.complexUniformConvergesValue
        (fun n (x : ↥(E ∩ approachRegionValue q r₀)) => F n x) (fun x => f x) →
      (∀ n, finiteApproachLimitValue (F n) E q (b n)) →
      ∃ B : ℂ, complexSequenceConvergesValue b B ∧
        finiteApproachLimitValue f E q B ∧
        ∀ B₁ B₂ : ℂ, finiteApproachLimitValue f E q B₁ →
          complexSequenceConvergesValue b B₂ → B₁ = B₂

def complexInterchangeLimits : Prop :=
  ∀ (E : Set ℝ) (q : RealApproach),
    ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (b : ℕ → ℂ),
      approachNontrivialValue E q →
      Uniform.complexUniformConvergesValue
        (fun n (x : E) => F n x) (fun x => f x) →
      (∀ n, finiteApproachLimitValue (F n) E q (b n)) →
      ∃ B : ℂ, complexSequenceConvergesValue b B ∧
        finiteApproachLimitValue f E q B ∧
        ∀ B₁ B₂ : ℂ, finiteApproachLimitValue f E q B₁ →
          complexSequenceConvergesValue b B₂ → B₁ = B₂

end Specs.SingleVariableAnalysis.Ch12.InterchangeLimits
