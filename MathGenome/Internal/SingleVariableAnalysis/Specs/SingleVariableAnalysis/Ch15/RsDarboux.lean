import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.DarbouxSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums

/-! K03.15.rs_darboux (paper.tex:3683). Closed-cell weighted Darboux
sums for bounded real functions. Monotonicity is relative to the closed
interval; no continuity or right continuity of the integrator is required.
The zero-cell partition includes the degenerate interval. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsDarboux
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators
namespace D
export Specs.SingleVariableAnalysis.Ch08.DarbouxSums
  (boundedOnIntervalValue cellSupremumValue cellInfimumValue)
end D

abbrev sumType := (f α : ℝ → ℝ) → {a b : ℝ} → (P : PartitionData a b) →
  D.boundedOnIntervalValue f a b → ℝ
noncomputable def upperSumValue : sumType := fun f α {_ _} P hf =>
  ∑ i : Fin P.n, D.cellSupremumValue f P hf i *
    (α (P.point i.succ) - α (P.point i.castSucc))
noncomputable def lowerSumValue : sumType := fun f α {_ _} P hf =>
  ∑ i : Fin P.n, D.cellInfimumValue f P hf i *
    (α (P.point i.succ) - α (P.point i.castSucc))

abbrev integralType := (f α : ℝ → ℝ) → (a b : ℝ) →
  D.boundedOnIntervalValue f a b → ℝ
noncomputable def upperIntegralValue : integralType := fun f α a b hf =>
  sInf (Set.range (fun P : PartitionData a b => upperSumValue f α P hf))
noncomputable def lowerIntegralValue : integralType := fun f α a b hf =>
  sSup (Set.range (fun P : PartitionData a b => lowerSumValue f α P hf))

def refinement : Prop := ∀ (a b : ℝ) (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  ∀ P Q : PartitionData a b,
  Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue Q P →
  lowerSumValue f α P hf ≤ lowerSumValue f α Q hf ∧
  upperSumValue f α Q hf ≤ upperSumValue f α P hf

def tagExtrema : Prop := ∀ (a b : ℝ) (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  ∀ P : PartitionData a b,
  IsGLB (Set.range (fun t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P =>
    Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f α))
    (lowerSumValue f α P hf) ∧
  IsLUB (Set.range (fun t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P =>
    Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f α))
    (upperSumValue f α P hf)

def integralBounds : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  IsGLB (Set.range (fun P : PartitionData a b => upperSumValue f α P hf))
    (upperIntegralValue f α a b hf) ∧
  IsLUB (Set.range (fun P : PartitionData a b => lowerSumValue f α P hf))
    (lowerIntegralValue f α a b hf) ∧
  lowerIntegralValue f α a b hf ≤ upperIntegralValue f α a b hf

def epsilonCriterion : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  (upperIntegralValue f α a b hf = lowerIntegralValue f α a b hf ↔
    ∀ ε : ℝ, 0 < ε → ∃ P : PartitionData a b,
      upperSumValue f α P hf - lowerSumValue f α P hf < ε)

def integrabilityCriterion : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  ((∃ I : ℝ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I) ↔
    upperIntegralValue f α a b hf = lowerIntegralValue f α a b hf)

def integralValue : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ)
  (hf : D.boundedOnIntervalValue f a b), MonotoneOn α (Set.Icc a b) →
  ∀ I : ℝ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I ↔
    upperIntegralValue f α a b hf = lowerIntegralValue f α a b hf ∧
    I = lowerIntegralValue f α a b hf
end Specs.SingleVariableAnalysis.Ch15.RsDarboux
