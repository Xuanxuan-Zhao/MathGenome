import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf

/-! Independent specification for `K03.08.darboux_sums`, paper.tex:1910–1928.
The function is real valued and bounded on the whole closed interval. Suprema
and infima are taken on closed cells; no continuity or attained extrema are
assumed. The proof arguments restrict the sums to their stated domain.
The upstream zero-cell convention also covers singleton intervals. -/

namespace Specs.SingleVariableAnalysis.Ch08.DarbouxSums
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators

def boundedOnIntervalType := (ℝ → ℝ) → ℝ → ℝ → Prop
def boundedOnIntervalValue : boundedOnIntervalType := fun f a b =>
  BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b)

abbrev cellType := {a b : ℝ} → (P : PartitionData a b) → Fin P.n → Set ℝ
def cellValue : cellType := fun P i =>
  Set.Icc (P.point i.castSucc) (P.point i.succ)

abbrev cellBoundType := (f : ℝ → ℝ) → {a b : ℝ} → (P : PartitionData a b) →
  boundedOnIntervalValue f a b → Fin P.n → ℝ
noncomputable def cellSupremumValue : cellBoundType := fun f {_ _} P _ i =>
  sSup (f '' cellValue P i)
noncomputable def cellInfimumValue : cellBoundType := fun f {_ _} P _ i =>
  sInf (f '' cellValue P i)

abbrev sumType := (f : ℝ → ℝ) → {a b : ℝ} → (P : PartitionData a b) →
  boundedOnIntervalValue f a b → ℝ
noncomputable def upperSumValue : sumType := fun f {_ _} P hf =>
  ∑ i : Fin P.n, cellSupremumValue f P hf i * Partitions.lengthValue P i
noncomputable def lowerSumValue : sumType := fun f {_ _} P hf =>
  ∑ i : Fin P.n, cellInfimumValue f P hf i * Partitions.lengthValue P i

def cellBounds : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P : PartitionData a b)
  (hf : boundedOnIntervalValue f a b) (i : Fin P.n),
  IsGLB (f '' cellValue P i) (cellInfimumValue f P hf i) ∧
  IsLUB (f '' cellValue P i) (cellSupremumValue f P hf i)

def lowerRefinement : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P Q : PartitionData a b)
  (hf : boundedOnIntervalValue f a b), Partitions.refinesValue Q P →
  lowerSumValue f P hf ≤ lowerSumValue f Q hf

def upperRefinement : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P Q : PartitionData a b)
  (hf : boundedOnIntervalValue f a b), Partitions.refinesValue Q P →
  upperSumValue f Q hf ≤ upperSumValue f P hf

def lowerLeUpper : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P Q : PartitionData a b)
  (hf : boundedOnIntervalValue f a b), lowerSumValue f P hf ≤ upperSumValue f Q hf

def taggedBounds : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P : PartitionData a b)
  (hf : boundedOnIntervalValue f a b) (ξ : Partitions.taggingValue P),
  lowerSumValue f P hf ≤ Partitions.sumValue P ξ f ∧
  Partitions.sumValue P ξ f ≤ upperSumValue f P hf

def degenerateSums : Prop := ∀ (f : ℝ → ℝ) (a : ℝ) (P : PartitionData a a)
  (hf : boundedOnIntervalValue f a a),
  lowerSumValue f P hf = 0 ∧ upperSumValue f P hf = 0

end Specs.SingleVariableAnalysis.Ch08.DarbouxSums
