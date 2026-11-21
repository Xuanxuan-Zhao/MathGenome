import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Nat.Log

/-! The dyadic typewriter example, paper.tex:712–718. The sample space is
exactly the half-open interval, with the subspace Borel sigma algebra and
Lebesgue measure. Indexing starts at zero: level m occupies indices
2^m - 1 through 2^(m+1) - 2. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch02.TypewriterCounterexample

abbrev Sample := ↥(Ico (0 : ℝ) 1)

noncomputable def probability : Measure Sample := volume.comap Subtype.val

instance probability_isProbabilityMeasure : IsProbabilityMeasure probability where
  measure_univ := by
    rw [probability, comap_subtype_coe_apply measurableSet_Ico, image_univ, Subtype.range_coe]
    change volume (Ico (0 : ℝ) 1) = 1
    simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

def level (n : ℕ) : ℕ := Nat.log 2 (n + 1)
def slot (n : ℕ) : ℕ := n + 1 - 2 ^ level n
def index (m j : ℕ) : ℕ := 2 ^ m - 1 + j

def dyadic (m j : ℕ) : Set Sample :=
  Subtype.val ⁻¹' Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m)

noncomputable def typewriter (n : ℕ) : Sample → ℝ :=
  (dyadic (level n) (slot n)).indicator (fun _ => 1)

def enumerationType : Prop :=
  (∀ n, slot n < 2 ^ level n ∧ index (level n) (slot n) = n) ∧
  (∀ m j, j < 2 ^ m → level (index m j) = m ∧ slot (index m j) = j) ∧
  Tendsto level atTop atTop

def partitionType : Prop :=
  ∀ m (x : Sample), ∃! j : Fin (2 ^ m), x ∈ dyadic m j

def momentType : Prop :=
  ∀ (p : ℝ), 0 < p → ∀ n,
    (∫ x, |typewriter n x| ^ p ∂probability) = ((2 : ℝ) ^ level n)⁻¹

def lpConvergenceType : Prop :=
  ∀ (p : ℝ), 0 < p →
    (∀ n, Measurable (typewriter n) ∧ MemLp (typewriter n) (ENNReal.ofReal p) probability) ∧
    MemLp (fun _ : Sample => (0 : ℝ)) (ENNReal.ofReal p) probability ∧
    Tendsto (fun n => ∫ x, |typewriter n x - 0| ^ p ∂probability) atTop (𝓝 0)

def probabilityConvergenceType : Prop :=
  Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces.ConvergesInProbabilityValue
    probability typewriter (fun _ => 0)

def oscillationType : Prop :=
  ∀ x : Sample, (∀ N, ∃ n ≥ N, typewriter n x = 1) ∧
    (∀ N, ∃ n ≥ N, typewriter n x = 0)

def nowhereConvergentType : Prop :=
  ∀ (x : Sample) (a : ℝ), ¬ Tendsto (fun n => typewriter n x) atTop (𝓝 a)

def notAlmostSureType : Prop :=
  (¬ ∀ᵐ x ∂probability, Tendsto (fun n => typewriter n x) atTop (𝓝 (0 : ℝ))) ∧
  (∀ Y : Sample → ℝ,
    ¬ ∀ᵐ x ∂probability, Tendsto (fun n => typewriter n x) atTop (𝓝 (Y x))) ∧
  probability {x | ∃ a : ℝ, Tendsto (fun n => typewriter n x) atTop (𝓝 a)} = 0

end Specs.ProbabilityFoundations.Ch02.TypewriterCounterexample
