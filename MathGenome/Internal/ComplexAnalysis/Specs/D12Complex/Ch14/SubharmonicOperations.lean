import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicDefinition
import Mathlib.Topology.Order.Lattice

/-! The linear and maximum operations of paper.tex:2618–2623.
The canonical predicate includes continuity on the open set. Finite sums
include the empty sum; finite maxima explicitly require a nonempty family. -/
noncomputable section
open Set Metric
open scoped BigOperators

namespace Specs.D12Complex.Ch14.SubharmonicOperations
open _root_.D12Complex

def subharmonicOn_const_type : Prop :=
  ∀ (U : Set ℂ) (c : ℝ), IsOpen U → SubharmonicOn U (fun _ => c)

def harmonicOn_subharmonicOn_type : Prop :=
  ∀ (U : Set ℂ) (h : ℂ → ℝ), HarmonicOn U h → SubharmonicOn U h

def subharmonicOn_add_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ), SubharmonicOn U u → SubharmonicOn U v →
    SubharmonicOn U (fun z => u z + v z)

def subharmonicOn_nonneg_mul_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (c : ℝ), 0 ≤ c → SubharmonicOn U u →
    SubharmonicOn U (fun z => c * u z)

def subharmonicOn_nonneg_linearCombination_type : Prop :=
  ∀ {ι : Type*} (s : Finset ι) (U : Set ℂ) (c : ι → ℝ) (u : ι → ℂ → ℝ),
    IsOpen U → (∀ i ∈ s, 0 ≤ c i) → (∀ i ∈ s, SubharmonicOn U (u i)) →
    SubharmonicOn U (fun z => ∑ i ∈ s, c i * u i z)

def subharmonicOn_max_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ), SubharmonicOn U u → SubharmonicOn U v →
    SubharmonicOn U (fun z => max (u z) (v z))

def subharmonicOn_finset_max_type : Prop :=
  ∀ {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U : Set ℂ) (u : ι → ℂ → ℝ),
    IsOpen U → (∀ i ∈ s, SubharmonicOn U (u i)) →
    SubharmonicOn U (fun z => s.sup' hs (fun i => u i z))

def subharmonicOn_add_const_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (c : ℝ), SubharmonicOn U u →
    SubharmonicOn U (fun z => u z + c)

def subharmonicOn_sub_harmonic_type : Prop :=
  ∀ (U : Set ℂ) (u h : ℂ → ℝ), SubharmonicOn U u → HarmonicOn U h →
    SubharmonicOn U (fun z => u z - h z)

end Specs.D12Complex.Ch14.SubharmonicOperations
