import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.PerronEnvelope
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.HarmonicReplacementPasting

/-! The positive local barriers of paper.tex:2635–2641. The function is
represented by a total real function, but only its values on the cap closure
are constrained. These expected values are independent of the implementation;
no harmonicity or boundary attainment is built into regularity. -/
noncomputable section
open Set Metric Filter
open scoped Topology


namespace Specs.D12Complex.Ch14.BarrierSqueeze
open _root_.D12Complex

def PositiveLocalBarrier_type := Set ℂ → ℂ → ℝ → (ℂ → ℝ) → Prop
def PositiveLocalBarrier_value : PositiveLocalBarrier_type := fun Ω ξ r b =>
  0 < r ∧ SuperharmonicOn (Ω ∩ ball ξ r) b ∧
    ContinuousOn b (closure (Ω ∩ ball ξ r)) ∧ b ξ = 0 ∧
    ∀ z ∈ closure (Ω ∩ ball ξ r), z ≠ ξ → 0 < b z

def RegularBoundaryPoint_type := Set ℂ → ℂ → Prop
def RegularBoundaryPoint_value : RegularBoundaryPoint_type := fun Ω ξ =>
  ξ ∈ frontier Ω ∧ ∃ r : ℝ, ∃ b : ℂ → ℝ, PositiveLocalBarrier_value Ω ξ r b

/-- The complete unrestricted approach from the domain, for every continuous datum. -/
def barrier_squeeze_type : Prop :=
  ∀ (Ω : Set ℂ) (φ : ℂ → ℝ) (ξ : ℂ), IsDomain Ω → Bornology.IsBounded Ω →
    ContinuousOn φ (frontier Ω) → RegularBoundaryPoint_value Ω ξ →
    Tendsto (perronEnvelope Ω φ) (𝓝[Ω] ξ) (𝓝 (φ ξ))

end Specs.D12Complex.Ch14.BarrierSqueeze
