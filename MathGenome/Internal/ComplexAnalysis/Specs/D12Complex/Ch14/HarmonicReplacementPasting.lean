import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicDefinition

/-! Harmonic replacement and continuous pasting, paper.tex:2618–2623.
The disk has positive radius and its entire closed disk lies in the open set.
The interface upper limit is expressed by its epsilon-delta condition, without
assuming values or an extension of the local function on the interface. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- Replace the values in the open disk by the Poisson extension of the
original circle values, retaining the original function elsewhere. -/
def harmonicReplacement (a : ℂ) (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  by classical exact if z ∈ ball a R then diskPoissonExtension a R u z else u z

/-- Take a maximum on the open pasted region and retain `u` outside it. -/
def subharmonicPaste (W : Set ℂ) (u v : ℂ → ℝ) (z : ℂ) : ℝ :=
  by classical exact if z ∈ W then max (u z) (v z) else u z

end D12Complex

namespace Specs.D12Complex.Ch14.HarmonicReplacementPasting
open _root_.D12Complex

def harmonicReplacement_type := ℂ → ℝ → (ℂ → ℝ) → ℂ → ℝ
def harmonicReplacement_value : harmonicReplacement_type := fun a R u z =>
  by classical exact if z ∈ ball a R then diskPoissonExtension a R u z else u z

def subharmonicPaste_type := Set ℂ → (ℂ → ℝ) → (ℂ → ℝ) → ℂ → ℝ
def subharmonicPaste_value : subharmonicPaste_type := fun W u v z =>
  by classical exact if z ∈ W then max (u z) (v z) else u z

def harmonicReplacement_properties_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (a : ℂ) (R : ℝ),
    SubharmonicOn U u → 0 < R → closedBall a R ⊆ U →
    ContinuousOn (harmonicReplacement a R u) U ∧
    SubharmonicOn U (harmonicReplacement a R u) ∧
    HarmonicOn (ball a R) (harmonicReplacement a R u) ∧
    (∀ z ∈ U, u z ≤ harmonicReplacement a R u z)

def harmonicReplacement_monotone_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ) (a : ℂ) (R : ℝ),
    SubharmonicOn U u → SubharmonicOn U v → 0 < R → closedBall a R ⊆ U →
    (∀ z ∈ U, u z ≤ v z) →
    ∀ z ∈ U, harmonicReplacement a R u z ≤ harmonicReplacement a R v z

def subharmonic_pasting_type : Prop :=
  ∀ (U W : Set ℂ) (u v : ℂ → ℝ),
    SubharmonicOn U u → SubharmonicOn W v → W ⊆ U →
    (∀ ξ ∈ U ∩ frontier W, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ W, dist z ξ < δ → v z ≤ u ξ + ε) →
    ContinuousOn (subharmonicPaste W u v) U →
    SubharmonicOn U (subharmonicPaste W u v)

end Specs.D12Complex.Ch14.HarmonicReplacementPasting
