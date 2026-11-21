import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The obstruction example in paper.tex:3282–3286. The base is the whole
complex plane. Continuation is the canonical locally represented germ family,
not just the existence of a function at the terminal point. -/
open scoped Topology
noncomputable section
namespace D12Complex.NoncontinuationExample

/-- The rational function whose germ at zero is considered. -/
def reciprocal (z : ℂ) : ℂ := (1 - z)⁻¹

/-- The straight path from zero to the real point r, normalized to [0,1]. -/
def segmentPath (r : ℝ) (t : unitInterval) : ℂ := ((r * (t : ℝ) : ℝ) : ℂ)

end D12Complex.NoncontinuationExample

namespace Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation
open _root_.D12Complex
open _root_.D12Complex.NoncontinuationExample

def reciprocal_type := ℂ → ℂ
def reciprocal_value : reciprocal_type := fun z => (1 - z)⁻¹

def segmentPath_type := ℝ → unitInterval → ℂ
def segmentPath_value : segmentPath_type := fun r t => ((r * (t : ℝ) : ℝ) : ℂ)

def reciprocal_holomorphic_type : Prop :=
  HolomorphicOn {z : ℂ | z ≠ 1} reciprocal

/-- Even a merely continuous filling of the punctured identity is impossible. -/
def no_continuous_extension_type : Prop :=
  ∀ f : ℂ → ℂ, ContinuousAt f 1 →
    ¬ (∀ᶠ z in 𝓝[≠] (1 : ℂ), (1 - z) * f z = 1)

/-- The initial germ exists, and continues to every real point before 1. -/
def continuation_before_one_type : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 →
    ∃ (φ : HolomorphicGerm (segmentPath r 0)) (Φ : GermFamily (segmentPath r)),
      φ.val = (reciprocal : Filter.Germ (𝓝 (segmentPath r 0)) ℂ) ∧
      IsContinuation Set.univ (segmentPath r) φ Φ

/-- A stronger obstruction: every path from 0 to 1 fails, even if it makes
arbitrary detours. No continuation-existence assumption is hidden here. -/
def no_continuation_to_one_type : Prop :=
  ∀ (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0)),
    γ 0 = 0 → γ 1 = 1 →
    φ.val = (reciprocal : Filter.Germ (𝓝 (γ 0)) ℂ) →
    ¬ ∃ Φ : GermFamily γ, IsContinuation Set.univ γ φ Φ

/-- The conclusion of monodromy also fails if its all-path hypothesis is dropped:
no entire function represents the initial rational germ. -/
def no_entire_extension_type : Prop :=
  ¬ ∃ f : ℂ → ℂ, HolomorphicOn Set.univ f ∧
    (f : Filter.Germ (𝓝 (0 : ℂ)) ℂ) = (reciprocal : Filter.Germ (𝓝 (0 : ℂ)) ℂ)

/-- The explicit counterexample on a simply connected base, along [0,1]. -/
def simply_connected_counterexample_type : Prop :=
  SimplyConnectedSpace ℂ ∧ IsDomain (Set.univ : Set ℂ) ∧
    Continuous (segmentPath 1) ∧ segmentPath 1 0 = 0 ∧ segmentPath 1 1 = 1 ∧
    ∃ φ : HolomorphicGerm (segmentPath 1 0),
      φ.val = (reciprocal : Filter.Germ (𝓝 (segmentPath 1 0)) ℂ) ∧
      ¬ ∃ Φ : GermFamily (segmentPath 1),
        IsContinuation Set.univ (segmentPath 1) φ Φ

end Specs.D12Complex.Ch19.SimplyConnectedNoncontinuation
