import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import Mathlib.Topology.Homeomorph.Defs

/-! Independent statements for paper.tex:1382–1401, the injective part of
D12.05.06. Injectivity is only on Ω. A global inverse is a total function
constrained on f '' Ω; no behavior outside that open image is prescribed.
The homeomorphism carries precisely the original function. -/
noncomputable section

namespace Specs.D12Complex.Ch05.UnivalentHolomorphicInverse
open _root_.D12Complex

def injective_holomorphic_deriv_ne_zero_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    Set.InjOn f Ω → ∀ a ∈ Ω, deriv f a ≠ 0

def injective_holomorphic_image_open_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    Set.InjOn f Ω → IsOpen (f '' Ω)

/-- The same inverse works on the whole image, with the reciprocal derivative
at each image point. BiholomorphicPair includes both inverse identities. -/
def injective_holomorphic_inverse_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    Set.InjOn f Ω → ∃ g : ℂ → ℂ, BiholomorphicPair Ω (f '' Ω) f g ∧
      ∀ w ∈ f '' Ω, HasDerivAt g (1 / deriv f (g w)) w ∧
        deriv g w = 1 / deriv f (g w)

def injective_holomorphic_homeomorph_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → HolomorphicOn Ω f →
    Set.InjOn f Ω → ∃ e : Ω ≃ₜ (f '' Ω), ∀ z : Ω, (e z : ℂ) = f z

/-- The source's E is the factorial-series exponential, not a new example
with postulated regularity. Every point has a distinct period translate. -/
def exponential_local_not_global_type : Prop :=
  HolomorphicOn Set.univ E ∧ (∀ z : ℂ, deriv E z ≠ 0) ∧
    (∀ z : ℂ, E (z + (2 * Real.pi : ℂ) * Complex.I) = E z ∧
      z + (2 * Real.pi : ℂ) * Complex.I ≠ z) ∧ ¬ Function.Injective E

end Specs.D12Complex.Ch05.UnivalentHolomorphicInverse
