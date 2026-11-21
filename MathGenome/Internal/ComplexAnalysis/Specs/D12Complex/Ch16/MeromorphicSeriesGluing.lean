import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.CompatibleExhaustion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicLimits
import Mathlib.Analysis.Meromorphic.Basic

/-! The normal-series gluing step of Mittag–Leffler (paper.tex:2832–2833).
These are ordinary complex representatives, with their given values at poles.
Holomorphy is asserted for the tails after subtraction of each finite head.
Neither connectedness nor nonemptiness of the open set is required. -/

open Set Filter

namespace Specs.D12Complex.Ch16.MeromorphicSeriesGluing
open _root_.D12Complex _root_.D12Complex.Ch15

/-- A summable bound on the expanding stages gives a meromorphic sum,
ordinary locally uniform convergence, and holomorphic tail remainders. -/
def meromorphic_series_gluing_type : Prop :=
  ∀ (Ω : Set ℂ) (K : ℕ → Set ℂ) (t : ℕ → ℂ → ℂ) (b : ℕ → ℝ),
    IsOpen Ω → K 0 = ∅ → IsCompatibleExhaustion Ω K →
    Summable b → (∀ n, 0 ≤ b n) →
    (∀ n, MeromorphicOn (t n) Ω) →
    (∀ n, HolomorphicOn (interior (K n)) (t n)) →
    (∀ n z, z ∈ K n → ‖t n z‖ ≤ b n) →
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧
      TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, t n z) f atTop Ω ∧
      ∀ m, HolomorphicOn (interior (K m))
        (fun z => f z - ∑ n ∈ Finset.range m, t n z)

end Specs.D12Complex.Ch16.MeromorphicSeriesGluing
