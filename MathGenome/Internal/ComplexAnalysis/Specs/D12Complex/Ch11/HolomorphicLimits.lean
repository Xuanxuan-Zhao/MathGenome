import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Independent statements for paper.tex:2402–2412, D12.11.02.
The convergence is ordinary complex locally uniform convergence on an arbitrary
open set. Derivatives are actual iterated complex derivatives. Real suprema
below are over the indicated closed disk and circle; continuity and compactness
ensure these sets of norms are bounded and nonempty under the hypotheses.
-/
noncomputable section
open Set Metric Filter

namespace Specs.D12Complex.Ch11.HolomorphicLimits
open _root_.D12Complex

def holomorphic_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (F n)) → TendstoLocallyUniformlyOn F f atTop Ω →
    HolomorphicOn Ω f

def iteratedDeriv_locallyUniform_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (F n)) → TendstoLocallyUniformlyOn F f atTop Ω →
    ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
      (iteratedDeriv k f) atTop Ω

/-- The quantitative conclusion for every sequence index and every order,
including k = 0 and the singleton inner disk r = 0. -/
def holomorphic_limits_disk_estimate_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (F n)) → TendstoLocallyUniformlyOn F f atTop Ω →
    ∀ (a : ℂ) (r R : ℝ), 0 ≤ r → r < R → closedBall a R ⊆ Ω →
    ∀ n k : ℕ,
      sSup ((fun z => ‖iteratedDeriv k (F n) z - iteratedDeriv k f z‖) ''
        closedBall a r) ≤
      ((k.factorial : ℝ) * R / (R - r) ^ (k + 1)) *
        sSup ((fun w => ‖F n w - f w‖) '' sphere a R)

end Specs.D12Complex.Ch11.HolomorphicLimits
