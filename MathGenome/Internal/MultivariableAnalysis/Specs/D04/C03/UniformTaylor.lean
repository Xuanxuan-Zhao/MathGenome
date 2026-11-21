import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces

/-! Compact-uniform Taylor, including degree zero. A total real function ω
represents its restriction to [0,ρ]. The compact neighborhood C and its
uniform continuity make the degree-zero assertion explicit. The optional
next-derivative estimate uses the very same radius. Empty K is permitted. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C03.UniformTaylor
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model

def uniform_taylorType : Prop :=
  ∀ {n m : ℕ} (k : ℕ) (K U : Set (E n)) (f : E n → E m),
    IsCompact K → IsOpen U → K ⊆ U → CrOn k U f →
    ∃ (ρ : ℝ), 0 < ρ ∧ ∃ (C : Set (E n)) (ω : ℝ → ℝ),
      IsCompact C ∧ K ⊆ interior C ∧ C ⊆ U ∧ UniformContinuousOn f C ∧
      (∀ s ∈ Icc (0 : ℝ) ρ, 0 ≤ ω s) ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ a ∈ K, ∀ h : E n, ‖h‖ ≤ ρ →
        (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) ∧
        ‖taylorRemainder k f a h‖ ≤ ω ‖h‖ * ‖h‖^k / (k.factorial : ℝ)) ∧
      (CrOn (k+1) U f → ∃ M : ℝ, 0 ≤ M ∧
        ∀ a ∈ K, ∀ h : E n, ‖h‖ ≤ ρ →
          ‖taylorRemainder k f a h‖ ≤ M * ‖h‖^(k+1) / ((k+1).factorial : ℝ))

end Specs.D04.C03.UniformTaylor
