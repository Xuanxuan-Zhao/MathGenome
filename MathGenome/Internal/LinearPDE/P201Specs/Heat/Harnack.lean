import MathGenome.Internal.LinearPDE.P201Specs.Heat.HeatBallMeanValue
import Mathlib.Topology.Connected.Basic

/-! Local parabolic Harnack inequality, paper.tex, pde:heat-harnack.
`V` is an arbitrary connected set, with no openness assumption. The real
supremum and infimum are accompanied by boundedness assertions. The constant
is chosen before both the solution and the final cylinder time. -/
noncomputable section
open Set
namespace P201Specs.Heat.Harnack

def localParabolicHarnackStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n) (V : Set (Space n)),
    IsConnected V → IsCompact (closure V) → closure V ⊆ (Ω : Set (Space n)) →
  ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
  ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, t₂ < T → ∀ u : SpaceTime n → ℝ,
      IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
      (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
      BddAbove ((fun x => u (x,t₁)) '' V) ∧
      BddBelow ((fun y => u (y,t₂)) '' V) ∧
      sSup ((fun x => u (x,t₁)) '' V) ≤
        C * sInf ((fun y => u (y,t₂)) '' V)

end P201Specs.Heat.Harnack
