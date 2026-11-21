import MathGenome.Internal.LinearPDE.P201Specs.Heat.HeatBallMeanValue
import Mathlib.Topology.Connected.Basic

/-! The strong maximum and minimum principles, paper.tex, 2928–2970.
Only interior caloricity and continuity on the half-closed cylinder are needed.
These weaker regularity assumptions in particular include the manuscript's
C^{2,1} solutions with left time derivatives at the final time. No extension
past the final time, or continuity on a lateral boundary, is required. -/
noncomputable section
open Set
namespace P201Specs.Heat

abbrev heatCylinder {n : ℕ} (Ω : Set (Space n)) (T : ℝ) : Set (SpaceTime n) :=
  Ω ×ˢ Ioc 0 T

abbrev openHeatCylinder {n : ℕ} (Ω : Set (Space n)) (T : ℝ) : Set (SpaceTime n) :=
  Ω ×ˢ Ioo 0 T

def strongMaximumStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Set (Space n)), IsOpen Ω → IsConnected Ω →
  ∀ (T : ℝ), 0 < T → ∀ (u : SpaceTime n → ℝ),
  ContinuousOn u (heatCylinder Ω T) →
  IsClassicalCaloricOn u (openHeatCylinder Ω T) →
  ∀ M : ℝ, (∀ z ∈ heatCylinder Ω T, u z ≤ M) →
  ∀ (x₀ : Space n), x₀ ∈ Ω → ∀ (t₀ : ℝ), 0 < t₀ → t₀ ≤ T →
  u (x₀, t₀) = M → ∀ (x : Space n), x ∈ Ω →
  ∀ t : ℝ, 0 < t → t ≤ t₀ → u (x, t) = M

def strongMinimumStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Set (Space n)), IsOpen Ω → IsConnected Ω →
  ∀ (T : ℝ), 0 < T → ∀ (u : SpaceTime n → ℝ),
  ContinuousOn u (heatCylinder Ω T) →
  IsClassicalCaloricOn u (openHeatCylinder Ω T) →
  ∀ m : ℝ, (∀ z ∈ heatCylinder Ω T, m ≤ u z) →
  ∀ (x₀ : Space n), x₀ ∈ Ω → ∀ (t₀ : ℝ), 0 < t₀ → t₀ ≤ T →
  u (x₀, t₀) = m → ∀ (x : Space n), x ∈ Ω →
  ∀ t : ℝ, 0 < t → t ≤ t₀ → u (x, t) = m

end P201Specs.Heat
