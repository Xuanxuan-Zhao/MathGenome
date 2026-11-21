import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.IrrationalRotationNotChaotic
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.RigidRotation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ChaosDefinitions

/-! The irrational rotation counterexample to inferring chaos from dense orbits. -/
namespace D13Unified.Ch17.IrrationalRotationNotChaotic

open Ch15.DiscreteDefinitions Ch15.RigidRotation ChaosDefinitions
open Specs.D13Unified.Ch15.CircleLift (Circle)
open scoped Topology

theorem rotation_isometry (α : ℝ) : Isometry (rotation α) := by
  apply Isometry.of_dist_eq
  intro x y
  exact iterate_dist α x y 1

/-- The ball of half the proposed separation radius works for all forward times. -/
theorem rotation_small_neighborhood (α δ : ℝ) (hδ : 0 < δ) (x : Circle) :
    ∃ U : Set Circle, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ n : ℕ, dist ((rotation α)^[n] x) ((rotation α)^[n] y) < δ := by
  refine ⟨Metric.ball x (δ / 2), Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hδ), ?_⟩
  intro y hy n
  rw [iterate_dist, dist_comm]
  exact lt_trans hy (half_lt_self hδ)

theorem rotation_not_sensitive (α : ℝ) : ¬ SensitiveDependence (rotation α) := by
  rintro ⟨δ, hδ, hs⟩
  obtain ⟨U, hU, hx, hclose⟩ := rotation_small_neighborhood α δ hδ (0 : Circle)
  obtain ⟨y, hy, n, hn⟩ := hs 0 U (hU.mem_nhds hx)
  exact (not_lt_of_gt (hclose y hy n)) hn

theorem irrational_periodicPoints_eq_empty (α : ℝ) (hα : Irrational α) :
    periodicPoints (rotation α) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨n, hn, hfix⟩ := (mem_periodicPoints (rotation α) x).mp hx
  exact irrational_not_periodic α hα x n hn hfix

theorem irrational_rotation_not_chaotic (α : ℝ) (hα : Irrational α) :
    (∀ x : Circle, Dense (orbitSet (rotation α) x)) ∧
    periodicPoints (rotation α) = ∅ ∧
    Isometry (rotation α) ∧
    (∀ (δ : ℝ), 0 < δ → ∀ x : Circle, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ n : ℕ, dist ((rotation α)^[n] x) ((rotation α)^[n] y) < δ) ∧
    ¬ SensitiveDependence (rotation α) ∧ ¬ Chaotic (rotation α) := by
  refine ⟨irrational_dense_forwardOrbit α hα,
    irrational_periodicPoints_eq_empty α hα, rotation_isometry α, ?_,
    rotation_not_sensitive α, ?_⟩
  · intro δ hδ x
    obtain ⟨U, hU, hx, hclose⟩ := rotation_small_neighborhood α δ hδ x
    exact ⟨U, hU.mem_nhds hx, hclose⟩
  · intro hchaos
    exact rotation_not_sensitive α ((chaotic_iff (rotation α)).mp hchaos).2.2

end D13Unified.Ch17.IrrationalRotationNotChaotic
