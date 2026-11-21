import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ContinuityAboveCounterexample

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace D11.Ch01.ContinuityAboveCounterexample

open D11.Ch03

/-- The sole coordinate identifies `Point 1` with the real line. -/
theorem coordinate_bijective :
    Specs.D11.Ch01.ContinuityAboveCounterexample.coordinate_bijective := by
  constructor
  · intro x y h
    apply WithLp.ofLp_injective
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hj] using h
  · intro t
    exact ⟨WithLp.toLp 2 (fun _ : Fin 1 => t), rfl⟩

/-- Exactly the intervals `(n, ∞)`, in the upstream real-line coordinates. -/
def ray (n : ℕ) : Set (Point 1) :=
  (fun x : Point 1 => x (0 : Fin 1)) ⁻¹' Ioi (n : ℝ)

theorem rays_measurable :
    Specs.D11.Ch01.ContinuityAboveCounterexample.rays_measurable := by
  intro n
  apply LebesgueMeasures.native_borel_le 1
  exact (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable measurableSet_Ioi

theorem rays_antitone :
    Specs.D11.Ch01.ContinuityAboveCounterexample.rays_antitone := by
  intro m n hmn x hx
  change (m : ℝ) < x (0 : Fin 1)
  change (n : ℝ) < x (0 : Fin 1) at hx
  exact lt_of_le_of_lt (Nat.cast_le.mpr hmn) hx

theorem rays_intersection :
    Specs.D11.Ch01.ContinuityAboveCounterexample.rays_intersection := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (x (0 : Fin 1))
  exact (lt_asymm hn (mem_iInter.mp hx n))

/-- Native one-dimensional volume agrees with Chapter 3's covering measure
on these Borel rays; both measurable-structure changes are explicit. -/
theorem rays_infinite :
    Specs.D11.Ch01.ContinuityAboveCounterexample.rays_infinite := by
  intro n
  rw [LebesgueMeasures.lebesgue_apply 1 _ (rays_measurable n),
    ← LebesgueMeasures.native_outer_agreement 1]
  have hp := (volume_preserving_funUnique (Fin 1) ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 1))
  have h := hp.measure_preimage (s := Ioi (n : ℝ)) measurableSet_Ioi.nullMeasurableSet
  exact h.trans Real.volume_Ioi

theorem intersection_mass :
    Specs.D11.Ch01.ContinuityAboveCounterexample.intersection_mass := by
  unfold Specs.D11.Ch01.ContinuityAboveCounterexample.intersection_mass
  rw [rays_intersection, measure_empty]

theorem masses_tendsto_top :
    Specs.D11.Ch01.ContinuityAboveCounterexample.masses_tendsto_top := by
  have h : (fun n => LebesgueMeasures.lebesgue 1
      (Specs.D11.Ch01.ContinuityAboveCounterexample.ray_value n)) =
      (fun _ : ℕ => (∞ : ℝ≥0∞)) := funext rays_infinite
  unfold Specs.D11.Ch01.ContinuityAboveCounterexample.masses_tendsto_top
  change Tendsto (fun n => LebesgueMeasures.lebesgue 1
    (Specs.D11.Ch01.ContinuityAboveCounterexample.ray_value n)) atTop (𝓝 ∞)
  rw [h]
  exact tendsto_const_nhds

theorem continuity_above_failure :
    Specs.D11.Ch01.ContinuityAboveCounterexample.continuity_above_failure := by
  intro h
  have heq := tendsto_nhds_unique masses_tendsto_top h
  rw [intersection_mass] at heq
  exact ENNReal.top_ne_zero heq

end D11.Ch01.ContinuityAboveCounterexample
