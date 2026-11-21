import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.RotationErgodicity
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.RotationUniqueErgodic
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.UniqueErgodicUniform
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.RigidRotation
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Tactic.NormNum

namespace D13Unified.Ch19.RotationErgodicity

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators
open D13Unified.Ch19.RotationUniqueErgodic

theorem normalization : Specs.D13Unified.Ch19.RotationErgodicity.normalizationStatement := by
  exact ⟨lebesgueProbability_isProbability, lebesgueProbability_eq_map,
    integral_lebesgueProbability⟩

theorem preserves : Specs.D13Unified.Ch19.RotationErgodicity.preservesStatement :=
  rotation_preserves_lebesgueProbability

theorem ergodic : Specs.D13Unified.Ch19.RotationErgodicity.ergodicStatement := by
  intro α hα
  haveI : IsProbabilityMeasure lebesgueProbability := lebesgueProbability_isProbability
  apply (MeasureDefinitions.isErgodic_iff_native _ _
    (rotation_preserves_lebesgueProbability α)).mpr
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)

theorem uniquelyErgodic : Specs.D13Unified.Ch19.RotationErgodicity.uniquelyErgodicStatement :=
  invariant_probability_unique

lemma rotation_iterate (α : ℝ) (x : Circle) (n : ℕ) :
    (rotation α)^[n] x = x + n • D13Unified.Ch15.CircleLift.quotientMap α :=
  D13Unified.Ch15.RigidRotation.rotation_iterate α x n

/-- Every tail of an irrational orbit meets the open set of translations
farther than 1/4 from zero. -/
lemma arbitrarily_large_far_iterates (α : ℝ) (hα : Irrational α) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (1 / 4 : ℝ) < dist ((rotation α)^[n] 0) 0 := by
  have hd := D13Unified.Ch15.RigidRotation.irrational_dense_forwardOrbit α hα
    ((rotation α)^[N] 0)
  have hne : ({x : Circle | (1 / 4 : ℝ) < dist x 0} : Set Circle).Nonempty := by
    refine ⟨((1 / 2 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
    change (1 / 4 : ℝ) < dist ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) 0
    rw [dist_zero_right, AddCircle.norm_half_period_eq]
    norm_num
  obtain ⟨y, ⟨m, rfl⟩, hy⟩ := hd.exists_mem_open
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)) hne
  refine ⟨m + N, Nat.le_add_left N m, ?_⟩
  change (1 / 4 : ℝ) < dist ((rotation α)^[m] ((rotation α)^[N] 0)) 0 at hy
  simpa only [Function.iterate_add_apply] using hy

/-- A quarter-length closed arc cannot meet its preimage under a translation
whose displacement exceeds a quarter-turn. -/
lemma arc_disjoint_of_far (α : ℝ) (n : ℕ)
    (hn : (1 / 4 : ℝ) < dist ((rotation α)^[n] 0) 0) :
    closedBall (0 : Circle) (1 / 8) ∩
      ((rotation α)^[n] ⁻¹' closedBall 0 (1 / 8)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, htx⟩
  have hx' : dist x 0 ≤ (1 / 8 : ℝ) := hx
  have htx' : dist ((rotation α)^[n] x) 0 ≤ (1 / 8 : ℝ) := htx
  have heq : dist ((rotation α)^[n] 0) 0 = dist ((rotation α)^[n] x) x := by
    simp only [rotation_iterate, zero_add]
    simpa only [add_zero, add_comm] using
      (dist_add_right (n • D13Unified.Ch15.CircleLift.quotientMap α) 0 x).symm
  have ht := dist_triangle ((rotation α)^[n] x) 0 x
  rw [← heq, dist_comm 0 x] at ht
  linarith

theorem nonmixingWitness :
    Specs.D13Unified.Ch19.RotationErgodicity.nonmixingWitnessStatement := by
  intro α hα
  refine ⟨closedBall 0 (1 / 8), measurableSet_closedBall, ?_, ?_⟩
  · change volume (closedBall (0 : AddCircle (1 : ℝ)) (1 / 8)) = _
    rw [AddCircle.volume_closedBall]
    norm_num
  · intro N
    obtain ⟨n, hn, hfar⟩ := arbitrarily_large_far_iterates α hα N
    exact ⟨n, hn, by rw [arc_disjoint_of_far α n hfar, measure_empty]⟩

theorem notMixing : Specs.D13Unified.Ch19.RotationErgodicity.notMixingStatement := by
  intro α hα hmix
  obtain ⟨A, hA, hmass, hzero⟩ := nonmixingWitness α hα
  have hlim := hmix A A hA hA
  change Tendsto (fun n : ℕ => (volume : Measure Circle) (A ∩ ((rotation α)^[n] ⁻¹' A)))
    atTop (𝓝 ((volume : Measure Circle) A * (volume : Measure Circle) A)) at hlim
  have hpos : (0 : ENNReal) < (volume : Measure Circle) A * (volume : Measure Circle) A := by
    rw [hmass]
    positivity
  have hev := hlim.eventually (Ioi_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨n, hn, hz⟩ := hzero N
  have := hN n hn
  simp [hz] at this

/-- Periodic observables descend through the actual quotient map. -/
lemma continuous_periodic_lift (g : ℝ → ℝ) (hg : Continuous g)
    (hp : Function.Periodic g 1) : Continuous (hp.lift : Circle → ℝ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact hg

theorem periodicUniformAverages :
    Specs.D13Unified.Ch19.RotationErgodicity.periodicUniformAveragesStatement := by
  intro α hα g hg hp ε hε
  haveI : IsProbabilityMeasure (volume : Measure Circle) := lebesgueProbability_isProbability
  let ν : ProbabilityMeasure Circle := (volume : Measure Circle).toProbabilityMeasure
  have hν : ∀ η : ProbabilityMeasure Circle,
      MeasureDefinitions.PreservesMeasure (rotation α) (η : Measure Circle) → η = ν := by
    intro η hη
    apply Subtype.ext
    exact invariant_probability_unique α hα (η : Measure Circle) inferInstance hη
  have hbound := D13Unified.Ch19.averages_uniform_bound (rotation α)
    (continuous_id.add continuous_const) ν hν hp.lift
    (continuous_periodic_lift g hg hp) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hI : (∫ y, hp.lift y ∂(ν : Measure Circle)) = ∫ t in (0 : ℝ)..1, g t := by
    exact integral_lebesgueProbability hp.lift
  have hterm (x : ℝ) (j : ℕ) :
      hp.lift ((rotation α)^[j] (D13Unified.Ch15.CircleLift.quotientMap x)) =
        g (x + (j : ℝ) * α) := by
    rw [rotation_iterate]
    change hp.lift ((x : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ))) = _
    rw [← AddCircle.coe_nsmul, ← AddCircle.coe_add, hp.lift_coe, nsmul_eq_mul]
  refine eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro n hn x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hk : N ≤ k := by omega
  have hx := hN k hk (D13Unified.Ch15.CircleLift.quotientMap x)
  rw [hI] at hx
  simpa only [birkhoffAverage, birkhoffSum, smul_eq_mul, hterm, div_eq_mul_inv,
    mul_comm] using hx

end
end D13Unified.Ch19.RotationErgodicity
