import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RigidRotation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.CircleLift
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

/-! Rigid rotations: periods, dense forward orbits, and preservation of distance. -/
namespace D13Unified.Ch15.RigidRotation

open CircleLift DiscreteDefinitions

noncomputable section

abbrev rotation : Specs.D13Unified.Ch15.RigidRotation.rotationType :=
  Specs.D13Unified.Ch15.RigidRotation.rotation

theorem rotation_quotient (α x : ℝ) :
    rotation α (quotientMap x) = quotientMap (x + α) := by
  exact (AddCircle.coe_add (1 : ℝ) x α).symm

theorem rotation_iterate (α : ℝ) (x : Specs.D13Unified.Ch15.CircleLift.Circle) (n : ℕ) :
    (rotation α)^[n] x = x + n • quotientMap α := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change x + n • quotientMap α + quotientMap α = _
    simp only [succ_nsmul, add_assoc]

theorem rational_leastPeriod (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hpq : p.natAbs.Coprime q) (x : Specs.D13Unified.Ch15.CircleLift.Circle) :
    HasLeastPeriod (rotation ((p : ℝ) / (q : ℝ))) x q := by
  have ho : addOrderOf (quotientMap ((p : ℝ) / (q : ℝ))) = q := by
    simpa only [mul_one, CircleLift.quotientMap,
      Specs.D13Unified.Ch15.CircleLift.quotientMap] using
      (AddCircle.addOrderOf_div_of_gcd_eq_one' (p := (1 : ℝ)) hq hpq)
  have h := (addOrderOf_eq_iff hq).mp ho
  apply (hasLeastPeriod_iff _ _ _).mpr
  refine ⟨hq, ?_, ?_⟩
  · rw [rotation_iterate, h.1, add_zero]
  · intro m hm hmq heq
    rw [rotation_iterate, add_eq_left] at heq
    exact h.2 m hmq hm heq

theorem irrational_dense_forwardOrbit (α : ℝ) (hα : Irrational α) (x : Specs.D13Unified.Ch15.CircleLift.Circle) :
    Dense (orbitSet (rotation α) x) := by
  have hz : DenseRange (fun n : ℤ => n • quotientMap α) := by
    exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  have hn : DenseRange (fun n : ℕ => n • quotientMap α) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have ht : DenseRange (fun n : ℕ => x + n • quotientMap α) := by
    exact (Homeomorph.addLeft x).surjective.denseRange.comp hn
      (Homeomorph.addLeft x).continuous
  change DenseRange (fun n : ℕ => (rotation α)^[n] x)
  simpa only [rotation_iterate] using ht

theorem irrational_not_periodic (α : ℝ) (hα : Irrational α) (x : Specs.D13Unified.Ch15.CircleLift.Circle)
    (n : ℕ) (hn : 0 < n) : (rotation α)^[n] x ≠ x := by
  have hz : DenseRange (fun m : ℤ => m • quotientMap α) := by
    exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  have ho : addOrderOf (quotientMap α) = 0 := AddCircle.denseRange_zsmul_iff.mp hz
  intro h
  rw [rotation_iterate, add_eq_left] at h
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  rw [ho, zero_dvd_iff] at hd
  exact hn.ne' hd

theorem iterate_dist (α : ℝ) (x y : Specs.D13Unified.Ch15.CircleLift.Circle) (n : ℕ) :
    dist ((rotation α)^[n] x) ((rotation α)^[n] y) = dist x y := by
  simp only [rotation_iterate, dist_add_right]

end
end D13Unified.Ch15.RigidRotation
