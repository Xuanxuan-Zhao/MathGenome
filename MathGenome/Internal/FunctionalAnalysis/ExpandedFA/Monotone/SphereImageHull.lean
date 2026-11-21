import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.SphereImageHull
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24LcsSeparation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! The sphere-image hull theorem, `fa2:p2:schur-cauchy-sphere`.
A weak-star separator is evaluation at a vector. From an interior point,
the positive ray in that direction meets the unit sphere. Monotonicity
then contradicts strict separation. -/

noncomputable section
open scoped Topology
namespace ExpandedFA.Monotone.SphereImageHull

universe u

/-- A nonconstant ray from an interior point meets the unit sphere. -/
lemma exists_pos_norm_add_smul_eq_one {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {x v : X} (hx : ‖x‖ < 1) (hv : v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ‖x + t • v‖ = 1 := by
  let R : ℝ := (1 + ‖x‖) / ‖v‖
  have hR : 0 < R := div_pos (by positivity) (norm_pos_iff.mpr hv)
  have hprod : R * ‖v‖ = 1 + ‖x‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)
  have hfar : 1 ≤ ‖x + R • v‖ := by
    have htri := norm_sub_norm_le (R • v) (-x)
    rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      hprod, add_comm (R • v) x] at htri
    linarith
  have hc : Continuous (fun t : ℝ => ‖x + t • v‖) :=
    (continuous_const.add (continuous_id.smul continuous_const)).norm
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hR.le hc.continuousOn
    (show (1 : ℝ) ∈ Set.Icc ‖x + (0 : ℝ) • v‖ ‖x + R • v‖ from
      ⟨by simpa using hx.le, hfar⟩)
  refine ⟨t, ?_, heq⟩
  by_contra hn
  have ht0 : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
  exact (ne_of_lt hx) (by simpa [ht0] using heq)

/-- Every value on the ball lies in the weak-star closed convex hull of the
values on the unit sphere. No regularity of `A` is required. -/
theorem image_subset_weakStar_closed_convex_hull : Spec.ImageInWeakStarHull.{u} := by
  intro X _ _ hSphere A hA f hf
  let : LocallyConvexSpace ℝ (WeakDual ℝ X) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing ℝ X)
  obtain ⟨x, rfl⟩ := hf
  let C : Set (WeakDual ℝ X) := closure (convexHull ℝ (sphereImage A))
  have hboundary (z : UnitBall X) (hz : ‖(z : X)‖ = 1) : (A z).toWeakDual ∈ C :=
    subset_closure (subset_convexHull ℝ (sphereImage A) ⟨z, hz, rfl⟩)
  by_cases hx : ‖(x : X)‖ = 1
  · exact hboundary x hx
  have hxlt : ‖(x : X)‖ < 1 := lt_of_le_of_ne x.property hx
  have hC : C.Nonempty := by
    obtain ⟨z, hz⟩ := hSphere
    have hz' : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    exact ⟨(A ⟨z, hz'.le⟩).toWeakDual, hboundary ⟨z, hz'.le⟩ hz'⟩
  change (A x).toWeakDual ∈ C
  by_contra hnot
  obtain ⟨ℓ, hℓ, hbd, hsep, _⟩ :=
    ExpandedFA.P1.C24.real_locally_convex_closed_convex_separation
      C (A x).toWeakDual hC isClosed_closure (convex_convexHull ℝ _).closure hnot
  obtain ⟨v, hv⟩ := (topDualPairing ℝ X).dualEmbedding_surjective ℓ
  have heval (g : WeakDual ℝ X) : ℓ g = g v := by
    rw [← hv]
    rfl
  have hv0 : v ≠ 0 := by
    intro hv0
    apply hℓ
    ext g
    change ℓ g = 0
    rw [heval, hv0, map_zero]
  obtain ⟨t, ht, hzt⟩ := exists_pos_norm_add_smul_eq_one hxlt hv0
  let z : UnitBall X := ⟨(x : X) + t • v, hzt.le⟩
  have hle : ℓ (A z).toWeakDual ≤ sSup (ℓ '' C) :=
    le_csSup hbd ⟨(A z).toWeakDual, hboundary z hzt, rfl⟩
  have hstrict : (A z) v < (A x) v := by
    simpa only [heval, StrongDual.toWeakDual_apply] using hle.trans_lt hsep
  have hm := hA z x
  have hdiff : (z : X) - (x : X) = t • v := by
    dsimp [z]
    abel
  rw [hdiff, map_smul, sub_apply, smul_eq_mul] at hm
  have hnegative : t * ((A z) v - (A x) v) < 0 :=
    mul_neg_of_pos_of_neg ht (sub_neg.mpr hstrict)
  exact (not_lt_of_ge hm) hnegative

end ExpandedFA.Monotone.SphereImageHull
