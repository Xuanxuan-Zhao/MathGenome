import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.BoundedOrbitFixedPoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.AsymptoticCenters
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Dynamics.FixedPoints.Topology

namespace ExpandedFA.BanachConvex.BoundedOrbitFixedPoint
open Set Filter
universe u
noncomputable section

variable {X : Type u} [NormedAddCommGroup X] {C : Set X}

/-- Dropping the first term does not change the actual real limsup radius. -/
lemma radius_shift (s : ℕ → X) (x : X) :
    AsymptoticCenters.radius (fun n => s (n + 1)) x = AsymptoticCenters.radius s x := by
  unfold AsymptoticCenters.radius
  change limsup ((fun n => ‖x - s n‖) ∘ (fun n : ℕ => n + 1)) atTop = _
  rw [limsup_comp, map_add_atTop_eq_nat]

/-- Nonexpansiveness and the orbit identity compare radii after one shift. -/
lemma radius_map_le (T : C → C) (hT : LipschitzWith 1 T) (a : C)
    (hb : Bornology.IsBounded (range (orbit T a))) (x : C) :
    AsymptoticCenters.radius (orbit T a) (T x : X) ≤
      AsymptoticCenters.radius (orbit T a) (x : X) := by
  rw [← radius_shift (orbit T a) (T x : X)]
  apply limsup_le_limsup
  · apply Eventually.of_forall
    intro n
    have h := hT.dist_le_mul x (T^[n] a)
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm,
      orbit, Function.iterate_succ_apply'] using h
  · exact AsymptoticCenters.distances_cobounded _ _
  · exact AsymptoticCenters.distances_bounded hb _

theorem orbit_center_fixed : Spec.OrbitCenterFixed.{u} := by
  intro X _ _ _ _ C hne hclosed hconv T hT a hb
  refine ⟨AsymptoticCenters.unique_center X C (orbit T a) hne hclosed hconv hb
    (fun n => (T^[n] a).property), ?_⟩
  intro c hc
  apply Subtype.ext
  apply AsymptoticCenters.center_unique hb hconv _ hc
  refine ⟨(T c).property, fun x hx => ?_⟩
  exact (radius_map_le T hT a hb c).trans (hc.2 x hx)

/-- Relative continuity combined with closedness of C gives ambient closedness. -/
lemma fixedSet_closed (hclosed : IsClosed C) (T : C → C) (hT : LipschitzWith 1 T) :
    IsClosed (fixedSet T) :=
  hclosed.isClosedMap_subtype_val _ (isClosed_fixedPoints hT.continuous)

variable [NormedSpace ℝ X] [StrictConvexSpace ℝ X]

/-- The two distance bounds from the endpoints force a fixed convex combination. -/
lemma fixedSet_convex (hconv : Convex ℝ C) (T : C → C) (hT : LipschitzWith 1 T) :
    Convex ℝ (fixedSet T) := by
  rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩ s t hs ht hst
  change T p' = p' at hp'
  change T q' = q' at hq'
  let z : C := ⟨s • (p' : X) + t • (q' : X), hconv p'.property q'.property hs ht hst⟩
  have hs' : 1 - t = s := by linarith
  have hz : (z : X) = AffineMap.lineMap (p' : X) (q' : X) t := by
    simp only [AffineMap.lineMap_apply_module, hs']
    rfl
  have hpz : dist (p' : X) (z : X) = t * dist (p' : X) (q' : X) := by
    rw [hz, dist_left_lineMap, Real.norm_of_nonneg ht]
  have hzq : dist (z : X) (q' : X) = s * dist (p' : X) (q' : X) := by
    rw [hz, dist_lineMap_right, hs', Real.norm_of_nonneg hs]
  have h₁ : dist (p' : X) (T z : X) ≤ t * dist (p' : X) (q' : X) := by
    have h := hT.dist_le_mul p' z
    simpa only [NNReal.coe_one, one_mul, hp', Subtype.dist_eq, hpz] using h
  have h₂ : dist (T z : X) (q' : X) ≤ s * dist (p' : X) (q' : X) := by
    have h := hT.dist_le_mul z q'
    simpa only [NNReal.coe_one, one_mul, hq', Subtype.dist_eq, hzq] using h
  have htri := dist_triangle (p' : X) (T z : X) (q' : X)
  have hsum : s * dist (p' : X) (q' : X) + t * dist (p' : X) (q' : X) =
      dist (p' : X) (q' : X) := by rw [← add_mul, hst, one_mul]
  have he₁ : dist (p' : X) (T z : X) = t * dist (p' : X) (q' : X) := by
    linarith
  have he₂ : dist (T z : X) (q' : X) = (1 - t) * dist (p' : X) (q' : X) := by
    rw [hs']
    linarith
  have hfix : (T z : X) = (z : X) :=
    (eq_lineMap_of_dist_eq_mul_of_dist_eq_mul he₁ he₂).trans hz.symm
  exact ⟨z, (show T z = z from Subtype.ext hfix), rfl⟩

theorem fixed_set_closed_convex : Spec.FixedSetClosedConvex.{u} := by
  intro X _ _ _ _ C _hne hclosed hconv T hT
  exact ⟨fixedSet_closed hclosed T hT, fixedSet_convex hconv T hT⟩

end
end ExpandedFA.BanachConvex.BoundedOrbitFixedPoint
