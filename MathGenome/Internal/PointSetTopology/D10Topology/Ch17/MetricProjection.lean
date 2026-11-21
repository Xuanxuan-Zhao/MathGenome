import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.MetricProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! The metric projection of paper.tex, d10:17:projection.
The variational characterization of a convex minimizer yields the estimate
‖p-q‖² ≤ ⟪x-y,p-q⟫ ≤ ‖x-y‖ ‖p-q‖. This proves nonexpansiveness
and uniqueness, without requiring K to have full affine dimension.
-/

open Set

namespace D10Topology.Ch17

abbrev NearestPoint := @MetricProjectionData.NearestPoint
noncomputable abbrev projection := @MetricProjectionData.projection

namespace MetricProjectionLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A pointwise minimizer attains the infimum over the subtype. -/
theorem norm_eq_iInf_of_minimizer {K : Set E} {x p : E} (hp : p ∈ K)
    (hmin : ∀ q ∈ K, ‖x - p‖ ≤ ‖x - q‖) :
    ‖x - p‖ = ⨅ q : K, ‖x - q‖ := by
  let : Nonempty K := ⟨⟨p, hp⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun q => hmin q q.property)
  · apply ciInf_le (f := fun q : K => ‖x - q‖) _ ⟨p, hp⟩
    exact ⟨(0 : ℝ), by rintro _ ⟨q, rfl⟩; exact norm_nonneg _⟩

/-- The projection estimate applies to any two minimizers on a convex set. -/
theorem minimizers_nonexpansive {K : Set E} (hconv : Convex ℝ K)
    {x y p q : E} (hp : p ∈ K) (hq : q ∈ K)
    (hpmin : ∀ z ∈ K, ‖x - p‖ ≤ ‖x - z‖)
    (hqmin : ∀ z ∈ K, ‖y - q‖ ≤ ‖y - z‖) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mp
    (norm_eq_iInf_of_minimizer hp hpmin) q hq
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hconv hq).mp
    (norm_eq_iInf_of_minimizer hq hqmin) p hp
  have hneg : q - p = -(p - q) := by abel
  rw [hneg, inner_neg_right] at h₁
  have hsub : x - y = (x - p) - (y - q) + (p - q) := by abel
  have hsq : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    rw [hsub, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hbound := hsq.trans (real_inner_le_norm (x - y) (p - q))
  by_cases heq : p = q
  · simp [heq]
  · have hpos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
    nlinarith

end MetricProjectionLemmas

variable {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
  (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)

include hK hne hconv

theorem projection_nearest (x : EuclideanSpace ℝ (Fin m)) :
    NearestPoint K x (projection K hK hne x) := by
  exact Classical.choose_spec
    (hK.exists_isMinOn hne (f := fun p => ‖x - p‖)
      (continuous_const.sub continuous_id).norm.continuousOn)

theorem nearest_unique (x : EuclideanSpace ℝ (Fin m)) :
    ∃! p, NearestPoint K x p := by
  refine ⟨projection K hK hne x, projection_nearest K hK hne hconv x, ?_⟩
  intro p hp
  have hproj := projection_nearest K hK hne hconv x
  have h := MetricProjectionLemmas.minimizers_nonexpansive hconv hp.1 hproj.1 hp.2 hproj.2
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using h

theorem nearest_iff_eq_projection (x p : EuclideanSpace ℝ (Fin m)) :
    NearestPoint K x p ↔ p = (projection K hK hne x : EuclideanSpace ℝ (Fin m)) := by
  constructor
  · intro hp
    exact (nearest_unique K hK hne hconv x).unique hp (projection_nearest K hK hne hconv x)
  · rintro rfl
    exact projection_nearest K hK hne hconv x

theorem projection_fixes (x : K) : projection K hK hne x = x := by
  apply Subtype.ext
  apply Eq.symm
  apply (nearest_iff_eq_projection K hK hne hconv x x).mp
  exact ⟨x.property, fun q _ => by simpa only [sub_self, norm_zero] using norm_nonneg (x.val - q)⟩

theorem projection_nonexpansive (x y : EuclideanSpace ℝ (Fin m)) :
    ‖(projection K hK hne x : EuclideanSpace ℝ (Fin m)) - projection K hK hne y‖ ≤
      ‖x - y‖ := by
  have hp := projection_nearest K hK hne hconv x
  have hq := projection_nearest K hK hne hconv y
  exact MetricProjectionLemmas.minimizers_nonexpansive hconv hp.1 hq.1 hp.2 hq.2

theorem projection_continuous_retraction :
    Continuous (projection K hK hne) ∧
      Function.LeftInverse (projection K hK hne)
        (Subtype.val : K → EuclideanSpace ℝ (Fin m)) := by
  have hLip : LipschitzWith 1 (projection K hK hne) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] using
      projection_nonexpansive K hK hne hconv x y
  exact ⟨hLip.continuous, projection_fixes K hK hne hconv⟩

end D10Topology.Ch17
