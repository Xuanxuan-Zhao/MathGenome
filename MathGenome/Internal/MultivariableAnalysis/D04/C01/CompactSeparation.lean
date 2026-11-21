import MathGenome.Internal.MultivariableAnalysis.D04.C01.DistanceFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.CompactSeparation

/-! Positive distance between a nonempty compact set and a disjoint nonempty
closed set, and compact closed neighborhoods inside an open set.
The whole-space case chooses radius one without taking a distance to its
empty complement. Closed thickenings of the empty set are empty. -/

noncomputable section
open Set
namespace D04

def closedThickening {n : ℕ} (K : Set (E n)) (ρ : ℝ) : Set (E n) :=
  Specs.D04.C01.CompactSeparation.Model.closedThickening K ρ

theorem closedThickening_nonempty_eq {n : ℕ} (K : Set (E n))
    (hK : K.Nonempty) (ρ : ℝ) :
    closedThickening K ρ = {x | distanceToSet K hK x ≤ ρ} := by
  simp only [closedThickening, Specs.D04.C01.CompactSeparation.Model.closedThickening,
    dite_eq_left hK, distanceToSet]

theorem closedThickening_empty {n : ℕ} (ρ : ℝ) :
    closedThickening (∅ : Set (E n)) ρ = ∅ := by
  simp [closedThickening, Specs.D04.C01.CompactSeparation.Model.closedThickening]

/-- Minimize the continuous distance to F over K. Its minimum is positive
because F is closed and disjoint from K. -/
theorem compact_closed_separation_bound {n : ℕ} (K F : Set (E n))
    (hneK : K.Nonempty) (hneF : F.Nonempty) (hK : Compact K) (hF : Closed F)
    (hdisj : Disjoint K F) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ F, δ ≤ ‖x - y‖ := by
  have hcK := (compact_iff_isCompact K).mp hK
  have hcF := (closed_iff_isClosed F).mp hF
  obtain ⟨a, ha, hmin⟩ := hcK.exists_isMinOn hneK
    (Metric.continuous_infDist_pt F).continuousOn
  have hapos : 0 < Metric.infDist a F :=
    (hcF.notMem_iff_infDist_pos hneF).mp (fun haf => Set.disjoint_left.mp hdisj ha haf)
  refine ⟨Metric.infDist a F, hapos, ?_⟩
  intro x hx y hy
  exact (hmin hx).trans (by simpa only [dist_eq_norm] using
    (Metric.infDist_le_dist_of_mem (x := x) hy))

/-- The real infimum over all pairwise Euclidean distances is strictly positive. -/
theorem compact_closed_separation {n : ℕ} (K F : Set (E n))
    (hneK : K.Nonempty) (hneF : F.Nonempty) (hK : Compact K) (hF : Closed F)
    (hdisj : Disjoint K F) :
    0 < sInf ((fun p : E n × E n => ‖p.1 - p.2‖) '' (K ×ˢ F)) := by
  obtain ⟨δ, hδ, hbound⟩ := compact_closed_separation_bound K F hneK hneF hK hF hdisj
  apply hδ.trans_le
  apply le_csInf ((hneK.prod hneF).image _)
  rintro r ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact hbound x hx y hy

/-- Every finite-radius sublevel set is closed and bounded. Compactness of K
supplies both a uniform norm bound and a nearest point to each x. -/
theorem compact_closedThickening {n : ℕ} (K : Set (E n)) (ρ : ℝ)
    (hK : Compact K) : Compact (closedThickening K ρ) := by
  by_cases hne : K.Nonempty
  · rw [closedThickening_nonempty_eq K hne]
    have hcK := (compact_iff_isCompact K).mp hK
    obtain ⟨B, hB⟩ := ((compact_iff_closed_bounded K).mp hK).2
    apply (compact_iff_closed_bounded _).mpr
    constructor
    · apply (closed_iff_isClosed _).mpr
      simp_rw [distanceToSet_eq_infDist]
      exact isClosed_le (Metric.continuous_infDist_pt K) continuous_const
    · refine ⟨ρ + B, ?_⟩
      intro x hx
      rw [mem_ofPred_eq, distanceToSet_eq_infDist] at hx
      obtain ⟨y, hy, hdist⟩ := hcK.exists_infDist_eq_dist hne x
      calc
        ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
        _ ≤ ρ + B := add_le_add (by simpa only [hdist, dist_eq_norm] using hx) (hB y hy)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, closedThickening_empty]
    exact compact_empty

theorem exists_compact_distance_neighborhood {n : ℕ} (K U : Set (E n))
    (hne : K.Nonempty) (hK : Compact K) (hU : Open U) (hKU : K ⊆ U) :
    ∃ ρ > 0, {x | distanceToSet K hne x ≤ ρ} ⊆ U ∧
      Compact {x | distanceToSet K hne x ≤ ρ} := by
  by_cases hfull : U = Set.univ
  · refine ⟨1, zero_lt_one, ?_, ?_⟩
    · rw [hfull]; exact subset_univ _
    · rw [← closedThickening_nonempty_eq K hne]
      exact compact_closedThickening K 1 hK
  · have hcompl : Uᶜ.Nonempty := Set.nonempty_compl.mpr hfull
    have hclosed : Closed Uᶜ := (closed_iff_isClosed _).mpr
      ((open_iff_isOpen U).mp hU).isClosed_compl
    obtain ⟨δ, hδ, hbound⟩ := compact_closed_separation_bound K Uᶜ hne hcompl hK
      hclosed (Set.disjoint_compl_right_iff_subset.mpr hKU)
    refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
    · intro x hx
      by_contra hxu
      have hlow : δ ≤ Metric.infDist x K := (Metric.le_infDist hne).mpr (by
        intro y hy
        simpa only [dist_eq_norm, norm_sub_rev] using hbound y hy x hxu)
      have hupp : Metric.infDist x K ≤ δ / 2 := by
        simpa only [mem_ofPred_eq, distanceToSet_eq_infDist] using hx
      exact (not_le_of_gt (half_lt_self hδ)) (hlow.trans hupp)
    · rw [← closedThickening_nonempty_eq K hne]
      exact compact_closedThickening K (δ / 2) hK

theorem exists_compact_closedThickening {n : ℕ} (K U : Set (E n))
    (hK : Compact K) (hU : Open U) (hKU : K ⊆ U) :
    ∃ ρ > 0, closedThickening K ρ ⊆ U ∧ Compact (closedThickening K ρ) := by
  by_cases hne : K.Nonempty
  · obtain ⟨ρ, hρ, hsub, hc⟩ := exists_compact_distance_neighborhood K U hne hK hU hKU
    exact ⟨ρ, hρ, by rwa [closedThickening_nonempty_eq K hne],
      by rwa [closedThickening_nonempty_eq K hne]⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact ⟨1, zero_lt_one, by rw [closedThickening_empty]; exact empty_subset U,
      by rw [closedThickening_empty]; exact compact_empty⟩

end D04
