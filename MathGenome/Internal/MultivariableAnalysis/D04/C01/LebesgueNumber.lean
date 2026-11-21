import MathGenome.Internal.MultivariableAnalysis.D04.C01.Compactness
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.LebesgueNumber

/-! Lebesgue numbers for relatively open covers of compact Euclidean sets.
Represent the relative opens by ambient opens and apply the general metric
compact-cover lemma. A subset of K is bounded, so its real diameter bounds
every pairwise distance. The radius conclusion uses diam(K ∩ B(x,r)) ≤ 2r.
No nonemptiness of K or of the cover index type is assumed. -/

open Set
namespace D04

theorem lebesgue_number {n : ℕ} {ι : Type*}
    (K : Set (E n)) (U : ι → Set (E n))
    (hK : Compact K) (hU : ∀ i, RelativelyOpen K (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ S : Set (E n), S.Nonempty → S ⊆ K →
      Metric.diam S < δ → ∃ i, S ⊆ U i := by
  classical
  have hc : IsCompact K := (compact_iff_isCompact K).mp hK
  choose V hV heq using fun i => (relativelyOpen_iff K (U i)).mp (hU i)
  have hcoverV : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    rw [heq i] at hi
    exact mem_iUnion.mpr ⟨i, hi.2⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hc hV hcoverV
  refine ⟨δ, hδ, ?_⟩
  intro S hS hSK hdiam
  obtain ⟨x, hx⟩ := hS
  obtain ⟨i, hi⟩ := hball x (hSK hx)
  refine ⟨i, ?_⟩
  intro y hy
  rw [heq i]
  refine ⟨hSK hy, hi ?_⟩
  exact (Metric.dist_le_diam_of_mem (hc.isBounded.subset hSK) hy hx).trans_lt hdiam

theorem lebesgue_number_and_relative_balls {n : ℕ} {ι : Type*}
    (K : Set (E n)) (U : ι → Set (E n))
    (hK : Compact K) (hU : ∀ i, RelativelyOpen K (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ δ > 0,
      (∀ S : Set (E n), S.Nonempty → S ⊆ K →
        Metric.diam S < δ → ∃ i, S ⊆ U i) ∧
      (∀ r : ℝ, 0 < r → r < δ / 2 →
        ∀ x ∈ K, ∃ i, relativeBall K x r ⊆ U i) := by
  obtain ⟨δ, hδ, hsmall⟩ := lebesgue_number K U hK hU hcover
  refine ⟨δ, hδ, hsmall, ?_⟩
  intro r hr hrδ x hx
  apply hsmall (relativeBall K x r)
  · exact ⟨x, hx, by simpa [ball] using hr⟩
  · exact inter_subset_left
  · have hdiam : Metric.diam (relativeBall K x r) ≤ 2 * r := by
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      intro y hy z hz
      have hy' : dist y x < r := by simpa [ball, dist_eq_norm] using hy.2
      have hz' : dist z x < r := by simpa [ball, dist_eq_norm] using hz.2
      calc
        dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
        _ ≤ 2 * r := by rw [dist_comm x z]; linarith
    exact hdiam.trans_lt (by linarith)

end D04
