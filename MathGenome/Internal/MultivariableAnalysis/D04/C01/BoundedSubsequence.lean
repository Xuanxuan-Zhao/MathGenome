import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.BoundedSubsequence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-! Bounded subsequences are obtained by successive scalar extractions.
No compactness theorem for a vector space is used. -/

noncomputable section
open Filter Topology

namespace D04

/-- A finite collection of bounded scalar sequences admits one common
subsequence on which every sequence converges. Later extractions preserve
all the earlier limits. For the empty collection use the identity index. -/
private theorem finite_scalar_subsequence {ι : Type*} (t : Finset ι)
    (x : ℕ → ι → ℝ) (h : ∀ i ∈ t, ∃ B : ℝ, ∀ k, |x k i| ≤ B) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ i ∈ t, ∃ a : ℝ, Tendsto (fun k => x (s k) i) atTop (𝓝 a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨id, strictMono_id, by simp⟩
  | @insert i t hit ih =>
    obtain ⟨s, hs, hst⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨B, hB⟩ := h i (Finset.mem_insert_self i t)
    -- This is scalar Bolzano–Weierstrass, on a closed real interval.
    obtain ⟨a, _ha, r, hr, hlim⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (-B) B)).tendsto_subseq
        (fun k => abs_le.mp (hB (s k)))
    refine ⟨s ∘ r, hs.comp hr, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨a, hlim⟩
    · obtain ⟨b, hb⟩ := hst j hj
      exact ⟨b, hb.comp hr.tendsto_atTop⟩

/-- Every bounded sequence in `E n`, including the singleton space `E 0`,
has a convergent subsequence with strictly increasing natural indices. -/
theorem bounded_subsequence {n : ℕ} (x : ℕ → E n)
    (hx : ∃ B : ℝ, ∀ k, ‖x k‖ ≤ B) :
    ∃ (s : ℕ → ℕ) (a : E n), StrictMono s ∧
      Tendsto (x ∘ s) atTop (𝓝 a) := by
  classical
  obtain ⟨B, hB⟩ := hx
  obtain ⟨s, hs, hcoord⟩ := finite_scalar_subsequence
    (Finset.univ : Finset (Fin n)) (fun k i => x k i) (by
      intro i _hi
      refine ⟨B, fun k => ?_⟩
      have hi : |x k i| ≤ ‖x k‖ := by
        simpa only [Real.norm_eq_abs] using
          (coordinate_norm_le_maxNorm (x k) i).trans (maxNorm_le_norm (x k))
      exact hi.trans (hB k))
  have hlimits : ∀ i : Fin n, ∃ b : ℝ,
      Tendsto (fun k => x (s k) i) atTop (𝓝 b) :=
    fun i => hcoord i (Finset.mem_univ i)
  choose b hb using hlimits
  refine ⟨s, WithLp.toLp 2 b, hs, ?_⟩
  exact (tendsto_iff_coordinate_tendsto (x ∘ s) _).mpr hb

end D04
