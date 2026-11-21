import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.GlobalClosedOpen

/-! Global closed/open approximation, paper.tex:915–934.

For the outer approximation, intersect the measurable set with a countable
finite-measure cover. Approximate these intersections by open sets with a
summable error budget whose sum is strictly smaller than the requested error.
Subadditivity controls the excess of their union, even for infinite-measure
sets. Applying the same argument to the complement gives the closed subset.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch03.GlobalClosedOpen

/-- A sigma-finite outer regular measure admits open supersets with arbitrarily
small excess, without a finite-measure hypothesis on the measurable set. -/
theorem exists_open_superset_small_excess {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] (μ : Measure α) [SigmaFinite μ] [μ.OuterRegular]
    {E : Set α} (hE : MeasurableSet E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ G : Set α, E ⊆ G ∧ IsOpen G ∧ μ (G \ E) < ε := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  let A : ℕ → Set α := fun n => E ∩ spanningSets μ n
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    hE.inter (measurableSet_spanningSets μ n)
  have hAfin (n : ℕ) : μ (A n) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
  have hcover : E = ⋃ n, A n := by
    simp only [A, ← inter_iUnion, iUnion_spanningSets, inter_univ]
  choose U hAU hUopen hUfin hUerror using
    fun n => (hAm n).exists_isOpen_sdiff_lt (hAfin n) (hδpos n).ne'
  refine ⟨⋃ n, U n, ?_, isOpen_iUnion hUopen, ?_⟩
  · rw [hcover]
    exact iUnion_mono hAU
  · have herror : (⋃ n, U n) \ E ⊆ ⋃ n, U n \ A n := by
      rintro x ⟨hx, hxE⟩
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, hxn, fun hxA => hxE hxA.1⟩
    calc
      μ ((⋃ n, U n) \ E) ≤ μ (⋃ n, U n \ A n) := measure_mono herror
      _ ≤ ∑' n, μ (U n \ A n) := measure_iUnion_le _
      _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hUerror n).le
      _ < ε := hδsum

open LebesgueMeasures

theorem global_closed_open_approximation :
    Specs.D11.Ch03.GlobalClosedOpen.global_closed_open_approximation := by
  intro d _ E hE ε hε
  let : MeasurableSpace (Point d) := lebesgueSpace d
  change MeasurableSet E at hE
  have hε' : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨G, hEG, hG, hGE⟩ :=
    exists_open_superset_small_excess (lebesgue d) hE hε'
  obtain ⟨H, hEcH, hH, hHEc⟩ :=
    exists_open_superset_small_excess (lebesgue d) hE.compl hε'
  refine ⟨Hᶜ, G, hH.isClosed_compl, hG, ?_, hEG, ?_, hGE⟩
  · intro x hx
    by_contra hxE
    exact hx (hEcH hxE)
  · have heq : E \ Hᶜ = H \ Eᶜ := by
      ext x
      simp only [mem_sdiff, mem_compl_iff, not_not, and_comm]
    rw [heq]
    exact hHEc

end D11.Ch03.GlobalClosedOpen
