import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.MetricClosedRegular

/-!
Metric Borel regularity with finite balls (paper.tex:5392–5403).

A finite Borel measure on a metric space is weakly regular. We apply this
to restrictions to an open exhaustion, where finiteness holds, and sum strictly
positive local error budgets with total smaller than the requested error.
This also treats Borel sets of infinite measure. Complementation gives the
closed inner approximation. All approximating closed sets are merely closed.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch18.MetricClosedRegular

/-- Finite-measure open covers allow the finite metric regularity theorem to
give an arbitrarily small open excess, even for an infinite-measure Borel set. -/
theorem exists_open_sdiff_lt_of_finite_open_cover
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (O : ℕ → Set X) (hO : ∀ n, IsOpen (O n))
    (hfinite : ∀ n, μ (O n) < ∞) (hcover : (⋃ n, O n) = univ)
    (E : Set X) (hE : MeasurableSet E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ E ⊆ U ∧ μ (U \ E) < ε := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hlocal : ∀ n, ∃ V : Set X, IsOpen V ∧ E ⊆ V ∧
      μ ((V ∩ O n) \ E) < δ n := by
    intro n
    let ν := μ.restrict (O n)
    have : Fact (μ (O n) < ∞) := ⟨hfinite n⟩
    have : IsFiniteMeasure ν := inferInstance
    obtain ⟨V, hEV, hVo, _, hV⟩ :=
      hE.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν E) (hδpos n).ne'
    refine ⟨V, hVo, hEV, ?_⟩
    have heq : (V ∩ O n) \ E = (V \ E) ∩ O n := by
      ext x
      simp only [mem_sdiff, mem_inter_iff]
      tauto
    rw [heq, ← Measure.restrict_apply ((hVo.measurableSet).diff hE)]
    exact hV
  choose V hVo hEV hV using hlocal
  refine ⟨⋃ n, V n ∩ O n, isOpen_iUnion (fun n => (hVo n).inter (hO n)), ?_, ?_⟩
  · intro x hx
    have hxcover : x ∈ ⋃ n, O n := by rw [hcover]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxcover
    exact mem_iUnion.mpr ⟨n, hEV n hx, hn⟩
  · calc
      μ ((⋃ n, V n ∩ O n) \ E) = μ (⋃ n, (V n ∩ O n) \ E) := by
        rw [iUnion_sdiff]
      _ ≤ ∑' n, μ ((V n ∩ O n) \ E) := measure_iUnion_le _
      _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum (fun n => (hV n).le)
      _ < ε := hδsum

/-- Both strict error estimates for every Borel set under exactly the finite-ball
hypothesis. This includes empty spaces and sets of infinite measure. -/
theorem metric_closed_regular
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (hball : ∀ (x : X) (r : ℝ), 0 < r → μ (Metric.ball x r) < ∞)
    (E : Set X) (hE : MeasurableSet E) (ε : ℝ) (hε : 0 < ε) :
    ∃ U F : Set X, IsOpen U ∧ IsClosed F ∧ E ⊆ U ∧ F ⊆ E ∧
      μ (U \ E) < ENNReal.ofReal ε ∧ μ (E \ F) < ENNReal.ofReal ε := by
  have hε' : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  cases isEmpty_or_nonempty X with
  | inl hempty =>
    have : IsEmpty X := hempty
    refine ⟨∅, ∅, isOpen_empty, isClosed_empty, ?_, empty_subset _, ?_, ?_⟩
    · exact Set.eq_empty_of_isEmpty E ▸ Subset.rfl
    · simpa using hε'
    · simpa [Set.eq_empty_of_isEmpty E] using hε'
  | inr hnonempty =>
    obtain ⟨x₀⟩ := hnonempty
    let O : ℕ → Set X := fun n => Metric.ball x₀ (n + 1)
    have hO : ∀ n, IsOpen (O n) := fun _ => Metric.isOpen_ball
    have hfinite : ∀ n, μ (O n) < ∞ := fun n =>
      hball x₀ (n + 1) (by positivity)
    have hcover : (⋃ n, O n) = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt (dist x x₀)
      apply mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change dist x x₀ < (n : ℝ) + 1
      linarith
    obtain ⟨U, hUo, hEU, hU⟩ :=
      exists_open_sdiff_lt_of_finite_open_cover μ O hO hfinite hcover E hE hε'.ne'
    obtain ⟨V, hVo, hEV, hV⟩ :=
      exists_open_sdiff_lt_of_finite_open_cover μ O hO hfinite hcover Eᶜ hE.compl hε'.ne'
    refine ⟨U, Vᶜ, hUo, hVo.isClosed_compl, hEU, compl_subset_comm.mp hEV, hU, ?_⟩
    have heq : E \ Vᶜ = V \ Eᶜ := by
      ext x
      simp only [mem_sdiff, mem_compl_iff, not_not]
      tauto
    rwa [heq]

end D11.Ch18.MetricClosedRegular
