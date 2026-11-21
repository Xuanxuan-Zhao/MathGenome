import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.VaryingMapping
import Mathlib.Topology.Sequences

open MeasureTheory Filter Topology Set

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section

/-- Extend a convergent subsequence by its limit at the unused indices. -/
lemma exists_extension_tendsto {S : Type u} [TopologicalSpace S]
    {x : S} {ys : ℕ → S} {k : ℕ → ℕ} (hk : StrictMono k)
    (hy : Tendsto ys atTop (𝓝 x)) :
    ∃ xs : ℕ → S, Tendsto xs atTop (𝓝 x) ∧ ∀ j, xs (k j) = ys j := by
  classical
  let xs : ℕ → S := fun n => if h : ∃ j, k j = n then ys h.choose else x
  have heq (j : ℕ) : xs (k j) = ys j := by
    dsimp [xs]
    split_ifs with h
    · congr 1
      exact hk.injective h.choose_spec
    · exact False.elim (h ⟨j, rfl⟩)
  refine ⟨xs, ?_, heq⟩
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually hU)
  apply eventually_atTop.mpr
  refine ⟨k N, fun n hn => ?_⟩
  by_cases h : ∃ j, k j = n
  · obtain ⟨j, rfl⟩ := h
    rw [heq]
    exact hN j (hk.le_iff_le.mp hn)
  · simpa [xs, h] using mem_of_mem_nhds hU

/-- The sequential hypothesis also controls every strictly increasing subsequence. -/
lemma varying_tendsto_subsequence {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] {gs : ℕ → S → T} {g : S → T} {x : S}
    (h : ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n => gs n (xs n)) atTop (𝓝 (g x)))
    {k : ℕ → ℕ} (hk : StrictMono k) {ys : ℕ → S}
    (hy : Tendsto ys atTop (𝓝 x)) :
    Tendsto (fun j => gs (k j) (ys j)) atTop (𝓝 (g x)) := by
  obtain ⟨xs, hx, heq⟩ := exists_extension_tendsto hk hy
  simpa only [Function.comp_def, heq] using (h xs hx).comp hk.tendsto_atTop

/-- A point in all closed tail unions must map into the closed target set. -/
lemma mem_closed_of_mem_closed_tails {S : Type u} {T : Type v}
    [MetricSpace S] [TopologicalSpace T] {gs : ℕ → S → T} {g : S → T}
    {x : S} {F : Set T} (hF : IsClosed F)
    (h : ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n => gs n (xs n)) atTop (𝓝 (g x)))
    (hx : ∀ m : ℕ, x ∈ closure (⋃ n ≥ m, gs n ⁻¹' F)) : g x ∈ F := by
  classical
  have hchoose : ∀ j : ℕ, ∃ n : ℕ, ∃ y : S,
      j ≤ n ∧ gs n y ∈ F ∧ dist x y < 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (hx j)
      (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨n, hn, hy⟩ := mem_iUnion₂.mp hy
    exact ⟨n, y, hn, hy, hd⟩
  choose k ys hk hy hd using hchoose
  have hys : Tendsto ys atTop (𝓝 x) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hr : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hr.eventually (gt_mem_nhds hε)] with j hj
    exact lt_trans (by simpa only [dist_comm] using hd j) hj
  obtain ⟨φ, hφ, hkφ⟩ := strictMono_subseq_of_id_le hk
  apply hF.mem_of_tendsto (varying_tendsto_subsequence h hkφ (hys.comp hφ.tendsto_atTop))
  exact Eventually.of_forall (fun j => hy (φ j))

/-- Varying Borel maps preserve weak convergence under the full sequential hypothesis. -/
theorem varying_mapping {S : Type u} {T : Type v}
    [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (gs : ℕ → S → T) (g : S → T)
    (hgs : ∀ n, Measurable (gs n)) (hg : Measurable g)
    (hμ : WeaklyConverges atTop μs μ)
    (C : Set S) (hC : MeasurableSet C) (hμC : (μ : Measure S) C = 1)
    (hseq : ∀ x ∈ C, ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n => gs n (xs n)) atTop (𝓝 (g x))) :
    WeaklyConverges atTop (fun n => (μs n).map (gs n)) (μ.map g) := by
  apply (weaklyConverges_iff_closed _ _).mpr
  intro F hF
  simp_rw [ProbabilityMeasure.map_apply' _ (hgs _).aemeasurable hF.measurableSet]
  rw [ProbabilityMeasure.map_apply' _ hg.aemeasurable hF.measurableSet]
  let H : ℕ → Set S := fun m => closure (⋃ n ≥ m, gs n ⁻¹' F)
  have hclosed (m : ℕ) : IsClosed (H m) := isClosed_closure
  have hanti : Antitone H := by
    intro m n hmn
    apply closure_mono
    exact iUnion₂_mono' (fun j hj => ⟨j, hmn.trans hj, subset_rfl⟩)
  have hbound (m : ℕ) :
      limsup (fun n => (μs n : Measure S) (gs n ⁻¹' F)) atTop ≤ (μ : Measure S) (H m) := by
    refine (limsup_le_limsup ?_).trans
      ((weaklyConverges_iff_closed μs μ).mp hμ (H m) (hclosed m))
    filter_upwards [eventually_ge_atTop m] with n hn
    apply measure_mono
    intro z hz
    apply subset_closure
    exact mem_iUnion₂.mpr ⟨n, hn, hz⟩
  calc
    _ ≤ ⨅ m, (μ : Measure S) (H m) := le_iInf hbound
    _ = (μ : Measure S) (⋂ m, H m) :=
      (hanti.measure_iInter (fun m => (hclosed m).measurableSet.nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩).symm
    _ ≤ (μ : Measure S) (g ⁻¹' F) := by
      apply measure_mono_ae
      filter_upwards [(mem_ae_iff_prob_eq_one hC).mpr hμC] with x hx
      intro hxt
      exact mem_closed_of_mem_closed_tails hF (hseq x hx) (mem_iInter.mp hxt)

/-- A fixed Borel map continuous almost everywhere in its whole domain preserves
weak convergence. -/
theorem almostEverywhere_continuous_mapping {S : Type u} {T : Type v}
    [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (g : S → T) (hg : Measurable g) (hμ : WeaklyConverges atTop μs μ)
    (hcont : ∀ᵐ x ∂(μ : Measure S), ContinuousAt g x) :
    WeaklyConverges atTop (fun n => (μs n).map g) (μ.map g) := by
  apply varying_mapping μs μ (fun _ => g) g (fun _ => hg) hg hμ
    {x | ContinuousAt g x} (measurableSet_of_continuousAt g)
    ((mem_ae_iff_prob_eq_one (measurableSet_of_continuousAt g)).mp hcont)
  intro x hx xs hxs
  exact hx.tendsto.comp hxs

end
end ProbabilityFoundations.Ch06
