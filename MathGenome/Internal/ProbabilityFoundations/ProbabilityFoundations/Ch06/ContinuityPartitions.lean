import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuityPartitions
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.Linarith

open MeasureTheory TopologicalSpace Metric Set Filter
open scoped Topology

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

/-- A Borel set whose boundary is null under the specified measure. -/
def IsContinuitySet {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) (A : Set S) : Prop :=
  MeasurableSet A ∧ μ (frontier A) = 0

variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- At a fixed center, only countably many positive radii give a ball
whose boundary has positive measure. -/
theorem countable_bad_ball_radii (μ : Measure S) [IsFiniteMeasure μ] (x : S) :
    {t : ℝ | 0 < t ∧ ¬ IsContinuitySet μ (ball x t)}.Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := μ) (g := fun y : S => dist y x)
    (continuous_id.dist continuous_const).measurable
  apply h.mono
  intro t ht
  have hn : μ (frontier (ball x t)) ≠ 0 := by
    intro hz
    exact ht.2 ⟨isOpen_ball.measurableSet, hz⟩
  exact (pos_iff_ne_zero.mpr hn).trans_le
    (measure_mono frontier_ball_subset_sphere)

namespace IsContinuitySet

variable {μ : Measure S} {A B : Set S}

protected theorem empty : IsContinuitySet μ ∅ := by
  simp [IsContinuitySet]

protected theorem compl (h : IsContinuitySet μ A) : IsContinuitySet μ Aᶜ :=
  ⟨h.1.compl, by simpa only [frontier_compl] using h.2⟩

protected theorem union (hA : IsContinuitySet μ A) (hB : IsContinuitySet μ B) :
    IsContinuitySet μ (A ∪ B) :=
  ⟨hA.1.union hB.1, measure_mono_null
    ((frontier_union_subset A B).trans
      (union_subset_union inter_subset_left inter_subset_right))
    (measure_union_null hA.2 hB.2)⟩

protected theorem inter (hA : IsContinuitySet μ A) (hB : IsContinuitySet μ B) :
    IsContinuitySet μ (A ∩ B) :=
  ⟨hA.1.inter hB.1, measure_mono_null
    ((frontier_inter_subset A B).trans
      (union_subset_union inter_subset_left inter_subset_right))
    (measure_union_null hA.2 hB.2)⟩

protected theorem sdiff (hA : IsContinuitySet μ A) (hB : IsContinuitySet μ B) :
    IsContinuitySet μ (A \ B) := by
  simpa only [sdiff_eq] using hA.inter hB.compl

protected theorem biUnion {ι : Type*} (F : Finset ι) (f : ι → Set S)
    (hf : ∀ i ∈ F, IsContinuitySet μ (f i)) : IsContinuitySet μ (⋃ i ∈ F, f i) := by
  classical
  induction F using Finset.induction with
  | empty => simpa using (IsContinuitySet.empty (μ := μ))
  | insert i F hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hf i (Finset.mem_insert_self i F)).union
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end IsContinuitySet

/-- A continuity ball with radius in any prescribed open interval. -/
theorem exists_continuity_ball_radius (μ : Measure S) [IsFiniteMeasure μ]
    (x : S) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsContinuitySet μ (ball x t) := by
  obtain ⟨t, ht, hnull⟩ := exists_null_frontier_thickening μ ({x} : Set S) hab
  rw [Metric.thickening_singleton] at hnull
  exact ⟨t, ht, isOpen_ball.measurableSet, hnull⟩

/-- Countably many small continuity balls cover a nonempty separable set.
The centers may lie in the ambient space; no ambient separability is used. -/
theorem countable_small_continuity_cover (μ : Measure S) [IsFiniteMeasure μ]
    (M : Set S) (hM : M.Nonempty) (hsep : IsSeparable M)
    (r : ℝ) (hr : 0 < r) :
    ∃ B : ℕ → Set S,
      (∀ n, IsContinuitySet μ (B n) ∧ Bornology.IsBounded (B n) ∧ diam (B n) < r) ∧
      M ⊆ ⋃ n, B n := by
  obtain ⟨D, hD, hMD⟩ := hsep
  have hDne : D.Nonempty := by
    by_contra hn
    have he : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := hM
    simpa [he] using hMD hx
  obtain ⟨c, hc⟩ := hD.exists_eq_range hDne
  have hab : r / 4 < r / 2 := by linarith
  choose ρ hρ hB using fun n : ℕ => exists_continuity_ball_radius μ (c n) hab
  refine ⟨fun n => ball (c n) (ρ n), ?_, ?_⟩
  · intro n
    refine ⟨hB n, isBounded_ball, (diam_ball ?_).trans_lt ?_⟩
    · linarith [(hρ n).1]
    · linarith [(hρ n).2]
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hMD hx) (r / 4) (by linarith)
    obtain ⟨n, rfl⟩ := hc ▸ hy
    exact mem_iUnion.mpr ⟨n, hxy.trans (hρ n).1⟩

/-- For a full-mass set, finitely many sets from a countable measurable
cover leave arbitrarily small mass uncovered. -/
theorem exists_small_remainder (μ : Measure S) [IsProbabilityMeasure μ]
    (M : Set S) (hM : MeasurableSet M) (hμM : μ M = 1)
    (B : ℕ → Set S) (hB : ∀ n, IsContinuitySet μ (B n))
    (hcover : M ⊆ ⋃ n, B n) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, μ (⋃ i ∈ Finset.range (N + 1), B i)ᶜ < ENNReal.ofReal ε := by
  let U : ℕ → Set S := fun n => ⋃ i ∈ Finset.range (n + 1), B i
  have hU (n : ℕ) : IsContinuitySet μ (U n) :=
    IsContinuitySet.biUnion _ B (fun i _ => hB i)
  have hmono : Monotone U := by
    intro n m hnm
    exact biUnion_mono (Finset.range_mono (Nat.add_le_add_right hnm 1)) (fun i _ => Subset.rfl)
  have hinter : (⋂ n, (U n)ᶜ) ⊆ Mᶜ := by
    intro x hx hxM
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hxM)
    exact (mem_iInter.mp hx i) (mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self i), hi⟩⟩)
  have hnullM : μ Mᶜ = 0 := by simp [measure_compl hM, hμM]
  have hnull : μ (⋂ n, (U n)ᶜ) = 0 := measure_mono_null hinter hnullM
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hU n).1.compl.nullMeasurableSet)
    (fun i j hij => compl_subset_compl.mpr (hmono hij))
    ⟨0, measure_ne_top μ _⟩
  rw [hnull] at hlim
  have hev := (tendsto_order.mp hlim).2 (ENNReal.ofReal ε) (by simpa using hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, hN N le_rfl⟩

/-- The small-continuity-set partition of Proposition 6.4. The finite set
`C` contains precisely the nonempty small cells; `A₀` is the remainder. -/
theorem small_continuity_partition (μ : Measure S) [IsProbabilityMeasure μ]
    (M : Set S) (hM : MeasurableSet M) (hsep : IsSeparable M) (hμM : μ M = 1)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ (A₀ : Set S) (C : Finset (Set S)),
      IsContinuitySet μ A₀ ∧ μ A₀ < ENNReal.ofReal ε ∧
      (C : Set (Set S)).Pairwise Disjoint ∧
      (∀ A ∈ C, A.Nonempty ∧ IsContinuitySet μ A ∧
        Bornology.IsBounded A ∧ diam A < r) ∧
      (∀ A ∈ C, Disjoint A₀ A) ∧
      A₀ ∪ (⋃ A ∈ C, A) = univ := by
  classical
  have hMne : M.Nonempty := by
    apply nonempty_of_measure_ne_zero
    rw [hμM]
    exact one_ne_zero
  obtain ⟨B, hB, hcover⟩ := countable_small_continuity_cover μ M hMne hsep r hr
  obtain ⟨N, hN⟩ := exists_small_remainder μ M hM hμM B (fun n => (hB n).1) hcover ε hε
  let D := disjointed B
  let C : Finset (Set S) := ((Finset.range (N + 1)).image D).filter Set.Nonempty
  let U : Set S := ⋃ i ∈ Finset.range (N + 1), B i
  have hU : IsContinuitySet μ U :=
    IsContinuitySet.biUnion _ B (fun i _ => (hB i).1)
  have hD (i : ℕ) : IsContinuitySet μ (D i) :=
    disjointedRec (p := IsContinuitySet μ)
      (fun {t j} ht => ht.sdiff (hB j).1) (hB i).1
  have hDU : (⋃ i ∈ Finset.range (N + 1), D i) = U := by
    exact (biUnion_range_succ_disjointed B N).trans (partialSups_eq_biUnion_range B N)
  have hCU : (⋃ A ∈ C, A) = U := by
    rw [← hDU]
    ext x
    constructor
    · intro hx
      obtain ⟨A, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hAC, hxA⟩ := mem_iUnion.mp hx
      obtain ⟨hAi, _⟩ := Finset.mem_filter.mp hAC
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hAi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxA⟩⟩
    · intro hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := mem_iUnion.mp hx
      have hmem : D i ∈ C := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, ⟨x, hxi⟩⟩
      exact mem_iUnion.mpr ⟨D i, mem_iUnion.mpr ⟨hmem, hxi⟩⟩
  refine ⟨Uᶜ, C, hU.compl, hN, ?_, ?_, ?_, ?_⟩
  · intro A hA B' hB' hne
    obtain ⟨hAi, _⟩ := Finset.mem_filter.mp hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hAi
    obtain ⟨hBi, _⟩ := Finset.mem_filter.mp hB'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hBi
    exact disjoint_disjointed B (fun he => hne (congrArg D he))
  · intro A hA
    obtain ⟨hAi, hAne⟩ := Finset.mem_filter.mp hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hAi
    have hsub : D i ⊆ B i := disjointed_subset B i
    exact ⟨hAne, hD i, (hB i).2.1.subset hsub,
      (diam_mono hsub (hB i).2.1).trans_lt (hB i).2.2⟩
  · intro A hA
    apply disjoint_compl_left_iff.mpr
    rw [← hCU]
    exact subset_iUnion_of_subset A (subset_iUnion_of_subset hA Subset.rfl)
  · rw [hCU]
    exact compl_union_self U

end
end ProbabilityFoundations.Ch06
