import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.VitaliHahnSaksUniformity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Uniform variation absolute continuity in Vitali--Hahn--Saks

This implements the uniformity stage at paper.tex:9734--9794. First, summable
symmetric differences give completeness of the measurable-set pseudometric.
Baire's theorem applied to closed setwise-Cauchy bounds gives uniform small-set
control of scalar values. For signed measures, grouping positive and negative
partition values bounds variation by twice the subset bound. Real and imaginary
parts then give the complex case. The final theorems bound the supremum itself.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal symmDiff

namespace ExpandedFA.Compactness.VitaliHahnSaksUniformity

variable {α : Type*} [MeasurableSpace α]

/-- On a finite measure space, sets whose indicators eventually vanish almost
 everywhere have measures tending to zero. -/
lemma tendsto_measure_zero_of_ae_eventually_notMem
    (ν : Measure α) [IsFiniteMeasure ν] (s : ℕ → Set α)
    (hs : ∀ n, MeasurableSet (s n))
    (h : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ s n) :
    Tendsto (fun n => ν (s n)) atTop (𝓝 0) := by
  let t n := ⋃ i ≥ n, s i
  have ht : Antitone t := by
    intro n m hnm
    exact iUnion₂_mono' fun i hi => ⟨i, le_trans hnm hi, subset_rfl⟩
  have hz : ν (⋂ n, t n) = 0 := by
    apply measure_mono_null (t := {x | ¬ ∀ᶠ n in atTop, x ∉ s n})
    · intro x hx hn
      obtain ⟨N, hN⟩ := eventually_atTop.1 hn
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (mem_iInter.1 hx N)
      exact hN i hi hxi
    · exact ae_iff.1 h
  have hlim := tendsto_measure_iInter_atTop
    (μ := ν) (fun n => (MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => hs i).nullMeasurableSet) ht
    ⟨0, measure_ne_top ν _⟩
  rw [hz] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => by positivity) (fun n => measure_mono (by
      intro x hx
      exact mem_iUnion₂.2 ⟨n, le_rfl, hx⟩))


/-- The epsilon-delta form of absolute continuity for a finite measure. -/
lemma exists_pos_measure_lt_of_absolutelyContinuous
    {ρ ν : Measure α} [IsFiniteMeasure ν] (hν : ν ≪ ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ν s < ENNReal.ofReal ε := by
  classical
  by_contra! h
  have hex n : ∃ s : Set α, MeasurableSet s ∧
      ρ s < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧ ENNReal.ofReal ε ≤ ν s :=
    h _ (pow_pos (by norm_num) n)
  choose s hs hρ hsν using hex
  have hgeom : (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hsum : (∑' n, ρ (s n)) ≠ ∞ :=
    ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun n => (hρ n).le)
  have hae : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ s n :=
    hν.ae_le (ae_eventually_notMem hsum)
  have hlim := tendsto_measure_zero_of_ae_eventually_notMem ν s hs hae
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hε)).exists
  exact (hsν n).not_gt hn

/-- A summably controlled sequence of measurable sets has an a.e. stable indicator. -/
lemma ae_eventually_mem_iff_liminf
    {ρ : Measure α} (s : ℕ → Set α)
    (hsum : (∑' n, ρ (s (n + 1) ∆ s n)) ≠ ∞) :
    ∀ᵐ x ∂ρ, ∀ᶠ n in atTop, (x ∈ s n ↔ x ∈ liminf s atTop) := by
  filter_upwards [ae_eventually_notMem hsum] with x hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  have hstable : ∀ n, N ≤ n → (x ∈ s n ↔ x ∈ s N) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have h := hN n hn
      simp only [mem_symmDiff, not_or, not_and, not_not] at h
      tauto
  have hlim : x ∈ liminf s atTop ↔ x ∈ s N := by
    rw [mem_liminf_iff_eventually_mem]
    constructor
    · intro h
      obtain ⟨n, hxn, hn⟩ := (h.and (eventually_ge_atTop N)).exists
      exact (hstable n hn).1 hxn
    · intro h
      exact (eventually_ge_atTop N).mono fun n hn => (hstable n hn).2 h
  exact (eventually_ge_atTop N).mono fun n hn => (hstable n hn).trans hlim.symm

/-- Completeness for the symmetric-difference pseudometric; the metric quotient
is the complete measure algebra used in the paper. -/
lemma completeSpace_measuredSets (ρ : Measure α) [IsFiniteMeasure ρ] :
    CompleteSpace (MeasuredSets ρ) := by
  apply Metric.complete_of_convergent_controlled_sequences
    (fun n => (1 / 2 : ℝ) ^ n) (fun n => pow_pos (by norm_num) n)
  intro u hu
  let s : ℕ → Set α := fun n => u n
  have hs n : MeasurableSet (s n) := (u n).2
  have hbound n : ρ (s (n + 1) ∆ s n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
    apply ENNReal.ofReal_le_ofReal
    exact (hu n (n + 1) n (Nat.le_succ n) le_rfl).le
  have hsum : (∑' n, ρ (s (n + 1) ∆ s n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  let a : MeasuredSets ρ := ⟨liminf s atTop, MeasurableSet.measurableSet_liminf hs⟩
  refine ⟨a, ?_⟩
  have hlim : Tendsto (fun n => ρ (s n ∆ (a : Set α))) atTop (𝓝 0) := by
    apply tendsto_measure_zero_of_ae_eventually_notMem ρ
      (fun n => s n ∆ (a : Set α)) (fun n => (hs n).symmDiff a.2)
    filter_upwards [ae_eventually_mem_iff_liminf s hsum] with x hx
    exact hx.mono fun n hn => by simp only [mem_symmDiff]; tauto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hreal : Tendsto (fun n => ρ.real (s n ∆ (a : Set α))) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top ρ _)).2 hlim
  simpa only [MeasuredSets.dist_def] using
    (eventually_atTop.1 ((tendsto_order.1 hreal).2 ε hε))


variable {E : Type*} [NormedAddCommGroup E]

/-- Baire's argument for countably additive functions on the measure algebra.
Only continuity of the individual evaluations is needed at this stage. -/
lemma uniform_small_set_norm_of_continuous
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → VectorMeasure α E)
    (hcont : ∀ n, Continuous (fun s : MeasuredSets ρ => μ n (s : Set α)))
    (hcau : ∀ s, MeasurableSet s → CauchySeq (fun n => μ n s))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ∀ n, ‖μ n s‖ < ε := by
  classical
  let : CompleteSpace (MeasuredSets ρ) := completeSpace_measuredSets ρ
  let : BaireSpace (MeasuredSets ρ) := BaireSpace.of_completelyPseudoMetrizable
  let : Nonempty (MeasuredSets ρ) := ⟨⟨∅, MeasurableSet.empty⟩⟩
  let η := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  let F : ℕ → Set (MeasuredSets ρ) := fun N =>
    {s | ∀ n ≥ N, ∀ m ≥ N, ‖μ n (s : Set α) - μ m (s : Set α)‖ ≤ η}
  have hF N : IsClosed (F N) := by
    simp only [F, Set.ofPred_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun m =>
      isClosed_iInter fun _ => isClosed_le ((hcont n).sub (hcont m)).norm continuous_const
  have hcover : (⋃ N, F N) = univ := by
    apply eq_univ_of_forall
    intro s
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcau s s.2) η hη
    exact mem_iUnion.2 ⟨N, fun n hn m hm => by simpa only [dist_eq_norm] using (hN n hn m hm).le⟩
  obtain ⟨N, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hF hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  have hin : Metric.ball a r ⊆ F N := hball.trans interior_subset
  have htail {s : Set α} (hs : MeasurableSet s)
      (hsmall : ρ s < ENNReal.ofReal r) {n m : ℕ} (hn : N ≤ n) (hm : N ≤ m) :
      ‖(μ n - μ m) s‖ ≤ 4 * η := by
    let ν := μ n - μ m
    have hnear (t : MeasuredSets ρ) (ht : (t : Set α) ∆ (a : Set α) ⊆ s) :
        ‖ν (t : Set α)‖ ≤ η := by
      apply (hin (show t ∈ Metric.ball a r from ?_)) n hn m hm
      rw [Metric.mem_ball, MeasuredSets.dist_def]
      apply (ENNReal.toReal_mono (measure_ne_top ρ _) (measure_mono ht)).trans_lt
      exact (ENNReal.toReal_lt_of_lt_ofReal hsmall)
    have ha0 : ‖ν (a : Set α)‖ ≤ η := hnear a (by simp)
    have hau : ‖ν ((a : Set α) ∪ s)‖ ≤ η :=
      hnear ⟨(a : Set α) ∪ s, a.2.union hs⟩ (by intro x hx; change x ∈ ((a : Set α) ∪ s) ∆ (a : Set α) at hx; simp only [mem_symmDiff, mem_union] at hx; tauto)
    have had : ‖ν ((a : Set α) \ s)‖ ≤ η :=
      hnear ⟨(a : Set α) \ s, a.2.diff hs⟩ (by intro x hx; change x ∈ ((a : Set α) \ s) ∆ (a : Set α) at hx; simp only [mem_symmDiff, Set.mem_sdiff] at hx; tauto)
    have hleft : ‖ν (s \ (a : Set α))‖ ≤ 2 * η := by
      have heq : ν (s \ (a : Set α)) = ν ((a : Set α) ∪ s) - ν (a : Set α) := by
        have h := ν.of_add_of_sdiff a.2 (a.2.union hs) subset_union_left
        change ν (a : Set α) + ν (((a : Set α) ∪ s) \ (a : Set α)) = ν ((a : Set α) ∪ s) at h
        have he : ((a : Set α) ∪ s) \ (a : Set α) = s \ (a : Set α) := by ext x; simp
        rw [he] at h
        exact eq_sub_of_add_eq' h
      rw [heq]
      exact (norm_sub_le _ _).trans (by linarith)
    have hright : ‖ν (s ∩ (a : Set α))‖ ≤ 2 * η := by
      have heq : ν (s ∩ (a : Set α)) = ν (a : Set α) - ν ((a : Set α) \ s) := by
        have h := ν.of_add_of_sdiff (a.2.diff hs) a.2 sdiff_subset
        have he : (a : Set α) \ ((a : Set α) \ s) = s ∩ (a : Set α) := by ext x; simp; tauto
        change ν ((a : Set α) \ s) + ν ((a : Set α) \ ((a : Set α) \ s)) = ν (a : Set α) at h
        rw [he] at h
        exact eq_sub_of_add_eq' h
      rw [heq]
      exact (norm_sub_le _ _).trans (by linarith)
    have heq : ν s = ν (s \ (a : Set α)) + ν (s ∩ (a : Set α)) := by
      have h := ν.of_union disjoint_sdiff_inter (hs.diff a.2) (hs.inter a.2)
      change ν ((s \ (a : Set α)) ∪ (s ∩ (a : Set α))) = _ at h
      have he : (s \ (a : Set α)) ∪ (s ∩ (a : Set α)) = s := by ext x; simp
      rw [he] at h
      exact h
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  have hinitial n : ∃ d : ℝ, 0 < d ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal d → ‖μ n s‖ < η := by
    have hcn : ContinuousAt (fun s : MeasuredSets ρ => μ n (s : Set α))
        (⟨∅, MeasurableSet.empty⟩ : MeasuredSets ρ) := (hcont n).continuousAt
    obtain ⟨d, hd, hnd⟩ := Metric.continuousAt_iff.1 hcn η hη
    refine ⟨d, hd, fun s hs hsmall => ?_⟩
    have hdist : @dist (MeasuredSets ρ) _ ⟨s, hs⟩ ⟨∅, MeasurableSet.empty⟩ < d := by
      change (ρ (s ∆ ∅)).toReal < d
      simpa [Set.symmDiff_def] using ENNReal.toReal_lt_of_lt_ofReal hsmall
    have hh := hnd hdist
    change dist (μ n s) (μ n ∅) < η at hh
    simpa only [VectorMeasure.empty, dist_zero_right] using hh
  choose d hd hnd using hinitial
  let δ := min r (Finset.inf' (Finset.range (N + 1)) (by simp) d)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hr ((Finset.lt_inf'_iff _).2 (fun i hi => hd i))
  refine ⟨δ, hδ, fun s hs hsmall n => ?_⟩
  have hsmallr : ρ s < ENNReal.ofReal r :=
    hsmall.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hsmalli i (hi : i ≤ N) : ‖μ i s‖ < η := by
    apply hnd i s hs
    apply hsmall.trans_le (ENNReal.ofReal_le_ofReal _)
    exact (min_le_right _ _).trans (Finset.inf'_le _ (by simpa using hi))
  by_cases hn : n ≤ N
  · exact (hsmalli n hn).trans (by dsimp [η]; linarith)
  · have hN := hsmalli N le_rfl
    have hdiff := htail hs hsmallr (Nat.le_of_lt (lt_of_not_ge hn)) le_rfl
    have heq : μ n s = (μ n - μ N) s + μ N s := by simp
    calc
      ‖μ n s‖ = ‖(μ n - μ N) s + μ N s‖ := congrArg norm heq
      _ ≤ ‖(μ n - μ N) s‖ + ‖μ N s‖ := norm_add_le _ _
      _ < ε := by dsimp [η] at *; linarith


/-- An absolutely continuous finite dominating measure makes set evaluation
continuous for the symmetric-difference metric. -/
lemma continuous_eval_of_dominated
    (ρ ν : Measure α) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (μ : VectorMeasure α E) (hac : ν ≪ ρ)
    (hdom : ∀ s, MeasurableSet s → ‖μ s‖ ≤ ν.real s) :
    Continuous (fun s : MeasuredSets ρ => μ (s : Set α)) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_measure_lt_of_absolutelyContinuous hac
    (ε := ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {b} hba => ?_⟩
  have hρ : ρ ((b : Set α) ∆ (a : Set α)) < ENNReal.ofReal δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top ρ _)).2 hba
  have hb : ν.real ((b : Set α) ∆ (a : Set α)) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal (hsmall _ (b.2.symmDiff a.2) hρ)
  have hnorm {s : Set α} (hs : MeasurableSet s)
      (hsub : s ⊆ (b : Set α) ∆ (a : Set α)) : ‖μ s‖ < ε / 2 :=
    (hdom s hs).trans_lt ((ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)).trans_lt hb)
  have h1 := μ.of_add_of_sdiff (b.2.inter a.2) b.2 inter_subset_left
  have h2 := μ.of_add_of_sdiff (b.2.inter a.2) a.2 inter_subset_right
  change μ ((b : Set α) ∩ (a : Set α)) +
    μ ((b : Set α) \ ((b : Set α) ∩ (a : Set α))) = μ (b : Set α) at h1
  change μ ((b : Set α) ∩ (a : Set α)) +
    μ ((a : Set α) \ ((b : Set α) ∩ (a : Set α))) = μ (a : Set α) at h2
  have he1 : (b : Set α) \ ((b : Set α) ∩ (a : Set α)) = (b : Set α) \ (a : Set α) := by
    ext x; simp
  have he2 : (a : Set α) \ ((b : Set α) ∩ (a : Set α)) = (a : Set α) \ (b : Set α) := by
    ext x; simp
  rw [he1] at h1
  rw [he2] at h2
  have he : μ (b : Set α) - μ (a : Set α) =
      μ ((b : Set α) \ (a : Set α)) - μ ((a : Set α) \ (b : Set α)) := by
    rw [← h1, ← h2]; abel
  rw [dist_eq_norm, he]
  have hleft := hnorm (b.2.diff a.2) subset_union_left
  have hright := hnorm (a.2.diff b.2) subset_union_right
  apply (norm_sub_le _ _).trans_lt
  calc
    _ < ε / 2 + ε / 2 := add_lt_add hleft hright
    _ = ε := by ring

/-- Null-set absolute continuity of a signed measure implies the same for its
positive total variation. The input only asks for null measurable sets. -/
lemma signed_totalVariation_absolutelyContinuous
    (ρ : Measure α) (μ : SignedMeasure α)
    (hac : ∀ s, MeasurableSet s → ρ s = 0 → μ s = 0) :
    μ.totalVariation ≪ ρ := by
  rw [μ.totalVariation_eq_variation]
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hρ
  apply (VectorMeasure.variation_apply_eq_zero hs).2
  intro t hts ht
  exact hac t ht (measure_mono_null hts hρ)

/-- Signed variation is at most twice a common bound on all subset values. -/
lemma signed_variation_le_of_subset_bound
    (μ : SignedMeasure α) {s : Set α} (hs : MeasurableSet s)
    {c : ℝ} (_hc : 0 ≤ c)
    (h : ∀ t, MeasurableSet t → t ⊆ s → ‖μ t‖ ≤ c) :
    μ.totalVariation s ≤ ENNReal.ofReal (2 * c) := by
  rw [μ.totalVariation_eq_variation]
  by_contra! hbad
  obtain ⟨t, hts, ht, hlt⟩ := μ.exists_subset_lt_enorm_apply_of_lt_variation hs hbad
  have hnorm : ‖μ t‖ₑ ≤ ENNReal.ofReal c := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h t ht hts)
  have hle : 2 * ‖μ t‖ₑ ≤ ENNReal.ofReal (2 * c) := by
    calc
      2 * ‖μ t‖ₑ ≤ 2 * ENNReal.ofReal c := by gcongr
      _ = ENNReal.ofReal (2 * c) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  exact hlt.not_ge hle

/-- Vitali--Hahn--Saks, uniform variation stage, for signed measures. -/
theorem uniform_variation_signed_pointwise
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → SignedMeasure α)
    (hac : ∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0)
    (hconv : ∀ s, MeasurableSet s → ∃ l : ℝ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ∀ n, (μ n).totalVariation s < ENNReal.ofReal ε := by
  intro ε hε
  have hcont n : Continuous (fun s : MeasuredSets ρ => μ n (s : Set α)) :=
    continuous_eval_of_dominated ρ (μ n).totalVariation (μ n)
      (signed_totalVariation_absolutelyContinuous ρ (μ n) (hac n))
      (fun s _ => (μ n).norm_le_totalVariation s)
  have hcau s (hs : MeasurableSet s) : CauchySeq (fun n => μ n s) := by
    obtain ⟨l, hl⟩ := hconv s hs
    exact hl.cauchySeq
  obtain ⟨δ, hδ, hsmall⟩ := uniform_small_set_norm_of_continuous ρ μ hcont hcau
    (ε := ε / 3) (by positivity)
  refine ⟨δ, hδ, fun s hs hρ n => ?_⟩
  have hvar : (μ n).totalVariation s ≤ ENNReal.ofReal (2 * (ε / 3)) :=
    signed_variation_le_of_subset_bound (μ n) hs (by positivity)
      (fun t ht hts => (hsmall t ht ((measure_mono hts).trans_lt hρ) n).le)
  exact hvar.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))


/-- The ordinary complex total variation is dominated by the sum of the
variations of the real and imaginary parts. -/
lemma complex_variation_le (μ : ComplexMeasure α) :
    μ.variation ≤ μ.re.totalVariation + μ.im.totalVariation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  have hre := μ.re.norm_le_totalVariation s
  have him := μ.im.norm_le_totalVariation s
  change ‖(μ s).re‖ ≤ μ.re.totalVariation.real s at hre
  change ‖(μ s).im‖ ≤ μ.im.totalVariation.real s at him
  calc
    ‖μ s‖ₑ = ENNReal.ofReal ‖μ s‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (μ.re.totalVariation.real s + μ.im.totalVariation.real s) := by
      apply ENNReal.ofReal_le_ofReal
      exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)
    _ = (μ.re.totalVariation + μ.im.totalVariation) s := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), Measure.add_apply,
        measureReal_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Vitali--Hahn--Saks, uniform variation stage, for complex measures. -/
theorem uniform_variation_complex_pointwise
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → ComplexMeasure α)
    (hac : ∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0)
    (hconv : ∀ s, MeasurableSet s → ∃ l : ℂ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → ∀ n, (μ n).variation s < ENNReal.ofReal ε := by
  intro ε hε
  have hreac n s (hs : MeasurableSet s) (hρ : ρ s = 0) : (μ n).re s = 0 := by
    change (μ n s).re = 0
    rw [hac n s hs hρ]; rfl
  have himac n s (hs : MeasurableSet s) (hρ : ρ s = 0) : (μ n).im s = 0 := by
    change (μ n s).im = 0
    rw [hac n s hs hρ]; rfl
  have hreconv s (hs : MeasurableSet s) :
      ∃ l : ℝ, Tendsto (fun n => (μ n).re s) atTop (𝓝 l) := by
    obtain ⟨l, hl⟩ := hconv s hs
    exact ⟨l.re, Complex.continuous_re.continuousAt.tendsto.comp hl⟩
  have himconv s (hs : MeasurableSet s) :
      ∃ l : ℝ, Tendsto (fun n => (μ n).im s) atTop (𝓝 l) := by
    obtain ⟨l, hl⟩ := hconv s hs
    exact ⟨l.im, Complex.continuous_im.continuousAt.tendsto.comp hl⟩
  obtain ⟨δr, hδr, hr⟩ := uniform_variation_signed_pointwise ρ
    (fun n => (μ n).re) hreac hreconv (ε / 2) (by positivity)
  obtain ⟨δi, hδi, hi⟩ := uniform_variation_signed_pointwise ρ
    (fun n => (μ n).im) himac himconv (ε / 2) (by positivity)
  refine ⟨min δr δi, lt_min hδr hδi, fun s hs hρ n => ?_⟩
  have hrn := hr s hs (hρ.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))) n
  have hin := hi s hs (hρ.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))) n
  calc
    (μ n).variation s ≤ ((μ n).re.totalVariation + (μ n).im.totalVariation) s :=
      complex_variation_le (μ n) s
    _ = (μ n).re.totalVariation s + (μ n).im.totalVariation s := Measure.add_apply _ _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hrn hin
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Uniform absolute continuity of the total variations of a setwise convergent
sequence of signed measures. The supremum itself is strictly below `ε`. -/
theorem uniform_variation_signed
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → SignedMeasure α)
    (hac : ∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0)
    (hconv : ∀ s, MeasurableSet s → ∃ l : ℝ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → (⨆ n, (μ n).totalVariation s) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := uniform_variation_signed_pointwise ρ μ hac hconv (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs hρ => ?_⟩
  exact (iSup_le fun n => (h s hs hρ n).le).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))

/-- Uniform absolute continuity of the total variations of a setwise convergent
sequence of complex measures, with no convergence-in-variation hypothesis. -/
theorem uniform_variation_complex
    (ρ : Measure α) [IsFiniteMeasure ρ] (μ : ℕ → ComplexMeasure α)
    (hac : ∀ n s, MeasurableSet s → ρ s = 0 → μ n s = 0)
    (hconv : ∀ s, MeasurableSet s → ∃ l : ℂ,
      Tendsto (fun n => μ n s) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ρ s < ENNReal.ofReal δ → (⨆ n, (μ n).variation s) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := uniform_variation_complex_pointwise ρ μ hac hconv (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs hρ => ?_⟩
  exact (iSup_le fun n => (h s hs hρ n).le).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))

end ExpandedFA.Compactness.VitaliHahnSaksUniformity




