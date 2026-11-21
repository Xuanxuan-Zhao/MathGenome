import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.FirstBorelCantelli
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.ProductMeasure

/-!
Skorokhod representation, paper.tex 1905–1968. Only the limiting law needs
a separable Borel set of full mass; the ambient metric space and approximating
laws remain unrestricted. Finite continuity partitions give measure mixtures,
which are realized on a product space with one shared coin per block.
Summable block errors yield a common measurable full event by Borel–Cantelli.
Simultaneous modification on its complement gives convergence everywhere.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section

/-- The optional modification in the source works on the original sigma
algebra because the common full-probability event is measurable. -/
theorem modify_on_common_null_event :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.nullModificationType.{u,v} := by
  classical
  intro Ω S _ _ _ P _ X Xs hX hXs E hE hPE hlim
  let Ys : ℕ → Ω → S := fun n => E.piecewise (Xs n) X
  have hmem : ∀ᵐ ω ∂P, ω ∈ E := (mem_ae_iff_prob_eq_one hE).mpr hPE
  refine ⟨Ys, fun n => (hXs n).piecewise hE hX, ?_, ?_, ?_⟩
  · intro n ω hω
    exact piecewise_eq_of_mem E (Xs n) X hω
  · intro n
    apply Measure.map_congr
    exact hmem.mono (fun ω hω => piecewise_eq_of_mem E (Xs n) X hω)
  · intro ω
    by_cases hω : ω ∈ E
    · simpa only [Ys, piecewise_eq_of_mem E _ X hω] using hlim ω hω
    · simpa only [Ys, piecewise_eq_of_notMem E _ X hω] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => X ω) atTop (𝓝 (X ω)))

/-- On a continuity set, every positive fraction strictly below its limit
mass is eventually dominated by the approximating masses. -/
theorem eventually_dominate_continuity_set
    {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hweak : WeaklyConverges atTop μs μ) (A : Set S)
    (hA : IsContinuitySet (μ : Measure S) A) (a : ℝ≥0∞) (ha : a < 1) :
    ∀ᶠ n in atTop, a * (μ : Measure S) A ≤ (μs n : Measure S) A := by
  by_cases hzero : (μ : Measure S) A = 0
  · simp [hzero]
  have hlim := (weaklyConverges_iff_continuitySets μs μ).mp hweak A hA
  have hlt : a * (μ : Measure S) A < (μ : Measure S) A := by
    simpa [mul_comm] using ENNReal.mul_lt_mul_right hzero (measure_ne_top (μ : Measure S) A) ha
  exact (hlim.eventually (lt_mem_nhds hlt)).mono (fun n hn => hn.le)

/-- Finitely many cells admit one common threshold. -/
theorem eventually_dominate_finite_continuity_sets
    {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hweak : WeaklyConverges atTop μs μ) (C : Finset (Set S))
    (hC : ∀ A ∈ C, IsContinuitySet (μ : Measure S) A)
    (a : ℝ≥0∞) (ha : a < 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A ∈ C,
      a * (μ : Measure S) A ≤ (μs n : Measure S) A := by
  apply eventually_atTop.mp
  exact C.eventually_all.mpr (fun A hA =>
    eventually_dominate_continuity_set μs μ hweak A (hC A hA) a ha)

/-- Choose strictly increasing thresholds for countably many eventual facts. -/
theorem exists_strictMono_thresholds (p : ℕ → ℕ → Prop)
    (hp : ∀ m, ∀ᶠ n in atTop, p m n) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ m n, N m ≤ n → p m n := by
  choose t ht using fun m => eventually_atTop.mp (hp m)
  let N : ℕ → ℕ := fun m => Nat.rec (t 0) (fun k prev => max (prev + 1) (t (k + 1))) m
  have hNt : ∀ m, t m ≤ N m := by
    intro m
    cases m with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  refine ⟨N, strictMono_nat_of_lt_succ (fun m => ?_), ?_⟩
  · exact (Nat.lt_succ_self (N m)).trans_le (le_max_left _ _)
  · intro m n hmn
    exact ht m n ((hNt m).trans hmn)

/-- Every sufficiently late index lies in one of the increasing blocks. -/
theorem exists_threshold_block (N : ℕ → ℕ) (hN : StrictMono N)
    (n : ℕ) (hn : N 0 ≤ n) :
    ∃ m, N m ≤ n ∧ n < N (m + 1) := by
  have hex : ∃ k, n < N k := by
    obtain ⟨k, hk⟩ := (hN.tendsto_atTop.eventually (eventually_gt_atTop n)).exists
    exact ⟨k, hk⟩
  let k := Nat.find hex
  have hk : n < N k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz] at hk
    exact (not_lt_of_ge hn) hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨m, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega : m < k))
  · simpa only [hm] using hk

/-- Successful blocks whose radii tend to zero imply convergence of the
whole sequence, regardless of the lengths of the blocks. -/
theorem tendsto_of_eventually_successful_blocks
    {S : Type u} [MetricSpace S] (Xs : ℕ → S) (X : S)
    (N : ℕ → ℕ) (hN : StrictMono N) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsuccess : ∀ᶠ m in atTop, ∀ n, N m ≤ n → n < N (m + 1) → dist (Xs n) X < r m) :
    Tendsto Xs atTop (𝓝 X) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hsuccess.and (hr.eventually (gt_mem_nhds hε)))
  refine ⟨N M, fun n hn => ?_⟩
  obtain ⟨m, hmn, hnm⟩ := exists_threshold_block N hN n ((hN.monotone (Nat.zero_le M)).trans hn)
  have hMm : M ≤ m := by
    by_contra hnot
    have hmM : m + 1 ≤ M := by omega
    exact (not_lt_of_ge ((hN.monotone hmM).trans hn)) hnm
  exact ((hM m hMm).1 n hmn hnm).trans (hM m hMm).2

/-- First Borel–Cantelli for block success events, followed by the deterministic
block lemma. The common full event is obtained in the original sigma algebra. -/
theorem common_full_event_of_block_bounds
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (Xs : ℕ → Ω → S)
    (N : ℕ → ℕ) (hN : StrictMono N) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (G : ℕ → Set Ω) (hG : ∀ m, MeasurableSet (G m))
    (hsum : (∑' m, P (G m)ᶜ) < ∞)
    (hgood : ∀ m ω, ω ∈ G m → ∀ n, N m ≤ n → n < N (m + 1) →
      dist (Xs n ω) (X ω) < r m) :
    ∃ E : Set Ω, MeasurableSet E ∧ P E = 1 ∧
      ∀ ω ∈ E, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω)) := by
  apply (Ch01.almostSurely_iff_measurable_one P _).mp
  have hbc : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ G m := by
    have hnull := Ch02.first_borel_cantelli P (fun m => (G m)ᶜ) (fun m => (hG m).compl) hsum
    rw [Ch02.infinitelyOftenEvent_eq_limsup] at hnull
    have hae := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with ω hω
    simpa only [mem_limsup_iff_frequently_mem, Filter.Frequently, mem_compl_iff,
      not_not] using hω
  exact hbc.mono (fun ω hω => tendsto_of_eventually_successful_blocks
    (fun n => Xs n ω) (X ω) N hN r hr
      (hω.mono (fun m hm n hmn hnm => hgood m ω hm n hmn hnm)))

/-- The source's continuity partitions can be scheduled so that every cell
has the required common-mass lower bound throughout every later index. -/
theorem scheduled_continuity_partitions
    {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hweak : WeaklyConverges atTop μs μ)
    (M : Set S) (hM : MeasurableSet M) (hsep : TopologicalSpace.IsSeparable M)
    (hμM : (μ : Measure S) M = 1)
    (r ε : ℕ → ℝ) (hr : ∀ m, 0 < r m) (hε : ∀ m, 0 < ε m)
    (a : ℕ → ℝ≥0∞) (ha : ∀ m, a m < 1) :
    ∃ (A₀ : ℕ → Set S) (C : ℕ → Finset (Set S)) (N : ℕ → ℕ),
      StrictMono N ∧
      (∀ m, IsContinuitySet (μ : Measure S) (A₀ m) ∧
        (μ : Measure S) (A₀ m) < ENNReal.ofReal (ε m) ∧
        (C m : Set (Set S)).Pairwise Disjoint ∧
        (∀ A ∈ C m, A.Nonempty ∧ IsContinuitySet (μ : Measure S) A ∧
          Bornology.IsBounded A ∧ diam A < r m) ∧
        (∀ A ∈ C m, Disjoint (A₀ m) A) ∧
        A₀ m ∪ (⋃ A ∈ C m, A) = univ) ∧
      ∀ m n, N m ≤ n → ∀ A ∈ insert (A₀ m) (C m),
        a m * (μ : Measure S) A ≤ (μs n : Measure S) A := by
  classical
  choose A₀ C hC using fun m =>
    small_continuity_partition (μ : Measure S) M hM hsep hμM (r m) (ε m) (hr m) (hε m)
  have hc : ∀ m A, A ∈ insert (A₀ m) (C m) → IsContinuitySet (μ : Measure S) A := by
    intro m A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact (hC m).1
    · exact ((hC m).2.2.2.1 A hA).2.1
  have hevent : ∀ m, ∀ᶠ n in atTop, ∀ A ∈ insert (A₀ m) (C m),
      a m * (μ : Measure S) A ≤ (μs n : Measure S) A := by
    intro m
    exact eventually_atTop.mpr
      (eventually_dominate_finite_continuity_sets μs μ hweak _ (hc m) (a m) (ha m))
  obtain ⟨N, hN, hdom⟩ := exists_strictMono_thresholds _ hevent
  exact ⟨A₀, C, N, hN, hC, hdom⟩

/-- A common full-event realization yields an everywhere-convergent one,
without imposing any further condition on the target measurable space. -/
theorem everywhere_realization_of_almostSure :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.modificationOfRepresentationType.{u} := by
  intro S _ _ μs μ h
  rcases h with ⟨Ω, mΩ, h⟩
  let := mΩ
  rcases h with ⟨P, X, Xs, hX, hXs, hLaw, hLaws, E, hE, hPE, hlim⟩
  obtain ⟨Ys, hYs, _, hYLaws, hYlim⟩ :=
    modify_on_common_null_event (P : Measure Ω) X Xs hX hXs E hE hPE hlim
  refine ⟨Ω, mΩ, P, X, Ys, hX, hYs, hLaw, ?_, hYlim⟩
  intro n
  exact (hYLaws n).trans (hLaws n)

/-- The separable-space specialization uses the whole space as the separable
Borel support, and never needs completeness. -/
theorem separable_full_support
    {S : Type u} [MetricSpace S] [MeasurableSpace S]
    [TopologicalSpace.SeparableSpace S] (μ : ProbabilityMeasure S) :
    ∃ M : Set S, MeasurableSet M ∧ TopologicalSpace.IsSeparable M ∧ (μ : Measure S) M = 1 :=
  ⟨univ, MeasurableSet.univ, TopologicalSpace.IsSeparable.of_separableSpace univ, measure_univ⟩

/-- Package a measurable common-space block construction as the required
representation. This is the final analytic assembly step. -/
theorem representation_of_block_realization
    {S Ω : Type u} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace Ω]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (P : ProbabilityMeasure Ω) (X : Ω → S) (Xs : ℕ → Ω → S)
    (hX : Measurable X) (hXs : ∀ n, Measurable (Xs n))
    (hLaw : Measure.map X (P : Measure Ω) = (μ : Measure S))
    (hLaws : ∀ n, Measure.map (Xs n) (P : Measure Ω) = (μs n : Measure S))
    (N : ℕ → ℕ) (hN : StrictMono N) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (G : ℕ → Set Ω) (hG : ∀ m, MeasurableSet (G m))
    (hsum : (∑' m, (P : Measure Ω) (G m)ᶜ) < ∞)
    (hgood : ∀ m ω, ω ∈ G m → ∀ n, N m ≤ n → n < N (m + 1) →
      dist (Xs n ω) (X ω) < r m) :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.AlmostSureRepresentation μs μ := by
  obtain ⟨E, hE, hPE, hlim⟩ := common_full_event_of_block_bounds
    (P : Measure Ω) X Xs N hN r hr G hG hsum hgood
  exact ⟨Ω, inferInstance, P, X, Xs, hX, hXs, hLaw, hLaws, E, hE, hPE, hlim⟩

/-- Turn the upstream distinguished-remainder representation into a single
finite measurable partition, as needed for the mixture construction. -/
theorem finite_partition_of_remainder
    {S : Type u} [MeasurableSpace S] (A₀ : Set S) (C : Finset (Set S))
    (hA₀ : MeasurableSet A₀) (hC : ∀ A ∈ C, MeasurableSet A)
    (hpair : (C : Set (Set S)).Pairwise Disjoint)
    (hdis : ∀ A ∈ C, Disjoint A₀ A)
    (hcover : A₀ ∪ (⋃ A ∈ C, A) = univ) :
    (insert A₀ C : Set (Set S)).Pairwise Disjoint ∧
      (∀ A ∈ insert A₀ C, MeasurableSet A) ∧
      (⋃ A ∈ insert A₀ C, A) = univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.coe_insert] using
      hpair.insert (fun A hA _ => ⟨hdis A hA, (hdis A hA).symm⟩)
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact hA₀
    · exact hC A hA
  · rw [Finset.set_biUnion_insert]
    exact hcover

/-- The source's bound `a_m + μ(A₀_m)` is summable when both terms are
bounded by one common summable sequence. -/
theorem summable_block_errors
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (G : ℕ → Set Ω) (a b : ℕ → ℝ≥0∞)
    (ha : (∑' m, a m) < ∞) (hb : ∀ m, b m ≤ a m)
    (hbound : ∀ m, P (G m)ᶜ ≤ a m + b m) :
    (∑' m, P (G m)ᶜ) < ∞ := by
  calc
    (∑' m, P (G m)ᶜ) ≤ ∑' m, (a m + a m) :=
      ENNReal.tsum_le_tsum (fun m => (hbound m).trans (add_le_add le_rfl (hb m)))
    _ = (∑' m, a m) + ∑' m, a m := ENNReal.tsum_add
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨ha, ha⟩


/-- A finite partition gives a mixture with a common portion whose conditional
laws are supported in their respective positive-mass cells. The remainder is
an actual probability measure, including when some cells have zero mass. -/
theorem finite_partition_mixture
    {S : Type u} {ι : Type v} [MeasurableSpace S] [Fintype ι]
    (μ ν : ProbabilityMeasure S) (D : ι → Set S)
    (hD : ∀ i, MeasurableSet (D i)) (hdis : _root_.Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcover : (⋃ i, D i) = univ)
    (b : ℝ≥0∞) (hb0 : b ≠ 0) (hb1 : b < 1)
    (hdom : ∀ i, b * (μ : Measure S) (D i) ≤ (ν : Measure S) (D i)) :
    ∃ (lam : ι → ProbabilityMeasure S) (ρ : ProbabilityMeasure S),
      (∀ i, (μ : Measure S) (D i) ≠ 0 → (lam i : Measure S) (D i) = 1) ∧
      (ν : Measure S) =
        b • (∑ i, (μ : Measure S) (D i) • (lam i : Measure S)) +
        (1 - b) • (ρ : Measure S) := by
  classical
  let lam : ι → ProbabilityMeasure S := fun i =>
    if h : (ν : Measure S) (D i) = 0 then ν
    else ⟨ProbabilityTheory.cond (ν : Measure S) (D i),
      ProbabilityTheory.cond_isProbabilityMeasure h⟩
  have hlam (i : ι) (hi : (ν : Measure S) (D i) ≠ 0) :
      (lam i : Measure S) = ((ν : Measure S) (D i))⁻¹ • (ν : Measure S).restrict (D i) := by
    simp [lam, hi, ProbabilityTheory.cond]
  have hsupport (i : ι) (hi : (μ : Measure S) (D i) ≠ 0) :
      (lam i : Measure S) (D i) = 1 := by
    have hνi : (ν : Measure S) (D i) ≠ 0 := by
      intro hz
      have := hdom i
      rw [hz, nonpos_iff_eq_zero, mul_eq_zero] at this
      exact this.elim hb0 hi
    rw [hlam i hνi, Measure.smul_apply, Measure.restrict_apply (hD i), inter_self,
      smul_eq_mul, ENNReal.inv_mul_cancel hνi (measure_ne_top _ _)]
  let Q : Measure S := ∑ i, (μ : Measure S) (D i) • (lam i : Measure S)
  have hmass : Q univ = 1 := by
    simp only [Q, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    simpa only [hcover, measure_univ, tsum_fintype] using
      (measure_iUnion hdis hD (μ := (μ : Measure S))).symm
  haveI : IsProbabilityMeasure Q := ⟨hmass⟩
  have hle : b • Q ≤ (ν : Measure S) := by
    have hterm (i : ι) :
        b • ((μ : Measure S) (D i) • (lam i : Measure S)) ≤
          (ν : Measure S).restrict (D i) := by
      by_cases hz : (ν : Measure S) (D i) = 0
      · have hμi : (μ : Measure S) (D i) = 0 := by
          have := hdom i
          rw [hz, nonpos_iff_eq_zero, mul_eq_zero] at this
          exact this.resolve_left hb0
        simp only [hμi, zero_smul, smul_zero]
        exact bot_le
      · rw [hlam i hz, smul_smul, smul_smul]
        have hc : b * (μ : Measure S) (D i) * ((ν : Measure S) (D i))⁻¹ ≤ 1 := by
          calc
            b * (μ : Measure S) (D i) * ((ν : Measure S) (D i))⁻¹ ≤
                (ν : Measure S) (D i) * ((ν : Measure S) (D i))⁻¹ :=
              mul_le_mul (hdom i) le_rfl zero_le zero_le
            _ = 1 := ENNReal.mul_inv_cancel hz (measure_ne_top _ _)
        intro A
        simp only [Measure.smul_apply, smul_eq_mul]
        exact (mul_le_mul hc le_rfl zero_le zero_le).trans_eq (one_mul _)
    calc
      b • Q = ∑ i, b • ((μ : Measure S) (D i) • (lam i : Measure S)) :=
        Finset.smul_sum ..
      _ ≤ ∑ i, (ν : Measure S).restrict (D i) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (ν : Measure S) := by
        rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdis hD, hcover,
          Measure.restrict_univ]
  have hbtop : b ≠ ∞ := ne_top_of_lt hb1
  haveI : IsFiniteMeasure (b • Q) := Q.smul_finite hbtop
  have hres : ((ν : Measure S) - b • Q) univ = 1 - b := by
    rw [Measure.sub_apply MeasurableSet.univ hle, measure_univ, Measure.smul_apply,
      hmass, smul_eq_mul, mul_one]
  have ha0 : 1 - b ≠ 0 := (tsub_pos_iff_lt.mpr hb1).ne'
  have hatop : 1 - b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  let ρ : ProbabilityMeasure S :=
    ⟨(1 - b)⁻¹ • ((ν : Measure S) - b • Q), ⟨by
      rw [Measure.smul_apply, hres, smul_eq_mul, ENNReal.inv_mul_cancel ha0 hatop]⟩⟩
  refine ⟨lam, ρ, hsupport, ?_⟩
  change (ν : Measure S) = b • Q + (1 - b) • ((1 - b)⁻¹ • ((ν : Measure S) - b • Q))
  rw [smul_smul, ENNReal.mul_inv_cancel ha0 hatop, one_smul, add_comm,
    Measure.sub_add_cancel_of_le hle]


/-- Choose the cell of a measurable partition, allowing empty cells. -/
def partitionIndex {A : Type*} {ι : Type*} (D : ι → Set A)
    (hcover : (⋃ i, D i) = univ) (x : A) : ι :=
  Classical.choose (show ∃ i, x ∈ D i from mem_iUnion.mp (hcover.symm ▸ mem_univ x))

theorem mem_partitionIndex {A : Type*} {ι : Type*} (D : ι → Set A)
    (hcover : (⋃ i, D i) = univ) (x : A) : x ∈ D (partitionIndex D hcover x) :=
  Classical.choose_spec (show ∃ i, x ∈ D i from mem_iUnion.mp (hcover.symm ▸ mem_univ x))

theorem partitionIndex_eq {A : Type*} {ι : Type*} (D : ι → Set A)
    (hcover : (⋃ i, D i) = univ)
    (hdis : _root_.Pairwise (fun i j => Disjoint (D i) (D j)))
    {x : A} {i : ι} (hi : x ∈ D i) : partitionIndex D hcover x = i := by
  by_contra hn
  exact Set.disjoint_left.mp (hdis hn) (mem_partitionIndex D hcover x) hi

/-- Selecting an independent sample according to a finite measurable partition
has the corresponding mixture law. No topology is needed on any space. -/
theorem finite_partition_sampling
    {A W S ι : Type*} [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace S]
    [Fintype ι] (μ : Measure A) (Q : Measure W) [IsProbabilityMeasure Q]
    (D : ι → Set A) (hD : ∀ i, MeasurableSet (D i))
    (hdis : _root_.Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcover : (⋃ i, D i) = univ)
    (Z : ι → W → S) (hZ : ∀ i, Measurable (Z i)) :
    let Y : A × W → S := fun p => Z (partitionIndex D hcover p.1) p.2
    Measurable Y ∧
      Measure.map Y (μ.prod Q) = ∑ i, μ (D i) • Measure.map (Z i) Q := by
  classical
  dsimp only
  let Y : A × W → S := fun p => Z (partitionIndex D hcover p.1) p.2
  have hpre (B : Set S) : Y ⁻¹' B = ⋃ i, D i ×ˢ (Z i ⁻¹' B) := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion.mpr ⟨partitionIndex D hcover p.1, mem_partitionIndex D hcover p.1, hp⟩
    · intro hp
      obtain ⟨i, hi, hZp⟩ := mem_iUnion.mp hp
      change Z (partitionIndex D hcover p.1) p.2 ∈ B
      rw [partitionIndex_eq D hcover hdis hi]
      exact hZp
  have hY : Measurable Y := by
    intro B hB
    rw [hpre B]
    exact MeasurableSet.iUnion (fun i => (hD i).prod (hZ i hB))
  refine ⟨hY, ?_⟩
  ext B hB
  rw [Measure.map_apply hY hB, hpre B, measure_iUnion, tsum_fintype]
  · simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.prod_prod, Measure.map_apply (hZ _) hB]
  · intro i j hij
    exact (hdis hij).set_prod_left _ _
  · exact fun i => (hD i).prod (hZ i hB)


/-- Add a failure cell to a partition by means of a measurable gate. -/
def gatedPartition {A B ι : Type*} (D : ι → Set A) (T : Set B) :
    Option ι → Set (A × B)
  | none => univ ×ˢ Tᶜ
  | some i => D i ×ˢ T

theorem gatedPartition_properties
    {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (D : ι → Set A) (hD : ∀ i, MeasurableSet (D i))
    (hdis : _root_.Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcover : (⋃ i, D i) = univ) (T : Set B) (hT : MeasurableSet T) :
    (∀ i, MeasurableSet (gatedPartition D T i)) ∧
    _root_.Pairwise (fun i j => Disjoint (gatedPartition D T i) (gatedPartition D T j)) ∧
    (⋃ i, gatedPartition D T i) = univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases i with
    | none => exact MeasurableSet.univ.prod hT.compl
    | some i => exact (hD i).prod hT
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact disjoint_compl_left.set_prod_right _ _
    · exact disjoint_compl_right.set_prod_right _ _
    · exact (hdis (fun he => hij (congrArg some he))).set_prod_left _ _
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x.2 ∈ T
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x.1)
      exact mem_iUnion.mpr ⟨some i, hi, hx⟩
    · exact mem_iUnion.mpr ⟨none, mem_univ _, hx⟩

/-- A coin with an extended-nonnegative success parameter. -/
def partitionCoin (b : ℝ≥0∞) (hb : b ≤ 1) : ProbabilityMeasure Bool :=
  ⟨b • Measure.dirac true + (1 - b) • Measure.dirac false, ⟨by
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le hb⟩⟩

@[simp] theorem partitionCoin_true (b : ℝ≥0∞) (hb : b ≤ 1) :
    (partitionCoin b hb : Measure Bool) {true} = b := by
  simp [partitionCoin, Measure.add_apply, Measure.smul_apply]


/-- Strict thresholds give disjoint blocks. -/
theorem threshold_block_unique (N : ℕ → ℕ) (hN : StrictMono N)
    {n i j : ℕ} (hi : N i ≤ n ∧ n < N (i + 1))
    (hj : N j ≤ n ∧ n < N (j + 1)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim ((not_lt_of_ge ((hN.monotone (by omega : i + 1 ≤ j)).trans hj.1)) hi.2)
  · exact hij
  · exact False.elim ((not_lt_of_ge ((hN.monotone (by omega : j + 1 ≤ i)).trans hi.1)) hj.2)

/-- The block estimate only needs to hold almost everywhere in each block.
This avoids imposing measurability of the distance between two arbitrary
metric-space-valued random elements. -/
theorem common_full_event_of_ae_block_bounds
    {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MetricSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → S) (Xs : ℕ → Ω → S)
    (N : ℕ → ℕ) (hN : StrictMono N) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (G : ℕ → Set Ω) (hG : ∀ m, MeasurableSet (G m))
    (hsum : (∑' m, P (G m)ᶜ) < ∞)
    (hgood : ∀ m, ∀ᵐ ω ∂P, ω ∈ G m → ∀ n, N m ≤ n → n < N (m + 1) →
      dist (Xs n ω) (X ω) < r m) :
    ∃ E : Set Ω, MeasurableSet E ∧ P E = 1 ∧
      ∀ ω ∈ E, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω)) := by
  apply (Ch01.almostSurely_iff_measurable_one P _).mp
  have hnull := Ch02.first_borel_cantelli P (fun m => (G m)ᶜ)
    (fun m => (hG m).compl) hsum
  rw [Ch02.infinitelyOftenEvent_eq_limsup] at hnull
  have hbc : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ G m := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with ω hω
    simpa only [mem_limsup_iff_frequently_mem, Filter.Frequently, mem_compl_iff,
      not_not] using hω
  filter_upwards [hbc, ae_all_iff.mpr hgood] with ω hω hg
  exact tendsto_of_eventually_successful_blocks (fun n => Xs n ω) (X ω) N hN r hr
    (hω.mono (fun m hm => hg m hm))


/-- Realize all the finite-cell mixtures at once. A single coin is shared by
an entire block. Independent coordinates supply the conditional samples and
remainders, and the original laws supply the finitely many initial samples. -/
theorem representation_of_cell_mixtures
    {S : Type u} [MetricSpace S] [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (ι : ℕ → Type u) [∀ m, Fintype (ι m)]
    (D : ∀ m, ι m → Set S) (i₀ : ∀ m, ι m)
    (hD : ∀ m i, MeasurableSet (D m i))
    (hdis : ∀ m, _root_.Pairwise (fun i j => Disjoint (D m i) (D m j)))
    (hcover : ∀ m, (⋃ i, D m i) = univ)
    (N : ℕ → ℕ) (hN : StrictMono N) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsmall : ∀ m i, i ≠ i₀ m → Bornology.IsBounded (D m i) ∧ diam (D m i) < r m)
    (b : ℕ → ℝ≥0∞) (hb : ∀ m, b m ≤ 1)
    (lam : ∀ m, ℕ → ι m → ProbabilityMeasure S)
    (ρ : ℕ → ℕ → ProbabilityMeasure S)
    (hsupport : ∀ m n, N m ≤ n → ∀ i,
      (μ : Measure S) (D m i) ≠ 0 → (lam m n i : Measure S) (D m i) = 1)
    (hmix : ∀ m n, N m ≤ n → (μs n : Measure S) =
      b m • (∑ i, (μ : Measure S) (D m i) • (lam m n i : Measure S)) +
        (1 - b m) • (ρ m n : Measure S))
    (hsum : (∑' m, ((1 - b m) + (μ : Measure S) (D m (i₀ m)))) < ∞) :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.AlmostSureRepresentation μs μ := by
  classical
  let J := (Σ m : ℕ, ℕ × Option (ι m)) ⊕ ℕ
  let π : J → ProbabilityMeasure S := fun j => match j with
    | .inl ⟨m, n, none⟩ => ρ m n
    | .inl ⟨m, n, some i⟩ => lam m n i
    | .inr n => μs n
  let W := J → S
  let Q : Measure W := Measure.infinitePi (fun j => (π j : Measure S))
  haveI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  let C : Measure (ℕ → Bool) :=
    Measure.infinitePi (fun m => (partitionCoin (b m) (hb m) : Measure Bool))
  haveI : IsProbabilityMeasure C := by dsimp [C]; infer_instance
  let A : Measure (S × (ℕ → Bool)) := (μ : Measure S).prod C
  haveI : IsProbabilityMeasure A := by dsimp [A]; infer_instance
  let Ω := (S × (ℕ → Bool)) × W
  let P : Measure Ω := A.prod Q
  haveI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : Ω → S := fun ω => ω.1.1
  have hX : Measurable X := measurable_fst.comp measurable_fst
  have hXlaw : Measure.map X P = (μ : Measure S) := by
    change Measure.map (Prod.fst ∘ Prod.fst) (A.prod Q) = _
    rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
    simp [A]
  let Z : J → Ω → S := fun j ω => ω.2 j
  have hZ (j : J) : Measurable (Z j) := (measurable_pi_apply j).comp measurable_snd
  have hZlaw (j : J) : Measure.map (Z j) P = (π j : Measure S) := by
    change Measure.map ((fun w : W => w j) ∘ Prod.snd) (A.prod Q) = _
    rw [← Measure.map_map (measurable_pi_apply j) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
    exact Measure.infinitePi_map_eval _ j
  let T : ℕ → Set (ℕ → Bool) := fun m => {c | c m = true}
  have hT (m : ℕ) : MeasurableSet (T m) := by
    change MeasurableSet ((fun c : ℕ → Bool => c m) ⁻¹' {true})
    exact (measurable_pi_apply m) (measurableSet_singleton true)
  have hCT (m : ℕ) : C (T m) = b m := by
    change C ((fun c : ℕ → Bool => c m) ⁻¹' {true}) = _
    rw [← Measure.map_apply (measurable_pi_apply m) (measurableSet_singleton true)]
    simp [C, Measure.infinitePi_map_eval]
  have heval (j : J) : Measure.map (fun w : W => w j) Q = (π j : Measure S) :=
    Measure.infinitePi_map_eval _ j
  have hCcompl (m : ℕ) : C (T m)ᶜ = 1 - b m := by
    rw [prob_compl_eq_one_sub (hT m), hCT]
  let E (m : ℕ) := gatedPartition (D m) (T m)
  have hE (m : ℕ) := gatedPartition_properties (D m) (hD m) (hdis m) (hcover m) (T m) (hT m)
  let Y : ℕ → ℕ → Ω → S := fun m n ω =>
    ω.2 (.inl ⟨m, n, partitionIndex (E m) (hE m).2.2 ω.1⟩)
  have hY (m n : ℕ) : Measurable (Y m n) :=
    (finite_partition_sampling A Q (E m) (hE m).1 (hE m).2.1 (hE m).2.2
      (fun i (w : W) => w (.inl ⟨m, n, i⟩)) (fun i => measurable_pi_apply _)).1
  have hYlaw (m n : ℕ) (hn : N m ≤ n) : Measure.map (Y m n) P = (μs n : Measure S) := by
    have hh := (finite_partition_sampling A Q (E m) (hE m).1 (hE m).2.1 (hE m).2.2
      (fun i (w : W) => w (.inl ⟨m, n, i⟩)) (fun i => measurable_pi_apply _)).2
    change Measure.map (Y m n) P = _ at hh
    rw [hh, Fintype.sum_option, hmix m n hn, Finset.smul_sum]
    simp only [E, gatedPartition, A, Measure.prod_prod, measure_univ, one_mul,
      hCcompl, hCT, heval, π, smul_smul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  let k : ∀ n, N 0 ≤ n → ℕ := fun n hn => (exists_threshold_block N hN n hn).choose
  have hk (n : ℕ) (hn : N 0 ≤ n) : N (k n hn) ≤ n ∧ n < N (k n hn + 1) :=
    (exists_threshold_block N hN n hn).choose_spec
  let Xs : ℕ → Ω → S := fun n => if hn : N 0 ≤ n then Y (k n hn) n else Z (.inr n)
  have hXs (n : ℕ) : Measurable (Xs n) := by
    dsimp only [Xs]
    split_ifs with hn
    · exact hY _ _
    · exact hZ _
  have hLaws (n : ℕ) : Measure.map (Xs n) P = (μs n : Measure S) := by
    dsimp only [Xs]
    split_ifs with hn
    · exact hYlaw _ _ (hk n hn).1
    · exact hZlaw _
  have hblock {m n : ℕ} (hn : N m ≤ n) (hn' : n < N (m + 1)) : Xs n = Y m n := by
    have hn0 : N 0 ≤ n := (hN.monotone (Nat.zero_le m)).trans hn
    dsimp only [Xs]
    rw [dite_eq_left hn0, threshold_block_unique N hN (hk n hn0) ⟨hn, hn'⟩]
  let G : ℕ → Set Ω := fun m => ((D m (i₀ m))ᶜ ×ˢ T m) ×ˢ (univ : Set W)
  have hG (m : ℕ) : MeasurableSet (G m) :=
    ((hD m _).compl.prod (hT m)).prod MeasurableSet.univ
  have hGbound (m : ℕ) : P (G m)ᶜ ≤ (1 - b m) + (μ : Measure S) (D m (i₀ m)) := by
    have heq : (G m)ᶜ =
        ((D m (i₀ m) ×ˢ (univ : Set (ℕ → Bool))) ×ˢ (univ : Set W)) ∪
        (((univ : Set S) ×ˢ (T m)ᶜ) ×ˢ (univ : Set W)) := by
      ext ω
      change ¬ ((ω.1.1 ∉ D m (i₀ m) ∧ ω.1.2 ∈ T m) ∧ True) ↔
        ((ω.1.1 ∈ D m (i₀ m) ∧ True) ∧ True) ∨ ((True ∧ ω.1.2 ∉ T m) ∧ True)
      simp only [and_true, true_and, not_and_or, not_not]
    rw [heq]
    apply (measure_union_le _ _).trans_eq
    change ((μ : Measure S).prod C).prod Q _ + ((μ : Measure S).prod C).prod Q _ = _
    rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
      measure_univ, measure_univ, measure_univ, hCcompl]
    simp only [mul_one, one_mul]
    exact add_comm _ _
  have hgood (m : ℕ) : ∀ᵐ ω ∂P, ω ∈ G m → ∀ n, N m ≤ n → n < N (m + 1) →
      dist (Xs n ω) (X ω) < r m := by
    have hx (i : ι m) : ∀ᵐ ω ∂P, X ω ∈ D m i → (μ : Measure S) (D m i) ≠ 0 := by
      by_cases hz : (μ : Measure S) (D m i) = 0
      · have hzero : P (X ⁻¹' D m i) = 0 := by
          rw [← Measure.map_apply hX (hD m i), hXlaw, hz]
        exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono (fun ω hω hmem => (hω hmem).elim)
      · exact Eventually.of_forall (fun _ _ => hz)
    have hz (n : ℕ) (i : ι m) : ∀ᵐ ω ∂P, N m ≤ n → (μ : Measure S) (D m i) ≠ 0 →
        Z (.inl ⟨m, n, some i⟩) ω ∈ D m i := by
      by_cases hn : N m ≤ n
      · by_cases hi : (μ : Measure S) (D m i) ≠ 0
        · have hfull : P (Z (.inl ⟨m, n, some i⟩) ⁻¹' D m i) = 1 := by
            rw [← Measure.map_apply (hZ _) (hD m i), hZlaw]
            exact hsupport m n hn i hi
          have hzmem : ∀ᵐ ω ∂P, Z (.inl ⟨m, n, some i⟩) ω ∈ D m i :=
            (mem_ae_iff_prob_eq_one ((hD m i).preimage (hZ _))).mpr hfull
          exact Filter.Eventually.mono hzmem (fun ω hω _ _ => hω)
        · exact Eventually.of_forall (fun _ _ h => (hi h).elim)
      · exact Eventually.of_forall (fun _ h => (hn h).elim)
    filter_upwards [ae_all_iff.mpr hx, ae_all_iff.mpr (fun n => ae_all_iff.mpr (hz n))]
      with ω hxω hzω
    intro hω n hn hn'
    let i := partitionIndex (D m) (hcover m) (X ω)
    have hxi : X ω ∈ D m i := mem_partitionIndex (D m) (hcover m) (X ω)
    have hi : i ≠ i₀ m := by
      intro he
      exact hω.1.1 (he ▸ hxi)
    have hy : Y m n ω = Z (.inl ⟨m, n, some i⟩) ω := by
      change ω.2 (.inl ⟨m, n, partitionIndex (E m) (hE m).2.2 ω.1⟩) = _
      rw [partitionIndex_eq (E m) (hE m).2.2 (hE m).2.1
        (show ω.1 ∈ E m (some i) from ⟨hxi, hω.1.2⟩)]
    rw [hblock hn hn', hy]
    exact (dist_le_diam_of_mem (hsmall m i hi).1 (hzω n i hn (hxω i hxi)) hxi).trans_lt
      (hsmall m i hi).2
  have hs : (∑' m, P (G m)ᶜ) < ∞ :=
    (ENNReal.tsum_le_tsum hGbound).trans_lt hsum
  obtain ⟨F, hF, hPF, hlim⟩ := common_full_event_of_ae_block_bounds P X Xs N hN r hr G hG hs hgood
  exact ⟨Ω, inferInstance, ⟨P, inferInstance⟩, X, Xs, hX, hXs, hXlaw, hLaws, F, hF, hPF, hlim⟩

/-- Skorokhod representation on an arbitrary metric space when the limiting
law has a separable Borel set of full mass. -/
theorem skorokhod_representation :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.representationType.{u} := by
  classical
  intro S _ _ _ μs μ hweak ⟨M, hM, hsep, hμM⟩
  let r : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1)
  let a : ℕ → ℝ≥0∞ := fun m => (1 / 2 : ℝ≥0∞) ^ (m + 1)
  let b : ℕ → ℝ≥0∞ := fun m => 1 - a m
  have hrpos (m : ℕ) : 0 < r m := pow_pos (by norm_num) _
  have halt (m : ℕ) : a m < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have haof (m : ℕ) : ENNReal.ofReal (r m) = a m := by
    dsimp [r, a]
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hapos (m : ℕ) : 0 < a m := by
    rw [← haof]
    exact ENNReal.ofReal_pos.mpr (hrpos m)
  have hb0 (m : ℕ) : b m ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr (halt m))
  have hblt (m : ℕ) : b m < 1 := ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt (hapos m))
  have hbsub (m : ℕ) : 1 - b m = a m := ENNReal.sub_sub_cancel (by simp) (halt m).le
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  have hasum : (∑' m, a m) < ∞ := by
    dsimp [a]
    rw [ENNReal.tsum_geometric_add_one]
    apply ENNReal.mul_lt_top
    · norm_num
    · rw [ENNReal.inv_lt_top]
      norm_num
  obtain ⟨A₀, C, N, hN, hC, hdom⟩ :=
    scheduled_continuity_partitions μs μ hweak M hM hsep hμM r r hrpos hrpos b hblt
  let ι : ℕ → Type u := fun m => {A : Set S // A ∈ insert (A₀ m) (C m)}
  let D : ∀ m, ι m → Set S := fun _ i => i.1
  let i₀ : ∀ m, ι m := fun m => ⟨A₀ m, Finset.mem_insert_self _ _⟩
  have hpart (m : ℕ) := finite_partition_of_remainder (A₀ m) (C m)
    (hC m).1.1 (fun A hA => ((hC m).2.2.2.1 A hA).2.1.1)
    (hC m).2.2.1 (hC m).2.2.2.2.1 (hC m).2.2.2.2.2
  have hD (m : ℕ) (i : ι m) : MeasurableSet (D m i) := (hpart m).2.1 _ i.2
  have hdis (m : ℕ) : _root_.Pairwise (fun i j => Disjoint (D m i) (D m j)) := by
    intro i j hij
    have hp : (↑(insert (A₀ m) (C m)) : Set (Set S)).Pairwise Disjoint := by
      simpa only [Finset.coe_insert] using (hpart m).1
    exact hp i.2 j.2 (fun h => hij (Subtype.ext h))
  have hcover (m : ℕ) : (⋃ i, D m i) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x ∈ ⋃ A ∈ insert (A₀ m) (C m), A := by rw [(hpart m).2.2]; trivial
    rcases mem_iUnion.mp hx with ⟨A, hA⟩
    rcases mem_iUnion.mp hA with ⟨hA, hx⟩
    exact ⟨⟨A, hA⟩, hx⟩
  have hsmall (m : ℕ) (i : ι m) (hi : i ≠ i₀ m) :
      Bornology.IsBounded (D m i) ∧ diam (D m i) < r m := by
    have hmem : i.1 ∈ C m := by
      rcases Finset.mem_insert.mp i.2 with h | h
      · exact (hi (Subtype.ext h)).elim
      · exact h
    exact ((hC m).2.2.2.1 _ hmem).2.2
  have hfinite (m n : ℕ) (hn : N m ≤ n) := finite_partition_mixture μ (μs n)
    (D m) (hD m) (hdis m) (hcover m) (b m) (hb0 m) (hblt m)
    (fun i => hdom m n hn i.1 i.2)
  choose lam ρ hsupport hmix using hfinite
  let lam' : ∀ m, ℕ → ι m → ProbabilityMeasure S := fun m n =>
    if hn : N m ≤ n then lam m n hn else fun _ => μ
  let ρ' : ℕ → ℕ → ProbabilityMeasure S := fun m n =>
    if hn : N m ≤ n then ρ m n hn else μ
  have hsupport' (m n : ℕ) (hn : N m ≤ n) (i : ι m)
      (hi : (μ : Measure S) (D m i) ≠ 0) :
      (lam' m n i : Measure S) (D m i) = 1 := by
    simpa only [lam', dite_eq_left hn] using hsupport m n hn i hi
  have hmix' (m n : ℕ) (hn : N m ≤ n) : (μs n : Measure S) =
      b m • (∑ i, (μ : Measure S) (D m i) • (lam' m n i : Measure S)) +
        (1 - b m) • (ρ' m n : Measure S) := by
    simpa only [lam', ρ', dite_eq_left hn] using hmix m n hn
  have hsum : (∑' m, ((1 - b m) + (μ : Measure S) (D m (i₀ m)))) < ∞ := by
    calc
      (∑' m, ((1 - b m) + (μ : Measure S) (D m (i₀ m)))) ≤ ∑' m, (a m + a m) := by
        apply ENNReal.tsum_le_tsum
        intro m
        rw [hbsub]
        apply add_le_add le_rfl
        change (μ : Measure S) (A₀ m) ≤ a m
        rw [← haof]
        exact (hC m).2.1.le
      _ = (∑' m, a m) + ∑' m, a m := ENNReal.tsum_add
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hasum, hasum⟩
  exact representation_of_cell_mixtures μs μ ι D i₀ hD hdis hcover N hN r hrlim hsmall
    b (fun m => (hblt m).le) lam' ρ' hsupport' hmix' hsum

/-- The whole target space supplies the separable Borel full-mass set. -/
theorem skorokhod_representation_separable :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.separableRepresentationType.{u} := by
  intro S _ _ _ _ μs μ hweak
  exact skorokhod_representation μs μ hweak (separable_full_support μ)

/-- Modify the constructed variables on their common measurable null event. -/
theorem skorokhod_representation_everywhere :
    Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation.everywhereRepresentationType.{u} := by
  intro S _ _ _ μs μ hweak hsep
  exact everywhere_realization_of_almostSure μs μ (skorokhod_representation μs μ hweak hsep)

end
end ProbabilityFoundations.Ch06
