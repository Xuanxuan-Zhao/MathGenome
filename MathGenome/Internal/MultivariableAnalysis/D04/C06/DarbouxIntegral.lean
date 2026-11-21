import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.StepComparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

noncomputable section
open Set
open scoped BigOperators
namespace D04.Darboux

abbrev Box := Specs.D04.C06.DarbouxIntegral.Model.Box
abbrev carrier := @Specs.D04.C06.DarbouxIntegral.Model.carrier
abbrev content := @Specs.D04.C06.DarbouxIntegral.Model.content
abbrev Degenerate := @Specs.D04.C06.DarbouxIntegral.Model.Degenerate
abbrev Nondegenerate := @Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate
abbrev Grid := @Specs.D04.C06.DarbouxIntegral.Model.Grid
abbrev CellIndex := @Specs.D04.C06.DarbouxIntegral.Model.CellIndex
abbrev cellBox := @Specs.D04.C06.DarbouxIntegral.Model.cellBox
abbrev cell := @Specs.D04.C06.DarbouxIntegral.Model.cell
abbrev cellContent := @Specs.D04.C06.DarbouxIntegral.Model.cellContent
abbrev mesh := @Specs.D04.C06.DarbouxIntegral.Model.mesh
abbrev Tagging := @Specs.D04.C06.DarbouxIntegral.Model.Tagging
abbrev taggedSum := @Specs.D04.C06.DarbouxIntegral.Model.taggedSum
abbrev Bounded := @Specs.D04.C06.DarbouxIntegral.Model.Bounded
abbrev cellInfimum := @Specs.D04.C06.DarbouxIntegral.Model.cellInfimum
abbrev cellSupremum := @Specs.D04.C06.DarbouxIntegral.Model.cellSupremum
abbrev lowerSum := @Specs.D04.C06.DarbouxIntegral.Model.lowerSum
abbrev upperSum := @Specs.D04.C06.DarbouxIntegral.Model.upperSum
abbrev lowerIntegral := @Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
abbrev upperIntegral := @Specs.D04.C06.DarbouxIntegral.Model.upperIntegral
abbrev Integrable := @Specs.D04.C06.DarbouxIntegral.Model.Integrable
abbrev integral := @Specs.D04.C06.DarbouxIntegral.Model.integral
abbrev Refines := @Specs.D04.C06.DarbouxIntegral.Model.Refines
abbrev GapCriterion := @Specs.D04.C06.DarbouxIntegral.Model.GapCriterion
abbrev HasTaggedIntegral := @Specs.D04.C06.DarbouxIntegral.Model.HasTaggedIntegral
abbrev scalarPoint := Specs.D04.C06.DarbouxIntegral.Model.scalarPoint
abbrev intervalBox := Specs.D04.C06.DarbouxIntegral.Model.intervalBox
abbrev intervalTags := @Specs.D04.C06.DarbouxIntegral.Model.intervalTags
abbrev intervalGrid := @Specs.D04.C06.DarbouxIntegral.Model.intervalGrid

variable {n : ℕ}

theorem content_nonneg (Q : Box n) : 0 ≤ content Q :=
  Finset.prod_nonneg fun i _ => sub_nonneg.mpr (Q.ordered i)

theorem content_degenerate (Q : Box n) (h : Degenerate Q) : content Q = 0 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.mpr hi.symm)

theorem lower_mem (Q : Box n) : Q.lower ∈ carrier Q := fun i => ⟨le_rfl, Q.ordered i⟩
theorem upper_mem (Q : Box n) : Q.upper ∈ carrier Q := fun i => ⟨Q.ordered i, le_rfl⟩
theorem carrier_nonempty (Q : Box n) : (carrier Q).Nonempty := ⟨Q.lower, lower_mem Q⟩

theorem grid_exists (Q : Box n) : Nonempty (Grid Q) := by
  exact ⟨fun i => Classical.choice (SingleVariableAnalysis.Riemann.partition_exists (Q.ordered i))⟩

theorem cell_subset {Q : Box n} (P : Grid Q) (c : CellIndex P) : cell P c ⊆ carrier Q := by
  intro x hx i
  exact SingleVariableAnalysis.Riemann.cell_subset_interval (P i) (c i) (hx i)

theorem cell_nonempty {Q : Box n} (P : Grid Q) (c : CellIndex P) : (cell P c).Nonempty :=
  carrier_nonempty (cellBox P c)

theorem cellContent_nonneg {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    0 ≤ cellContent P c := content_nonneg _

theorem cellContent_product {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    cellContent P c = ∏ i, SingleVariableAnalysis.Riemann.cellLength (P i) (c i) := rfl

theorem content_partition {Q : Box n} (P : Grid Q) :
    ∑ c, cellContent P c = content Q := by
  classical
  change (∑ c : ∀ i, Fin (P i).n, ∏ i, SingleVariableAnalysis.Riemann.cellLength (P i) (c i)) = _
  have hp := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Fin (P i).n)))
    (fun i j => SingleVariableAnalysis.Riemann.cellLength (P i) j)
  simp only [Fintype.piFinset_univ] at hp
  rw [← hp]
  apply Finset.prod_congr rfl
  intro i _
  exact (SingleVariableAnalysis.Riemann.sum_cell_differences (P i).point).trans (by rw [(P i).first, (P i).last])

theorem tags_exist {Q : Box n} (P : Grid Q) : Nonempty (Tagging P) :=
  ⟨fun c => ⟨(cellBox P c).lower, lower_mem _⟩⟩

theorem cell_image_bounded (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (c : CellIndex P) :
    BddBelow (f '' cell P c) ∧ BddAbove (f '' cell P c) :=
  ⟨hf.1.mono (Set.image_mono (cell_subset P c)),
   hf.2.mono (Set.image_mono (cell_subset P c))⟩

theorem cellInfimum_le (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (c : CellIndex P) {x : E n} (hx : x ∈ cell P c) :
    cellInfimum f P c ≤ f x :=
  csInf_le (cell_image_bounded f hf P c).1 ⟨x, hx, rfl⟩

theorem le_cellSupremum (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (c : CellIndex P) {x : E n} (hx : x ∈ cell P c) :
    f x ≤ cellSupremum f P c :=
  le_csSup (cell_image_bounded f hf P c).2 ⟨x, hx, rfl⟩

theorem tagged_bounds (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (ξ : Tagging P) : lowerSum f P ≤ taggedSum f P ξ ∧
    taggedSum f P ξ ≤ upperSum f P := by
  constructor
  · exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right
      (cellInfimum_le f hf P c (ξ c).property) (cellContent_nonneg P c)
  · exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right
      (le_cellSupremum f hf P c (ξ c).property) (cellContent_nonneg P c)

theorem same_grid_lower_le_upper (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) : lowerSum f P ≤ upperSum f P := by
  obtain ⟨ξ⟩ := tags_exist P
  exact (tagged_bounds f hf P ξ).1.trans (tagged_bounds f hf P ξ).2

/-- Degenerate boxes have an empty product of cell-index choices, because at
least one coordinate partition has no intervals. This does not affect R^0. -/
theorem no_cells_of_degenerate {Q : Box n} (h : Degenerate Q) (P : Grid Q) :
    IsEmpty (CellIndex P) := by
  obtain ⟨i, hi⟩ := h
  have hn : (P i).n = 0 := by
    by_contra hn
    have ht := (P i).strictMono (show (0 : Fin ((P i).n + 1)) < Fin.last (P i).n from
      Nat.pos_of_ne_zero hn)
    rw [(P i).first, (P i).last, hi] at ht
    exact lt_irrefl _ ht
  exact ⟨fun c => by have hc := (c i).isLt; omega⟩

theorem degenerate_sums (f : E n → ℝ) {Q : Box n} (h : Degenerate Q)
    (P : Grid Q) (ξ : Tagging P) :
    taggedSum f P ξ = 0 ∧ lowerSum f P = 0 ∧ upperSum f P = 0 := by
  let _ := no_cells_of_degenerate h P
  simp [taggedSum, Specs.D04.C06.DarbouxIntegral.Model.taggedSum, lowerSum, Specs.D04.C06.DarbouxIntegral.Model.lowerSum, upperSum, Specs.D04.C06.DarbouxIntegral.Model.upperSum]

theorem degenerate_integrals (f : E n → ℝ) (Q : Box n) (h : Degenerate Q) :
    lowerIntegral f Q = 0 ∧ upperIntegral f Q = 0 := by
  obtain ⟨P₀⟩ := grid_exists Q
  have hl : Set.range (lowerSum f (Q := Q)) = {0} := by
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      obtain ⟨ξ⟩ := tags_exist P
      exact (degenerate_sums f h P ξ).2.1
    · rintro rfl
      obtain ⟨ξ⟩ := tags_exist P₀
      exact ⟨P₀, (degenerate_sums f h P₀ ξ).2.1⟩
  have hu : Set.range (upperSum f (Q := Q)) = {0} := by
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      obtain ⟨ξ⟩ := tags_exist P
      exact (degenerate_sums f h P ξ).2.2
    · rintro rfl
      obtain ⟨ξ⟩ := tags_exist P₀
      exact ⟨P₀, (degenerate_sums f h P₀ ξ).2.2⟩
  change sSup _ = 0 ∧ sInf _ = 0
  rw [hl, hu, csSup_singleton, csInf_singleton]
  exact ⟨rfl, rfl⟩

theorem integrable_degenerate (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q)
    (h : Degenerate Q) : Integrable f Q :=
  ⟨hf, (degenerate_integrals f Q h).1.trans (degenerate_integrals f Q h).2.symm⟩

theorem zero_dimension (Q : Box 0) (f : E 0 → ℝ) :
    content Q = 1 ∧ Integrable f Q ∧ lowerIntegral f Q = f 0 ∧ upperIntegral f Q = f 0 ∧
      ∀ (P : Grid Q) (ξ : Tagging P), taggedSum f P ξ = f 0 ∧
        lowerSum f P = f 0 ∧ upperSum f P = f 0 := by
  have hc (P : Grid Q) (c : CellIndex P) : cell P c = {0} := by
    ext x
    simp [cell, Specs.D04.C06.DarbouxIntegral.Model.cell, Specs.D04.C06.DarbouxIntegral.Model.carrier, Subsingleton.elim x 0]
  have hs (P : Grid Q) (ξ : Tagging P) : taggedSum f P ξ = f 0 ∧
      lowerSum f P = f 0 ∧ upperSum f P = f 0 := by
    have hcontent (c : CellIndex P) : cellContent P c = 1 := by
      simp [cellContent, Specs.D04.C06.DarbouxIntegral.Model.cellContent, Specs.D04.C06.DarbouxIntegral.Model.content]
    have himage (c : CellIndex P) : f '' cell P c = {f 0} := by rw [hc]; simp
    simp [taggedSum, Specs.D04.C06.DarbouxIntegral.Model.taggedSum, lowerSum, Specs.D04.C06.DarbouxIntegral.Model.lowerSum, upperSum, Specs.D04.C06.DarbouxIntegral.Model.upperSum,
      Specs.D04.C06.DarbouxIntegral.Model.cellInfimum, Specs.D04.C06.DarbouxIntegral.Model.cellSupremum, himage, hcontent, Subsingleton.elim (↑(ξ _) : E 0) 0]
  have hl : Set.range (lowerSum f (Q := Q)) = {f 0} := by
    obtain ⟨P₀⟩ := grid_exists Q
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      obtain ⟨ξ⟩ := tags_exist P
      exact (hs P ξ).2.1
    · rintro rfl
      obtain ⟨ξ⟩ := tags_exist P₀
      exact ⟨P₀, (hs P₀ ξ).2.1⟩
  have hu : Set.range (upperSum f (Q := Q)) = {f 0} := by
    obtain ⟨P₀⟩ := grid_exists Q
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      obtain ⟨ξ⟩ := tags_exist P
      exact (hs P ξ).2.2
    · rintro rfl
      obtain ⟨ξ⟩ := tags_exist P₀
      exact ⟨P₀, (hs P₀ ξ).2.2⟩
  have hli : lowerIntegral f Q = f 0 := by change sSup _ = _; rw [hl, csSup_singleton]
  have hui : upperIntegral f Q = f 0 := by change sInf _ = _; rw [hu, csInf_singleton]
  have hb : Bounded f Q := by
    have himage : f '' carrier Q = {f 0} := by
      have hq : carrier Q = {0} := by ext x; simp [carrier, Specs.D04.C06.DarbouxIntegral.Model.carrier, Subsingleton.elim x 0]
      rw [hq]; simp
    exact ⟨by rw [himage]; exact bddBelow_singleton, by rw [himage]; exact bddAbove_singleton⟩
  exact ⟨by simp [content, Specs.D04.C06.DarbouxIntegral.Model.content], ⟨hb, hli.trans hui.symm⟩, hli, hui, hs⟩

def commonRefinement {Q : Box n} (P R : Grid Q) : Grid Q :=
  fun i => Classical.choose (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i))

theorem common_refinement {Q : Box n} (P R : Grid Q) :
    ∃ T : Grid Q, Refines T P ∧ Refines T R :=
  ⟨commonRefinement P R,
   (fun i => (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i)).choose_spec.2.1),
   (fun i => (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i)).choose_spec.2.2)⟩

/-- A strictly positive fine interval cannot lie in two distinct coarse cells. -/
theorem containing_interval_unique {a b : ℝ}
    (P R : SingleVariableAnalysis.Riemann.Partition a b) (j : Fin R.n)
    (i k : Fin P.n)
    (hi : SingleVariableAnalysis.Riemann.cell R j ⊆ SingleVariableAnalysis.Riemann.cell P i)
    (hk : SingleVariableAnalysis.Riemann.cell R j ⊆ SingleVariableAnalysis.Riemann.cell P k) :
    i = k := by
  have hlo : R.point j.castSucc ∈ SingleVariableAnalysis.Riemann.cell R j :=
    ⟨le_rfl, (R.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩
  have hhi : R.point j.succ ∈ SingleVariableAnalysis.Riemann.cell R j :=
    ⟨(R.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩
  apply SingleVariableAnalysis.Riemann.Step.open_cells_disjoint P i k
    (x := (R.point j.castSucc + R.point j.succ) / 2)
  · constructor <;> linarith [(hi hlo).1, (hi hhi).2,
      R.strictMono (Fin.castSucc_lt_succ (i := j))]
  · constructor <;> linarith [(hk hlo).1, (hk hhi).2,
      R.strictMono (Fin.castSucc_lt_succ (i := j))]

/-- A finite tensor sum of the coordinate cell lengths. -/
def weightedGridSum {m : ℕ} {a b : Fin m → ℝ}
    (P : ∀ i, SingleVariableAnalysis.Riemann.Partition (a i) (b i))
    (w : (∀ i, Fin (P i).n) → ℝ) : ℝ :=
  ∑ c, w c * ∏ i, SingleVariableAnalysis.Riemann.cellLength (P i) (c i)

theorem weightedGridSum_cons {m : ℕ} {a b : Fin (m + 1) → ℝ}
    (P : ∀ i, SingleVariableAnalysis.Riemann.Partition (a i) (b i))
    (w : (∀ i, Fin (P i).n) → ℝ) :
    weightedGridSum P w = ∑ j : Fin (P 0).n,
      weightedGridSum (fun i => P i.succ) (fun d => w (Fin.cons j d)) *
        SingleVariableAnalysis.Riemann.cellLength (P 0) j := by
  classical
  unfold weightedGridSum
  rw [← (Fin.consEquiv (fun i => Fin (P i).n)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  change w (Fin.cons j d) * (∏ i, SingleVariableAnalysis.Riemann.cellLength (P i) (Fin.cons (α := fun i => Fin (P i).n) j d i)) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- Tensorization of the admitted scalar weighted-refinement inequality.
The hypothesis refers to actual closed-cell containment in each coordinate. -/
theorem weighted_grid_refinement_le : ∀ {m : ℕ} {a b : Fin m → ℝ}
    (P R : ∀ i, SingleVariableAnalysis.Riemann.Partition (a i) (b i))
    (_h : ∀ i, SingleVariableAnalysis.Riemann.Refines (R i) (P i))
    (wP : (∀ i, Fin (P i).n) → ℝ) (wR : (∀ i, Fin (R i).n) → ℝ),
    (∀ c d, (∀ i, SingleVariableAnalysis.Riemann.cell (R i) (d i) ⊆
      SingleVariableAnalysis.Riemann.cell (P i) (c i)) → wR d ≤ wP c) →
    weightedGridSum R wR ≤ weightedGridSum P wP := by
  intro m
  induction m with
  | zero =>
    intro a b P R h wP wR hc
    have ht := hc default default (fun i => Fin.elim0 i)
    simpa [weightedGridSum] using ht
  | succ m ih =>
    intro a b P R h wP wR hc
    let parent : Fin (R 0).n → Fin (P 0).n := fun j =>
      Classical.choose (SingleVariableAnalysis.Riemann.Step.refinement_cell_contained
        (P 0) (R 0) (h 0) j)
    have hparent (j : Fin (R 0).n) :
        SingleVariableAnalysis.Riemann.cell (R 0) j ⊆
          SingleVariableAnalysis.Riemann.cell (P 0) (parent j) :=
      Classical.choose_spec (SingleVariableAnalysis.Riemann.Step.refinement_cell_contained
        (P 0) (R 0) (h 0) j)
    rw [weightedGridSum_cons, weightedGridSum_cons]
    calc
      _ ≤ ∑ j : Fin (R 0).n,
          weightedGridSum (fun i => P i.succ) (fun c => wP (Fin.cons (parent j) c)) *
            SingleVariableAnalysis.Riemann.cellLength (R 0) j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (SingleVariableAnalysis.Riemann.cell_positive (R 0) j).le
        apply ih (fun i => P i.succ) (fun i => R i.succ) (fun i => h i.succ)
        intro c d hcd
        apply hc (Fin.cons (parent j) c) (Fin.cons j d)
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simpa using hparent j
        · simpa using hcd k
      _ ≤ _ := by
        apply SingleVariableAnalysis.Riemann.weighted_sum_refinement_le (P 0) (R 0) (h 0)
        intro i j hij
        have heq : parent j = i := containing_interval_unique (P 0) (R 0) j _ _
          (hparent j) hij
        rw [heq]

/-- Refinement of the genuine upper Darboux sums. -/
theorem upper_refinement (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P R : Grid Q) (h : Refines R P) : upperSum f R ≤ upperSum f P := by
  apply weighted_grid_refinement_le P R h (cellSupremum f P) (cellSupremum f R)
  intro c d hcd
  apply csSup_le ((cell_nonempty R d).image f)
  rintro _ ⟨x, hx, rfl⟩
  exact le_cellSupremum f hf P c (fun i => hcd i (hx i))

theorem lower_refinement (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P R : Grid Q) (h : Refines R P) : lowerSum f P ≤ lowerSum f R := by
  have hs := weighted_grid_refinement_le P R h
    (fun c => -cellInfimum f P c) (fun d => -cellInfimum f R d) (by
      intro c d hcd
      apply neg_le_neg
      apply le_csInf ((cell_nonempty R d).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact cellInfimum_le f hf P c (fun i => hcd i (hx i)))
  change (∑ c, cellInfimum f P c * ∏ i, SingleVariableAnalysis.Riemann.cellLength (P i) (c i)) ≤
    ∑ c, cellInfimum f R c * ∏ i, SingleVariableAnalysis.Riemann.cellLength (R i) (c i)
  simpa only [weightedGridSum, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] using hs

theorem lower_le_upper (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P R : Grid Q) : lowerSum f P ≤ upperSum f R := by
  obtain ⟨T, hTP, hTR⟩ := common_refinement P R
  exact (lower_refinement f hf P T hTP).trans
    ((same_grid_lower_le_upper f hf T).trans (upper_refinement f hf R T hTR))


theorem sum_ranges_finite (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    (Set.range (lowerSum f (Q := Q))).Nonempty ∧
    (Set.range (upperSum f (Q := Q))).Nonempty ∧
    BddAbove (Set.range (lowerSum f (Q := Q))) ∧
    BddBelow (Set.range (upperSum f (Q := Q))) := by
  obtain ⟨P⟩ := grid_exists Q
  refine ⟨⟨lowerSum f P, ⟨P, rfl⟩⟩, ⟨upperSum f P, ⟨P, rfl⟩⟩,
    ⟨upperSum f P, ?_⟩, ⟨lowerSum f P, ?_⟩⟩
  · rintro _ ⟨R, rfl⟩
    exact lower_le_upper f hf R P
  · rintro _ ⟨R, rfl⟩
    exact lower_le_upper f hf P R

theorem lowerIntegral_isLUB (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    IsLUB (Set.range (lowerSum f (Q := Q))) (lowerIntegral f Q) :=
  isLUB_csSup (sum_ranges_finite f Q hf).1 (sum_ranges_finite f Q hf).2.2.1

theorem upperIntegral_isGLB (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    IsGLB (Set.range (upperSum f (Q := Q))) (upperIntegral f Q) :=
  isGLB_csInf (sum_ranges_finite f Q hf).2.1 (sum_ranges_finite f Q hf).2.2.2

theorem lowerIntegral_le_upperIntegral (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    lowerIntegral f Q ≤ upperIntegral f Q := by
  apply (lowerIntegral_isLUB f Q hf).2
  rintro _ ⟨P, rfl⟩
  apply (upperIntegral_isGLB f Q hf).2
  rintro _ ⟨R, rfl⟩
  exact lower_le_upper f hf P R

theorem integral_bounds (f : E n → ℝ) (Q : Box n) (h : Integrable f Q) (P : Grid Q) :
    lowerSum f P ≤ integral f Q h ∧ integral f Q h ≤ upperSum f P := by
  refine ⟨(lowerIntegral_isLUB f Q h.1).1 ⟨P, rfl⟩, ?_⟩
  change lowerIntegral f Q ≤ _
  exact h.2.le.trans ((upperIntegral_isGLB f Q h.1).1 ⟨P, rfl⟩)

theorem integrable_iff_gap (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    Integrable f Q ↔ GapCriterion f Q := by
  constructor
  · intro hi ε hε
    obtain ⟨u, ⟨P, rfl⟩, _hu, hP⟩ := (upperIntegral_isGLB f Q hf).exists_between
      (lt_add_of_pos_right _ (half_pos hε))
    obtain ⟨l, ⟨R, rfl⟩, hR, _hl⟩ := (lowerIntegral_isLUB f Q hf).exists_between
      (sub_lt_self _ (half_pos hε))
    obtain ⟨T, hTP, hTR⟩ := common_refinement P R
    refine ⟨T, ?_⟩
    have hu := upper_refinement f hf P T hTP
    have hl := lower_refinement f hf R T hTR
    linarith [hi.2]
  · intro hg
    refine ⟨hf, le_antisymm (lowerIntegral_le_upperIntegral f Q hf) ?_⟩
    by_contra hnot
    have hp : 0 < upperIntegral f Q - lowerIntegral f Q := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨P, hP⟩ := hg _ hp
    have hl := (lowerIntegral_isLUB f Q hf).1 ⟨P, rfl⟩
    have hu := (upperIntegral_isGLB f Q hf).1 ⟨P, rfl⟩
    linarith


@[simp] theorem scalarPoint_apply (t : ℝ) (i : Fin 1) : scalarPoint t i = t := rfl
@[simp] theorem scalarPoint_coordinate (x : E 1) : scalarPoint (x 0) = x := by
  ext i
  fin_cases i
  rfl

theorem scalar_carrier_image (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b) :
    f '' carrier (intervalBox a b hab) = (fun t => f (scalarPoint t)) '' Icc a b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x 0, hx 0, congrArg f (scalarPoint_coordinate x)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨scalarPoint t, fun _ => ht, rfl⟩

theorem scalar_bounded_iff (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b) :
    Bounded f (intervalBox a b hab) ↔
      SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b := by
  change (BddBelow _ ∧ BddAbove _) ↔ (BddBelow _ ∧ BddAbove _)
  rw [scalar_carrier_image]

def scalarCellIndexEquiv {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b) :
    CellIndex (intervalGrid (hab := hab) P) ≃ Fin P.n where
  toFun c := c 0
  invFun j := fun _ => j
  left_inv c := by funext i; fin_cases i; rfl
  right_inv _ := rfl

theorem scalar_grid_surjective (a b : ℝ) (hab : a ≤ b)
    (P : Grid (intervalBox a b hab)) : P = intervalGrid (P 0) := by
  funext i
  fin_cases i
  rfl

theorem scalar_cell_image (f : E 1 → ℝ) {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b)
    (c : CellIndex (intervalGrid (hab := hab) P)) :
    f '' cell (intervalGrid (hab := hab) P) c =
      (fun t => f (scalarPoint t)) '' SingleVariableAnalysis.Riemann.cell P (c 0) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x 0, hx 0, congrArg f (scalarPoint_coordinate x)⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨scalarPoint t, ?_, rfl⟩
    intro i
    fin_cases i
    exact ht

theorem scalar_cellContent {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b)
    (c : CellIndex (intervalGrid (hab := hab) P)) :
    cellContent (intervalGrid (hab := hab) P) c =
      SingleVariableAnalysis.Riemann.cellLength P (c 0) := by
  rw [cellContent_product]
  exact Fin.prod_univ_one _

theorem scalar_lowerSum (f : E 1 → ℝ) {a b : ℝ} {hab : a ≤ b}
    (hb : SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b)
    (P : SingleVariableAnalysis.Riemann.Partition a b) :
    lowerSum f (intervalGrid (hab := hab) P) =
      SingleVariableAnalysis.Riemann.lowerSum (fun t => f (scalarPoint t)) P hb := by
  apply Fintype.sum_equiv (scalarCellIndexEquiv (hab := hab) P)
  intro c
  change cellInfimum f (intervalGrid (hab := hab) P) c * cellContent (intervalGrid (hab := hab) P) c = _
  rw [scalar_cellContent]
  change sInf _ * _ = sInf _ * _
  rw [scalar_cell_image]
  rfl

theorem scalar_upperSum (f : E 1 → ℝ) {a b : ℝ} {hab : a ≤ b}
    (hb : SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b)
    (P : SingleVariableAnalysis.Riemann.Partition a b) :
    upperSum f (intervalGrid (hab := hab) P) =
      SingleVariableAnalysis.Riemann.upperSum (fun t => f (scalarPoint t)) P hb := by
  apply Fintype.sum_equiv (scalarCellIndexEquiv (hab := hab) P)
  intro c
  change cellSupremum f (intervalGrid (hab := hab) P) c * cellContent (intervalGrid (hab := hab) P) c = _
  rw [scalar_cellContent]
  change sSup _ * _ = sSup _ * _
  rw [scalar_cell_image]
  rfl

theorem scalar_sums (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Bounded f (intervalBox a b hab)) (P : SingleVariableAnalysis.Riemann.Partition a b) :
    ∃ hb : SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b,
      lowerSum f (intervalGrid (hab := hab) P) =
        SingleVariableAnalysis.Riemann.lowerSum (fun t => f (scalarPoint t)) P hb ∧
      upperSum f (intervalGrid (hab := hab) P) =
        SingleVariableAnalysis.Riemann.upperSum (fun t => f (scalarPoint t)) P hb :=
  ⟨(scalar_bounded_iff f a b hab).mp hf, scalar_lowerSum f _ P, scalar_upperSum f _ P⟩

theorem scalar_lowerIntegral (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hb : SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b) :
    lowerIntegral f (intervalBox a b hab) =
      SingleVariableAnalysis.Riemann.lowerIntegral (fun t => f (scalarPoint t)) hab hb := by
  change sSup _ = sSup _
  congr 1
  ext y
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨P 0, ?_⟩
    exact (scalar_lowerSum f hb (P 0)).symm.trans
      (congrArg (lowerSum f) (scalar_grid_surjective a b hab P)).symm
  · rintro ⟨P, rfl⟩
    exact ⟨intervalGrid (hab := hab) P, scalar_lowerSum f hb P⟩

theorem scalar_upperIntegral (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hb : SingleVariableAnalysis.Riemann.BoundedOnInterval (fun t => f (scalarPoint t)) a b) :
    upperIntegral f (intervalBox a b hab) =
      SingleVariableAnalysis.Riemann.upperIntegral (fun t => f (scalarPoint t)) hab hb := by
  change sInf _ = sInf _
  congr 1
  ext y
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨P 0, ?_⟩
    exact (scalar_upperSum f hb (P 0)).symm.trans
      (congrArg (upperSum f) (scalar_grid_surjective a b hab P)).symm
  · rintro ⟨P, rfl⟩
    exact ⟨intervalGrid (hab := hab) P, scalar_upperSum f hb P⟩

theorem scalar_integrable_iff (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b) :
    Integrable f (intervalBox a b hab) ↔
      SingleVariableAnalysis.Riemann.RealIntegrable (fun t => f (scalarPoint t)) a b := by
  constructor
  · rintro ⟨hf, heq⟩
    have hb := (scalar_bounded_iff f a b hab).mp hf
    exact ⟨hab, hb, (scalar_lowerIntegral f a b hab hb).symm.trans
      (heq.trans (scalar_upperIntegral f a b hab hb))⟩
  · rintro ⟨_, hb, heq⟩
    exact ⟨(scalar_bounded_iff f a b hab).mpr hb,
      (scalar_lowerIntegral f a b hab hb).trans (heq.trans (scalar_upperIntegral f a b hab hb).symm)⟩

theorem scalar_integral (f : E 1 → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (Integrable f (intervalBox a b hab) ↔
      SingleVariableAnalysis.Riemann.RealIntegrable (fun t => f (scalarPoint t)) a b) ∧
    ∀ h : Integrable f (intervalBox a b hab),
      ∃ hs : SingleVariableAnalysis.Riemann.RealIntegrable (fun t => f (scalarPoint t)) a b,
        integral f (intervalBox a b hab) h =
          SingleVariableAnalysis.Riemann.realIntegral (fun t => f (scalarPoint t)) hs := by
  refine ⟨scalar_integrable_iff f a b hab, fun h => ?_⟩
  let hs := (scalar_integrable_iff f a b hab).mp h
  refine ⟨hs, ?_⟩
  exact scalar_lowerIntegral f a b hab (SingleVariableAnalysis.Riemann.RealIntegrable.bounded hs)


/-- An elementary bound used only to control Euclidean cell diameters. -/
theorem norm_le_sum_abs (x : E n) : ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  simpa only [Real.norm_eq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|)
      (fun i _ => abs_nonneg _))

theorem carrier_dist_bound (Q : Box n) {x y : E n} (hx : x ∈ carrier Q) (hy : y ∈ carrier Q) :
    dist x y ≤ ∑ i, (Q.upper i - Q.lower i) := by
  rw [dist_eq_norm]
  apply (norm_le_sum_abs (x - y)).trans
  apply Finset.sum_le_sum
  intro i _
  change |x i - y i| ≤ _
  exact abs_sub_le_iff.mpr ⟨by linarith [(hx i).2, (hy i).1],
    by linarith [(hy i).2, (hx i).1]⟩

theorem carrier_isBounded (Q : Box n) : Bornology.IsBounded (carrier Q) :=
  Metric.isBounded_iff.mpr ⟨∑ i, (Q.upper i - Q.lower i),
    fun _ hx _ hy => carrier_dist_bound Q hx hy⟩

theorem mesh_nonneg {Q : Box n} (P : Grid Q) : 0 ≤ mesh P :=
  Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem cell_diam_le_mesh {Q : Box n} (P : Grid Q) (c : CellIndex P) :
    Metric.diam (cell P c) ≤ mesh P :=
  Finset.le_sup' (s := insert 0 (Finset.univ.image (fun d => Metric.diam (cell P d)))) id
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))

theorem arbitrarily_fine (Q : Box n) (_hq : Nondegenerate Q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Grid Q, mesh P < δ := by
  let η := δ / ((n : ℝ) + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  choose P hP using (fun i => SingleVariableAnalysis.Riemann.exists_fine_partition
    (Q.ordered i) η hη)
  refine ⟨P, lt_of_le_of_lt (b := (n : ℝ) * η) ?_ ?_⟩
  · apply Finset.sup'_le
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact mul_nonneg (Nat.cast_nonneg n) hη.le
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ht
      apply Metric.diam_le_of_forall_dist_le (mul_nonneg (Nat.cast_nonneg n) hη.le)
      intro x hx y hy
      apply (carrier_dist_bound (cellBox P c) hx hy).trans
      calc
        _ ≤ ∑ _i : Fin n, η := Finset.sum_le_sum fun i _ =>
          (SingleVariableAnalysis.Riemann.cellLength_le_mesh (P i) (c i)).trans (hP i).le
        _ = (n : ℝ) * η := by simp
  · dsimp [η]
    have hp : (0 : ℝ) < n + 1 := by positivity
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hp).mpr
    nlinarith

/-- In positive-side boxes every coordinate list has a cell. -/
theorem coordinate_cells_positive {Q : Box n} (hq : Nondegenerate Q) (P : Grid Q) (i : Fin n) :
    0 < (P i).n := by
  by_contra hn
  have hn0 : (P i).n = 0 := by omega
  have heq : (0 : Fin ((P i).n + 1)) = Fin.last (P i).n := Fin.ext (by simp [hn0])
  have hab : Q.lower i = Q.upper i :=
    (P i).first.symm.trans ((congrArg (P i).point heq).trans (P i).last)
  exact (ne_of_lt (hq i)) hab

theorem coordinate_mesh_le {Q : Box n} (hq : Nondegenerate Q) (P : Grid Q) (i : Fin n) :
    SingleVariableAnalysis.Riemann.mesh (P i) ≤ mesh P := by
  classical
  apply SingleVariableAnalysis.Riemann.mesh_le _ (mesh_nonneg P)
  intro j
  let c : CellIndex P := Function.update (fun k => ⟨0, coordinate_cells_positive hq P k⟩) i j
  let x := (cellBox P c).lower
  let y : E n := WithLp.toLp 2 (Function.update (fun k => x k) i ((cellBox P c).upper i))
  have hx : x ∈ cell P c := lower_mem _
  have hy : y ∈ cell P c := by
    intro k
    by_cases hk : k = i
    · subst k
      simp only [y, Function.update_self]
      exact ⟨(cellBox P c).ordered i, le_rfl⟩
    · simpa only [y, PiLp.toLp_apply, Function.update_of_ne hk] using hx k
  have hcoord := PiLp.norm_apply_le (y - x) i
  have hlen : SingleVariableAnalysis.Riemann.cellLength (P i) j ≤ dist x y := by
    rw [dist_comm, dist_eq_norm]
    apply le_trans _ hcoord
    change _ ≤ |y i - x i|
    have hid : c i = j := Function.update_self _ _ _
    simp only [y, Function.update_self]
    change SingleVariableAnalysis.Riemann.cellLength (P i) j ≤
      |(P i).point (c i).succ - (P i).point (c i).castSucc|
    rw [hid]
    exact le_abs_self _
  exact hlen.trans ((Metric.dist_le_diam_of_mem (carrier_isBounded _) hx hy).trans
    (cell_diam_le_mesh P c))

/-- Supremum approximation chooses separate tags, without assuming maxima exist. -/
theorem exists_tag_near_supremum (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, ∀ c, cellSupremum f P c - η < f (ξ c) := by
  have hex (c : CellIndex P) : ∃ x : {x // x ∈ cell P c}, cellSupremum f P c - η < f x := by
    obtain ⟨y, ⟨x, hx, rfl⟩, hy, _⟩ :=
      (isLUB_csSup ((cell_nonempty P c).image f) (cell_image_bounded f hf P c).2).exists_between
        (sub_lt_self (cellSupremum f P c) hη)
    exact ⟨⟨x, hx⟩, hy⟩
  exact ⟨fun c => (hex c).choose, fun c => (hex c).choose_spec⟩

theorem exists_tag_near_infimum (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, ∀ c, f (ξ c) < cellInfimum f P c + η := by
  have hex (c : CellIndex P) : ∃ x : {x // x ∈ cell P c}, f x < cellInfimum f P c + η := by
    obtain ⟨y, ⟨x, hx, rfl⟩, _, hy⟩ :=
      (isGLB_csInf ((cell_nonempty P c).image f) (cell_image_bounded f hf P c).1).exists_between
        (lt_add_of_pos_right (cellInfimum f P c) hη)
    exact ⟨⟨x, hx⟩, hy⟩
  exact ⟨fun c => (hex c).choose, fun c => (hex c).choose_spec⟩

theorem exists_tag_upper_error (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, upperSum f P - taggedSum f P ξ ≤ η * content Q := by
  obtain ⟨ξ, hξ⟩ := exists_tag_near_supremum f hf P η hη
  refine ⟨ξ, ?_⟩
  change (∑ c, cellSupremum f P c * cellContent P c) -
    (∑ c, f (ξ c) * cellContent P c) ≤ _
  rw [← Finset.sum_sub_distrib, ← content_partition P, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => by
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [hξ c]) (cellContent_nonneg P c)

theorem exists_tag_lower_error (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (P : Grid Q) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, taggedSum f P ξ - lowerSum f P ≤ η * content Q := by
  obtain ⟨ξ, hξ⟩ := exists_tag_near_infimum f hf P η hη
  refine ⟨ξ, ?_⟩
  change (∑ c, f (ξ c) * cellContent P c) -
    (∑ c, cellInfimum f P c * cellContent P c) ≤ _
  rw [← Finset.sum_sub_distrib, ← content_partition P, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => by
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [hξ c]) (cellContent_nonneg P c)

theorem integrable_of_taggedIntegral (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q)
    (hq : Nondegenerate Q) (I : ℝ) (hI : HasTaggedIntegral f Q I) : Integrable f Q := by
  apply (integrable_iff_gap f Q hf).mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hI (ε / 4) (by positivity)
  obtain ⟨P, hP⟩ := arbitrarily_fine Q hq δ hδ
  let η := ε / (8 * (content Q + 1))
  have hp : 0 < 8 * (content Q + 1) := by nlinarith [content_nonneg Q]
  have hη : 0 < η := div_pos hε hp
  obtain ⟨ξ, hξ⟩ := exists_tag_upper_error f hf P η hη
  obtain ⟨ζ, hζ⟩ := exists_tag_lower_error f hf P η hη
  have hu := (abs_lt.mp (hc P ξ hP)).2
  have hl := (abs_lt.mp (hc P ζ hP)).1
  have he : η * content Q ≤ ε / 8 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [hε]
  exact ⟨P, by linarith⟩


/-- Product summation of coordinate interval lengths, in a raw coordinate family. -/
theorem weightedGridSum_const {m : ℕ} {a b : Fin m → ℝ}
    (P : ∀ i, SingleVariableAnalysis.Riemann.Partition (a i) (b i)) (C : ℝ) :
    weightedGridSum P (fun _ => C) = C * ∏ i, (b i - a i) := by
  classical
  unfold weightedGridSum
  rw [← Finset.mul_sum]
  congr 1
  have hp := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (Fin (P i).n)))
    (fun i j => SingleVariableAnalysis.Riemann.cellLength (P i) j)
  simp only [Fintype.piFinset_univ] at hp
  rw [← hp]
  apply Finset.prod_congr rfl
  intro i _
  exact SingleVariableAnalysis.Riemann.sum_cellLength (P i)

theorem partition_ordered {a b : ℝ} (P : SingleVariableAnalysis.Riemann.Partition a b) : a ≤ b :=
  P.first.symm.trans_le ((P.strictMono.monotone (Fin.zero_le (Fin.last P.n))).trans_eq P.last)

/-- A coarse bound for a coordinate marginal. Adding one to every side length
avoids division by side lengths and works also when a side vanishes. -/
theorem coordinate_weighted_bound : ∀ {m : ℕ} {a b : Fin m → ℝ}
    (P : ∀ i, SingleVariableAnalysis.Riemann.Partition (a i) (b i)) (i : Fin m)
    (g : Fin (P i).n → ℝ), (∀ j, 0 ≤ g j) →
    weightedGridSum P (fun c => g (c i)) ≤
      (∑ j, g j * SingleVariableAnalysis.Riemann.cellLength (P i) j) *
        ∏ k, (b k - a k + 1) := by
  intro m
  induction m with
  | zero => intro a b P i; exact Fin.elim0 i
  | succ m ih =>
    intro a b P i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro g hg
      rw [weightedGridSum_cons]
      simp only [Fin.cons_zero]
      simp_rw [weightedGridSum_const]
      have hs : 0 ≤ ∑ j, g j * SingleVariableAnalysis.Riemann.cellLength (P 0) j :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hg j) (SingleVariableAnalysis.Riemann.cell_positive (P 0) j).le
      have htail : (∏ k : Fin m, (b k.succ - a k.succ)) ≤
          ∏ k : Fin m, (b k.succ - a k.succ + 1) := by
        apply Finset.prod_le_prod₀
        · intro k _; exact sub_nonneg.mpr (partition_ordered (P k.succ))
        · intro k _; linarith
      have ht : 0 ≤ ∏ k : Fin m, (b k.succ - a k.succ + 1) :=
        Finset.prod_nonneg fun k _ => by linarith [partition_ordered (P k.succ)]
      have hprod : (∏ k : Fin m, (b k.succ - a k.succ)) ≤ ∏ k, (b k - a k + 1) := by
        rw [Fin.prod_univ_succ]
        exact htail.trans (by nlinarith [partition_ordered (P 0)])
      calc
        _ = (∑ j, g j * SingleVariableAnalysis.Riemann.cellLength (P 0) j) *
            ∏ k : Fin m, (b k.succ - a k.succ) := by rw [Finset.sum_mul]; congr 1; funext j; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod hs
    · intro g hg
      rw [weightedGridSum_cons]
      have hs : 0 ≤ ∑ j, g j * SingleVariableAnalysis.Riemann.cellLength (P i.succ) j :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hg j) (SingleVariableAnalysis.Riemann.cell_positive (P i.succ) j).le
      have ht : 0 ≤ ∏ k : Fin m, (b k.succ - a k.succ + 1) :=
        Finset.prod_nonneg fun k _ => by linarith [partition_ordered (P k.succ)]
      calc
        _ ≤ ∑ j : Fin (P 0).n,
            ((∑ k, g k * SingleVariableAnalysis.Riemann.cellLength (P i.succ) k) *
              ∏ k : Fin m, (b k.succ - a k.succ + 1)) *
                SingleVariableAnalysis.Riemann.cellLength (P 0) j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_right _ (SingleVariableAnalysis.Riemann.cell_positive (P 0) j).le
          simpa using ih (fun k => P k.succ) i g hg
        _ = ((∑ k, g k * SingleVariableAnalysis.Riemann.cellLength (P i.succ) k) *
              ∏ k : Fin m, (b k.succ - a k.succ + 1)) * (b 0 - a 0) := by
          rw [← Finset.mul_sum, SingleVariableAnalysis.Riemann.sum_cellLength]
        _ ≤ _ := by rw [Fin.prod_univ_succ]; nlinarith

/-- Charging fine cells to a fixed coordinate face has vanishing total content. -/
theorem face_charge_bound {Q : Box n} (hq : Nondegenerate Q) (P : Grid Q)
    (i : Fin n) (x C : ℝ) (hC : 0 ≤ C) :
    weightedGridSum P (fun c => if (P i).point (c i).castSucc < x ∧
        x < (P i).point (c i).succ then C else 0) ≤
      C * mesh P * ∏ k, (Q.upper k - Q.lower k + 1) := by
  classical
  have ht : 0 ≤ ∏ k, (Q.upper k - Q.lower k + 1) :=
    Finset.prod_nonneg fun k _ => by linarith [Q.ordered k]
  apply (coordinate_weighted_bound P i
    (fun j => if (P i).point j.castSucc < x ∧ x < (P i).point j.succ then C else 0)
    (fun j => by split <;> positivity)).trans
  have hb := SingleVariableAnalysis.Riemann.sum_crossing_point_le (P i) x C hC
  simp_rw [ite_mul, zero_mul]
  exact (mul_le_mul_of_nonneg_right hb ht).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coordinate_mesh_le hq P i) hC) ht)


/-- A fixed comparison grid controls the Darboux gaps of all grids with a small
mesh. Only cells crossing one of its finitely many coordinate faces are charged. -/
theorem gap_le_gap_add_mesh (f : E n → ℝ) {Q : Box n} (hf : Bounded f Q)
    (hq : Nondegenerate Q) (P R : Grid Q) (lo hi : ℝ)
    (hlo : ∀ x ∈ carrier Q, lo ≤ f x) (hhi : ∀ x ∈ carrier Q, f x ≤ hi)
    (hbound : lo ≤ hi) :
    upperSum f R - lowerSum f R ≤ upperSum f P - lowerSum f P +
      (∑ i, ((P i).n + 1 : ℕ) * (hi - lo) *
        ∏ k, (Q.upper k - Q.lower k + 1)) * mesh R := by
  classical
  let T := commonRefinement P R
  have hTP : Refines T P := fun i => (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i)).choose_spec.2.1
  have hTR : Refines T R := fun i => (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i)).choose_spec.2.2
  let o (S : Grid Q) (c : CellIndex S) := cellSupremum f S c - cellInfimum f S c
  let e (c : CellIndex R) := ∑ i, ∑ k : Fin ((P i).n + 1),
    if (R i).point (c i).castSucc < (P i).point k ∧ (P i).point k < (R i).point (c i).succ
      then hi - lo else 0
  have ho_nonneg (S : Grid Q) (c : CellIndex S) : 0 ≤ o S c := by
    obtain ⟨x, hx⟩ := cell_nonempty S c
    exact sub_nonneg.mpr ((cellInfimum_le f hf S c hx).trans (le_cellSupremum f hf S c hx))
  have ho_le (S : Grid Q) (c : CellIndex S) : o S c ≤ hi - lo := by
    have hu : cellSupremum f S c ≤ hi := by
      apply csSup_le ((cell_nonempty S c).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact hhi x (cell_subset S c hx)
    have hl : lo ≤ cellInfimum f S c := by
      apply le_csInf ((cell_nonempty S c).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact hlo x (cell_subset S c hx)
    exact sub_le_sub hu hl
  have he_nonneg (c : CellIndex R) : 0 ≤ e c := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by split <;> linarith
  have hcoeff (c : CellIndex R) (d : CellIndex T)
      (hcd : ∀ i, SingleVariableAnalysis.Riemann.cell (T i) (d i) ⊆
        SingleVariableAnalysis.Riemann.cell (R i) (c i)) : -o T d ≤ -o R c + e c := by
    by_cases hbad : ∃ i, ∃ k : Fin ((P i).n + 1),
        (R i).point (c i).castSucc < (P i).point k ∧ (P i).point k < (R i).point (c i).succ
    · obtain ⟨i, k, hk⟩ := hbad
      have he : hi - lo ≤ e c := by
        apply le_trans _ (Finset.single_le_sum (s := Finset.univ) (f := fun i =>
          ∑ k : Fin ((P i).n + 1), if (R i).point (c i).castSucc < (P i).point k ∧
            (P i).point k < (R i).point (c i).succ then hi - lo else 0)
          (fun i _ => Finset.sum_nonneg fun k _ => by split <;> linarith) (Finset.mem_univ i))
        have ht := Finset.single_le_sum (s := Finset.univ)
          (f := fun k : Fin ((P i).n + 1) => if (R i).point (c i).castSucc < (P i).point k ∧
            (P i).point k < (R i).point (c i).succ then hi - lo else 0)
          (fun k _ => by split <;> linarith) (Finset.mem_univ k)
        simpa only [ite_eq_left hk] using ht
      linarith [ho_nonneg T d, ho_le R c]
    · have hcells (i : Fin n) : SingleVariableAnalysis.Riemann.cell (T i) (d i) =
          SingleVariableAnalysis.Riemann.cell (R i) (c i) := by
        apply SingleVariableAnalysis.Riemann.cell_eq_of_no_inserted_interior (P i) (R i) (T i)
          (SingleVariableAnalysis.Riemann.common_refinement (P i) (R i)).choose_spec.1
          (c i) (d i) (hcd i)
        exact fun ⟨k, hk⟩ => hbad ⟨i, k, hk⟩
      have hcell : cell T d = cell R c := by
        ext x
        change (∀ i, x i ∈ SingleVariableAnalysis.Riemann.cell (T i) (d i)) ↔
          (∀ i, x i ∈ SingleVariableAnalysis.Riemann.cell (R i) (c i))
        simp_rw [hcells]
      have heq : o T d = o R c := by
        dsimp [o, cellSupremum, cellInfimum, Specs.D04.C06.DarbouxIntegral.Model.cellSupremum,
          Specs.D04.C06.DarbouxIntegral.Model.cellInfimum]
        change Specs.D04.C06.DarbouxIntegral.Model.cell T d = _ at hcell
        rw [hcell]
      linarith [he_nonneg c]
  have hw := weighted_grid_refinement_le R T hTR (fun c => -o R c + e c)
    (fun d => -o T d) hcoeff
  have ho_sum (S : Grid Q) : weightedGridSum S (o S) = upperSum f S - lowerSum f S := by
    simp only [weightedGridSum, o, sub_mul, Finset.sum_sub_distrib]
    rfl
  have hRT : upperSum f R - lowerSum f R ≤
      upperSum f T - lowerSum f T + weightedGridSum R e := by
    simp only [weightedGridSum, add_mul, neg_mul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib] at hw
    change -(weightedGridSum T (o T)) ≤ -(weightedGridSum R (o R)) + weightedGridSum R e at hw
    rw [ho_sum, ho_sum] at hw
    linarith
  have he_sum : weightedGridSum R e ≤
      (∑ i, ((P i).n + 1 : ℕ) * (hi - lo) *
        ∏ k, (Q.upper k - Q.lower k + 1)) * mesh R := by
    have hexpand : weightedGridSum R e = ∑ i, ∑ k : Fin ((P i).n + 1),
        weightedGridSum R (fun c => if (R i).point (c i).castSucc < (P i).point k ∧
          (P i).point k < (R i).point (c i).succ then hi - lo else 0) := by
      simp only [weightedGridSum, e, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    rw [hexpand, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ ∑ _k : Fin ((P i).n + 1), (hi - lo) * mesh R *
          ∏ k, (Q.upper k - Q.lower k + 1) :=
        Finset.sum_le_sum fun k _ => face_charge_bound hq R i ((P i).point k) (hi-lo) (sub_nonneg.mpr hbound)
      _ = _ := by simp; ring
  have hT_upper := upper_refinement f hf P T hTP
  have hT_lower := lower_refinement f hf P T hTP
  linarith

/-- All sufficiently fine tagged grids converge to the common Darboux value. -/
theorem tagged_forward (f : E n → ℝ) (Q : Box n) (hq : Nondegenerate Q)
    (hint : Integrable f Q) : HasTaggedIntegral f Q (integral f Q hint) := by
  intro ε hε
  obtain ⟨lo, hlo⟩ := hint.1.1
  obtain ⟨hi, hhi⟩ := hint.1.2
  have hlo' : ∀ x ∈ carrier Q, lo ≤ f x := fun x hx => hlo ⟨x, hx, rfl⟩
  have hhi' : ∀ x ∈ carrier Q, f x ≤ hi := fun x hx => hhi ⟨x, hx, rfl⟩
  have hbound : lo ≤ hi := (hlo' Q.lower (lower_mem Q)).trans (hhi' Q.lower (lower_mem Q))
  obtain ⟨P, hP⟩ := (integrable_iff_gap f Q hint.1).mp hint (ε / 2) (half_pos hε)
  let K : ℝ := ∑ i, ((P i).n + 1 : ℕ) * (hi - lo) * ∏ k, (Q.upper k - Q.lower k + 1)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hbound))
    (Finset.prod_nonneg fun k _ => by linarith [Q.ordered k])
  have hKpos : 0 < K + 1 := by linarith
  let δ := (ε / 2) / (K + 1)
  refine ⟨δ, div_pos (half_pos hε) hKpos, ?_⟩
  intro R ξ hmesh
  have herror : K * mesh R < ε / 2 := by
    calc
      _ ≤ (K+1) * mesh R := mul_le_mul_of_nonneg_right (by linarith) (mesh_nonneg R)
      _ < (K+1) * δ := mul_lt_mul_of_pos_left hmesh hKpos
      _ = ε / 2 := by dsimp [δ]; field_simp
  have hgap := gap_le_gap_add_mesh f hint.1 hq P R lo hi hlo' hhi' hbound
  change upperSum f R - lowerSum f R ≤ upperSum f P - lowerSum f P + K * mesh R at hgap
  have htag := tagged_bounds f hint.1 R ξ
  have hval := integral_bounds f Q hint R
  exact abs_lt.mpr ⟨by linarith [htag.1, hval.2], by linarith [htag.2, hval.1]⟩

theorem taggedIntegral_unique (f : E n → ℝ) (Q : Box n) (hq : Nondegenerate Q)
    {I J : ℝ} (hI : HasTaggedIntegral f Q I) (hJ : HasTaggedIntegral f Q J) : I = J := by
  by_contra hne
  have hp : 0 < |I - J| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δI, hδI, hcI⟩ := hI (|I-J| / 2) (half_pos hp)
  obtain ⟨δJ, hδJ, hcJ⟩ := hJ (|I-J| / 2) (half_pos hp)
  obtain ⟨P, hP⟩ := arbitrarily_fine Q hq (min δI δJ) (lt_min hδI hδJ)
  obtain ⟨ξ⟩ := tags_exist P
  have hi := hcI P ξ (hP.trans_le (min_le_left _ _))
  have hj := hcJ P ξ (hP.trans_le (min_le_right _ _))
  have ht := abs_sub_le I (taggedSum f P ξ) J
  rw [abs_sub_comm I (taggedSum f P ξ)] at ht
  linarith

theorem equivalent_criteria (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q)
    (hq : Nondegenerate Q) :
    (Integrable f Q ↔ GapCriterion f Q) ∧
    (Integrable f Q ↔ ∃ I, HasTaggedIntegral f Q I) ∧
    ∀ I, HasTaggedIntegral f Q I → ∃ h : Integrable f Q, I = integral f Q h := by
  refine ⟨integrable_iff_gap f Q hf, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact ⟨integral f Q h, tagged_forward f Q hq h⟩
  · rintro ⟨I, hI⟩
    exact integrable_of_taggedIntegral f Q hf hq I hI
  · intro I hI
    let h := integrable_of_taggedIntegral f Q hf hq I hI
    exact ⟨h, taggedIntegral_unique f Q hq hI (tagged_forward f Q hq h)⟩


/-- Every point of a positive-side box belongs to a closed grid cell. -/
theorem cells_cover (Q : Box n) (hq : Nondegenerate Q) (P : Grid Q) :
    carrier Q = ⋃ c, cell P c := by
  ext x
  constructor
  · intro hx
    have hex (i : Fin n) : ∃ j : Fin (P i).n, x i ∈ SingleVariableAnalysis.Riemann.cell (P i) j := by
      by_cases he : x i = Q.upper i
      · let j : Fin (P i).n := ⟨(P i).n - 1, by have := coordinate_cells_positive hq P i; omega⟩
        refine ⟨j, ?_⟩
        have hj : j.succ = Fin.last (P i).n := Fin.ext (by
          change (P i).n - 1 + 1 = (P i).n
          have := coordinate_cells_positive hq P i
          omega)
        have hu : (P i).point j.succ = Q.upper i := (congrArg (P i).point hj).trans (P i).last
        exact ⟨((P i).strictMono (Fin.castSucc_lt_succ (i := j))).le.trans_eq (hu.trans he.symm),
          (he.trans hu.symm).le⟩
      · obtain ⟨j, hj, hj'⟩ := SingleVariableAnalysis.Riemann.Step.exists_halfOpen_cell (P i)
          (hx i).1 (lt_of_le_of_ne (hx i).2 he)
        exact ⟨j, hj, hj'.le⟩
    choose c hc using hex
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  · intro hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    exact cell_subset P c hc

/-- Actual bijection of closed-cell tag choices with the scalar tags. -/
def scalarTaggingEquiv {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b) :
    Tagging (intervalGrid (hab := hab) P) ≃ SingleVariableAnalysis.Riemann.Tagging P where
  toFun ξ j := ⟨(ξ (fun _ => j)).val 0, (ξ (fun _ => j)).property 0⟩
  invFun ζ c := ⟨scalarPoint (ζ (c 0)), fun i => by fin_cases i; exact (ζ (c 0)).property⟩
  left_inv ξ := by
    funext c
    apply Subtype.ext
    have hc : (fun _ : Fin 1 => c 0) = c := (scalarCellIndexEquiv (hab := hab) P).left_inv c
    change scalarPoint ((ξ (fun _ => c 0)).val 0) = _
    rw [hc]
    exact scalarPoint_coordinate _
  right_inv ζ := by funext j; apply Subtype.ext; rfl

theorem scalar_taggedSum (f : E 1 → ℝ) {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b)
    (ζ : SingleVariableAnalysis.Riemann.Tagging P) :
    taggedSum f (intervalGrid (hab := hab) P) ((scalarTaggingEquiv P).symm ζ) =
      SingleVariableAnalysis.Riemann.taggedSum P ζ (fun t => f (scalarPoint t)) := by
  apply Fintype.sum_equiv (scalarCellIndexEquiv (hab := hab) P)
  intro c
  change f (scalarPoint (ζ (c 0))) * cellContent (intervalGrid (hab := hab) P) c = _
  rw [scalar_cellContent]
  change _ = SingleVariableAnalysis.Riemann.cellLength P (c 0) * f (scalarPoint (ζ (c 0)))
  exact mul_comm _ _

theorem scalar_cell_diam {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b)
    (c : CellIndex (intervalGrid (hab := hab) P)) :
    Metric.diam (cell (intervalGrid (hab := hab) P) c) =
      SingleVariableAnalysis.Riemann.cellLength P (c 0) := by
  let C := cellBox (intervalGrid (hab := hab) P) c
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (SingleVariableAnalysis.Riemann.cell_positive P (c 0)).le
    intro x hx y hy
    exact (carrier_dist_bound C hx hy).trans_eq (Fin.sum_univ_one _)
  · have hd : dist C.upper C.lower = SingleVariableAnalysis.Riemann.cellLength P (c 0) := by
      rw [EuclideanSpace.dist_eq]
      simp only [Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]
      exact abs_of_pos (SingleVariableAnalysis.Riemann.cell_positive P (c 0))
    rw [← hd]
    exact Metric.dist_le_diam_of_mem (carrier_isBounded C) (upper_mem C) (lower_mem C)

theorem scalar_mesh {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b) :
    mesh (intervalGrid (hab := hab) P) = SingleVariableAnalysis.Riemann.mesh P := by
  classical
  have himage : Finset.univ.image (fun c : CellIndex (intervalGrid (hab := hab) P) =>
      Metric.diam (cell (intervalGrid (hab := hab) P) c)) =
      Finset.univ.image (SingleVariableAnalysis.Riemann.cellLength P) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c 0, (scalar_cell_diam P c).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨fun _ => j, scalar_cell_diam P (fun _ => j)⟩
  dsimp only [mesh, Specs.D04.C06.DarbouxIntegral.Model.mesh,
    SingleVariableAnalysis.Riemann.mesh, SingleVariableAnalysis.Riemann.S.meshValue]
  change Finset.univ.image (fun c => Metric.diam
    (Specs.D04.C06.DarbouxIntegral.Model.cell (intervalGrid (hab := hab) P) c)) = _ at himage
  exact congrArg (fun s : Finset ℝ => (insert 0 s).sup'
    (Finset.insert_nonempty 0 s) id) himage

theorem scalar_tags_surjective {a b : ℝ} {hab : a ≤ b}
    (P : SingleVariableAnalysis.Riemann.Partition a b)
    (ξ : Tagging (intervalGrid (hab := hab) P)) :
    ∃ ζ : SingleVariableAnalysis.Riemann.Tagging P, ξ = intervalTags P ζ :=
  ⟨scalarTaggingEquiv P ξ, ((scalarTaggingEquiv P).symm_apply_apply ξ).symm⟩

theorem zero_box_unique : Subsingleton (Box 0) := by
  constructor
  intro Q R
  cases Q with
  | mk l u h =>
    cases R with
    | mk l' u' h' =>
      have hl : l = l' := Subsingleton.elim _ _
      have hu : u = u' := Subsingleton.elim _ _
      subst l'
      subst u'
      rfl

theorem scalar_box_representation (Q : Box 1) :
    Q = intervalBox (Q.lower 0) (Q.upper 0) (Q.ordered 0) := by
  cases Q with
  | mk l u h =>
    have hl := scalarPoint_coordinate l
    have hu := scalarPoint_coordinate u
    change Specs.D04.C06.DarbouxIntegral.Model.Box.mk l u h =
      Specs.D04.C06.DarbouxIntegral.Model.Box.mk (scalarPoint (l 0)) (scalarPoint (u 0)) _
    congr 1
    · exact hl.symm
    · exact hu.symm

end D04.Darboux
