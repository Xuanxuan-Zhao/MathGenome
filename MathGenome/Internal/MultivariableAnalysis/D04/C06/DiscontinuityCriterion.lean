import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DiscontinuityCriterion
import MathGenome.Internal.MultivariableAnalysis.D04.C06.NullCovers
import MathGenome.Internal.MultivariableAnalysis.D04.C01.LebesgueNumber
import Mathlib.Tactic.Linarith

/-! Riemann's criterion for the upstream Darboux integral and countable-cover
nullity. Oscillation is always relative to the closed box. The forward proof
covers grid faces separately; the reverse proof uses a Lebesgue number for
small-oscillation neighborhoods and a finite open cover of the compact bad set.
The only measure calculation is the elementary disjoint-box volume estimate
in `grid_content_le_cover`; no integral comparison theorem is used. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.DiscontinuityCriterion
open Darboux NullCovers

abbrev discontinuitySet := @Specs.D04.C06.DiscontinuityCriterion.Model.discontinuitySet
abbrev badOscillationSet := @Specs.D04.C06.DiscontinuityCriterion.Model.badOscillationSet

variable {n : ℕ} {f : E n → ℝ} {Q : Box n}

lemma difference_bound (hf : Bounded f Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ carrier Q, ∀ z ∈ carrier Q, |f y - f z| ≤ B := by
  obtain ⟨a, ha⟩ := hf.1
  obtain ⟨b, hb⟩ := hf.2
  refine ⟨b - a, ?_, ?_⟩
  · exact sub_nonneg.mpr ((ha ⟨Q.lower, lower_mem Q, rfl⟩).trans
      (hb ⟨Q.lower, lower_mem Q, rfl⟩))
  · intro y hy z hz
    apply abs_le.mpr
    constructor <;> linarith [ha ⟨y, hy, rfl⟩, hb ⟨y, hy, rfl⟩,
      ha ⟨z, hz, rfl⟩, hb ⟨z, hz, rfl⟩]

lemma local_values_bdd (hf : Bounded f Q) (x : E n) (r : ℝ) :
    BddAbove {v | ∃ y ∈ carrier Q ∩ Metric.ball x r,
      ∃ z ∈ carrier Q ∩ Metric.ball x r, v = |f y - f z|} := by
  obtain ⟨B, _, hB⟩ := difference_bound hf
  exact ⟨B, by rintro v ⟨y, hy, z, hz, rfl⟩; exact hB y hy.1 z hz.1⟩

lemma local_values_nonempty {x : E n} (hx : x ∈ carrier Q) {r : ℝ} (hr : 0 < r) :
    ({v | ∃ y ∈ carrier Q ∩ Metric.ball x r,
      ∃ z ∈ carrier Q ∩ Metric.ball x r, v = |f y - f z|} : Set ℝ).Nonempty :=
  ⟨0, x, ⟨hx, Metric.mem_ball_self hr⟩, x, ⟨hx, Metric.mem_ball_self hr⟩, by simp⟩

lemma localOscillation_nonneg (hf : Bounded f Q) {x : E n} (hx : x ∈ carrier Q)
    {r : ℝ} (hr : 0 < r) : 0 ≤ localOscillation f Q x r := by
  exact le_csSup (local_values_bdd hf x r)
    ⟨x, ⟨hx, Metric.mem_ball_self hr⟩, x, ⟨hx, Metric.mem_ball_self hr⟩, by simp⟩

lemma difference_le_localOscillation (hf : Bounded f Q) {x y z : E n} {r : ℝ}
    (hy : y ∈ carrier Q ∩ Metric.ball x r) (hz : z ∈ carrier Q ∩ Metric.ball x r) :
    |f y - f z| ≤ localOscillation f Q x r :=
  le_csSup (local_values_bdd hf x r) ⟨y, hy, z, hz, rfl⟩

lemma localOscillation_le (_hf : Bounded f Q) {x : E n} (hx : x ∈ carrier Q)
    {r : ℝ} (hr : 0 < r) {B : ℝ}
    (hB : ∀ y ∈ carrier Q ∩ Metric.ball x r,
      ∀ z ∈ carrier Q ∩ Metric.ball x r, |f y - f z| ≤ B) :
    localOscillation f Q x r ≤ B := by
  apply csSup_le (local_values_nonempty hx hr)
  rintro v ⟨y, hy, z, hz, rfl⟩
  exact hB y hy z hz

lemma oscillation_values_bdd (hf : Bounded f Q) {x : E n} (hx : x ∈ carrier Q) :
    BddBelow {v | ∃ r > 0, v = localOscillation f Q x r} :=
  ⟨0, by rintro v ⟨r, hr, rfl⟩; exact localOscillation_nonneg hf hx hr⟩

lemma oscillation_nonneg (hf : Bounded f Q) {x : E n} (hx : x ∈ carrier Q) :
    0 ≤ oscillation f Q x := by
  change 0 ≤ sInf {v | ∃ r > 0, v = localOscillation f Q x r}
  apply le_csInf (s := {v | ∃ r > 0, v = localOscillation f Q x r})
    ⟨localOscillation f Q x 1, 1, zero_lt_one, rfl⟩
  rintro v ⟨r, hr, rfl⟩
  exact localOscillation_nonneg hf hx hr

lemma oscillation_le_localOscillation (hf : Bounded f Q) {x : E n}
    (hx : x ∈ carrier Q) {r : ℝ} (hr : 0 < r) :
    oscillation f Q x ≤ localOscillation f Q x r :=
  csInf_le (oscillation_values_bdd hf hx) ⟨r, hr, rfl⟩

lemma exists_localOscillation_lt (_hf : Bounded f Q) {x : E n} (_hx : x ∈ carrier Q)
    {η : ℝ} (hη : oscillation f Q x < η) :
    ∃ r > 0, localOscillation f Q x r < η := by
  obtain ⟨v, ⟨r, hr, rfl⟩, hv⟩ := exists_lt_of_csInf_lt
    (show ({v | ∃ r > 0, v = localOscillation f Q x r} : Set ℝ).Nonempty from
      ⟨localOscillation f Q x 1, 1, zero_lt_one, rfl⟩) hη
  exact ⟨r, hr, hv⟩

theorem oscillation_eq_zero_iff (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q)
    (x : E n) (hx : x ∈ carrier Q) :
    oscillation f Q x = 0 ↔ ContinuousWithinAt f (carrier Q) x := by
  constructor
  · intro h
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨r, hr, hosc⟩ := exists_localOscillation_lt hf hx (by simpa [h] using hε)
    refine ⟨r, hr, fun y hy hyd => ?_⟩
    exact (difference_le_localOscillation hf ⟨hy, hyd⟩
      ⟨hx, Metric.mem_ball_self hr⟩).trans_lt hosc
  · intro h
    apply le_antisymm _ (oscillation_nonneg hf hx)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r, hr, hh⟩ := Metric.continuousWithinAt_iff.mp h (ε / 2) (half_pos hε)
    have hl : localOscillation f Q x r ≤ ε := by
      apply localOscillation_le hf hx hr
      intro y hy z hz
      have hy' : |f y - f x| < ε / 2 := hh hy.1 hy.2
      have hz' : |f x - f z| < ε / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using hh hz.1 hz.2
      calc
        |f y - f z| ≤ |f y - f x| + |f x - f z| := abs_sub_le _ _ _
        _ ≤ ε := by linarith
    simpa using (oscillation_le_localOscillation hf hx hr).trans hl

/-- An oscillation bound persists at nearby points, using smaller relative balls. -/
lemma nearby_oscillation_lt (hf : Bounded f Q) {x : E n} (hx : x ∈ carrier Q)
    {η : ℝ} (hη : oscillation f Q x < η) :
    ∃ δ > 0, ∀ y ∈ carrier Q, dist y x < δ → oscillation f Q y < η := by
  obtain ⟨r, hr, hosc⟩ := exists_localOscillation_lt hf hx hη
  refine ⟨r / 2, half_pos hr, fun y hy hyd => ?_⟩
  have hsub : carrier Q ∩ Metric.ball y (r / 2) ⊆ carrier Q ∩ Metric.ball x r := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzy : dist z y < r / 2 := hz.2
    exact (dist_triangle z y x).trans_lt (by linarith)
  have hle : localOscillation f Q y (r / 2) ≤ localOscillation f Q x r := by
    apply localOscillation_le hf hy (half_pos hr)
    intro z hz w hw
    exact difference_le_localOscillation hf (hsub hz) (hsub hw)
  exact ((oscillation_le_localOscillation hf hy (half_pos hr)).trans hle).trans_lt hosc

lemma badOscillationSet_closed (hf : Bounded f Q) (η : ℝ) :
    IsClosed (badOscillationSet f Q η) := by
  rw [← isOpen_compl_iff]
  apply Metric.isOpen_iff.mpr
  intro x hx
  by_cases hxQ : x ∈ carrier Q
  · have hxη : oscillation f Q x < η := lt_of_not_ge (fun h => hx ⟨hxQ, h⟩)
    obtain ⟨δ, hδ, hh⟩ := nearby_oscillation_lt hf hxQ hxη
    refine ⟨δ, hδ, ?_⟩
    intro y hy hbad
    exact (not_lt_of_ge hbad.2) (hh y hbad.1 hy)
  · obtain ⟨δ, hδ, hh⟩ := Metric.isOpen_iff.mp (isClosed_carrier Q).isOpen_compl x hxQ
    exact ⟨δ, hδ, fun y hy hbad => hh hy hbad.1⟩

theorem badOscillationSet_compact (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q)
    (η : ℝ) (_hη : 0 < η) : IsCompact (badOscillationSet f Q η) := by
  exact (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_carrier Q, carrier_isBounded Q⟩).of_isClosed_subset
      (badOscillationSet_closed hf η) (fun _ hx => hx.1)

theorem discontinuitySet_eq_iUnion (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    discontinuitySet f Q = ⋃ k : ℕ, badOscillationSet f Q (1 / (k + 1 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx, hdisc⟩
    have hp : 0 < oscillation f Q x := lt_of_le_of_ne (oscillation_nonneg hf hx)
      (fun h => hdisc ((oscillation_eq_zero_iff f Q hf x hx).mp h.symm))
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hp
    exact mem_iUnion.mpr ⟨k, hx, hk.le⟩
  · intro h
    obtain ⟨k, hx, hk⟩ := mem_iUnion.mp h
    refine ⟨hx, fun hc => ?_⟩
    have hz := (oscillation_eq_zero_iff f Q hf x hx).mpr hc
    have hp : 0 < (1 : ℝ) / (k + 1 : ℝ) := by positivity
    linarith

/-- Open coordinate cells have the same content as closed cells and are disjoint.
Only the elementary box-volume interface is used here, not an integral comparison. -/
def openCoordinateCell (P : Grid Q) (c : CellIndex P) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Ioo ((P i).point (c i).castSucc) ((P i).point (c i).succ))

lemma openCoordinateCell_volume (P : Grid Q) (c : CellIndex P) :
    MeasureTheory.volume (openCoordinateCell P c) = ENNReal.ofReal (cellContent P c) := by
  rw [openCoordinateCell, Real.volume_pi_Ioo]
  exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
    sub_nonneg.mpr ((P i).strictMono (Fin.castSucc_lt_succ (i := c i))).le).symm

lemma openCoordinateCell_disjoint (P : Grid Q) :
    Pairwise (fun c d => Disjoint (openCoordinateCell P c) (openCoordinateCell P d)) := by
  intro c d hcd
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ d i := Function.ne_iff.mp hcd
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hc : (P i).point (c i).castSucc < x i ∧ x i < (P i).point (c i).succ := hx i (mem_univ i)
  have hd : (P i).point (d i).castSucc < x i ∧ x i < (P i).point (d i).succ := hy i (mem_univ i)
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hh : (c i).succ ≤ (d i).castSucc := by simpa using hlt
    have := (P i).strictMono.monotone hh
    linarith
  · have hh : (d i).succ ≤ (c i).castSucc := by simpa using hgt
    have := (P i).strictMono.monotone hh
    linarith

lemma grid_content_le_cover (P : Grid Q) (F : Finset (CellIndex P))
    {ι : Type} [Countable ι] (R : ι → Box n)
    (hcover : ∀ c ∈ F, cell P c ⊆ ⋃ i, carrier (R i)) :
    ENNReal.ofReal (∑ c ∈ F, cellContent P c) ≤
      ∑' i, ENNReal.ofReal (content (R i)) := by
  classical
  have hdis : Pairwise (fun c d : F => Disjoint (openCoordinateCell P c) (openCoordinateCell P d)) :=
    fun c d h => openCoordinateCell_disjoint P (Subtype.val_injective.ne h)
  have hmeas : ∀ c : F, MeasurableSet (openCoordinateCell P c) :=
    fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hvol : MeasureTheory.volume (⋃ c : F, openCoordinateCell P c) =
      ENNReal.ofReal (∑ c ∈ F, cellContent P c) := by
    rw [MeasureTheory.measure_iUnion hdis hmeas, tsum_fintype]
    simp_rw [openCoordinateCell_volume]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => cellContent_nonneg _ _),
      Finset.sum_coe_sort]
  rw [← hvol]
  calc
    _ ≤ MeasureTheory.volume (⋃ i, (fun x : E n => fun j => x j) '' carrier (R i)) := by
      apply MeasureTheory.measure_mono
      intro x hx
      obtain ⟨c, hc⟩ := mem_iUnion.mp hx
      have hxc : WithLp.toLp 2 x ∈ cell P c :=
        fun i => ⟨(hc i (mem_univ i)).1.le, (hc i (mem_univ i)).2.le⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover c c.property hxc)
      exact mem_iUnion.mpr ⟨i, WithLp.toLp 2 x, hi, rfl⟩
    _ ≤ ∑' i, MeasureTheory.volume ((fun x : E n => fun j => x j) '' carrier (R i)) :=
      MeasureTheory.measure_iUnion_le _
    _ = _ := tsum_congr fun _ => coordinate_volume _

lemma cell_gap_nonneg (hf : Bounded f Q) (P : Grid Q) (c : CellIndex P) :
    0 ≤ cellSupremum f P c - cellInfimum f P c := by
  obtain ⟨x, hx⟩ := cell_nonempty P c
  exact sub_nonneg.mpr ((cellInfimum_le f hf P c hx).trans (le_cellSupremum f hf P c hx))

lemma difference_le_cell_gap (hf : Bounded f Q) (P : Grid Q) (c : CellIndex P)
    {y z : E n} (hy : y ∈ cell P c) (hz : z ∈ cell P c) :
    |f y - f z| ≤ cellSupremum f P c - cellInfimum f P c := by
  apply abs_le.mpr
  constructor <;> linarith [cellInfimum_le f hf P c hy, cellInfimum_le f hf P c hz,
    le_cellSupremum f hf P c hy, le_cellSupremum f hf P c hz]

lemma cell_gap_le (_hf : Bounded f Q) (P : Grid Q) (c : CellIndex P) {B : ℝ}
    (hB : ∀ y ∈ cell P c, ∀ z ∈ cell P c, |f y - f z| ≤ B) :
    cellSupremum f P c - cellInfimum f P c ≤ B := by
  have hh : cellSupremum f P c ≤ cellInfimum f P c + B := by
    apply csSup_le ((cell_nonempty P c).image f)
    rintro _ ⟨y, hy, rfl⟩
    have hl : f y - B ≤ cellInfimum f P c := by
      apply le_csInf ((cell_nonempty P c).image f)
      rintro _ ⟨z, hz, rfl⟩
      have := (abs_le.mp (hB y hy z hz)).2
      linarith
    linarith
  linarith

lemma gap_eq_sum (f : E n → ℝ) (P : Grid Q) :
    upperSum f P - lowerSum f P =
      ∑ c, (cellSupremum f P c - cellInfimum f P c) * cellContent P c := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  rfl

lemma finite_cover_join {ι κ : Type} [Finite ι] [Finite κ]
    (R : ι → Box n) (T : κ → Box n) {ε : ℝ} (hε : 0 < ε)
    (hR : (∑' i, ENNReal.ofReal (content (R i))) < ENNReal.ofReal (ε / 2))
    (hT : (∑' i, ENNReal.ofReal (content (T i))) < ENNReal.ofReal (ε / 2)) :
    (∑' i, ENNReal.ofReal (content (Sum.elim R T i))) < ENNReal.ofReal ε := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  rw [tsum_fintype, Fintype.sum_sum_type]
  rw [tsum_fintype] at hR hT
  calc
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hR hT
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

lemma badOscillationSet_contentZero_of_integrable
    (hf : Bounded f Q) (hq : Nondegenerate Q) (hI : Integrable f Q)
    {η : ℝ} (hη : 0 < η) : ContentZero (badOscillationSet f Q η) := by
  classical
  intro ε hε
  obtain ⟨P, hP⟩ := (integrable_iff_gap f Q hf).mp hI (η * (ε / 2))
    (mul_pos hη (half_pos hε))
  let F : Finset (CellIndex P) := Finset.univ.filter
    (fun c => η ≤ cellSupremum f P c - cellInfimum f P c)
  have hsum : η * (∑ c ∈ F, cellContent P c) ≤ upperSum f P - lowerSum f P := by
    rw [gap_eq_sum, Finset.mul_sum]
    apply (Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_right
      (Finset.mem_filter.mp hc).2 (cellContent_nonneg P c)).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun c _ _ => mul_nonneg (cell_gap_nonneg hf P c) (cellContent_nonneg P c))
  have hsmall : (∑ c ∈ F, cellContent P c) < ε / 2 := by nlinarith
  -- Every coordinate endpoint is included, including the exterior faces.
  let endpoints : Finset (Fin n × ℝ) := Finset.univ.image
    (fun p : Σ i : Fin n, Fin ((P i).n + 1) => (p.1, (P p.1).point p.2))
  let Z := ⋃ p ∈ endpoints, coordinateFace Q p.1 p.2
  obtain ⟨κ, hκ, T, hT, hTsum⟩ := finite_faces_contentZero Q endpoints (ε / 2) (half_pos hε)
  let := hκ
  refine ⟨F ⊕ κ, inferInstance, Sum.elim (fun c : F => cellBox P c) T, ?_, ?_⟩
  · intro x hx
    have hxcover : x ∈ ⋃ c, cell P c := by rw [← cells_cover Q hq P]; exact hx.1
    obtain ⟨c, hc⟩ := mem_iUnion.mp hxcover
    by_cases hxc : x ∈ openCarrier (cellBox P c)
    -- A local oscillation bound for the cell is used only at interior points.
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_openCarrier (cellBox P c)) x hxc
      have hosc : oscillation f Q x ≤ cellSupremum f P c - cellInfimum f P c := by
        apply (oscillation_le_localOscillation hf hx.1 hr).trans
        apply localOscillation_le hf hx.1 hr
        intro y hy z hz
        exact difference_le_cell_gap hf P c
          (openCarrier_subset _ (hball hy.2)) (openCarrier_subset _ (hball hz.2))
      have hcF : c ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.trans hosc⟩
      exact mem_iUnion.mpr ⟨Sum.inl ⟨c, hcF⟩, hc⟩
    · have hxZ : x ∈ Z := by
        have hnot : ¬ ∀ i, (cellBox P c).lower i < x i ∧ x i < (cellBox P c).upper i := hxc
        obtain ⟨i, hi⟩ := not_forall.mp hnot
        have heq : x i = (P i).point (c i).castSucc ∨ x i = (P i).point (c i).succ := by
          have hl := (hc i).1
          have hu := (hc i).2
          change ¬ ((P i).point (c i).castSucc < x i ∧ x i < (P i).point (c i).succ) at hi
          change (P i).point (c i).castSucc ≤ x i at hl
          change x i ≤ (P i).point (c i).succ at hu
          rcases not_and_or.mp hi with h | h
          · exact Or.inl (le_antisymm (le_of_not_gt h) hl)
          · exact Or.inr (le_antisymm hu (le_of_not_gt h))
        rcases heq with heq | heq
        · exact mem_iUnion₂.mpr ⟨(i, (P i).point (c i).castSucc),
            Finset.mem_image.mpr ⟨⟨i, (c i).castSucc⟩, Finset.mem_univ _, rfl⟩, hx.1, heq⟩
        · exact mem_iUnion₂.mpr ⟨(i, (P i).point (c i).succ),
            Finset.mem_image.mpr ⟨⟨i, (c i).succ⟩, Finset.mem_univ _, rfl⟩, hx.1, heq⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hT hxZ)
      exact mem_iUnion.mpr ⟨Sum.inr j, hj⟩
  · apply finite_cover_join _ _ hε _ hTsum
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => content_nonneg _)]
    change ENNReal.ofReal (∑ c : F, cellContent P c) < ENNReal.ofReal (ε / 2)
    rw [Finset.sum_coe_sort]
    exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hsmall

lemma carrier_compact (Q : Box n) : IsCompact (carrier Q) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_carrier Q, carrier_isBounded Q⟩

lemma integrable_of_null_discontinuitySet (hf : Bounded f Q) (hq : Nondegenerate Q)
    (hnull : Null (discontinuitySet f Q)) : Integrable f Q := by
  classical
  apply (integrable_iff_gap f Q hf).mpr
  intro ε hε
  obtain ⟨B, hB, hdiff⟩ := difference_bound hf
  let t := ε / (B + content Q + 1)
  have hden : 0 < B + content Q + 1 := by linarith [content_nonneg Q]
  have ht : 0 < t := div_pos hε hden
  have htEq : t * (B + content Q + 1) = ε := div_mul_cancel₀ _ hden.ne'
  have hbad : Null (badOscillationSet f Q t) := by
    apply null_mono _ hnull
    rintro x ⟨hx, hxosc⟩
    refine ⟨hx, fun hc => ?_⟩
    have hz := (oscillation_eq_zero_iff f Q hf x hx).mpr hc
    linarith
  have hfinite := compact_null_contentZero _ (badOscillationSet_compact f Q hf t ht) hbad
  obtain ⟨ι, hι, R, hR, hsumR⟩ := (contentZero_iff_openContentZero _).mp hfinite t ht
  let := hι
  let G := {x : E n // x ∈ carrier Q ∧ oscillation f Q x < t}
  have hex (x : G) : ∃ r > 0, localOscillation f Q x r < t :=
    exists_localOscillation_lt hf x.property.1 x.property.2
  choose r hr hrosc using hex
  let U : ι ⊕ G → Set (E n) := Sum.elim (fun i => openCarrier (R i))
    (fun x => Metric.ball x (r x))
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | inl i => exact isOpen_openCarrier _
    | inr x => exact Metric.isOpen_ball
  have hcover : carrier Q ⊆ ⋃ i, carrier Q ∩ U i := by
    intro x hx
    by_cases hxt : t ≤ oscillation f Q x
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hR ⟨hx, hxt⟩)
      exact mem_iUnion.mpr ⟨Sum.inl i, hx, hi⟩
    · exact mem_iUnion.mpr ⟨Sum.inr ⟨x, hx, lt_of_not_ge hxt⟩, hx,
        Metric.mem_ball_self (hr _)⟩
  obtain ⟨δ, hδ, hsmall⟩ := D04.lebesgue_number (carrier Q) (fun i => carrier Q ∩ U i)
    ((compact_iff_isCompact _).mpr (carrier_compact Q))
    (fun i => (relativelyOpen_iff _ _).mpr ⟨U i, hUopen i, rfl⟩) hcover
  obtain ⟨P, hP⟩ := arbitrarily_fine Q hq δ hδ
  have hcell (c : CellIndex P) : ∃ i, cell P c ⊆ U i := by
    obtain ⟨i, hi⟩ := hsmall _ (cell_nonempty P c) (cell_subset P c)
      ((cell_diam_le_mesh P c).trans_lt hP)
    exact ⟨i, fun x hx => (hi hx).2⟩
  let F : Finset (CellIndex P) := Finset.univ.filter
    (fun c => ∃ i, cell P c ⊆ openCarrier (R i))
  have hFcover : ∀ c ∈ F, cell P c ⊆ ⋃ i, carrier (R i) := by
    intro c hc
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hc).2
    exact fun x hx => mem_iUnion.mpr ⟨i, openCarrier_subset _ (hi hx)⟩
  have hFsum : (∑ c ∈ F, cellContent P c) < t := by
    have hh := (grid_content_le_cover P F R hFcover).trans_lt hsumR
    exact (ENNReal.ofReal_lt_ofReal_iff ht).mp hh
  have hgood (c : CellIndex P) (hc : c ∉ F) :
      cellSupremum f P c - cellInfimum f P c ≤ t := by
    obtain ⟨i, hi⟩ := hcell c
    cases i with
    | inl i => exact False.elim (hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi⟩))
    | inr x =>
      apply cell_gap_le hf P c
      intro y hy z hz
      apply (difference_le_localOscillation hf ⟨cell_subset P c hy, hi hy⟩
        ⟨cell_subset P c hz, hi hz⟩).trans
      exact (hrosc x).le
  have hgap : upperSum f P - lowerSum f P ≤
      B * (∑ c ∈ F, cellContent P c) + t * content Q := by
    rw [gap_eq_sum]
    calc
      _ ≤ ∑ c, ((if c ∈ F then B * cellContent P c else 0) + t * cellContent P c) := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : c ∈ F
        · rw [ite_eq_left hc]
          have hb : cellSupremum f P c - cellInfimum f P c ≤ B :=
            cell_gap_le hf P c fun y hy z hz => hdiff y (cell_subset P c hy) z (cell_subset P c hz)
          have htvol := mul_nonneg ht.le (cellContent_nonneg P c)
          have := mul_le_mul_of_nonneg_right hb (cellContent_nonneg P c)
          linarith
        · rw [ite_eq_right hc, zero_add]
          exact mul_le_mul_of_nonneg_right (hgood c hc) (cellContent_nonneg P c)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, content_partition]
        congr 1
        rw [← Finset.sum_filter, ← Finset.mul_sum]
        simp
  refine ⟨P, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hFsum.le hB
  nlinarith

lemma null_carrier_of_degenerate (Q : Box n) (hQ : Degenerate Q) : Null (carrier Q) := by
  intro ε hε
  refine ⟨Unit, inferInstance, fun _ => Q, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨(), hx⟩
  · simpa [content_degenerate Q hQ] using ENNReal.ofReal_pos.mpr hε

theorem integrable_iff_null_discontinuitySet (_hn : 0 < n)
    (f : E n → ℝ) (Q : Box n) (hf : Bounded f Q) :
    Integrable f Q ↔ Null (discontinuitySet f Q) := by
  classical
  by_cases hdeg : Degenerate Q
  · exact ⟨fun _ => null_mono (fun _ hx => hx.1) (null_carrier_of_degenerate Q hdeg),
      fun _ => integrable_degenerate f Q hf hdeg⟩
  have hq : Nondegenerate Q := by
    intro i
    exact lt_of_le_of_ne (Q.ordered i) (fun h => hdeg ⟨i, h⟩)
  constructor
  · intro hI
    rw [discontinuitySet_eq_iUnion f Q hf]
    apply null_iUnion
    intro k
    exact contentZero_null (badOscillationSet_contentZero_of_integrable hf hq hI (by positivity))
  · exact integrable_of_null_discontinuitySet hf hq

end D04.DiscontinuityCriterion
