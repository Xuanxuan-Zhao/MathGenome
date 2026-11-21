import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachRealMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BanachCircleIntegration
import Mathlib.Topology.Order.Bornology
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.Linarith

/-! The bounded-interval exhaustion in the real-line Banach measure
construction. All limits are suprema in `ℝ≥0∞`, retaining infinite values. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1

/-- A finite content on bounded subsets of the line. Its values on unbounded
sets are irrelevant. This is an intermediate interface, not an existence
assumption in the final theorem. -/
structure BoundedRealContent where
  val : Set ℝ → ℝ≥0∞
  empty : val ∅ = 0
  finite : ∀ s, Bornology.IsBounded s → val s ≠ ∞
  union : ∀ s t, Bornology.IsBounded s → Bornology.IsBounded t →
    Disjoint s t → val (s ∪ t) = val s + val t
  translate : ∀ (a : ℝ) s, Bornology.IsBounded s →
    val ((fun x => a + x) '' s) = val s
  measurable : ∀ s, Bornology.IsBounded s → NullMeasurableSet s volume →
    val s = volume s

namespace BanachReal

/-- The half-open symmetric bounded exhaustion used in the manuscript. -/
def window (n : ℕ) : Set ℝ := Ico (-(n : ℝ)) n

lemma window_bounded (n : ℕ) : Bornology.IsBounded (window n) :=
  Metric.isBounded_Ico _ _

lemma window_mono : Monotone window := by
  intro n m h
  exact Ico_subset_Ico (neg_le_neg (by exact_mod_cast h)) (by exact_mod_cast h)

lemma bounded_subset_window {s : Set ℝ} (hs : Bornology.IsBounded s) :
    ∃ n : ℕ, s ⊆ window n := by
  obtain ⟨l, hl⟩ := hs.bddBelow
  obtain ⟨u, hu⟩ := hs.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt (max (-l) u)
  refine ⟨n, fun x hx => ⟨?_, ?_⟩⟩
  · have := (le_max_left (-l) u).trans_lt hn
    linarith [hl hx]
  · exact (hu hx).trans_lt ((le_max_right (-l) u).trans_lt hn)

lemma iUnion_window : (⋃ n, window n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact mem_iUnion.mpr ⟨n, ⟨by linarith [(neg_abs_le x)],
    (le_abs_self x).trans_lt hn⟩⟩

/-- Actual bounded indicator, without a measurability restriction. -/
def circleIndicator (s : Set UnitAddCircle) : BoundedCircleFunction :=
  ⟨s.indicator (fun _ => (1 : ℝ)), memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ s <;> simp [hx]⟩⟩

@[simp] lemma circleIndicator_apply (s : Set UnitAddCircle) (x : UnitAddCircle) :
    circleIndicator s x = s.indicator (fun _ => (1 : ℝ)) x := rfl

lemma circleIndicator_nonneg (s : Set UnitAddCircle) (x : UnitAddCircle) :
    0 ≤ circleIndicator s x := by
  by_cases hx : x ∈ s <;> simp [hx]

@[simp] lemma circleIndicator_empty : circleIndicator ∅ = 0 := by
  ext x
  simp

lemma circleIndicator_union {s t : Set UnitAddCircle} (h : Disjoint s t) :
    circleIndicator (s ∪ t) = circleIndicator s + circleIndicator t := by
  ext x
  change (s ∪ t).indicator (fun _ => (1 : ℝ)) x =
    s.indicator (fun _ => (1 : ℝ)) x + t.indicator (fun _ => (1 : ℝ)) x
  have hx : ¬ (x ∈ s ∧ x ∈ t) := fun hx => Set.disjoint_left.mp h hx.1 hx.2
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp_all

/-- A circle probability content on the full power set. -/
structure CircleContent where
  val : Set UnitAddCircle → ℝ≥0∞
  empty : val ∅ = 0
  finite : ∀ s, val s ≠ ∞
  union : ∀ s t, Disjoint s t → val (s ∪ t) = val s + val t
  translate : ∀ (a : UnitAddCircle) s,
    val ((fun x => a + x) '' s) = val s
  measurable : ∀ s, NullMeasurableSet s volume → val s = volume s

/-- Taking indicators in the accepted Banach integral gives the required
circle set content. -/
lemma exists_circle_content : Nonempty CircleContent := by
  obtain ⟨I, hpos, _hnorm, hinv, hext⟩ := banach_circle_integration
  let c : Set UnitAddCircle → ℝ≥0∞ := fun s => ENNReal.ofReal (I (circleIndicator s))
  have hcpos : ∀ s, 0 ≤ I (circleIndicator s) :=
    fun s => hpos _ (circleIndicator_nonneg s)
  refine ⟨⟨c, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [c]
  · intro s
    exact ENNReal.ofReal_ne_top
  · intro s t h
    simp only [c, circleIndicator_union h, map_add]
    exact ENNReal.ofReal_add (hcpos s) (hcpos t)
  · intro a s
    have hfun : circleIndicator ((fun x => a + x) '' s) =
        circleTranslate (-a) (circleIndicator s) := by
      ext x
      change (((fun x => a + x) '' s).indicator (fun _ => (1 : ℝ))) x =
        s.indicator (fun _ => (1 : ℝ)) (-a + x)
      by_cases hx : -a + x ∈ s <;> simp [hx]
    simp only [c, hfun, hinv]
  · intro s hs
    have hf : NullMeasurable (fun x => circleIndicator s x) volume := by
      exact (aestronglyMeasurable_const.indicator₀ hs).aemeasurable.nullMeasurable
    dsimp [c]
    rw [hext _ hf]
    change ENNReal.ofReal (∫ x : UnitAddCircle, s.indicator (fun _ => (1 : ℝ)) x) = _
    rw [integral_indicator₀ hs, setIntegral_const, smul_eq_mul, mul_one]
    exact ofReal_measureReal

/-- Unit cells for an arbitrarily translated integer grid. -/
def cell (a : ℝ) (n : ℤ) : Set ℝ := Ico (a + n) (a + n + 1)

lemma mem_cell_iff (a x : ℝ) (n : ℤ) : x ∈ cell a n ↔ ⌊x - a⌋ = n := by
  rw [Int.floor_eq_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma cell_disjoint (a : ℝ) : Pairwise (fun n m : ℤ => Disjoint (cell a n) (cell a m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hnm ((mem_cell_iff a x n).mp hx |>.symm.trans ((mem_cell_iff a x m).mp hy))

lemma iUnion_cell (a : ℝ) : (⋃ n, cell a n) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x - a⌋, (mem_cell_iff _ _ _).mpr rfl⟩

/-- Only finitely many cells meet a bounded set, regardless of the grid origin. -/
lemma finite_cell_support (a : ℝ) {s : Set ℝ} (hs : Bornology.IsBounded s) :
    ∃ F : Finset ℤ, ∀ n, n ∉ F → s ∩ cell a n = ∅ := by
  classical
  obtain ⟨l, hl⟩ := hs.bddBelow
  obtain ⟨u, hu⟩ := hs.bddAbove
  refine ⟨Finset.Icc ⌊l - a⌋ ⌊u - a⌋, ?_⟩
  intro n hn
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hcell⟩
  apply hn
  rw [Finset.mem_Icc, ← (mem_cell_iff a x n).mp hcell]
  exact ⟨Int.floor_mono (sub_le_sub_right (hl hx) a),
    Int.floor_mono (sub_le_sub_right (hu hx) a)⟩

/-- On any one unit interval the quotient projection is injective. -/
lemma projection_injOn (a : ℝ) : Set.InjOn ((↑) : ℝ → UnitAddCircle) (Ico a (a + 1)) := by
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp hxy

/-- The representative in a half-open unit interval preserves Lebesgue measure.
This uses the existing Ioc quotient measure theorem and the fact that the two
endpoint conventions differ only by null singletons. -/
lemma representative_measurePreserving (a : ℝ) :
    MeasurePreserving (fun x : UnitAddCircle => (AddCircle.equivIco 1 a x : ℝ))
      volume (volume.restrict (Ico a (a + 1))) := by
  have hsub := measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (s := Ico a (a + 1)) measurableSet_Ico
  have hmk : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ico a (a + 1))) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact AddCircle.measurePreserving_mk 1 a
  have hinv : MeasurePreserving (AddCircle.measurableEquivIco 1 a).symm
      (Measure.comap Subtype.val volume) volume := hmk.comp hsub
  exact hsub.comp (MeasurePreserving.symm _ hinv)

lemma projection_measurable {s : Set ℝ} (a : ℝ) (hs : s ⊆ Ico a (a + 1))
    (hm : NullMeasurableSet s volume) :
    NullMeasurableSet (((↑) : ℝ → UnitAddCircle) '' s) volume ∧
      volume (((↑) : ℝ → UnitAddCircle) '' s) = volume s := by
  have hmp := representative_measurePreserving a
  have heq : (fun x : UnitAddCircle => (AddCircle.equivIco 1 a x : ℝ)) ⁻¹' s =
      ((↑) : ℝ → UnitAddCircle) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, AddCircle.coe_equivIco⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, AddCircle.equivIco_coe_of_mem (hs hy)] using hy
  constructor
  · rw [← heq]
    exact (hm.mono Measure.restrict_le_self).preimage hmp.quasiMeasurePreserving
  · rw [← heq, hmp.measure_preimage (hm.mono Measure.restrict_le_self),
      Measure.restrict_apply₀' measurableSet_Ico.nullMeasurableSet,
      inter_eq_left.mpr hs]

namespace CircleContent

variable (c : CircleContent)

/-- Project a real set to the circle. Additivity of this function is used only
when the quotient is injective on the union. -/
def weight (s : Set ℝ) : ℝ≥0∞ := c.val (((↑) : ℝ → UnitAddCircle) '' s)

@[simp] lemma weight_empty : c.weight ∅ = 0 := by simp [weight, c.empty]

lemma weight_union {s t : Set ℝ} (h : Disjoint s t) (a : ℝ)
    (hst : s ∪ t ⊆ Ico a (a + 1)) :
    c.weight (s ∪ t) = c.weight s + c.weight t := by
  unfold weight
  rw [image_union]
  apply c.union
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have heq := projection_injOn a (hst (Or.inl hx)) (hst (Or.inr hy)) hxy.symm
  exact Set.disjoint_left.mp h hx (heq ▸ hy)

lemma weight_translate (a : ℝ) (s : Set ℝ) :
    c.weight ((fun x => a + x) '' s) = c.weight s := by
  have heq : ((↑) : ℝ → UnitAddCircle) '' ((fun x => a + x) '' s) =
      (fun x : UnitAddCircle => (a : UnitAddCircle) + x) '' (((↑) : ℝ → UnitAddCircle) '' s) := by
    simp only [image_image, AddCircle.coe_add]
  exact (congrArg c.val heq).trans (c.translate _ _)

lemma weight_measurable {s : Set ℝ} (a : ℝ) (hs : s ⊆ Ico a (a + 1))
    (hm : NullMeasurableSet s volume) : c.weight s = volume s := by
  obtain ⟨h₁, h₂⟩ := projection_measurable a hs hm
  exact (c.measurable _ h₁).trans h₂

lemma weight_biUnion {ι : Type*} (F : Finset ι) (f : ι → Set ℝ) (a : ℝ)
    (hs : ∀ i ∈ F, f i ⊆ Ico a (a + 1))
    (hd : Pairwise (fun i j => Disjoint (f i) (f j))) :
    c.weight (⋃ i ∈ F, f i) = ∑ i ∈ F, c.weight (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    have hsF : ∀ j ∈ F, f j ⊆ Ico a (a + 1) :=
      fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hdis : Disjoint (f i) (⋃ j ∈ F, f j) := by
      apply disjoint_iUnion_right.mpr
      intro j
      apply disjoint_iUnion_right.mpr
      intro hj
      exact hd (by intro hij; exact hi (hij ▸ hj))
    have hb : f i ∪ (⋃ j ∈ F, f j) ⊆ Ico a (a + 1) :=
      union_subset (hs i (Finset.mem_insert_self _ _)) (iUnion₂_subset hsF)
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert,
      c.weight_union hdis a hb, ih hsF]

/-- The sum over all integer cells is a finite sum on every bounded set.
Using a tsum is only a convenient encoding of that finite sum. -/
def gridSum (a : ℝ) (s : Set ℝ) : ℝ≥0∞ := ∑' n : ℤ, c.weight (s ∩ cell a n)

lemma gridSum_eq_finite (a : ℝ) {s : Set ℝ} (hs : Bornology.IsBounded s) :
    ∃ F : Finset ℤ, c.gridSum a s = ∑ n ∈ F, c.weight (s ∩ cell a n) := by
  obtain ⟨F, hF⟩ := finite_cell_support a hs
  refine ⟨F, tsum_eq_sum fun n hn => ?_⟩
  rw [hF n hn, c.weight_empty]

lemma weight_partition {s : Set ℝ} (r : ℝ) (hs : s ⊆ Ico r (r + 1)) (a : ℝ) :
    c.weight s = c.gridSum a s := by
  classical
  obtain ⟨F, hF⟩ := finite_cell_support a ((Metric.isBounded_Ico _ _).subset hs)
  have heq : (⋃ n ∈ F, s ∩ cell a n) = s := by
    apply Subset.antisymm (iUnion₂_subset fun _ _ => inter_subset_left)
    intro x hx
    have hxcell : x ∈ cell a ⌊x - a⌋ := (mem_cell_iff _ _ _).mpr rfl
    have hn : ⌊x - a⌋ ∈ F := by
      by_contra hn
      have hx' : x ∈ s ∩ cell a ⌊x - a⌋ := ⟨hx, hxcell⟩
      rw [hF _ hn] at hx'
      exact hx'
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hn, hx, hxcell⟩⟩
  have hsum : c.gridSum a s = ∑ n ∈ F, c.weight (s ∩ cell a n) :=
    tsum_eq_sum fun n hn => by rw [hF n hn, c.weight_empty]
  rw [hsum, ← c.weight_biUnion F (fun n => s ∩ cell a n) r
    (fun _ _ => inter_subset_left.trans hs) (fun n m h =>
      (cell_disjoint a h).mono inter_subset_right inter_subset_right), heq]

/-- Simultaneously refine two unit-cell decompositions. The inner sums on
each side are finite because the set being refined lies in a unit cell. -/
lemma gridSum_origin (a b : ℝ) (s : Set ℝ) : c.gridSum a s = c.gridSum b s := by
  calc
    c.gridSum a s = ∑' n : ℤ, ∑' m : ℤ,
        c.weight ((s ∩ cell a n) ∩ cell b m) := by
      apply tsum_congr
      intro n
      exact c.weight_partition (a + n) inter_subset_right b
    _ = ∑' m : ℤ, ∑' n : ℤ,
        c.weight ((s ∩ cell a n) ∩ cell b m) := ENNReal.tsum_comm
    _ = c.gridSum b s := by
      apply tsum_congr
      intro m
      calc
        _ = c.gridSum a (s ∩ cell b m) := by
          apply tsum_congr
          intro n
          rw [inter_right_comm]
        _ = _ := (c.weight_partition (b + m) inter_subset_right a).symm

lemma gridSum_empty (a : ℝ) : c.gridSum a ∅ = 0 := by
  simp [gridSum]

lemma gridSum_union (a : ℝ) {s t : Set ℝ} (h : Disjoint s t) :
    c.gridSum a (s ∪ t) = c.gridSum a s + c.gridSum a t := by
  unfold gridSum
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro n
  rw [union_inter_distrib_right]
  exact c.weight_union (h.mono inter_subset_left inter_subset_left) (a + n)
    (union_subset inter_subset_right inter_subset_right)

lemma gridSum_finite (a : ℝ) {s : Set ℝ} (hs : Bornology.IsBounded s) :
    c.gridSum a s ≠ ∞ := by
  obtain ⟨F, hF⟩ := c.gridSum_eq_finite a hs
  rw [hF]
  exact ENNReal.sum_ne_top.mpr fun n _ => c.finite _

lemma gridSum_translate (a : ℝ) (s : Set ℝ) :
    c.gridSum 0 ((fun x => a + x) '' s) = c.gridSum 0 s := by
  rw [c.gridSum_origin 0 a]
  apply tsum_congr
  intro n
  have heq : ((fun x => a + x) '' s) ∩ cell a n =
      (fun x => a + x) '' (s ∩ cell 0 n) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      change _ ≤ _ ∧ _ < _ at hy
      change _ ≤ _ ∧ _ < _
      constructor <;> linarith [hy.1, hy.2]
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change _ ≤ _ ∧ _ < _ at hy ⊢
      constructor <;> linarith [hy.1, hy.2]
  rw [heq, c.weight_translate]

lemma gridSum_measurable (a : ℝ) {s : Set ℝ} (hs : NullMeasurableSet s volume) :
    c.gridSum a s = volume s := by
  have hpieces : ∀ n, c.weight (s ∩ cell a n) = volume (s ∩ cell a n) := by
    intro n
    exact c.weight_measurable (a + n) inter_subset_right
      (hs.inter measurableSet_Ico.nullMeasurableSet)
  have heq : (⋃ n, s ∩ cell a n) = s := by rw [← inter_iUnion, iUnion_cell, inter_univ]
  unfold gridSum
  simp_rw [hpieces]
  rw [← measure_iUnion₀ (μ := (volume : Measure ℝ)) (fun n m h =>
    ((cell_disjoint a h).mono inter_subset_right inter_subset_right).aedisjoint)
    (fun _ => hs.inter measurableSet_Ico.nullMeasurableSet), heq]

/-- The bounded content constructed from the finite unit-cell decomposition. -/
def boundedContent : _root_.ExpandedFA.P1.BoundedRealContent where
  val := c.gridSum 0
  empty := c.gridSum_empty 0
  finite := fun _ hs => c.gridSum_finite 0 hs
  union := fun _ _ _ _ h => c.gridSum_union 0 h
  translate := fun a s _ => c.gridSum_translate a s
  measurable := fun _ _ hs => c.gridSum_measurable 0 hs

end CircleContent

end BanachReal

open BanachReal

namespace BoundedRealContent

variable (b : _root_.ExpandedFA.P1.BoundedRealContent)

lemma mono {s t : Set ℝ} (ht : Bornology.IsBounded t) (hst : s ⊆ t) :
    b.val s ≤ b.val t := by
  have heq : s ∪ (t \ s) = t := by ext x; simp only [mem_union, mem_sdiff]; tauto
  have h := b.union s (t \ s) (ht.subset hst) (ht.subset sdiff_subset)
    disjoint_sdiff_right
  rw [heq] at h
  rw [h]
  exact le_self_add

/-- The monotone limit of the finite bounded contents. -/
def exhaustion (s : Set ℝ) : ℝ≥0∞ := ⨆ n, b.val (s ∩ window n)

lemma truncation_mono (s : Set ℝ) : Monotone (fun n => b.val (s ∩ window n)) := by
  intro n m h
  exact b.mono ((window_bounded m).subset inter_subset_right)
    (inter_subset_inter_right s (window_mono h))

lemma exhaustion_empty : b.exhaustion ∅ = 0 := by
  simp [exhaustion, b.empty]

lemma exhaustion_mono {s t : Set ℝ} (h : s ⊆ t) : b.exhaustion s ≤ b.exhaustion t := by
  apply iSup_mono
  intro n
  exact b.mono ((window_bounded n).subset inter_subset_right)
    (inter_subset_inter_left _ h)

lemma exhaustion_of_bounded {s : Set ℝ} (hs : Bornology.IsBounded s) :
    b.exhaustion s = b.val s := by
  obtain ⟨n, hn⟩ := bounded_subset_window hs
  apply le_antisymm
  · exact iSup_le fun k => b.mono hs inter_subset_left
  · have heq : s ∩ window n = s := inter_eq_left.mpr hn
    exact le_iSup_of_le n (by rw [heq])

lemma exhaustion_union {s t : Set ℝ} (h : Disjoint s t) :
    b.exhaustion (s ∪ t) = b.exhaustion s + b.exhaustion t := by
  unfold exhaustion
  rw [ENNReal.iSup_add_iSup_of_monotone (b.truncation_mono s) (b.truncation_mono t)]
  congr 1
  funext n
  rw [union_inter_distrib_right]
  exact b.union _ _ ((window_bounded n).subset inter_subset_right)
    ((window_bounded n).subset inter_subset_right)
    (h.mono inter_subset_left inter_subset_left)

/-- A bounded subset can be translated without altering its content. This
cofinality argument needs no continuity of the original finite content. -/
lemma exhaustion_translate_le (a : ℝ) (s : Set ℝ) :
    b.exhaustion ((fun x => a + x) '' s) ≤ b.exhaustion s := by
  apply iSup_le
  intro n
  let t : Set ℝ := s ∩ ((fun x => a + x) ⁻¹' window n)
  have ht : Bornology.IsBounded t := by
    have hsub : t ⊆ Ico (-(n : ℝ) - a) ((n : ℝ) - a) := by
      intro x hx
      have hx' : a + x ∈ window n := hx.2
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    exact (Metric.isBounded_Ico _ _).subset hsub
  have heq : ((fun x => a + x) '' s) ∩ window n = (fun x => a + x) '' t := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hy⟩
  rw [heq, b.translate a t ht, ← b.exhaustion_of_bounded ht]
  exact b.exhaustion_mono inter_subset_left

lemma exhaustion_translate (a : ℝ) (s : Set ℝ) :
    b.exhaustion ((fun x => a + x) '' s) = b.exhaustion s := by
  apply le_antisymm (b.exhaustion_translate_le a s)
  have h := b.exhaustion_translate_le (-a) ((fun x => a + x) '' s)
  simpa only [image_image, neg_add_cancel_left, Set.image_id'] using h

lemma exhaustion_measurable {s : Set ℝ} (hs : NullMeasurableSet s volume) :
    b.exhaustion s = volume s := by
  have heq : (⋃ n, s ∩ window n) = s := by rw [← inter_iUnion, iUnion_window, inter_univ]
  unfold exhaustion
  simp_rw [b.measurable _ ((window_bounded _).subset inter_subset_right)
    (hs.inter measurableSet_Ico.nullMeasurableSet)]
  have hmono : Monotone (fun n => s ∩ window n) :=
    fun _ _ h => inter_subset_inter_right s (window_mono h)
  rw [← hmono.measure_iUnion, heq]

/-- Assembly of the real-line extension once the finite unit-cell content
has been constructed. -/
theorem gives_banach_real_measure (b : _root_.ExpandedFA.P1.BoundedRealContent) :
    Specs.ExpandedFA.P1.BanachRealMeasure.banachRealMeasureType := by
  exact ⟨b.exhaustion, b.exhaustion_empty,
    fun _ _ h => b.exhaustion_union h, b.exhaustion_translate,
    fun _ hs => b.exhaustion_measurable hs⟩

end BoundedRealContent

/-- Banach's translation-invariant extension of Lebesgue measure to the full
power set of the real line, constructed by unit cells and bounded exhaustion. -/
theorem banach_real_measure :
    Specs.ExpandedFA.P1.BanachRealMeasure.banachRealMeasureType := by
  obtain ⟨c⟩ := BanachReal.exists_circle_content
  exact BoundedRealContent.gives_banach_real_measure c.boundedContent

end ExpandedFA.P1
