import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.NullCovers
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C01.Compactness
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.FunProp

noncomputable section
open Set Filter MeasureTheory Topology
open scoped BigOperators ENNReal
namespace D04.NullCovers
open Darboux
abbrev openCarrier := @Specs.D04.C06.NullCovers.Model.openCarrier
abbrev Null := @Specs.D04.C06.NullCovers.Model.Null
abbrev OpenNull := @Specs.D04.C06.NullCovers.Model.OpenNull
abbrev ContentZero := @Specs.D04.C06.NullCovers.Model.ContentZero
abbrev OpenContentZero := @Specs.D04.C06.NullCovers.Model.OpenContentZero
abbrev localOscillation := @Specs.D04.C06.NullCovers.Model.localOscillation
abbrev oscillation := @Specs.D04.C06.NullCovers.Model.oscillation
abbrev coordinateFace := @Specs.D04.C06.NullCovers.Model.coordinateFace
abbrev rationalUnit := Specs.D04.C06.NullCovers.Model.rationalUnit
variable {n : ℕ}

lemma openCarrier_subset (Q : Box n) : openCarrier Q ⊆ carrier Q :=
  fun _ hx i => ⟨(hx i).1.le, (hx i).2.le⟩

lemma isOpen_openCarrier (Q : Box n) : IsOpen (openCarrier Q) := by
  simp only [openCarrier, Specs.D04.C06.NullCovers.Model.openCarrier, ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
      (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)

lemma isClosed_carrier (Q : Box n) : IsClosed (carrier Q) := by
  simp only [carrier, Specs.D04.C06.DarbouxIntegral.Model.carrier, ofPred_forall, mem_Icc]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (EuclideanSpace.proj i).continuous).inter
      (isClosed_le (EuclideanSpace.proj i).continuous continuous_const)

/-- Uniform enlargement by `δ` in every coordinate. -/
def enlarge (Q : Box n) (δ : ℝ) (hδ : 0 ≤ δ) : Box n where
  lower := WithLp.toLp 2 (fun i => Q.lower i - δ)
  upper := WithLp.toLp 2 (fun i => Q.upper i + δ)
  ordered i := by simpa using (show Q.lower i - δ ≤ Q.upper i + δ by linarith [Q.ordered i])

lemma exists_open_enlargement (Q : Box n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Box n, carrier Q ⊆ openCarrier R ∧ content R < content Q + ε := by
  let f : ℝ → ℝ := fun δ => ∏ i, ((Q.upper i + δ) - (Q.lower i - δ))
  have hf : Continuous f := by unfold f; fun_prop
  have h0 : f 0 = content Q := by simp [f, content, Specs.D04.C06.DarbouxIntegral.Model.content]
  have hn : ∀ᶠ δ in 𝓝 (0 : ℝ), f δ < content Q + ε :=
    hf.continuousAt.eventually (gt_mem_nhds (by simpa [h0] using hε))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hn
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  refine ⟨enlarge Q t ht.le, ?_, ?_⟩
  · intro x hx i
    change Q.lower i - t < x i ∧ x i < Q.upper i + t
    constructor <;> linarith [(hx i).1, (hx i).2]
  · apply hd
    change |t - 0| < δ
    rw [sub_zero, abs_of_pos ht]
    exact half_lt_self hδ

/-- A countable family can be opened with any prescribed total extra budget. -/
lemma open_family {ι : Type} [Countable ι] (Q : ι → Box n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ι → Box n, (∀ i, carrier (Q i) ⊆ openCarrier (R i)) ∧
      (∑' i, ENNReal.ofReal (content (R i))) ≤
        (∑' i, ENNReal.ofReal (content (Q i))) + ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' ι
  choose R hR hcont using fun i => exists_open_enlargement (Q i)
    (show (0 : ℝ) < δ i from hδ i)
  refine ⟨R, hR, ?_⟩
  calc
    (∑' i, ENNReal.ofReal (content (R i))) ≤
        ∑' i, (ENNReal.ofReal (content (Q i)) + (δ i : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      simpa [ENNReal.ofReal_add (content_nonneg _)] using
        ENNReal.ofReal_le_ofReal (hcont i).le
    _ = (∑' i, ENNReal.ofReal (content (Q i))) + ∑' i, (δ i : ℝ≥0∞) :=
      ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl hsum.le

lemma null_iff_openNull (S : Set (E n)) : Null S ↔ OpenNull S := by
  constructor
  · intro h ε hε
    obtain ⟨ι, hι, Q, hQ, hsum⟩ := h (ε / 2) (half_pos hε)
    let := hι
    obtain ⟨R, hR, htotal⟩ := open_family Q (half_pos hε)
    refine ⟨ι, hι, R, hQ.trans (iUnion_mono hR), ?_⟩
    calc
      _ ≤ _ := htotal
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hsum
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
  · intro h ε hε
    obtain ⟨ι, hι, Q, hQ, hsum⟩ := h ε hε
    exact ⟨ι, hι, Q, hQ.trans (iUnion_mono fun i => openCarrier_subset (Q i)), hsum⟩

lemma contentZero_iff_openContentZero (S : Set (E n)) :
    ContentZero S ↔ OpenContentZero S := by
  constructor
  · intro h ε hε
    obtain ⟨ι, hι, Q, hQ, hsum⟩ := h (ε / 2) (half_pos hε)
    let := hι
    obtain ⟨R, hR, htotal⟩ := open_family Q (half_pos hε)
    refine ⟨ι, hι, R, hQ.trans (iUnion_mono hR), ?_⟩
    calc
      _ ≤ _ := htotal
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hsum
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
  · intro h ε hε
    obtain ⟨ι, hι, Q, hQ, hsum⟩ := h ε hε
    exact ⟨ι, hι, Q, hQ.trans (iUnion_mono fun i => openCarrier_subset (Q i)), hsum⟩

lemma null_mono {S T : Set (E n)} (h : S ⊆ T) (hT : Null T) : Null S := by
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := hT ε hε
  exact ⟨ι, hι, Q, h.trans hQ, hsum⟩

lemma contentZero_mono {S T : Set (E n)} (h : S ⊆ T) (hT : ContentZero T) : ContentZero S := by
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := hT ε hε
  exact ⟨ι, hι, Q, h.trans hQ, hsum⟩

lemma contentZero_null {S : Set (E n)} (h : ContentZero S) : Null S := by
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := h ε hε
  let := hι
  exact ⟨ι, inferInstance, Q, hQ, hsum⟩

lemma null_iUnion_countable {κ : Type} [Countable κ] (S : κ → Set (E n))
    (h : ∀ i, Null (S i)) : Null (⋃ i, S i) := by
  intro ε hε
  obtain ⟨δ, hδ, htotal⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' κ
  choose ι hι Q hQ hsum using fun i => h i (δ i) (hδ i)
  let : ∀ i, Countable (ι i) := hι
  refine ⟨(Σ i, ι i), inferInstance, fun p => Q p.1 p.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hQ i hi)
    exact mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩
  · calc
      _ = ∑' i, ∑' j, ENNReal.ofReal (content (Q i j)) := ENNReal.tsum_sigma' _
      _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i => by simpa using (hsum i).le
      _ < _ := htotal

lemma null_iUnion (S : ℕ → Set (E n)) (h : ∀ i, Null (S i)) : Null (⋃ i, S i) :=
  null_iUnion_countable S h

lemma compact_null_contentZero (S : Set (E n)) (hc : IsCompact S) (h : Null S) :
    ContentZero S := by
  classical
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := (null_iff_openNull S).mp h ε hε
  let := hι
  obtain ⟨F, hF⟩ := hc.elim_finite_subcover _ (fun i => isOpen_openCarrier (Q i)) hQ
  refine ⟨F, inferInstance, fun i => Q i, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hF hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, openCarrier_subset _ hxi⟩
  · calc
      _ = ∑ i ∈ F, ENNReal.ofReal (content (Q i)) := by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort F (fun i => ENNReal.ofReal (content (Q i)))
      _ ≤ ∑' i, ENNReal.ofReal (content (Q i)) := ENNReal.sum_le_tsum _
      _ < _ := hsum

lemma closure_contentZero (S : Set (E n)) (h : ContentZero S) : ContentZero (closure S) := by
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := h ε hε
  let := hι
  exact ⟨ι, hι, Q, closure_minimal hQ (isClosed_iUnion_of_finite fun i => isClosed_carrier (Q i)), hsum⟩

/-- Coordinate-space Lebesgue volume is used only through F4: box volume and
subadditivity. There is no use of a Riemann/Lebesgue integral comparison. -/
lemma coordinate_volume (Q : Box n) :
    volume ((fun x : E n => fun i => x i) '' carrier Q) = ENNReal.ofReal (content Q) := by
  have heq : (fun x : E n => fun i => x i) '' carrier Q =
      Icc (fun i => Q.lower i) (fun i => Q.upper i) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩
    · intro hx
      exact ⟨WithLp.toLp 2 x, fun i => ⟨hx.1 i, hx.2 i⟩, rfl⟩
  rw [heq, Real.volume_Icc_pi]
  exact (ENNReal.ofReal_prod_of_nonneg fun i _ => sub_nonneg.mpr (Q.ordered i)).symm

lemma box_cover_content_ennreal {ι : Type} [Countable ι] (Q : Box n) (R : ι → Box n)
    (h : carrier Q ⊆ ⋃ i, carrier (R i)) :
    ENNReal.ofReal (content Q) ≤ ∑' i, ENNReal.ofReal (content (R i)) := by
  rw [← coordinate_volume]
  calc
    _ ≤ volume ((fun x : E n => fun i => x i) '' (⋃ i, carrier (R i))) :=
      measure_mono (image_mono h)
    _ = volume (⋃ i, (fun x : E n => fun j => x j) '' carrier (R i)) := by rw [image_iUnion]
    _ ≤ ∑' i, volume ((fun x : E n => fun j => x j) '' carrier (R i)) := measure_iUnion_le _
    _ = _ := tsum_congr fun i => coordinate_volume _

lemma finite_box_cover_content (Q : Box n) {ι : Type} [Fintype ι] (R : ι → Box n)
    (h : carrier Q ⊆ ⋃ i, carrier (R i)) : content Q ≤ ∑ i, content (R i) := by
  have hh := box_cover_content_ennreal Q R h
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => content_nonneg _)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => content_nonneg _)).mp hh

lemma box_not_null (Q : Box n) (hQ : Nondegenerate Q) : ¬ Null (carrier Q) := by
  intro h
  have hp : 0 < content Q := Finset.prod_pos fun i _ => sub_pos.mpr (hQ i)
  obtain ⟨ι, hι, R, hR, hsum⟩ := h (content Q) hp
  let := hι
  exact (not_lt_of_ge (box_cover_content_ennreal Q R hR)) hsum

lemma zero_dim_point_not_null : ¬ Null ({0} : Set (E 0)) := by
  let Q : Box 0 := ⟨0, 0, fun i => Fin.elim0 i⟩
  have hQ : carrier Q = ({0} : Set (E 0)) := by
    ext x; simp [carrier, Specs.D04.C06.DarbouxIntegral.Model.carrier, Subsingleton.elim x 0]
  rw [← hQ]
  exact box_not_null Q fun i => Fin.elim0 i

/-- Replacing one coordinate by a singleton gives the containing face box. -/
def faceBox (Q : Box n) (i : Fin n) (c : ℝ) : Box n where
  lower := WithLp.toLp 2 (Function.update (fun j => Q.lower j) i c)
  upper := WithLp.toLp 2 (Function.update (fun j => Q.upper j) i c)
  ordered j := by
    by_cases hj : j = i
    · subst j; simp
    · simpa [Function.update_of_ne hj] using Q.ordered j

lemma faceBox_content (Q : Box n) (i : Fin n) (c : ℝ) : content (faceBox Q i c) = 0 := by
  apply content_degenerate
  exact ⟨i, by simp [faceBox]⟩

lemma coordinateFace_subset (Q : Box n) (i : Fin n) (c : ℝ) :
    coordinateFace Q i c ⊆ carrier (faceBox Q i c) := by
  rintro x ⟨hx, hxc⟩ j
  change x i = c at hxc
  by_cases hj : j = i
  · subst j
    change Function.update (fun j => Q.lower j) i c i ≤ x i ∧
      x i ≤ Function.update (fun j => Q.upper j) i c i
    simpa [hxc]
  · change Function.update (fun k => Q.lower k) i c j ≤ x j ∧
      x j ≤ Function.update (fun k => Q.upper k) i c j
    simpa [Function.update_of_ne hj] using hx j

lemma finite_faces_contentZero (Q : Box n) (F : Finset (Fin n × ℝ)) :
    ContentZero (⋃ p ∈ F, coordinateFace Q p.1 p.2) := by
  classical
  intro ε hε
  refine ⟨F, inferInstance, fun p => faceBox Q p.val.1 p.val.2, ?_, ?_⟩
  · rintro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, coordinateFace_subset Q p.1 p.2 hxp⟩
  · simpa [faceBox_content] using ENNReal.ofReal_pos.mpr hε

lemma singleton_contentZero (hn : 0 < n) (x : E n) : ContentZero ({x} : Set (E n)) := by
  intro ε hε
  let Q : Box n := ⟨x, x, fun _ => le_rfl⟩
  have hz : content Q = 0 := content_degenerate Q ⟨⟨0, hn⟩, rfl⟩
  refine ⟨Unit, inferInstance, fun _ => Q, ?_, ?_⟩
  · rintro y rfl
    exact mem_iUnion.mpr ⟨(), lower_mem Q⟩
  · simpa [hz] using ENNReal.ofReal_pos.mpr hε

lemma countable_null (hn : 0 < n) {S : Set (E n)} (hS : S.Countable) : Null S := by
  let := hS.to_subtype
  have h := null_iUnion_countable (fun x : S => ({x.val} : Set (E n)))
    (fun x => contentZero_null (singleton_contentZero hn x.val))
  apply null_mono (T := ⋃ x : S, ({x.val} : Set (E n))) _ h
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x, hx⟩, rfl⟩

lemma rationalUnit_bounded : Bornology.IsBounded rationalUnit := by
  apply (carrier_isBounded (intervalBox 0 1 (by norm_num))).subset
  intro x hx i
  fin_cases i
  exact hx.2

lemma rationalUnit_null : Null rationalUnit := by
  apply null_mono (T := Set.range (fun q : ℚ => scalarPoint (q : ℝ)))
  · rintro x ⟨⟨q, hq⟩, hx⟩
    refine ⟨q, ?_⟩
    ext i; fin_cases i; exact hq
  · exact countable_null (by decide) (Set.countable_range _)

lemma continuous_scalarPoint : Continuous scalarPoint :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => continuous_id)

/-- Density of the rational unit interval, with the endpoints retained. -/
lemma unitBox_subset_closure_rationalUnit :
    carrier (intervalBox 0 1 (by norm_num)) ⊆ closure rationalUnit := by
  have hd : Ioo (0 : ℝ) 1 ⊆ closure
      (Set.range (fun q : ℚ => (q : ℝ)) ∩ Ioo (0 : ℝ) 1) :=
    by simpa [inter_comm] using
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo :
        Ioo (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1 ∩ Set.range (fun q : ℚ => (q : ℝ))))
  have hi : Icc (0 : ℝ) 1 ⊆ closure
      (Set.range (fun q : ℚ => (q : ℝ)) ∩ Ioo (0 : ℝ) 1) := by
    rw [← closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact closure_minimal hd isClosed_closure
  intro x hx
  have hxx : scalarPoint (x 0) = x := by ext i; fin_cases i; rfl
  rw [← hxx]
  apply closure_mono (s := scalarPoint ''
    (Set.range (fun q : ℚ => (q : ℝ)) ∩ Ioo (0 : ℝ) 1))
  · rintro y ⟨t, ⟨ht, ht01⟩, rfl⟩
    exact ⟨ht, ht01.1.le, ht01.2.le⟩
  · exact (image_closure_subset_closure_image continuous_scalarPoint)
      ⟨x 0, hi (hx 0), rfl⟩

lemma rationalUnit_finite_cover {ι : Type} [Fintype ι] (R : ι → Box 1)
    (hR : rationalUnit ⊆ ⋃ i, carrier (R i)) : (1 : ℝ) ≤ ∑ i, content (R i) := by
  have hc : closure rationalUnit ⊆ ⋃ i, carrier (R i) :=
    closure_minimal hR (isClosed_iUnion_of_finite fun i => isClosed_carrier (R i))
  have hb := finite_box_cover_content (intervalBox 0 1 (by norm_num)) R
    (unitBox_subset_closure_rationalUnit.trans hc)
  simpa [content, Specs.D04.C06.DarbouxIntegral.Model.content,
    intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
    scalarPoint, Specs.D04.C06.DarbouxIntegral.Model.scalarPoint] using hb

lemma rationalUnit_not_contentZero : ¬ ContentZero rationalUnit := by
  intro h
  obtain ⟨ι, hι, R, hR, hsum⟩ := h 1 (by norm_num)
  let := hι
  let := Fintype.ofFinite ι
  have hb := rationalUnit_finite_cover R hR
  have he := ENNReal.ofReal_le_ofReal hb
  have heq : ENNReal.ofReal (∑ i, content (R i)) =
      ∑' i, ENNReal.ofReal (content (R i)) := by
    rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun i _ => content_nonneg _)]
  rw [heq] at he
  exact (not_lt_of_ge he) hsum

end D04.NullCovers
