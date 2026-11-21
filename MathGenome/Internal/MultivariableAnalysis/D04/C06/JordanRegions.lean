import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ExceptionalSets
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SubdivisionUniformVector
import MathGenome.Internal.MultivariableAnalysis.D04.C01.TopologicalTests

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology
open scoped BigOperators ENNReal
namespace D04.JordanRegions
open Darboux NullCovers DiscontinuityCriterion

abbrev Encloses := @Specs.D04.C06.JordanRegions.Model.Encloses
abbrev enclosingBox := @Specs.D04.C06.JordanRegions.Model.enclosingBox
abbrev zeroExtension := @Specs.D04.C06.JordanRegions.Model.zeroExtension
abbrev RegionBounded := @Specs.D04.C06.JordanRegions.Model.RegionBounded
abbrev indicator := @Specs.D04.C06.JordanRegions.Model.indicator
abbrev Jordan := @Specs.D04.C06.JordanRegions.Model.Jordan
abbrev volume := @Specs.D04.C06.JordanRegions.Model.volume
abbrev RegionIntegrable := @Specs.D04.C06.JordanRegions.Model.RegionIntegrable
abbrev regionIntegral := @Specs.D04.C06.JordanRegions.Model.regionIntegral
abbrev regionDiscontinuities := @Specs.D04.C06.JordanRegions.Model.regionDiscontinuities
abbrev VectorRegionIntegrable := @Specs.D04.C06.JordanRegions.Model.VectorRegionIntegrable
abbrev vectorRegionIntegral := @Specs.D04.C06.JordanRegions.Model.vectorRegionIntegral
abbrev OpenIntegrable := @Specs.D04.C06.JordanRegions.Model.OpenIntegrable
abbrev openIntegral := @Specs.D04.C06.JordanRegions.Model.openIntegral

variable {n : ℕ} {S T : Set (E n)} {Q : Box n}

@[simp] lemma zeroExtension_apply {V : Type} [Zero V] (f : S → V) (x : S) :
    zeroExtension f x = f x := by
  simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, x.property]

@[simp] lemma zeroExtension_of_not_mem {V : Type} [Zero V] (f : S → V)
    {x : E n} (hx : x ∉ S) : zeroExtension f x = 0 := by
  simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma encloses_subset (h : Encloses S Q) : S ⊆ carrier Q :=
  subset_closure.trans (h.trans interior_subset)

lemma encloses_bounded (h : Encloses S Q) : Bornology.IsBounded S :=
  (carrier_isBounded Q).subset (encloses_subset h)

lemma encloses_exists_iff_bounded (S : Set (E n)) :
    (∃ Q, Encloses S Q) ↔ Bornology.IsBounded S := by
  constructor
  · rintro ⟨Q, hQ⟩; exact encloses_bounded hQ
  · intro hS
    obtain ⟨R, hR, hbound⟩ := hS.closure.exists_pos_norm_lt
    let Q : Box n := ⟨WithLp.toLp 2 (fun _ => -R), WithLp.toLp 2 (fun _ => R),
      fun _ => by change -R ≤ R; linarith⟩
    refine ⟨Q, ?_⟩
    have hopen : openCarrier Q ⊆ interior (carrier Q) :=
      interior_maximal (openCarrier_subset Q) (isOpen_openCarrier Q)
    intro x hx
    apply hopen
    intro i
    have hi : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) x i
    have hb := hbound x hx
    change -R < x i ∧ x i < R
    exact ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩

lemma enclosingBox_encloses (hS : Bornology.IsBounded S) : Encloses S (enclosingBox S) := by
  have h := (encloses_exists_iff_bounded S).mpr hS
  simp only [enclosingBox, Specs.D04.C06.JordanRegions.Model.enclosingBox, dite_eq_left h]
  exact (Classical.choose_spec h)

lemma jordan_bounded (hS : Jordan S) : Bornology.IsBounded S := by
  obtain ⟨Q, hQ, _⟩ := hS
  exact encloses_bounded hQ

lemma indicator_bounded (S : Set (E n)) (Q : Box n) : Bounded (indicator S) Q := by
  apply bounded_of_abs_le (M := 1)
  intro x _
  classical
  by_cases hx : x ∈ S <;> simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx]


lemma indicator_continuousAt_iff (S : Set (E n)) (x : E n) :
    ContinuousAt (indicator S) x ↔ x ∉ frontier S := by
  classical
  constructor
  · intro hc hfr
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
    rw [frontier_eq_closure_inter_closure] at hfr
    by_cases hx : x ∈ S
    · obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hfr.2 δ hδ
      have hh := hd (show dist y x < δ by rwa [dist_comm])
      norm_num [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx, show y ∉ S from hy] at hh
    · obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hfr.1 δ hδ
      have hh := hd (show dist y x < δ by rwa [dist_comm])
      norm_num [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx, hy] at hh
  · intro hx
    exact (continuousOn_const : ContinuousOn (fun _ : E n => (1 : ℝ))
      (interior S)).continuousAt_indicator hx

lemma indicator_discontinuitySet (hQ : Encloses S Q) :
    discontinuitySet (indicator S) Q = frontier S := by
  ext x
  constructor
  · rintro ⟨_, hx⟩
    by_contra hf
    exact hx (((indicator_continuousAt_iff S x).mpr hf).continuousWithinAt)
  · intro hx
    have hi := hQ (frontier_subset_closure hx)
    refine ⟨interior_subset hi, ?_⟩
    intro hc
    exact (indicator_continuousAt_iff S x).mp
      (hc.continuousAt (mem_interior_iff_mem_nhds.mp hi)) hx

lemma frontier_compact (hS : Bornology.IsBounded S) : IsCompact (frontier S) :=
  hS.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

lemma jordan_iff_boundary (hn : 0 < n) (S : Set (E n)) (hb : Bornology.IsBounded S) :
    Jordan S ↔ ContentZero (frontier S) := by
  constructor
  · rintro ⟨Q, hQ, hi⟩
    apply compact_null_contentZero _ (frontier_compact hb)
    rw [← indicator_discontinuitySet hQ]
    exact (integrable_iff_null_discontinuitySet hn _ Q hi.1).mp hi
  · intro hS
    obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr hb
    refine ⟨Q, hQ, ?_⟩
    apply (integrable_iff_null_discontinuitySet hn _ Q (indicator_bounded S Q)).mpr
    rw [indicator_discontinuitySet hQ]
    exact contentZero_null hS

lemma zero_dim_encloses (S : Set (E 0)) (Q : Box 0) : Encloses S Q := by
  have he : carrier Q = univ := by ext x; simp [carrier,
    Specs.D04.C06.DarbouxIntegral.Model.carrier]
  intro x _
  simp [he]

lemma jordan_zero_dim (S : Set (E 0)) : Jordan S := by
  let Q : Box 0 := ⟨0, 0, fun i => Fin.elim0 i⟩
  exact ⟨Q, zero_dim_encloses S Q, (zero_dimension Q (indicator S)).2.1⟩

lemma jordan_empty (n : ℕ) : Jordan (∅ : Set (E n)) := by
  let Q : Box n := ⟨0, 0, fun _ => le_rfl⟩
  refine ⟨Q, ?_, ?_⟩
  · simp [Specs.D04.C06.JordanRegions.Model.Encloses]
  · simpa [indicator, Specs.D04.C06.JordanRegions.Model.indicator] using integrable_const Q 0

lemma contentZero_union {A B : Set (E n)} (hA : ContentZero A) (hB : ContentZero B) :
    ContentZero (A ∪ B) := by
  intro ε hε
  obtain ⟨ι, hι, R, hR, hsR⟩ := hA (ε / 2) (half_pos hε)
  obtain ⟨κ, hκ, T, hT, hsT⟩ := hB (ε / 2) (half_pos hε)
  let := hι
  let := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim R T, ?_, ?_⟩
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hR hx)
      exact mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hT hx)
      exact mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · let := Fintype.ofFinite ι
    let := Fintype.ofFinite κ
    rw [tsum_fintype, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    simp only [tsum_fintype] at hsR hsT
    calc
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hsR hsT
      _ = _ := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring

lemma jordan_union (hS : Jordan S) (hT : Jordan T) : Jordan (S ∪ T) := by
  cases n with
  | zero => exact jordan_zero_dim _
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    apply (jordan_iff_boundary hn _ ((jordan_bounded hS).union (jordan_bounded hT))).mpr
    exact contentZero_mono ((frontier_union_subset S T).trans
      (union_subset_union inter_subset_left inter_subset_right))
      (contentZero_union ((jordan_iff_boundary hn _ (jordan_bounded hS)).mp hS)
        ((jordan_iff_boundary hn _ (jordan_bounded hT)).mp hT))

lemma jordan_inter (hS : Jordan S) (hT : Jordan T) : Jordan (S ∩ T) := by
  cases n with
  | zero => exact jordan_zero_dim _
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    apply (jordan_iff_boundary hn _ ((jordan_bounded hS).subset inter_subset_left)).mpr
    exact contentZero_mono ((frontier_inter_subset S T).trans
      (union_subset_union inter_subset_left inter_subset_right))
      (contentZero_union ((jordan_iff_boundary hn _ (jordan_bounded hS)).mp hS)
        ((jordan_iff_boundary hn _ (jordan_bounded hT)).mp hT))

lemma jordan_diff (hS : Jordan S) (hT : Jordan T) : Jordan (S \ T) := by
  cases n with
  | zero => exact jordan_zero_dim _
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    apply (jordan_iff_boundary hn _ ((jordan_bounded hS).subset sdiff_subset)).mpr
    apply contentZero_mono (T := frontier S ∪ frontier T)
    · simpa only [sdiff_eq_compl_inter, frontier_compl, inter_comm] using
        (frontier_inter_subset S Tᶜ).trans (union_subset_union inter_subset_left inter_subset_right)
    · exact contentZero_union ((jordan_iff_boundary hn _ (jordan_bounded hS)).mp hS)
        ((jordan_iff_boundary hn _ (jordan_bounded hT)).mp hT)

lemma jordan_finite_union {ι : Type} (s : Finset ι) (S : ι → Set (E n))
    (hS : ∀ i ∈ s, Jordan (S i)) : Jordan (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jordan_empty n
  | @insert i s hi ih =>
    simpa using jordan_union (hS i (Finset.mem_insert_self i s))
      (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))


lemma zeroExtension_bounded {S : Set (E n)} (f : S → ℝ) (hb : RegionBounded f)
    (Q : Box n) : Bounded (zeroExtension f) Q := by
  obtain ⟨M, hM⟩ := hb
  apply bounded_of_abs_le (M := max M 0)
  intro x _
  classical
  by_cases hx : x ∈ S
  · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx,
      Real.norm_eq_abs] using (hM ⟨x, hx⟩).trans (le_max_left M 0)
  · simp [zeroExtension_of_not_mem f hx]

lemma regionBounded_of_box (f : S → ℝ) (hQ : Encloses S Q)
    (hb : Bounded (zeroExtension f) Q) : RegionBounded f := by
  obtain ⟨M, _, hM⟩ := exists_abs_bound hb
  exact ⟨M, fun x => by simpa using hM x (encloses_subset hQ x.property)⟩

lemma region_continuity_iff {V : Type} [TopologicalSpace V] [Zero V]
    (f : S → V) (x : S) :
    ContinuousWithinAt (zeroExtension f) S x ↔ ContinuousAt f x := by
  have he : S.domRestrict (zeroExtension f) = f := by funext y; exact zeroExtension_apply f y
  simpa only [he] using
    continuousWithinAt_iff_continuousAt_domRestrict (zeroExtension f) x.property

lemma zeroExtension_continuousAt_off_closure {V : Type} [TopologicalSpace V] [Zero V]
    (f : S → V) {x : E n} (hx : x ∉ closure S) : ContinuousAt (zeroExtension f) x := by
  apply (continuousAt_const : ContinuousAt (fun _ : E n => (0 : V)) x).congr
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  exact (zeroExtension_of_not_mem f (fun h => hy (subset_closure h))).symm

lemma zeroExtension_discontinuities_subset (f : S → ℝ) (Q : Box n) :
    discontinuitySet (zeroExtension f) Q ⊆ frontier S ∪ regionDiscontinuities f := by
  rintro x ⟨hxQ, hdisc⟩
  by_contra h
  have hfr : x ∉ frontier S := fun hx => h (Or.inl hx)
  have hd : x ∉ regionDiscontinuities f := fun hx => h (Or.inr hx)
  by_cases hcl : x ∈ closure S
  · have hi : x ∈ interior S := by
      by_contra hn
      exact hfr ⟨hcl, hn⟩
    have hs : x ∈ S := interior_subset hi
    have hc : ContinuousAt f ⟨x, hs⟩ := by
      by_contra hc
      exact hd ⟨hs, hc⟩
    exact hdisc (((region_continuity_iff f ⟨x, hs⟩).mpr hc).continuousAt
      (mem_interior_iff_mem_nhds.mp hi)).continuousWithinAt
  · exact hdisc (zeroExtension_continuousAt_off_closure f hcl).continuousWithinAt

lemma null_union {A B : Set (E n)} (hA : Null A) (hB : Null B) : Null (A ∪ B) := by
  have hh := null_iUnion_countable (fun b : Bool => cond b A B) (by
    intro b; cases b <;> assumption)
  apply null_mono (T := ⋃ b : Bool, cond b A B) _ hh
  rintro x (hx | hx)
  · exact mem_iUnion.mpr ⟨true, hx⟩
  · exact mem_iUnion.mpr ⟨false, hx⟩

lemma integrable_of_null_relative_discontinuities (hn : 0 < n) (hS : Jordan S)
    (f : S → ℝ) (hb : RegionBounded f) (hd : Null (regionDiscontinuities f)) :
    RegionIntegrable f := by
  have hfront := (jordan_iff_boundary hn S (jordan_bounded hS)).mp hS
  obtain ⟨Q, hQ, _⟩ := hS
  refine ⟨hb, Q, hQ, ?_⟩
  apply (integrable_iff_null_discontinuitySet hn _ Q (zeroExtension_bounded f hb Q)).mpr
  exact null_mono (zeroExtension_discontinuities_subset f Q)
    (null_union (contentZero_null hfront) hd)

lemma integrable_continuous_on_closure (hn : 0 < n) (hS : Jordan S)
    (f : closure S → ℝ) (hf : Continuous f) :
    RegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩) := by
  let g : S → ℝ := fun x => f ⟨x, subset_closure x.property⟩
  have hc : Continuous g := hf.comp (continuous_subtype_val.subtype_mk _)
  apply integrable_of_null_relative_discontinuities hn hS g
  · have hk : IsCompact (closure S) := (jordan_bounded hS).isCompact_closure
    let : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hk
    have him : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨M, hM⟩ := him.isBounded.exists_norm_le
    exact ⟨M, fun x => hM _ ⟨⟨x, subset_closure x.property⟩, rfl⟩⟩
  · apply null_mono (T := ∅) _ ExceptionalSets.null_empty
    rintro x ⟨hx, hh⟩
    exact False.elim (hh hc.continuousAt)

lemma region_integrable_zero_dim (S : Set (E 0)) (f : S → ℝ) : RegionIntegrable f := by
  let Q : Box 0 := ⟨0, 0, fun i => Fin.elim0 i⟩
  refine ⟨⟨‖zeroExtension f 0‖, ?_⟩, Q, zero_dim_encloses S Q,
    (Darboux.zero_dimension Q (zeroExtension f)).2.1⟩
  intro x
  have he : (x : E 0) = 0 := Subsingleton.elim _ _
  simp only [← he, zeroExtension_apply, le_refl]

lemma zero_dimension (S : Set (E 0)) : Jordan S ∧
    volume S = (if (0 : E 0) ∈ S then 1 else 0) ∧
    ∀ f : S → ℝ, RegionIntegrable f ∧
      regionIntegral f = (if h : (0 : E 0) ∈ S then f ⟨0, h⟩ else 0) := by
  classical
  refine ⟨jordan_zero_dim S, ?_, fun f => ⟨region_integrable_zero_dim S f, ?_⟩⟩
  · change lowerIntegral _ _ = _
    rw [(Darboux.zero_dimension (enclosingBox S) (indicator S)).2.2.1]
    simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, Set.indicator]
  · change lowerIntegral _ _ = _
    rw [(Darboux.zero_dimension (enclosingBox S) (zeroExtension f)).2.2.1]
    rfl

lemma vector_coordinate {k : ℕ} (f : S → E k) (i : Fin k) :
    vectorRegionIntegral f i = regionIntegral (fun x => f x i) := rfl


lemma box_image_congr {f g : E n → ℝ} (h : EqOn f g (carrier Q)) :
    f '' carrier Q = g '' carrier Q := by
  ext y
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, (h hx).symm⟩
  · exact ⟨x, hx, h hx⟩

lemma lowerIntegral_congr {f g : E n → ℝ} (h : EqOn f g (carrier Q)) :
    lowerIntegral f Q = lowerIntegral g Q := by
  change sSup (Set.range _) = sSup (Set.range _)
  congr 2
  funext P
  apply Finset.sum_congr rfl
  intro c _
  change sInf (f '' cell P c) * _ = sInf (g '' cell P c) * _
  exact congrArg (fun A : Set ℝ => sInf A * cellContent P c)
    (box_image_congr (Q := cellBox P c) (h.mono (cell_subset P c)))

lemma upperIntegral_congr {f g : E n → ℝ} (h : EqOn f g (carrier Q)) :
    upperIntegral f Q = upperIntegral g Q := by
  change sInf (Set.range _) = sInf (Set.range _)
  congr 2
  funext P
  apply Finset.sum_congr rfl
  intro c _
  change sSup (f '' cell P c) * _ = sSup (g '' cell P c) * _
  exact congrArg (fun A : Set ℝ => sSup A * cellContent P c)
    (box_image_congr (Q := cellBox P c) (h.mono (cell_subset P c)))

lemma integrable_congr {f g : E n → ℝ} (h : EqOn f g (carrier Q)) :
    Integrable f Q ↔ Integrable g Q := by
  change (Bounded f Q ∧ lowerIntegral f Q = upperIntegral f Q) ↔
    (Bounded g Q ∧ lowerIntegral g Q = upperIntegral g Q)
  have hb : Bounded f Q ↔ Bounded g Q := by
    change (BddBelow _ ∧ BddAbove _) ↔ (BddBelow _ ∧ BddAbove _)
    rw [box_image_congr h]
  rw [hb, lowerIntegral_congr h, upperIntegral_congr h]

lemma interior_carrier (Q : Box n) : interior (carrier Q) = openCarrier Q := by
  apply subset_antisymm
  · intro x hx i
    have hmap : MapsTo (fun x : E n => x i) (carrier Q) (Icc (Q.lower i) (Q.upper i)) :=
      fun x hx => hx i
    have h := (PiLp.isOpenMap_apply (p := (2 : ℝ≥0∞)) (fun _ : Fin n => ℝ) i).mapsTo_interior hmap hx
    simpa only [interior_Icc, mem_Ioo] using h
  · exact interior_maximal (openCarrier_subset Q) (isOpen_openCarrier Q)

lemma encloses_open (h : Encloses S Q) : closure S ⊆ openCarrier Q := by
  change closure S ⊆ interior (carrier Q) at h
  rwa [interior_carrier] at h

/-- Subdividing a larger box into three intervals in each coordinate leaves
`Q` as the central cell. Other cells miss the support lying inside `Q`. -/
def threePartition (a c d b : ℝ) (hac : a < c) (hcd : c < d) (hdb : d < b) :
    SingleVariableAnalysis.Riemann.Partition a b where
  n := 3
  point := ![a, c, d, b]
  strictMono := Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> simpa)
  first := rfl
  last := rfl


lemma integrable_eq_zero_on_box {f : E n → ℝ} (h : EqOn f (fun _ => 0) (carrier Q)) :
    ∃ hi : Integrable f Q, integral f Q hi = 0 := by
  have hi := (integrable_congr h).mpr (integrable_const Q 0)
  refine ⟨hi, ?_⟩
  exact (lowerIntegral_congr h).trans ((constant_integrals Q 0).1.trans (zero_mul _))

lemma box_integral_enlarge {f : E n → ℝ} {R : Box n} (hQ : Encloses S Q)
    (hq : Nondegenerate Q) (hl : ∀ i, R.lower i < Q.lower i)
    (hu : ∀ i, Q.upper i < R.upper i)
    (hzero : ∀ x, x ∉ S → f x = 0) (hb : Bounded f R) :
    (Integrable f R ↔ Integrable f Q) ∧
    ∀ (hR : Integrable f R) (hfQ : Integrable f Q), integral f R hR = integral f Q hfQ := by
  classical
  let P : Grid R := fun i => threePartition (R.lower i) (Q.lower i) (Q.upper i)
    (R.upper i) (hl i) (hq i) (hu i)
  let c₀ : CellIndex P := fun _ => (1 : Fin 3)
  have hmid : cellBox P c₀ = Q := by
    apply Subdivision.box_ext <;> ext i <;> rfl
  have hother (c : CellIndex P) (hc : c ≠ c₀) :
      EqOn f (fun _ => 0) (carrier (cellBox P c)) := by
    intro x hx
    apply hzero
    intro hxS
    have hxi := encloses_open hQ (subset_closure hxS)
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ (1 : Fin 3) := by
      by_contra! he
      exact hc (funext he)
    have hxc := hx i
    change ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).castSucc ≤ x i ∧
      x i ≤ ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).succ at hxc
    generalize hci : c i = j at hxc hi
    fin_cases j
    · norm_num at hxc
      exact (not_lt_of_ge hxc.2) (hxi i).1
    · exact (hi rfl).elim
    · norm_num at hxc
      exact (not_lt_of_ge hxc.1) (hxi i).2
  have hcInt (hf : Integrable f Q) (c : CellIndex P) : Integrable f (cellBox P c) := by
    by_cases hc : c = c₀
    · subst c; rwa [hmid]
    · exact (integrable_eq_zero_on_box (hother c hc)).1
  refine ⟨?_, ?_⟩
  · constructor
    · intro hf
      have hh := (subdivision_integrable f R hb P).mp hf c₀
      rwa [hmid] at hh
    · intro hf
      exact (subdivision_integrable f R hb P).mpr (hcInt hf)
  · intro hR hfQ
    rw [subdivision_integral f R P hR (hcInt hfQ)]
    rw [Finset.sum_eq_single c₀]
    · change lowerIntegral f _ = lowerIntegral f Q
      rw [hmid]
    · intro c _ hc
      exact (lowerIntegral_congr (hother c hc)).trans
        ((constant_integrals (cellBox P c) 0).1.trans (zero_mul _))
    · simp

lemma supported_box_independence {f : E n → ℝ} {R : Box n}
    (hQ : Encloses S Q) (hR : Encloses S R)
    (hzero : ∀ x, x ∉ S → f x = 0) (hb : ∀ B : Box n, Bounded f B) :
    (Integrable f Q ↔ Integrable f R) ∧
    ∀ (hfQ : Integrable f Q) (hfR : Integrable f R), integral f Q hfQ = integral f R hfR := by
  classical
  by_cases he : S.Nonempty
  · obtain ⟨x, hx⟩ := he
    have hq : Nondegenerate Q := fun i =>
      ((encloses_open hQ (subset_closure hx) i).1).trans
        ((encloses_open hQ (subset_closure hx) i).2)
    have hr : Nondegenerate R := fun i =>
      ((encloses_open hR (subset_closure hx) i).1).trans
        ((encloses_open hR (subset_closure hx) i).2)
    let B : Box n := {
      lower := WithLp.toLp 2 (fun i => min (Q.lower i) (R.lower i) - 1)
      upper := WithLp.toLp 2 (fun i => max (Q.upper i) (R.upper i) + 1)
      ordered := fun i => by
        change min (Q.lower i) (R.lower i) - 1 ≤ max (Q.upper i) (R.upper i) + 1
        linarith [min_le_left (Q.lower i) (R.lower i), le_max_left (Q.upper i) (R.upper i), Q.ordered i] }
    have hQB := box_integral_enlarge (R := B) hQ hq
      (fun i => by change min _ _ - 1 < _; linarith [min_le_left (Q.lower i) (R.lower i)])
      (fun i => by change _ < max _ _ + 1; linarith [le_max_left (Q.upper i) (R.upper i)]) hzero (hb B)
    have hRB := box_integral_enlarge (R := B) hR hr
      (fun i => by change min _ _ - 1 < _; linarith [min_le_right (Q.lower i) (R.lower i)])
      (fun i => by change _ < max _ _ + 1; linarith [le_max_right (Q.upper i) (R.upper i)]) hzero (hb B)
    refine ⟨hQB.1.symm.trans hRB.1, ?_⟩
    intro hfQ hfR
    have hB := hQB.1.mpr hfQ
    exact (hQB.2 hB hfQ).symm.trans (hRB.2 hB hfR)
  · have hz : ∀ x, f x = 0 := fun x => hzero x (fun hx => he ⟨x, hx⟩)
    have hQ0 := integrable_eq_zero_on_box (Q := Q) (fun x _ => hz x)
    have hR0 := integrable_eq_zero_on_box (Q := R) (fun x _ => hz x)
    exact ⟨⟨fun _ => hR0.1, fun _ => hQ0.1⟩, fun _ _ => hQ0.2.trans hR0.2.symm⟩


lemma integrable_iff_on_enclosing_box (f : S → ℝ) (hQ : Encloses S Q) :
    RegionIntegrable f ↔ RegionBounded f ∧ Integrable (zeroExtension f) Q := by
  constructor
  · rintro ⟨hb, R, hR, hi⟩
    exact ⟨hb, (supported_box_independence hR hQ
      (fun x hx => zeroExtension_of_not_mem f hx) (zeroExtension_bounded f hb)).1.mp hi⟩
  · rintro ⟨hb, hi⟩
    exact ⟨hb, Q, hQ, hi⟩

lemma region_integrable_iff_box (f : S → ℝ) (hQ : Encloses S Q) :
    RegionIntegrable f ↔ Integrable (zeroExtension f) Q := by
  rw [integrable_iff_on_enclosing_box f hQ]
  exact ⟨And.right, fun hi => ⟨regionBounded_of_box f hQ hi.1, hi⟩⟩

lemma integral_eq_on_enclosing_box (f : S → ℝ) (hf : RegionIntegrable f)
    (hQ : Encloses S Q) (h : Integrable (zeroExtension f) Q) :
    regionIntegral f = integral (zeroExtension f) Q h := by
  have hcan := enclosingBox_encloses (encloses_bounded hQ)
  have hi := (region_integrable_iff_box f hcan).mp hf
  exact (supported_box_independence hcan hQ
    (fun x hx => zeroExtension_of_not_mem f hx) (zeroExtension_bounded f hf.1)).2 hi h

lemma jordan_integrable_on_box (hS : Jordan S) (hQ : Encloses S Q) : Integrable (indicator S) Q := by
  obtain ⟨R, hR, hi⟩ := hS
  exact (supported_box_independence hR hQ
    (fun x hx => by simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx])
    (indicator_bounded S)).1.mp hi

lemma volume_eq_on_enclosing_box (hS : Jordan S) (hQ : Encloses S Q)
    (h : Integrable (indicator S) Q) : volume S = integral (indicator S) Q h := by
  have hcan := enclosingBox_encloses (jordan_bounded hS)
  have hi := jordan_integrable_on_box hS hcan
  exact (supported_box_independence hcan hQ
    (fun x hx => by simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx])
    (indicator_bounded S)).2 hi h

lemma volume_nonneg (hS : Jordan S) : 0 ≤ volume S := by
  have hQ := enclosingBox_encloses (jordan_bounded hS)
  have hi := jordan_integrable_on_box hS hQ
  have hh := integral_mono (integrable_const (enclosingBox S) 0) hi (by
    intro x _
    classical
    by_cases hx : x ∈ S <;> simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx])
  rw [integral_const, zero_mul] at hh
  exact hh

lemma volume_empty (n : ℕ) : volume (∅ : Set (E n)) = 0 := by
  change lowerIntegral (indicator (∅ : Set (E n))) (enclosingBox ∅) = 0
  have he : indicator (∅ : Set (E n)) = (fun _ => 0) := by
    funext x; simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator]
  rw [he]
  exact (constant_integrals _ 0).1.trans (zero_mul _)

lemma empty_region (f : (∅ : Set (E n)) → ℝ) : RegionIntegrable f ∧ regionIntegral f = 0 := by
  have hz : zeroExtension f = (fun _ => 0) := by funext x; exact zeroExtension_of_not_mem f (by simp)
  have hQ := enclosingBox_encloses (S := (∅ : Set (E n))) Bornology.isBounded_empty
  have hi : Integrable (zeroExtension f) (enclosingBox ∅) := by rw [hz]; exact integrable_const _ 0
  refine ⟨(region_integrable_iff_box f hQ).mpr hi, ?_⟩
  change lowerIntegral (zeroExtension f) (enclosingBox ∅) = 0
  rw [hz]
  exact (constant_integrals _ 0).1.trans (zero_mul _)

lemma zeroExtension_union (f : E n → ℝ) (hST : Disjoint S T) :
    zeroExtension (fun x : (S ∪ T : Set (E n)) => f x) =
      fun x => zeroExtension (fun x : S => f x) x + zeroExtension (fun x : T => f x) x := by
  funext x
  classical
  have hh : ¬ (x ∈ S ∧ x ∈ T) := fun h => Set.disjoint_left.mp hST h.1 h.2
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
    simp_all [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]

lemma integral_disjoint_union (f : E n → ℝ) (hS : Jordan S) (hT : Jordan T)
    (hST : Disjoint S T) (hfS : RegionIntegrable (fun x : S => f x))
    (hfT : RegionIntegrable (fun x : T => f x)) :
    RegionIntegrable (fun x : (S ∪ T : Set (E n)) => f x) ∧
      regionIntegral (fun x : (S ∪ T : Set (E n)) => f x) =
        regionIntegral (fun x : S => f x) + regionIntegral (fun x : T => f x) := by
  let Q := enclosingBox (S ∪ T)
  have hQ : Encloses (S ∪ T) Q := enclosingBox_encloses (jordan_bounded (jordan_union hS hT))
  have hsQ : Encloses S Q := (closure_mono subset_union_left).trans hQ
  have htQ : Encloses T Q := (closure_mono subset_union_right).trans hQ
  have hiS := (region_integrable_iff_box _ hsQ).mp hfS
  have hiT := (region_integrable_iff_box _ htQ).mp hfT
  have hsum := integrable_add hiS hiT
  have hi : Integrable (zeroExtension (fun x : (S ∪ T : Set (E n)) => f x)) Q := by
    rw [zeroExtension_union f hST]; exact hsum
  have hf := (region_integrable_iff_box _ hQ).mpr hi
  refine ⟨hf, ?_⟩
  rw [integral_eq_on_enclosing_box _ hf hQ hi,
    integral_eq_on_enclosing_box _ hfS hsQ hiS, integral_eq_on_enclosing_box _ hfT htQ hiT]
  have hval := integral_add hiS hiT hsum
  exact (congrArg (fun g => lowerIntegral g Q) (zeroExtension_union f hST)).trans hval

lemma integral_finite_disjoint_union {ι : Type} (s : Finset ι) (S : ι → Set (E n))
    (f : E n → ℝ) (hS : ∀ i ∈ s, Jordan (S i)) (hdis : (s : Set ι).PairwiseDisjoint S)
    (hf : ∀ i ∈ s, RegionIntegrable (fun x : S i => f x)) :
    RegionIntegrable (fun x : (⋃ i ∈ s, S i) => f x) ∧
    regionIntegral (fun x : (⋃ i ∈ s, S i) => f x) =
      ∑ i ∈ s, regionIntegral (fun x : S i => f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset ι), S i) = ∅ := by simp
    rw [he]
    simpa using empty_region (fun x : (∅ : Set (E n)) => f x)
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, Jordan (S j) := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hfs : ∀ j ∈ s, RegionIntegrable (fun x : S j => f x) :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hd : (s : Set ι).PairwiseDisjoint S := by
      intro j hj k hk hne
      exact hdis (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hne
    have hind := ih hs hd hfs
    have hsep : Disjoint (S i) (⋃ j ∈ s, S j) := by
      apply Set.disjoint_left.mpr
      rintro x hxi hxj
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxj
      exact Set.disjoint_left.mp
        (hdis.disjoint_of_ne (i := i) (j := j) (by simp) (by simp [hj]) (by
          intro he; apply hi; rwa [he])) hxi hxj
    have hh := integral_disjoint_union f (hS i (by simp)) (jordan_finite_union s S hs)
      hsep (hf i (by simp)) hind.1
    have he : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by simp
    rw [he, Finset.sum_insert hi]
    exact ⟨hh.1, hh.2.trans (congrArg (fun t => regionIntegral (fun x : S i => f x) + t) hind.2)⟩


lemma zero_volume_contentZero (hS : Jordan S) (hv : volume S = 0) : ContentZero S := by
  classical
  by_cases he : S.Nonempty
  · let Q := enclosingBox S
    have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
    have hi := jordan_integrable_on_box hS hQ
    have hval : upperIntegral (indicator S) Q = 0 := hi.2.symm.trans hv
    obtain ⟨x₀, hx₀⟩ := he
    have hq : Nondegenerate Q := fun i =>
      (encloses_open hQ (subset_closure hx₀) i).1.trans
        (encloses_open hQ (subset_closure hx₀) i).2
    intro ε hε
    obtain ⟨u, ⟨P, rfl⟩, _, hP⟩ := (upperIntegral_isGLB (indicator S) Q hi.1).exists_between
      (show upperIntegral (indicator S) Q < ε by rwa [hval])
    let A : Finset (CellIndex P) := Finset.univ.filter (fun c => ∃ x ∈ cell P c, x ∈ S)
    have hsup (c : CellIndex P) : 0 ≤ cellSupremum (indicator S) P c := by
      obtain ⟨x, hx⟩ := cell_nonempty P c
      have hh := le_cellSupremum (indicator S) hi.1 P c hx
      have hz : 0 ≤ indicator S x := by
        by_cases hxS : x ∈ S <;> simp [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS]
      exact hz.trans hh
    have hsum : (∑ c ∈ A, cellContent P c) ≤ upperSum (indicator S) P := by
      calc
        _ ≤ ∑ c ∈ A, cellSupremum (indicator S) P c * cellContent P c := by
          apply Finset.sum_le_sum
          intro c hc
          obtain ⟨x, hx, hxS⟩ := (Finset.mem_filter.mp hc).2
          have hh := le_cellSupremum (indicator S) hi.1 P c hx
          have hone : (1 : ℝ) ≤ cellSupremum (indicator S) P c := by
            simpa [indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS] using hh
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (cellContent_nonneg P c)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun c _ _ => mul_nonneg (hsup c) (cellContent_nonneg P c))
    refine ⟨A, inferInstance, fun c => cellBox P c, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, hc⟩ := mem_iUnion.mp ((cells_cover Q hq P) ▸ (encloses_subset hQ hx))
      exact mem_iUnion.mpr ⟨⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, x, hc, hx⟩⟩, hc⟩
    · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun c _ => content_nonneg _)]
      apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
      rw [Finset.sum_coe_sort A (fun c => content (cellBox P c))]
      exact hsum.trans_lt hP
  · have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    subst S
    intro ε hε
    exact ⟨Empty, inferInstance, Empty.elim, by simp, by simpa using ENNReal.ofReal_pos.mpr hε⟩

lemma zero_volume_region (hS : Jordan S) (hv : volume S = 0) (f : S → ℝ)
    (hb : RegionBounded f) : RegionIntegrable f ∧ regionIntegral f = 0 := by
  cases n with
  | zero =>
    have hdim := zero_dimension S
    have hx : (0 : E 0) ∉ S := by
      intro hx
      have hh := hdim.2.1
      simp only [ite_eq_left hx, hv] at hh
      norm_num at hh
    exact ⟨hdim.2.2 f |>.1, by simpa only [dite_eq_right hx] using (hdim.2.2 f).2⟩
  | succ n =>
    let Q := enclosingBox S
    have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
    obtain ⟨hi, hval⟩ := ExceptionalSets.zero_off_contentZero (Nat.succ_pos n)
      (zeroExtension_bounded f hb Q) (zero_volume_contentZero hS hv)
      (fun x _ hx => zeroExtension_of_not_mem f hx)
    have hf := (region_integrable_iff_box f hQ).mpr hi
    exact ⟨hf, (integral_eq_on_enclosing_box f hf hQ hi).trans hval⟩

lemma open_integral_eq_on_enclosing_box {U : Set (E n)} (f : U → ℝ) (hf : OpenIntegrable f)
    (Q : Box n) (hQ : Encloses (Function.support (zeroExtension f)) Q) :
    ∃ h : Integrable (zeroExtension f) Q, openIntegral f = integral (zeroExtension f) Q h := by
  obtain ⟨hU, hbS, R, hR, hiR⟩ := hf
  have hzero : ∀ x, x ∉ Function.support (zeroExtension f) → zeroExtension f x = 0 := by
    intro x hx; simpa only [Function.mem_support, not_not] using hx
  obtain ⟨M, hM, hbound⟩ := exists_abs_bound hiR.1
  have hb (B : Box n) : Bounded (zeroExtension f) B := by
    apply bounded_of_abs_le (M := M)
    intro x _
    by_cases hx : x ∈ Function.support (zeroExtension f)
    · exact hbound x (encloses_subset hR hx)
    · rw [hzero x hx, abs_zero]; exact hM
  have hiQ := (supported_box_independence hR hQ hzero hb).1.mp hiR
  have hcan := enclosingBox_encloses hbS
  have hican := (supported_box_independence hR hcan hzero hb).1.mp hiR
  exact ⟨hiQ, (supported_box_independence hcan hQ hzero hb).2 hican hiQ⟩


lemma zeroExtension_coordinate {k : ℕ} (f : S → E k) (i : Fin k) :
    (fun x => zeroExtension f x i) = zeroExtension (fun x => f x i) := by
  funext x
  classical
  by_cases hx : x ∈ S <;>
    simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma zeroExtension_norm {k : ℕ} (f : S → E k) :
    (fun x => ‖zeroExtension f x‖) = zeroExtension (fun x => ‖f x‖) := by
  funext x
  classical
  by_cases hx : x ∈ S <;>
    simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma vector_integrable_iff_box {k : ℕ} (f : S → E k) (hQ : Encloses S Q) :
    VectorRegionIntegrable f ↔ VectorIntegrable (zeroExtension f) Q := by
  constructor
  · intro hf i
    rw [zeroExtension_coordinate]
    exact (region_integrable_iff_box _ hQ).mp (hf.2 i)
  · intro hf
    refine ⟨encloses_bounded hQ, fun i => ?_⟩
    apply (region_integrable_iff_box _ hQ).mpr
    have h := hf i
    rwa [zeroExtension_coordinate] at h

lemma vectorRegionIntegral_eq_box {k : ℕ} (f : S → E k) (hf : VectorRegionIntegrable f)
    (hQ : Encloses S Q) (hi : VectorIntegrable (zeroExtension f) Q) :
    vectorRegionIntegral f = vectorIntegral (zeroExtension f) Q hi := by
  ext i
  change regionIntegral (fun x => f x i) = integral (fun x => zeroExtension f x i) Q (hi i)
  have he := zeroExtension_coordinate f i
  have hii : Integrable (zeroExtension (fun x => f x i)) Q := he ▸ (hi i)
  exact (integral_eq_on_enclosing_box _ (hf.2 i) hQ hii).trans
    (congrArg (fun g => lowerIntegral g Q) he.symm)

lemma vector_integrable_norm {k : ℕ} (f : S → E k) (hf : VectorRegionIntegrable f) :
    RegionIntegrable (fun x => ‖f x‖) := by
  have hQ := enclosingBox_encloses hf.1
  apply (region_integrable_iff_box _ hQ).mpr
  have hi := Darboux.integrable_norm ((vector_integrable_iff_box f hQ).mp hf)
  rwa [zeroExtension_norm] at hi

lemma vector_norm_bound {k : ℕ} (f : S → E k) (hf : VectorRegionIntegrable f) :
    ‖vectorRegionIntegral f‖ ≤ regionIntegral (fun x => ‖f x‖) := by
  have hQ := enclosingBox_encloses hf.1
  have hi := (vector_integrable_iff_box f hQ).mp hf
  have hn := Darboux.integrable_norm hi
  have hni : Integrable (zeroExtension (fun x => ‖f x‖)) (enclosingBox S) :=
    (zeroExtension_norm f) ▸ hn
  rw [vectorRegionIntegral_eq_box f hf hQ hi]
  exact (vector_integral_norm_le hi hn).trans_eq
    ((congrArg (fun g => lowerIntegral g (enclosingBox S)) (zeroExtension_norm f)).trans
      (integral_eq_on_enclosing_box _ (vector_integrable_norm f hf) hQ hni).symm)

lemma vector_uniform_bound {k : ℕ} (hS : Jordan S) (f : S → E k)
    (hf : VectorRegionIntegrable f) (M : ℝ) (_hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖vectorRegionIntegral f‖ ≤ M * volume S := by
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses hf.1
  have hnf := vector_integrable_norm f hf
  have hni := (region_integrable_iff_box _ hQ).mp hnf
  have hiS := jordan_integrable_on_box hS hQ
  have hiM := integrable_smul M hiS
  have hle : ∀ x ∈ carrier Q,
      zeroExtension (fun x => ‖f x‖) x ≤ M * indicator S x := by
    intro x _
    classical
    by_cases hx : x ∈ S
    · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, indicator,
        Specs.D04.C06.JordanRegions.Model.indicator, hx] using hb ⟨x, hx⟩
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, indicator,
        Specs.D04.C06.JordanRegions.Model.indicator, hx]
  have hh := integral_mono hni hiM hle
  rw [integral_smul M hiS hiM] at hh
  exact (vector_norm_bound f hf).trans ((integral_eq_on_enclosing_box _ hnf hQ hni).le.trans
    (hh.trans_eq (congrArg (fun t => M * t) (volume_eq_on_enclosing_box hS hQ hiS).symm)))

lemma zeroExtension_linear {k m : ℕ} (f : S → E k) (A : E k →ₗ[ℝ] E m) :
    zeroExtension (fun x => A (f x)) = (fun x => A (zeroExtension f x)) := by
  funext x
  classical
  by_cases hx : x ∈ S <;>
    simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma vector_integral_linear {k m : ℕ} (f : S → E k) (A : E k →ₗ[ℝ] E m)
    (hf : VectorRegionIntegrable f) :
    VectorRegionIntegrable (fun x => A (f x)) ∧
    vectorRegionIntegral (fun x => A (f x)) = A (vectorRegionIntegral f) := by
  have hQ := enclosingBox_encloses hf.1
  have hi := (vector_integrable_iff_box f hQ).mp hf
  have hAi := Darboux.vector_integrable_linear A hi
  have hAe : VectorIntegrable (zeroExtension (fun x => A (f x))) (enclosingBox S) := by
    rw [zeroExtension_linear]; exact hAi
  have hAf := (vector_integrable_iff_box _ hQ).mpr hAe
  refine ⟨hAf, ?_⟩
  rw [vectorRegionIntegral_eq_box _ hAf hQ hAe, vectorRegionIntegral_eq_box f hf hQ hi]
  have he : vectorIntegral (zeroExtension (fun x => A (f x))) (enclosingBox S) hAe =
      vectorIntegral (fun x => A (zeroExtension f x)) (enclosingBox S) hAi := by
    congr 1
    exact zeroExtension_linear f A
  exact he.trans (Darboux.vector_integral_linear A hi hAi)


lemma jordan_finite_inter {ι : Type} (s : Finset ι) (S : ι → Set (E n))
    (hne : s.Nonempty) (hS : ∀ i ∈ s, Jordan (S i)) : Jordan (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert i s hi ih =>
    by_cases hs : s.Nonempty
    · have he : (⋂ j ∈ insert i s, S j) = S i ∩ ⋂ j ∈ s, S j := by simp
      rw [he]
      exact jordan_inter (hS i (by simp))
        (ih hs (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa using hS i (by simp)

lemma regionIntegral_one (S : Set (E n)) :
    regionIntegral (fun _ : S => (1 : ℝ)) = volume S := rfl

lemma volume_finite_disjoint_union {ι : Type} (s : Finset ι) (S : ι → Set (E n))
    (hS : ∀ i ∈ s, Jordan (S i)) (hdis : (s : Set ι).PairwiseDisjoint S) :
    volume (⋃ i ∈ s, S i) = ∑ i ∈ s, volume (S i) := by
  have hf (i : ι) (hi : i ∈ s) : RegionIntegrable (fun _ : S i => (1 : ℝ)) := by
    obtain ⟨Q, hQ, hiQ⟩ := hS i hi
    exact ⟨⟨1, by intro x; simp⟩, Q, hQ, hiQ⟩
  exact (integral_finite_disjoint_union s S (fun _ => 1) hS hdis hf).2

lemma zeroExtension_abs (f : S → ℝ) :
    (fun x => |zeroExtension f x|) = zeroExtension (fun x => |f x|) := by
  funext x
  classical
  by_cases hx : x ∈ S <;>
    simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma scalar_abs_bound (f : S → ℝ) (hf : RegionIntegrable f) :
    RegionIntegrable (fun x => |f x|) ∧ |regionIntegral f| ≤ regionIntegral (fun x => |f x|) := by
  obtain ⟨R, hR, _⟩ := hf.2
  have hQ := enclosingBox_encloses (encloses_bounded hR)
  have hi := (region_integrable_iff_box f hQ).mp hf
  have ha := integrable_abs hi
  have hae : Integrable (zeroExtension (fun x => |f x|)) (enclosingBox S) :=
    (zeroExtension_abs f) ▸ ha
  refine ⟨(region_integrable_iff_box _ hQ).mpr hae, ?_⟩
  exact (integral_abs_bound hi ha).1.trans_eq
    (congrArg (fun g => lowerIntegral g (enclosingBox S)) (zeroExtension_abs f))

lemma scalar_uniform_bound (hS : Jordan S) (f : S → ℝ) (hf : RegionIntegrable f)
    (M : ℝ) (_hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) : |regionIntegral f| ≤ M * volume S := by
  have hQ := enclosingBox_encloses (jordan_bounded hS)
  have ha := (scalar_abs_bound f hf).1
  have hai := (region_integrable_iff_box _ hQ).mp ha
  have hiS := jordan_integrable_on_box hS hQ
  have hiM := integrable_smul M hiS
  have hle : ∀ x ∈ carrier (enclosingBox S),
      zeroExtension (fun x => |f x|) x ≤ M * indicator S x := by
    intro x _
    classical
    by_cases hx : x ∈ S
    · simpa [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, indicator,
        Specs.D04.C06.JordanRegions.Model.indicator, hx] using hb ⟨x, hx⟩
    · simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension, indicator,
        Specs.D04.C06.JordanRegions.Model.indicator, hx]
  have hh := integral_mono hai hiM hle
  rw [integral_smul M hiS hiM] at hh
  exact (scalar_abs_bound f hf).2.trans hh

lemma vector_zero_dimension {k : ℕ} (S : Set (E 0)) (f : S → E k) :
    VectorRegionIntegrable f ∧ vectorRegionIntegral f =
      (if h : (0 : E 0) ∈ S then f ⟨0, h⟩ else 0) := by
  classical
  refine ⟨⟨jordan_bounded (jordan_zero_dim S), fun i => (zero_dimension S).2.2 _ |>.1⟩, ?_⟩
  ext i
  have hh := ((zero_dimension S).2.2 (fun x => f x i)).2
  by_cases hx : (0 : E 0) ∈ S
  · simpa only [vector_coordinate, dite_eq_left hx] using hh
  · simpa only [vector_coordinate, dite_eq_right hx, PiLp.zero_apply] using hh

lemma vector_zero_target (hb : Bornology.IsBounded S) (f : S → E 0) :
    VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0 :=
  ⟨⟨hb, fun i => Fin.elim0 i⟩, Subsingleton.elim _ _⟩

lemma vector_empty {k : ℕ} (f : (∅ : Set (E n)) → E k) :
    VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0 := by
  refine ⟨⟨Bornology.isBounded_empty, fun i => (empty_region (fun x => f x i)).1⟩, ?_⟩
  ext i
  exact (empty_region (fun x => f x i)).2

lemma vector_zero_volume {k : ℕ} (hS : Jordan S) (hv : volume S = 0) (f : S → E k)
    (hb : RegionBounded f) : VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0 := by
  have hbi (i : Fin k) : RegionBounded (fun x => f x i) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun x => (PiLp.norm_apply_le (f x) i).trans (hM x)⟩
  refine ⟨⟨jordan_bounded hS, fun i => (zero_volume_region hS hv _ (hbi i)).1⟩, ?_⟩
  ext i
  exact (zero_volume_region hS hv _ (hbi i)).2


/-- The ambient-function finite-additivity statement applies to every function
on the union, through its actual zero extension. -/
lemma integral_disjoint_union_subtype (f : (S ∪ T : Set (E n)) → ℝ)
    (hS : Jordan S) (hT : Jordan T) (hST : Disjoint S T)
    (hfS : RegionIntegrable (fun x : S => f ⟨x, Or.inl x.property⟩))
    (hfT : RegionIntegrable (fun x : T => f ⟨x, Or.inr x.property⟩)) :
    RegionIntegrable f ∧ regionIntegral f =
      regionIntegral (fun x : S => f ⟨x, Or.inl x.property⟩) +
        regionIntegral (fun x : T => f ⟨x, Or.inr x.property⟩) := by
  have heS : (fun x : S => zeroExtension f x) = (fun x : S => f ⟨x, Or.inl x.property⟩) := by
    funext x; exact zeroExtension_apply f ⟨x, Or.inl x.property⟩
  have heT : (fun x : T => zeroExtension f x) = (fun x : T => f ⟨x, Or.inr x.property⟩) := by
    funext x; exact zeroExtension_apply f ⟨x, Or.inr x.property⟩
  have heU : (fun x : (S ∪ T : Set (E n)) => zeroExtension f x) = f := by
    funext x; exact zeroExtension_apply f x
  have hiS : RegionIntegrable (fun x : S => zeroExtension f x) := heS ▸ hfS
  have hiT : RegionIntegrable (fun x : T => zeroExtension f x) := heT ▸ hfT
  have hh := integral_disjoint_union (zeroExtension f) hS hT hST hiS hiT
  rwa [heU, heS, heT] at hh

end D04.JordanRegions
