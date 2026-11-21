import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.FiniteSheetCounting
import MathGenome.Internal.MultivariableAnalysis.D04.C07.CoordinateSeamsVolumes
import MathGenome.Internal.MultivariableAnalysis.D04.C07.ImproperSubstitution

noncomputable section
open Set
open scoped BigOperators Classical
namespace D04.FiniteSheetCounting
open Darboux JordanRegions
open Specs.D04.C07.FiniteSheetCounting.Model
open Specs.D04.C07.CoordinateCharts.Model

abbrev AmbientIntegrable := @Specs.D04.C07.FiniteSheetCounting.Model.AmbientIntegrable
abbrev ambientIntegral := @Specs.D04.C07.FiniteSheetCounting.Model.ambientIntegral
abbrev imageMultiplicity := @Specs.D04.C07.FiniteSheetCounting.Model.imageMultiplicity

lemma zeroExtension_univ {n : ℕ} (F : E n → ℝ) :
    zeroExtension (fun x : (univ : Set (E n)) => F x) = F := by
  funext x
  exact zeroExtension_apply _ ⟨x, mem_univ x⟩

lemma ambient_eq_box {n : ℕ} (F : E n → ℝ) (hF : AmbientIntegrable F)
    (Q : Box n) (hQ : Encloses (Function.support F) Q) :
    ∃ hi : Integrable F Q, ambientIntegral F = integral F Q hi := by
  have hF' : OpenIntegrable (fun x : (univ : Set (E n)) => F x) := hF
  obtain ⟨hi, hv⟩ := open_integral_eq_on_enclosing_box _ hF' Q (by
    simpa only [zeroExtension_univ] using hQ)
  have hi' : Integrable F Q := by simpa only [zeroExtension_univ] using hi
  refine ⟨hi', ?_⟩
  exact hv.trans (congrArg (fun G => lowerIntegral G Q) (zeroExtension_univ F))

theorem ambient_sum : Specs.D04.C07.FiniteSheetCounting.ambient_sumType := by
  intro n m F hF
  have hb (i : Fin m) : Bornology.IsBounded (Function.support (F i)) := by
    have h := (hF i).2.1
    simpa only [zeroExtension_univ] using h
  let S := ⋃ i, Function.support (F i)
  have hbS : Bornology.IsBounded S := Bornology.isBounded_iUnion.mpr hb
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr hbS
  have hQi (i : Fin m) : Encloses (Function.support (F i)) Q :=
    (closure_mono (subset_iUnion (fun i => Function.support (F i)) i)).trans hQ
  have hi (i : Fin m) := (ambient_eq_box (F i) (hF i) Q (hQi i)).choose
  have his : Integrable (fun x => ∑ i, F i x) Q := by
    simpa only [Finset.sum_const_zero] using
      integrable_sum Finset.univ F (fun i _ => hi i)
  have hsupp : Function.support (fun x => ∑ i, F i x) ⊆ S := by
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro i _
    by_contra hnF
    exact hn (mem_iUnion.mpr ⟨i, hnF⟩)
  have hs : AmbientIntegrable (fun x => ∑ i, F i x) := by
    refine ⟨isOpen_univ, ?_, Q, ?_, ?_⟩
    · change Bornology.IsBounded (Function.support (zeroExtension
        (fun x : (univ : Set (E n)) => ∑ i, F i x)))
      rw [zeroExtension_univ (fun x => ∑ i, F i x)]; exact hbS.subset hsupp
    · change Encloses (Function.support (zeroExtension
        (fun x : (univ : Set (E n)) => ∑ i, F i x))) Q
      rw [zeroExtension_univ (fun x => ∑ i, F i x)]; exact (closure_mono hsupp).trans hQ
    · change Integrable (zeroExtension
        (fun x : (univ : Set (E n)) => ∑ i, F i x)) Q
      rwa [zeroExtension_univ (fun x => ∑ i, F i x)]
  refine ⟨hs, ?_⟩
  obtain ⟨hsQ, hsval⟩ := ambient_eq_box _ hs Q ((closure_mono hsupp).trans hQ)
  change ambientIntegral (fun y => ∑ i, F i y) = ∑ i, ambientIntegral (F i)
  rw [hsval]
  have hv := integral_sum Finset.univ F (fun i _ => hi i) his
  simp only [Finset.mem_univ, ↓reduceDIte] at hv
  exact hv.trans (Finset.sum_congr rfl (fun i _ =>
    (ambient_eq_box (F i) (hF i) Q (hQi i)).choose_spec.symm))

theorem multiplicity_identity : Specs.D04.C07.FiniteSheetCounting.multiplicity_identityType := by
  intro n m S f y
  classical
  simp only [imageMultiplicity, Specs.D04.C07.FiniteSheetCounting.Model.imageMultiplicity,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : y ∈ S i <;> simp [hy]

theorem counting_integral : Specs.D04.C07.FiniteSheetCounting.counting_integralType := by
  intro n m S f hf
  have h := ambient_sum (fun i => (S i).indicator f) hf
  have he : (fun y => f y * (imageMultiplicity S y : ℝ)) =
      fun y => ∑ i, (S i).indicator f y := funext (multiplicity_identity S f)
  rw [he]
  exact ⟨h.1, h.2.symm⟩

/-- A bounded integration domain and its actual ambient zero extension have
the same Riemann integral. No Jordan condition on the domain is needed. -/
lemma ambient_region {n : ℕ} {S : Set (E n)} (hbS : Bornology.IsBounded S)
    (F : E n → ℝ) (hF : AmbientIntegrable (S.indicator F)) :
    RegionIntegrable (fun x : S => F x) ∧
      regionIntegral (fun x : S => F x) = ambientIntegral (S.indicator F) := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr hbS
  have hsupp : Function.support (S.indicator F) ⊆ S := by
    intro x hx
    by_contra hn
    exact hx (Set.indicator_of_notMem hn F)
  obtain ⟨hi, hv⟩ := ambient_eq_box _ hF Q ((closure_mono hsupp).trans hQ)
  have he : zeroExtension (fun x : S => F x) = S.indicator F := by
    funext x
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply _ ⟨x, hx⟩, indicator_of_mem hx]
    · rw [zeroExtension_of_not_mem _ hx, indicator_of_notMem hx]
  have hif : Integrable (zeroExtension (fun x : S => F x)) Q := he ▸ hi
  have hri := (region_integrable_iff_box _ hQ).mpr hif
  refine ⟨hri, ?_⟩
  exact (integral_eq_on_enclosing_box _ hri hQ hif).trans
    ((congrArg (fun G => lowerIntegral G Q) he).trans hv.symm)

/-- Passing to the ambient zero extension preserves the region integral. -/
lemma ambient_zeroExtension {n : ℕ} {S : Set (E n)} (f : S → ℝ)
    (hf : RegionIntegrable f) :
    AmbientIntegrable (zeroExtension f) ∧
      ambientIntegral (zeroExtension f) = regionIntegral f := by
  have hb := encloses_bounded hf.2.choose_spec.1
  have hi := (RegionSubstitution.region_integrable_iff_open isOpen_univ
    (subset_univ S) hb f hf.1).mp hf
  exact ⟨hi, (RegionSubstitution.region_integral_eq_open (subset_univ S) f hf hi).symm⟩

lemma zeroExtension_restrict {n : ℕ} (S : Set (E n)) (F : E n → ℝ) :
    zeroExtension (fun x : S => F x) = S.indicator F := by
  funext x
  by_cases hx : x ∈ S
  · rw [zeroExtension_apply _ ⟨x, hx⟩, indicator_of_mem hx]
  · rw [zeroExtension_of_not_mem _ hx, indicator_of_notMem hx]

/-- Restricting an ambient Riemann integrand to any Jordan region is valid. -/
lemma ambient_restrict {n : ℕ} (F : E n → ℝ) (hF : AmbientIntegrable F)
    {K : Set (E n)} (hK : Jordan K) :
    RegionIntegrable (fun x : K => F x) ∧
      AmbientIntegrable (K.indicator F) ∧
      ambientIntegral (K.indicator F) = regionIntegral (fun x : K => F x) := by
  have hbF : Bornology.IsBounded (Function.support F) := by
    simpa only [zeroExtension_univ] using hF.2.1
  obtain ⟨R, hR⟩ := (encloses_exists_iff_bounded _).mpr (hbF.union (jordan_bounded hK))
  have hFR : (carrier R).indicator F = F := by
    funext x
    by_cases hx : x ∈ carrier R
    · exact indicator_of_mem hx F
    · rw [indicator_of_notMem hx]
      symm
      by_contra hn
      exact hx (encloses_subset hR (Or.inl hn))
  have hiR := (ambient_region (carrier_isBounded R) F (hFR.symm ▸ hF)).1
  have hiK := AbsoluteConvergence.region_restrict hiR hK
    (fun x hx => encloses_subset hR (Or.inr hx))
  have ha := ambient_zeroExtension (fun x : K => F x) hiK
  rw [zeroExtension_restrict] at ha
  exact ⟨hiK, ha⟩

/-- An integrable function vanishing outside an open set converges along every
regular compact Jordan exhaustion of that set. The support need not be closed
inside the open set. Cells whose entire value interval avoids zero form a
compact subset of the open set; retaining those cells bounds every truncation
between the original lower and upper Darboux sums. -/
lemma ambient_exhaustion {n : ℕ} (F : E n → ℝ) (hF : AmbientIntegrable F)
    {U : Set (E n)} (hs : Function.support F ⊆ U)
    {K : ℕ → Set (E n)} (hK : ImproperExhaustions.RegularExhaustion U K) :
    ImproperExhaustions.HasIntegralAlong F K (ambientIntegral F) := by
  open Filter Topology in
  rw [ImproperExhaustions.HasIntegralAlong,
    Specs.D04.C06.ImproperExhaustions.Model.HasIntegralAlong]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hb : Bornology.IsBounded (Function.support F) := by
    simpa only [zeroExtension_univ] using hF.2.1
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded _).mpr hb
  obtain ⟨hi, hv⟩ := ambient_eq_box F hF Q hQ
  obtain ⟨P, hP⟩ := (integrable_iff_gap F Q hi.1).mp hi ε hε
  let A : Finset (CellIndex P) := Finset.univ.filter
    (fun c => 0 < cellInfimum F P c ∨ cellSupremum F P c < 0)
  let C : Set (E n) := ⋃ c ∈ A, cell P c
  have hc : IsCompact C := A.isCompact_biUnion (fun c _ =>
    DiscontinuityCriterion.carrier_compact (cellBox P c))
  have hCU : C ⊆ U := by
    intro x hx
    obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hx
    have ha := (Finset.mem_filter.mp hc).2
    apply hs
    change F x ≠ 0
    rcases ha with ha | ha
    · exact ne_of_gt (ha.trans_le (cellInfimum_le F hi.1 P c hx))
    · exact ne_of_lt ((le_cellSupremum F hi.1 P c hx).trans_lt ha)
  obtain ⟨j, hj⟩ := ImproperExhaustions.compact_contained_in_exhaustion hK hc hCU
  refine ⟨j, fun k hjk => ?_⟩
  have hCK : C ⊆ K k := hj.trans (ImproperExhaustions.regular_exhaustion_mono hK hjk)
  let G := (K k).indicator F
  have hg := ambient_restrict F hF (hK.1 k).2.1
  have hsG : Function.support G ⊆ Function.support F := by
    intro x hx
    by_cases hxK : x ∈ K k
    · change G x ≠ 0 at hx
      change F x ≠ 0
      simpa only [G, indicator_of_mem hxK] using hx
    · exact False.elim (hx (indicator_of_notMem hxK F))
  obtain ⟨hgi, hgv⟩ := ambient_eq_box G hg.2.1 Q ((closure_mono hsG).trans hQ)
  have hbounds (c : CellIndex P) (x : E n) (hx : x ∈ cell P c) :
      cellInfimum F P c ≤ G x ∧ G x ≤ cellSupremum F P c := by
    by_cases hxK : x ∈ K k
    · rw [show G x = F x from indicator_of_mem hxK F]
      exact ⟨cellInfimum_le F hi.1 P c hx, le_cellSupremum F hi.1 P c hx⟩
    · rw [show G x = 0 from indicator_of_notMem hxK F]
      have hn : c ∉ A := by
        intro hc
        exact hxK (hCK (mem_iUnion₂.mpr ⟨c, hc, hx⟩))
      have hn' : ¬ (0 < cellInfimum F P c ∨ cellSupremum F P c < 0) := by
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hn
      exact ⟨le_of_not_gt (fun h => hn' (Or.inl h)),
        le_of_not_gt (fun h => hn' (Or.inr h))⟩
  have hlow : lowerSum F P ≤ lowerSum G P := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_right _ (cellContent_nonneg P c)
    exact le_csInf ((cell_nonempty P c).image G) (by
      rintro _ ⟨x, hx, rfl⟩; exact (hbounds c x hx).1)
  have hupp : upperSum G P ≤ upperSum F P := by
    apply Finset.sum_le_sum
    intro c _
    apply mul_le_mul_of_nonneg_right _ (cellContent_nonneg P c)
    exact csSup_le ((cell_nonempty P c).image G) (by
      rintro _ ⟨x, hx, rfl⟩; exact (hbounds c x hx).2)
  have hbF := integral_bounds F Q hi P
  have hbG := integral_bounds G Q hgi P
  change |regionIntegral (fun x : K k => F x) - ambientIntegral F| < ε
  have heval : regionIntegral (fun x : K k => F x) = integral G Q hgi :=
    hg.2.2.symm.trans hgv
  rw [heval, hv]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The existing compact-contained theorem, bridged to the ambient integral
used in counting. The unrestricted theorem below uses the same region
substitution theorem on corresponding regular truncations. -/
lemma compact_single_sheet {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (S : Set (E n)) (hS : Jordan S) (hU : closure S ⊆ e.source)
    (f : E n → ℝ) (hf : AmbientIntegrable ((e '' S).indicator f)) :
    RegionIntegrable (fun x : S => f (e x) * |(fderiv ℝ e x).det|) ∧
    regionIntegral (fun x : S => f (e x) * |(fderiv ℝ e x).det|) =
      ambientIntegral ((e '' S).indicator f) := by
  have hK := (jordan_bounded hS).isCompact_closure
  have himg := RegionSubstitution.jordan_image e he hei S hS hK hU
  have hri := ambient_region himg.1 f hf
  have hsub := RegionSubstitution.region_substitution e he hei S hS hK hU
    (fun y : e '' S => f y) hri.1.1
  exact ⟨hsub.2.1.mp hri.1, (hsub.2.2 (Or.inl hri.1)).symm.trans hri.2⟩

/-- Single-sheet substitution using corresponding regular truncations. Both
limits are taken in the original ambient Riemann integral, without imposing
compact containment on the closure of the piece. -/
theorem single_sheet : Specs.D04.C07.FiniteSheetCounting.single_sheetType := by
  intro n e he hei S _hS hSU f _hb hf hg
  let F := (e '' S).indicator f
  let g : S → ℝ := fun x => f (e x) * |(fderiv ℝ e x).det|
  let G := zeroExtension g
  have hG := ambient_zeroExtension g hg
  have hFs : Function.support F ⊆ e.target := by
    intro y hy
    have hyS : y ∈ e '' S := by
      by_contra hn
      exact hy (indicator_of_notMem hn f)
    obtain ⟨x, hx, rfl⟩ := hyS
    exact e.map_source (hSU hx)
  have hGs : Function.support G ⊆ e.source :=
    (RegionSubstitution.support_zeroExtension_subset g).trans hSU
  have hw (x : e.source) : F (e x) * |(fderiv ℝ e x).det| = G x := by
    simpa only [zeroExtension_restrict] using
      RegionSubstitution.weighted_extension e hSU (fun y : e '' S => f y) x
  obtain ⟨K, hK⟩ := ImproperExhaustions.regular_exhaustion_exists e.source e.open_source
  have hL := ImproperSubstitution.regularExhaustion_image e he hei hK
  have hlimF := ambient_exhaustion F hf hFs hL
  have hlimG := ambient_exhaustion G hG.1 hGs hK
  have heq (j : ℕ) :
      regionIntegral (fun y : e '' K j => F y) =
        regionIntegral (fun x : K j => G x) := by
    have hI := ambient_restrict F hf (hL.1 j).2.1
    have hsub := RegionSubstitution.region_substitution e he hei (K j)
      (hK.1 j).2.1 (by simpa only [(hK.1 j).1.isClosed.closure_eq] using (hK.1 j).1)
      (by simpa only [(hK.1 j).1.isClosed.closure_eq] using (hK.1 j).2.2)
      (fun y : e '' K j => F y) hI.1.1
    refine (hsub.2.2 (Or.inl hI.1)).trans ?_
    congr 1
    funext x
    exact hw ⟨x, (hK.1 j).2.2 x.property⟩
  have hfun : (fun j => regionIntegral (fun y : e '' K j => F y)) =
      (fun j => regionIntegral (fun x : K j => G x)) := funext heq
  change Filter.Tendsto _ Filter.atTop (nhds (ambientIntegral F)) at hlimF
  change Filter.Tendsto _ Filter.atTop (nhds (ambientIntegral G)) at hlimG
  rw [hfun] at hlimF
  exact hG.2.symm.trans (tendsto_nhds_unique hlimG hlimF)

/-- Each sheet is substituted separately, then the actual image indicators
are added. The parameter decomposition retains the original scope; no
restriction on image overlaps is used. -/
theorem finite_sheet_counting :
    Specs.D04.C07.FiniteSheetCounting.finite_sheet_countingType := by
  intro n m Φ T Z S e hS _hd hU he hei _hΦ _hZ _hT f hb hf hg
  have hc := counting_integral (fun i => (e i) '' S i) f hf
  refine ⟨hc.1, ?_⟩
  calc
    (∑ i, regionIntegral (fun x : S i =>
      f (e i x) * |(fderiv ℝ (e i) x).det|)) =
        ∑ i, ambientIntegral (((e i) '' S i).indicator f) := by
      apply Finset.sum_congr rfl
      intro i _
      exact single_sheet (e i) (he i) (hei i) (S i) (hS i) (hU i) f hb (hf i) (hg i)
    _ = _ := hc.2

theorem remainder_zero : Specs.D04.C07.FiniteSheetCounting.remainder_zeroType := by
  intro n hn Z hZ h hb
  have hbound : Bornology.IsBounded Z := by
    obtain ⟨ι, hι, B, hcover, _⟩ := hZ 1 zero_lt_one
    exact (Bornology.isBounded_iUnion.mpr (fun i =>
      carrier_isBounded (B i))).subset hcover
  have hz := LinearVolume.contentZero_jordan_volume hn Z hbound hZ
  exact zero_volume_region hz.1 hz.2 h hb

/-- Open boxes are Jordan, including arbitrary bounded assignments on their
faces in later applications. -/
lemma jordan_open_box {n : ℕ} (hn : 0 < n) (Q : Box n) :
    Jordan (interior (carrier Q)) := by
  have hz := LinearVolume.contentZero_jordan_volume hn
    (Specs.D04.C07.CoordinateSeamsVolumes.Model.faces Q)
    ((carrier_isBounded Q).subset sdiff_subset)
    (CoordinateSeamsVolumes.box_faces_contentZero Q)
  have heq : interior (carrier Q) = carrier Q \
      Specs.D04.C07.CoordinateSeamsVolumes.Model.faces Q := by
    ext x
    simp only [Specs.D04.C07.CoordinateSeamsVolumes.Model.faces, mem_diff]
    constructor
    · intro hx; exact ⟨interior_subset hx, fun hh => hh.2 hx⟩
    · rintro ⟨hx, hh⟩
      by_contra hn
      exact hh ⟨hx, hn⟩
  rw [heq]
  exact jordan_diff (ImproperExhaustions.jordan_box Q) hz.1

/-- Four strips of angular width π. Widening each angular interval to 2π
provides a genuine diffeomorphism on a neighborhood of that strip. -/
def pieceBox (i : Fin 4) : Box 2 where
  lower := WithLp.toLp 2 ![1, (i : ℝ) * Real.pi]
  upper := WithLp.toLp 2 ![2, ((i : ℝ) + 1) * Real.pi]
  ordered := by
    intro j
    fin_cases j <;> dsimp <;> linarith [Real.pi_pos]

lemma angularPiece_eq_interior (i : Fin 4) :
    angularPiece i = interior (carrier (pieceBox i)) := by
  rw [interior_carrier]
  ext p
  change (1 < p 0 ∧ p 0 < 2 ∧ _ < p 1 ∧ p 1 < _) ↔
    (∀ j : Fin 2, _ < p j ∧ p j < _)
  constructor
  · rintro ⟨hr, hR, ht, hT⟩ j
    fin_cases j
    · exact ⟨hr, hR⟩
    · exact ⟨ht, hT⟩
  · intro h
    exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩

lemma angularPiece_jordan (i : Fin 4) : Jordan (angularPiece i) := by
  rw [angularPiece_eq_interior]
  exact jordan_open_box (by decide) _

lemma angularPiece_subset (i : Fin 4) : angularPiece i ⊆ doubleDomain := by
  intro p hp
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hi4 : (i : ℝ) + 1 ≤ 4 := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  refine ⟨hp.1, hp.2.1, ?_, ?_⟩
  · exact lt_of_le_of_lt (mul_nonneg hi0 Real.pi_pos.le) hp.2.2.1
  · exact lt_of_lt_of_le hp.2.2.2 (mul_le_mul_of_nonneg_right hi4 Real.pi_pos.le)

lemma angularPieces_disjoint : Pairwise
    (fun i j : Fin 4 => Disjoint (angularPiece i) (angularPiece j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hp hq
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij')
    have he := mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    exact (not_lt_of_ge (le_trans hp.2.2.2.le he)) hq.2.2.1
  · have hc : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hji')
    have he := mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    exact (not_lt_of_ge (le_trans hq.2.2.2.le he)) hp.2.2.1

lemma angularPiece_chart (i : Fin 4) :
    ∃ e : OpenPartialHomeomorph (E 2) (E 2),
      (e : E 2 → E 2) = polar ∧ angularPiece i ⊆ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target := by
  let α : ℝ := (i : ℝ) * Real.pi - Real.pi / 2
  obtain ⟨e, hs, _, he, hc, hci⟩ := (CoordinateCharts.polar_chart α).2
  refine ⟨e, he, ?_, hc, hci⟩
  rw [hs]
  intro p hp
  refine ⟨by linarith [hp.1], ?_, ?_⟩
  · change α < p 1
    dsimp [α]; linarith [hp.2.2.1, Real.pi_pos]
  · change p 1 < α + 2 * Real.pi
    dsimp [α]; linarith [hp.2.2.2, Real.pi_pos]

lemma doubleDomain_eq_interior : doubleDomain = interior (carrier doubleBox) := by
  rw [interior_carrier]
  ext p
  constructor
  · intro h j
    fin_cases j
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.2.2.1, h.2.2.2⟩
  · intro h
    exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩

lemma double_remainder_contentZero : NullCovers.ContentZero
    (doubleDomain \ ⋃ i : Fin 4, angularPiece i) := by
  let F : Finset (Fin 2 × ℝ) := {(1, Real.pi), (1, 2 * Real.pi), (1, 3 * Real.pi)}
  apply NullCovers.contentZero_mono (T := ⋃ a ∈ F,
    NullCovers.coordinateFace doubleBox a.1 a.2) ?_
    (NullCovers.finite_faces_contentZero doubleBox F)
  rintro p ⟨hp, hn⟩
  have hnot (i : Fin 4) : p ∉ angularPiece i := fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩)
  have hpQ : p ∈ carrier doubleBox := by
    intro j
    fin_cases j
    · exact ⟨hp.1.le, hp.2.1.le⟩
    · exact ⟨hp.2.2.1.le, hp.2.2.2.le⟩
  have heq : p 1 = Real.pi ∨ p 1 = 2 * Real.pi ∨ p 1 = 3 * Real.pi := by
    by_contra! h
    by_cases hlt1 : p 1 < Real.pi
    · exact hnot 0 ⟨hp.1, hp.2.1, by simpa using hp.2.2.1, by simpa using hlt1⟩
    have hgt1 : Real.pi < p 1 := lt_of_le_of_ne (le_of_not_gt hlt1) (Ne.symm h.1)
    by_cases hlt2 : p 1 < 2 * Real.pi
    · apply hnot 1
      simp only [angularPiece, mem_setOf_eq, Fin.val_one, Nat.cast_one, one_mul, one_add_one_eq_two]
      exact And.intro hp.1 (And.intro hp.2.1 (And.intro hgt1 hlt2))
    have hgt2 : 2 * Real.pi < p 1 := lt_of_le_of_ne (le_of_not_gt hlt2) (Ne.symm h.2.1)
    by_cases hlt3 : p 1 < 3 * Real.pi
    · apply hnot 2
      norm_num [angularPiece]
      exact ⟨hp.1, hp.2.1, hgt2, hlt3⟩
    have hgt3 : 3 * Real.pi < p 1 := lt_of_le_of_ne (le_of_not_gt hlt3) (Ne.symm h.2.2)
    apply hnot 3
    norm_num [angularPiece]
    exact ⟨hp.1, hp.2.1, hgt3, hp.2.2.2⟩
  rcases heq with heq | heq | heq
  · exact mem_iUnion₂.mpr ⟨(1, Real.pi), by simp [F], hpQ, heq⟩
  · exact mem_iUnion₂.mpr ⟨(1, 2 * Real.pi), by simp [F], hpQ, heq⟩
  · exact mem_iUnion₂.mpr ⟨(1, 3 * Real.pi), by simp [F], hpQ, heq⟩

lemma closed_double_remainder_contentZero : NullCovers.ContentZero
    (carrier doubleBox \ ⋃ i : Fin 4, angularPiece i) := by
  apply NullCovers.contentZero_mono (T :=
    Specs.D04.C07.CoordinateSeamsVolumes.Model.faces doubleBox ∪
      (doubleDomain \ ⋃ i : Fin 4, angularPiece i)) ?_
    (contentZero_union (CoordinateSeamsVolumes.box_faces_contentZero doubleBox)
      double_remainder_contentZero)
  rintro p ⟨hp, hn⟩
  by_cases hi : p ∈ doubleDomain
  · exact Or.inr ⟨hi, hn⟩
  · left
    exact ⟨hp, by rw [← doubleDomain_eq_interior]; exact hi⟩

theorem double_decomposition : Specs.D04.C07.FiniteSheetCounting.double_decompositionType :=
  ⟨angularPiece_jordan, angularPieces_disjoint, angularPiece_subset,
    closed_double_remainder_contentZero, angularPiece_chart⟩

theorem annulus_area : Specs.D04.C07.FiniteSheetCounting.annulus_areaType := by
  have h1 := CoordinateSeamsVolumes.disk_area 1 (by norm_num)
  have h2 := CoordinateSeamsVolumes.disk_area 2 (by norm_num)
  have heq : annulus = Metric.ball (0 : E 2) 2 \ Metric.closedBall 0 1 := by
    ext y
    simp only [annulus, mem_setOf_eq, mem_diff, Metric.mem_ball,
      Metric.mem_closedBall, dist_zero_right, not_le]
    exact and_comm
  have hj : Jordan annulus := heq ▸ jordan_diff h2.2.2.1 h1.1
  have hu : Metric.closedBall (0 : E 2) 1 ∪ annulus = Metric.ball 0 2 := by
    ext y
    simp only [mem_union, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
      annulus, mem_setOf_eq]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases h1 : ‖y‖ ≤ 1
      · exact Or.inl h1
      · exact Or.inr ⟨lt_of_not_ge h1, h⟩
  have hd : Disjoint (Metric.closedBall (0 : E 2) 1) annulus := by
    apply Set.disjoint_left.mpr
    intro y hy hyA
    have hy' : ‖y‖ ≤ 1 := by simpa using hy
    exact (not_lt_of_ge hy') hyA.1
  have hv := (integral_disjoint_union (fun _ => (1 : ℝ)) h1.1 hj hd
    (LinearVolume.region_one_integrable h1.1) (LinearVolume.region_one_integrable hj)).2
  simp only [regionIntegral_one] at hv
  change volume (Metric.closedBall (0 : E 2) 1 ∪ annulus) =
    volume (Metric.closedBall (0 : E 2) 1) + volume annulus at hv
  rw [hu] at hv
  refine ⟨hj, ?_⟩
  have hv1 := h1.2.1
  have hv2 := h2.2.2.2
  change volume (Metric.closedBall (0 : E 2) 1) = _ at hv1
  norm_num at hv1 hv2
  linarith

lemma polar_norm (p : E 2) : ‖polar p‖ = |p 0| := by
  have hnorm := EuclideanSpace.real_norm_sq_eq (polar p)
  have hs := CoordinateCharts.circle_squares (p 0) (p 1)
  simp only [Fin.sum_univ_two] at hnorm
  change ‖polar p‖ ^ 2 = (p 0 * Real.cos (p 1)) ^ 2 +
    (p 0 * Real.sin (p 1)) ^ 2 at hnorm
  nlinarith [norm_nonneg (polar p), abs_nonneg (p 0), sq_abs (p 0)]

theorem double_image : Specs.D04.C07.FiniteSheetCounting.double_imageType := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    change 1 < ‖polar p‖ ∧ ‖polar p‖ < 2
    rw [polar_norm, abs_of_pos (by linarith [hp.1] : 0 < p 0)]
    exact ⟨hp.1, hp.2.1⟩
  · intro hy
    obtain ⟨r, t, hr, ht, hrsq, hx, hz⟩ :=
      CoordinateSeamsVolumes.polar_representation (y 0) (y 1) Real.pi
    have hnorm : ‖y‖ ^ 2 = (y 0)^2 + (y 1)^2 := by
      simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq y
    have hrnorm : r = ‖y‖ := by nlinarith [norm_nonneg y]
    have hrad : 1 < r ∧ r < 2 := hrnorm ▸ hy
    let p : E 2 := WithLp.toLp 2 ![r, t]
    refine ⟨p, ?_, ?_⟩
    · change 1 < r ∧ r < 2 ∧ 0 < t ∧ t < 4 * Real.pi
      exact ⟨hrad.1, hrad.2, by linarith [ht.1, Real.pi_pos],
        by linarith [ht.2, Real.pi_pos]⟩
    · ext k
      fin_cases k
      · exact hx
      · exact hz

lemma angular_images_periodic (i j : Fin 4) (hij : (j : ℝ) = (i : ℝ) + 2) :
    polar '' angularPiece j = polar '' angularPiece i := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    let q : E 2 := WithLp.toLp 2 ![p 0, p 1 - 2 * Real.pi]
    refine ⟨q, ?_, ?_⟩
    · change 1 < p 0 ∧ p 0 < 2 ∧ (i : ℝ) * Real.pi < p 1 - 2 * Real.pi ∧
        p 1 - 2 * Real.pi < ((i : ℝ) + 1) * Real.pi
      refine ⟨hp.1, hp.2.1, ?_, ?_⟩ <;>
        nlinarith [hp.2.2.1, hp.2.2.2]
    · ext k
      fin_cases k <;> simp [q, polar, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  · rintro ⟨p, hp, rfl⟩
    let q : E 2 := WithLp.toLp 2 ![p 0, p 1 + 2 * Real.pi]
    refine ⟨q, ?_, ?_⟩
    · change 1 < p 0 ∧ p 0 < 2 ∧ (j : ℝ) * Real.pi < p 1 + 2 * Real.pi ∧
        p 1 + 2 * Real.pi < ((j : ℝ) + 1) * Real.pi
      refine ⟨hp.1, hp.2.1, ?_, ?_⟩ <;>
        nlinarith [hp.2.2.1, hp.2.2.2]
    · ext k
      fin_cases k <;> simp [q, polar, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma first_two_images_disjoint : Disjoint
    (polar '' angularPiece 0) (polar '' angularPiece 1) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
  have hpD : p ∈ polarDomain 0 := by
    norm_num [angularPiece] at hp
    refine ⟨by linarith [hp.1], by simpa using hp.2.2.1, ?_⟩
    dsimp
    linarith [hp.2.2.2, Real.pi_pos]
  have hqD : q ∈ polarDomain 0 := by
    norm_num [angularPiece] at hq
    refine ⟨by linarith [hq.1], ?_, by simpa using hq.2.2.2⟩
    dsimp
    linarith [hq.2.2.1, Real.pi_pos]
  have hpq := CoordinateCharts.polar_injOn 0 hpD hqD (hpy.trans hqy.symm)
  exact Set.disjoint_left.mp (angularPieces_disjoint (by decide : (0 : Fin 4) ≠ 1))
    hp (hpq.symm ▸ hq)

lemma annulus_covered_by_first_two {y : E 2} (hy : y ∈ annulus) (hy1 : y 1 ≠ 0) :
    y ∈ polar '' angularPiece 0 ∪ polar '' angularPiece 1 := by
  obtain ⟨r, t, hr, ht, hrsq, hx, hz⟩ := CoordinateSeamsVolumes.polar_representation (y 0) (y 1) 0
  have hnorm : ‖y‖ ^ 2 = (y 0)^2 + (y 1)^2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq y
  have hrnorm : r = ‖y‖ := by nlinarith [norm_nonneg y]
  have hrad : 1 < r ∧ r < 2 := hrnorm ▸ hy
  have ht0 : t ≠ 0 := by intro h; subst t; simp at hz; exact hy1 hz.symm
  have ht2 : t ≠ 2 * Real.pi := by
    intro h; subst t
    rw [Real.sin_two_pi, mul_zero] at hz
    exact hy1 hz.symm
  have htpi : t ≠ Real.pi := by
    intro h; subst t
    rw [Real.sin_pi, mul_zero] at hz
    exact hy1 hz.symm
  let p : E 2 := WithLp.toLp 2 ![r, t]
  have hpval : polar p = y := by
    ext k
    fin_cases k
    · exact hx
    · exact hz
  by_cases hlt : t < Real.pi
  · left
    refine ⟨p, ?_, hpval⟩
    norm_num [angularPiece, p]
    exact ⟨hrad.1, hrad.2, lt_of_le_of_ne ht.1 (Ne.symm ht0), hlt⟩
  · right
    refine ⟨p, ?_, hpval⟩
    norm_num [angularPiece, p]
    exact ⟨hrad.1, hrad.2, lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm htpi),
      lt_of_le_of_ne (by simpa using ht.2) ht2⟩

theorem double_multiplicity : Specs.D04.C07.FiniteSheetCounting.double_multiplicityType := by
  intro y hy hy1
  have h20 := angular_images_periodic 0 2 (by norm_num)
  have h31 := angular_images_periodic 1 3 (by norm_num)
  have hd := first_two_images_disjoint
  rcases annulus_covered_by_first_two hy hy1 with h0 | h1
  · have h1 : y ∉ polar '' angularPiece 1 := Set.disjoint_left.mp hd h0
    have h2 : y ∈ polar '' angularPiece 2 := h20.symm ▸ h0
    have h3 : y ∉ polar '' angularPiece 3 := h31.symm ▸ h1
    have hf : Finset.univ.filter (fun i : Fin 4 => y ∈ polar '' angularPiece i) = {0, 2} := by
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
    change (Finset.univ.filter (fun i : Fin 4 => y ∈ polar '' angularPiece i)).card = 2
    rw [hf]
    decide
  · have h0 : y ∉ polar '' angularPiece 0 := Set.disjoint_right.mp hd h1
    have h2 : y ∉ polar '' angularPiece 2 := h20.symm ▸ h0
    have h3 : y ∈ polar '' angularPiece 3 := h31.symm ▸ h1
    have hf : Finset.univ.filter (fun i : Fin 4 => y ∈ polar '' angularPiece i) = {1, 3} := by
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
    change (Finset.univ.filter (fun i : Fin 4 => y ∈ polar '' angularPiece i)).card = 2
    rw [hf]
    decide

theorem double_jacobian : Specs.D04.C07.FiniteSheetCounting.double_jacobianType := by
  intro p hp
  have hpos : 0 < p 0 := by linarith [hp.1]
  rw [CoordinateCharts.polar_det]
  exact ⟨rfl, abs_of_pos hpos, hpos⟩

lemma closed_double_parameter_integral :
    RegionIntegrable (fun p : carrier doubleBox => p.val 0) ∧
    regionIntegral (fun p : carrier doubleBox => p.val 0) = 6 * Real.pi := by
  let Q := doubleBox
  let S := carrier Q
  have hj : Jordan S := ImproperExhaustions.jordan_box Q
  have hbS : Bornology.IsBounded S := carrier_isBounded Q
  have hone := LinearVolume.region_one_integrable hj
  have hr : RegionIntegrable (fun x : S => x.val 0) := by
    simpa only [mul_one] using SlicingAndMoments.weighted_integrable hbS
      (fun _ : S => (1 : ℝ)) hone (fun x => x 0) (PiLp.continuous_apply 2 _ 0)
  have h3 := SlicingAndMoments.region_smul hbS (fun _ : S => (1 : ℝ)) hone 3
  simp only [mul_one, regionIntegral_one] at h3
  have hsub := SlicingAndMoments.region_sub hbS (fun _ : S => (3 : ℝ))
    (fun x : S => x.val 0) h3.1 hr
  let v : E 2 := WithLp.toLp 2 ![3, 4 * Real.pi]
  let e := (Homeomorph.subLeft v).toOpenPartialHomeomorph
  have he (x : E 2) : e x = v - x := rfl
  have hreg : ContDiff ℝ 1 (fun x : E 2 => v - x) := contDiff_const.sub contDiff_id
  have heC : ContDiffOn ℝ 1 e e.source := hreg.contDiffOn
  have heiC : ContDiffOn ℝ 1 e.symm e.target := by
    have heis : (e.symm : E 2 → E 2) = fun x => v - x := by
      funext x
      have hi := e.right_inv (show x ∈ e.target from mem_univ x)
      rw [he] at hi
      simpa only [sub_sub_cancel] using congrArg (fun y : E 2 => v - y) hi
    rw [heis]
    exact hreg.contDiffOn
  have heS : e '' S = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · change 1 ≤ 3 - x 0 ∧ 3 - x 0 ≤ 2
        have hx0 := hx 0
        change 1 ≤ x 0 ∧ x 0 ≤ 2 at hx0
        constructor <;> linarith
      · change 0 ≤ 4 * Real.pi - x 1 ∧ 4 * Real.pi - x 1 ≤ 4 * Real.pi
        have hx1 := hx 1
        change 0 ≤ x 1 ∧ x 1 ≤ 4 * Real.pi at hx1
        constructor <;> linarith
    · intro hy
      refine ⟨v - y, ?_, ?_⟩
      · intro j
        fin_cases j
        · change 1 ≤ 3 - y 0 ∧ 3 - y 0 ≤ 2
          have hy0 := hy 0
          change 1 ≤ y 0 ∧ y 0 ≤ 2 at hy0
          constructor <;> linarith
        · change 0 ≤ 4 * Real.pi - y 1 ∧ 4 * Real.pi - y 1 ≤ 4 * Real.pi
          have hy1 := hy 1
          change 0 ≤ y 1 ∧ y 1 ≤ 4 * Real.pi at hy1
          constructor <;> linarith
      · change v - (v - y) = y
        abel
  have hdet (x : E 2) : |(fderiv ℝ e x).det| = 1 := by
    have hd : HasFDerivAt (fun y : E 2 => v - y)
        (-ContinuousLinearMap.id ℝ (E 2)) x := (hasFDerivAt_id x).const_sub v
    change |(fderiv ℝ (fun y : E 2 => v - y) x).det| = 1
    rw [hd.fderiv]
    change |LinearMap.det (-(LinearMap.id : E 2 →ₗ[ℝ] E 2))| = 1
    rw [show -(LinearMap.id : E 2 →ₗ[ℝ] E 2) = (-1 : ℝ) • LinearMap.id by simp,
      LinearMap.det_smul]
    simp
  have hfi : RegionIntegrable (fun y : e '' S => y.val 0) := heS.symm ▸ hr
  have hs := (RegionSubstitution.region_substitution e heC heiC S hj
    hbS.isCompact_closure (subset_univ _) (fun y : e '' S => y.val 0) hfi.1).2.2 (Or.inl hfi)
  simp only [hdet, mul_one] at hs
  change regionIntegral (fun y : e '' S => y.val 0) =
    regionIntegral (fun x : S => 3 - x.val 0) at hs
  rw [heS] at hs
  have hvQ : volume S = 4 * Real.pi := by
    have hbridge := CoordinateSeamsVolumes.rectangle_integral_bridge (by decide : 0 < 2)
      Q (fun _ => (1 : ℝ)) hone
    have hext : zeroExtension (fun _ : S => (1 : ℝ)) = JordanRegions.indicator S := by
      funext x
      by_cases hx : x ∈ S <;> simp [zeroExtension,
        Specs.D04.C06.JordanRegions.Model.zeroExtension, JordanRegions.indicator,
        Specs.D04.C06.JordanRegions.Model.indicator, hx]
    have hcongr : EqOn (zeroExtension (fun _ : S => (1 : ℝ))) (fun _ => 1) (carrier Q) :=
      fun x hx => zeroExtension_apply _ ⟨x, hx⟩
    have hhi := (integrable_congr hcongr).mp hbridge.1
    have hv := lowerIntegral_congr hcongr
    change lowerIntegral _ Q = lowerIntegral _ Q at hv
    have hconst := (constant_integrals Q 1).1
    have he := hbridge.2
    change lowerIntegral _ Q = volume S at he
    rw [hv, hconst] at he
    have hcont : content Q = 4 * Real.pi := by
      norm_num [Q, doubleBox, content, Specs.D04.C06.DarbouxIntegral.Model.content,
        Fin.prod_univ_two]
    rw [hcont] at he
    linarith
  refine ⟨hr, ?_⟩
  rw [h3.2, hvQ] at hsub
  linarith [hsub.2]

theorem double_parameter_integral :
    Specs.D04.C07.FiniteSheetCounting.double_parameter_integralType := by
  have hclosed := closed_double_parameter_integral
  have hj : Jordan doubleDomain := by
    rw [doubleDomain_eq_interior]
    exact jordan_open_box (by decide) doubleBox
  have hinc : doubleDomain ⊆ carrier doubleBox := by
    rw [doubleDomain_eq_interior]; exact interior_subset
  have hi := AbsoluteConvergence.region_restrict (f := fun x : E 2 => x 0) hclosed.1 hj hinc
  have hext := CoordinateSeamsVolumes.extend_region hinc (carrier_isBounded doubleBox)
    (fun p : doubleDomain => p.val 0) hi
  have hb : RegionBounded (fun p : carrier doubleBox => p.val 0) := hclosed.1.1
  have hm := CoordinateSeamsVolumes.region_modification (by decide : 0 < 2)
    (fun p : carrier doubleBox => zeroExtension (fun q : doubleDomain => q.val 0) p)
    (fun p : carrier doubleBox => p.val 0) hext.1 hb
    (CoordinateSeamsVolumes.box_faces_contentZero doubleBox) (by
      intro p hp
      have hpD : p.val ∈ doubleDomain := by
        rw [doubleDomain_eq_interior]
        by_contra hn
        exact hp ⟨p.property, hn⟩
      exact zeroExtension_apply _ ⟨p.val, hpD⟩)
  exact ⟨hi, hext.2.symm.trans (hm.2.symm.trans hclosed.2)⟩

theorem double_noninjective : Specs.D04.C07.FiniteSheetCounting.double_noninjectiveType := by
  let p : E 2 := WithLp.toLp 2 ![(3 : ℝ) / 2, Real.pi / 2]
  let q : E 2 := WithLp.toLp 2 ![(3 : ℝ) / 2, Real.pi / 2 + 2 * Real.pi]
  refine ⟨p, ?_, q, ?_, ?_, ?_, ?_, ?_⟩
  · change 1 < (3 : ℝ) / 2 ∧ (3 : ℝ) / 2 < 2 ∧ 0 < Real.pi / 2 ∧
      Real.pi / 2 < 4 * Real.pi
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  · change 1 < (3 : ℝ) / 2 ∧ (3 : ℝ) / 2 < 2 ∧ 0 < Real.pi / 2 + 2 * Real.pi ∧
      Real.pi / 2 + 2 * Real.pi < 4 * Real.pi
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  · intro h
    have := congrArg (fun x : E 2 => x 1) h
    change Real.pi / 2 = Real.pi / 2 + 2 * Real.pi at this
    linarith [Real.pi_pos]
  · ext i
    fin_cases i <;> simp [p, q, polar, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · change (3 : ℝ) / 2 ≠ 0; norm_num
  · change (3 : ℝ) / 2 ≠ 0; norm_num

end D04.FiniteSheetCounting
