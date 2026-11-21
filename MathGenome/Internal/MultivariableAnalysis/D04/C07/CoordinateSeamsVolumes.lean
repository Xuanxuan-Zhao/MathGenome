import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateSeamsVolumes
import MathGenome.Internal.MultivariableAnalysis.D04.C07.CoordinateCharts
import MathGenome.Internal.MultivariableAnalysis.D04.C07.LinearVolume
import MathGenome.Internal.MultivariableAnalysis.D04.C06.AbsoluteConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
open Set Function Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace D04.CoordinateSeamsVolumes
open Darboux JordanRegions NullCovers
open Specs.D04.C07.CoordinateCharts.Model
open Specs.D04.C07.CoordinateSeamsVolumes.Model

/-- The entire boundary of a closed rectangle has content zero, including
when the rectangle is degenerate. -/
lemma box_faces_contentZero {n : ℕ} (Q : Box n) : ContentZero (faces Q) := by
  classical
  let F : Finset (Fin n × ℝ) :=
    Finset.univ.biUnion (fun i => {(i, Q.lower i), (i, Q.upper i)})
  apply contentZero_mono (T := ⋃ p ∈ F, coordinateFace Q p.1 p.2) ?_
    (finite_faces_contentZero Q F)
  intro x hx
  have ho : x ∉ openCarrier Q := by
    simpa only [JordanRegions.interior_carrier] using hx.2
  obtain ⟨i, hi⟩ : ∃ i, ¬ (Q.lower i < x i ∧ x i < Q.upper i) := by
    simpa only [openCarrier, Specs.D04.C06.NullCovers.Model.openCarrier,
      mem_ofPred_eq, not_forall] using ho
  have heq : x i = Q.lower i ∨ x i = Q.upper i := by
    have hb := hx.1 i
    rcases not_and_or.mp hi with h | h
    · exact Or.inl (le_antisymm (not_lt.mp h) hb.1)
    · exact Or.inr (le_antisymm hb.2 (not_lt.mp h))
  rcases heq with h | h
  · exact mem_iUnion.mpr ⟨(i, Q.lower i), mem_iUnion.mpr ⟨by simp only [F, Finset.mem_biUnion]; exact ⟨i, Finset.mem_univ _, by simp⟩, hx.1, h⟩⟩
  · exact mem_iUnion.mpr ⟨(i, Q.upper i), mem_iUnion.mpr ⟨by simp only [F, Finset.mem_biUnion]; exact ⟨i, Finset.mem_univ _, by simp⟩, hx.1, h⟩⟩

/-- A reusable region version of bounded content-zero modification. Both
functions have their actual zero extensions compared on an enclosing box. -/
lemma region_modification {n : ℕ} (hn : 0 < n) {S Z : Set (E n)}
    (f g : S → ℝ) (hf : RegionIntegrable f) (hg : RegionBounded g)
    (hZ : ContentZero Z) (heq : ∀ x : S, (x : E n) ∉ Z → f x = g x) :
    RegionIntegrable g ∧ regionIntegral g = regionIntegral f := by
  obtain ⟨Q, hQ, hfi⟩ := hf.2
  obtain ⟨hgi, he⟩ := ExceptionalSets.modification_contentZero hn hfi
    (zeroExtension_bounded g hg Q) hZ (fun x _ hxZ => by
      by_cases hx : x ∈ S
      · simpa only [zeroExtension_apply f ⟨x, hx⟩, zeroExtension_apply g ⟨x, hx⟩]
          using heq ⟨x, hx⟩ hxZ
      · simp only [zeroExtension_of_not_mem _ hx])
  have hi : RegionIntegrable g := ⟨hg, Q, hQ, hgi⟩
  exact ⟨hi, (integral_eq_on_enclosing_box g hi hQ hgi).trans
    (he.trans (integral_eq_on_enclosing_box f hf hQ hfi).symm)⟩

theorem face_modification : Specs.D04.C07.CoordinateSeamsVolumes.face_modificationType := by
  intro n hn Q f g hf hg he
  apply region_modification hn f g hf hg (box_faces_contentZero Q)
  intro x hx
  exact he x (by by_contra h; exact hx ⟨x.property, h⟩)

/-- Ambient discontinuities of an integrable zero extension are null. No
Jordan hypothesis on its original domain is needed. -/
lemma null_zeroExtension_discontinuities {n : ℕ} (hn : 0 < n)
    {S : Set (E n)} {f : S → ℝ} (hf : RegionIntegrable f) :
    Null {x | ¬ ContinuousAt (zeroExtension f) x} := by
  have hb : Bornology.IsBounded S := encloses_bounded hf.2.choose_spec.1
  have ho := (RegionSubstitution.region_integrable_iff_open isOpen_univ
    (subset_univ S) hb f hf.1).mp hf
  have hnul := RiemannSubstitution.null_ambient_discontinuities hn ho
  rwa [RegionSubstitution.zeroExtension_nested (subset_univ S) f] at hnul

/-- Bounded pullbacks under a regular chart are integrable on a *closed*
parameter rectangle if the chart is regular throughout its interior. This
uses the inverse chart's null preservation only on its true open domain. -/
lemma integrable_on_closed_parameter_box {n : ℕ} (hn : 0 < n)
    (Q : Box n) (e : OpenPartialHomeomorph (E n) (E n))
    (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hQe : interior (carrier Q) ⊆ e.source)
    (J : E n → ℝ) (hJ : ContinuousOn J (carrier Q))
    {S : Set (E n)} (f : S → ℝ) (hf : RegionIntegrable f)
    (g : carrier Q → ℝ) (hg : RegionBounded g)
    (heq : ∀ x : carrier Q, (x : E n) ∈ interior (carrier Q) →
      g x = zeroExtension f (e x) * J x) : RegionIntegrable g := by
  have hD := null_zeroExtension_discontinuities hn hf
  let D : Set (E n) := e.target ∩ {y | ¬ ContinuousAt (zeroExtension f) y}
  have hN : Null (e.symm '' D) := NullPreservation.c1_null_image hn e.target e.symm
    e.open_target ((crOn_iff_contDiffOn 1 _ _ e.open_target).mpr hei)
      D inter_subset_left (null_mono inter_subset_right hD)
  apply integrable_of_null_relative_discontinuities hn (ImproperExhaustions.jordan_box Q) g hg
  apply null_mono (T := faces Q ∪ e.symm '' D) ?_
    (JordanRegions.null_union (contentZero_null (box_faces_contentZero Q)) hN)
  rintro x ⟨hx, hdisc⟩
  by_cases hi : x ∈ interior (carrier Q)
  · right
    have hs := hQe hi
    refine ⟨e x, ⟨e.map_source hs, ?_⟩, e.left_inv hs⟩
    intro hc
    have hcomp : ContinuousAt (fun y => zeroExtension f (e y) * J y) x :=
      (hc.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hs))).mul
        ((hJ x hx).continuousAt (mem_interior_iff_mem_nhds.mp hi))
    have hlocal : (fun y : carrier Q => g y) =ᶠ[𝓝 ⟨x, hx⟩]
        (fun y : carrier Q => zeroExtension f (e y) * J y) := by
      filter_upwards [(isOpen_interior.preimage continuous_subtype_val).mem_nhds hi] with y hy
      exact heq y hy
    have hcsub : ContinuousAt (fun y : carrier Q => zeroExtension f (e y) * J y) ⟨x, hx⟩ :=
      hcomp.comp (f := (Subtype.val : carrier Q → E n)) (x := ⟨x, hx⟩)
        continuous_subtype_val.continuousAt
    exact hdisc (hcsub.congr hlocal.symm)
  · exact Or.inl ⟨hx, hi⟩

/-- On the interior of each full coordinate rectangle the already proved
regular chart is applicable. The radius and the angular endpoint faces are
handled by the general closed-rectangle lemma above. -/
theorem polar_integrability : Specs.D04.C07.CoordinateSeamsVolumes.polar_integrabilityType := by
  intro R α hR S _ f hf g hg
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.polar_chart α).2
  apply integrable_on_closed_parameter_box (by decide) (polarBox R α hR.le) e hei
    (J := fun p => p 0) (f := f) (g := g)
  · intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2⟩
  · exact (EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn
  · exact hf
  · exact hg.1
  · intro x hx
    simpa only [he] using hg.2 x hx

theorem cylindrical_integrability :
    Specs.D04.C07.CoordinateSeamsVolumes.cylindrical_integrabilityType := by
  intro R α a b hR hab S _ f hf g hg
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.cylindrical_chart α).2
  apply integrable_on_closed_parameter_box (by decide) (cylinderBox R α a b hR.le hab)
    e hei (J := fun p => p 0) (f := f) (g := g)
  · intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2⟩
  · exact (EuclideanSpace.proj (0 : Fin 3)).continuous.continuousOn
  · exact hf
  · exact hg.1
  · intro x hx
    simpa only [he] using hg.2 x hx

theorem spherical_integrability :
    Specs.D04.C07.CoordinateSeamsVolumes.spherical_integrabilityType := by
  intro R α hR S _ f hf g hg
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.spherical_chart α).2
  refine integrable_on_closed_parameter_box (by decide) (sphericalBox R α hR.le)
    e hei ?_ (fun p => (p 0)^2 * Real.sin (p 1)) ?_ f hf g hg.1 ?_
  · intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2, (hp 2).1, (hp 2).2⟩
  · exact (((EuclideanSpace.proj (0 : Fin 3)).continuous.pow 2).mul
      (Real.continuous_sin.comp (EuclideanSpace.proj (1 : Fin 3)).continuous)).continuousOn
  · intro x hx
    simpa only [he] using hg.2 x hx

/-- Continuous Jacobians are bounded on the compact parameter rectangle;
therefore the natural (unmodified) pullback satisfies the boundedness premise
of the three integrability theorems. -/
lemma weighted_pullback_bounded {n : ℕ} (Q : Box n) {S : Set (E n)}
    (f : S → ℝ) (hf : RegionBounded f) (Φ : E n → E n)
    (J : E n → ℝ) (hJ : ContinuousOn J (carrier Q)) :
    RegionBounded (fun p : carrier Q => zeroExtension f (Φ p) * J p) := by
  obtain ⟨M, hM⟩ := RegionSubstitution.extended_bounded (U := (univ : Set (E n))) f hf
  obtain ⟨N, hN⟩ := (DiscontinuityCriterion.carrier_compact Q).bddAbove_image hJ.norm
  refine ⟨max M 0 * max N 0, fun p => ?_⟩
  rw [norm_mul]
  apply mul_le_mul
  · exact (hM ⟨Φ p, mem_univ _⟩).trans (le_max_left _ _)
  · exact (hN (mem_image_of_mem _ p.property)).trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact le_max_right _ _

/-- The arbitrary-basis result uses the actual column determinant, with no
orthogonality hypothesis, and also records the coordinate map itself. -/
theorem basis_factor : Specs.D04.C07.CoordinateSeamsVolumes.basis_factorType := by
  intro n b S hS
  have h := LinearVolume.basis_substitution b S hS
  have hd := LinearVolume.basis_determinant b
  dsimp only at hd h ⊢
  simpa only [hd] using h

theorem zero_radius : Specs.D04.C07.CoordinateSeamsVolumes.zero_radiusType := by
  constructor
  · intro n hn
    have hz := LinearVolume.contentZero_jordan_volume hn ({0} : Set (E n))
      (isCompact_singleton.isBounded) (singleton_contentZero hn 0)
    simpa only [Metric.closedBall_zero, Metric.ball_zero, volume_empty] using
      And.intro hz.1 (And.intro hz.2 (And.intro (jordan_empty n) (volume_empty n)))
  · intro A
    have hz := LinearVolume.contentZero_jordan_volume (by decide) ({0} : Set (E 3))
      (isCompact_singleton.isBounded) (singleton_contentZero (by decide) 0)
    constructor
    · simp only [Metric.ball_zero, image_empty, volume_empty]
    · simpa only [Metric.closedBall_zero, image_singleton, map_zero] using hz.2

/-- Global C¹ maps send the entire compact rectangle boundary to a set
of content zero; no injectivity or nonzero derivative on that boundary is
required. This applies to coordinate singularities as well as seams. -/
lemma image_faces_contentZero {n : ℕ} (hn : 0 < n) (Q : Box n)
    (Φ : E n → E n) (hΦ : ContDiff ℝ 1 Φ) : ContentZero (Φ '' faces Q) := by
  apply NullPreservation.c1_contentZero_image hn univ Φ isOpen_univ
    ((crOn_iff_contDiffOn 1 _ _ isOpen_univ).mpr hΦ.contDiffOn)
    (faces Q) (subset_univ _) ((DiscontinuityCriterion.carrier_compact Q).diff isOpen_interior)
    (box_faces_contentZero Q)

theorem polar_seams : Specs.D04.C07.CoordinateSeamsVolumes.polar_seamsType := by
  intro R α hR
  apply contentZero_mono (image_mono ?_)
    (image_faces_contentZero (by decide) (polarBox R α hR) polar CoordinateCharts.polar_contDiff)
  rintro p ⟨hp, h⟩
  refine ⟨hp, ?_⟩
  rw [interior_carrier]
  intro hi
  rcases h with h | h | h
  · have hh := (hi 0).1; change 0 < p 0 at hh; linarith
  · have hh := (hi 1).1; change α < p 1 at hh; linarith
  · have hh := (hi 1).2; change p 1 < α + 2 * Real.pi at hh; linarith

theorem cylindrical_seams : Specs.D04.C07.CoordinateSeamsVolumes.cylindrical_seamsType := by
  intro R α a b hR hab
  apply contentZero_mono (image_mono ?_)
    (image_faces_contentZero (by decide) (cylinderBox R α a b hR hab)
      cylindrical CoordinateCharts.cylindrical_contDiff)
  rintro p ⟨hp, h⟩
  refine ⟨hp, ?_⟩
  rw [interior_carrier]
  intro hi
  rcases h with h | h | h
  · have hh := (hi 0).1; change 0 < p 0 at hh; linarith
  · have hh := (hi 1).1; change α < p 1 at hh; linarith
  · have hh := (hi 1).2; change p 1 < α + 2 * Real.pi at hh; linarith

theorem spherical_seams : Specs.D04.C07.CoordinateSeamsVolumes.spherical_seamsType := by
  intro R α hR
  apply contentZero_mono (image_mono ?_)
    (image_faces_contentZero (by decide) (sphericalBox R α hR)
      spherical CoordinateCharts.spherical_contDiff)
  rintro p ⟨hp, h⟩
  refine ⟨hp, ?_⟩
  rw [interior_carrier]
  intro hi
  rcases h with h | h | h | h | h
  · have hh := (hi 0).1; change 0 < p 0 at hh; linarith
  · have hh := (hi 1).1; change 0 < p 1 at hh; linarith
  · have hh := (hi 1).2; change p 1 < Real.pi at hh; linarith
  · have hh := (hi 2).1; change α < p 2 at hh; linarith
  · have hh := (hi 2).2; change p 2 < α + 2 * Real.pi at hh; linarith

/-- Content-zero compact sets have uniformly small finite-cover
neighborhoods. Compactness is essential for the single positive radius. -/
lemma vanishingNeighborhoodContent_of_compact {n : ℕ} {Z : Set (E n)}
    (hZ : IsCompact Z) (hz : ContentZero Z) : VanishingNeighborhoodContent Z := by
  intro ε hε
  obtain ⟨ι, hι, Q, hQ, hsum⟩ := (contentZero_iff_openContentZero Z).mp hz ε hε
  let := hι
  obtain ⟨ρ, hρ, hρQ⟩ := hZ.exists_thickening_subset_open
    (isOpen_iUnion (fun i => isOpen_openCarrier (Q i))) hQ
  exact ⟨ρ, hρ, ι, hι, Q, hρQ, hsum⟩

lemma image_faces_vanishingNeighborhoodContent {n : ℕ} (hn : 0 < n)
    (Q : Box n) (Φ : E n → E n) (hΦ : ContDiff ℝ 1 Φ) :
    VanishingNeighborhoodContent (Φ '' faces Q) :=
  vanishingNeighborhoodContent_of_compact
    (((DiscontinuityCriterion.carrier_compact Q).diff isOpen_interior).image hΦ.continuous)
    (image_faces_contentZero hn Q Φ hΦ)

theorem cartesian_neighborhoods :
    Specs.D04.C07.CoordinateSeamsVolumes.cartesian_neighborhoodsType :=
  ⟨fun R α hR => image_faces_vanishingNeighborhoodContent (by decide) _ _
      CoordinateCharts.polar_contDiff,
   fun R α a b hR hab => image_faces_vanishingNeighborhoodContent (by decide) _ _
      CoordinateCharts.cylindrical_contDiff,
   fun R α hR => image_faces_vanishingNeighborhoodContent (by decide) _ _
      CoordinateCharts.spherical_contDiff⟩

/-- For an indicator the lower cell value records whether the *whole*
closed cell is contained in the region. -/
lemma indicator_cellInfimum {n : ℕ} (S : Set (E n)) {Q : Box n}
    (P : Grid Q) (c : CellIndex P) :
    cellInfimum (JordanRegions.indicator S) P c = if cell P c ⊆ S then 1 else 0 := by
  classical
  split_ifs with h
  · change sInf (JordanRegions.indicator S '' cell P c) = 1
    have he : JordanRegions.indicator S '' cell P c = {1} := by
      apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
      refine ⟨(cell_nonempty P c).image _, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      simp [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, h hx]
    rw [he, csInf_singleton]
  · simp only [Set.subset_def, not_forall] at h
    obtain ⟨x, hx, hxS⟩ := h
    apply le_antisymm
    · have hh := cellInfimum_le (JordanRegions.indicator S) (indicator_bounded S Q) P c hx
      simpa [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS] using hh
    · apply le_csInf ((cell_nonempty P c).image _)
      rintro y ⟨x, _, rfl⟩
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma indicator_cellSupremum {n : ℕ} (S : Set (E n)) {Q : Box n}
    (P : Grid Q) (c : CellIndex P) :
    cellSupremum (JordanRegions.indicator S) P c =
      if ∃ x ∈ cell P c, x ∈ S then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨x, hx, hxS⟩ := h
    apply le_antisymm
    · apply csSup_le ((cell_nonempty P c).image _)
      rintro y ⟨x, _, rfl⟩
      by_cases hxS : x ∈ S <;>
        simp [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS]
    · have hh := le_cellSupremum (JordanRegions.indicator S) (indicator_bounded S Q) P c hx
      simpa [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS] using hh
  · change sSup (JordanRegions.indicator S '' cell P c) = 0
    have he : JordanRegions.indicator S '' cell P c = {0} := by
      apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
      refine ⟨(cell_nonempty P c).image _, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hxS : x ∉ S := fun hh => h ⟨x, hx, hh⟩
      simp [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hxS]
    rw [he, csSup_singleton]

/-- Elementary volume comparison for a Jordan set: disjoint interior grid
cells bound its coordinate Lebesgue outer measure below, and all meeting
closed cells bound it above. This proves the bridge needed for the volume
calculations, rather than assuming Riemann/Lebesgue agreement. -/
lemma jordan_volume_eq_coordinate_measure {n : ℕ} {S : Set (E n)} (hS : Jordan S) :
    ENNReal.ofReal (volume S) = MeasureTheory.volume (WithLp.ofLp '' S) := by
  classical
  by_cases hne : S.Nonempty
  swap
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he, volume_empty]
  let Q := enclosingBox S
  have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
  have hi := jordan_integrable_on_box hS hQ
  have hq : Nondegenerate Q := by
    obtain ⟨x, hx⟩ := hne
    exact fun i => ((encloses_open hQ (subset_closure hx) i).1).trans
      ((encloses_open hQ (subset_closure hx) i).2)
  let μS := MeasureTheory.volume (WithLp.ofLp '' S)
  have hfin : μS ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((MeasureTheory.measure_mono (image_mono (encloses_subset hQ))).trans_eq (coordinate_volume Q))
  have hlow (P : Grid Q) :
      ENNReal.ofReal (lowerSum (JordanRegions.indicator S) P) ≤ μS := by
    let F : Finset (CellIndex P) := Finset.univ.filter (fun c => cell P c ⊆ S)
    have hsum : lowerSum (JordanRegions.indicator S) P = ∑ c ∈ F, cellContent P c := by
      simp only [lowerSum, Specs.D04.C06.DarbouxIntegral.Model.lowerSum,
        indicator_cellInfimum, ite_mul, one_mul, zero_mul]
      simp [F, Finset.sum_filter]
    have hvol : MeasureTheory.volume (⋃ c : F, DiscontinuityCriterion.openCoordinateCell P c) =
        ENNReal.ofReal (∑ c ∈ F, cellContent P c) := by
      rw [MeasureTheory.measure_iUnion
        (fun c d h => DiscontinuityCriterion.openCoordinateCell_disjoint P
          (Subtype.val_injective.ne h))
        (fun _ => MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)), tsum_fintype]
      simp_rw [DiscontinuityCriterion.openCoordinateCell_volume]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => cellContent_nonneg _ _), Finset.sum_coe_sort]
    rw [hsum, ← hvol]
    apply MeasureTheory.measure_mono
    intro y hy
    obtain ⟨c, hc⟩ := mem_iUnion.mp hy
    have hx : WithLp.toLp 2 y ∈ cell P c :=
      fun i => ⟨(hc i (mem_univ i)).1.le, (hc i (mem_univ i)).2.le⟩
    exact ⟨WithLp.toLp 2 y, (Finset.mem_filter.mp c.property).2 hx, rfl⟩
  have hupp (P : Grid Q) :
      μS ≤ ENNReal.ofReal (upperSum (JordanRegions.indicator S) P) := by
    let F : Finset (CellIndex P) := Finset.univ.filter (fun c => ∃ x ∈ cell P c, x ∈ S)
    have hsum : upperSum (JordanRegions.indicator S) P = ∑ c ∈ F, cellContent P c := by
      simp only [upperSum, Specs.D04.C06.DarbouxIntegral.Model.upperSum,
        indicator_cellSupremum, ite_mul, one_mul, zero_mul]
      simp [F, Finset.sum_filter]
    have hcover : WithLp.ofLp '' S ⊆ ⋃ c : F, WithLp.ofLp '' cell P c := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := mem_iUnion.mp ((cells_cover Q hq P) ▸ encloses_subset hQ hx)
      exact mem_iUnion.mpr ⟨⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hc, hx⟩⟩,
        x, hc, rfl⟩
    calc
      μS ≤ MeasureTheory.volume (⋃ c : F, WithLp.ofLp '' cell P c) := MeasureTheory.measure_mono hcover
      _ ≤ ∑' c : F, MeasureTheory.volume (WithLp.ofLp '' cell P c) := MeasureTheory.measure_iUnion_le _
      _ = ENNReal.ofReal (∑ c ∈ F, cellContent P c) := by
        simp_rw [show ∀ c : F, MeasureTheory.volume (WithLp.ofLp '' cell P c) =
          ENNReal.ofReal (cellContent P c) from fun c => coordinate_volume (cellBox P c)]
        rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => cellContent_nonneg _ _),
          Finset.sum_coe_sort]
      _ = _ := congrArg ENNReal.ofReal hsum.symm
  have hreal : volume S = μS.toReal := by
    apply le_antisymm
    · exact (lowerIntegral_isLUB _ Q hi.1).2 (by
        rintro _ ⟨P, rfl⟩
        have h := ENNReal.toReal_mono hfin (hlow P)
        rw [ENNReal.toReal_ofReal (by
          unfold lowerSum Specs.D04.C06.DarbouxIntegral.Model.lowerSum
          apply Finset.sum_nonneg; intro c _
          change 0 ≤ cellInfimum (JordanRegions.indicator S) P c * cellContent P c
          exact mul_nonneg (by rw [indicator_cellInfimum]; split_ifs <;> norm_num)
            (cellContent_nonneg P c))] at h
        exact h)
    · change μS.toReal ≤ lowerIntegral _ Q
      change μS.toReal ≤ Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
        (JordanRegions.indicator S) Q
      rw [hi.2]
      exact (upperIntegral_isGLB _ Q hi.1).2 (by
        rintro _ ⟨P, rfl⟩
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupp P)
        rw [ENNReal.toReal_ofReal (by
          unfold upperSum Specs.D04.C06.DarbouxIntegral.Model.upperSum
          apply Finset.sum_nonneg; intro c _
          change 0 ≤ cellSupremum (JordanRegions.indicator S) P c * cellContent P c
          exact mul_nonneg (by rw [indicator_cellSupremum]; split_ifs <;> norm_num)
            (cellContent_nonneg P c))] at h
        exact h)
  rw [hreal, ENNReal.ofReal_toReal hfin]

/-- The coordinate copy uses the same normalization of Euclidean volume. -/
lemma coordinate_measure_eq_euclidean {n : ℕ} (S : Set (E n)) :
    MeasureTheory.volume (WithLp.ofLp '' S) = MeasureTheory.volume S := by
  have hm : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)) := PiLp.volume_preserving_toLp (Fin n)
  have he : WithLp.ofLp '' S = (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨WithLp.toLp 2 x, hx, rfl⟩
  rw [he]
  exact hm.measure_preimage_equiv S

lemma jordan_volume_eq_measure {n : ℕ} {S : Set (E n)} (hS : Jordan S) :
    ENNReal.ofReal (volume S) = MeasureTheory.volume S :=
  (jordan_volume_eq_coordinate_measure hS).trans (coordinate_measure_eq_euclidean S)

/-- Sphere nullity is used only to establish the Jordan property; the
Riemann value is subsequently identified by the proved volume comparison. -/
lemma sphere_contentZero {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ContentZero (Metric.sphere (0 : E n) R) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply compact_null_contentZero _ (isCompact_sphere 0 R)
  apply NullPreservation.null_of_coordinate_volume_zero hn
  rw [coordinate_measure_eq_euclidean]
  exact MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume 0 R

lemma balls_jordan {n : ℕ} (hn : 0 < n) (R : ℝ) :
    Jordan (Metric.closedBall (0 : E n) R) ∧ Jordan (Metric.ball (0 : E n) R) := by
  have hz := sphere_contentZero hn R
  constructor
  · exact (jordan_iff_boundary hn _ Metric.isBounded_closedBall).mpr
      (contentZero_mono Metric.frontier_closedBall_subset_sphere hz)
  · exact (jordan_iff_boundary hn _ Metric.isBounded_ball).mpr
      (contentZero_mono Metric.frontier_ball_subset_sphere hz)

lemma volume_eq_of_measure {n : ℕ} {S : Set (E n)} (hS : Jordan S)
    {c : ℝ} (hc : 0 ≤ c) (hv : MeasureTheory.volume S = ENNReal.ofReal c) : volume S = c := by
  have h := congrArg ENNReal.toReal ((jordan_volume_eq_measure hS).trans hv)
  simpa only [ENNReal.toReal_ofReal (volume_nonneg hS), ENNReal.toReal_ofReal hc] using h

theorem disk_area : Specs.D04.C07.CoordinateSeamsVolumes.disk_areaType := by
  intro R hR
  obtain ⟨hC, hB⟩ := balls_jordan (n := 2) (by decide) R
  refine ⟨hC, volume_eq_of_measure hC (by positivity) ?_,
    hB, volume_eq_of_measure hB (by positivity) ?_⟩
  · rw [EuclideanSpace.volume_closedBall_fin_two, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hR]
    exact mul_comm _ _
  · rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hR]
    exact mul_comm _ _

theorem ball_volume : Specs.D04.C07.CoordinateSeamsVolumes.ball_volumeType := by
  intro R hR
  obtain ⟨hC, hB⟩ := balls_jordan (n := 3) (by decide) R
  have he : ENNReal.ofReal R ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) =
      ENNReal.ofReal (4 * Real.pi * R^3 / 3) := by
    rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (pow_nonneg hR 3)]
    congr 1; ring
  exact ⟨hC, volume_eq_of_measure hC (by positivity)
      ((EuclideanSpace.volume_closedBall_fin_three 0 R).trans he),
    hB, volume_eq_of_measure hB (by positivity)
      ((EuclideanSpace.volume_ball_fin_three 0 R).trans he)⟩

theorem ellipsoid_volume : Specs.D04.C07.CoordinateSeamsVolumes.ellipsoid_volumeType := by
  intro R hR A
  obtain ⟨_, _, hB, hv⟩ := ball_volume R hR
  have h := LinearVolume.linear_volume A.toLinearMap (Metric.ball (0 : E 3) R) hB
  exact ⟨h.1, by simpa only [hv, LinearEquiv.coe_coe] using h.2⟩

/-- Enlarging a bounded integration domain after zero extension preserves
both Riemann integrability and the integral; the domains need not be Jordan. -/
lemma extend_region {n : ℕ} {S T : Set (E n)} (hST : S ⊆ T)
    (hT : Bornology.IsBounded T) (f : S → ℝ) (hf : RegionIntegrable f) :
    RegionIntegrable (fun y : T => zeroExtension f y) ∧
      regionIntegral (fun y : T => zeroExtension f y) = regionIntegral f := by
  let F : T → ℝ := fun y => zeroExtension f y
  have hbS : Bornology.IsBounded S := hT.subset hST
  have hbF : RegionBounded F := RegionSubstitution.extended_bounded f hf.1
  have ho := (RegionSubstitution.region_integrable_iff_open isOpen_univ
    (subset_univ S) hbS f hf.1).mp hf
  have hext := RegionSubstitution.zeroExtension_nested hST f
  have heq : (fun y : (univ : Set (E n)) => zeroExtension F y) =
      (fun y : (univ : Set (E n)) => zeroExtension f y) :=
    funext (fun y => congrFun hext y)
  have hoF : OpenIntegrable (fun y : (univ : Set (E n)) => zeroExtension F y) := heq.symm ▸ ho
  have hiF := (RegionSubstitution.region_integrable_iff_open isOpen_univ
    (subset_univ T) hT F hbF).mpr hoF
  refine ⟨hiF, ?_⟩
  calc
    regionIntegral F = openIntegral (fun y : (univ : Set (E n)) => zeroExtension F y) :=
      RegionSubstitution.region_integral_eq_open (subset_univ T) F hiF hoF
    _ = openIntegral (fun y : (univ : Set (E n)) => zeroExtension f y) := congrArg openIntegral heq
    _ = regionIntegral f :=
      (RegionSubstitution.region_integral_eq_open (subset_univ S) f hf ho).symm

/-- The discarded Riemann integral tends to zero under compact Jordan
truncations covering all but a content-zero set. The argument uses continuity
of ordinary volume from above and the elementary bound M·volume; it never
identifies a general Riemann function with a measure integral. -/
lemma discarded_integral_tendsto_zero {n : ℕ} {T Z : Set (E n)}
    (hT : IsCompact T) (hjT : Jordan T) (hZ : ContentZero Z)
    (K : ℕ → Set (E n)) (hK : ∀ j, IsCompact (K j) ∧ Jordan (K j) ∧ K j ⊆ T)
    (hKm : Monotone K) (hcover : T \ ⋃ j, K j ⊆ Z)
    (F : E n → ℝ) (hF : RegionIntegrable (fun x : T => F x)) :
    Tendsto (fun j => regionIntegral (fun x : (T \ K j : Set (E n)) => F x)) atTop (𝓝 0) := by
  have hjD (j : ℕ) : Jordan (T \ K j) := jordan_diff hjT (hK j).2.1
  have hzμ : MeasureTheory.volume Z = 0 := by
    rw [← coordinate_measure_eq_euclidean]
    exact NullPreservation.coordinate_volume_zero_of_null (contentZero_null hZ)
  have hiμ : MeasureTheory.volume (⋂ j, T \ K j) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hzμ
    intro x hx
    apply hcover
    exact ⟨(mem_iInter.mp hx 0).1, by
      intro h; obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact (mem_iInter.mp hx j).2 hj⟩
  have hm : Antitone (fun j => T \ K j) := fun i j hij =>
    fun x hx => ⟨hx.1, fun hxK => hx.2 (hKm hij hxK)⟩
  have hμ := MeasureTheory.tendsto_measure_iInter_atTop
    (fun j => (hT.isClosed.measurableSet.diff (hK j).1.isClosed.measurableSet).nullMeasurableSet)
    hm ⟨0, by rw [← jordan_volume_eq_measure (hjD 0)]; exact ENNReal.ofReal_ne_top⟩
  rw [hiμ] at hμ
  have hv : Tendsto (fun j => volume (T \ K j)) atTop (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hμ
    simpa only [Function.comp_def, ← jordan_volume_eq_measure (hjD _),
      ENNReal.toReal_ofReal (volume_nonneg (hjD _)), ENNReal.toReal_zero] using hh
  obtain ⟨M, hM⟩ := hF.1
  have hbound (j : ℕ) : |regionIntegral (fun x : (T \ K j : Set (E n)) => F x)| ≤
      max M 0 * volume (T \ K j) := by
    apply scalar_uniform_bound (hjD j) _
      (AbsoluteConvergence.region_restrict hF (hjD j) sdiff_subset) (max M 0) (le_max_right _ _)
    intro x
    have hh : |F x| ≤ M := by simpa only [Real.norm_eq_abs] using hM ⟨x, x.property.1⟩
    exact hh.trans (le_max_left _ _)
  apply squeeze_zero_norm (fun j => by simpa only [Real.norm_eq_abs] using hbound j)
  simpa only [mul_zero] using tendsto_const_nhds.mul hv

lemma truncation_integral_tendsto {n : ℕ} {T Z : Set (E n)}
    (hT : IsCompact T) (hjT : Jordan T) (hZ : ContentZero Z)
    (K : ℕ → Set (E n)) (hK : ∀ j, IsCompact (K j) ∧ Jordan (K j) ∧ K j ⊆ T)
    (hKm : Monotone K) (hcover : T \ ⋃ j, K j ⊆ Z)
    (F : E n → ℝ) (hF : RegionIntegrable (fun x : T => F x)) :
    Tendsto (fun j => regionIntegral (fun x : K j => F x)) atTop
      (𝓝 (regionIntegral (fun x : T => F x))) := by
  have hd := discarded_integral_tendsto_zero hT hjT hZ K hK hKm hcover F hF
  have he (j : ℕ) : regionIntegral (fun x : K j => F x) =
      regionIntegral (fun x : T => F x) - regionIntegral (fun x : (T \ K j : Set (E n)) => F x) := by
    have h := AbsoluteConvergence.region_diff hjT (hK j).2.1 (hK j).2.2 hF
    linarith
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub hd

/-- A regular chart on the interior of a compact box has a Jordan compact
image even when its boundary is singular or identified. -/
lemma chart_box_image_jordan {n : ℕ} (hn : 0 < n) (Q : Box n)
    (e : OpenPartialHomeomorph (E n) (E n)) (he : ContDiff ℝ 1 e)
    (hQe : interior (carrier Q) ⊆ e.source) : Jordan (e '' carrier Q) := by
  have hc := (DiscontinuityCriterion.carrier_compact Q).image he.continuous
  apply (jordan_iff_boundary hn _ hc.isBounded).mpr
  apply contentZero_mono (T := e '' faces Q) ?_ (image_faces_contentZero hn Q e he)
  have hopen := e.isOpen_image_of_subset_source isOpen_interior hQe
  have hins : e '' interior (carrier Q) ⊆ interior (e '' carrier Q) :=
    interior_maximal (image_mono interior_subset) hopen
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hc.isClosed.closure_eq ▸ hy.1
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  intro hi
  exact hy.2 (hins (mem_image_of_mem e hi))

/-- Substitution across identified/singular faces, proved by compact regular
truncations on both sides. The conclusion concerns every bounded Riemann zero
extension and any bounded assignment of parameter-face values. -/
lemma chart_box_formula {n : ℕ} (hn : 0 < n) (Q : Box n)
    (e : OpenPartialHomeomorph (E n) (E n)) (he : ContDiff ℝ 1 e)
    (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hQe : interior (carrier Q) ⊆ e.source)
    (J : E n → ℝ) (hJ : ContinuousOn J (carrier Q))
    (hdet : ∀ x ∈ interior (carrier Q), |(fderiv ℝ e x).det| = J x) :
    FullFormula Q (e '' carrier Q) e J := by
  intro S hST f hf g hg
  let T := e '' carrier Q
  let F : E n → ℝ := zeroExtension f
  let G : E n → ℝ := zeroExtension g
  have hcT : IsCompact T := (DiscontinuityCriterion.carrier_compact Q).image he.continuous
  have hjT : Jordan T := chart_box_image_jordan hn Q e he hQe
  have hfT := extend_region hST hcT.isBounded f hf
  have hgI : RegionIntegrable g :=
    integrable_on_closed_parameter_box hn Q e hei hQe J hJ f hf g hg.1 hg.2
  have hgQ : RegionIntegrable (fun x : carrier Q => G x) := by
    have hh : (fun x : carrier Q => G x) = g := funext (fun x => zeroExtension_apply g x)
    exact hh.symm ▸ hgI
  obtain ⟨K, hK⟩ := ImproperExhaustions.regular_exhaustion_exists (interior (carrier Q)) isOpen_interior
  have hKp (j : ℕ) : IsCompact (K j) ∧ Jordan (K j) ∧ K j ⊆ carrier Q :=
    ⟨(hK.1 j).1, (hK.1 j).2.1, (hK.1 j).2.2.trans interior_subset⟩
  have hKe (j : ℕ) : closure (K j) ⊆ e.source := by
    rw [(hK.1 j).1.isClosed.closure_eq]
    exact (hK.1 j).2.2.trans hQe
  have hKI (j : ℕ) : IsCompact (e '' K j) ∧ Jordan (e '' K j) ∧ e '' K j ⊆ T :=
    ⟨(hK.1 j).1.image he.continuous,
      (RegionSubstitution.jordan_image e he.contDiffOn hei (K j) (hK.1 j).2.1
        ((hK.1 j).1.closure) (hKe j)).2,
      image_mono (hKp j).2.2⟩
  have hm := ImproperExhaustions.regular_exhaustion_mono hK
  have hcoverQ : carrier Q \ ⋃ j, K j ⊆ faces Q := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hi
    have hmem : x ∈ ⋃ j, interior (K j) := hK.2.2.symm ▸ hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact hx.2 (mem_iUnion.mpr ⟨j, interior_subset hj⟩)
  have hcoverT : T \ ⋃ j, e '' K j ⊆ e '' faces Q := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, hcoverQ ⟨hx, ?_⟩, rfl⟩
    intro hh
    obtain ⟨j, hj⟩ := mem_iUnion.mp hh
    exact hy (mem_iUnion.mpr ⟨j, mem_image_of_mem e hj⟩)
  have hlimQ := truncation_integral_tendsto (DiscontinuityCriterion.carrier_compact Q)
    (ImproperExhaustions.jordan_box Q) (box_faces_contentZero Q) K hKp hm hcoverQ G hgQ
  have hlimT := truncation_integral_tendsto hcT hjT (image_faces_contentZero hn Q e he)
    (fun j => e '' K j) hKI (fun i j hij => image_mono (hm hij)) hcoverT F hfT.1
  have hproper (j : ℕ) : regionIntegral (fun y : e '' K j => F y) =
      regionIntegral (fun x : K j => G x) := by
    have hFI := AbsoluteConvergence.region_restrict hfT.1 (hKI j).2.1 (hKI j).2.2
    have hsub := RegionSubstitution.region_substitution e he.contDiffOn hei (K j)
      (hK.1 j).2.1 ((hK.1 j).1.closure) (hKe j) (fun y : e '' K j => F y) hFI.1
    have hh := hsub.2.2 (Or.inl hFI)
    have hfun : (fun x : K j => F (e x) * |(fderiv ℝ e x).det|) =
        (fun x : K j => G x) := by
      funext x
      rw [hdet x ((hK.1 j).2.2 x.property)]
      exact (hg.2 ⟨x, (hKp j).2.2 x.property⟩ ((hK.1 j).2.2 x.property)).symm.trans
        (zeroExtension_apply g ⟨x, (hKp j).2.2 x.property⟩).symm
    exact hh.trans (congrArg regionIntegral hfun)
  have hvalues := tendsto_nhds_unique hlimT (by simpa only [hproper] using hlimQ)
  refine ⟨hgI, ?_⟩
  have hgval : regionIntegral (fun x : carrier Q => G x) = regionIntegral g :=
    congrArg regionIntegral (funext (fun x => zeroExtension_apply g x))
  exact hgval.symm.trans (hvalues.symm.trans hfT.2)

/-- A simultaneous sine/cosine representative in any closed angular
interval of length 2π. The complex norm handles the origin as well. -/
lemma polar_representation (x y α : ℝ) :
    ∃ r θ : ℝ, 0 ≤ r ∧ θ ∈ Icc α (α + 2 * Real.pi) ∧
      r^2 = x^2 + y^2 ∧ r * Real.cos θ = x ∧ r * Real.sin θ = y := by
  let z : ℂ := ⟨x, y⟩
  obtain ⟨m, hm, _⟩ := existsUnique_add_zsmul_mem_Ico Real.two_pi_pos z.arg α
  refine ⟨‖z‖, z.arg + m * (2 * Real.pi), norm_nonneg _, ?_, ?_, ?_, ?_⟩
  · simpa only [zsmul_eq_mul] using (show z.arg + m • (2 * Real.pi) ∈
      Icc α (α + 2 * Real.pi) from ⟨hm.1, hm.2.le⟩)
  · simpa [z, Complex.normSq_mk, sq] using Complex.sq_norm z
  · rw [Real.cos_add_int_mul_two_pi]
    exact Complex.norm_mul_cos_arg z
  · rw [Real.sin_add_int_mul_two_pi]
    exact Complex.norm_mul_sin_arg z

lemma disk_subset_polar_image (R α : ℝ) (hR : 0 ≤ R) :
    disk R ⊆ polar '' carrier (polarBox R α hR) := by
  intro x hx
  obtain ⟨r, θ, hr, hθ, hrsq, hx0, hx1⟩ := polar_representation (x 0) (x 1) α
  have hnorm : ‖x‖^2 = (x 0)^2 + (x 1)^2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have hre : r = ‖x‖ := by nlinarith [norm_nonneg x]
  have hrR : r ≤ R := by simpa only [hre, disk, Metric.mem_closedBall, dist_zero_right] using hx
  let p : E 2 := WithLp.toLp 2 ![r, θ]
  refine ⟨p, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨hr, hrR⟩
    · exact hθ
  · ext i; fin_cases i
    · exact hx0
    · exact hx1

lemma cylinder_subset_cylindrical_image (R α a b : ℝ) (hR : 0 ≤ R) (hab : a ≤ b) :
    solidCylinder R a b ⊆ cylindrical '' carrier (cylinderBox R α a b hR hab) := by
  intro x hx
  obtain ⟨r, θ, hr, hθ, hrsq, hx0, hx1⟩ := polar_representation (x 0) (x 1) α
  have hrR : r ≤ R := by nlinarith [hx.1]
  let p : E 3 := WithLp.toLp 2 ![r, θ, x 2]
  refine ⟨p, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨hr, hrR⟩
    · exact hθ
    · exact hx.2
  · ext i; fin_cases i
    · exact hx0
    · exact hx1
    · rfl

lemma ball_subset_spherical_image (R α : ℝ) (hR : 0 ≤ R) :
    Specs.D04.C07.CoordinateSeamsVolumes.Model.ball R ⊆
      spherical '' carrier (sphericalBox R α hR) := by
  intro x hx
  obtain ⟨ρ, θ, hρ, hθ, hρsq, hx0, hx1⟩ := polar_representation (x 0) (x 1) α
  let w : ℂ := ⟨x 2, ρ⟩
  let r := ‖w‖
  let φ := w.arg
  have hφ : φ ∈ Icc 0 Real.pi := ⟨Complex.arg_nonneg_iff.mpr hρ, Complex.arg_le_pi w⟩
  have hrc : r * Real.cos φ = x 2 := Complex.norm_mul_cos_arg w
  have hrs : r * Real.sin φ = ρ := Complex.norm_mul_sin_arg w
  have hrsq : r^2 = (x 2)^2 + ρ^2 := by
    simpa [r, w, Complex.normSq_mk, sq] using Complex.sq_norm w
  have hnorm : ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq x
  have hre : r = ‖x‖ := by
    have hr : 0 ≤ r := norm_nonneg w
    nlinarith [norm_nonneg x]
  have hrR : r ≤ R := by
    simpa only [hre, Specs.D04.C07.CoordinateSeamsVolumes.Model.ball,
      Metric.mem_closedBall, dist_zero_right] using hx
  let p : E 3 := WithLp.toLp 2 ![r, φ, θ]
  refine ⟨p, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨norm_nonneg w, hrR⟩
    · exact hφ
    · exact hθ
  · ext i; fin_cases i
    · change r * Real.sin φ * Real.cos θ = x 0
      rw [hrs]; exact hx0
    · change r * Real.sin φ * Real.sin θ = x 1
      rw [hrs]; exact hx1
    · exact hrc

theorem polar_formula : Specs.D04.C07.CoordinateSeamsVolumes.polar_formulaType := by
  intro R α hR
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.polar_chart α).2
  have hQe : interior (carrier (polarBox R α hR.le)) ⊆ e.source := by
    intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2⟩
  have hform := chart_box_formula (by decide) (polarBox R α hR.le) e
    (by simpa only [he] using CoordinateCharts.polar_contDiff) hei hQe
    (fun p => p 0) (EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn
    (by intro x hx; rw [he, CoordinateCharts.polar_det, abs_of_pos]
        exact ((hs ▸ hQe hx) : x ∈ polarDomain α).1)
  rw [he] at hform
  intro S hST f hf g hg
  exact hform S (hST.trans (disk_subset_polar_image R α hR.le)) f hf g hg

theorem cylindrical_formula : Specs.D04.C07.CoordinateSeamsVolumes.cylindrical_formulaType := by
  intro R α a b hR hab
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.cylindrical_chart α).2
  have hQe : interior (carrier (cylinderBox R α a b hR.le hab)) ⊆ e.source := by
    intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2⟩
  have hform := chart_box_formula (by decide) (cylinderBox R α a b hR.le hab) e
    (by simpa only [he] using CoordinateCharts.cylindrical_contDiff) hei hQe
    (fun p => p 0) (EuclideanSpace.proj (0 : Fin 3)).continuous.continuousOn
    (by intro x hx; rw [he, CoordinateCharts.cylindrical_det, abs_of_pos]
        exact ((hs ▸ hQe hx) : x ∈ cylindricalDomain α).1)
  rw [he] at hform
  intro S hST f hf g hg
  exact hform S (hST.trans (cylinder_subset_cylindrical_image R α a b hR.le hab)) f hf g hg

theorem spherical_formula : Specs.D04.C07.CoordinateSeamsVolumes.spherical_formulaType := by
  intro R α hR
  obtain ⟨e, hs, _, he, _, hei⟩ := (CoordinateCharts.spherical_chart α).2
  have hQe : interior (carrier (sphericalBox R α hR.le)) ⊆ e.source := by
    intro p hp
    rw [hs]
    rw [interior_carrier] at hp
    exact ⟨(hp 0).1, (hp 1).1, (hp 1).2, (hp 2).1, (hp 2).2⟩
  have hform := chart_box_formula (by decide) (sphericalBox R α hR.le) e
    (by simpa only [he] using CoordinateCharts.spherical_contDiff) hei hQe
    (fun p => (p 0)^2 * Real.sin (p 1))
    ((((EuclideanSpace.proj (0 : Fin 3)).continuous.pow 2).mul
      (Real.continuous_sin.comp (EuclideanSpace.proj (1 : Fin 3)).continuous)).continuousOn)
    (by
      intro x hx
      have hp : x ∈ sphericalDomain α := hs ▸ hQe hx
      rw [he, CoordinateCharts.spherical_det, abs_of_nonneg]
      exact mul_nonneg (sq_nonneg _) (Real.sin_nonneg_of_mem_Icc ⟨hp.2.1.le, hp.2.2.1.le⟩))
  rw [he] at hform
  intro S hST f hf g hg
  exact hform S (hST.trans (ball_subset_spherical_image R α hR.le)) f hf g hg

theorem zero_cylinder : Specs.D04.C07.CoordinateSeamsVolumes.zero_cylinderType := by
  intro a b hab
  let Q := cylinderBox 0 0 a b (le_refl 0) hab
  have hs := cylinder_subset_cylindrical_image 0 0 a b (le_refl 0) hab
  have hfaces : carrier Q ⊆ faces Q := by
    intro p hp
    refine ⟨hp, ?_⟩
    rw [interior_carrier]
    intro hi
    have h0 := hi 0
    change 0 < p 0 ∧ p 0 < 0 at h0
    linarith [h0.1, h0.2]
  have hz := contentZero_mono (image_mono hfaces)
    (image_faces_contentZero (by decide) Q cylindrical CoordinateCharts.cylindrical_contDiff)
  have hc := (DiscontinuityCriterion.carrier_compact Q).image CoordinateCharts.cylindrical_contDiff.continuous
  exact LinearVolume.contentZero_jordan_volume (by decide) _ (hc.isBounded.subset hs)
    (contentZero_mono hs hz)

lemma natural_formula_of_fullFormula {n : ℕ} {Q : Box n} {T : Set (E n)}
    {Φ : E n → E n} {J : E n → ℝ} (hJ : ContinuousOn J (carrier Q))
    (hform : FullFormula Q T Φ J) (S : Set (E n)) (hST : S ⊆ T)
    (f : S → ℝ) (hf : RegionIntegrable f) :
    RegionIntegrable (fun p : carrier Q => zeroExtension f (Φ p) * J p) ∧
      regionIntegral (fun p : carrier Q => zeroExtension f (Φ p) * J p) = regionIntegral f :=
  hform S hST f hf _ ⟨weighted_pullback_bounded Q f hf.1 Φ J hJ, fun _ _ => rfl⟩

theorem natural_formulas : Specs.D04.C07.CoordinateSeamsVolumes.natural_formulasType := by
  refine ⟨?_, ?_, ?_⟩
  · intro R α hR S hST f hf
    exact natural_formula_of_fullFormula
      (EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn
      (polar_formula R α hR) S hST f hf
  · intro R α a b hR hab S hST f hf
    exact natural_formula_of_fullFormula
      (EuclideanSpace.proj (0 : Fin 3)).continuous.continuousOn
      (cylindrical_formula R α a b hR hab) S hST f hf
  · intro R α hR S hST f hf
    exact natural_formula_of_fullFormula
      ((((EuclideanSpace.proj (0 : Fin 3)).continuous.pow 2).mul
        (Real.continuous_sin.comp (EuclideanSpace.proj (1 : Fin 3)).continuous)).continuousOn)
      (spherical_formula R α hR) S hST f hf

/-- Region integration on a closed box agrees with the original primitive
box integral. Values on its faces are retained on both sides. -/
theorem rectangle_integral_bridge :
    Specs.D04.C07.CoordinateSeamsVolumes.rectangle_integral_bridgeType := by
  intro n hn Q g hg
  let F := zeroExtension g
  by_cases hd : Degenerate Q
  · have hfaces : carrier Q ⊆ faces Q := by
      intro x hx
      refine ⟨hx, ?_⟩
      rw [interior_carrier]
      intro hi
      obtain ⟨i, hiEq⟩ := hd
      have h := hi i
      linarith [h.1, h.2]
    have hz := LinearVolume.contentZero_jordan_volume hn (carrier Q)
      (carrier_isBounded Q) (contentZero_mono hfaces (box_faces_contentZero Q))
    exact ⟨integrable_degenerate F Q (zeroExtension_bounded g hg.1 Q) hd,
      (degenerate_integrals F Q hd).1.trans (zero_volume_region hz.1 hz.2 g hg.1).2.symm⟩
  have hq := nondegenerate_of_not_degenerate hd
  obtain ⟨R, hR, hiR⟩ := hg.2
  have hl (i : Fin n) : R.lower i < Q.lower i :=
    (encloses_open hR (subset_closure (lower_mem Q)) i).1
  have hu (i : Fin n) : Q.upper i < R.upper i :=
    (encloses_open hR (subset_closure (upper_mem Q)) i).2
  let P : Grid R := fun i => threePartition (R.lower i) (Q.lower i) (Q.upper i)
    (R.upper i) (hl i) (hq i) (hu i)
  let c₀ : CellIndex P := fun _ => (1 : Fin 3)
  have hmid : cellBox P c₀ = Q := by apply Subdivision.box_ext <;> ext i <;> rfl
  have hiC := (subdivision_integrable F R hiR.1 P).mp hiR
  have hiQ : Integrable F Q := hmid ▸ hiC c₀
  have hother (c : CellIndex P) (hc : c ≠ c₀) :
      integral F (cellBox P c) (hiC c) = 0 := by
    obtain ⟨hci, hval⟩ := ExceptionalSets.zero_off_contentZero hn
      (zeroExtension_bounded g hg.1 (cellBox P c)) (box_faces_contentZero Q) (by
        intro x hx hxf
        apply zeroExtension_of_not_mem g
        intro hxQ
        have hxi : x ∈ openCarrier Q := by
          rw [← interior_carrier]
          by_contra hxI
          exact hxf ⟨hxQ, hxI⟩
        obtain ⟨i, hi⟩ : ∃ i, c i ≠ (1 : Fin 3) := by
          by_contra! hh
          exact hc (funext hh)
        have hxc := hx i
        change ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).castSucc ≤ x i ∧
          x i ≤ ![R.lower i, Q.lower i, Q.upper i, R.upper i] (c i).succ at hxc
        generalize hci : c i = j at hxc hi
        fin_cases j
        · norm_num at hxc; exact (not_lt_of_ge hxc.2) (hxi i).1
        · exact hi rfl
        · norm_num at hxc; exact (not_lt_of_ge hxc.1) (hxi i).2)
    exact hval
  have he : integral F R hiR = lowerIntegral F Q := by
    rw [subdivision_integral F R P hiR hiC, Finset.sum_eq_single c₀]
    · change lowerIntegral F (cellBox P c₀) = lowerIntegral F Q
      rw [hmid]
    · intro c _ hc; exact hother c hc
    · simp
  exact ⟨hiQ, ((integral_eq_on_enclosing_box g hg hR hiR).trans he).symm⟩

end D04.CoordinateSeamsVolumes
