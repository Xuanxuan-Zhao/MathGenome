import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteGeometricUnionIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteGeometricPatchIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ManifoldIntegralIndependence
import Mathlib.Topology.Compactness.Lindelof

/-! Components of geometric multiplicity-one integration.
No integral equality is an input to the geometric overlap lemmas. All
coordinate integrals below are the shared Jordan/Darboux values. The actual
localized manifold integrals agree with finite patch displays; the seam
complement has an embedded manifold structure and the pieces' tangent spaces.
Smooth deletion of seam neighborhoods converges in the actual manifold values.
Prescribed positive-dimensional orientations glue uniquely on that complement,
and compatible decompositions induce the same actual tangent orientation there.
Actual integral comparison and a display-independent union value are proved
below for compact manifold decompositions with displayed ambient seams. The
regular-cell interior charts, induced orientations, face seam displays, full-cube
seam nullity, and actual cell/interior-manifold cutoff comparison are also proved.
Global comparison and a unique all-display value cover finite cell, manifold
and mixed assemblies. Compact overlap carriers may be covered by countably many
compact lower-dimensional images. The admission bridges derive these coverings
from arbitrary local-C¹ parameter pieces and from embedded manifolds, including
noncompact pieces and boundary charts; see proof-work.md. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open Set Function Topology Filter
open scoped ContDiff BigOperators Classical
namespace D04.GeometricUnion
open Darboux JordanRegions
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral
open Model

abbrev AmbientSeams := Model.AmbientSeams
abbrev seamCarrier := @Model.AmbientSeams.carrier

lemma seam_map_continuous {k n : ℕ} (p : Model.CompactSeam k n) :
    ContinuousOn p.map p.parameter := by
  intro x hx
  obtain ⟨U,g,hU,hg,heq⟩ := p.localC1 x hx
  have he : g =ᶠ[𝓝[p.parameter] x] p.map :=
    mem_of_superset (inter_mem_nhdsWithin _ hU) (fun _ hy => heq hy)
  exact hg.continuousAt.continuousWithinAt.congr_of_eventuallyEq he.symm
    (heq ⟨hx,mem_of_mem_nhds hU⟩).symm

theorem ambient_seams_compact : ambient_seams_compactType := by
  intro k n s
  exact s.isCompact

lemma restrict_seam_parameter_compact {k n : ℕ} (p : Model.CompactSeam k n)
    {K : Set (E n)} (hK : IsCompact K) : IsCompact (p.parameter ∩ p.map ⁻¹' K) :=
  p.compact.of_isClosed_subset
    ((seam_map_continuous p).preimage_isClosed_of_isClosed
      p.compact.isClosed hK.isClosed) inter_subset_left

lemma restricted_seam_image {k n : ℕ} (p : Model.CompactSeam k n) (K : Set (E n)) :
    p.map '' (p.parameter ∩ p.map ⁻¹' K) = (p.map '' p.parameter) ∩ K := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hK⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hK⟩
  · rintro ⟨⟨x,hx,rfl⟩,hK⟩
    exact ⟨x,⟨hx,hK⟩,rfl⟩

theorem chart_seams_contentZero : chart_seams_contentZeroType := by
  intro k n M c hkn s K hK htarget
  obtain ⟨P,hP,hcover⟩ := s.cover
  letI := hP.to_subtype
  have hpieces (p : P) :
      NullCovers.ContentZero (c.invFun '' ((p.val.map '' p.val.parameter) ∩ K)) := by
    rw [← restricted_seam_image p.val K]
    apply (LowerDimensionalImages.chart_local_overlap c p.val.lower hkn
      (p.val.parameter ∩ p.val.map ⁻¹' K) p.val.map
      (restrict_seam_parameter_compact p.val hK) ?_ ?_).2
    · intro x hx
      obtain ⟨U,g,hU,hg,he⟩ := p.val.localC1 x hx.1
      exact ⟨U,g,hU,hg,fun _ hy => he ⟨hy.1.1,hy.2⟩⟩
    · rintro y ⟨x,hx,rfl⟩
      exact htarget hx.2
  have hc : IsCompact (c.invFun '' (s.carrier ∩ K)) :=
    (s.isCompact.inter hK).image_of_continuousOn
      (c.continuous_invFun.mono (inter_subset_right.trans htarget))
  refine ⟨hc,NullCovers.compact_null_contentZero _ hc ?_⟩
  apply NullCovers.null_mono (T := ⋃ p : P,
    c.invFun '' ((p.val.map '' p.val.parameter) ∩ K)) ?_
    (NullCovers.null_iUnion_countable _ (fun p => NullCovers.contentZero_null (hpieces p)))
  rintro y ⟨x,⟨hx,hxK⟩,rfl⟩
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hcover hx)
  exact mem_iUnion.mpr ⟨p,⟨x,⟨hp,hxK⟩,rfl⟩⟩

theorem region_integral_unchanged : region_integral_unchangedType := by
  intro k S hS f g hf hg Z hZ he
  cases k with
  | zero =>
    have hZ0 : Z = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply NullCovers.zero_dim_point_not_null
      apply NullCovers.null_mono (singleton_subset_iff.mpr (show (0 : E 0) ∈ Z by
        simpa only [Subsingleton.elim x 0] using hx))
      exact NullCovers.contentZero_null hZ
    have hfg : f = g := funext (fun x => he x (by simp [hZ0]))
    simpa only [← hfg] using And.intro hf (rfl : regionIntegral f = regionIntegral f)
  | succ k =>
    let Q := enclosingBox S
    have hQ : Encloses S Q := enclosingBox_encloses (jordan_bounded hS)
    have hfi := ((integrable_iff_on_enclosing_box _ hQ).mp hf).2
    have hbg := zeroExtension_bounded g hg Q
    obtain ⟨hgi,hval⟩ := LowerDimensionalImages.coefficient_integral_unchanged
      (Nat.succ_pos _) Z hZ Q (zeroExtension f) (zeroExtension g) hfi hbg (by
        intro x hx hxZ
        by_cases hxS : x ∈ S
        · simpa only [zeroExtension_apply f ⟨x,hxS⟩, zeroExtension_apply g ⟨x,hxS⟩]
            using he ⟨x,hxS⟩ hxZ
        · rw [zeroExtension_of_not_mem f hxS,zeroExtension_of_not_mem g hxS])
    have hG : RegionIntegrable g := (integrable_iff_on_enclosing_box g hQ).mpr ⟨hg,hgi⟩
    refine ⟨hG,?_⟩
    exact (integral_eq_on_enclosing_box g hG hQ hgi).trans
      (hval.trans (integral_eq_on_enclosing_box f hf hQ hfi).symm)

theorem chart_seam_changes : chart_seam_changesType := by
  intro k n M c hkn s K hK htarget S hS f g hf hg he
  exact region_integral_unchanged hS f g hf hg _
    (chart_seams_contentZero c hkn s K hK htarget).2 he

theorem multiplicity_one : multiplicity_oneType := by
  intro n ι _ A Z hp x hx
  by_cases hxu : x ∈ ⋃ i, A i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hxu
    rw [indicator_of_mem hxu, Finset.sum_eq_single i]
    · exact indicator_of_mem hi _
    · intro j _ hji
      exact indicator_of_notMem (fun hj => hx (hp j i hji ⟨hj,hi⟩)) _
    · simp
  · rw [indicator_of_notMem hxu]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun hi => hxu (mem_iUnion.mpr ⟨i,hi⟩)) _

theorem isolated_piece : isolated_pieceType := by
  intro n ι _ A Z hA hp i x hxi hxZ
  let U : Set (E n) := ⋂ j : {j : ι // j ≠ i}, (A j.val)ᶜ
  have hU : IsOpen U := isOpen_iInter_of_finite (fun j => (hA j.val).isClosed.isOpen_compl)
  have hxU : x ∈ U := by
    refine mem_iInter.mpr (fun j => ?_)
    exact fun hxj => hxZ (hp j.val i j.property ⟨hxj,hxi⟩)
  refine ⟨U,hU,hxU,?_⟩
  ext y
  constructor
  · rintro ⟨hyU,hy⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    have hji : j = i := by
      by_contra hji
      exact (mem_iInter.mp hyU ⟨j,hji⟩) hj
    exact ⟨hyU,hji ▸ hj⟩
  · rintro ⟨hyU,hy⟩
    exact ⟨hyU,mem_iUnion.mpr ⟨i,hy⟩⟩

theorem common_piece_germ : common_piece_germType := by
  intro n ι κ _ _ A B Z W hA hB hpA hpB hcover x hx hxZW
  have hxZ : x ∉ Z := fun h => hxZW (Or.inl h)
  have hxW : x ∉ W := fun h => hxZW (Or.inr h)
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover ▸ hx)
  obtain ⟨U,hU,hxU,hUA⟩ := isolated_piece A Z hA hpA i x hi hxZ
  obtain ⟨V,hV,hxV,hVB⟩ := isolated_piece B W hB hpB j x hj hxW
  have hlocalA : (U ∩ V) ∩ (⋃ l, A l) = (U ∩ V) ∩ A i := by
    calc
      _ = V ∩ (U ∩ (⋃ l, A l)) := by ext y; simp only [mem_inter_iff]; tauto
      _ = V ∩ (U ∩ A i) := by rw [hUA]
      _ = _ := by ext y; simp only [mem_inter_iff]; tauto
  have hlocalB : (U ∩ V) ∩ (⋃ l, B l) = (U ∩ V) ∩ B j := by
    calc
      _ = U ∩ (V ∩ (⋃ l, B l)) := by ext y; simp only [mem_inter_iff]; tauto
      _ = U ∩ (V ∩ B j) := by rw [hVB]
      _ = _ := by ext y; simp only [mem_inter_iff]; tauto
  refine ⟨i,j,U ∩ V,hi,hj,hU.inter hV,⟨hxU,hxV⟩,?_,hlocalA⟩
  rw [← hlocalA,← hlocalB,hcover]

theorem coordinate_union_integral : coordinate_union_integralType := by
  intro k ι _ A hA Z hZ hp f hf
  have hUnion : Jordan (⋃ i, A i) := by
    simpa only [Finset.mem_univ, iUnion_true] using
      jordan_finite_union Finset.univ A (fun i _ => hA i)
  refine ⟨hUnion,GeometricPatches.continuous_integrable hUnion hf,?_⟩
  exact GeometricPatches.region_integral_finite_cover hUnion f hf A hA
    (fun i => subset_iUnion A i) rfl hZ hp

theorem coordinate_common_refinement : coordinate_common_refinementType := by
  intro k ι κ _ _ A B hA hB Z W hZ hW hpA hpB hcover f hf
  have hIA i : ContinuousOn f (closure (A i)) :=
    hf.mono (closure_mono (subset_iUnion A i))
  have hIB j : ContinuousOn f (closure (B j)) := by
    rw [hcover] at hf
    exact hf.mono (closure_mono (subset_iUnion B j))
  have hrow i : regionIntegral (fun x : A i => f x) =
      ∑ j, regionIntegral (fun x : ↥(A i ∩ B j) => f x) := by
    refine GeometricPatches.region_integral_finite_cover (hA i) f (hIA i)
      (fun j => A i ∩ B j) (fun j => jordan_inter (hA i) (hB j))
      (fun _ => inter_subset_left) ?_ hW ?_
    · ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · intro hx
        have hxU : x ∈ ⋃ j, B j := hcover ▸ mem_iUnion.mpr ⟨i,hx⟩
        obtain ⟨j,hj⟩ := mem_iUnion.mp hxU
        exact ⟨j,hx,hj⟩
      · rintro ⟨j,hx,_⟩; exact hx
    · intro j l hjl x hx
      exact hpB j l hjl ⟨hx.1.2,hx.2.2⟩
  have hcol j : regionIntegral (fun x : B j => f x) =
      ∑ i, regionIntegral (fun x : ↥(A i ∩ B j) => f x) := by
    refine GeometricPatches.region_integral_finite_cover (hB j) f (hIB j)
      (fun i => A i ∩ B j) (fun i => jordan_inter (hA i) (hB j))
      (fun _ => inter_subset_right) ?_ hZ ?_
    · ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · intro hx
        have hxU : x ∈ ⋃ i, A i := hcover.symm ▸ mem_iUnion.mpr ⟨j,hx⟩
        obtain ⟨i,hi⟩ := mem_iUnion.mp hxU
        exact ⟨i,hi,hx⟩
      · rintro ⟨i,_,hx⟩; exact hx
    · intro i l hil x hx
      exact hpA i l hil ⟨hx.1.1,hx.2.1⟩
  refine ⟨fun i j => jordan_inter (hA i) (hB j),hrow,hcol,?_⟩
  calc
    _ = ∑ i, ∑ j, regionIntegral (fun x : ↥(A i ∩ B j) => f x) :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    _ = ∑ j, ∑ i, regionIntegral (fun x : ↥(A i ∩ B j) => f x) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (hcol j).symm)

lemma chart_subregion_frontier {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (K : Set (E k)) (hK : IsCompact K)
    (hsource : K ⊆ c.source) {ι : Type} [Fintype ι]
    (B : ι → Set (E n)) (Z : Set (E n)) (hB : ∀ j, IsCompact (B j))
    (hp : ∀ i j, i ≠ j → B i ∩ B j ⊆ Z)
    (hcover : c.toFun '' K ⊆ ⋃ j, B j) (j : ι) :
    IsCompact (K ∩ c.toFun ⁻¹' B j) ∧
      frontier (K ∩ c.toFun ⁻¹' B j) ⊆
        frontier K ∪ c.invFun '' (Z ∩ (c.toFun '' K)) := by
  have hc : ContinuousOn c.toFun K := c.continuous_toFun.mono hsource
  have hT : IsCompact (K ∩ c.toFun ⁻¹' B j) :=
    hK.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed hK.isClosed (hB j).isClosed) inter_subset_left
  refine ⟨hT,?_⟩
  intro x hx
  have hxT : x ∈ K ∩ c.toFun ⁻¹' B j := hT.isClosed.closure_subset hx.1
  by_cases hxF : x ∈ frontier K
  · exact Or.inl hxF
  right
  by_contra hxCoord
  have hxI : x ∈ interior K :=
    not_not.mp (fun h => hxF ⟨subset_closure hxT.1,h⟩)
  have hxZ : c.toFun x ∉ Z := by
    intro hz
    exact hxCoord ⟨c.toFun x,⟨hz,⟨x,hxT.1,rfl⟩⟩,c.left_inv x (hsource hxT.1)⟩
  obtain ⟨U,hU,hxU,hEq⟩ := isolated_piece B Z hB hp j (c.toFun x) hxT.2 hxZ
  have hKnhds : K ∈ 𝓝 x :=
    mem_of_superset (isOpen_interior.mem_nhds hxI) interior_subset
  have hct : ContinuousAt c.toFun x := hc.continuousAt hKnhds
  have hnU : c.toFun ⁻¹' U ∈ 𝓝 x := hct.preimage_mem_nhds (hU.mem_nhds hxU)
  have hnT : K ∩ c.toFun ⁻¹' B j ∈ 𝓝 x := by
    apply mem_of_superset (inter_mem hKnhds hnU)
    intro y hy
    exact ⟨hy.1,(show c.toFun y ∈ U ∩ B j from
      hEq ▸ ⟨hy.2,hcover ⟨y,hy.1,rfl⟩⟩).2⟩
  exact hx.2 (mem_interior_iff_mem_nhds.mpr hnT)

theorem chart_subregions_jordan : chart_subregions_jordanType := by
  intro k n M c hkn K hK hJK hsource ι _ B s hB hp hcover j
  obtain ⟨hT,hFront⟩ := chart_subregion_frontier c K hK hsource B s.carrier hB hp hcover j
  refine ⟨hT,hFront,?_⟩
  have hImage : IsCompact (c.toFun '' K) := hK.image_of_continuousOn
    (c.continuous_toFun.mono hsource)
  have hSeam : NullCovers.ContentZero (c.invFun '' (s.carrier ∩ (c.toFun '' K))) :=
    (chart_seams_contentZero c hkn s _ hImage (by
      rintro y ⟨x,hx,rfl⟩; exact c.map_source (hsource hx))).2
  cases k with
  | zero => exact jordan_zero_dim _
  | succ k =>
    apply (jordan_iff_boundary (Nat.succ_pos _) _ hT.isBounded).mpr
    exact NullCovers.contentZero_mono hFront
      (contentZero_union (GeometricPatches.frontier_contentZero hJK) hSeam)

theorem chart_geometric_decomposition : chart_geometric_decompositionType := by
  intro k n M c hkn K hK hJK hsource ι _ B s hB hp hcover f hf
  have hJ j := (chart_subregions_jordan c hkn K hK hJK hsource B s hB hp hcover j).2.2
  have hImage : IsCompact (c.toFun '' K) :=
    hK.image_of_continuousOn (c.continuous_toFun.mono hsource)
  have hSeam := (chart_seams_contentZero c hkn s _ hImage (by
    rintro y ⟨x,hx,rfl⟩; exact c.map_source (hsource hx))).2
  refine GeometricPatches.region_integral_finite_cover hJK f
    (by simpa only [hK.isClosed.closure_eq] using hf)
    (fun j => K ∩ c.toFun ⁻¹' B j) hJ (fun _ => inter_subset_left) ?_ hSeam ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover ⟨x,hx,rfl⟩)
      exact mem_iUnion.mpr ⟨j,hx,hj⟩
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact hj.1
  · intro i j hij x hx
    refine ⟨c.toFun x,⟨hp i j hij ⟨hx.1.2,hx.2.2⟩,⟨x,hx.1.1,rfl⟩⟩,?_⟩
    exact c.left_inv x (hsource hx.1.1)

private def changeChartCarrier {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (he : M ∩ c.ambient = N ∩ c.ambient) :
    EmbeddedChart r k n N where
  half := c.half
  half_pos := c.half_pos
  source := c.source
  source_open := c.source_open
  ambient := c.ambient
  ambient_open := c.ambient_open
  toFun := c.toFun
  invFun := c.invFun
  map_source := he ▸ c.map_source
  map_target := he ▸ c.map_target
  left_inv := c.left_inv
  right_inv := he ▸ c.right_inv
  continuous_toFun := c.continuous_toFun
  continuous_invFun := he ▸ c.continuous_invFun
  regular := c.regular

theorem chart_retarget : chart_retargetType := by
  intro r k n M N c U hU he
  let a := D04.EmbeddedChart.restrict c U hU
  have he' : M ∩ a.ambient = N ∩ a.ambient := by
    change M ∩ (c.ambient ∩ U) = N ∩ (c.ambient ∩ U)
    calc
      _ = c.ambient ∩ (U ∩ M) := by ext y; simp only [mem_inter_iff]; tauto
      _ = c.ambient ∩ (U ∩ N) := by rw [he]
      _ = _ := by ext y; simp only [mem_inter_iff]; tauto
  exact ⟨changeChartCarrier a he',rfl,rfl,rfl,rfl,rfl⟩

theorem common_piece_charts : common_piece_chartsType := by
  intro k n ι κ _ _ A B Z W hA hB hAm hpA hpB hcover x hx hxZW
  obtain ⟨i,j,U,hxi,hxj,hU,hxU,hEq,_⟩ :=
    common_piece_germ A B Z W hA hB hpA hpB hcover x hx hxZW
  obtain ⟨c,u,hcenter,hcu⟩ := (hAm i).2.2 x hxi
  let a := D04.EmbeddedChart.restrict c U hU
  obtain ⟨d,hdsource,hdambient,hdmap,hdinv,hdhalf⟩ := chart_retarget c U hU hEq
  exact ⟨i,j,a,d,u,⟨hcenter.1,by change c.toFun u ∈ U; rw [hcu]; exact hxU⟩,
    hcu,hdsource,hdmap,hdinv,hdambient,hdhalf⟩

theorem common_chart_integrals : common_chart_integralsType := by
  intro r k n M N c d hr hsource hmap S hS hSc O omega ho hO w hw
  obtain ⟨P,hPS,hPc,hPd⟩ := GeometricPatches.chart_patch_exists c hr O ho.1
    S hS hSc hO
  have hPsource : P.region ⊆ c.source := by
    rw [hPS]; exact subset_closure.trans hSc
  have hcmap : EqOn P.map c.toFun P.region := by
    intro x hx; exact hPc (subset_closure (hPS ▸ hx))
  have hdiff (x : E k) (hx : x ∈ P.region) :
      fderiv ℝ P.map x =
        Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c x :=
    hPd x (subset_closure (hPS ▸ hx))
  have hc := GeometricPatches.chart_integral_bridge c P hPsource hcmap hdiff
    omega ho w hw
  have hd := GeometricPatches.chart_integral_bridge d P
    (by rw [hsource]; exact hPsource)
    (by rw [hmap]; exact hcmap)
    (by
      intro x hx
      simpa only [Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential,
        hsource,hmap] using hdiff x hx)
    omega ho w hw
  dsimp only at hc hd ⊢
  rw [hPS] at hc hd
  exact ⟨hc.1,hd.1,hc.2.trans hd.2.symm⟩


/-- Cutting a coordinate box by the model half-space remains Jordan. -/
lemma parameter_box_jordan {k : ℕ} (Q : Box k) (half : Bool) :
    Jordan (carrier Q ∩ parameterSpace k half) := by
  cases half with
  | false =>
    change Jordan (carrier Q ∩ (Set.univ : Set (E k)))
    simpa using OneCoordinate.Boxes.jordan_carrier Q
  | true =>
    cases k with
    | zero => exact jordan_zero_dim _
    | succ k =>
      let T := carrier Q ∩ halfSpace (k+1)
      have hT : IsCompact T := (DiscontinuityCriterion.carrier_compact Q).inter_right
        (DirectedSubstitution.parameterSpace_closed (k+1) true)
      apply (jordan_iff_boundary (Nat.succ_pos _) _ hT.isBounded).mpr
      have hsub : frontier T ⊆ frontier (carrier Q) ∪
          NullCovers.coordinateFace Q (Fin.last k) 0 := by
        intro x hx
        have hxT : x ∈ T := hT.isClosed.closure_subset hx.1
        by_cases hxF : x ∈ frontier (carrier Q)
        · exact Or.inl hxF
        right
        refine ⟨hxT.1,?_⟩
        by_contra hn
        have hp : 0 < x (Fin.last k) := lt_of_le_of_ne hxT.2 (Ne.symm hn)
        have hxI : x ∈ interior (carrier Q) :=
          not_not.mp (fun h => hxF ⟨subset_closure hxT.1,h⟩)
        have hU : IsOpen (interior (carrier Q) ∩ {y : E (k+1) | 0 < y (Fin.last k)}) :=
          isOpen_interior.inter (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last k)).continuous)
        have hUT : interior (carrier Q) ∩ {y : E (k+1) | 0 < y (Fin.last k)} ⊆ T :=
          fun y hy => ⟨interior_subset hy.1,by
            change 0 ≤ y (Fin.last k)
            exact le_of_lt hy.2⟩
        exact hx.2 (mem_interior_iff_mem_nhds.mpr
          (mem_of_superset (hU.mem_nhds ⟨hxI,hp⟩) hUT))
      exact NullCovers.contentZero_mono hsub (contentZero_union
        (GeometricPatches.frontier_contentZero (OneCoordinate.Boxes.jordan_carrier Q))
        (by simpa using NullCovers.finite_faces_contentZero Q {(Fin.last k,0)}))

/-- Compact subsets of a relative model domain have compact Jordan cores.
This does not try to enclose them in one rectangle contained in the domain. -/
lemma parameter_jordan_core {k : ℕ} (half : Bool) {S L : Set (E k)}
    (hS : ∃ W : Set (E k), IsOpen W ∧ S = parameterSpace k half ∩ W)
    (hL : IsCompact L) (hLS : L ⊆ S) :
    ∃ K : Set (E k), IsCompact K ∧ Jordan K ∧ L ⊆ K ∧ K ⊆ S := by
  obtain ⟨W,hW,hSW⟩ := hS
  choose Q hxQ hnd hQW using fun x : L =>
    OneCoordinate.Boxes.exists_closed_box hW x.val ((hSW ▸ hLS x.property).2)
  obtain ⟨t,ht⟩ := hL.elim_finite_subcover (fun x : L => interior (carrier (Q x)))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxQ ⟨x,hx⟩⟩)
  let C : t → Set (E k) := fun i => carrier (Q i.val) ∩ parameterSpace k half
  have hC (i : t) : IsCompact (C i) :=
    (DiscontinuityCriterion.carrier_compact _).inter_right (DirectedSubstitution.parameterSpace_closed k half)
  refine ⟨⋃ i, C i,isCompact_iUnion hC,?_,?_,?_⟩
  · simpa only [Finset.mem_univ,iUnion_true] using
      jordan_finite_union Finset.univ C (fun i _ => parameter_box_jordan _ half)
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,interior_subset hxi,(hSW ▸ hLS hx).1⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hSW ▸ ⟨hi.2,hQW i.val hi.1⟩




open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

abbrev ChartPatch := @Model.ChartPatch

theorem chart_jordan_core : chart_jordan_coreType := by
  intro r k n M c L hL hLS
  exact parameter_jordan_core c.half c.source_open hL hLS

theorem chart_patch_exists : chart_patch_existsType := by
  intro r k n M O c hr hO hMO w hwk hws
  have hk := ManifoldIntegral.chart_weight_compact c w hwk hws
  let L := Subtype.val '' tsupport (fun u : c.source => w (c.toFun u))
  have hL : IsCompact L := hk.image continuous_subtype_val
  have hLS : L ⊆ c.source := by rintro _ ⟨u,_,rfl⟩; exact u.property
  obtain ⟨K,hK,hJK,hLK,hKS⟩ := parameter_jordan_core c.half c.source_open hL hLS
  obtain ⟨P,hPK,hmap,hd⟩ := GeometricPatches.chart_patch_exists c hr O hO K hJK
    (by simpa only [hK.isClosed.closure_eq] using hKS)
    (by
      rw [hK.isClosed.closure_eq]
      intro u hu
      exact hMO (c.map_source (hKS hu)).1)
  refine ⟨⟨P,?_,?_,?_,?_⟩⟩
  · rw [hPK,hK.isClosed.closure_eq]; exact hKS
  · intro u hu; exact hmap (subset_closure (hPK ▸ hu))
  · intro u hu; exact hd u (subset_closure (hPK ▸ hu))
  · intro u hu
    rw [hPK]
    exact hLK ⟨u,subset_tsupport _ hu,rfl⟩

theorem chart_patch_integral : chart_patch_integralType := by
  intro r k n M O c w P omega ho hw
  have hp := GeometricPatches.chart_integral_bridge c P.patch
    (subset_closure.trans P.source) P.map_eq P.differential_eq omega ho w hw
  have heq : (fun u : c.source => if u.val ∈ P.patch.region then
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w u else 0) =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w := by
    funext u
    split_ifs with hu
    · rfl
    · have hz : w (c.toFun u) = 0 := not_not.mp (fun hn => hu (P.covers u hn))
      simp [localizedTopCoefficient,hz]
  dsimp only at hp
  rw [heq] at hp
  exact hp

theorem ambient_restriction_continuous : ambient_restriction_continuousType := by
  intro r k n M O hr hMO omega ho c
  have hc : Continuous (fun u : c.source => c.toFun u) := c.continuous_toFun.domRestrict
  have hd : Continuous (fun u : c.source =>
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u) :=
    (D04MetricDensity.chartDifferential_continuous c hr).domRestrict
  change Continuous (fun u : c.source => omega (c.toFun u)
    (fun j => Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u
      (standardBasis k j)))
  simp_rw [formField_evaluation]
  apply continuous_finsetSum
  intro I _
  apply Continuous.mul
  · exact (ho.2 I).comp_continuous hc (fun u => hMO (c.map_source u.property).1)
  · exact (D04.finiteDimensional_multilinear_continuous k (fun _ => E n)
      (dx (standardBasis n) I).toMultilinearMap).comp
      (continuous_pi (fun j => hd.clm_apply continuous_const))

lemma manifold_patch_value {r : ℕ∞ω} {k n : ℕ} {M O : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (omega : FormField n k)
    (ho : IsCrForm (some 0) O omega)
    (P : SignedChartPartition o (topSupport (GeometricPatches.ambientRestriction omega)))
    (C : ∀ i, ChartPatch (O := O) (P.chart i) (P.weight i)) :
    orientedIntegral (GeometricPatches.ambientRestriction omega) P =
      ∑ i, (P.sign i).val * GeometricPatches.patchIntegral (C i).patch (P.weight i) omega := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg ((P.sign i).val * ·)
    (chart_patch_integral (P.chart i) (P.weight i) (C i) omega ho
      (P.partition.1 i).continuous.continuousOn).2

theorem manifold_patch_expansion : manifold_patch_expansionType := by
  intro r k n M O o hO hMO omega ho P
  have hex i := chart_patch_exists (P.chart i) o.manifold.1 hO hMO (P.weight i)
    (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2
  let C := fun i => Classical.choice (hex i)
  exact ⟨C,manifold_patch_value o omega ho P C⟩

theorem manifold_patch_independent : manifold_patch_independentType := by
  intro r k n M O o hMO omega ho P Q C D
  rw [← manifold_patch_value o omega ho P C,← manifold_patch_value o omega ho Q D]
  exact ManifoldIntegralIndependence.oriented_independent o _
    (ambient_restriction_continuous o.manifold.1 hMO omega ho) P Q


abbrev regularLocus := @Model.regularLocus

theorem common_chart_tangentSpaces : common_chart_tangentSpacesType := by
  intro r k n M N c d hr hkn hsource hmap u hu
  rw [D04.tangentSpace_chart c hr hkn u hu]
  have hd := D04.tangentSpace_chart d hr hkn u (hsource ▸ hu)
  simpa only [hmap,Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential,hsource]
    using hd.symm

theorem regular_locus_charts : regular_locus_chartsType := by
  intro r k n ι _ A Z hZ hA hAm hp x hx
  obtain ⟨i,hxi⟩ := mem_iUnion.mp hx.1
  obtain ⟨U,hU,hxU,hUA⟩ := isolated_piece A Z hA hp i x hxi hx.2
  let T := U ∩ Zᶜ
  have hT : IsOpen T := hU.inter hZ.isOpen_compl
  have hxT : x ∈ T := ⟨hxU,hx.2⟩
  have he : T ∩ A i = T ∩ regularLocus A Z := by
    ext y
    constructor
    · rintro ⟨hyT,hyi⟩
      exact ⟨hyT,mem_iUnion.mpr ⟨i,hyi⟩,hyT.2⟩
    · rintro ⟨hyT,hyR⟩
      exact ⟨hyT,(show y ∈ U ∩ A i from hUA ▸ ⟨hyT.1,hyR.1⟩).2⟩
  obtain ⟨c,u,hcenter,hcu⟩ := (hAm i).2.2 x hxi
  let a := D04.EmbeddedChart.restrict c T hT
  obtain ⟨d,hdsource,hdambient,hdmap,hdinv,hdhalf⟩ := chart_retarget c T hT he
  refine ⟨i,a,d,u,?_,hcu,hdsource,hdmap,hdinv,hdambient,hdhalf⟩
  exact ⟨⟨hcenter.1,by change c.toFun u ∈ T; rw [hcu]; exact hxT⟩,hcenter.2⟩

theorem regular_locus_manifold : regular_locus_manifoldType := by
  intro k n ι _ A s hkn hA hAm hp
  refine ⟨⟨le_rfl,by simp⟩,hkn,?_⟩
  intro x hx
  obtain ⟨i,c,d,u,hc,hcu,hds,hdmap,hdinv,hda,hdhalf⟩ :=
    regular_locus_charts A s.carrier (ambient_seams_compact s).isClosed hA hAm hp x hx
  refine ⟨d,u,?_,?_⟩
  · exact ⟨hds ▸ hc.1,fun hh => hc.2 (hdhalf ▸ hh)⟩
  · rw [hdmap]; exact hcu


theorem regular_locus_tangentSpace : regular_locus_tangentSpaceType := by
  intro r k n ι _ A Z hr hkn hZ hA hAm hp x hx i hi
  obtain ⟨j,c,d,u,hc,hcu,hds,hdmap,hdinv,hda,hdhalf⟩ :=
    regular_locus_charts A Z hZ hA hAm hp x hx
  have hj : x ∈ A j := hcu ▸ (c.map_source hc.1).1
  have hji : j = i := by
    by_contra hn
    exact hx.2 (hp j i hn ⟨hj,hi⟩)
  subst j
  rw [← hcu]
  exact (common_chart_tangentSpaces c d hr hkn hds hdmap u hc.1).symm

/-- Finite box covers control a Darboux integral uniformly for every box.
The error outside the selected neighborhood may be small rather than zero. -/
lemma box_integral_small_near_null {k : ℕ} (Z : Set (E k))
    (hZc : IsCompact Z) (hZ : NullCovers.ContentZero Z)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (E k), IsOpen U ∧ Z ⊆ U ∧
      ∀ (Q : Box k) (f : E k → ℝ) (hf : Integrable f Q)
        (δ : ℝ), 0 ≤ δ →
        (∀ x ∈ carrier Q, |f x| ≤ M) →
        (∀ x ∈ carrier Q, x ∉ U → |f x| ≤ δ) →
        |integral f Q hf| < ε + δ * content Q := by
  let t := ε / (M + 1)
  have ht : 0 < t := div_pos hε (by linarith)
  obtain ⟨ι,hι,R,hR,hsum⟩ :=
    (NullCovers.contentZero_iff_openContentZero Z).mp hZ t ht
  let := hι
  have hRo : IsOpen (⋃ i, NullCovers.openCarrier (R i)) :=
    isOpen_iUnion (fun i => NullCovers.isOpen_openCarrier (R i))
  obtain ⟨U,hU,hZU,hUR⟩ := hZc.exists_isOpen_closure_subset (hRo.mem_nhdsSet.mpr hR)
  refine ⟨U,hU,hZU,?_⟩
  intro Q f hf δ hδ hbound hout
  by_cases hdeg : Degenerate Q
  · have hz : integral f Q hf = 0 := (degenerate_integrals f Q hdeg).1
    rw [hz,abs_zero]
    exact lt_of_lt_of_le hε (le_add_of_nonneg_right (mul_nonneg hδ (content_nonneg Q)))
  have hq : Nondegenerate Q := nondegenerate_of_not_degenerate hdeg
  let V : Option ι → Set (E k) := fun i =>
    match i with
    | none => (closure U)ᶜ
    | some j => NullCovers.openCarrier (R j)
  have hVo : ∀ i, IsOpen (V i) := by
    intro i
    cases i with
    | none => exact isClosed_closure.isOpen_compl
    | some i => exact NullCovers.isOpen_openCarrier _
  have hcover : carrier Q ⊆ ⋃ i, carrier Q ∩ V i := by
    intro x hx
    by_cases hxU : x ∈ closure U
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (hUR hxU)
      exact mem_iUnion.mpr ⟨some i,hx,hi⟩
    · exact mem_iUnion.mpr ⟨none,hx,hxU⟩
  obtain ⟨η,hη,hsmall⟩ := D04.lebesgue_number (carrier Q) (fun i => carrier Q ∩ V i)
    ((D04.compact_iff_isCompact _).mpr (DiscontinuityCriterion.carrier_compact Q))
    (fun i => (D04.relativelyOpen_iff _ _).mpr ⟨V i,hVo i,rfl⟩) hcover
  obtain ⟨P,hP⟩ := arbitrarily_fine Q hq η hη
  have hcell (c : CellIndex P) : ∃ i, cell P c ⊆ V i := by
    obtain ⟨i,hi⟩ := hsmall _ (cell_nonempty P c) (cell_subset P c)
      ((cell_diam_le_mesh P c).trans_lt hP)
    exact ⟨i,fun x hx => (hi hx).2⟩
  let F : Finset (CellIndex P) := Finset.univ.filter
    (fun c => ∃ i, cell P c ⊆ NullCovers.openCarrier (R i))
  have hFsum : (∑ c ∈ F, cellContent P c) < t := by
    have hcov : ∀ c ∈ F, cell P c ⊆ ⋃ i, carrier (R i) := by
      intro c hc
      obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hc).2
      exact fun x hx => mem_iUnion.mpr ⟨i,NullCovers.openCarrier_subset _ (hi hx)⟩
    exact (ENNReal.ofReal_lt_ofReal_iff ht).mp
      ((DiscontinuityCriterion.grid_content_le_cover P F R hcov).trans_lt hsum)
  have hsup (c : CellIndex P) :
      cellSupremum (fun x => |f x|) P c ≤ (if c ∈ F then M else 0) + δ := by
    apply csSup_le ((cell_nonempty P c).image (fun x => |f x|))
    rintro _ ⟨x,hx,rfl⟩
    by_cases hc : c ∈ F
    · simp only [ite_eq_left hc]
      exact (hbound x (cell_subset P c hx)).trans (le_add_of_nonneg_right hδ)
    · simp only [ite_eq_right hc,zero_add]
      obtain ⟨i,hi⟩ := hcell c
      cases i with
      | none => exact hout x (cell_subset P c hx) (fun h => hi hx (subset_closure h))
      | some i => exact False.elim (hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi⟩))
  have hupp : upperSum (fun x => |f x|) P ≤
      M * (∑ c ∈ F, cellContent P c) + δ * content Q := by
    calc
      _ ≤ ∑ c, (((if c ∈ F then M else 0) + δ) * cellContent P c) :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_right (hsup c) (cellContent_nonneg P c))
      _ = _ := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib,← Finset.mul_sum,content_partition]
        congr 1
        rw [Finset.mul_sum]
        simp only [ite_mul,zero_mul]
        simp
  have hMt : M * (∑ c ∈ F, cellContent P c) < ε := by
    have h1 := mul_le_mul_of_nonneg_left hFsum.le hM
    have h2 : t * (M + 1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  exact ((integral_abs_bound hf (integrable_abs hf)).1.trans
    ((integral_bounds _ Q (integrable_abs hf) P).2.trans hupp)).trans_lt
      (by linarith)

/-- The neighborhood estimate for actual zero-extended region integrals. -/
lemma region_integral_small_near_null {k : ℕ} (Z : Set (E k))
    (hZc : IsCompact Z) (hZ : NullCovers.ContentZero Z)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (E k), IsOpen U ∧ Z ⊆ U ∧
      ∀ (S : Set (E k)), Jordan S → ∀ (f : S → ℝ), RegionIntegrable f →
        ∀ δ : ℝ, 0 ≤ δ → (∀ x, |f x| ≤ M) →
        (∀ x : S, x.val ∉ U → |f x| ≤ δ) →
        |regionIntegral f| < ε + δ * content (enclosingBox S) := by
  obtain ⟨U,hU,hZU,hsmall⟩ := box_integral_small_near_null Z hZc hZ M hM ε hε
  refine ⟨U,hU,hZU,?_⟩
  intro S hS f hf δ hδ hbound hout
  have hQ := enclosingBox_encloses (jordan_bounded hS)
  have hi := ((integrable_iff_on_enclosing_box f hQ).mp hf).2
  rw [integral_eq_on_enclosing_box f hf hQ hi]
  apply hsmall _ _ hi δ hδ
  · intro x hx
    by_cases hxS : x ∈ S
    · simpa only [zeroExtension_apply f ⟨x,hxS⟩] using hbound ⟨x,hxS⟩
    · simpa [zeroExtension_of_not_mem f hxS] using hM
  · intro x hx hxU
    by_cases hxS : x ∈ S
    · simpa only [zeroExtension_apply f ⟨x,hxS⟩] using hout ⟨x,hxS⟩ hxU
    · simpa [zeroExtension_of_not_mem f hxS] using hδ

/-- Uniform convergence away from every neighborhood of a compact null set,
together with a uniform bound, gives convergence of the actual region values.
Integrability is retained explicitly; no measurable integral is substituted. -/
theorem region_seam_limit {k : ℕ} {S : Set (E k)} (hS : Jordan S)
    (Z : Set (E k)) (hZc : IsCompact Z) (hZ : NullCovers.ContentZero Z)
    (f : S → ℝ) (g : ℕ → S → ℝ) (hf : RegionIntegrable f)
    (hg : ∀ m, RegionIntegrable (g m)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ m x, |g m x - f x| ≤ M)
    (hconv : ∀ U : Set (E k), IsOpen U → Z ⊆ U → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in atTop, ∀ x : S, x.val ∉ U → |g m x - f x| ≤ δ) :
    Tendsto (fun m => regionIntegral (g m)) atTop (𝓝 (regionIntegral f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U,hU,hZU,hsmall⟩ := region_integral_small_near_null Z hZc hZ M hM
    (ε / 2) (half_pos hε)
  let C := content (enclosingBox S)
  have hC : 0 ≤ C := content_nonneg _
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (2 * (C + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hconv U hU hZU δ hδ] with m hm
  have hd := SlicingAndMoments.region_sub (jordan_bounded hS) (g m) f (hg m) hf
  have hest := hsmall S hS _ hd.1 δ hδ.le (hbound m) hm
  rw [Real.dist_eq,← hd.2]
  exact hest.trans (by change ε / 2 + δ * C < ε; nlinarith)

/-- Smooth ambient deletion of the geometric seams changes any continuous
coefficient integral on a compact Jordan chart core by arbitrarily little. -/
theorem chart_seam_cutoff {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (hkn : k ≤ n) (s : AmbientSeams k n)
    (K : Set (E k)) (hK : IsCompact K) (hKJ : Jordan K) (hKs : K ⊆ c.source)
    (f : E k → ℝ) (hf : ContinuousOn f K) (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : E n → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∃ V : Set (E n), IsOpen V ∧ s.carrier ⊆ V ∧ EqOn χ (fun _ => 0) V) ∧
      RegionIntegrable (fun x : K => χ (c.toFun x) * f x) ∧
      |regionIntegral (fun x : K => χ (c.toFun x) * f x) -
        regionIntegral (fun x : K => f x)| < ε := by
  have hc : ContinuousOn c.toFun K := c.continuous_toFun.mono hKs
  have hImage : IsCompact (c.toFun '' K) := hK.image_of_continuousOn hc
  have hTarget : c.toFun '' K ⊆ M ∩ c.ambient := by
    rintro _ ⟨x,hx,rfl⟩
    exact c.map_source (hKs hx)
  let Z := c.invFun '' (s.carrier ∩ (c.toFun '' K))
  have hz := chart_seams_contentZero c hkn s _ hImage hTarget
  obtain ⟨B,hB,hfB⟩ := (hK.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  have hbound : ∀ x : K, |f x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hfB (f x) (mem_image_of_mem f x.property)
  obtain ⟨U,hU,hZU,hsmall⟩ := region_integral_small_near_null Z hz.1 hz.2 B hB.le ε hε
  let A := c.toFun '' (K \ U)
  have hA : IsCompact A := (hK.diff hU).image_of_continuousOn (hc.mono sdiff_subset)
  have hsA : s.carrier ⊆ Aᶜ := by
    intro y hy
    rintro ⟨x,⟨hx,hxU⟩,hxy⟩
    apply hxU
    apply hZU
    exact ⟨y,⟨hy,⟨x,hx,hxy⟩⟩,by rw [← hxy]; exact c.left_inv x (hKs hx)⟩
  obtain ⟨η,hη⟩ := EuclideanSmoothCutoffs.exists_smooth_cutoff
    s.carrier Aᶜ (ambient_seams_compact s) hA.isClosed.isOpen_compl hsA
  let χ : E n → ℝ := fun y => 1 - η y
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub hη.1
  have hχv : ∀ y, χ y ∈ Icc (0 : ℝ) 1 := by
    intro y
    obtain ⟨hl,hu⟩ := hη.2.2.1 y
    exact ⟨by dsimp [χ]; linarith, by dsimp [χ]; linarith⟩
  have hfi : RegionIntegrable (fun x : K => f x) :=
    GeometricPatches.continuous_integrable hKJ (by simpa [hK.isClosed.closure_eq] using hf)
  have hgi : RegionIntegrable (fun x : K => χ (c.toFun x) * f x) :=
    GeometricPatches.continuous_integrable hKJ (by
      rw [hK.isClosed.closure_eq]
      exact ((hχ.continuous.continuousOn.comp hc (fun _ _ => mem_univ _))).mul hf)
  have hd := SlicingAndMoments.region_sub (jordan_bounded hKJ) _ _ hgi hfi
  have herr : |regionIntegral (fun x : K => χ (c.toFun x) * f x - f x)| < ε := by
    have hest := hsmall K hKJ _ hd.1 0 le_rfl (by
      intro x
      have hv := hη.2.2.1 (c.toFun x)
      have he : χ (c.toFun x) * f x - f x = -η (c.toFun x) * f x := by dsimp [χ]; ring
      rw [he,abs_mul,abs_neg,abs_of_nonneg hv.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hv.2).trans (hbound x)) (by
      intro x hxU
      have hxA : c.toFun x ∈ A := ⟨x,⟨x.property,hxU⟩,rfl⟩
      have hzη : η (c.toFun x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hη.2.2.2.2.2 h hxA)
      simp [χ,hzη])
    simpa only [zero_mul,add_zero] using hest
  refine ⟨χ,hχ,hχv,?_,hgi,?_⟩
  · obtain ⟨V,hV,hsV,hone⟩ := hη.2.2.2.1
    exact ⟨V,hV,hsV,fun y hy => by dsimp [χ]; rw [hone hy]; ring⟩
  · rwa [hd.2] at herr

/-- A compact ambient exceptional set admits smooth deletions which are
identically one eventually on each compact set disjoint from it. -/
theorem smooth_seam_cutoff_sequence {n : ℕ} (Z : Set (E n)) (hZ : IsCompact Z) :
    ∃ χ : ℕ → E n → ℝ,
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧
      (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, ∃ V : Set (E n), IsOpen V ∧ Z ⊆ V ∧ EqOn (χ m) (fun _ => 0) V) ∧
      (∀ A : Set (E n), IsCompact A → Disjoint A Z →
        ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) := by
  by_cases hZe : Z = ∅
  · subst Z
    refine ⟨fun _ _ => 1,fun _ => contDiff_const,fun _ _ => ⟨zero_le_one,le_rfl⟩,
      fun _ => ⟨∅,isOpen_empty,subset_rfl,by simp⟩,?_⟩
    intro A hA hd
    exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
  have hZne : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZe
  let V : ℕ → Set (E n) := fun m => {y | Metric.infDist y Z < 1 / ((m : ℝ) + 1)}
  have hV : ∀ m, IsOpen (V m) := fun m => isOpen_lt (Metric.continuous_infDist_pt Z) continuous_const
  have hZV : ∀ m, Z ⊆ V m := by
    intro m y hy
    change Metric.infDist y Z < 1 / ((m : ℝ) + 1)
    rw [Metric.infDist_zero_of_mem hy]
    positivity
  choose η hη using fun m => EuclideanSmoothCutoffs.exists_smooth_cutoff Z (V m) hZ (hV m) (hZV m)
  refine ⟨fun m y => 1 - η m y,fun m => contDiff_const.sub (hη m).1,?_,?_,?_⟩
  · intro m y
    obtain ⟨hl,hu⟩ := (hη m).2.2.1 y
    exact ⟨by linarith,by linarith⟩
  · intro m
    obtain ⟨W,hW,hZW,hone⟩ := (hη m).2.2.2.1
    exact ⟨W,hW,hZW,fun y hy => by change 1 - η m y = 0; rw [hone hy]; ring⟩
  · intro A hA hd
    obtain ⟨r,hr,hrA⟩ := hA.exists_forall_le' (Metric.continuous_infDist_pt Z).continuousOn
      (fun y hy => (hZ.isClosed.notMem_iff_infDist_pos hZne).mp
        (fun hyZ => Set.disjoint_left.mp hd hy hyZ))
    have hev : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < r :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
    filter_upwards [hev] with m hm y hy
    have hout : y ∉ V m := not_lt.mpr ((hm.trans_le (hrA y hy)).le)
    have hzη : η m y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hout ((hη m).2.2.2.2.2 hh))
    simp [hzη]

/-- Smooth seam deletions converge in each compact chart's actual coefficient
integral. The ambient cutoffs may be chosen once for every chart core. -/
theorem chart_seam_cutoff_limit {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (hkn : k ≤ n) (s : AmbientSeams k n)
    (K : Set (E k)) (hK : IsCompact K) (hKJ : Jordan K) (hKs : K ⊆ c.source)
    (f : E k → ℝ) (hf : ContinuousOn f K)
    (χ : ℕ → E n → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) :
    (∀ m, RegionIntegrable (fun x : K => χ m (c.toFun x) * f x)) ∧
      Tendsto (fun m => regionIntegral (fun x : K => χ m (c.toFun x) * f x))
        atTop (𝓝 (regionIntegral (fun x : K => f x))) := by
  have hc : ContinuousOn c.toFun K := c.continuous_toFun.mono hKs
  have hImage : IsCompact (c.toFun '' K) := hK.image_of_continuousOn hc
  have hTarget : c.toFun '' K ⊆ M ∩ c.ambient := by
    rintro _ ⟨x,hx,rfl⟩
    exact c.map_source (hKs hx)
  let Z := c.invFun '' (s.carrier ∩ (c.toFun '' K))
  have hz := chart_seams_contentZero c hkn s _ hImage hTarget
  have hfi : RegionIntegrable (fun x : K => f x) :=
    GeometricPatches.continuous_integrable hKJ (by simpa [hK.isClosed.closure_eq] using hf)
  have hgi (m : ℕ) : RegionIntegrable (fun x : K => χ m (c.toFun x) * f x) :=
    GeometricPatches.continuous_integrable hKJ (by
      rw [hK.isClosed.closure_eq]
      exact (((hχ m).continuous.continuousOn.comp hc (fun _ _ => mem_univ _))).mul hf)
  refine ⟨hgi,?_⟩
  obtain ⟨B,hB,hfB⟩ := (hK.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  apply region_seam_limit hKJ Z hz.1 hz.2 _ _ hfi hgi B hB.le
  · intro m x
    obtain ⟨hl,hu⟩ := hχv m (c.toFun x)
    have he : χ m (c.toFun x) * f x - f x = (χ m (c.toFun x) - 1) * f x := by ring
    rw [he,abs_mul]
    have hv : |χ m (c.toFun x) - 1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    exact (mul_le_of_le_one_left (abs_nonneg _) hv).trans (by
      simpa only [Real.norm_eq_abs] using hfB (f x) (mem_image_of_mem f x.property))
  · intro U hU hZU δ hδ
    let A := c.toFun '' (K \ U)
    have hA : IsCompact A := (hK.diff hU).image_of_continuousOn (hc.mono sdiff_subset)
    have hdis : Disjoint A s.carrier := Set.disjoint_left.mpr (by
      rintro y ⟨x,⟨hx,hxU⟩,hxy⟩ hy
      apply hxU
      apply hZU
      exact ⟨y,⟨hy,⟨x,hx,hxy⟩⟩,by rw [← hxy]; exact c.left_inv x (hKs hx)⟩)
    filter_upwards [hχone A hA hdis] with m hm x hxU
    have hxA : c.toFun x ∈ A := ⟨x,⟨x.property,hxU⟩,rfl⟩
    simpa [hm hxA] using hδ.le

/-- Restricting a represented coefficient to a core containing its support
preserves its actual ambient zero extension and hence its proper value. -/
lemma coefficient_restrict_core {k : ℕ} {S K : Set (E k)} (hKS : K ⊆ S)
    (f : S → ℝ) (hsupport : ∀ u, f u ≠ 0 → u.val ∈ K) :
    (DirectedSubstitution.ProperIntegrable f ↔
      DirectedSubstitution.ProperIntegrable (fun x : K => f ⟨x,hKS x.property⟩)) ∧
    DirectedSubstitution.coefficientIntegral f =
      DirectedSubstitution.coefficientIntegral (fun x : K => f ⟨x,hKS x.property⟩) := by
  apply DirectedSubstitution.proper_congr
  funext x
  by_cases hxK : x ∈ K
  · rw [zeroExtension_apply f ⟨x,hKS hxK⟩,
      zeroExtension_apply (fun y : K => f ⟨y,hKS y.property⟩) ⟨x,hxK⟩]
  · rw [zeroExtension_of_not_mem _ hxK]
    by_cases hxS : x ∈ S
    · rw [zeroExtension_apply f ⟨x,hxS⟩]
      exact not_not.mp (fun hn => hxK (hsupport ⟨x,hxS⟩ hn))
    · exact zeroExtension_of_not_mem f hxS

/-- Actual proper chart coefficients converge under the same ambient seam
cutoffs; compact Jordan cores are constructed rather than assumed. -/
theorem coefficient_seam_cutoff_limit {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 k n M) (hkn : k ≤ n) (s : AmbientSeams k n)
    (f : c.source → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (χ : ℕ → E n → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A) :
    (∀ m, DirectedSubstitution.ProperIntegrable (fun u => χ m (c.toFun u) * f u)) ∧
      Tendsto (fun m => DirectedSubstitution.coefficientIntegral
        (fun u : c.source => χ m (c.toFun u) * f u))
        atTop (𝓝 (DirectedSubstitution.coefficientIntegral f)) := by
  let L := Subtype.val '' tsupport f
  have hL : IsCompact L := hfc.image continuous_subtype_val
  have hLS : L ⊆ c.source := by rintro _ ⟨u,_,rfl⟩; exact u.property
  obtain ⟨K,hK,hKJ,hLK,hKS⟩ := parameter_jordan_core c.half c.source_open hL hLS
  have hsupport : ∀ u, f u ≠ 0 → u.val ∈ K :=
    fun u hu => hLK ⟨u,subset_tsupport _ hu,rfl⟩
  let F := zeroExtension f
  have hF : ContinuousOn F K := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun x : K => F x) = fun x : K => f ⟨x,hKS x.property⟩ := by
      funext x
      exact zeroExtension_apply f ⟨x,hKS x.property⟩
    change Continuous (fun x : K => F x)
    rw [he]
    exact hf.comp (continuous_inclusion hKS)
  have hl := chart_seam_cutoff_limit c hkn s K hK hKJ hKS F hF χ hχ hχv hχone
  have heq : (fun x : K => F x) = fun x : K => f ⟨x,hKS x.property⟩ := by
    funext x
    exact zeroExtension_apply f ⟨x,hKS x.property⟩
  have hfeq : regionIntegral (fun x : K => F x) =
      DirectedSubstitution.coefficientIntegral f := by
    calc
      _ = DirectedSubstitution.coefficientIntegral (fun x : K => F x) :=
        (GeometricPatches.region_coefficient_integral hKJ (fun x : K => F x)
          (GeometricPatches.continuous_integrable hKJ
            (by simpa [hK.isClosed.closure_eq] using hF))).2
      _ = _ := by rw [heq,← (coefficient_restrict_core hKS f hsupport).2]
  have hgeq (m : ℕ) : regionIntegral (fun x : K => χ m (c.toFun x) * F x) =
      DirectedSubstitution.coefficientIntegral (fun u : c.source => χ m (c.toFun u) * f u) := by
    calc
      _ = DirectedSubstitution.coefficientIntegral (fun x : K => χ m (c.toFun x) * F x) :=
        (GeometricPatches.region_coefficient_integral hKJ _ (hl.1 m)).2
      _ = _ := ?_
    have hg := coefficient_restrict_core hKS (fun u : c.source => χ m (c.toFun u) * f u)
      (fun u hu => hsupport u (fun hz => hu (by rw [hz,mul_zero])))
    rw [hg.2]
    congr 1
    funext x
    rw [show F x = f ⟨x,hKS x.property⟩ from zeroExtension_apply f ⟨x,hKS x.property⟩]
  constructor
  · intro m
    have hi := (GeometricPatches.region_coefficient_integral hKJ _ (hl.1 m)).1
    have hg := coefficient_restrict_core hKS (fun u : c.source => χ m (c.toFun u) * f u)
      (fun u hu => hsupport u (fun hz => hu (by rw [hz,mul_zero])))
    apply hg.1.mpr
    convert hi using 1
    funext x
    exact congrArg (χ m (c.toFun x) * ·) (zeroExtension_apply f ⟨x,hKS x.property⟩).symm
  · simpa only [hgeq,hfeq] using hl.2

open Specs.D04.C14.MetricTopFormsAndDensities.Model

/-- Passage across seam neighborhoods for the prescribed oriented manifold
integrals, allowing an independent chart partition at every cutoff stage. -/
theorem manifold_seam_cutoff_limit {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 k M) (s : AmbientSeams k n)
    (η : TangentTopField 1 k M) (hη : ContinuousTopField η)
    (χ : ℕ → E n → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχv : ∀ m x, χ m x ∈ Icc (0 : ℝ) 1)
    (hχone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (χ m) (fun _ => 1) A)
    (P : SignedChartPartition o (topSupport η))
    (Q : ∀ m, SignedChartPartition o (topSupport (fun x : M => χ m x • η x))) :
    Tendsto (fun m => orientedIntegral (fun x : M => χ m x • η x) (Q m))
      atTop (𝓝 (orientedIntegral η P)) := by
  have hlim (i : Fin P.count) := coefficient_seam_cutoff_limit (P.chart i) o.manifold.2.1 s
    (localizedTopCoefficient η (P.chart i) (P.weight i))
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).1
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).2.1
    χ hχ hχv hχone
  have heq (m : ℕ) : orientedIntegral (fun x : M => χ m x • η x) (Q m) =
      ∑ i, (P.sign i).val * DirectedSubstitution.coefficientIntegral
        (fun u : (P.chart i).source => χ m ((P.chart i).toFun u) *
          localizedTopCoefficient η (P.chart i) (P.weight i) u) := by
    have hh := ManifoldIntegralIndependence.oriented_comparison o
      (fun x : M => χ m x • η x)
      (ManifoldIntegralIndependence.continuousTopField_weight (χ m) (hχ m).continuous hη)
      (Q m) P Subset.rfl (ManifoldIntegralIndependence.topSupport_weight_subset _ η)
    change orientedIntegral (fun x : M => χ m x • η x) (Q m) = _ at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    funext u
    simp only [localizedTopCoefficient,ManifoldIntegralIndependence.topCoefficient_weight]
    ring
  simp_rw [heq]
  exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul (hlim i).2)

/-- One ambient smooth cutoff sequence works for all compact manifold pieces.
Its localized supports are compact and avoid the seams, and the prescribed
actual oriented integrals converge with arbitrary choices of partitions. -/
theorem manifold_seam_cutoffs {k n : ℕ} (s : AmbientSeams k n) :
    ∃ χ : ℕ → E n → ℝ,
      (∀ m, ContDiff ℝ ∞ (χ m)) ∧
      (∀ m x, χ m x ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, ∃ V : Set (E n), IsOpen V ∧ s.carrier ⊆ V ∧ EqOn (χ m) (fun _ => 0) V) ∧
      ∀ (M : Set (E n)), IsCompact M →
      ∀ (o : PositiveManifoldOrientation 1 k M) (η : TangentTopField 1 k M),
        ContinuousTopField η →
        (∀ m, IsCompact (Subtype.val '' topSupport (fun x : M => χ m x • η x)) ∧
          Disjoint (Subtype.val '' topSupport (fun x : M => χ m x • η x)) s.carrier) ∧
        ∀ (P : SignedChartPartition o (topSupport η))
          (Q : ∀ m, SignedChartPartition o (topSupport (fun x : M => χ m x • η x))),
          Tendsto (fun m => orientedIntegral (fun x : M => χ m x • η x) (Q m))
            atTop (𝓝 (orientedIntegral η P)) := by
  obtain ⟨χ,hχ,hχv,hχzero,hχone⟩ := smooth_seam_cutoff_sequence s.carrier (ambient_seams_compact s)
  refine ⟨χ,hχ,hχv,hχzero,?_⟩
  intro M hM o η hη
  constructor
  · intro m
    let : CompactSpace M := isCompact_iff_compactSpace.mp hM
    constructor
    · exact isClosed_closure.isCompact.image continuous_subtype_val
    · obtain ⟨V,hV,hsV,hzero⟩ := hχzero m
      have hs : topSupport (fun x : M => χ m x • η x) ⊆ (Subtype.val ⁻¹' V)ᶜ := by
        apply closure_minimal _ (hV.preimage continuous_subtype_val).isClosed_compl
        intro x hx hxV
        apply hx
        change χ m x • η x = 0
        rw [hzero hxV,zero_smul]
      apply Set.disjoint_left.mpr
      rintro y ⟨x,hx,rfl⟩ hy
      exact hs hx (hsV hy)
  · intro P Q
    exact manifold_seam_cutoff_limit o s η hη χ hχ hχv hχone P Q


abbrev transportOrientation := @Model.transportOrientation

/-- Equal tangent subspaces are identified by the actual identity on ambient
vectors. The arbitrary ray representative does not affect the sign. -/
lemma transported_orientation_sign {k n : ℕ} {P Q : Submodule ℝ (E n)}
    (h : P = Q) (p : Orientation ℝ P (Fin k)) (q : Orientation ℝ Q (Fin k))
    (hq : q = transportOrientation h p) (v : Fin k → P) (w : Fin k → Q)
    (hvw : ∀ i, (v i).val = (w i).val) :
    Real.sign (p.someVector v) = Real.sign (q.someVector w) := by
  subst Q
  have hqp : q = p := by
    simpa [transportOrientation, Model.transportOrientation, LinearEquiv.ofEq_rfl,
      Orientation.map_refl] using hq
  rw [hqp]
  have hvw' : v = w := funext (fun i => Subtype.ext (hvw i))
  rw [hvw']

/-- Chart signs agree across distinct carriers when the tangent orientations
are transported by the identity on their equal tangent spaces. -/
theorem chart_sign_transport {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N)
    (hr : ManifoldRegularity r) (hs : d.source ⊆ c.source) (hf : d.toFun = c.toFun)
    (a : TangentOrientationField r k M) (b : TangentOrientationField r k N)
    (u : E k) (hu : u ∈ d.source)
    (ht : tangentSpace r k N (d.toFun u) = tangentSpace r k M (c.toFun u))
    (ho : a (c.toFun u) (c.map_source (hs hu)).1 =
      transportOrientation ht (b (d.toFun u) (d.map_source hu).1)) :
    chartSign a c u (hs hu) = chartSign b d u hu := by
  have hd : chartDifferential d u = chartDifferential c u := by
    apply (D04.EmbeddedChart.source_uniqueDiff d u hu).eq
      (D04.EmbeddedChart.hasDifferential d hr hu)
    rw [hf]
    exact (D04.EmbeddedChart.hasDifferential c hr (hs hu)).mono hs
  exact (transported_orientation_sign ht _ _ ho
    (fun i => tangentChartMap d u hu (standardBasis k i))
    (fun i => tangentChartMap c u (hs hu) (standardBasis k i))
    (fun i => DFunLike.congr_fun hd (standardBasis k i))).symm

/-- The orientations on the disjoint piece germs glue on the actual regular
locus. No smooth structure on the whole cornered union is required. -/
theorem regular_locus_orientation {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)) (hr : ManifoldRegularity r)
    (hk : 0 < k) (hkn : k ≤ n) (hZ : IsClosed Z)
    (hA : ∀ i, IsCompact (A i)) (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (hp : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z) :
    ∃ p : PositiveManifoldOrientation r k (regularLocus A Z),
      ∀ x (hx : x ∈ regularLocus A Z) i (hi : x ∈ A i),
        ∃ h : tangentSpace r k (A i) x = tangentSpace r k (regularLocus A Z) x,
          p.atPoint x hx = transportOrientation h ((o i).atPoint x hi) := by
  let R := regularLocus A Z
  have hAm : ∀ i, IsEmbeddedManifold r k (A i) := fun i => (o i).manifold
  have hRm : IsEmbeddedManifold r k R := by
    refine ⟨hr,hkn,?_⟩
    intro x hx
    obtain ⟨i,c,d,u,hc,hcu,hds,hdf,hdi,hda,hdh⟩ :=
      regular_locus_charts A Z hZ hA hAm hp x hx
    exact ⟨d,u,⟨hds ▸ hc.1,fun hh => hc.2 (hdh ▸ hh)⟩,hdf ▸ hcu⟩
  have piece (x : E n) (hx : x ∈ R) : ∃ i, x ∈ A i := mem_iUnion.mp hx.1
  let idx := fun x hx => Classical.choose (piece x hx)
  have idx_mem (x : E n) (hx : x ∈ R) : x ∈ A (idx x hx) :=
    Classical.choose_spec (piece x hx)
  let F : TangentOrientationField r k R := fun x hx =>
    transportOrientation
      (regular_locus_tangentSpace A Z hr hkn hZ hA hAm hp x hx (idx x hx) (idx_mem x hx)).symm
      ((o (idx x hx)).atPoint x (idx_mem x hx))
  have compat (x : E n) (hx : x ∈ R) (i : ι) (hi : x ∈ A i) :
      F x hx = transportOrientation
        (regular_locus_tangentSpace A Z hr hkn hZ hA hAm hp x hx i hi).symm
          ((o i).atPoint x hi) := by
    have he : idx x hx = i := by
      by_contra hn
      exact hx.2 (hp (idx x hx) i hn ⟨idx_mem x hx,hi⟩)
    dsimp [F]
    congr 1 <;> cases he <;> rfl
  refine ⟨⟨hk,hRm,F,?_⟩,fun x hx i hi =>
    ⟨(regular_locus_tangentSpace A Z hr hkn hZ hA hAm hp x hx i hi).symm,
      compat x hx i hi⟩⟩
  intro c
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro u
  let x := c.toFun u
  have hx : x ∈ R := (c.map_source u.property).1
  obtain ⟨i,hi⟩ := piece x hx
  obtain ⟨U,hU,hxU,hUA⟩ := isolated_piece A Z hA hp i x hi hx.2
  let T := U ∩ Zᶜ
  have hT : IsOpen T := hU.inter hZ.isOpen_compl
  have hxT : x ∈ T := ⟨hxU,hx.2⟩
  have he : T ∩ R = T ∩ A i := by
    ext y
    constructor
    · rintro ⟨hyT,hyR⟩
      exact ⟨hyT,(show y ∈ U ∩ A i from hUA ▸ ⟨hyT.1,hyR.1⟩).2⟩
    · rintro ⟨hyT,hyi⟩
      exact ⟨hyT,mem_iUnion.mpr ⟨i,hyi⟩,hyT.2⟩
  obtain ⟨d,hds,hda,hdf,hdi,hdh⟩ := chart_retarget c T hT he
  have hs : d.source ⊆ c.source := hds ▸ inter_subset_left
  have hud : (u : E k) ∈ d.source := hds ▸ ⟨u.property,hxT⟩
  have sign_eq (v : d.source) : chartSign F c v (hs v.property) =
      chartSign (o i).atPoint d v v.property := by
    have hvR : c.toFun v ∈ R := (c.map_source (hs v.property)).1
    have hvi : c.toFun v ∈ A i := by simpa only [hdf] using (d.map_source v.property).1
    have ht : tangentSpace r k (A i) (d.toFun v) = tangentSpace r k R (c.toFun v) := by
      rw [hdf]
      exact (regular_locus_tangentSpace A Z hr hkn hZ hA hAm hp _ hvR i hvi).symm
    apply chart_sign_transport c d hr hs hdf F (o i).atPoint v v.property ht
    have htransport (y : E n) (hy : y ∈ A i) (heq : y = c.toFun v)
        (ht' : tangentSpace r k (A i) y = tangentSpace r k R (c.toFun v)) :
        F (c.toFun v) hvR = transportOrientation ht' ((o i).atPoint y hy) := by
      subst y
      exact compat (c.toFun v) hvR i hy
    exact htransport _ _ (congrFun hdf v) ht
  have hopen : IsOpen ((Subtype.val : c.source → E k) ⁻¹' d.source) := by
    have hc : Continuous (fun v : c.source => c.toFun v) :=
      continuousOn_iff_continuous_domRestrict.mp c.continuous_toFun
    convert hT.preimage hc using 1
    ext v
    simp only [mem_preimage, hds, mem_inter_iff, v.property, true_and]
  have hem := Topology.IsOpenEmbedding.inclusion hs hopen
  obtain ⟨V,hV,huV,hconst⟩ := (o i).locally_constant d |>.exists_open ⟨u,hud⟩
  refine ⟨Set.inclusion hs '' V,hem.isOpenMap V hV,⟨⟨u,hud⟩,huV,rfl⟩,?_⟩
  rintro v ⟨w,hw,rfl⟩
  exact (sign_eq w).trans ((hconst w hw).trans (sign_eq ⟨u,hud⟩).symm)


/-- The inherited regular-locus orientation is unique, so it is independent
of the pointwise choice of the containing piece used during construction. -/
theorem regular_locus_orientation_unique {r : ℕ∞ω} {k n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (Z : Set (E n)) (hr : ManifoldRegularity r)
    (hk : 0 < k) (hkn : k ≤ n) (hZ : IsClosed Z)
    (hA : ∀ i, IsCompact (A i)) (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (hp : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z) :
    ∃! p : PositiveManifoldOrientation r k (regularLocus A Z),
      ∀ x (hx : x ∈ regularLocus A Z) i (hi : x ∈ A i),
        ∃ h : tangentSpace r k (A i) x = tangentSpace r k (regularLocus A Z) x,
          p.atPoint x hx = transportOrientation h ((o i).atPoint x hi) := by
  obtain ⟨p,hp'⟩ := regular_locus_orientation A Z hr hk hkn hZ hA o hp
  refine ⟨p,hp',?_⟩
  intro q hq
  have he : q.atPoint = p.atPoint := by
    funext x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx.1
    obtain ⟨h,hh⟩ := hq x hx i hi
    obtain ⟨g,hg⟩ := hp' x hx i hi
    rw [hh,hg]
  cases q
  cases p
  cases he
  rfl

/-- Transport is functorial for the actual ambient-identity equivalences. -/
lemma transportOrientation_trans {k n : ℕ} {P Q S : Submodule ℝ (E n)}
    (h : P = Q) (g : Q = S) (o : Orientation ℝ P (Fin k)) :
    transportOrientation g (transportOrientation h o) = transportOrientation (h.trans g) o := by
  subst Q
  subst S
  simp [transportOrientation,Model.transportOrientation,LinearEquiv.ofEq_rfl,Orientation.map_refl]

abbrev appendSeams := @Model.appendSeams

/-- Both countable geometric coverings are retained. -/
theorem append_seams_carrier : append_seams_carrierType := by
  intro k n s t
  rfl


/-- Geometric equality of the union plus compatible prescribed orientations
makes the inherited regular orientation independent of both decompositions. -/
theorem common_regular_orientation : common_regular_orientationType := by
  intro r k n ι κ _ _ A B Z W hr hk hkn hZ hW hA hB o p hpA hpB hcover hc
  let T := Z ∪ W
  have hT : IsClosed T := hZ.union hW
  have hpA' : ∀ i j, i ≠ j → A i ∩ A j ⊆ T :=
    fun i j hij x hx => Or.inl (hpA i j hij hx)
  have hpB' : ∀ i j, i ≠ j → B i ∩ B j ⊆ T :=
    fun i j hij x hx => Or.inr (hpB i j hij hx)
  have hR : regularLocus B T = regularLocus A T := by
    simp only [regularLocus,Model.regularLocus,hcover]
  obtain ⟨q,hq,huq⟩ := regular_locus_orientation_unique A T hr hk hkn hT hA o hpA'
  refine ⟨q,⟨hq,?_⟩,fun e he => huq e he.1⟩
  intro x hx j hj
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx.1
  obtain ⟨ha,hqa⟩ := hq x hx i hi
  have hxb : x ∈ regularLocus B T := hR.symm ▸ hx
  have hb : tangentSpace r k (B j) x = tangentSpace r k (regularLocus A T) x := by
    rw [← hR]
    exact (regular_locus_tangentSpace B T hr hkn hT hB (fun j => (p j).manifold)
      hpB' x hxb j hj).symm
  refine ⟨hb,?_⟩
  rw [← hc x hx.2 i j hi hj (ha.trans hb.symm)]
  exact hqa.trans (transportOrientation_trans (ha.trans hb.symm) hb ((o i).atPoint x hi)).symm

/-! Locality for actual full chart coefficients on distinct carriers. -/

lemma common_chart_differential {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N)
    (hr : ManifoldRegularity r) (hs : d.source ⊆ c.source) (he : d.toFun = c.toFun)
    (u : E k) (hu : u ∈ d.source) : chartDifferential d u = chartDifferential c u := by
  apply (D04.EmbeddedChart.source_uniqueDiff d u hu).eq
    (D04.EmbeddedChart.hasDifferential d hr hu)
  rw [he]
  exact (D04.EmbeddedChart.hasDifferential c hr (hs hu)).mono hs

lemma common_ambient_coefficient {r : ℕ∞ω} {k n : ℕ} {M N : Set (E n)}
    (c : EmbeddedChart r k n M) (d : EmbeddedChart r k n N)
    (hr : ManifoldRegularity r) (hs : d.source ⊆ c.source) (he : d.toFun = c.toFun)
    (omega : FormField n k) (w : E n → ℝ) (u : d.source) :
    localizedTopCoefficient (GeometricPatches.ambientRestriction omega) d w u =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w ⟨u,hs u.property⟩ := by
  change w (d.toFun u) * omega (d.toFun u)
      (fun j => chartDifferential d u (standardBasis k j)) =
    w (c.toFun u) * omega (c.toFun u)
      (fun j => chartDifferential c u (standardBasis k j))
  rw [common_chart_differential c d hr hs he u u.property,he]

/-- Equality of full proper coefficients, including their zero extensions.
No Jordan truncation or integrability certificate is needed for this locality
identity; integrability on either side implies integrability on the other. -/
theorem common_chart_proper_integrals : common_chart_proper_integralsType := by
  intro r k n M N c d hr hs he omega w
  have hsub : d.source ⊆ c.source := hs ▸ Subset.rfl
  have hval := coefficient_restrict_core hsub
    (localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w)
    (by intro u _; rw [hs]; exact u.property)
  have hf : (fun u : d.source =>
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w ⟨u,hsub u.property⟩) =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) d w := by
    funext u
    exact (common_ambient_coefficient c d hr hsub he omega w u).symm
  rwa [hf] at hval

/-- A chart may be restricted and retargeted without changing the full proper
integral of an ambient form whose weighted coefficient vanishes on the removed
parameters. The support condition concerns the actual coefficient. -/
theorem restricted_chart_proper_integrals : restricted_chart_proper_integralsType := by
  intro r k n M N c d hr hs he omega w hsupport
  have hval := coefficient_restrict_core hs
    (localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w) hsupport
  have hf : (fun u : d.source =>
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w ⟨u,hs u.property⟩) =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) d w := by
    funext u
    exact (common_ambient_coefficient c d hr hs he omega w u).symm
  rwa [hf] at hval

/-- Locality of actual manifold integrals on two distinct carriers, when the
supports lie in identical local charts with compatible prescribed orientations.
The partitions used for the two manifold values are completely independent. -/
theorem common_single_chart_integral : common_single_chart_integralType := by
  intro r k n M N O o p hMO hNO omega ho w hw c d hs he s hsign hcompat
  dsimp only
  intro hMc hNc hMs hNs P Q
  let eta : TangentTopField r k M := fun x => w x • GeometricPatches.ambientRestriction omega x
  let xi : TangentTopField r k N := fun x => w x • GeometricPatches.ambientRestriction omega x
  have hη : ContinuousTopField eta := ManifoldIntegralIndependence.continuousTopField_weight
    w hw (ambient_restriction_continuous o.manifold.1 hMO omega ho)
  have hξ : ContinuousTopField xi := ManifoldIntegralIndependence.continuousTopField_weight
    w hw (ambient_restriction_continuous p.manifold.1 hNO omega ho)
  have hsub : d.source ⊆ c.source := hs ▸ Subset.rfl
  have hdsign (u : d.source) : chartSign p.atPoint d u u.property = s.val := by
    have ht : tangentSpace r k M (c.toFun u) = tangentSpace r k N (d.toFun u) := by
      rw [he]
      exact common_chart_tangentSpaces c d o.manifold.1 o.manifold.2.1 hs he u (hsub u.property)
    have hc := chart_sign_transport d c o.manifold.1
      (hs.symm ▸ Subset.rfl) he.symm p.atPoint o.atPoint u (hsub u.property) ht
      (hcompat u (hsub u.property) u.property ht)
    exact hc.trans (hsign ⟨u,hsub u.property⟩)
  have hM := ManifoldIntegralIndependence.oriented_single_chart o eta hη hMc P c hMs s hsign
  have hN := ManifoldIntegralIndependence.oriented_single_chart p xi hξ hNc Q d hNs s hdsign
  have hcoeffM : topCoefficient eta c =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) c w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ c u
  have hcoeffN : topCoefficient xi d =
      localizedTopCoefficient (GeometricPatches.ambientRestriction omega) d w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ d u
  rw [hcoeffM] at hM
  rw [hcoeffN] at hN
  refine ⟨hM.1,hN.1,?_⟩
  exact hM.2.trans ((congrArg (s.val * ·)
    (common_chart_proper_integrals c d o.manifold.1 hs he omega w).2).trans hN.2.symm)

/-- The common local chart cover needed for actual integral comparison can
be chosen simultaneously sign-constant, seam-free and isolated in both finite
decompositions. All of these properties are derived from the geometry. -/
theorem common_signed_chart_germs : common_signed_chart_germsType := by
  intro r k n ι κ _ _ A B Z W hZ hW hA hB o p hpA hpB hcover hcompat x hx hxZW
  obtain ⟨i,j,U,hxi,hxj,hU,hxU,heq,hUA⟩ :=
    common_piece_germ A B Z W hA hB hpA hpB hcover x hx hxZW
  have hUB : U ∩ (⋃ l, B l) = U ∩ B j := by rw [← hcover,hUA,heq]
  let T := U ∩ (Z ∪ W)ᶜ
  have hT : IsOpen T := hU.inter (hZ.union hW).isOpen_compl
  have hxT : x ∈ T := ⟨hxU,hxZW⟩
  have hTeq : T ∩ A i = T ∩ B j := by
    ext y
    have hy := Set.ext_iff.mp heq y
    simp only [mem_inter_iff,T] at hy ⊢
    tauto
  obtain ⟨a,s,hxa,hasign⟩ := ManifoldIntegral.constant_signed_chart_at (o i) ⟨x,hxi⟩
  let c := D04.EmbeddedChart.restrict a T hT
  obtain ⟨d,hds,hda,hdf,hdi,hdh⟩ := chart_retarget a T hT hTeq
  have hds' : d.source = c.source := hds
  have hdf' : d.toFun = c.toFun := hdf
  have hsub : c.source ⊆ a.source := inter_subset_left
  have hcT : c.ambient ⊆ T := inter_subset_right
  have hdisA (l : ι) (hli : l ≠ i) : Disjoint (A l) c.ambient := by
    apply Set.disjoint_left.mpr
    intro y hyl hyc
    have hyU := (hcT hyc).1
    have hyAi : y ∈ U ∩ A i := hUA ▸ (show y ∈ U ∩ (⋃ l, A l) from
      ⟨hyU,mem_iUnion.mpr ⟨l,hyl⟩⟩)
    have hyi : y ∈ A i := hyAi.2
    exact (hcT hyc).2 (Or.inl (hpA l i hli ⟨hyl,hyi⟩))
  have hdisB (l : κ) (hlj : l ≠ j) : Disjoint (B l) c.ambient := by
    apply Set.disjoint_left.mpr
    intro y hyl hyc
    have hyU := (hcT hyc).1
    have hyBj : y ∈ U ∩ B j := hUB ▸ (show y ∈ U ∩ (⋃ l, B l) from
      ⟨hyU,mem_iUnion.mpr ⟨l,hyl⟩⟩)
    have hyj : y ∈ B j := hyBj.2
    exact (hcT hyc).2 (Or.inr (hpB l j hlj ⟨hyl,hyj⟩))
  have hcsign (u : c.source) : chartSign (o i).atPoint c u u.property = s.val := by
    rw [Orientations.restriction_sign (o i).atPoint a c (o i).manifold.1
      hsub rfl u u.property]
    exact hasign ⟨u,hsub u.property⟩
  have hdsign (u : d.source) : chartSign (p j).atPoint d u u.property = s.val := by
    have huc : (u : E k) ∈ c.source := hds' ▸ u.property
    have ht : tangentSpace r k (A i) (c.toFun u) = tangentSpace r k (B j) (d.toFun u) := by
      rw [hdf']
      exact common_chart_tangentSpaces c d (o i).manifold.1 (o i).manifold.2.1
        hds' hdf' u huc
    have hco : (p j).atPoint (d.toFun u) (d.map_source u.property).1 =
        transportOrientation ht ((o i).atPoint (c.toFun u) (c.map_source huc).1) := by
      have htransport (y : E n) (hy : y ∈ B j) (he : y = c.toFun u)
          (g : tangentSpace r k (A i) (c.toFun u) = tangentSpace r k (B j) y) :
          (p j).atPoint y hy =
            transportOrientation g ((o i).atPoint (c.toFun u) (c.map_source huc).1) := by
        subst y
        exact (hcompat _ ((hcT (c.map_source huc).2).2) i j (c.map_source huc).1 hy g).symm
      exact htransport _ _ (congrFun hdf' u) ht
    exact (chart_sign_transport d c (o i).manifold.1 (hds'.symm ▸ Subset.rfl)
      hdf'.symm (p j).atPoint (o i).atPoint u huc ht hco).trans (hcsign ⟨u,huc⟩)
  exact ⟨i,j,c,d,s,hxi,hxj,⟨hxa,hxT⟩,hds',hdf',hdi,hda,hdh,
    fun y hy => (hcT hy).2,hdisA,hdisB,hcsign,hdsign⟩


lemma weighted_topSupport_subset {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (w : E n → ℝ) (eta : TangentTopField r k M) :
    topSupport (fun x : M => w x • eta x) ⊆ Subtype.val ⁻¹' tsupport w := by
  apply closure_minimal _ ((isClosed_tsupport w).preimage continuous_subtype_val)
  intro x hx
  exact subset_tsupport w (fun hz => hx (by change w x • eta x = 0; rw [hz,zero_smul]))

lemma topSupport_compact_of_compact {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsCompact M) (eta : TangentTopField r k M) : IsCompact (topSupport eta) := by
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  exact isClosed_closure.isCompact

lemma coefficient_integral_eq_zero {k : ℕ} {S : Set (E k)} (f : S → ℝ)
    (hf : ∀ x, f x = 0) : DirectedSubstitution.coefficientIntegral f = 0 := by
  let g : (∅ : Set (E k)) → ℝ := fun _ => 0
  have hz : zeroExtension f = zeroExtension g := by
    funext x
    rw [zeroExtension_of_not_mem g (notMem_empty x)]
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply f ⟨x,hx⟩,hf]
    · exact zeroExtension_of_not_mem f hx
  exact (DirectedSubstitution.proper_congr hz).2.trans (DirectedSubstitution.empty_integral g).2

lemma oriented_integral_eq_zero {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (eta : TangentTopField r k M)
    (hzero : ∀ x, eta x = 0) (P : SignedChartPartition o (topSupport eta)) :
    orientedIntegral eta P = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hz := coefficient_integral_eq_zero (localizedTopCoefficient eta (P.chart i) (P.weight i)) (by
    intro u
    change P.weight i ((P.chart i).toFun u) * eta (chartPoint (P.chart i) u) _ = 0
    rw [hzero]
    simp)
  change (P.sign i).val * DirectedSubstitution.coefficientIntegral
    (localizedTopCoefficient eta (P.chart i) (P.weight i)) = 0
  rw [hz,mul_zero]

/-- An ambient weight supported in an isolated common signed chart gives the
same actual sum over either compact family. Every other piece contributes zero.
This is local geometric additivity, with arbitrary chart partitions on the pieces. -/
theorem common_weighted_piece_integrals
    {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n))
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (i : ι) (j : κ) (c : EmbeddedChart r k n (A i)) (d : EmbeddedChart r k n (B j))
    (hs : d.source = c.source) (he : d.toFun = c.toFun) (s : PointSign)
    (hsc : ∀ u : c.source, chartSign (o i).atPoint c u u.property = s.val)
    (hsd : ∀ u : d.source, chartSign (p j).atPoint d u u.property = s.val)
    (hdisA : ∀ l, l ≠ i → Disjoint (A l) c.ambient)
    (hdisB : ∀ l, l ≠ j → Disjoint (B l) d.ambient)
    (w : E n → ℝ) (hw : Continuous w)
    (hwc : tsupport w ⊆ c.ambient) (hwd : tsupport w ⊆ d.ambient)
    (P : ∀ l, SignedChartPartition (o l)
      (topSupport (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x)))
    (Q : ∀ l, SignedChartPartition (p l)
      (topSupport (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x))) :
    (∑ l, orientedIntegral (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P l)) =
      ∑ l, orientedIntegral (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q l) := by
  have hzerosA (l : ι) (hli : l ≠ i) :
      orientedIntegral (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P l) = 0 := by
    apply oriented_integral_eq_zero
    intro x
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp (hdisA l hli) x.property (hwc h))
    rw [hz,zero_smul]
  have hzerosB (l : κ) (hlj : l ≠ j) :
      orientedIntegral (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q l) = 0 := by
    apply oriented_integral_eq_zero
    intro x
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp (hdisB l hlj) x.property (hwd h))
    rw [hz,zero_smul]
  have hη := ManifoldIntegralIndependence.continuousTopField_weight w hw
    (ambient_restriction_continuous (o i).manifold.1 (hAO i) omega ho)
  have hξ := ManifoldIntegralIndependence.continuousTopField_weight w hw
    (ambient_restriction_continuous (p j).manifold.1 (hBO j) omega ho)
  have hm := ManifoldIntegralIndependence.oriented_single_chart (o i) _ hη
    (topSupport_compact_of_compact (hA i) _) (P i) c
    (fun x hx => hwc (weighted_topSupport_subset w _ hx)) s hsc
  have hn := ManifoldIntegralIndependence.oriented_single_chart (p j) _ hξ
    (topSupport_compact_of_compact (hB j) _) (Q j) d
    (fun x hx => hwd (weighted_topSupport_subset w _ hx)) s hsd
  have hcoefM : topCoefficient
      (fun x : A i => w x • GeometricPatches.ambientRestriction (r := r) omega x) c =
      localizedTopCoefficient (GeometricPatches.ambientRestriction (r := r) omega) c w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ c u
  have hcoefN : topCoefficient
      (fun x : B j => w x • GeometricPatches.ambientRestriction (r := r) omega x) d =
      localizedTopCoefficient (GeometricPatches.ambientRestriction (r := r) omega) d w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ d u
  rw [hcoefM] at hm
  rw [hcoefN] at hn
  calc
    _ = orientedIntegral (fun x : A i => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P i) :=
      Finset.sum_eq_single i (fun l _ hli => hzerosA l hli) (by simp)
    _ = orientedIntegral (fun x : B j => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q j) :=
      hm.2.trans ((congrArg (s.val * ·)
        (common_chart_proper_integrals c d (o i).manifold.1 hs he omega w).2).trans hn.2.symm)
    _ = _ := (Finset.sum_eq_single j (fun l _ hlj => hzerosB l hlj) (by simp)).symm

lemma ambient_topSupport_subset {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (omega : FormField n k) :
    topSupport (GeometricPatches.ambientRestriction (r := r) (M := M) omega) ⊆
      Subtype.val ⁻¹' tsupport omega := by
  apply closure_minimal _ ((isClosed_tsupport omega).preimage continuous_subtype_val)
  intro x hx
  apply subset_tsupport omega
  intro hz
  apply hx
  ext v
  change omega x _ = 0
  rw [hz]
  rfl

/-- Off the two displayed seam carriers, geometric equality and compatible
orientations imply equality of the sums of the actual piece integrals. No
partition, chart, or integral correspondence is part of the hypotheses. -/
theorem manifold_decomposition_away_seams
    {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (Z W : Set (E n))
    (hZ : IsClosed Z) (hW : IsClosed W)
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    (hpA : ∀ i j, i ≠ j → A i ∩ A j ⊆ Z)
    (hpB : ∀ i j, i ≠ j → B i ∩ B j ⊆ W)
    (hcover : (⋃ i, A i) = ⋃ j, B j)
    (hcompat : ∀ x, x ∉ Z ∪ W → ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace r k (A i) x = tangentSpace r k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj)
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (V : Set (E n)) (hV : IsOpen V) (hZW : Z ∪ W ⊆ V)
    (hzero : EqOn omega (fun _ => 0) V)
    (P : ∀ i, SignedChartPartition (o i)
      (topSupport (GeometricPatches.ambientRestriction (r := r) omega)))
    (Q : ∀ j, SignedChartPartition (p j)
      (topSupport (GeometricPatches.ambientRestriction (r := r) omega))) :
    (∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := r) omega) (P i)) =
      ∑ j, orientedIntegral (GeometricPatches.ambientRestriction (r := r) omega) (Q j) := by
  let K := (⋃ i, A i) ∩ tsupport omega
  have hK : IsCompact K := (isCompact_iUnion hA).inter_right (isClosed_tsupport omega)
  have hsV : tsupport omega ⊆ Vᶜ :=
    closure_minimal (fun x hx hxV => hx (hzero hxV)) hV.isClosed_compl
  have hKZW (x : K) : (x : E n) ∉ Z ∪ W := fun hz => hsV x.property.2 (hZW hz)
  choose a b c d s hxa hxb hxc hds hdf hdi hda hdh hcZW hdisA hdisB hsc hsd using
    fun x : K => common_signed_chart_germs A B Z W hZ hW hA hB o p hpA hpB hcover hcompat
      x x.property.1 (hKZW x)
  obtain ⟨m,l,R,hR⟩ := GeometricPatches.ambient_partition_exists K hK
    (fun x : K => (c x).ambient) (fun x => (c x).ambient_open)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxc ⟨x,hx⟩⟩)
  let PA := fun (i : ι) (t : Fin m) => Classical.choice (ManifoldIntegral.signed_partition_exists (o i)
    (topSupport (fun x : A i => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x))
    (topSupport_compact_of_compact (hA i) _))
  let PB := fun (j : κ) (t : Fin m) => Classical.choice (ManifoldIntegral.signed_partition_exists (p j)
    (topSupport (fun x : B j => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x))
    (topSupport_compact_of_compact (hB j) _))
  have hlocal (t : Fin m) := common_weighted_piece_integrals A B hA hB o p hAO hBO omega ho
    (a (l t)) (b (l t)) (c (l t)) (d (l t)) (hds (l t)) (hdf (l t)) (s (l t))
    (hsc (l t)) (hsd (l t)) (hdisA (l t))
    (by simpa only [hda] using hdisB (l t))
    (R.weight t) (R.smooth t).continuous (hR t) (by rw [hda]; exact hR t)
    (fun i => PA i t) (fun j => PB j t)
  have hsumA (i : ι) := ManifoldIntegralIndependence.oriented_finite_localization (o i)
    (GeometricPatches.ambientRestriction (r := r) omega)
    (ambient_restriction_continuous (o i).manifold.1 (hAO i) omega ho) R.weight
    (fun t => (R.smooth t).continuous) (fun x hx => by
      have hxK : (x : E n) ∈ K := ⟨mem_iUnion.mpr ⟨i,x.property⟩,
        ambient_topSupport_subset omega (subset_closure hx)⟩
      obtain ⟨D,hD,hKD,hone⟩ := R.sum_one
      exact hone x (hKD hxK)) (P i) (PA i)
  have hsumB (j : κ) := ManifoldIntegralIndependence.oriented_finite_localization (p j)
    (GeometricPatches.ambientRestriction (r := r) omega)
    (ambient_restriction_continuous (p j).manifold.1 (hBO j) omega ho) R.weight
    (fun t => (R.smooth t).continuous) (fun x hx => by
      have hxU : (x : E n) ∈ ⋃ i, A i := hcover.symm ▸ mem_iUnion.mpr ⟨j,x.property⟩
      have hxK : (x : E n) ∈ K := ⟨hxU,
        ambient_topSupport_subset omega (subset_closure hx)⟩
      obtain ⟨D,hD,hKD,hone⟩ := R.sum_one
      exact hone x (hKD hxK)) (Q j) (PB j)
  calc
    _ = ∑ i, ∑ t, orientedIntegral
        (fun x : A i => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x) (PA i t) :=
      Finset.sum_congr rfl (fun i _ => hsumA i)
    _ = ∑ t, ∑ i, orientedIntegral
        (fun x : A i => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x) (PA i t) :=
      Finset.sum_comm
    _ = ∑ t, ∑ j, orientedIntegral
        (fun x : B j => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x) (PB j t) :=
      Finset.sum_congr rfl (fun t _ => hlocal t)
    _ = ∑ j, ∑ t, orientedIntegral
        (fun x : B j => R.weight t x • GeometricPatches.ambientRestriction (r := r) omega x) (PB j t) :=
      Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (hsumB j).symm)


lemma oriented_integral_cast {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} {eta xi : TangentTopField r k M}
    (he : eta = xi) (P : SignedChartPartition o (topSupport eta)) :
    orientedIntegral eta P = orientedIntegral xi (he ▸ P) := by
  cases he
  rfl

lemma ambientRestriction_weight {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (w : E n → ℝ) (omega : FormField n k) :
    GeometricPatches.ambientRestriction (r := r) (M := M) (fun y => w y • omega y) =
      fun x : M => w x • GeometricPatches.ambientRestriction (r := r) omega x := by
  funext x
  ext v
  rfl

lemma continuous_ambientForm_weight {k n : ℕ} {O : Set (E n)}
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (w : E n → ℝ) (hw : Continuous w) :
    IsCrForm (some 0) O (fun y => w y • omega y) := by
  refine ⟨ho.1,fun I => ?_⟩
  change ContinuousOn (fun x => w x *
    Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient (standardBasis n) (omega x) I) O
  exact hw.continuousOn.mul (ho.2 I)

/-- Decomposition independence for finite unions of distinct compact C¹
manifolds with lower-dimensional geometric overlaps. The union may have corners.
All prescribed orientations and actual upstream integral values are retained,
and every signed chart partition on every piece is permitted. -/
theorem manifold_decomposition_independent
    {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n)) (s t : AmbientSeams k n)
    (hA : ∀ i, IsCompact (A i)) (hB : ∀ j, IsCompact (B j))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i))
    (p : ∀ j, PositiveManifoldOrientation 1 k (B j))
    (hpA : ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier)
    (hpB : ∀ i j, i ≠ j → B i ∩ B j ⊆ t.carrier)
    (hcover : (⋃ i, A i) = ⋃ j, B j)
    (hcompat : ∀ x, x ∉ s.carrier ∪ t.carrier →
      ∀ i j (hi : x ∈ A i) (hj : x ∈ B j),
      ∀ h : tangentSpace 1 k (A i) x = tangentSpace 1 k (B j) x,
        transportOrientation h ((o i).atPoint x hi) = (p j).atPoint x hj)
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (P : ∀ i, SignedChartPartition (o i)
      (topSupport (GeometricPatches.ambientRestriction (r := 1) omega)))
    (Q : ∀ j, SignedChartPartition (p j)
      (topSupport (GeometricPatches.ambientRestriction (r := 1) omega))) :
    (∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) (P i)) =
      ∑ j, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) (Q j) := by
  let z := appendSeams s t
  obtain ⟨chi,hchi,hvals,hzero,hone⟩ := smooth_seam_cutoff_sequence z.carrier (ambient_seams_compact z)
  let PA := fun (i : ι) (m : ℕ) => Classical.choice (ManifoldIntegral.signed_partition_exists (o i)
    (topSupport (fun x : A i => chi m x • GeometricPatches.ambientRestriction (r := 1) omega x))
    (topSupport_compact_of_compact (hA i) _))
  let PB := fun (j : κ) (m : ℕ) => Classical.choice (ManifoldIntegral.signed_partition_exists (p j)
    (topSupport (fun x : B j => chi m x • GeometricPatches.ambientRestriction (r := 1) omega x))
    (topSupport_compact_of_compact (hB j) _))
  have hlimA (i : ι) := manifold_seam_cutoff_limit (o i) z
    (GeometricPatches.ambientRestriction (r := 1) omega)
    (ambient_restriction_continuous (o i).manifold.1 (hAO i) omega ho)
    chi hchi hvals hone (P i) (PA i)
  have hlimB (j : κ) := manifold_seam_cutoff_limit (p j) z
    (GeometricPatches.ambientRestriction (r := 1) omega)
    (ambient_restriction_continuous (p j).manifold.1 (hBO j) omega ho)
    chi hchi hvals hone (Q j) (PB j)
  have hlocal (m : ℕ) :
      (∑ i, orientedIntegral (fun x : A i => chi m x •
        GeometricPatches.ambientRestriction (r := 1) omega x) (PA i m)) =
      ∑ j, orientedIntegral (fun x : B j => chi m x •
        GeometricPatches.ambientRestriction (r := 1) omega x) (PB j m) := by
    obtain ⟨V,hV,hzV,hzeroV⟩ := hzero m
    have hzwV : s.carrier ∪ t.carrier ⊆ V := by
      rw [← append_seams_carrier s t]
      exact hzV
    have heA (i : ι) := ambientRestriction_weight (r := 1) (M := A i) (chi m) omega
    have heB (j : κ) := ambientRestriction_weight (r := 1) (M := B j) (chi m) omega
    let RA : ∀ i, SignedChartPartition (o i) (topSupport
        (GeometricPatches.ambientRestriction (r := 1) (fun y => chi m y • omega y))) :=
      fun i => (heA i).symm ▸ PA i m
    let RB : ∀ j, SignedChartPartition (p j) (topSupport
        (GeometricPatches.ambientRestriction (r := 1) (fun y => chi m y • omega y))) :=
      fun j => (heB j).symm ▸ PB j m
    have h := manifold_decomposition_away_seams A B s.carrier t.carrier
      (ambient_seams_compact s).isClosed (ambient_seams_compact t).isClosed hA hB o p
      hpA hpB hcover hcompat hAO hBO (fun y => chi m y • omega y)
      (continuous_ambientForm_weight omega ho _ (hchi m).continuous)
      V hV hzwV (fun y hy => by change chi m y • omega y = 0; rw [hzeroV hy,zero_smul]) RA RB
    calc
      _ = ∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1)
          (fun y => chi m y • omega y)) (RA i) :=
        Finset.sum_congr rfl (fun i _ => oriented_integral_cast (heA i).symm (PA i m))
      _ = _ := h
      _ = _ := Finset.sum_congr rfl
        (fun j _ => (oriented_integral_cast (heB j).symm (PB j m)).symm)
  have hAconv := tendsto_finsetSum Finset.univ (fun i _ => hlimA i)
  have hBconv := tendsto_finsetSum Finset.univ (fun j _ => hlimB j)
  simp only [hlocal] at hAconv
  exact tendsto_nhds_unique hAconv hBconv


abbrev CompactManifoldDecomposition := Model.CompactManifoldDecomposition
abbrev decompositionCarrier := @Model.CompactManifoldDecomposition.carrier
abbrev CompatibleDecompositions := @Model.CompatibleDecompositions
abbrev HasCompactUnionIntegral := @Model.HasCompactUnionIntegral
abbrev compactUnionIntegral := @Model.compactUnionIntegral

lemma compatible_decompositions_refl {k n : ℕ} (D : CompactManifoldDecomposition k n) :
    CompatibleDecompositions D D := by
  refine ⟨rfl,?_⟩
  intro x hx i j hi hj h
  have hij : i = j := by
    by_contra hn
    exact hx (Or.inl (D.overlap i j hn ⟨hi,hj⟩))
  subst j
  simp [transportOrientation,Model.transportOrientation,LinearEquiv.ofEq_rfl,Orientation.map_refl]

/-- No integral certificate occurs in the geometric decomposition record.
This proof constructs the value and verifies its characterization for all
compatible displays using the actual cross-carrier comparison theorem. -/
theorem compact_union_integral_exists : compact_union_integral_existsType := by
  intro k n D O hDO omega ho
  let P := fun i => Classical.choice (ManifoldIntegral.signed_partition_exists (D.orientation i)
    (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := D.piece i) omega))
    (topSupport_compact_of_compact (D.compact i) _))
  let v := ∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) (P i)
  have hv : HasCompactUnionIntegral D omega v := by
    intro F hF Q
    exact (manifold_decomposition_independent D.piece F.piece D.seams F.seams
      D.compact F.compact D.orientation F.orientation D.overlap F.overlap hF.1 hF.2
      (fun i x hx => hDO (mem_iUnion.mpr ⟨i,hx⟩))
      (fun j x hx => hDO (hF.1.symm ▸ mem_iUnion.mpr ⟨j,hx⟩)) omega ho P Q).symm
  refine ⟨v,hv,?_⟩
  intro w hw
  exact (hw D (compatible_decompositions_refl D) P).symm

/-- Every geometric display and every partition recovers this value. -/
theorem compact_union_integral_eq_sum : compact_union_integral_eq_sumType := by
  intro k n D F hF O hDO omega ho Q
  have hex : ∃ v, HasCompactUnionIntegral D omega v :=
    (compact_union_integral_exists D hDO omega ho).exists
  have hv := Classical.choose_spec hex
  change (if h : ∃ v, Model.HasCompactUnionIntegral D omega v then Classical.choose h else 0) = _
  rw [dite_eq_left hex]
  exact (hv F hF Q).symm

/-- Choice of a geometric decomposition does not change the constructed usual
integral. Both sides have their own independent choices of all chart data. -/
theorem compact_union_integral_independent : compact_union_integral_independentType := by
  intro k n D F hF O hDO omega ho
  let Q := fun j => Classical.choice (ManifoldIntegral.signed_partition_exists (F.orientation j)
    (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := F.piece j) omega))
    (topSupport_compact_of_compact (F.compact j) _))
  have hFO : F.carrier ⊆ O := hF.1 ▸ hDO
  exact (compact_union_integral_eq_sum D F hF hDO omega ho Q).trans
    (compact_union_integral_eq_sum F F (compatible_decompositions_refl F) hFO omega ho Q).symm


abbrev singleManifoldDecomposition := @Model.singleManifoldDecomposition

lemma single_decomposition_carrier {k n : ℕ} {M : Set (E n)}
    (hM : IsCompact M) (o : PositiveManifoldOrientation 1 k M) :
    (singleManifoldDecomposition hM o).carrier = M := by
  ext x
  simp [Model.CompactManifoldDecomposition.carrier,singleManifoldDecomposition,
    Model.singleManifoldDecomposition]

/-- The geometric value preserves the upstream usual integral on smooth pieces. -/
theorem compact_union_integral_single : compact_union_integral_singleType := by
  intro k n M O hM o hMO omega ho P
  let D := singleManifoldDecomposition hM o
  have hDO : D.carrier ⊆ O := by rw [single_decomposition_carrier]; exact hMO
  have h := compact_union_integral_eq_sum D D (compatible_decompositions_refl D) hDO omega ho
    (fun _ => P)
  change compactUnionIntegral D omega =
    ∑ _ : Fin 1, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) P at h
  simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using h

/-- The union value also equals every allowed display by actual parameter
patches. Each term keeps its prescribed chart sign and ambient weight. -/
theorem compact_union_integral_patch_expansion : compact_union_integral_patch_expansionType := by
  intro k n D O hDO omega ho P C
  rw [compact_union_integral_eq_sum D D (compatible_decompositions_refl D) hDO omega ho P]
  exact Finset.sum_congr rfl (fun i _ => manifold_patch_value (D.orientation i) omega ho (P i) (C i))

/-- Compact injectivity supplies inverse continuity before the rank condition
is used. In particular no chart at a cube corner is asserted. -/
theorem compact_parameter_chart : compact_parameter_chartType := by
  intro r k n S V f hS hV hVS hf hinj hreg
  let F : S → E n := fun x => f x
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hF : Continuous F := continuousOn_iff_continuous_domRestrict.mp hf
  have hEmb : Topology.IsClosedEmbedding F := hF.isClosedEmbedding (by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy))
  have hInv : ContinuousOn (Function.invFunOn f S) (f '' S) := by
    have him : F '' (Set.univ : Set S) = f '' S := by
      ext y
      simp only [mem_image, mem_univ, true_and, F]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [← him, hEmb.isEmbedding.isInducing.continuousOn_image_iff]
    have he : Function.invFunOn f S ∘ F = (Subtype.val : S → E k) := by
      funext x
      exact hinj.leftInvOn_invFunOn x.property
    rw [he]
    exact continuous_subtype_val.continuousOn
  have hrem : IsCompact (f '' (S \ V)) :=
    (hS.diff hV).image_of_continuousOn (hf.mono sdiff_subset)
  have hdis : f '' V ⊆ (f '' (S \ V))ᶜ := by
    rintro y ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
    exact hz.2 (hinj hz.1 (hVS hx) he ▸ hx)
  let c : EmbeddedChart r k n (f '' V) :=
    { half := false
      half_pos := by simp
      source := V
      source_open := ⟨V,hV,by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
      ambient := (f '' (S \ V))ᶜ
      ambient_open := hrem.isClosed.isOpen_compl
      toFun := f
      invFun := Function.invFunOn f S
      map_source := fun x hx => ⟨mem_image_of_mem f hx,hdis (mem_image_of_mem f hx)⟩
      map_target := by
        rintro y ⟨⟨x,hx,rfl⟩,_⟩
        rw [hinj.leftInvOn_invFunOn (hVS hx)]
        exact hx
      left_inv := fun x hx => hinj.leftInvOn_invFunOn (hVS hx)
      right_inv := by
        rintro y ⟨⟨x,hx,rfl⟩,_⟩
        rw [hinj.leftInvOn_invFunOn (hVS hx)]
      continuous_toFun := hf.mono hVS
      continuous_invFun := hInv.mono (fun y hy => image_mono hVS hy.1)
      regular := hreg }
  exact ⟨c,rfl,rfl,rfl,rfl,rfl,hdis⟩

open Specs.D04.C15.CellsChainsAndIntegrals.Model

theorem cell_interior_chart : cell_interior_chartType := by
  intro r k n O a hkn hinj hrank
  dsimp only
  have hS : IsCompact (cube k) := DiscontinuityCriterion.carrier_compact (cubeBox k)
  have hf : ContDiffOn ℝ 1 (cellExtension a) (extensionDomain a) := Cells.extension_C1 a
  have hreg : FullRankLocalExtension 1 (interior (cube k)) (cellExtension a) := by
    apply (D04.open_fullRankLocalExtension_iff _ _ isOpen_interior).mpr
    exact ⟨hf.mono (interior_subset.trans (extension_spec a).2.1),hrank⟩
  obtain ⟨c,hhalf,hsource,hmap,hinv,hambient,himage⟩ := compact_parameter_chart
    (cube k) (interior (cube k)) (cellExtension a) hS isOpen_interior interior_subset
    (hf.continuousOn.mono (extension_spec a).2.1) hinj hreg
  have hamb : c.ambient = (cellExtension a '' frontier (cube k))ᶜ := by
    rw [hambient, frontier, hS.isClosed.closure_eq]
  refine ⟨c,hhalf,hsource,hmap,hinv,hamb,⟨⟨le_rfl,by simp⟩,hkn,?_⟩⟩
  rintro y ⟨x,hx,rfl⟩
  refine ⟨c,x,⟨hsource.symm ▸ hx,?_⟩,congrFun hmap x⟩
  simp [hhalf]

theorem cell_faces_seams : cell_faces_seamsType := by
  intro r k n O a
  let e : Fin ((k+1)*2) ≃ Fin (k+1) × Bool :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)
  let b : Fin ((k+1)*2) → Cell r k O := fun j => cellFace a (e j).1 (e j).2
  let p : Fin ((k+1)*2) → Model.CompactSeam (k+1) n := fun j =>
    { dim := k
      lower := Nat.lt_succ_self k
      parameter := cube k
      compact := DiscontinuityCriterion.carrier_compact (cubeBox k)
      map := cellExtension (b j)
      localC1 := by
        intro x hx
        refine ⟨extensionDomain (b j),cellExtension (b j),
          (extension_spec (b j)).1.mem_nhds ((extension_spec (b j)).2.1 hx),?_,
          fun _ _ => rfl⟩
        exact (Cells.extension_C1 (b j)).contDiffAt
          ((extension_spec (b j)).1.mem_nhds ((extension_spec (b j)).2.1 hx)) }
  let s : AmbientSeams (k+1) n :=
    { carrier := ⋃ j, (p j).map '' (p j).parameter
      isCompact := isCompact_iUnion (fun j =>
        (p j).compact.image_of_continuousOn (seam_map_continuous (p j)))
      cover := ⟨Set.range p,Set.countable_range p,by
        intro y hy
        obtain ⟨j,hj⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨⟨p j,mem_range_self j⟩,hj⟩⟩ }
  refine ⟨s,?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨(e j).1,mem_iUnion.mpr ⟨(e j).2,hj⟩⟩
  · intro hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    obtain ⟨ε,hε⟩ := mem_iUnion.mp hi
    refine mem_iUnion.mpr ⟨e.symm (i,ε),?_⟩
    change y ∈ cellExtension (cellFace a (e (e.symm (i,ε))).1
      (e (e.symm (i,ε))).2) '' cube k
    simpa only [e.apply_symm_apply] using hε

/-- A local graph inverse becomes the inverse of the compact parametrization
on an ambient neighborhood by removing the compact image of all other branches. -/
theorem compact_parameter_inverse_extensions : compact_parameter_inverse_extensionsType := by
  intro k n S f hkn hS hf hinj hreg x hx
  obtain ⟨W₀,g₀,hW₀,hxW₀,he₀,hg₀,hrank₀⟩ := hreg x hx
  have hr : ManifoldRegularity (1 : ℕ∞ω) := ⟨le_rfl,by simp⟩
  have hgext : FullRankLocalExtension 1 W₀ g₀ :=
    (D04.open_fullRankLocalExtension_iff W₀ g₀ hW₀).mpr ⟨hg₀,hrank₀⟩
  obtain ⟨a,W,g,X,Y,q,H⟩ := D04.local_graph_and_ambient_inverse W₀ g₀ x false hr hkn
    (by simp) ⟨W₀,hW₀,by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
    hgext hxW₀
  let P := Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection a
  let T := W₀ ∩ X
  have hT : IsOpen T := hW₀.inter H.inverse.1
  have hxT : x ∈ T := ⟨hxW₀,H.inverse.2.2.1⟩
  have hPgx : P (f x) ∈ Y := by
    have hegx : g x = f x := (H.extension_agrees ⟨hxW₀,H.extension_center⟩).trans (he₀ ⟨hx,hxW₀⟩)
    simpa only [Function.comp_apply,hegx] using H.inverse.2.2.2.1
  let U := (P ⁻¹' Y) \ (f '' (S \ T))
  have hU : IsOpen U := (H.inverse.2.1.preimage P.continuous).sdiff
    ((hS.diff hT).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hfxU : f x ∈ U := by
    refine ⟨hPgx,?_⟩
    rintro ⟨z,hz,hez⟩
    exact hz.2 (hinj hz.1 hx hez ▸ hxT)
  refine ⟨U,q ∘ P,hU,hfxU,H.inverse_ambient_regular.mono sdiff_subset,?_⟩
  rintro y ⟨⟨z,hz,rfl⟩,hy⟩
  have hzT : z ∈ T := by
    by_contra hn
    exact hy.2 ⟨z,⟨hz,hn⟩,rfl⟩
  rw [hinj.leftInvOn_invFunOn hz,← he₀ ⟨hz,hzT.1⟩]
  exact H.inverse_left hzT

theorem compact_parameter_seams_contentZero : compact_parameter_seams_contentZeroType := by
  intro k n S f hkn hS hf hinj hreg s
  have hImage : IsCompact (f '' S) := hS.image_of_continuousOn hf
  obtain ⟨P,hP,hcover⟩ := s.cover
  letI := hP.to_subtype
  have hpieces (p : P) :
      IsCompact (Function.invFunOn f S '' ((p.val.map '' p.val.parameter) ∩ (f '' S))) ∧
      NullCovers.ContentZero (Function.invFunOn f S '' ((p.val.map '' p.val.parameter) ∩ (f '' S))) := by
    rw [← restricted_seam_image p.val (f '' S), image_image]
    apply LowerDimensionalImages.compact_local_C1_image p.val.lower
      (p.val.parameter ∩ p.val.map ⁻¹' (f '' S)) (Function.invFunOn f S ∘ p.val.map)
      (restrict_seam_parameter_compact p.val hImage)
    intro z hz
    obtain ⟨t,ht,het⟩ := hz.2
    obtain ⟨U,J,hU,hcenter,hJ,heJ⟩ :=
      compact_parameter_inverse_extensions S f hkn hS hf hinj hreg t ht
    have hzU : p.val.map z ∈ U := het ▸ hcenter
    obtain ⟨V,g,hV,hg,heg⟩ := p.val.localC1 z hz.1
    have hgz : g z = p.val.map z := heg ⟨hz.1,mem_of_mem_nhds hV⟩
    have hgzU : g z ∈ U := hgz.symm ▸ hzU
    refine ⟨V ∩ g ⁻¹' U,J ∘ g,
      inter_mem hV (hg.continuousAt.preimage_mem_nhds (hU.mem_nhds hgzU)),
      (hJ.contDiffAt (hU.mem_nhds hgzU)).comp z hg,?_⟩
    intro y hy
    change J (g y) = Function.invFunOn f S (p.val.map y)
    rw [heg ⟨hy.1.1,hy.2.1⟩]
    apply heJ
    refine ⟨hy.1.2,?_⟩
    rw [← heg ⟨hy.1.1,hy.2.1⟩]
    exact hy.2.2
  have hc : IsCompact (S ∩ f ⁻¹' s.carrier) :=
    hS.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hS.isClosed s.isCompact.isClosed)
      inter_subset_left
  refine ⟨hc,NullCovers.compact_null_contentZero _ hc ?_⟩
  apply NullCovers.null_mono (T := ⋃ p : P,
    Function.invFunOn f S '' ((p.val.map '' p.val.parameter) ∩ (f '' S))) ?_
    (NullCovers.null_iUnion_countable _ (fun p => NullCovers.contentZero_null (hpieces p).2))
  intro x hx
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hcover hx.2)
  exact mem_iUnion.mpr ⟨p,⟨f x,⟨hp,mem_image_of_mem f hx.1⟩,
    hinj.leftInvOn_invFunOn hx.1⟩⟩

/-- Openness of the injective locus for continuous linear maps supplies full
rank on separate Euclidean neighborhoods of all compact parameters. -/
lemma fullRankLocalExtension_of_C1 {k n : ℕ} {S U : Set (E k)} {f : E k → E n}
    (hU : IsOpen U) (hSU : S ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hrank : ∀ x ∈ S, Function.Injective (fderiv ℝ f x)) :
    FullRankLocalExtension 1 S f := by
  intro x hx
  have hD : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl x (hSU hx)).continuousAt (hU.mem_nhds (hSU hx))
  have hN : (fderiv ℝ f) ⁻¹' {L : E k →L[ℝ] E n | Function.Injective L} ∈ 𝓝 x :=
    hD.preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds (hrank x hx))
  obtain ⟨V,hVN,hV,hxV⟩ := mem_nhds_iff.mp hN
  exact ⟨U ∩ V,f,hU.inter hV,⟨hSU hx,hxV⟩,fun _ _ => rfl,
    hf.mono inter_subset_left,fun y hy => hVN hy.2⟩

theorem compact_parameter_cutoff_limit : compact_parameter_cutoff_limitType := by
  intro k n S f hkn hS hSJ hf hinj hreg s b hb χ hχ hχv hχone
  let Z := S ∩ f ⁻¹' s.carrier
  have hz := compact_parameter_seams_contentZero S f hkn hS hf hinj hreg s
  have hbi : RegionIntegrable (fun x : S => b x) :=
    GeometricPatches.continuous_integrable hSJ (by simpa [hS.isClosed.closure_eq] using hb)
  have hgi (m : ℕ) : RegionIntegrable (fun x : S => χ m (f x) * b x) :=
    GeometricPatches.continuous_integrable hSJ (by
      rw [hS.isClosed.closure_eq]
      exact ((hχ m).continuous.continuousOn.comp hf (fun _ _ => mem_univ _)).mul hb)
  refine ⟨hgi,?_⟩
  obtain ⟨B,hB,hbB⟩ := (hS.image_of_continuousOn hb).isBounded.exists_pos_norm_le
  apply region_seam_limit hSJ Z hz.1 hz.2 _ _ hbi hgi B hB.le
  · intro m x
    obtain ⟨hl,hu⟩ := hχv m (f x)
    have he : χ m (f x) * b x - b x = (χ m (f x) - 1) * b x := by ring
    rw [he,abs_mul]
    have hv : |χ m (f x) - 1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    exact (mul_le_of_le_one_left (abs_nonneg _) hv).trans (by
      simpa only [Real.norm_eq_abs] using hbB (b x) (mem_image_of_mem b x.property))
  · intro U hU hZU δ hδ
    let A := f '' (S \ U)
    have hA : IsCompact A := (hS.diff hU).image_of_continuousOn (hf.mono sdiff_subset)
    have hdis : Disjoint A s.carrier := Set.disjoint_left.mpr (by
      rintro y ⟨x,⟨hx,hxU⟩,rfl⟩ hy
      exact hxU (hZU ⟨hx,hy⟩))
    filter_upwards [hχone A hA hdis] with m hm x hxU
    simpa [hm (show f x ∈ A from ⟨x,⟨x.property,hxU⟩,rfl⟩)] using hδ.le

theorem cell_seams_contentZero : cell_seams_contentZeroType := by
  intro r k n O a hkn hinj hrank s
  exact compact_parameter_seams_contentZero (cube k) (cellExtension a) hkn
    (DiscontinuityCriterion.carrier_compact (cubeBox k))
    ((Cells.extension_C1 a).continuousOn.mono (extension_spec a).2.1) hinj
    (fullRankLocalExtension_of_C1 (extension_spec a).1 (extension_spec a).2.1
      (Cells.extension_C1 a) hrank) s

theorem cell_seam_cutoff_limit : cell_seam_cutoff_limitType := by
  intro r k n O a hkn hinj hrank s omega ho χ hχ hχv hχone
  have h := compact_parameter_cutoff_limit (cube k) (cellExtension a) hkn
    (DiscontinuityCriterion.carrier_compact (cubeBox k))
    (OneCoordinate.Boxes.jordan_carrier (cubeBox k))
    ((Cells.extension_C1 a).continuousOn.mono (extension_spec a).2.1) hinj
    (fullRankLocalExtension_of_C1 (extension_spec a).1 (extension_spec a).2.1
      (Cells.extension_C1 a) hrank) s (cellCoefficient a omega)
    (Cells.cellCoefficient_continuous a omega ho) χ hχ hχv hχone
  have hv : regionIntegral (fun x : cube k => cellCoefficient a omega x) = cellIntegral a omega :=
    GeometricPatches.box_region_integral (cubeBox k) (fun _ => zero_lt_one)
      (cellCoefficient a omega) (Cells.cellCoefficient_continuous a omega ho)
  exact ⟨h.1,hv ▸ h.2⟩

lemma sign_locally_constant_of_nonzero {α : Type*} [TopologicalSpace α]
    (f : α → ℝ) (hf : Continuous f) (hn : ∀ x, f x ≠ 0) :
    IsLocallyConstant (fun x => Real.sign (f x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  rcases lt_or_gt_of_ne (hn x) with hx | hx
  · refine ⟨{y | f y < 0},isOpen_lt hf continuous_const,hx,?_⟩
    intro y hy
    rw [Real.sign_of_neg hy,Real.sign_of_neg hx]
  · refine ⟨{y | 0 < f y},isOpen_lt continuous_const hf,hx,?_⟩
    intro y hy
    rw [Real.sign_of_pos hy,Real.sign_of_pos hx]

theorem global_chart_orientation : global_chart_orientationType := by
  intro r k n M c hr hk hkn hhalf hMambient
  let basis (x : E n) (hx : x ∈ M) : Module.Basis (Fin k) ℝ (tangentSpace r k M x) :=
    (D04.Orientations.chartBasis c hr hkn (c.invFun x) (c.map_target ⟨hx,hMambient hx⟩)).map
      (LinearEquiv.ofEq _ _ (congrArg (tangentSpace r k M) (c.right_inv x ⟨hx,hMambient hx⟩)))
  let F : TangentOrientationField r k M := fun x hx => (basis x hx).orientation
  have hsign : ∀ u (hu : u ∈ c.source), chartSign F c u hu = 1 := by
    intro u hu
    apply (D04.Orientations.chartSign_basis F c u hu (basis _ (c.map_source hu).1) ?_).mpr rfl
    intro i
    change chartDifferential c (c.invFun (c.toFun u)) (standardBasis k i) =
      chartDifferential c u (standardBasis k i)
    rw [c.left_inv u hu]
  have hMan : IsEmbeddedManifold r k M := by
    refine ⟨hr,hkn,?_⟩
    intro x hx
    refine ⟨c,c.invFun x,⟨c.map_target ⟨hx,hMambient hx⟩,?_⟩,c.right_inv x ⟨hx,hMambient hx⟩⟩
    simp [hhalf]
  refine ⟨⟨hk,hMan,F,?_⟩,hsign⟩
  intro d
  have hOverlap : chartOverlap d c = d.source := by
    ext u
    exact ⟨fun h => h.1,fun hu => ⟨hu,hMambient (d.map_source hu).1⟩⟩
  let D : d.source → ℝ := fun u =>
    (fderivWithin ℝ (chartTransition d c) (chartOverlap d c) u).det
  have hDc : Continuous D := by
    have h := ContinuousLinearMap.continuous_det.comp_continuousOn
      ((D04.chart_transition_regular d c hr hkn).1.continuousOn_fderivWithin
        (D04.EmbeddedChart.overlap_uniqueDiff d c) hr.1)
    exact (h.mono hOverlap.symm.subset).domRestrict
  have hDn (u : d.source) : D u ≠ 0 := by
    have hu : (u : E k) ∈ chartOverlap d c := hOverlap.symm ▸ u.property
    obtain ⟨A,hA,_⟩ := D04.chart_transition_derivatives d c hr hkn u hu
    have he := hA.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff d c u hu)
    change (fderivWithin ℝ (chartTransition d c) (chartOverlap d c) u).det ≠ 0
    rw [he]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have he (u : d.source) : chartSign F d u u.property = Real.sign (D u) := by
    have hu : (u : E k) ∈ chartOverlap d c := hOverlap.symm ▸ u.property
    have hv := (D04.EmbeddedChart.transition_mem d c hu).1
    rw [D04.Orientations.chartSign_transition F d c hr hkn u hu hv,hsign _ hv,one_mul]
  have heq : (fun u : d.source => chartSign F d u u.property) = fun u => Real.sign (D u) :=
    funext he
  rw [heq]
  exact sign_locally_constant_of_nonzero D hDc hDn

theorem cell_interior_orientation : cell_interior_orientationType := by
  intro r k n O a hk hkn hinj hrank
  dsimp only
  obtain ⟨c,hhalf,hsource,hmap,hinv,hambient,hMan⟩ := cell_interior_chart a hkn hinj hrank
  have hMambient : cellExtension a '' interior (cube k) ⊆ c.ambient := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [hmap] using (c.map_source (hsource.symm ▸ hx)).2
  obtain ⟨o,hsign⟩ := global_chart_orientation c hMan.1 hk hkn hhalf hMambient
  exact ⟨c,o,hhalf,hsource,hmap,hinv,hambient,hsign⟩

lemma cube_frontier_faces (k : ℕ) :
    frontier (cube (k+1)) = ⋃ i : Fin (k+1), ⋃ ε : Bool,
      faceInsertion i ε '' cube k := by
  have hclosed : IsClosed (cube (k+1)) := NullCovers.isClosed_carrier (cubeBox (k+1))
  have hi : interior (cube (k+1)) = {x : E (k+1) | ∀ j, 0 < x j ∧ x j < 1} :=
    interior_carrier (cubeBox (k+1))
  ext x
  constructor
  · intro hx
    have hxS : x ∈ cube (k+1) := hclosed.closure_subset hx.1
    have hex : ∃ i, x i = 0 ∨ x i = 1 := by
      by_contra hn
      apply hx.2
      rw [hi]
      intro i
      have h0 : x i ≠ 0 := fun h => hn ⟨i,Or.inl h⟩
      have h1 : x i ≠ 1 := fun h => hn ⟨i,Or.inr h⟩
      exact ⟨lt_of_le_of_ne (hxS i).1 h0.symm,lt_of_le_of_ne (hxS i).2 h1⟩
    obtain ⟨i,hiend⟩ := hex
    let u : E k := WithLp.toLp 2 (fun j => x (i.succAbove j))
    have hu : u ∈ cube k := fun j => hxS (i.succAbove j)
    have hrepr (ε : Bool) (he : x i = if ε then 1 else 0) : faceInsertion i ε u = x := by
      apply PiLp.ext
      intro j
      refine Fin.succAboveCases i ?_ (fun l => ?_) j
      · simpa only [Cells.faceInsertion_same] using he.symm
      · exact Cells.faceInsertion_other i ε u l
    rcases hiend with h0 | h1
    · exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨false,u,hu,hrepr false h0⟩⟩
    · exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨true,u,hu,hrepr true h1⟩⟩
  · intro hx
    obtain ⟨i,hi'⟩ := mem_iUnion.mp hx
    obtain ⟨ε,u,hu,rfl⟩ := mem_iUnion.mp hi' 
    refine ⟨subset_closure (faceInsertion_mem i ε hu),?_⟩
    rw [hi]
    intro hI
    have h := hI i
    rw [Cells.faceInsertion_same] at h
    cases ε <;> norm_num at h

theorem cell_frontier_seams : cell_frontier_seamsType := by
  intro r k n O a
  obtain ⟨s,hs⟩ := cell_faces_seams a
  refine ⟨s,?_⟩
  rw [hs,cube_frontier_faces]
  simp only [image_iUnion,image_image]
  congr 1
  funext i
  congr 1
  funext ε
  apply image_congr
  intro x hx
  exact (Cells.extension_on_cube (cellFace a i ε) ⟨x,hx⟩).trans
    (Cells.extension_on_cube a ⟨faceInsertion i ε x,faceInsertion_mem i ε hx⟩).symm

theorem cell_interior_integral : cell_interior_integralType := by
  intro r k n O a
  dsimp only
  intro c o hsource hmap hsign omega ho w V hw hV hface hzero
  let S := cube k
  let f := cellExtension a
  let M := f '' interior S
  let K := f '' S
  let eta : TangentTopField 1 k M := fun x => w x • GeometricPatches.ambientRestriction omega x
  have hS : IsCompact S := DiscontinuityCriterion.carrier_compact (cubeBox k)
  have hf : ContinuousOn f S := (Cells.extension_C1 a).continuousOn.mono (extension_spec a).2.1
  have hK : IsCompact K := hS.image_of_continuousOn hf
  have hMK : M ⊆ K := image_mono interior_subset
  have hMO : M ⊆ O := by
    rintro y ⟨x,hx,rfl⟩
    have he : f x = (a.toFun ⟨x,interior_subset hx⟩).val :=
      Cells.extension_on_cube a ⟨x,interior_subset hx⟩
    exact he.symm ▸ (a.toFun ⟨x,interior_subset hx⟩).property
  have hMambient : M ⊆ c.ambient := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [hmap] using (c.map_source (hsource.symm ▸ hx)).2
  have hRem : K \ V ⊆ M := by
    rintro y ⟨⟨x,hx,rfl⟩,hnV⟩
    by_cases hxi : x ∈ interior S
    · exact mem_image_of_mem f hxi
    · exact (hnV (hface ⟨x,⟨subset_closure hx,hxi⟩,rfl⟩)).elim
  have hCompact : IsCompact ((Subtype.val : M → E n) ⁻¹' (K \ V)) :=
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hRem)).mpr (hK.diff hV)
  have hsupp : topSupport eta ⊆ (Subtype.val : M → E n) ⁻¹' (K \ V) := by
    apply closure_minimal _ ((hK.diff hV).isClosed.preimage continuous_subtype_val)
    intro x hx
    refine ⟨hMK x.property,?_⟩
    intro hxV
    apply hx
    change w x • GeometricPatches.ambientRestriction omega x = 0
    rw [hzero hxV,zero_smul]
  have hEtaC : IsCompact (topSupport eta) := hCompact.of_isClosed_subset isClosed_closure hsupp
  have hEta : ContinuousTopField eta :=
    ManifoldIntegralIndependence.continuousTopField_weight w hw
      (ambient_restriction_continuous o.manifold.1 hMO omega ho)
  refine ⟨hEtaC,ManifoldIntegral.signed_partition_exists o _ hEtaC,?_⟩
  intro P
  have hi := ManifoldIntegralIndependence.oriented_single_chart o eta hEta hEtaC P c
    (fun x _ => hMambient x.property) ⟨1,Or.inl rfl⟩ (fun u => hsign u u.property)
  have hdiff (u : c.source) : chartDifferential c u = fderiv ℝ f u := by
    change fderivWithin ℝ c.toFun c.source u = fderiv ℝ f u
    have hcOpen : IsOpen c.source := hsource.symm ▸ isOpen_interior
    rw [fderivWithin_of_isOpen hcOpen u.property,hmap]
  have hcoeff (u : c.source) : topCoefficient eta c u =
      w (f u) * cellCoefficient a omega u := by
    change w (c.toFun u) * omega (c.toFun u)
      (fun j => chartDifferential c u (standardBasis k j)) = _
    rw [hdiff u,hmap]
    rfl
  let b : S → ℝ := fun x => w (f x) * cellCoefficient a omega x
  have hext : zeroExtension (topCoefficient eta c) = zeroExtension b := by
    funext x
    by_cases hxc : x ∈ c.source
    · have hxS : x ∈ S := interior_subset (hsource ▸ hxc)
      rw [zeroExtension_apply _ ⟨x,hxc⟩,zeroExtension_apply _ ⟨x,hxS⟩]
      exact hcoeff ⟨x,hxc⟩
    · rw [zeroExtension_of_not_mem _ hxc]
      by_cases hxS : x ∈ S
      · rw [zeroExtension_apply _ ⟨x,hxS⟩]
        have hxF : x ∈ frontier S := ⟨subset_closure hxS,
          fun hxi => hxc (hsource.symm ▸ hxi)⟩
        change 0 = w (f x) * cellCoefficient a omega x
        rw [hzero (hface (mem_image_of_mem f hxF)),zero_mul]
      · rw [zeroExtension_of_not_mem _ hxS]
  have hbi : RegionIntegrable b := by
    change RegionIntegrable (fun x : S => w (f x) * cellCoefficient a omega x)
    apply GeometricPatches.continuous_integrable (S := S)
      (f := fun x => w (f x) * cellCoefficient a omega x)
      (OneCoordinate.Boxes.jordan_carrier (cubeBox k))
    change ContinuousOn (fun x => w (f x) * cellCoefficient a omega x) (closure S)
    rw [hS.isClosed.closure_eq]
    exact (hw.continuousOn.comp hf (fun _ _ => mem_univ _)).mul
      (Cells.cellCoefficient_continuous a omega ho)
  have hbval := (GeometricPatches.region_coefficient_integral
    (OneCoordinate.Boxes.jordan_carrier (cubeBox k)) b hbi).2
  have hiVal : orientedIntegral eta P = DirectedSubstitution.coefficientIntegral
      (topCoefficient eta c) := by simpa only [one_mul] using hi.2
  exact hiVal.trans ((DirectedSubstitution.proper_congr hext).2.trans hbval.symm)

theorem cell_interior_manifold_limit : cell_interior_manifold_limitType := by
  intro r d n O a hkn hinj hrank s omega ho
  dsimp only
  obtain ⟨c,o,hhalf,hsource,hmap,hinv,hambient,hsign⟩ := cell_interior_orientation a
    (Nat.succ_pos _) hkn hinj (fun x hx => hrank x (interior_subset hx))
  obtain ⟨t,ht⟩ := cell_frontier_seams a
  let z := appendSeams s t
  have hz : z.carrier = s.carrier ∪ cellExtension a '' frontier (cube (d+1)) := by
    rw [append_seams_carrier,ht]
  obtain ⟨χ,hχ,hχv,hχzero,hχone⟩ :=
    smooth_seam_cutoff_sequence z.carrier (ambient_seams_compact z)
  have hbridge (m : ℕ) :
      IsCompact (topSupport (fun x : cellExtension a '' interior (cube (d+1)) =>
        χ m x • GeometricPatches.ambientRestriction (r := 1) omega x)) ∧
      Nonempty (SignedChartPartition o (topSupport
        (fun x : cellExtension a '' interior (cube (d+1)) =>
          χ m x • GeometricPatches.ambientRestriction (r := 1) omega x))) ∧
      ∀ P : SignedChartPartition o (topSupport
        (fun x : cellExtension a '' interior (cube (d+1)) =>
          χ m x • GeometricPatches.ambientRestriction (r := 1) omega x)),
        orientedIntegral
          (fun x : cellExtension a '' interior (cube (d+1)) =>
            χ m x • GeometricPatches.ambientRestriction (r := 1) omega x) P =
          regionIntegral (fun x : cube (d+1) =>
            χ m (cellExtension a x) * cellCoefficient a omega x) := by
    obtain ⟨V,hV,hzV,hzero⟩ := hχzero m
    apply cell_interior_integral a c o hsource hmap hsign omega ho (χ m) V
      (hχ m).continuous hV _ hzero
    intro y hy
    exact hzV (hz.symm ▸ Or.inr hy)
  refine ⟨c,o,χ,hhalf,hsource,hmap,hsign,hχ,hχv,?_,?_,
    fun m => ⟨(hbridge m).1,(hbridge m).2.1⟩,?_⟩
  · intro m
    simpa only [hz] using hχzero m
  · intro A hA hdis
    apply hχone A hA
    simpa only [hz] using hdis
  · intro Q
    have hl := (cell_seam_cutoff_limit a hkn hinj hrank z omega ho χ hχ hχv hχone).2
    have he (m : ℕ) := (hbridge m).2.2 (Q m)
    simp_rw [he]
    exact hl


abbrev RegularDecomposition := Model.RegularDecomposition
abbrev CompatibleRegularDecompositions := @Model.CompatibleRegularDecompositions

lemma regular_member {k n : ℕ} (D : RegularDecomposition k n) (i : Fin D.count)
    {x : E n} (hx : x ∈ D.piece i) (hz : x ∉ D.seams.carrier) : x ∈ D.regular i := by
  by_contra hn
  exact hz (D.singular i ⟨hx,hn⟩)

lemma regular_topSupport_compact {k n : ℕ} (D : RegularDecomposition k n)
    (omega : FormField n k) (V : Set (E n)) (hV : IsOpen V)
    (hZV : D.seams.carrier ⊆ V) (hz : EqOn omega (fun _ => 0) V) (i : Fin D.count) :
    IsCompact (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := D.regular i) omega)) := by
  have hRem : D.piece i \ V ⊆ D.regular i := by
    intro x hx
    exact regular_member D i hx.1 (fun h => hx.2 (hZV h))
  have hC : IsCompact ((Subtype.val : D.regular i → E n) ⁻¹' (D.piece i \ V)) :=
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hRem)).mpr ((D.compact i).diff hV)
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (((D.compact i).diff hV).isClosed.preimage continuous_subtype_val)
  intro x hx
  refine ⟨D.subset i x.property,?_⟩
  intro hv
  apply hx
  ext v
  change omega x _ = 0
  rw [hz hv]
  rfl

/-- Common signed chart germs follow from compact-carrier isolation, even
when only the regular parts are manifolds. -/
lemma regular_common_signed_germs {k n : ℕ} (D F : RegularDecomposition k n)
    (hc : CompatibleRegularDecompositions D F) (x : E n)
    (hx : x ∈ D.carrier) (hxZ : x ∉ D.seams.carrier ∪ F.seams.carrier) :
    ∃ i j, ∃ (c : EmbeddedChart 1 k n (D.regular i))
      (d : EmbeddedChart 1 k n (F.regular j)) (s : PointSign),
      x ∈ c.ambient ∧ d.source = c.source ∧ d.toFun = c.toFun ∧
      d.ambient = c.ambient ∧
      (∀ l, l ≠ i → Disjoint (D.regular l) c.ambient) ∧
      (∀ l, l ≠ j → Disjoint (F.regular l) c.ambient) ∧
      (∀ u : c.source, chartSign (D.orientation i).atPoint c u u.property = s.val) ∧
      (∀ u : d.source, chartSign (F.orientation j).atPoint d u u.property = s.val) := by
  obtain ⟨i,j,U,hxi,hxj,hU,hxU,heq,hUA⟩ :=
    common_piece_germ D.piece F.piece D.seams.carrier F.seams.carrier
      D.compact F.compact D.overlap F.overlap hc.1 x hx hxZ
  have hcover : (⋃ i, D.piece i) = ⋃ j, F.piece j := hc.1
  have hUB : U ∩ (⋃ l, F.piece l) = U ∩ F.piece j := by rw [← hcover,hUA,heq]
  let T := U ∩ (D.seams.carrier ∪ F.seams.carrier)ᶜ
  have hT : IsOpen T := hU.inter
    ((ambient_seams_compact D.seams).isClosed.union (ambient_seams_compact F.seams).isClosed).isOpen_compl
  have hxT : x ∈ T := ⟨hxU,hxZ⟩
  have hTeq : T ∩ D.regular i = T ∩ F.regular j := by
    ext y
    constructor
    · rintro ⟨hyT,hyi⟩
      have hyj : y ∈ F.piece j := (heq ▸ (show y ∈ U ∩ D.piece i from ⟨hyT.1,D.subset i hyi⟩)).2
      exact ⟨hyT,regular_member F j hyj (fun h => hyT.2 (Or.inr h))⟩
    · rintro ⟨hyT,hyj⟩
      have hyi : y ∈ D.piece i := (heq.symm ▸ (show y ∈ U ∩ F.piece j from ⟨hyT.1,F.subset j hyj⟩)).2
      exact ⟨hyT,regular_member D i hyi (fun h => hyT.2 (Or.inl h))⟩
  have hxiR := regular_member D i hxi (fun h => hxZ (Or.inl h))
  obtain ⟨a,s,hxa,hasign⟩ := ManifoldIntegral.constant_signed_chart_at (D.orientation i) ⟨x,hxiR⟩
  let c := D04.EmbeddedChart.restrict a T hT
  obtain ⟨d,hds,hda,hdf,hdi,hdh⟩ := chart_retarget a T hT hTeq
  have hds' : d.source = c.source := hds
  have hdf' : d.toFun = c.toFun := hdf
  have hsub : c.source ⊆ a.source := inter_subset_left
  have hcT : c.ambient ⊆ T := inter_subset_right
  have hdisA (l : Fin D.count) (hli : l ≠ i) : Disjoint (D.regular l) c.ambient := by
    apply Set.disjoint_left.mpr
    intro y hyl hyc
    have hyU := (hcT hyc).1
    have hyi : y ∈ D.piece i := (hUA ▸ (show y ∈ U ∩ (⋃ l, D.piece l) from
      ⟨hyU,mem_iUnion.mpr ⟨l,D.subset l hyl⟩⟩)).2
    exact (hcT hyc).2 (Or.inl (D.overlap l i hli ⟨D.subset l hyl,hyi⟩))
  have hdisB (l : Fin F.count) (hlj : l ≠ j) : Disjoint (F.regular l) c.ambient := by
    apply Set.disjoint_left.mpr
    intro y hyl hyc
    have hyU := (hcT hyc).1
    have hyj : y ∈ F.piece j := (hUB ▸ (show y ∈ U ∩ (⋃ l, F.piece l) from
      ⟨hyU,mem_iUnion.mpr ⟨l,F.subset l hyl⟩⟩)).2
    exact (hcT hyc).2 (Or.inr (F.overlap l j hlj ⟨F.subset l hyl,hyj⟩))
  have hcsign (u : c.source) : chartSign (D.orientation i).atPoint c u u.property = s.val := by
    rw [Orientations.restriction_sign (D.orientation i).atPoint a c (D.orientation i).manifold.1
      hsub rfl u u.property]
    exact hasign ⟨u,hsub u.property⟩
  have hdsign (u : d.source) : chartSign (F.orientation j).atPoint d u u.property = s.val := by
    have huc : (u : E k) ∈ c.source := hds' ▸ u.property
    have ht : tangentSpace 1 k (D.regular i) (c.toFun u) =
        tangentSpace 1 k (F.regular j) (d.toFun u) := by
      rw [hdf']
      exact common_chart_tangentSpaces c d (D.orientation i).manifold.1
        (D.orientation i).manifold.2.1 hds' hdf' u huc
    have hco : (F.orientation j).atPoint (d.toFun u) (d.map_source u.property).1 =
        transportOrientation ht ((D.orientation i).atPoint (c.toFun u) (c.map_source huc).1) := by
      have htransport (y : E n) (hy : y ∈ F.regular j) (he : y = c.toFun u)
          (g : tangentSpace 1 k (D.regular i) (c.toFun u) = tangentSpace 1 k (F.regular j) y) :
          (F.orientation j).atPoint y hy =
            transportOrientation g ((D.orientation i).atPoint (c.toFun u) (c.map_source huc).1) := by
        subst y
        exact (hc.2 _ ((hcT (c.map_source huc).2).2) i j (c.map_source huc).1 hy g).symm
      exact htransport _ _ (congrFun hdf' u) ht
    exact (chart_sign_transport d c (D.orientation i).manifold.1 (hds'.symm ▸ Subset.rfl)
      hdf'.symm (F.orientation j).atPoint (D.orientation i).atPoint u huc ht hco).trans (hcsign ⟨u,huc⟩)
  exact ⟨i,j,c,d,s,⟨hxa,hxT⟩,hds',hdf',hda,hdisA,hdisB,hcsign,hdsign⟩

lemma regular_common_weighted_integrals
    {r : ℕ∞ω} {k n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Set (E n)) (B : κ → Set (E n))
    (o : ∀ i, PositiveManifoldOrientation r k (A i))
    (p : ∀ j, PositiveManifoldOrientation r k (B j))
    {O : Set (E n)} (hAO : ∀ i, A i ⊆ O) (hBO : ∀ j, B j ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (i : ι) (j : κ) (c : EmbeddedChart r k n (A i)) (d : EmbeddedChart r k n (B j))
    (hs : d.source = c.source) (he : d.toFun = c.toFun) (s : PointSign)
    (hsc : ∀ u : c.source, chartSign (o i).atPoint c u u.property = s.val)
    (hsd : ∀ u : d.source, chartSign (p j).atPoint d u u.property = s.val)
    (hdisA : ∀ l, l ≠ i → Disjoint (A l) c.ambient)
    (hdisB : ∀ l, l ≠ j → Disjoint (B l) d.ambient)
    (w : E n → ℝ) (hw : Continuous w)
    (hwc : tsupport w ⊆ c.ambient) (hwd : tsupport w ⊆ d.ambient)
    (P : ∀ l, SignedChartPartition (o l)
      (topSupport (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x)))
    (Q : ∀ l, SignedChartPartition (p l)
      (topSupport (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x)))
    (hCA : ∀ l, IsCompact (topSupport (fun x : A l => w x •
      GeometricPatches.ambientRestriction (r := r) omega x)))
    (hCB : ∀ l, IsCompact (topSupport (fun x : B l => w x •
      GeometricPatches.ambientRestriction (r := r) omega x))) :
    (∑ l, orientedIntegral (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P l)) =
      ∑ l, orientedIntegral (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q l) := by
  have hzerosA (l : ι) (hli : l ≠ i) :
      orientedIntegral (fun x : A l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P l) = 0 := by
    apply oriented_integral_eq_zero
    intro x
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp (hdisA l hli) x.property (hwc h))
    rw [hz,zero_smul]
  have hzerosB (l : κ) (hlj : l ≠ j) :
      orientedIntegral (fun x : B l => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q l) = 0 := by
    apply oriented_integral_eq_zero
    intro x
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp (hdisB l hlj) x.property (hwd h))
    rw [hz,zero_smul]
  have hη := ManifoldIntegralIndependence.continuousTopField_weight w hw
    (ambient_restriction_continuous (o i).manifold.1 (hAO i) omega ho)
  have hξ := ManifoldIntegralIndependence.continuousTopField_weight w hw
    (ambient_restriction_continuous (p j).manifold.1 (hBO j) omega ho)
  have hm := ManifoldIntegralIndependence.oriented_single_chart (o i) _ hη
    (hCA i) (P i) c
    (fun x hx => hwc (weighted_topSupport_subset w _ hx)) s hsc
  have hn := ManifoldIntegralIndependence.oriented_single_chart (p j) _ hξ
    (hCB j) (Q j) d
    (fun x hx => hwd (weighted_topSupport_subset w _ hx)) s hsd
  have hcoefM : topCoefficient
      (fun x : A i => w x • GeometricPatches.ambientRestriction (r := r) omega x) c =
      localizedTopCoefficient (GeometricPatches.ambientRestriction (r := r) omega) c w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ c u
  have hcoefN : topCoefficient
      (fun x : B j => w x • GeometricPatches.ambientRestriction (r := r) omega x) d =
      localizedTopCoefficient (GeometricPatches.ambientRestriction (r := r) omega) d w := by
    funext u
    exact ManifoldIntegralIndependence.topCoefficient_weight w _ d u
  rw [hcoefM] at hm
  rw [hcoefN] at hn
  calc
    _ = orientedIntegral (fun x : A i => w x • GeometricPatches.ambientRestriction (r := r) omega x) (P i) :=
      Finset.sum_eq_single i (fun l _ hli => hzerosA l hli) (by simp)
    _ = orientedIntegral (fun x : B j => w x • GeometricPatches.ambientRestriction (r := r) omega x) (Q j) :=
      hm.2.trans ((congrArg (s.val * ·)
        (common_chart_proper_integrals c d (o i).manifold.1 hs he omega w).2).trans hn.2.symm)
    _ = _ := (Finset.sum_eq_single j (fun l _ hlj => hzerosB l hlj) (by simp)).symm


theorem regular_decomposition_away_seams : regular_decomposition_away_seamsType := by
  intro k n D F hc O hDO omega ho V hV hZW hzero
  have hAc (i : Fin D.count) := regular_topSupport_compact D omega V hV
    (fun x hx => hZW (Or.inl hx)) hzero i
  have hBc (j : Fin F.count) := regular_topSupport_compact F omega V hV
    (fun x hx => hZW (Or.inr hx)) hzero j
  refine ⟨hAc,hBc,?_⟩
  intro P Q
  let K := D.carrier ∩ tsupport omega
  have hK : IsCompact K := (isCompact_iUnion D.compact).inter_right (isClosed_tsupport omega)
  have hsV : tsupport omega ⊆ Vᶜ :=
    closure_minimal (fun x hx hxV => hx (hzero hxV)) hV.isClosed_compl
  have hKZW (x : K) : (x : E n) ∉ D.seams.carrier ∪ F.seams.carrier :=
    fun hz => hsV x.property.2 (hZW hz)
  choose a b c d sign hxc hds hdf hda hdisA hdisB hsc hsd using
    fun x : K => regular_common_signed_germs D F hc x x.property.1 (hKZW x)
  obtain ⟨m,l,R,hR⟩ := GeometricPatches.ambient_partition_exists K hK
    (fun x : K => (c x).ambient) (fun x => (c x).ambient_open)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxc ⟨x,hx⟩⟩)
  have hCA (i : Fin D.count) (t : Fin m) : IsCompact (topSupport
      (fun x : D.regular i => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x)) :=
    (hAc i).of_isClosed_subset isClosed_closure
      (ManifoldIntegralIndependence.topSupport_weight_subset _ _)
  have hCB (j : Fin F.count) (t : Fin m) : IsCompact (topSupport
      (fun x : F.regular j => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x)) :=
    (hBc j).of_isClosed_subset isClosed_closure
      (ManifoldIntegralIndependence.topSupport_weight_subset _ _)
  let PA := fun (i : Fin D.count) (t : Fin m) => Classical.choice
    (ManifoldIntegral.signed_partition_exists (D.orientation i) _ (hCA i t))
  let PB := fun (j : Fin F.count) (t : Fin m) => Classical.choice
    (ManifoldIntegral.signed_partition_exists (F.orientation j) _ (hCB j t))
  have hAO (i : Fin D.count) : D.regular i ⊆ O :=
    fun x hx => hDO (mem_iUnion.mpr ⟨i,D.subset i hx⟩)
  have hBO (j : Fin F.count) : F.regular j ⊆ O :=
    fun x hx => hDO (hc.1.symm ▸ mem_iUnion.mpr ⟨j,F.subset j hx⟩)
  have hlocal (t : Fin m) := regular_common_weighted_integrals D.regular F.regular
    D.orientation F.orientation hAO hBO omega ho
    (a (l t)) (b (l t)) (c (l t)) (d (l t)) (hds (l t)) (hdf (l t)) (sign (l t))
    (hsc (l t)) (hsd (l t)) (hdisA (l t))
    (by simpa only [hda] using hdisB (l t))
    (R.weight t) (R.smooth t).continuous (hR t) (by rw [hda]; exact hR t)
    (fun i => PA i t) (fun j => PB j t) (fun i => hCA i t) (fun j => hCB j t)
  have hsumA (i : Fin D.count) := ManifoldIntegralIndependence.oriented_finite_localization (D.orientation i)
    (GeometricPatches.ambientRestriction (r := 1) omega)
    (ambient_restriction_continuous (D.orientation i).manifold.1 (hAO i) omega ho) R.weight
    (fun t => (R.smooth t).continuous) (fun x hx => by
      have hxK : (x : E n) ∈ K := ⟨mem_iUnion.mpr ⟨i,D.subset i x.property⟩,
        ambient_topSupport_subset omega (subset_closure hx)⟩
      obtain ⟨D,hD,hKD,hone⟩ := R.sum_one
      exact hone x (hKD hxK)) (P i) (PA i)
  have hsumB (j : Fin F.count) := ManifoldIntegralIndependence.oriented_finite_localization (F.orientation j)
    (GeometricPatches.ambientRestriction (r := 1) omega)
    (ambient_restriction_continuous (F.orientation j).manifold.1 (hBO j) omega ho) R.weight
    (fun t => (R.smooth t).continuous) (fun x hx => by
      have hxU : (x : E n) ∈ D.carrier := hc.1.symm ▸ mem_iUnion.mpr ⟨j,F.subset j x.property⟩
      have hxK : (x : E n) ∈ K := ⟨hxU,
        ambient_topSupport_subset omega (subset_closure hx)⟩
      obtain ⟨D,hD,hKD,hone⟩ := R.sum_one
      exact hone x (hKD hxK)) (Q j) (PB j)
  calc
    _ = ∑ i, ∑ t, orientedIntegral
        (fun x : D.regular i => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x) (PA i t) :=
      Finset.sum_congr rfl (fun i _ => hsumA i)
    _ = ∑ t, ∑ i, orientedIntegral
        (fun x : D.regular i => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x) (PA i t) :=
      Finset.sum_comm
    _ = ∑ t, ∑ j, orientedIntegral
        (fun x : F.regular j => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x) (PB j t) :=
      Finset.sum_congr rfl (fun t _ => hlocal t)
    _ = ∑ j, ∑ t, orientedIntegral
        (fun x : F.regular j => R.weight t x • GeometricPatches.ambientRestriction (r := 1) omega x) (PB j t) :=
      Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (hsumB j).symm)


abbrev PieceRepresentation := @Model.PieceRepresentation
abbrev PieceHasIntegral := @Model.PieceRepresentation.HasIntegral
abbrev GeometricDecomposition := Model.GeometricDecomposition
abbrev HasGeometricUnionIntegral := @Model.HasGeometricUnionIntegral
abbrev geometricUnionIntegral := @Model.geometricUnionIntegral

lemma representation_inside {k n : ℕ} {K M O : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} (R : PieceRepresentation K M o O) : K ⊆ O := by
  cases R with
  | manifold same inside => exact inside
  | cell a hi hr hK hM c hs hm hp =>
    rw [hK]
    rintro y ⟨x,hx,rfl⟩
    have he : cellExtension a x = (a.toFun ⟨x,hx⟩).val := Cells.extension_on_cube a ⟨x,hx⟩
    exact he.symm ▸ (a.toFun ⟨x,hx⟩).property

lemma geometric_carrier_inside {k n : ℕ} {O : Set (E n)}
    (D : GeometricDecomposition k n O) : D.carrier ⊆ O := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  exact representation_inside (D.representation i) hi

lemma representation_integral_exists {k n : ℕ} {K M O : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} (R : PieceRepresentation K M o O)
    (hK : IsCompact K) (omega : FormField n k) (ho : IsCrForm (some 0) O omega) :
    ∃ v, R.HasIntegral omega v := by
  cases R with
  | manifold same inside =>
    have hM : IsCompact M := same ▸ hK
    have hMO : M ⊆ O := same ▸ inside
    let P := Classical.choice (ManifoldIntegral.signed_partition_exists o
      (topSupport (GeometricPatches.ambientRestriction (r := 1) omega))
      (topSupport_compact_of_compact hM _))
    refine ⟨orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) P,?_⟩
    intro Q
    exact ManifoldIntegralIndependence.oriented_independent o _
      (ambient_restriction_continuous o.manifold.1 hMO omega ho) Q P
  | cell a hi hr hK hM c hs hm hp => exact ⟨Cells.cellIntegral a omega,rfl⟩

theorem geometric_piece_integral_exists : geometric_piece_integral_existsType := by
  intro k n O D omega ho i
  exact representation_integral_exists (D.representation i) (D.compact i) omega ho

/-- A cell's excluded faces really are among the singular points of its
compact carrier: compact injectivity prevents a face from reappearing inside. -/
lemma cell_faces_subset_singular {k n : ℕ} {O : Set (E n)} (a : Cells.Cell 1 k O)
    (hi : InjOn (cellExtension a) (cube k)) :
    cellExtension a '' frontier (cube k) ⊆
      (cellExtension a '' cube k) \ (cellExtension a '' interior (cube k)) := by
  rintro y ⟨x,hx,rfl⟩
  have hxS : x ∈ cube k := (NullCovers.isClosed_carrier (cubeBox k)).closure_subset hx.1
  refine ⟨mem_image_of_mem _ hxS,?_⟩
  rintro ⟨u,hu,he⟩
  exact hx.2 (hi (interior_subset hu) hxS he ▸ hu)

/-- Seam deletion converges to each original piece's actual value. This is
proved separately for the two representations, never stored as geometric data. -/
lemma representation_cutoff_limit {k n : ℕ} {K M O : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} (R : PieceRepresentation K M o O)
    (hK : IsCompact K) (s : AmbientSeams k n) (hSing : K \ M ⊆ s.carrier)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega) (v : ℝ)
    (hv : R.HasIntegral omega v)
    (chi : ℕ → E n → ℝ) (hchi : ∀ m, ContDiff ℝ ∞ (chi m))
    (hval : ∀ m x, chi m x ∈ Icc (0 : ℝ) 1)
    (hzero : ∀ m, ∃ V : Set (E n), IsOpen V ∧ s.carrier ⊆ V ∧ EqOn (chi m) (fun _ => 0) V)
    (hone : ∀ A : Set (E n), IsCompact A → Disjoint A s.carrier →
      ∀ᶠ m in atTop, EqOn (chi m) (fun _ => 1) A)
    (P : ∀ m, SignedChartPartition o (topSupport
      (fun x : M => chi m x • GeometricPatches.ambientRestriction (r := 1) omega x))) :
    Tendsto (fun m => orientedIntegral
      (fun x : M => chi m x • GeometricPatches.ambientRestriction (r := 1) omega x) (P m))
      atTop (𝓝 v) := by
  cases R with
  | manifold same inside =>
    have hM : IsCompact M := same ▸ hK
    have hMO : M ⊆ O := same ▸ inside
    let Q := Classical.choice (ManifoldIntegral.signed_partition_exists o
      (topSupport (GeometricPatches.ambientRestriction (r := 1) omega))
      (topSupport_compact_of_compact hM _))
    have hl := manifold_seam_cutoff_limit o s
      (GeometricPatches.ambientRestriction (r := 1) omega)
      (ambient_restriction_continuous o.manifold.1 hMO omega ho)
      chi hchi hval hone Q P
    have he := hv Q
    rwa [he] at hl
  | cell a hi hr hKe hMe c hs hm hp =>
    subst K
    subst M
    have hface : cellExtension a '' frontier (cube k) ⊆ s.carrier :=
      (cell_faces_subset_singular a hi).trans hSing
    have he (m : ℕ) : orientedIntegral
        (fun x : cellExtension a '' interior (cube k) => chi m x •
          GeometricPatches.ambientRestriction (r := 1) omega x) (P m) =
        regionIntegral (fun x : cube k => chi m (cellExtension a x) * cellCoefficient a omega x) := by
      obtain ⟨V,hV,hsV,hzV⟩ := hzero m
      exact (cell_interior_integral a c o hs hm hp omega ho (chi m) V
        (hchi m).continuous hV (hface.trans hsV) hzV).2.2 (P m)
    simp_rw [he]
    have hl := (cell_seam_cutoff_limit a o.manifold.2.1 hi hr s omega ho
      chi hchi hval hone).2
    change cellIntegral a omega = v at hv
    rwa [hv] at hl

lemma compatible_regular_refl {k n : ℕ} (D : RegularDecomposition k n) :
    CompatibleRegularDecompositions D D := by
  refine ⟨rfl,?_⟩
  intro x hx i j hi hj h
  have hij : i = j := by
    by_contra hn
    exact hx (Or.inl (D.overlap i j hn ⟨D.subset i hi,D.subset j hj⟩))
  subst j
  simp [transportOrientation,Model.transportOrientation,LinearEquiv.ofEq_rfl,Orientation.map_refl]

/-- One cutoff stage already compares all regular parts. -/
lemma regular_weighted_comparison {k n : ℕ} (D F : RegularDecomposition k n)
    (hc : CompatibleRegularDecompositions D F) {O : Set (E n)} (hDO : D.carrier ⊆ O)
    (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
    (w : E n → ℝ) (hw : Continuous w) (V : Set (E n)) (hV : IsOpen V)
    (hZW : D.seams.carrier ∪ F.seams.carrier ⊆ V) (hz : EqOn w (fun _ => 0) V) :
    (∀ i, IsCompact (topSupport (fun x : D.regular i => w x •
      GeometricPatches.ambientRestriction (r := 1) omega x))) ∧
    (∀ j, IsCompact (topSupport (fun x : F.regular j => w x •
      GeometricPatches.ambientRestriction (r := 1) omega x))) ∧
    ∀ (P : ∀ i, SignedChartPartition (D.orientation i) (topSupport
        (fun x : D.regular i => w x • GeometricPatches.ambientRestriction (r := 1) omega x)))
      (Q : ∀ j, SignedChartPartition (F.orientation j) (topSupport
        (fun x : F.regular j => w x • GeometricPatches.ambientRestriction (r := 1) omega x))),
      (∑ i, orientedIntegral (fun x : D.regular i => w x •
        GeometricPatches.ambientRestriction (r := 1) omega x) (P i)) =
      ∑ j, orientedIntegral (fun x : F.regular j => w x •
        GeometricPatches.ambientRestriction (r := 1) omega x) (Q j) := by
  have h := regular_decomposition_away_seams D F hc hDO (fun y => w y • omega y)
    (continuous_ambientForm_weight omega ho w hw) V hV hZW
    (fun y hy => by change w y • omega y = 0; rw [hz hy,zero_smul])
  have heA (i : Fin D.count) := ambientRestriction_weight (r := 1) (M := D.regular i) w omega
  have heB (j : Fin F.count) := ambientRestriction_weight (r := 1) (M := F.regular j) w omega
  refine ⟨?_,?_,?_⟩
  · intro i
    simpa only [heA i] using h.1 i
  · intro j
    simpa only [heB j] using h.2.1 j
  · intro P Q
    let RA := fun i => (heA i).symm ▸ P i
    let RB := fun j => (heB j).symm ▸ Q j
    exact (Finset.sum_congr rfl (fun i _ => oriented_integral_cast (heA i).symm (P i))).trans
      ((h.2.2 RA RB).trans (Finset.sum_congr rfl
        (fun j _ => (oriented_integral_cast (heB j).symm (Q j)).symm)))

theorem geometric_decomposition_independent : geometric_decomposition_independentType := by
  intro k n O D F hc omega ho a b ha hb
  let z := appendSeams D.seams F.seams
  obtain ⟨chi,hchi,hval,hzero,hone⟩ := smooth_seam_cutoff_sequence z.carrier (ambient_seams_compact z)
  have hlocal (m : ℕ) := regular_weighted_comparison
    D.toRegularDecomposition F.toRegularDecomposition hc
    (geometric_carrier_inside D) omega ho (chi m) (hchi m).continuous
    (hzero m).choose (hzero m).choose_spec.1
    (by rw [← append_seams_carrier]; exact (hzero m).choose_spec.2.1)
    (hzero m).choose_spec.2.2
  let PA := fun (i : Fin D.count) (m : ℕ) => Classical.choice
    (ManifoldIntegral.signed_partition_exists (D.orientation i) _ ((hlocal m).1 i))
  let PB := fun (j : Fin F.count) (m : ℕ) => Classical.choice
    (ManifoldIntegral.signed_partition_exists (F.orientation j) _ ((hlocal m).2.1 j))
  have hlimA (i : Fin D.count) := representation_cutoff_limit (D.representation i) (D.compact i)
    z (fun x hx => by rw [append_seams_carrier]; exact Or.inl (D.singular i hx))
    omega ho (a i) (ha i) chi hchi hval hzero hone (PA i)
  have hlimB (j : Fin F.count) := representation_cutoff_limit (F.representation j) (F.compact j)
    z (fun x hx => by rw [append_seams_carrier]; exact Or.inr (F.singular j hx))
    omega ho (b j) (hb j) chi hchi hval hzero hone (PB j)
  have hEq (m : ℕ) := (hlocal m).2.2 (fun i => PA i m) (fun j => PB j m)
  have hA := tendsto_finsetSum Finset.univ (fun i _ => hlimA i)
  have hB := tendsto_finsetSum Finset.univ (fun j _ => hlimB j)
  simp only [hEq] at hA
  exact tendsto_nhds_unique hA hB

theorem geometric_union_integral_exists : geometric_union_integral_existsType := by
  intro k n O D omega ho
  choose v hv using geometric_piece_integral_exists D omega ho
  have hValue : HasGeometricUnionIntegral D omega (∑ i, v i) := by
    intro F hc w hw
    exact (geometric_decomposition_independent D F hc omega ho v w hv hw).symm
  refine ⟨∑ i, v i,hValue,?_⟩
  intro w hw
  exact (hw D (compatible_regular_refl D.toRegularDecomposition) v hv).symm

theorem geometric_union_integral_eq_sum : geometric_union_integral_eq_sumType := by
  intro k n O D F hc omega ho a ha
  have hex : ∃ v, HasGeometricUnionIntegral D omega v :=
    (geometric_union_integral_exists D omega ho).exists
  have hv := Classical.choose_spec hex
  change (if h : ∃ v, Model.HasGeometricUnionIntegral D omega v then Classical.choose h else 0) = _
  rw [dite_eq_left hex]
  exact (hv F hc a ha).symm

theorem geometric_union_integral_independent : geometric_union_integral_independentType := by
  intro k n O D F hc omega ho
  choose a ha using geometric_piece_integral_exists F omega ho
  exact (geometric_union_integral_eq_sum D F hc omega ho a ha).trans
    (geometric_union_integral_eq_sum F F (compatible_regular_refl F.toRegularDecomposition)
      omega ho a ha).symm

theorem finite_seams : finite_seamsType := by
  intro k n N s
  choose P hP hcover using fun i => (s i).cover
  refine ⟨{ carrier := ⋃ i, (s i).carrier
            isCompact := isCompact_iUnion (fun i => (s i).isCompact)
            cover := ⟨⋃ i, P i,Set.countable_iUnion hP,?_⟩ },rfl⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hcover i hi)
  exact mem_iUnion.mpr ⟨⟨p.val,mem_iUnion.mpr ⟨i,p.property⟩⟩,hp⟩

theorem cell_family_display : cell_family_displayType := by
  intro k n N O hk hkn a hi hr s hover
  have hex (i : Fin N) := cell_interior_orientation (a i) hk hkn (hi i)
    (fun x hx => hr i x (interior_subset hx))
  choose c o hhalf hsource hmap hinv hambient hsign using hex
  have hfaces : ∀ i, ∃ t : AmbientSeams k n,
      t.carrier = cellExtension (a i) '' frontier (cube k) := by
    intro i
    cases k with
    | zero => omega
    | succ d => exact cell_frontier_seams (a i)
  choose t ht using hfaces
  obtain ⟨z,hz⟩ := finite_seams t
  let seams := appendSeams s z
  have hseams : seams.carrier = s.carrier ∪ ⋃ i, cellExtension (a i) '' frontier (cube k) := by
    rw [append_seams_carrier,hz]
    simp_rw [ht]
  let D : GeometricDecomposition k n O :=
    { count := N
      piece := fun i => cellExtension (a i) '' cube k
      compact := fun i => (DiscontinuityCriterion.carrier_compact (cubeBox k)).image_of_continuousOn
        ((Cells.extension_C1 (a i)).continuousOn.mono (extension_spec (a i)).2.1)
      regular := fun i => cellExtension (a i) '' interior (cube k)
      subset := fun i => image_mono interior_subset
      orientation := o
      seams := seams
      singular := by
        rintro i y ⟨⟨x,hx,rfl⟩,hn⟩
        have hxi : x ∉ interior (cube k) := fun h => hn (mem_image_of_mem _ h)
        rw [hseams]
        exact Or.inr (mem_iUnion.mpr ⟨i,x,⟨subset_closure hx,hxi⟩,rfl⟩)
      overlap := fun i j hij x hx => by
        rw [hseams]
        exact Or.inl (hover i j hij hx)
      representation := fun i => .cell (a i) (hi i) (hr i) rfl rfl
        (c i) (hsource i) (hmap i) (hsign i) }
  refine ⟨D,Equiv.refl _,rfl,hseams,fun _ => ⟨rfl,rfl⟩,?_,?_⟩
  · intro i
    exact ⟨c i,hsource i,hmap i,hsign i⟩
  · intro omega ho
    exact geometric_union_integral_eq_sum D D (compatible_regular_refl D.toRegularDecomposition)
      omega ho (fun i => cellIntegral (a i) omega) (fun _ => rfl)

abbrev manifoldGeometricDecomposition := @Model.manifoldGeometricDecomposition

theorem geometric_union_integral_manifold : geometric_union_integral_manifoldType := by
  intro k n O D hDO omega ho
  let F := manifoldGeometricDecomposition D hDO
  let P := fun i => Classical.choice (ManifoldIntegral.signed_partition_exists (D.orientation i)
    (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := D.piece i) omega))
    (topSupport_compact_of_compact (D.compact i) _))
  let a := fun i => orientedIntegral (GeometricPatches.ambientRestriction (r := 1) omega) (P i)
  have ha (i : Fin F.count) : (F.representation i).HasIntegral omega (a i) := by
    intro Q
    exact ManifoldIntegralIndependence.oriented_independent (D.orientation i) _
      (ambient_restriction_continuous (D.orientation i).manifold.1
        (fun x hx => hDO (mem_iUnion.mpr ⟨i,hx⟩)) omega ho) Q (P i)
  exact (geometric_union_integral_eq_sum F F (compatible_regular_refl F.toRegularDecomposition)
    omega ho a ha).trans
    (compact_union_integral_eq_sum D D (compatible_decompositions_refl D) hDO omega ho P).symm

abbrev CompactSeam := Model.CompactSeam

/-- Local representatives on an arbitrary parameter set can be covered by
countably many compact C¹ images. No compactness or sigma-compactness of the
parameter set is assumed. The covering images may overcover the original image. -/
theorem local_parameter_compact_cover {d k n : ℕ} (hdk : d < k)
    (S : Set (E d)) (f : E d → E n)
    (hf : ∀ x ∈ S, ∃ (U : Set (E d)) (g : E d → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g f (S ∩ U)) :
    ∃ P : Set (Model.CompactSeam k n), P.Countable ∧
      f '' S ⊆ ⋃ p : P, p.val.map '' p.val.parameter := by
  have hlocal (x : S) : ∃ (r : ℝ) (p : Model.CompactSeam k n),
      0 < r ∧ f '' (S ∩ Metric.ball x.val r) ⊆ p.map '' p.parameter := by
    obtain ⟨U,g,hU,hg,heq⟩ := hf x.val x.property
    obtain ⟨T,hT,hgT⟩ := hg.contDiffOn (m := 1) le_rfl (by simp)
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hT)
    have hsub : Metric.closedBall x.val (r/2) ⊆ Metric.ball x.val r :=
      Metric.closedBall_subset_ball (half_lt_self hr)
    let p : Model.CompactSeam k n :=
      { dim := d
        lower := hdk
        parameter := Metric.closedBall x.val (r/2)
        compact := isCompact_closedBall _ _
        map := g
        localC1 := by
          intro y hy
          refine ⟨Set.univ,g,Filter.univ_mem,?_,fun _ _ => rfl⟩
          exact hgT.contDiffAt (mem_of_superset
            (Metric.isOpen_ball.mem_nhds (hsub hy)) (fun _ hz => (hball hz).2)) }
    refine ⟨r/2,p,half_pos hr,?_⟩
    rintro y ⟨z,⟨hzS,hzB⟩,rfl⟩
    exact ⟨z,Metric.ball_subset_closedBall hzB,heq ⟨hzS,(hball (hsub
      (Metric.ball_subset_closedBall hzB))).1⟩⟩
  choose r p hr hcover using hlocal
  obtain ⟨C,hC,hCS⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun x : S => Metric.ball x.val (r x)) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  refine ⟨p '' C,hC.image p,?_⟩
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨z,hz⟩ := mem_iUnion.mp (hCS hx)
  obtain ⟨hzC,hzB⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨⟨p z,⟨z,hzC,rfl⟩⟩,hcover z ⟨x,⟨hx,hzB⟩,rfl⟩⟩

/-- Compact overlap sets inside countably many noncompact parameter pieces
have an admissible seam presentation with exactly their original carrier. -/
theorem parameter_seams {k n : ℕ} {ι : Type} [Countable ι]
    (d : ι → ℕ) (hd : ∀ i, d i < k) (S : ∀ i, Set (E (d i)))
    (f : ∀ i, E (d i) → E n)
    (hf : ∀ i x, x ∈ S i → ∃ (U : Set (E (d i))) (g : E (d i) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f i) (S i ∩ U))
    (Z : Set (E n)) (hZ : IsCompact Z) (hcover : Z ⊆ ⋃ i, f i '' S i) :
    ∃ s : AmbientSeams k n, s.carrier = Z := by
  choose P hP hPf using fun i => local_parameter_compact_cover (hd i) (S i) (f i) (hf i)
  refine ⟨{ carrier := Z
            isCompact := hZ
            cover := ⟨⋃ i, P i,Set.countable_iUnion hP,?_⟩ },rfl⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hPf i hi)
  exact mem_iUnion.mpr ⟨⟨p.val,mem_iUnion.mpr ⟨i,p.property⟩⟩,hp⟩

/-- The complete image of a lower-dimensional embedded C¹ manifold, including
one with boundary or noncompact chart domains, has a countable compact cover. -/
theorem embedded_compact_cover {d k n : ℕ} (hdk : d < k) (M : Set (E n))
    (hM : IsEmbeddedManifold 1 d M) :
    ∃ P : Set (Model.CompactSeam k n), P.Countable ∧
      M ⊆ ⋃ p : P, p.val.map '' p.val.parameter := by
  have hchart (x : M) : ∃ c : EmbeddedChart 1 d n M, x.val ∈ c.ambient := by
    obtain ⟨c,u,hu,he⟩ := hM.2.2 x.val x.property
    exact ⟨c,he ▸ (c.map_source hu.1).2⟩
  choose c hc using hchart
  have hloc (x : M) : ∀ u ∈ (c x).source,
      ∃ (U : Set (E d)) (g : E d → E n),
        U ∈ 𝓝 u ∧ ContDiffAt ℝ 1 g u ∧ EqOn g (c x).toFun ((c x).source ∩ U) := by
    intro u hu
    obtain ⟨W,g,hW,huW,he,hg,_⟩ := (c x).regular u hu
    exact ⟨W,g,hW.mem_nhds huW,hg.contDiffAt (hW.mem_nhds huW),he⟩
  choose P hP hPf using fun x : M =>
    local_parameter_compact_cover hdk (c x).source (c x).toFun (hloc x)
  obtain ⟨C,hC,hCM⟩ := (HereditarilyLindelofSpace.isLindelof M).elim_countable_subcover
    (fun x : M => (c x).ambient) (fun x => (c x).ambient_open) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hc ⟨x,hx⟩⟩)
  letI := hC.to_subtype
  refine ⟨⋃ x : C, P x.val,Set.countable_iUnion (fun x => hP x.val),?_⟩
  intro x hx
  obtain ⟨z,hz⟩ := mem_iUnion.mp (hCM hx)
  obtain ⟨hzC,hzA⟩ := mem_iUnion.mp hz
  have hu : (c z).invFun x ∈ (c z).source := (c z).map_target ⟨hx,hzA⟩
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hPf z ⟨(c z).invFun x,hu,(c z).right_inv x ⟨hx,hzA⟩⟩)
  exact mem_iUnion.mpr ⟨⟨p.val,mem_iUnion.mpr ⟨⟨z,hzC⟩,p.property⟩⟩,hp⟩

/-- No compact parameter display is required of the lower-dimensional pieces. -/
theorem embedded_seams {k n : ℕ} {ι : Type} [Countable ι]
    (d : ι → ℕ) (hd : ∀ i, d i < k) (M : ι → Set (E n))
    (hM : ∀ i, IsEmbeddedManifold 1 (d i) (M i))
    (Z : Set (E n)) (hZ : IsCompact Z) (hcover : Z ⊆ ⋃ i, M i) :
    ∃ s : AmbientSeams k n, s.carrier = Z := by
  choose P hP hPf using fun i => embedded_compact_cover (hd i) (M i) (hM i)
  refine ⟨{ carrier := Z
            isCompact := hZ
            cover := ⟨⋃ i, P i,Set.countable_iUnion hP,?_⟩ },rfl⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hPf i hi)
  exact mem_iUnion.mpr ⟨⟨p.val,mem_iUnion.mpr ⟨i,p.property⟩⟩,hp⟩

lemma compact_overlap_carrier {n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (E n)) (hA : ∀ i, IsCompact (A i)) :
    IsCompact (⋃ i, ⋃ j : {j : ι // j ≠ i}, A i ∩ A j.val) :=
  isCompact_iUnion fun i => isCompact_iUnion fun j => (hA i).inter (hA j.val)

/-- Exact compact overlap carriers, even when the stipulated C¹ seam pieces
have noncompact parameter domains. -/
theorem finite_overlap_parameter_seams {k n : ℕ} {ι κ : Type} [Fintype ι] [Countable κ]
    (A : ι → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (d : κ → ℕ) (hd : ∀ l, d l < k) (S : ∀ l, Set (E (d l)))
    (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, f l '' S l) :
    ∃ s : AmbientSeams k n,
      s.carrier = (⋃ i, ⋃ j : {j : ι // j ≠ i}, A i ∩ A j.val) ∧
      ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier := by
  obtain ⟨s,hs⟩ := parameter_seams d hd S f hf _ (compact_overlap_carrier A hA) (by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    exact hover i j.val j.property.symm hj)
  refine ⟨s,hs,?_⟩
  intro i j hij x hx
  rw [hs]
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨j,hij.symm⟩,hx⟩⟩

/-- The same original-object admission for noncompact lower-dimensional
embedded manifolds with boundary. -/
theorem finite_overlap_embedded_seams {k n : ℕ} {ι κ : Type} [Fintype ι] [Countable κ]
    (A : ι → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (d : κ → ℕ) (hd : ∀ l, d l < k) (M : κ → Set (E n))
    (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, M l) :
    ∃ s : AmbientSeams k n,
      s.carrier = (⋃ i, ⋃ j : {j : ι // j ≠ i}, A i ∩ A j.val) ∧
      ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier := by
  obtain ⟨s,hs⟩ := embedded_seams d hd M hM _ (compact_overlap_carrier A hA) (by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    exact hover i j.val j.property.symm hj)
  refine ⟨s,hs,?_⟩
  intro i j hij x hx
  rw [hs]
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨j,hij.symm⟩,hx⟩⟩

/-- Direct specialization to the source's original regular cells and actual
cell integrals, without compactness assumptions on the lower-dimensional
parameter pieces containing their overlaps. Displayed faces are themselves
local-C¹ parameter images and may be included in this family. -/
theorem cell_family_from_lower_parameters {k n N : ℕ} {O : Set (E n)}
    (hk : 0 < k) (hkn : k ≤ n) (a : Fin N → Cells.Cell 1 k O)
    (hi : ∀ i, InjOn (Cells.cellExtension (a i)) (Cells.cube k))
    (hr : ∀ i, ∀ x ∈ Cells.cube k, Function.Injective (fderiv ℝ (Cells.cellExtension (a i)) x))
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (S : ∀ l, Set (E (d l))) (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j →
      (Cells.cellExtension (a i) '' Cells.cube k) ∩
      (Cells.cellExtension (a j) '' Cells.cube k) ⊆ ⋃ l, f l '' S l) :
    ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, Cells.cellExtension (a i) '' Cells.cube k ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        geometricUnionIntegral D omega = ∑ i, Cells.cellIntegral (a i) omega := by
  have hA (i : Fin N) : IsCompact (Cells.cellExtension (a i) '' Cells.cube k) :=
    (DiscontinuityCriterion.carrier_compact (Cells.cubeBox k)).image_of_continuousOn
      ((Cells.extension_C1 (a i)).continuousOn.mono (Specs.D04.C15.CellsChainsAndIntegrals.Model.extension_spec (a i)).2.1)
  obtain ⟨s,_,hs⟩ := finite_overlap_parameter_seams
    (fun i => Cells.cellExtension (a i) '' Cells.cube k) hA d hd S f hf hover
  obtain ⟨D,e,hD,_,_,_,hv⟩ := cell_family_display hk hkn a hi hr s hs
  exact ⟨D,hD,hv⟩

/-- Embedded lower-dimensional seam pieces give the identical source cell
admission, with their noncompactness and their intrinsic boundaries allowed. -/
theorem cell_family_from_lower_manifolds {k n N : ℕ} {O : Set (E n)}
    (hk : 0 < k) (hkn : k ≤ n) (a : Fin N → Cells.Cell 1 k O)
    (hi : ∀ i, InjOn (Cells.cellExtension (a i)) (Cells.cube k))
    (hr : ∀ i, ∀ x ∈ Cells.cube k, Function.Injective (fderiv ℝ (Cells.cellExtension (a i)) x))
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (M : κ → Set (E n)) (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j →
      (Cells.cellExtension (a i) '' Cells.cube k) ∩
      (Cells.cellExtension (a j) '' Cells.cube k) ⊆ ⋃ l, M l) :
    ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, Cells.cellExtension (a i) '' Cells.cube k ∧
      ∀ omega : FormField n k, IsCrForm (some 0) O omega →
        geometricUnionIntegral D omega = ∑ i, Cells.cellIntegral (a i) omega := by
  have hA (i : Fin N) : IsCompact (Cells.cellExtension (a i) '' Cells.cube k) :=
    (DiscontinuityCriterion.carrier_compact (Cells.cubeBox k)).image_of_continuousOn
      ((Cells.extension_C1 (a i)).continuousOn.mono (Specs.D04.C15.CellsChainsAndIntegrals.Model.extension_spec (a i)).2.1)
  obtain ⟨s,_,hs⟩ := finite_overlap_embedded_seams
    (fun i => Cells.cellExtension (a i) '' Cells.cube k) hA d hd M hM hover
  obtain ⟨D,e,hD,_,_,_,hv⟩ := cell_family_display hk hkn a hi hr s hs
  exact ⟨D,hD,hv⟩

/-- The actual original manifold integrals admit the same unified geometric
value. Every signed chart partition on every original piece is arbitrary. -/
lemma manifold_family_from_seams {k n N : ℕ} {O : Set (E n)}
    (A : Fin N → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i)) (hAO : ∀ i, A i ⊆ O)
    (s : AmbientSeams k n) (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ s.carrier) :
    ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, A i ∧
      ∀ (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
        (Q : ∀ i, SignedChartPartition (o i)
          (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega))),
        geometricUnionIntegral D omega =
          ∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega) (Q i) := by
  let C : Model.CompactManifoldDecomposition k n :=
    { count := N, piece := A, compact := hA, orientation := o, seams := s, overlap := hover }
  have hCO : C.carrier ⊆ O := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hAO i hi
  refine ⟨manifoldGeometricDecomposition C hCO,rfl,?_⟩
  intro omega ho Q
  exact (geometric_union_integral_manifold C hCO omega ho).trans
    (compact_union_integral_eq_sum C C (compatible_decompositions_refl C) hCO omega ho Q)

/-- Distinct compact manifold pieces need not lie in any common smooth
manifold. Their lower-dimensional seam parametrizations may be noncompact. -/
theorem manifold_family_from_lower_parameters {k n N : ℕ} {O : Set (E n)}
    (A : Fin N → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i)) (hAO : ∀ i, A i ⊆ O)
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (S : ∀ l, Set (E (d l))) (f : ∀ l, E (d l) → E n)
    (hf : ∀ l x, x ∈ S l → ∃ (U : Set (E (d l))) (g : E (d l) → E n),
      U ∈ 𝓝 x ∧ ContDiffAt ℝ 1 g x ∧ EqOn g (f l) (S l ∩ U))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, f l '' S l) :
    ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, A i ∧
      ∀ (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
        (Q : ∀ i, SignedChartPartition (o i)
          (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega))),
        geometricUnionIntegral D omega =
          ∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega) (Q i) := by
  obtain ⟨s,_,hs⟩ := finite_overlap_parameter_seams A hA d hd S f hf hover
  exact manifold_family_from_seams A hA o hAO s hs

/-- The corresponding full source admission when lower-dimensional seams
are embedded manifolds, including noncompact pieces with boundary. -/
theorem manifold_family_from_lower_manifolds {k n N : ℕ} {O : Set (E n)}
    (A : Fin N → Set (E n)) (hA : ∀ i, IsCompact (A i))
    (o : ∀ i, PositiveManifoldOrientation 1 k (A i)) (hAO : ∀ i, A i ⊆ O)
    {κ : Type} [Countable κ] (d : κ → ℕ) (hd : ∀ l, d l < k)
    (M : κ → Set (E n)) (hM : ∀ l, IsEmbeddedManifold 1 (d l) (M l))
    (hover : ∀ i j, i ≠ j → A i ∩ A j ⊆ ⋃ l, M l) :
    ∃ D : GeometricDecomposition k n O,
      D.carrier = ⋃ i, A i ∧
      ∀ (omega : FormField n k) (ho : IsCrForm (some 0) O omega)
        (Q : ∀ i, SignedChartPartition (o i)
          (topSupport (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega))),
        geometricUnionIntegral D omega =
          ∑ i, orientedIntegral (GeometricPatches.ambientRestriction (r := 1) (M := A i) omega) (Q i) := by
  obtain ⟨s,_,hs⟩ := finite_overlap_embedded_seams A hA d hd M hM hover
  exact manifold_family_from_seams A hA o hAO s hs

end D04.GeometricUnion
