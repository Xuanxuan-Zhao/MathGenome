import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.FiniteDegree
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.CompactMapFiniteness

noncomputable section
open Set Filter Topology

namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

lemma localMultiplicity_hasMultiplicity {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    HasMultiplicity S T f a (localMultiplicity S T f a) := by
  have h : ∃ m, HasMultiplicity S T f a m := (exists_unique_multiplicity S T f hf hnc a).exists
  simpa only [localMultiplicity, dite_eq_left h] using Classical.choose_spec h

lemma localMultiplicity_eq_of_hasMultiplicity {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c)
    {a : X} {m : ℕ} (hm : HasMultiplicity S T f a m) : localMultiplicity S T f a = m :=
  (exists_unique_multiplicity S T f hf hnc a).unique
    (localMultiplicity_hasMultiplicity hf hnc a) hm

lemma localMultiplicity_pos {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    0 < localMultiplicity S T f a := (localMultiplicity_hasMultiplicity hf hnc a).1

lemma localMultiplicity_eq_one_of_not_ramified {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c)
    {a : X} (ha : a ∉ ramificationLocus S T f) : localMultiplicity S T f a = 1 := by
  have hm := localMultiplicity_hasMultiplicity hf hnc a
  have hn : ¬ 1 < localMultiplicity S T f a := fun h => ha ⟨_, hm, h⟩
  have hp := hm.1
  omega

lemma locallyBiholomorphicAt_of_not_branch {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c)
    {a : X} (ha : f a ∉ branchValueSet S T f) : LocallyBiholomorphicAt S T f a := by
  have har : a ∉ ramificationLocus S T f := fun h => ha ⟨a, h, rfl⟩
  exact (locally_biholomorphic_iff_multiplicity_one S T f hf hnc a _
    (localMultiplicity_hasMultiplicity hf hnc a)).mpr
      (localMultiplicity_eq_one_of_not_ramified hf hnc har)

/-- A local biholomorphism is locally injective as a map of the actual spaces. -/
lemma LocallyBiholomorphicAt.exists_open_injOn {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} {a : X} (ha : LocallyBiholomorphicAt S T f a) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ Set.InjOn f U := by
  obtain ⟨e, he, d, hd, hae, hfa, U, V, g, haU, hU, hV, hpair⟩ := ha
  let W := e.val.source ∩ e.val ⁻¹' U
  have hW : IsOpen W := e.val.isOpen_inter_preimage hpair.1.1
  have haW : a ∈ W := ⟨hae, haU⟩
  refine ⟨W, hW, haW, ?_⟩
  intro x hx y hy hxy
  apply e.val.injOn hx.1 hy.1
  apply (biholomorphicPair_bijOn U V _ _ hpair).1.2.1 hx.2 hy.2
  simp only [coordinateMap, e.val.left_inv hx.1, e.val.left_inv hy.1, hxy]

/-- The proper-map step is supplied by compactness, through the checked
closed-map covering theorem. This proves genuinely evenly covered neighborhoods. -/
theorem compact_holomorphicMap_coveringOn_regularValues :
    Specs.D12Complex.Ch20.FiniteDegree.compact_holomorphicMap_coveringOn_regularValues_type := by
  intro X Y _ _ _ S T f hf hnc
  let := S.connected
  let := S.hausdorff
  let := T.hausdorff
  have hcont := holomorphicMap_continuous S T f hf
  have hopen := holomorphicMap_isOpenMap S T f hf hnc
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hcont
  intro a ha
  have hlocal := locallyBiholomorphicAt_of_not_branch hf hnc ha
  obtain ⟨U, hU, haU, hinj⟩ := hlocal.exists_open_injOn
  let e : OpenPartialHomeomorph X Y :=
    OpenPartialHomeomorph.ofContinuousOpen hinj.toPartialEquiv hcont.continuousOn hopen hU
  exact ⟨e, haU, rfl⟩

lemma fiberMultiplicitySum_pos [CompactSpace X] {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} (hf : HolomorphicMap S T f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) (b : Y) : 0 < fiberMultiplicitySum S T f b := by
  classical
  have hfin := compact_holomorphicMap_finite_fibers S T f hf hnc b
  letI : Fintype {a // f a = b} := hfin.fintype
  obtain ⟨a, ha⟩ := compact_holomorphicMap_surjective S T f hf hnc b
  letI : Nonempty {a // f a = b} := ⟨⟨a, ha⟩⟩
  rw [fiberMultiplicitySum, finsum_eq_sum_of_fintype]
  exact Finset.sum_pos (fun x _ => localMultiplicity_pos hf hnc x) Finset.univ_nonempty

lemma fiberMultiplicitySum_eq_card_of_not_branch [CompactSpace X] {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} (hf : HolomorphicMap S T f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) {b : Y} (hb : b ∉ branchValueSet S T f) :
    fiberMultiplicitySum S T f b = Nat.card {a // f a = b} := by
  classical
  letI : Fintype {a // f a = b} :=
    (compact_holomorphicMap_finite_fibers S T f hf hnc b).fintype
  rw [fiberMultiplicitySum, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  have hm (a : {a // f a = b}) : localMultiplicity S T f a = 1 := by
    apply localMultiplicity_eq_one_of_not_ramified hf hnc
    intro har
    exact hb ⟨a, har, a.property⟩
  simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- Contribution from a source neighborhood to one fibre. -/
def localFiberSum (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (U : Set X) (b : Y) : ℕ :=
  ∑ᶠ x : {x // x ∈ U ∧ f x = b}, localMultiplicity S T f x.val

/-- A power neighborhood can be chosen inside any prescribed neighborhood.
Its weighted contribution is constant, including the central ramified fibre. -/
lemma exists_constant_local_fiberSum {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c)
    (a : X) (O : Set X) (hO : IsOpen O) (haO : a ∈ O) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ U ⊆ O ∧
      ∃ V : Set Y, IsOpen V ∧ f a ∈ V ∧
        ∀ b ∈ V, localFiberSum S T f U b = localMultiplicity S T f a := by
  classical
  obtain ⟨R, hR, hoR, haR⟩ := eventually_nhds_iff.mp
    (ramification_eventually_absent hf hnc a)
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  obtain ⟨d, hd, hfa⟩ := T.isAtlas.1 (f a)
  have heM := subset_maximalAtlas S.isAtlas he
  have hdM := subset_maximalAtlas T.isAtlas hd
  let Ω := coordinateDomain e d f ∩ (e.val.target ∩ e.val.symm ⁻¹' (O ∩ R))
  have hF := coordinate_holomorphicOn hf heM hdM
  have hoΩ : IsOpen Ω := hF.1.inter (e.val.isOpen_inter_preimage_symm (hO.inter hoR))
  have haΩ : e.val a ∈ Ω := ⟨mem_coordinateDomain ha hfa,
    e.val.map_source ha, by simpa only [mem_preimage, e.val.left_inv ha, mem_inter_iff] using And.intro haO haR⟩
  obtain ⟨m, hm, r, hr, P, φ, ψ, haP, hP, hpair, hφ, hform, himage, hcount,
      hcenter, horder⟩ := LocalMappingNormalForm.local_mapping_normal_form Ω
    (coordinateMap e d f) (e.val a) ⟨hoΩ, fun z hz => hF.2 z hz.1⟩ haΩ
      (coordinate_not_eventually_constant hf hnc ha hfa)
  have hc : coordinateMap e d f (e.val a) = d.val (f a) := by
    simp only [coordinateMap, e.val.left_inv ha]
  have hmEq : m = localMultiplicity S T f a := by
    apply ENat.natCast_inj.mp
    exact horder.symm.trans (by
      simpa only [coordinateOrder, hc] using
        (localMultiplicity_hasMultiplicity hf hnc a).2 e heM d hdM ha hfa)
  let U := e.val.symm '' P
  have hPT : P ⊆ e.val.target := fun z hz => (hP hz).1.1
  have hoU : IsOpen U := e.val.isOpen_image_symm_of_subset_target hpair.1.1 hPT
  have haU : a ∈ U := ⟨e.val a, haP, e.val.left_inv ha⟩
  have hUO : U ⊆ O := by
    rintro x ⟨z, hz, rfl⟩
    exact (hP hz).2.2.1
  have hUR : U ⊆ R := by
    rintro x ⟨z, hz, rfl⟩
    exact (hP hz).2.2.2
  have hUe : U ⊆ e.val.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.val.map_target (hPT hz)
  have hEU (x : X) (hx : x ∈ U) : e.val x ∈ P := by
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [e.val.right_inv (hPT hz)] using hz
  let B := Metric.ball (coordinateMap e d f (e.val a)) (r ^ m)
  have hBT : B ⊆ d.val.target := by
    dsimp only [B]
    rw [← himage]
    rintro w ⟨z, hz, rfl⟩
    exact d.val.map_source (hP hz).1.2
  let V := d.val.symm '' B
  have hoV : IsOpen V := d.val.isOpen_image_symm_of_subset_target Metric.isOpen_ball hBT
  have hfaV : f a ∈ V := by
    refine ⟨d.val (f a), ?_, d.val.left_inv hfa⟩
    rw [← hc]
    exact Metric.mem_ball_self (pow_pos hr m)
  have hVd : V ⊆ d.val.source := by
    rintro b ⟨w, hw, rfl⟩
    exact d.val.map_target (hBT hw)
  have hVB (b : Y) (hb : b ∈ V) : d.val b ∈ B := by
    obtain ⟨w, hw, rfl⟩ := hb
    simpa only [d.val.right_inv (hBT hw)] using hw
  have center_eq (x : X) (hx : x ∈ U) (hfx : f x = f a) : x = a := by
    apply e.val.injOn (hUe hx) ha
    apply (hcenter _ (hEU x hx)).mp
    simp only [coordinateMap, e.val.left_inv (hUe hx), e.val.left_inv ha, hfx]
  refine ⟨U, hoU, haU, hUO, V, hoV, hfaV, ?_⟩
  intro b hb
  by_cases hba : b = f a
  · subst b
    change (∑ᶠ x : {x // x ∈ U ∧ f x = f a}, localMultiplicity S T f x.val) = _
    rw [finsum_eq_single _ (⟨a, haU, rfl⟩ : {x // x ∈ U ∧ f x = f a})]
    intro x hxa
    exact (hxa (Subtype.ext (center_eq x x.property.1 x.property.2))).elim
  · have hbij : Set.BijOn e.val {x | x ∈ U ∧ f x = b}
        {z | z ∈ P ∧ coordinateMap e d f z = d.val b} := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        refine ⟨hEU x hx.1, ?_⟩
        simp only [coordinateMap, e.val.left_inv (hUe hx.1), hx.2]
      · intro x hx y hy hxy
        exact e.val.injOn (hUe hx.1) (hUe hy.1) hxy
      · intro z hz
        refine ⟨e.val.symm z, ⟨⟨z, hz.1, rfl⟩, ?_⟩, e.val.right_inv (hPT hz.1)⟩
        exact d.val.injOn (hP hz.1).1.2 (hVd hb) hz.2
    have hw0 : d.val b ≠ coordinateMap e d f (e.val a) := by
      rw [hc]
      exact fun hh => hba (d.val.injOn (hVd hb) hfa hh)
    obtain ⟨hfin, hcard⟩ := hcount (d.val b) (hVB b hb) hw0
    have hfinX := hbij.finite_iff_finite.mpr hfin
    have hcardX := hbij.ncard_eq.trans (hcard.trans hmEq)
    letI : Fintype {x // x ∈ U ∧ f x = b} := hfinX.fintype
    have hm1 (x : {x // x ∈ U ∧ f x = b}) : localMultiplicity S T f x = 1 := by
      apply localMultiplicity_eq_one_of_not_ramified hf hnc
      apply hR x (hUR x.property.1)
      intro hxa
      apply hba
      rw [← x.property.2, hxa]
    rw [localFiberSum, finsum_eq_sum_of_fintype]
    simp only [hm1, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact (Nat.card_eq_fintype_card.symm.trans hcardX)

/-- Conservation of total local multiplicity, also across branch values. -/
theorem fiberMultiplicitySum_isLocallyConstant :
    Specs.D12Complex.Ch20.FiniteDegree.fiberMultiplicitySum_isLocallyConstant_type := by
  intro X Y _ _ _ S T f hf hnc
  classical
  let := S.hausdorff
  let := T.hausdorff
  have hcont := holomorphicMap_continuous S T f hf
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro b
  let A := {a // f a = b}
  have hfin := compact_holomorphicMap_finite_fibers S T f hf hnc b
  letI : Fintype A := hfin.fintype
  obtain ⟨O, hO, hDisj⟩ := hfin.t2_separation
  choose U hoU haU hUO V hoV hbV hsum using
    fun a : A => exists_constant_local_fiberSum hf hnc a (O a) (hO a).2
      (hO a).1
  let W := ⋃ a : A, U a
  have hoW : IsOpen W := isOpen_iUnion hoU
  have hAW : {a | f a = b} ⊆ W := fun a ha => mem_iUnion.mpr ⟨⟨a, ha⟩, haU ⟨a, ha⟩⟩
  have hclosed : IsClosed (f '' Wᶜ) := hcont.isClosedMap _ hoW.isClosed_compl
  have hbW : b ∈ (f '' Wᶜ)ᶜ := by
    rintro ⟨x, hx, hxb⟩
    exact hx (hAW hxb)
  let N := (f '' Wᶜ)ᶜ ∩ ⋂ a : A, V a
  have hoN : IsOpen N := hclosed.isOpen_compl.inter (isOpen_iInter_of_finite hoV)
  have hbN : b ∈ N := ⟨hbW, mem_iInter.mpr fun a => by simpa only [a.property] using hbV a⟩
  refine ⟨N, hoN, hbN, ?_⟩
  intro c hc
  let F : A → Set X := fun a => {x | x ∈ U a ∧ f x = c}
  have hFF : Pairwise (fun a a' => Disjoint (F a) (F a')) := by
    intro a a' haa'
    exact ((hDisj a.property a'.property (fun hh => haa' (Subtype.ext hh))).mono
      (hUO a) (hUO a')).mono
      (fun _ hx => hx.1) (fun _ hx => hx.1)
  have hFfin (a : A) : (F a).Finite :=
    (compact_holomorphicMap_finite_fibers S T f hf hnc c).subset (fun _ hx => hx.2)
  have hUnion : ⋃ a : A, F a = {x | f x = c} := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      exact ha.2
    · intro hx
      have hxW : x ∈ W := by
        by_contra hn
        exact hc.1 ⟨x, hn, hx⟩
      obtain ⟨a, ha⟩ := mem_iUnion.mp hxW
      exact mem_iUnion.mpr ⟨a, ha, hx⟩
  change (∑ᶠ x : ({x | f x = c} : Set X), localMultiplicity S T f x.val) =
    ∑ᶠ a : A, localMultiplicity S T f a.val
  rw [finsum_set_coe_eq_finsum_mem (f := localMultiplicity S T f) {x | f x = c},
    ← hUnion, finsum_mem_iUnion hFF hFfin]
  apply finsum_congr
  intro a
  rw [← finsum_set_coe_eq_finsum_mem (f := localMultiplicity S T f) (F a)]
  exact hsum a c (mem_iInter.mp hc.2 a)

/-- The global degree and the precise number of sheets follow from local
conservation, connectedness, and the compact covering theorem above. -/
theorem compact_holomorphicMap_finite_degree :
    Specs.D12Complex.Ch20.FiniteDegree.compact_holomorphicMap_finite_degree_type := by
  intro X Y _ _ _ S T f hf hnc
  let := T.connected
  let b₀ : Y := Classical.choice inferInstance
  have hconst := fiberMultiplicitySum_isLocallyConstant S T f hf hnc
  have hcov := compact_holomorphicMap_coveringOn_regularValues S T f hf hnc
  have hcard (b : Y) (hb : b ∉ branchValueSet S T f) :
      Nat.card {a // f a = b} = fiberMultiplicitySum S T f b₀ :=
    (fiberMultiplicitySum_eq_card_of_not_branch hf hnc hb).symm.trans
      (hconst.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ b) (mem_univ b₀))
  refine ⟨compact_holomorphicMap_surjective S T f hf hnc,
    compact_holomorphicMap_finite_fibers S T f hf hnc,
    compact_holomorphicMap_finite_ramification S T f hf hnc,
    compact_holomorphicMap_finite_branchValues S T f hf hnc,
    fiberMultiplicitySum S T f b₀, fiberMultiplicitySum_pos hf hnc b₀, ?_,
    hcov.isCoveringMap_restrictPreimage, hcard, ?_, ?_⟩
  · intro b
    exact hconst.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ b) (mem_univ b₀)
  · intro a ha
    exact locallyBiholomorphicAt_of_not_branch hf hnc ha
  · intro b
    have heven := hcov b b.property
    letI : DiscreteTopology (f ⁻¹' {b.val}) := heven.1
    have hfin : (f ⁻¹' {b.val}).Finite :=
      compact_holomorphicMap_finite_fibers S T f hf hnc b
    letI : Fintype (f ⁻¹' {b.val}) := hfin.fintype
    have hn : Fintype.card (f ⁻¹' {b.val}) = fiberMultiplicitySum S T f b₀ := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard b b.property
    exact (heven.of_fiber_homeomorph
      (Fintype.equivFinOfCardEq hn).toHomeomorphOfDiscrete).restrictPreimage ((branchValueSet S T f)ᶜ) b.property

end D12Complex.Surfaces

namespace D12Complex.Surfaces.FiniteDegreeDefinitions
abbrev localMultiplicity : Specs.D12Complex.Ch20.FiniteDegree.localMultiplicity_type :=
  @D12Complex.Surfaces.localMultiplicity
abbrev fiberMultiplicitySum : Specs.D12Complex.Ch20.FiniteDegree.fiberMultiplicitySum_type :=
  @D12Complex.Surfaces.fiberMultiplicitySum
end D12Complex.Surfaces.FiniteDegreeDefinitions
