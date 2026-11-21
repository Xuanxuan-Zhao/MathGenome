import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SubgroupCoverConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringCriterion

namespace P202.Topology.SubgroupCoverConstruction

open P202Specs.Topology
open scoped unitInterval
universe u v
noncomputable section

variable {B : Type u} [TopologicalSpace B] {b z w : B}
  (H : Subgroup (Pi1 B b))

/-- Equality in a fiber of the constructed space is precisely the defining
subgroup relation on path classes. -/
theorem mkClass_eq_iff (a c : PathClass b z) :
    SubgroupCover.mkClass H a = SubgroupCover.mkClass H c ↔
      ofClass (a.trans c.symm) ∈ H := by
  constructor
  · intro h
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj h).2)
  · intro h
    exact congrArg (Sigma.mk z) (Quotient.sound h)

theorem quotientEquality : SubgroupCoverExpected.quotientEquality.{u} := by
  intro B _ b z H a c
  exact mkClass_eq_iff H _ _

theorem representatives : SubgroupCoverExpected.representatives.{u} := by
  intro B _ b H q
  rcases q with ⟨z, q⟩
  induction q using Quotient.inductionOn with | _ c =>
    induction c using Path.Homotopic.Quotient.ind with | mk a =>
      exact ⟨a, rfl⟩

@[simp] theorem endpoint_mkClass (a : PathClass b z) :
    SubgroupCover.endpoint H (SubgroupCover.mkClass H a) = z := rfl

@[simp] theorem endpoint_mk (a : SourcePath b z) :
    SubgroupCover.endpoint H (SubgroupCover.mk H a) = z := rfl

@[simp] theorem endpoint_basepoint :
    SubgroupCover.endpoint H (SubgroupCover.basepoint H) = b := rfl

/-- The projection is onto as soon as every point is joined to b. -/
theorem endpoint_surjective [PathConnectedSpace B] :
    Function.Surjective (SubgroupCover.endpoint H) := by
  intro z
  exact ⟨SubgroupCover.mk H (PathConnectedSpace.somePath b z), rfl⟩

/-- Every point in a sheet projects into its base neighborhood. -/
theorem sheet_endpoint_mem (a : PathClass b z) {U : Set B}
    {q : SubgroupCover b H} (hq : q ∈ SubgroupCover.sheet H a U) :
    SubgroupCover.endpoint H q ∈ U := by
  obtain ⟨η, hη, _⟩ := hq
  change q.1 ∈ U
  simpa only [Path.target] using hη 1

/-- The center belongs to its sheet, without any local hypotheses. -/
theorem center_mem_sheet (a : PathClass b z) {U : Set B} (hz : z ∈ U) :
    SubgroupCover.mkClass H a ∈ SubgroupCover.sheet H a U := by
  refine ⟨Path.refl z, fun _ => hz, ?_⟩
  exact congrArg (SubgroupCover.mkClass H) (Path.Homotopic.Quotient.trans_refl a)

/-- Extension along one path preserves the subgroup relation in both directions. -/
theorem extension_eq_iff (a c : PathClass b z) (d : PathClass z w) :
    SubgroupCover.mkClass H (a.trans d) = SubgroupCover.mkClass H (c.trans d) ↔
      SubgroupCover.mkClass H a = SubgroupCover.mkClass H c := by
  rw [mkClass_eq_iff, mkClass_eq_iff]
  have hreverse : (c.trans d).symm = d.symm.trans c.symm := by
    induction c using Path.Homotopic.Quotient.ind with | mk c =>
      induction d using Path.Homotopic.Quotient.ind with | mk d =>
        exact congrArg Path.Homotopic.Quotient.mk (Path.trans_symm c d)
  rw [hreverse]
  simp only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc a d d.symm,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

/-- Equal subgroup classes have exactly the same extension sheet. -/
theorem sheet_eq_of_mkClass_eq (a c : PathClass b z) (U : Set B)
    (h : SubgroupCover.mkClass H a = SubgroupCover.mkClass H c) :
    SubgroupCover.sheet H a U = SubgroupCover.sheet H c U := by
  ext q
  constructor
  · rintro ⟨η, hη, hq⟩
    exact ⟨η, hη, ((extension_eq_iff H a c _).mpr h).symm.trans hq⟩
  · rintro ⟨η, hη, hq⟩
    exact ⟨η, hη, ((extension_eq_iff H a c _).mpr h).trans hq⟩

/-- Every declared sheet is open in the topology generated from sheets. -/
theorem sheet_isOpen (a : PathClass b z) {U : Set B}
    (hU : CoverNeighborhood U) (hz : z ∈ U) :
    IsOpen (SubgroupCover.sheet H a U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨z, a, U, hU, hz, rfl⟩

/-- Concatenating paths inside a set stays inside it. -/
theorem trans_mem {x y z : B} {U : Set B} (a : SourcePath x y)
    (c : SourcePath y z) (ha : ∀ t, a t ∈ U) (hc : ∀ t, c t ∈ U) :
    ∀ t, (a.trans c) t ∈ U := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range, Set.union_subset_iff]
  exact ⟨Set.range_subset_iff.mpr ha, Set.range_subset_iff.mpr hc⟩

/-- Moving the basepoint inside a path connected neighborhood transfers the
ambient null-homotopy condition to every point of the neighborhood. -/
theorem neighborhoodBasis : SubgroupCoverExpected.neighborhoodBasis.{u} := by
  intro B _ _ hsemi x V hV hxV
  obtain ⟨W, hW, hxW, hnull⟩ := hsemi x
  obtain ⟨U, ⟨hU, hxU, hpc⟩, hsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp ((hV.inter hW).mem_nhds ⟨hxV, hxW⟩)
  refine ⟨U, hxU, fun z hz => (hsub hz).1, hU, hpc, ?_⟩
  intro z hz a ha
  obtain ⟨d, hd⟩ := hpc.joinedIn x hxU z hz
  have hloop : loopClass ((d.trans a).trans d.symm) = 1 :=
    hnull _ (fun t => (hsub (trans_mem (d.trans a) d.symm
      (trans_mem d a hd ha) (fun s => hd (unitInterval.symm s)) t)).2)
  have heq : changeBasepoint d (loopClass a) = 1 := by
    apply pathClass_injective
    rw [basepointFormula, pathClass_loopClass, pathClass_one]
    exact congrArg pathClass hloop
  apply (changeBasepoint d).injective
  simpa only [map_one] using heq

/-- Shrinking the base neighborhood shrinks its endpoint-extension sheet. -/
theorem sheet_mono (a : PathClass b z) {U V : Set B} (hUV : U ⊆ V) :
    SubgroupCover.sheet H a U ⊆ SubgroupCover.sheet H a V := by
  rintro q ⟨η, hη, hq⟩
  exact ⟨η, fun t => hUV (hη t), hq⟩

/-- Re-centering a sheet at any of its points gives the same sheet. -/
theorem sheet_recenter (a : PathClass b z) (c : PathClass b w) {U : Set B}
    (hc : SubgroupCover.mkClass H c ∈ SubgroupCover.sheet H a U) :
    SubgroupCover.sheet H c U = SubgroupCover.sheet H a U := by
  obtain ⟨η, hη, heq⟩ := hc
  rw [← sheet_eq_of_mkClass_eq H _ c U heq]
  ext q
  constructor
  · rintro ⟨μ, hμ, hq⟩
    refine ⟨η.trans μ, trans_mem η μ hη hμ, ?_⟩
    change SubgroupCover.mkClass H (a.trans
      ((Path.Homotopic.Quotient.mk η).trans (Path.Homotopic.Quotient.mk μ))) = q
    rw [← Path.Homotopic.Quotient.trans_assoc]
    exact hq
  · rintro ⟨μ, hμ, hq⟩
    refine ⟨η.symm.trans μ, trans_mem η.symm μ
      (fun t => hη (unitInterval.symm t)) hμ, ?_⟩
    change SubgroupCover.mkClass H ((a.trans (Path.Homotopic.Quotient.mk η)).trans
      ((Path.Homotopic.Quotient.mk η).symm.trans (Path.Homotopic.Quotient.mk μ))) = q
    rw [Path.Homotopic.Quotient.trans_assoc, class_trans_symm_cancel]
    exact hq

theorem sheetBasis : SubgroupCoverExpected.sheetBasis.{u} := by
  intro B _ _ hsemi b H
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨z, a, U, hU, hz, rfl⟩ _ ⟨w, c, V, hV, hw, rfl⟩ q ⟨hqU, hqV⟩
    obtain ⟨d, hd⟩ := representatives B b H q
    obtain ⟨W, hqW, hsub, hW⟩ := neighborhoodBasis B hsemi q.1 (U ∩ V)
      (hU.1.inter hV.1) ⟨sheet_endpoint_mem H a hqU, sheet_endpoint_mem H c hqV⟩
    refine ⟨SubgroupCover.sheet H (.mk d) W, ⟨q.1, .mk d, W, hW, hqW, rfl⟩, ?_, ?_⟩
    · exact Eq.mp (congrArg (fun r => r ∈ SubgroupCover.sheet H (.mk d) W) hd)
        (center_mem_sheet H _ hqW)
    · intro r hr
      constructor
      · have h := sheet_recenter H a (.mk d) (U := U) (Eq.mpr (congrArg (fun r => r ∈ SubgroupCover.sheet H a U) hd) hqU)
        rw [← h]
        exact sheet_mono H _ (fun x hx => (hsub hx).1) hr
      · have h := sheet_recenter H c (.mk d) (U := V) (Eq.mpr (congrArg (fun r => r ∈ SubgroupCover.sheet H c V) hd) hqV)
        rw [← h]
        exact sheet_mono H _ (fun x hx => (hsub hx).2) hr
  · apply Set.eq_univ_of_forall
    intro q
    obtain ⟨a, ha⟩ := representatives B b H q
    obtain ⟨U, hqU, _, hU⟩ := neighborhoodBasis B hsemi q.1 Set.univ isOpen_univ
      (Set.mem_univ _)
    refine ⟨SubgroupCover.sheet H (.mk a) U, ⟨q.1, .mk a, U, hU, hqU, rfl⟩, ?_⟩
    exact Eq.mp (congrArg (fun r => r ∈ SubgroupCover.sheet H (.mk a) U) ha)
      (center_mem_sheet H _ hqU)

/-- The endpoint map is continuous for the constructed sheet topology. -/
theorem endpoint_continuous [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) : Continuous (SubgroupCover.endpoint H) := by
  apply continuous_def.mpr
  intro V hV
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨a, ha⟩ := representatives B b H q
  obtain ⟨U, hqU, hsub, hU⟩ := neighborhoodBasis B hsemi q.1 V hV hq
  apply Filter.mem_of_superset ((sheet_isOpen H (.mk a) hU hqU).mem_nhds ?_)
  · intro r hr
    exact hsub (sheet_endpoint_mem H _ hr)
  · exact Eq.mp (congrArg (fun r => r ∈ SubgroupCover.sheet H (.mk a) U) ha)
      (center_mem_sheet H _ hqU)

/-- The endpoint projection is bijective on every eligible sheet. -/
theorem sheet_bijOn (a : PathClass b z) {U : Set B} (hU : CoverNeighborhood U)
    (hz : z ∈ U) : Set.BijOn (SubgroupCover.endpoint H) (SubgroupCover.sheet H a U) U := by
  refine ⟨fun q hq => sheet_endpoint_mem H a hq, ?_, ?_⟩
  · intro q hq r hr heq
    rcases q with ⟨x, q⟩
    rcases r with ⟨y, r⟩
    change x = y at heq
    subst y
    obtain ⟨η, hη, hq⟩ := hq
    obtain ⟨μ, hμ, hr⟩ := hr
    have hnull := hU.2.2 z hz (η.trans μ.symm)
      (trans_mem η μ.symm hη (fun t => hμ (unitInterval.symm t)))
    have hdiff : (Path.Homotopic.Quotient.mk η).trans
        (Path.Homotopic.Quotient.mk μ).symm = Path.Homotopic.Quotient.refl z :=
      congrArg pathClass hnull
    have hημ : Path.Homotopic.Quotient.mk η = Path.Homotopic.Quotient.mk μ := by
      calc
        _ = ((Path.Homotopic.Quotient.mk η).trans
            (Path.Homotopic.Quotient.mk μ).symm).trans (Path.Homotopic.Quotient.mk μ) := by
          simp only [Path.Homotopic.Quotient.trans_assoc,
            Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
        _ = _ := by rw [hdiff, Path.Homotopic.Quotient.refl_trans]
    exact hq.symm.trans ((congrArg (fun d => SubgroupCover.mkClass H (a.trans d)) hημ).trans hr)
  · intro x hx
    obtain ⟨η, hη⟩ := hU.2.1.joinedIn z hz x hx
    exact ⟨SubgroupCover.mkClass H (a.trans (.mk η)), ⟨η, hη, rfl⟩, rfl⟩

theorem endpoint_image_sheet (a : PathClass b z) {U : Set B}
    (hU : CoverNeighborhood U) (hz : z ∈ U) :
    SubgroupCover.endpoint H '' SubgroupCover.sheet H a U = U :=
  (sheet_bijOn H a hU hz).image_eq

/-- Openness is proved from the actual basis, rather than assumed as part of
an abstract covering certificate. -/
theorem endpoint_isOpenMap [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) : IsOpenMap (SubgroupCover.endpoint H) := by
  apply (sheetBasis B hsemi b H).isOpenMap_iff.mpr
  rintro _ ⟨z, a, U, hU, hz, rfl⟩
  rw [endpoint_image_sheet H a hU hz]
  exact hU.1

theorem sheetHomeomorph : SubgroupCoverExpected.sheetHomeomorph.{u} := by
  intro B _ _ hsemi b z H a U hU hz
  let f : SubgroupCover.sheet H a U → U :=
    Subtype.map (SubgroupCover.endpoint H) (fun _ hq => sheet_endpoint_mem H a hq)
  have hbij : Function.Bijective f := (sheet_bijOn H a hU hz).bijective
  have hcont : Continuous f := (endpoint_continuous H hsemi).subtype_map _
  have hopen : IsOpenMap f := (endpoint_isOpenMap H hsemi).subtype_map
    (sheet_isOpen H a hU hz) _
  exact ⟨IsHomeomorph.homeomorph f ⟨hcont, hopen, hbij⟩, fun _ => rfl⟩

/-- An open set on which the endpoint map is bijective gives a genuine open
partial homeomorphism, with forward map exactly the endpoint projection. -/
def coveringSheetOfBijOn [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) (s : Set (SubgroupCover b H))
    {U : Set B} (hs : IsOpen s) (hbij : Set.BijOn (SubgroupCover.endpoint H) s U) :
    CoveringSheet (SubgroupCover.endpoint H) U := by
  letI : Nonempty (SubgroupCover b H) := ⟨SubgroupCover.basepoint H⟩
  exact {
    chart := OpenPartialHomeomorph.ofContinuousOpen
      (hbij.toPartialEquiv (SubgroupCover.endpoint H) s U)
      (endpoint_continuous H hsemi).continuousOn (endpoint_isOpenMap H hsemi) hs
    projection := rfl
    target_eq := rfl }

/-- Distinct endpoint-extension sheets over the same neighborhood are disjoint. -/
theorem sheets_disjoint_or_eq (a : PathClass b z) (c : PathClass b w) (U : Set B) :
    Disjoint (SubgroupCover.sheet H a U) (SubgroupCover.sheet H c U) ∨
      SubgroupCover.sheet H a U = SubgroupCover.sheet H c U := by
  by_cases hd : Disjoint (SubgroupCover.sheet H a U) (SubgroupCover.sheet H c U)
  · exact Or.inl hd
  · right
    obtain ⟨q, hqa, hqc⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨d, hd⟩ := representatives B b H q
    exact (sheet_recenter H a (.mk d)
      (Eq.mpr (congrArg (fun r => r ∈ SubgroupCover.sheet H a U) hd) hqa)).symm.trans
      (sheet_recenter H c (.mk d)
      (Eq.mpr (congrArg (fun r => r ∈ SubgroupCover.sheet H c U) hd) hqc))

/-- The sheets, as distinct subsets of the total space, give the disjoint
open-sheet decomposition required by the paper's definition of a covering. -/
theorem evenlyCovered [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) {U : Set B} (hU : CoverNeighborhood U) :
    EvenlyCovered (SubgroupCover.endpoint H) U := by
  classical
  let SheetIndex := {s : Set (SubgroupCover b H) //
    ∃ (z : B) (a : PathClass b z), z ∈ U ∧ s = SubgroupCover.sheet H a U}
  have hopen (i : SheetIndex) : IsOpen i.val := by
    obtain ⟨z, a, hz, heq⟩ := i.property
    rw [heq]
    exact sheet_isOpen H a hU hz
  have hbij (i : SheetIndex) : Set.BijOn (SubgroupCover.endpoint H) i.val U := by
    obtain ⟨z, a, hz, heq⟩ := i.property
    rw [heq]
    exact sheet_bijOn H a hU hz
  let f : SheetIndex → CoveringSheet (SubgroupCover.endpoint H) U :=
    fun i => coveringSheetOfBijOn H hsemi i.val (hopen i) (hbij i)
  refine ⟨hU.1, Set.range f, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    change Disjoint i.val j.val
    obtain ⟨z, a, hz, heq⟩ := i.property
    obtain ⟨w, c, hw, heq'⟩ := j.property
    rcases sheets_disjoint_or_eq H a c U with hd | he
    · rwa [heq, heq']
    · have hij : i = j := Subtype.ext (heq.trans (he.trans heq'.symm))
      exact (hne (congrArg f hij)).elim
  · ext q
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hqi⟩
      exact (hbij i).mapsTo hqi
    · intro hq
      obtain ⟨a, ha⟩ := representatives B b H q
      let i : SheetIndex := ⟨SubgroupCover.sheet H (.mk a) U, q.1, .mk a, hq, rfl⟩
      refine ⟨f i, ⟨i, rfl⟩, ?_⟩
      change q ∈ SubgroupCover.sheet H (.mk a) U
      exact Eq.mp (congrArg (fun r => r ∈ SubgroupCover.sheet H (.mk a) U) ha)
        (center_mem_sheet H _ hq)

theorem covering : SubgroupCoverExpected.covering.{u} := by
  intro B _ _ _ hsemi b H
  refine ⟨endpoint_surjective H, ?_⟩
  intro x
  obtain ⟨U, hxU, _, hU⟩ := neighborhoodBasis B hsemi x Set.univ isOpen_univ (Set.mem_univ _)
  exact ⟨U, hxU, evenlyCovered H hsemi hU⟩

/-- Pointwise equal paths, with possibly differently presented terminal
points, represent the same point of the constructed total space. -/
theorem mk_eq_of_pointwise {z w : B} (a : SourcePath b z) (c : SourcePath b w)
    (h : ∀ t, a t = c t) : SubgroupCover.mk H a = SubgroupCover.mk H c := by
  have hzw : z = w := a.target.symm.trans ((h 1).trans c.target)
  subst w
  have hac : a = c := Path.ext (funext h)
  exact congrArg (SubgroupCover.mk H) hac

/-- Prefixes and intervening subpaths compose in the endpoint-fixed groupoid. -/
theorem initialSegment_trans_subpath_class {z : B} (a : SourcePath b z)
    (s t : unitInterval) :
    (Path.Homotopic.Quotient.mk (SubgroupCover.initialSegment a s)).trans
      (Path.Homotopic.Quotient.mk (a.subpath s t)) =
      Path.Homotopic.Quotient.mk (SubgroupCover.initialSegment a t) := by
  apply Path.Homotopic.Quotient.eq.mpr
  exact ⟨(Path.Homotopy.subpathTransSubpath a 0 s t).pathCast a.source.symm rfl⟩

@[simp] theorem prefixClasses_zero {z : B} (a : SourcePath b z) :
    SubgroupCover.prefixClasses H a 0 = SubgroupCover.basepoint H := by
  apply mk_eq_of_pointwise H _ _
  intro t
  simp [SubgroupCover.initialSegment, Path.subpath_self]

@[simp] theorem prefixClasses_one {z : B} (a : SourcePath b z) :
    SubgroupCover.prefixClasses H a 1 = SubgroupCover.mk H a := by
  apply mk_eq_of_pointwise H _ _
  intro t
  simp [SubgroupCover.initialSegment, Path.subpath_zero_one]

/-- A nearby prefix is obtained by extending the current prefix by a short
subpath inside the given base neighborhood. Compactness of I makes the
containment uniform in the subpath parameter. -/
theorem prefixClasses_continuous [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) {z : B} (a : SourcePath b z) :
    Continuous (SubgroupCover.prefixClasses H a) := by
  rw [(sheetBasis B hsemi b H).continuous_iff]
  rintro _ ⟨w, c, U, hU, hw, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hsu : a s ∈ U := sheet_endpoint_mem H c hs
  have hcont : Continuous (fun p : unitInterval × unitInterval => a.subpath s p.1 p.2) :=
    a.subpath_continuous_family.comp (continuous_const.prodMk
      (continuous_fst.prodMk continuous_snd))
  have hnear : ∀ᶠ t in nhds s, ∀ r : unitInterval, a.subpath s t r ∈ U := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (K := Set.univ) (P := fun t r : unitInterval => a.subpath s t r ∈ U) (x₀ := s) ?_
    · simpa only [Set.mem_univ, forall_const] using h
    · intro r _
      apply hcont.continuousAt.preimage_mem_nhds
      simpa only [Path.subpath_self, Path.refl_apply] using hU.1.mem_nhds hsu
  apply hnear.mono
  intro t ht
  have hmem : SubgroupCover.prefixClasses H a t ∈
      SubgroupCover.sheet H (.mk (SubgroupCover.initialSegment a s)) U := by
    refine ⟨a.subpath s t, ht, ?_⟩
    exact congrArg (SubgroupCover.mkClass H) (initialSegment_trans_subpath_class a s t)
  have hsame := sheet_recenter H c (.mk (SubgroupCover.initialSegment a s)) hs
  exact hsame ▸ hmem

theorem prefixLift : SubgroupCoverExpected.prefixLift.{u} := by
  intro B _ _ hsemi b z H a
  exact ⟨prefixClasses_continuous H hsemi a, prefixClasses_zero H a,
    prefixClasses_one H a, fun _ => rfl⟩

theorem pathConnected : SubgroupCoverExpected.pathConnected.{u} := by
  intro B _ _ _ hsemi b H
  have hjoin (q : SubgroupCover b H) : Joined (SubgroupCover.basepoint H) q := by
    obtain ⟨a, ha⟩ := representatives B b H q
    refine ⟨{
      toFun := SubgroupCover.prefixClasses H a
      continuous_toFun := prefixClasses_continuous H hsemi a
      source' := prefixClasses_zero H a
      target' := (prefixClasses_one H a).trans ha }⟩
  exact { nonempty := ⟨SubgroupCover.basepoint H⟩
          joined := fun q r => (hjoin q).symm.trans (hjoin r) }

/-- Each sheet is path connected, since its endpoint homeomorphism has
path connected target. -/
theorem sheet_isPathConnected [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) (a : PathClass b z) {U : Set B}
    (hU : CoverNeighborhood U) (hz : z ∈ U) :
    IsPathConnected (SubgroupCover.sheet H a U) := by
  obtain ⟨e, _⟩ := sheetHomeomorph B hsemi b z H a U hU hz
  haveI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
  exact isPathConnected_iff_pathConnectedSpace.mpr e.symm.pathConnectedSpace

theorem locallyPathConnected : SubgroupCoverExpected.locallyPathConnected.{u} := by
  intro B _ _ _ hsemi b H
  apply LocallyPathConnectedSpace.of_bases
    (fun q : SubgroupCover b H => (sheetBasis B hsemi b H).nhds_hasBasis (a := q))
  rintro q s ⟨⟨z, a, U, hU, hz, rfl⟩, _⟩
  exact sheet_isPathConnected H hsemi a hU hz

/-- A based loop represents the distinguished point precisely when its
class is in H. This is the algebraic closing condition before using lifting. -/
theorem mk_loop_eq_basepoint (a : SourcePath b b) :
    SubgroupCover.mk H a = SubgroupCover.basepoint H ↔ loopClass a ∈ H := by
  rw [SubgroupCover.basepoint, quotientEquality]
  change ofClass ((Path.Homotopic.Quotient.mk a).trans
    (Path.Homotopic.Quotient.refl b)) ∈ H ↔ loopClass a ∈ H
  rw [Path.Homotopic.Quotient.trans_refl]
  rfl

theorem imageSubgroup : SubgroupCoverExpected.imageSubgroup.{u} := by
  intro B _ _ _ hsemi b H hc
  let p : PointedMap (SubgroupCover b H) B (SubgroupCover.basepoint H) b :=
    ⟨⟨SubgroupCover.endpoint H, hc⟩, rfl⟩
  have hp : Covering p.map := covering B hsemi b H
  apply SetLike.ext
  intro g
  obtain ⟨a, rfl⟩ := loopClass_surjective g
  let L : C(unitInterval, SubgroupCover b H) :=
    ⟨SubgroupCover.prefixClasses H a, prefixClasses_continuous H hsemi a⟩
  have heq := closedLiftCriterion (SubgroupCover b H) B (SubgroupCover.basepoint H) b
    p hp a L (fun _ => rfl) (prefixClasses_zero H a)
  rw [show L 1 = SubgroupCover.mk H a from prefixClasses_one H a] at heq
  exact heq.symm.trans (mk_loop_eq_basepoint H a)

/-- The trivial-subgroup construction has trivial fundamental group at its
specified point, by the proved image identity and covering injectivity. -/
theorem pi1_trivial [PathConnectedSpace B] [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B)
    (g : Pi1 (SubgroupCover b (⊥ : Subgroup (Pi1 B b))) (SubgroupCover.basepoint ⊥)) :
    g = 1 := by
  let p : PointedMap (SubgroupCover b (⊥ : Subgroup (Pi1 B b))) B
      (SubgroupCover.basepoint ⊥) b :=
    ⟨⟨SubgroupCover.endpoint ⊥, endpoint_continuous ⊥ hsemi⟩, rfl⟩
  apply coveringInducedInjective _ _ _ _ p (covering B hsemi b ⊥)
  rw [map_one]
  have hmem : p.induced g ∈ p.induced.range := ⟨g, rfl⟩
  rw [imageSubgroup B hsemi b ⊥ (endpoint_continuous ⊥ hsemi)] at hmem
  exact hmem

theorem simplyConnected : SubgroupCoverExpected.simplyConnected.{u} := by
  intro B _ _ _ hsemi b
  haveI := pathConnected B hsemi b (⊥ : Subgroup (Pi1 B b))
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x γ
  let d := PathConnectedSpace.somePath (SubgroupCover.basepoint (⊥ : Subgroup (Pi1 B b))) x
  have hγ : loopClass γ = 1 := by
    apply (changeBasepoint d).injective
    rw [map_one]
    exact pi1_trivial hsemi _
  exact Path.Homotopic.Quotient.eq.mp (congrArg pathClass hγ)

theorem universalProperty : SubgroupCoverExpected.universalProperty.{u,v} := by
  intro B E _ _ _ _ _ hsemi b e p hp
  let H : Subgroup (Pi1 B b) := ⊥
  haveI := pathConnected B hsemi b H
  haveI := locallyPathConnected B hsemi b H
  let f : PointedMap (SubgroupCover b H) B (SubgroupCover.basepoint H) b :=
    ⟨⟨SubgroupCover.endpoint H, endpoint_continuous H hsemi⟩, rfl⟩
  apply (coveringLiftCriterion E B (SubgroupCover b H) e b (SubgroupCover.basepoint H)
    p hp f).mpr
  rw [imageSubgroup B hsemi b H (endpoint_continuous H hsemi)]
  exact bot_le

end
end P202.Topology.SubgroupCoverConstruction
