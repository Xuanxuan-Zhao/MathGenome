import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.FreeProperQuotient
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.FunProp
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SmoothDescent
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SubmersionSections
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.RealProjectiveSpace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.FreeProperSlices

namespace SmoothManifolds.FreeProperQuotient
open FreeProperQuotientData FreeProperSliceData MapClassData Set Topology
universe u v

section Topology
variable {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
  [Group G] [MulAction G M]

omit [TopologicalSpace G] [TopologicalSpace M] in
lemma projection_eq_iff (x y : M) :
    orbitProjection (G := G) x = orbitProjection (G := G) y ↔ ∃ g : G, g • x = y := by
  change Quotient.mk (MulAction.orbitRel G M) x = Quotient.mk (MulAction.orbitRel G M) y ↔ _
  rw [Quotient.eq]
  exact MulAction.mem_orbit_symm.trans MulAction.mem_orbit_iff

/-- Compact inverse images give a closed orbit relation without a sequential
compactness assumption on the group. -/
lemma closed_orbit_relation [T2Space M] [LocallyCompactSpace M]
    (hc : Continuous (fun z : G × M => z.1 • z.2))
    (hp : IsProper (actionTransport (G := G) (M := M))) :
    IsClosed {z : M × M | orbitProjection (G := G) z.1 = orbitProjection (G := G) z.2} := by
  have hf : IsProperMap (actionTransport (G := G) (M := M)) :=
    isProperMap_iff_isCompact_preimage.mpr
      ⟨continuous_snd.prodMk hc, fun K hK => hp K hK⟩
  have heq : {z : M × M | orbitProjection (G := G) z.1 = orbitProjection (G := G) z.2} =
      range (actionTransport (G := G) (M := M)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨g, hg⟩ := (projection_eq_iff z.1 z.2).mp hz
      exact ⟨(g, z.1), Prod.ext rfl hg⟩
    · rintro ⟨⟨g, x⟩, rfl⟩
      exact (projection_eq_iff x (g • x)).mpr ⟨g, rfl⟩
  rw [heq]
  exact hf.isClosed_range

lemma orbit_quotient_topology [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M]
    (hc : Continuous (fun z : G × M => z.1 • z.2))
    (hp : IsProper (actionTransport (G := G) (M := M))) :
    IsOpenQuotientMap (orbitProjection (G := G) (M := M)) ∧
      T2Space (OrbitSpace G M) ∧ SecondCountableTopology (OrbitSpace G M) := by
  let : ContinuousSMul G M := ⟨hc⟩
  have hq : IsOpenQuotientMap (orbitProjection (G := G) (M := M)) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact ⟨hq, (t2Space_iff_of_isOpenQuotientMap hq).mpr (closed_orbit_relation hc hp),
    hq.secondCountableTopology⟩

/-- A global product trivialization identifies the actual open quotient
neighborhood with the slice, retaining its subspace topology. -/
lemma quotient_slice_homeomorph [ContinuousConstSMul G M]
    (s : Set M) (hs : IsOpen (saturation (G := G) s))
    (H : (G × s) ≃ₜ saturation (G := G) s)
    (hH : ∀ z, (H z).val = z.1 • z.2.val) :
    ∃ e : s ≃ₜ (orbitProjection (G := G) '' s),
      ∀ x, (e x).val = orbitProjection (G := G) x.val := by
  classical
  let q : M → OrbitSpace G M := orbitProjection
  let f : s → q '' s := fun x => ⟨q x.val, ⟨x.val, x.property, rfl⟩⟩
  have hq : IsOpenQuotientMap q := MulAction.isOpenQuotientMap_quotientMk
  have hf : Continuous f := (hq.continuous.comp continuous_subtype_val).subtype_mk _
  have hmem : ∀ y : saturation (G := G) s, q y.val ∈ q '' s := by
    rintro ⟨y, g, x, hx, hxy⟩
    exact ⟨x, hx, (projection_eq_iff x y).mpr ⟨g, hxy⟩⟩
  let qs : saturation (G := G) s → q '' s := fun y => ⟨q y.val, hmem y⟩
  have hqs : IsOpenQuotientMap qs := by
    refine ⟨?_, (hq.continuous.comp continuous_subtype_val).subtype_mk _, ?_⟩
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, 1, x, hx, one_smul G x⟩, rfl⟩
    · exact (hq.isOpenMap.comp hs.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict hmem
  have hfactor : f ∘ (Prod.snd : G × s → s) = qs ∘ H := by
    funext z
    apply Subtype.ext
    exact (projection_eq_iff z.2.val (H z).val).mpr ⟨z.1, (hH z).symm⟩
  have hfsnd : IsOpenQuotientMap (f ∘ (Prod.snd : G × s → s)) := by
    rw [hfactor]
    exact hqs.comp ⟨H.surjective, H.continuous, H.isOpenMap⟩
  have hfq : IsOpenQuotientMap f :=
    IsOpenQuotientMap.of_comp continuous_snd (fun x => ⟨(1, x), rfl⟩) hf hfsnd
  have hfinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨g, hg⟩ := (projection_eq_iff x.val y.val).mp (congrArg Subtype.val hxy)
    have h : H (g, x) = H (1, y) := by
      apply Subtype.ext
      rw [hH, hH, one_smul, hg]
    exact congrArg Prod.snd (H.injective h)
  let e : s ≃ q '' s := Equiv.ofBijective f ⟨hfinj, hfq.surjective⟩
  exact ⟨e.toHomeomorphOfContinuousOpen hf hfq.isOpenMap, fun _ => rfl⟩

omit [TopologicalSpace G] in
lemma quotient_slice_open [ContinuousConstSMul G M]
    (s : Set M) (hs : IsOpen (saturation (G := G) s)) :
    IsOpen (orbitProjection (G := G) '' s) := by
  apply (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := M)).isQuotientMap.isOpen_preimage.mp
  have heq : orbitProjection (G := G) ⁻¹' (orbitProjection (G := G) '' s) = saturation (G := G) s := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨g, hg⟩ := (projection_eq_iff x y).mp hxy
      exact ⟨g, x, hx, hg⟩
    · rintro ⟨g, x, hx, hxy⟩
      exact ⟨x, hx, (projection_eq_iff x y).mpr ⟨g, hxy⟩⟩
  change IsOpen (orbitProjection (G := G) ⁻¹' (orbitProjection (G := G) '' s))
  rw [heq]
  exact hs

end Topology

/-- The orbit space is Hausdorff and second countable with its quotient topology. -/
theorem quotient_topology :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.quotient_topologyType.{u,v} := by
  intro G M _ _ _ _ _ _ _ hc hp
  exact orbit_quotient_topology hc hp

/-- For a discrete group, the small-transporter conclusion with W={1}
gives precisely the disjoint-neighborhood criterion for a quotient covering. -/
theorem discrete_covering :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.discrete_coveringType.{u,v} := by
  intro G M _ _ _ _ _ _ _ hc hfree hp
  let : ContinuousSMul G M := ⟨hc⟩
  have hcover : IsQuotientCoveringMap (orbitProjection (G := G) (M := M)) G := {
    toIsQuotientMap := MulAction.isOpenQuotientMap_quotientMk.isQuotientMap
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := Quotient.eq
    disjoint := by
      intro p
      obtain ⟨U, hU, hpU, htrans⟩ := FreeProperSlices.small_transporters hc hfree hp p {1} (isOpen_discrete _) rfl
      refine ⟨U, hU.mem_nhds hpU, ?_⟩
      rintro g ⟨y, ⟨x, hx, rfl⟩, hy⟩
      exact htrans g x (g • x) hx hy rfl }
  exact hcover.isCoveringMap

/-- Globalize the given local action product and pass to the quotient. -/
theorem local_quotient_chart :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.local_quotient_chartType.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ hc hfree hp p W s₁ hW h1 hps h hsource ha
  obtain ⟨U, hU, hpU, hpsU, hsat, ⟨H, hH⟩, hunique⟩ :=
    FreeProperSlices.topological_trivialization hc hfree hp p W s₁ hW h1 hps h hsource ha
  obtain ⟨e, he⟩ := quotient_slice_homeomorph (s₁ ∩ U) hsat H hH
  exact ⟨U, hU, hpU, hpsU, quotient_slice_open (s₁ ∩ U) hsat, ⟨e, he⟩, hunique⟩

section Interior
open ModelData AtlasData MapData BoundaryData FiniteRegularityData Filter
open private eventually_ambient_of_model from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary

/-- A surjective differential cannot send an interior point to a boundary
point: the last target coordinate would have a local minimum and zero derivative. -/
lemma submersion_maps_interior {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (p : M) (hp : p ∈ manifoldInterior S)
    (hsub : IsSubmersionAt S T f p) : f p ∈ manifoldInterior T := by
  obtain ⟨e, he, hpe, hpint⟩ := hp
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  have hf1 := manifoldContDiff_of_le ⊤ 1 S.smoothStructure.val T.smoothStructure.val
    f (by simp) hf
  have hsurj := (MapClasses.chart_invariants S T f hf1 p e d he hd hpe hpd).2.2.mp hsub
  obtain ⟨F, hF, heF⟩ := FiniteRegularity.chartDerivative_exists ⊤ (by simp)
    e d f p ((hf p).2 e he d hd hpe hpd)
  have hFx : F (e p).val = (d (f p)).val := heF.eq_of_nhds
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [ContinuousAt, e.left_inv hpe] using e.symm.continuousAt (e.map_source hpe)
  have hm : ∀ᶠ z : ModelSpace m a in 𝓝 (e p), F z.val ∈ modelSet n b := by
    filter_upwards [heF.comp_tendsto ht, e.open_target.mem_nhds (e.map_source hpe)] with z hzF hz
    change F (e (e.symm z)).val = (d (f (e.symm z))).val at hzF
    rw [e.right_inv hz] at hzF
    rw [hzF]
    exact (d (f (e.symm z))).property
  have hm' := eventually_ambient_of_model (e p) hpint
    (P := fun z : Euclidean m => F z ∈ modelSet n b) hm
  have htarget : (d (f p)).val ∈ interior (modelSet n b) := by
    by_contra hface
    have hyface := (mem_modelFace_iff_not_mem_interior (d (f p))).mpr hface
    cases b with
    | euclidean => exact hyface
    | halfSpace =>
      cases n with
      | zero => exact hyface
      | succ n =>
        change (d (f p)).val (Fin.last n) = 0 at hyface
        have hmin : IsLocalMin (fun z => F z (Fin.last n)) (e p).val := by
          filter_upwards [hm'] with z hz
          change F (e p).val (Fin.last n) ≤ F z (Fin.last n)
          rw [hFx, hyface]
          exact hz
        have hz := hmin.hasFDerivAt_eq_zero
          ((ContinuousLinearMap.proj (Fin.last n) : Euclidean (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp
            (e p).val hF)
        obtain ⟨v, hv⟩ := hsurj (fun _ => 1)
        have hh := DFunLike.congr_fun hz v
        change (chartDerivative e d f p v) (Fin.last n) = 0 at hh
        rw [hv] at hh
        exact one_ne_zero hh
  exact ⟨d, hd, hpd, htarget⟩

lemma boundary_empty_of_surjective_submersion {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hsurj : Function.Surjective q) (hS : intrinsicBoundary S = ∅)
    (hq : IsSmoothMap S T q) (hsub : IsSubmersion S T q) : intrinsicBoundary T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : x ∈ manifoldInterior S := by
    rw [← compl_intrinsicBoundary S, hS]
    simp
  have hqx := submersion_maps_interior S T q hq x hx (hsub x)
  rw [← compl_intrinsicBoundary T] at hqx
  exact hqx hy

end Interior

section SmoothStructure
open ModelData AtlasData MapData BoundaryData SmoothDescentData
variable {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]

/-- Convert the upstream section-through-a-point theorem to the open-subspace
section interface used by smooth descent. -/
lemma smooth_local_sections_of_submersion
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hsurj : Function.Surjective q) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (hq : IsSmoothMap S T q)
    (hsub : IsSubmersion S T q) : HasSmoothLocalSections S T q := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hU, hx, s, hs, hqs, _⟩ :=
    SubmersionSections.local_section S T q hS hT hq hsub x
  refine ⟨U, hU, hx, (fun z => s z.val), ?_, ?_⟩
  · exact (manifoldContDiff_restrict_open ⊤ T.smoothStructure.val S.smoothStructure.val
      s U hU).mp hs
  · exact fun z => hqs z.val z.property

lemma smooth_map_test_of_sections
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hq : IsSmoothMap S T q) (hsec : HasSmoothLocalSections S T q) :
    SmoothMapTest.{u,v} S T q := by
  intro k c P _ R h
  constructor
  · intro hh
    exact manifoldContDiff_comp ⊤ S.smoothStructure.val T.smoothStructure.val
      R.smoothStructure.val T.smoothStructure.property.1.1 q h hq hh
  · exact SmoothDescent.smooth_of_comp S T R q h hsec

/-- Smooth identity maps in both directions identify the maximal atlases,
without assuming the desired uniqueness as part of the quotient data. -/
lemma smoothStructure_eq_of_identity
    (S T : SmoothManifold n b N) (hST : IsSmoothMap S T id)
    (hTS : IsSmoothMap T S id) : S.smoothStructure = T.smoothStructure := by
  have hsub : ∀ (S T : SmoothManifold n b N), IsSmoothMap S T id →
      IsSmoothMap T S id → S.smoothStructure.val ⊆ T.smoothStructure.val := by
    intro S T hST hTS e he
    have hmax : maximalExtension ⊤ T.smoothStructure.val = T.smoothStructure.val :=
      T.smoothStructure.property.2 _
        (maximalExtension_isContDiffAtlas T.smoothStructure.property.1)
        (subset_maximalExtension T.smoothStructure.property.1)
    rw [← hmax]
    intro d hd
    exact contDiffCompatible_of_germs
      (fun x hx hd' => (hST x).2 e he d hd hx hd')
      (fun x hx he' => (hTS x).2 d hd e he hx he')
  exact Subtype.ext (Subset.antisymm (hsub S T hST hTS) (hsub T S hTS hST))

lemma smooth_identities_of_sections
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (R : SmoothManifold k c N) (q : M → N)
    (hT : IsSmoothMap S T q) (hR : IsSmoothMap S R q)
    (hsT : HasSmoothLocalSections S T q) (hsR : HasSmoothLocalSections S R q) :
    IsSmoothMap T R id ∧ IsSmoothMap R T id := by
  exact ⟨SmoothDescent.smooth_of_comp S T R q id hsT hR,
    SmoothDescent.smooth_of_comp S R T q id hsR hT⟩

/-- This proves the uniqueness step whenever the competing structures have
actual local sections; a later construction must supply those sections. -/
lemma smoothStructure_eq_of_sections
    (S : SmoothManifold m a M) (T R : SmoothManifold n b N) (q : M → N)
    (hT : IsSmoothMap S T q) (hR : IsSmoothMap S R q)
    (hsT : HasSmoothLocalSections S T q) (hsR : HasSmoothLocalSections S R q) :
    T.smoothStructure = R.smoothStructure := by
  obtain ⟨hTR, hRT⟩ := smooth_identities_of_sections S T R q hT hR hsT hsR
  exact smoothStructure_eq_of_identity T R hTR hRT

/-- Uniqueness for all competing structures follows from the submersion
hypothesis alone: their boundarylessness and their local sections are derived. -/
lemma unique_submersion_structure
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hsurj : Function.Surjective q) (hS : intrinsicBoundary S = ∅)
    (hT : IsSmoothMap S T q) (hsT : HasSmoothLocalSections S T q) :
    UniqueSubmersionStructure S T q := by
  have hcompare : ∀ {k : ℕ} {c : ModelKind} (R : SmoothManifold k c N),
      IsSmoothMap S R q → IsSubmersion S R q →
        IsSmoothMap T R id ∧ IsSmoothMap R T id := by
    intro k c R hR hsubR
    have hbR := boundary_empty_of_surjective_submersion S R q hsurj hS hR hsubR
    have hsR := smooth_local_sections_of_submersion S R q hsurj hS hbR hR hsubR
    exact smooth_identities_of_sections S T R q hT hR hsT hsR
  refine ⟨hcompare, ?_⟩
  intro R hR hsubR
  have hh := hcompare R hR hsubR
  exact smoothStructure_eq_of_identity R T hh.2 hh.1

end SmoothStructure

/-- The topological conclusion specialized to the exact Lie-action input
interface. Smoothness supplies continuity on the ordinary product topology. -/
lemma lie_action_quotient_topology {d n : ℕ} {a b : ModelKind}
    {G M : Type u} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (h : SmoothLieAction A B)
    (hp : IsProper (actionTransport (G := G) (M := M))) :
    IsOpenQuotientMap (orbitProjection (G := G) (M := M)) ∧
      T2Space (OrbitSpace G M) ∧ SecondCountableTopology (OrbitSpace G M) := by
  let : T2Space M := B.topologicalManifold.hausdorff
  let : SecondCountableTopology M := B.topologicalManifold.secondCountable
  let : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace B.topologicalManifold
  exact orbit_quotient_topology
    (continuous_iff_continuousAt.mpr (fun z => (h.smooth_action z).1)) hp

section ProductMaps
open ModelData AtlasData MapData ProductData Filter

open private product_projections_smooth from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

lemma boundarylessProduct_projections_smooth {m n : ℕ} {a b : ModelKind}
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold m a X) (T : SmoothManifold n b Y)
    (P : FreeProperSliceData.BoundarylessProduct S T) :
    IsSmoothMap P.manifold S Prod.fst ∧ IsSmoothMap P.manifold T Prod.snd := by
  obtain ⟨hf, hg⟩ := product_projections_smooth P.left P.right P.coordinates P.manifold P.atlas_eq
  exact ⟨manifoldContDiff_comp ⊤ _ _ _ P.left.smoothStructure.property.1.1
    Prod.fst id hf P.left_from,
    manifoldContDiff_comp ⊤ _ _ _ P.right.smoothStructure.property.1.1
    Prod.snd id hg P.right_from⟩
end ProductMaps

section Covering
open ModelData AtlasData MapData BoundaryData Filter

/-- Factoring a smooth map through an open target preserves smoothness. -/
lemma smooth_codRestrict {m n : ℕ} {a b : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart m a X)) (B : Set (ModelChart n b Y))
    (U : Set Y) (hU : IsOpen U) (f : X → U)
    (hf : ManifoldSmooth A B (fun x => (f x).val)) :
    ManifoldSmooth A (openSubsetAtlas B U hU) f := by
  intro x
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (hf x).1, ?_⟩
  rintro e he _ ⟨hne, d, hd, rfl⟩ hx hfx
  exact (hf x).2 e he d hd hx (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfx)

/-- An inverse on an open sheet is smooth when the projection is a smooth
submersion. Local sections through the inverse point identify its germ. -/
lemma diffeomorph_of_submersion_sheet {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hS : intrinsicBoundary S = ∅) (hT : intrinsicBoundary T = ∅)
    (hq : IsSmoothMap S T q) (hsub : IsSubmersion S T q)
    (V : Set M) (U : Set N) (hV : IsOpen V) (hU : IsOpen U)
    (e : V ≃ₜ U) (he : ∀ x, (e x).val = q x.val) :
    ∃ d : Diffeomorph (openSubsetAtlas S.smoothStructure.val V hV)
        (openSubsetAtlas T.smoothStructure.val U hU),
      ∀ x, (d.toEquiv x).val = q x.val := by
  have hforward : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val V hV)
      T.smoothStructure.val (fun x : V => q x.val) :=
    (manifoldContDiff_restrict_open ⊤ S.smoothStructure.val T.smoothStructure.val q V hV).mp
      (fun x _ => hq x)
  have hf := smooth_codRestrict _ _ U hU e (by
    simpa only [he] using hforward)
  have hg : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val U hU)
      S.smoothStructure.val (fun y : U => (e.symm y).val) := by
    intro y
    let x := e.symm y
    obtain ⟨W, hW, hxW, s, hs, hqs, hsx⟩ :=
      SubmersionSections.local_section S T q hS hT hq hsub x.val
    have hqy : q x.val = y.val := by
      rw [← he x]
      exact congrArg Subtype.val (e.apply_symm_apply y)
    have hyW : y.val ∈ W := hqy ▸ hxW
    have hsy : s y.val = x.val := by rwa [hqy] at hsx
    have hsv : ∀ᶠ z in 𝓝 y.val, s z ∈ V :=
      (hs y.val hyW).1.preimage_mem_nhds (by rw [hsy]; exact hV.mem_nhds x.property)
    have hlocal : (fun z : U => s z.val) =ᶠ[𝓝 y]
        (fun z : U => (e.symm z).val) := by
      filter_upwards [continuousAt_subtype_val.eventually hsv,
        continuousAt_subtype_val.eventually (hW.mem_nhds hyW)] with z hzV hzW
      have hh : e ⟨s z.val, hzV⟩ = z := by
        apply Subtype.ext
        exact (he _).trans (hqs _ hzW)
      exact congrArg Subtype.val ((e.injective (hh.trans (e.apply_symm_apply z).symm)))
    -- Only the germ at y is needed; s is smooth on its own section neighborhood.
    have hsat : ManifoldSmoothAt (openSubsetAtlas T.smoothStructure.val U hU)
        S.smoothStructure.val (fun z : U => s z.val) y := by
      refine ⟨(hs y.val hyW).1.comp continuousAt_subtype_val, ?_⟩
      rintro _ ⟨hne, c, hc, rfl⟩ d hd hyc hys
      exact LocalCoordinateExtension.precomp
        ((hs y.val hyW).2 c hc d hd (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hyc) hys) continuousAt_subtype_val rfl
    exact manifoldContDiffAt_congr hsat hlocal
  exact ⟨⟨e.toEquiv, hf, smooth_codRestrict _ _ V hV e.symm hg⟩, he⟩

/-- A topological covering which is a smooth submersion is a smooth covering,
with sheets indexed by the actual fiber as in the specification. -/
lemma smooth_covering_of_submersion {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hS : intrinsicBoundary S = ∅) (hT : intrinsicBoundary T = ∅)
    (hq : IsSmoothMap S T q) (hsub : IsSubmersion S T q)
    (hcover : IsCoveringMap q) : IsSmoothCovering S T q := by
  classical
  intro y
  obtain ⟨hdisc, U, hyU, hU, hpre, H, hH⟩ := hcover y
  letI : DiscreteTopology (q ⁻¹' {y}) := hdisc
  let V : (q ⁻¹' {y}) → Set M := fun i =>
    Subtype.val '' (H ⁻¹' (univ ×ˢ {i}))
  have hV : ∀ i, IsOpen (V i) := fun i =>
    hpre.isOpenMap_subtype_val _
      (((isOpen_univ.prod (isOpen_discrete {i}))).preimage H.continuous)
  have hmem (i : q ⁻¹' {y}) (x : V i) : q x.val ∈ U := by
    obtain ⟨z, _, hz⟩ := x.property
    exact hz ▸ z.property
  have hlabel (i : q ⁻¹' {y}) (x : V i) : (H ⟨x.val, hmem i x⟩).2 = i := by
    obtain ⟨z, hz, heq⟩ := x.property
    have hz' : z = ⟨x.val, hmem i x⟩ := Subtype.ext heq
    rw [← hz']
    exact hz.2
  have hback (i : q ⁻¹' {y}) (z : U) : (H.symm (z, i)).val ∈ V i := by
    refine ⟨H.symm (z, i), ?_, rfl⟩
    change H (H.symm (z, i)) ∈ univ ×ˢ {i}
    simp
  have hproj (i : q ⁻¹' {y}) (z : U) : q (H.symm (z, i)).val = z.val := by
    rw [← hH]
    exact congrArg (fun w : U × (q ⁻¹' {y}) => w.1.val) (H.apply_symm_apply (z, i))
  let e (i : q ⁻¹' {y}) : V i ≃ₜ U := {
    toFun := fun x => ⟨q x.val, hmem i x⟩
    invFun := fun z => ⟨(H.symm (z, i)).val, hback i z⟩
    left_inv := by
      intro x
      apply Subtype.ext
      have heq : (⟨q x.val, hmem i x⟩, i) = H ⟨x.val, hmem i x⟩ := by
        apply Prod.ext
        · exact Subtype.ext (hH ⟨x.val, hmem i x⟩).symm
        · exact (hlabel i x).symm
      change (H.symm _).val = x.val
      rw [heq, H.symm_apply_apply]
    right_inv := by
      intro z
      exact Subtype.ext (hproj i z)
    continuous_toFun := ((hcover.continuous).comp continuous_subtype_val).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _ }
  refine ⟨U, hU, hyU, V, hV, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x hi hj
    have hh := (hlabel i ⟨x, hi⟩).symm.trans (hlabel j ⟨x, hj⟩)
    exact hij hh
  · ext x
    constructor
    · intro hx
      apply mem_iUnion.mpr
      exact ⟨(H ⟨x, hx⟩).2, ⟨⟨x, hx⟩, ⟨mem_univ _, rfl⟩, rfl⟩⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hmem i ⟨x, hi⟩
  · intro i
    exact diffeomorph_of_submersion_sheet S T q hS hT hq hsub
      (V i) U (hV i) hU (e i) (fun _ => rfl)

end Covering

section Construction
open ModelData AtlasData MapData BoundaryData FiniteRegularityData Filter

/-- A smooth local right inverse through x splits the full differential at x. -/
lemma submersionAt_of_local_right_inverse {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N)
    (hq : IsSmoothMap S T q) (x : M) (s : N → M)
    (hs : ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val s (q x))
    (hsx : s (q x) = x) (hqs : (q ∘ s) =ᶠ[𝓝 (q x)] id) :
    IsSubmersionAt S T q x := by
  obtain ⟨e, he, hxe⟩ := S.smoothStructure.property.1.1 x
  obtain ⟨d, hd, hqd⟩ := T.smoothStructure.property.1.1 (q x)
  apply (MapClasses.chart_invariants S T q
    (manifoldContDiff_of_le ⊤ 1 _ _ q (by simp) hq) x e d he hd hxe hqd).2.2.mpr
  have hse : s (q x) ∈ e.source := by simpa only [hsx] using hxe
  have hqse : q (s (q x)) ∈ d.source := by simpa only [hsx] using hqd
  have hcomp := FiniteRegularity.chartDerivative_comp ⊤ (by simp) d e d s q (q x)
    hqd hs.1 (hs.2 d hd e he hqd hse) ((hq (s (q x))).2 e he d hd hse hqse)
  have hid : chartDerivative d d (q ∘ s) (q x) = ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply FiniteRegularity.coordinateDerivative_eq d _ (q x) hqd
    exact ⟨id, hasFDerivAt_id _, hqs.symm.fun_comp (fun z => (d z).val)⟩
  rw [hid, hsx] at hcomp
  intro v
  refine ⟨chartDerivative d e s (q x) v, ?_⟩
  exact (DFunLike.congr_fun hcomp v).symm

/-- The canonical Euclidean atlas, explicitly retaining its identity chart. -/
noncomputable def euclideanIdentityChart (n : ℕ) : ModelChart n .euclidean (Euclidean n) :=
  (SphereTorus.euclideanModelHomeomorph n).toOpenPartialHomeomorph

lemma euclideanIdentityAtlas (n : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) {euclideanIdentityChart n} := by
  refine ⟨fun x => ⟨euclideanIdentityChart n, rfl, mem_univ _⟩, ?_⟩
  intro c hc d hd
  rcases mem_singleton_iff.mp hc with rfl
  rcases mem_singleton_iff.mp hd with rfl
  apply contDiffCompatible_of_germs <;> intro x _ _ <;>
    exact LocalCoordinateExtension.self ⊤ (fun y => (euclideanIdentityChart n y).val) x

noncomputable def euclideanManifold (n : ℕ) : SmoothManifold n .euclidean (Euclidean n) :=
  ⟨⟨inferInstance, inferInstance, _, (euclideanIdentityAtlas n).1⟩,
    ⟨_, maximalExtension_isMaximal (euclideanIdentityAtlas n)⟩⟩

lemma euclideanManifold_identity (n : ℕ) : HasEuclideanIdentityChart n (euclideanManifold n) :=
  ⟨euclideanIdentityChart n, subset_maximalExtension (euclideanIdentityAtlas n) rfl,
    rfl, rfl, fun _ => rfl⟩

lemma smooth_euclidean_map {m n : ℕ} (f : Euclidean m → Euclidean n)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsSmoothMap (euclideanManifold m) (euclideanManifold n) f := by
  apply (manifoldContDiff_maximalExtension_iff ⊤ _ _
    (euclideanIdentityAtlas m) (euclideanIdentityAtlas n) f).mpr
  intro x
  refine ⟨hf.continuous.continuousAt, ?_⟩
  rintro c rfl d rfl _ _
  exact ⟨univ, isOpen_univ, mem_univ _, f, hf.contDiffOn, Eventually.of_forall (fun _ => rfl)⟩

/-- Transport the given maximal smooth structure along a genuine homeomorphism. -/
noncomputable def transportedManifold {n : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n a X) (h : X ≃ₜ Y) : SmoothManifold n a Y := by
  letI := S.topologicalManifold.hausdorff
  letI := S.topologicalManifold.secondCountable
  exact ⟨⟨h.t2Space, h.symm.secondCountableTopology, _,
      (transportAtlas_isContDiffAtlas ⊤ _ h S.smoothStructure.property.1).1⟩,
    ⟨_, maximalExtension_isMaximal
      (transportAtlas_isContDiffAtlas ⊤ _ h S.smoothStructure.property.1)⟩⟩

lemma transportedManifold_maps {n : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n a X) (h : X ≃ₜ Y) :
    IsSmoothMap S (transportedManifold S h) h ∧
    IsSmoothMap (transportedManifold S h) S h.symm := by
  have hmax : maximalExtension ⊤ S.smoothStructure.val = S.smoothStructure.val :=
    S.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (subset_maximalExtension S.smoothStructure.property.1)
  have hh := transportAtlas_maps ⊤ S.smoothStructure.val h S.smoothStructure.property.1
  constructor
  · have hh' := (manifoldContDiff_maximalExtension_iff ⊤ _ _ S.smoothStructure.property.1
      (transportAtlas_isContDiffAtlas ⊤ _ h S.smoothStructure.property.1) h).mpr hh.1
    simpa only [transportedManifold, MapData.IsSmoothMap, MapData.ManifoldSmooth, hmax] using hh'
  · have hh' := (manifoldContDiff_maximalExtension_iff ⊤ _ _
      (transportAtlas_isContDiffAtlas ⊤ _ h S.smoothStructure.property.1)
      S.smoothStructure.property.1 h.symm).mpr hh.2
    simpa only [transportedManifold, MapData.IsSmoothMap, MapData.ManifoldSmooth, hmax] using hh'

/-- Locally identity coordinate expressions give smoothness and a surjective
full differential, also in dimension zero. -/
lemma projection_of_identity_germs {n : ℕ} {N : Type v} [TopologicalSpace N]
    (Q : SmoothManifold n .euclidean N) (q : Euclidean n → N) (hc : Continuous q)
    (hg : ∀ x, ∃ d ∈ Q.smoothStructure.val, q x ∈ d.source ∧
      (fun y => (d (q y)).val) =ᶠ[𝓝 x] id) :
    IsSmoothMap (euclideanManifold n) Q q ∧ IsSubmersion (euclideanManifold n) Q q := by
  let e := euclideanIdentityChart n
  have he : e ∈ (euclideanManifold n).smoothStructure.val :=
    subset_maximalExtension (euclideanIdentityAtlas n) rfl
  have hq : IsSmoothMap (euclideanManifold n) Q q := by
    intro x
    obtain ⟨d, hd, hxd, hcoord⟩ := hg x
    apply (manifoldContDiffAt_iff_oneChart ⊤ _ _
      (euclideanManifold n).smoothStructure.property.1 Q.smoothStructure.property.1 q x).mpr
    refine ⟨hc.continuousAt, e, he, d, hd, mem_univ _, hxd,
      univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    exact hcoord.symm
  refine ⟨hq, ?_⟩
  intro x
  obtain ⟨d, hd, hxd, hcoord⟩ := hg x
  apply (MapClasses.chart_invariants (euclideanManifold n) Q q
    (manifoldContDiff_of_le ⊤ 1 _ _ q (by simp) hq) x e d he hd (mem_univ _) hxd).2.2.mpr
  have hderiv : chartDerivative e d q x = ContinuousLinearMap.id ℝ (Euclidean n) :=
    FiniteRegularity.coordinateDerivative_eq e _ x (mem_univ _) _
      ⟨id, hasFDerivAt_id _, hcoord.symm⟩
  rw [hderiv]
  exact Function.surjective_id

end Construction

section Examples
open ModelData SphereTorusData ProjectiveData

lemma integer_translation_free (n : ℕ) (z : Fin n → ℤ) (x : Euclidean n)
    (h : integerTranslate n z x = x) : z = 0 := by
  funext i
  have hi := congrFun h i
  change x i + (z i : ℝ) = x i at hi
  have hz : (z i : ℝ) = 0 := by linarith
  exact_mod_cast hz

/-- The transporter map is a closed embedding: it is the product of the closed
lattice embedding with an identity, followed by a linear homeomorphism. -/
lemma integer_transport_proper (n : ℕ) : IsProper (integerTransport n) := by
  let h : (Euclidean n × Euclidean n) ≃ₜ (Euclidean n × Euclidean n) := {
    toFun := fun z => (z.2, z.2 + z.1)
    invFun := fun z => (z.2 - z.1, z.1)
    left_inv := by intro z; ext i <;> simp
    right_inv := by intro z; ext i <;> simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hcast : IsClosedEmbedding (fun z : Fin n → ℤ => fun i => (z i : ℝ)) :=
    IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)
  have hemb : IsClosedEmbedding (integerTransport n) :=
    h.isClosedEmbedding.comp (hcast.prodMap IsClosedEmbedding.id)
  exact fun K hK => hemb.isProperMap.isCompact_preimage hK

lemma antipode_ne_self {n : ℕ} (x : Sphere n) : antipode x ≠ x := by
  intro h
  have hz : ∀ i, x.val i = 0 := by
    intro i
    have hi := congrArg (fun y : Sphere n => y.val i) h
    change -x.val i = x.val i at hi
    linarith
  have hsum : squareSum x.val = 0 := by simp [squareSum, hz]
  rw [x.property] at hsum
  norm_num at hsum

/-- Finite-group properness does not require compactness of the space acted on. -/
lemma antipodal_transport_proper (n : ℕ) :
    IsProper (fun z : Bool × Sphere n =>
      (z.2, if z.1 then antipode z.2 else z.2)) := by
  have hc : Continuous (fun z : Bool × Sphere n =>
      (z.2, if z.1 then antipode z.2 else z.2)) := by
    apply continuous_prod_of_discrete_left.mpr
    intro b
    cases b
    · exact continuous_id.prodMk continuous_id
    · exact continuous_id.prodMk ((continuous_subtype_val.neg).subtype_mk _)
  have hp : IsProperMap (fun z : Bool × Sphere n =>
      (z.2, if z.1 then antipode z.2 else z.2)) :=
    isProperMap_of_comp_of_t2 hc continuous_fst isProperMap_snd_of_compactSpace
  exact fun K hK => hp.isCompact_preimage hK

/-- The coordinatewise quotient is a covering, via its discrete lattice kernel. -/
lemma flat_torus_covering (n : ℕ) : IsCoveringMap (quotientProjection n) := by
  let F : Euclidean n →+ FlatTorus n := {
    toFun := quotientProjection n
    map_zero' := by ext i; simp [SphereTorusData.quotientProjection]
    map_add' := by intros; rfl }
  have hker : (F.ker : Set (Euclidean n)) =
      range (fun z : Fin n → ℤ => fun i => (z i : ℝ)) := by
    ext x
    change quotientProjection n x = 0 ↔ _
    rw [← F.map_zero]
    change quotientProjection n x = quotientProjection n 0 ↔ _
    rw [SphereTorus.quotientProjection_fiber]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, funext (fun i => by simpa using (hz i).symm)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, fun _ => by simp⟩
  have hcast : IsClosedEmbedding (fun z : Fin n → ℤ => fun i => (z i : ℝ)) :=
    IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)
  have hdisc : IsDiscrete (F.ker : Set (Euclidean n)) := by
    rw [hker]
    exact hcast.isEmbedding.isInducing.isDiscrete_range
  exact ((SphereTorus.quotientProjection_isOpenQuotientMap n).isQuotientMap.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom (f := F) hdisc).isCoveringMap

/-- The literal lattice quotient inherits the angle atlas through the supplied
homeomorphism; its projection has identity coordinate germs on small boxes. -/
lemma lattice_projection_geometry (n : ℕ)
    (R : SmoothManifold n .euclidean (FlatTorus n))
    (hR : R.smoothStructure.val = maximalExtension ⊤ (angleAtlas n))
    (e : LatticeQuotient n ≃ₜ FlatTorus n)
    (he : ∀ x, e (latticeProjection n x) = quotientProjection n x) :
    IsSmoothMap (euclideanManifold n) (transportedManifold R e.symm) (latticeProjection n) ∧
    IsSubmersion (euclideanManifold n) (transportedManifold R e.symm) (latticeProjection n) := by
  apply projection_of_identity_germs
  · exact continuous_quotient_mk'
  · intro x
    let c := SphereTorus.angleChart x (1 / 8) (by norm_num)
    have hc := SphereTorus.angleChart_spec x (1 / 8) (by norm_num)
    have hcR : c ∈ R.smoothStructure.val := by
      rw [hR]
      exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas n)
        ⟨x, 1 / 8, by norm_num, by norm_num, hc⟩
    let d := e.toOpenPartialHomeomorph.trans c
    have hd : d ∈ (transportedManifold R e.symm).smoothStructure.val :=
      subset_maximalExtension (transportAtlas_isContDiffAtlas ⊤ _ e.symm
        R.smoothStructure.property.1) ⟨c, hcR, rfl⟩
    have hcx : quotientProjection n x ∈ c.source := by
      rw [hc.1]
      exact ⟨x, SphereTorus.mem_angleBox_center x (by norm_num), rfl⟩
    refine ⟨d, hd, ?_, ?_⟩
    · change latticeProjection n x ∈ univ ∩ e ⁻¹' c.source
      exact ⟨mem_univ _, by change e (latticeProjection n x) ∈ c.source; rw [he]; exact hcx⟩
    · filter_upwards [(SphereTorus.isOpen_angleBox x (1 / 8)).mem_nhds
        (SphereTorus.mem_angleBox_center x (by norm_num))] with y hy
      change (c (e (latticeProjection n y))).val = y
      rw [he]
      exact hc.2.2.1 y hy

lemma hemisphere_projection_injective {n : ℕ} (i : Fin (n + 1)) (b : Bool) :
    InjOn (@projectiveProjection n) (hemisphere i b) := by
  intro x hx y hy hxy
  rcases (Projective.projection_fiber x y).mp hxy with h | h
  · exact h
  · have hi := congrArg (fun z : Sphere n => z.val i) h
    change x.val i = -y.val i at hi
    cases b <;> simp only [hemisphere, Bool.false_eq_true, ↓reduceIte, mem_setOf_eq] at hx hy <;>
      linarith

/-- The antipodal projection is a genuine topological covering. -/
lemma projective_covering (n : ℕ) : IsCoveringMap (@projectiveProjection n) := by
  letI : AddAction (ZMod 2) (Sphere n) := {
    vadd := fun b x => if b = 0 then x else antipode x
    zero_vadd := by
      intro x
      change (if (0 : ZMod 2) = 0 then x else antipode x) = x
      simp
    add_vadd := by
      intro b c x
      change (if b + c = 0 then x else antipode x) =
        (if b = 0 then (if c = 0 then x else antipode x)
          else antipode (if c = 0 then x else antipode x))
      fin_cases b <;> fin_cases c <;> first | rfl | exact (antipode_antipode x).symm }
  have hcover : IsAddQuotientCoveringMap (@projectiveProjection n) (ZMod 2) := {
    toIsQuotientMap := (Projective.projection_isOpenQuotientMap n).isQuotientMap
    continuous_const_vadd := by
      intro b
      change Continuous (fun x : Sphere n => if b = 0 then x else antipode x)
      split_ifs
      · exact continuous_id
      · exact Projective.continuous_antipode n
    apply_eq_iff_mem_orbit := by
      intro x y
      rw [Projective.projection_fiber]
      change (x = y ∨ x = antipode y) ↔ ∃ b : ZMod 2, (if b = 0 then y else antipode y) = x
      constructor
      · rintro (h | h)
        · exact ⟨0, by simpa using h.symm⟩
        · exact ⟨1, by simpa using h.symm⟩
      · rintro ⟨b, h⟩
        fin_cases b
        · left; norm_num at h; exact h.symm
        · right; norm_num at h; exact h.symm
    disjoint := by
      intro x
      obtain ⟨i, b, hx⟩ := SphereTorus.hemisphere_cover n x
      refine ⟨hemisphere i b, (SphereTorus.isOpen_hemisphere i b).mem_nhds hx, ?_⟩
      rintro g ⟨y, ⟨z, hz, rfl⟩, hy⟩
      fin_cases g
      · rfl
      · change (if (1 : ZMod 2) = 0 then z else antipode z) ∈ hemisphere i b at hy
        have hz' : projectiveProjection z = projectiveProjection (antipode z) :=
          (Projective.projection_fiber _ _).mpr (Or.inr (antipode_antipode z).symm)
        have heq := hemisphere_projection_injective i b hz (by simpa using hy) hz'
        exact (antipode_ne_self z heq.symm).elim }
  exact hcover.isCoveringMap

open AtlasData MapData Filter

lemma standard_sphere_antipode_smooth (n : ℕ)
    (S : SmoothManifold n .euclidean (Sphere n))
    (hS : S.smoothStructure.val = maximalExtension ⊤ (hemisphereAtlas n)) :
    IsSmoothMap S S antipode := by
  have hsub : hemisphereAtlas n ⊆ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas n)
  intro x
  obtain ⟨i, b, hx⟩ := SphereTorus.hemisphere_cover n x
  let c := SphereTorus.hemisphereChart i b
  let d := SphereTorus.hemisphereChart i (!b)
  have hc := SphereTorus.hemisphereChart_spec i b
  have hd := SphereTorus.hemisphereChart_spec i (!b)
  have hxc : x ∈ c.source := hc.1.symm ▸ hx
  have hxd : antipode x ∈ d.source := by
    rw [hd.1]
    cases b <;> simpa [SphereTorusData.hemisphere, ProjectiveData.antipode] using hx
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ S.smoothStructure.property.1
    S.smoothStructure.property.1 antipode x).mpr
  refine ⟨(Projective.continuous_antipode n).continuousAt,
    c, hsub ⟨i, b, hc⟩, d, hsub ⟨i, !b, hd⟩, hxc, hxd,
    univ, isOpen_univ, mem_univ _, Neg.neg, contDiff_neg.contDiffOn, ?_⟩
  filter_upwards [c.open_source.mem_nhds hxc,
    (Projective.continuous_antipode n).continuousAt.eventually (d.open_source.mem_nhds hxd)]
    with z hzc hzd
  rw [hc.2.2.1 z hzc, hd.2.2.1 (antipode z) hzd]
  rfl

/-- Ratio coordinates of the projection have smooth ambient extensions on
hemisphere charts. No smooth quotient certificate is assumed. -/
lemma standard_projective_projection_smooth (n : ℕ)
    (S : SmoothManifold n .euclidean (Sphere n))
    (Q : SmoothManifold n .euclidean (RealProjectiveSpace n))
    (hS : S.smoothStructure.val = maximalExtension ⊤ (hemisphereAtlas n))
    (hQ : Q.smoothStructure.val = maximalExtension ⊤ (projectiveAtlas n)) :
    IsSmoothMap S Q projectiveProjection := by
  have hSsub : hemisphereAtlas n ⊆ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas n)
  have hQsub : projectiveAtlas n ⊆ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas n)
  intro x
  obtain ⟨i, b, hx⟩ := SphereTorus.hemisphere_cover n x
  let c := SphereTorus.hemisphereChart i b
  let d := Projective.projectiveChart i
  have hc := SphereTorus.hemisphereChart_spec i b
  have hxc : x ∈ c.source := hc.1.symm ▸ hx
  have hxi : x.val i ≠ 0 := by
    cases b
    · exact ne_of_lt hx
    · exact ne_of_gt hx
  have hxd : projectiveProjection x ∈ d.source := (Projective.projection_mem_locus i x).mpr hxi
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ S.smoothStructure.property.1
    Q.smoothStructure.property.1 projectiveProjection x).mpr
  refine ⟨(Projective.projection_isOpenQuotientMap n).continuous.continuousAt,
    c, hSsub ⟨i, b, hc⟩, d, hQsub ⟨i, Projective.projectiveChart_spec i⟩,
    hxc, hxd, {y | squareSum y < 1},
    isOpen_lt (SphereTorus.continuous_squareSum n) continuous_const, ?_,
    (fun y j => insertRoot i b y (i.succAbove j) / insertRoot i b y i), ?_, ?_⟩
  · have h := c.map_source hxc
    rwa [hc.2.1] at h
  · apply contDiffOn_pi.mpr
    intro j
    exact (contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i b) (i.succAbove j)).div
      (contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i b) i) (fun y hy => by
        simp only [SphereTorusData.insertRoot, Fin.insertNth_apply_same]
        change signedRoot b (1 - squareSum y) ≠ 0
        have ht := SphereTorus.signedRoot_sq b (sub_pos.mpr hy).le
        intro hz
        rw [hz, zero_pow (by decide)] at ht
        change squareSum y < 1 at hy
        linarith)
  · filter_upwards [c.open_source.mem_nhds hxc] with z hzc
    have hroot : insertRoot i b (c z).val = z.val := by
      rw [← hc.2.2.2 (c z) (c.map_source hzc), c.left_inv hzc]
    change (fun j => insertRoot i b (c z).val (i.succAbove j) / insertRoot i b (c z).val i) =
      projectiveRatios i (projectiveProjection z)
    rw [hroot]
    rfl

lemma normalizedRepresentative_contDiff (n : ℕ) (i : Fin (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean n => (normalizedRepresentative i y).val) := by
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_apply ℝ (fun _ => ℝ) j).comp (Projective.contDiff_insertOne i)).div
    ((contDiff_const.add (SphereTorus.contDiff_squareSum n)).sqrt (fun y => by
      have := SphereTorus.squareSum_nonneg y
      positivity))
    (fun y => (Projective.sqrt_normalizer_pos y).ne')

/-- The normalized ratio representative is a smooth local section, on every
full projective chart domain. -/
lemma normalized_section_smoothAt (n : ℕ)
    (S : SmoothManifold n .euclidean (Sphere n))
    (Q : SmoothManifold n .euclidean (RealProjectiveSpace n))
    (hS : S.smoothStructure.val = maximalExtension ⊤ (hemisphereAtlas n))
    (hQ : Q.smoothStructure.val = maximalExtension ⊤ (projectiveAtlas n))
    (i : Fin (n + 1)) (p : RealProjectiveSpace n) (hp : p ∈ projectiveLocus i) :
    ManifoldSmoothAt Q.smoothStructure.val S.smoothStructure.val
      (fun y => normalizedRepresentative i (projectiveRatios i y)) p := by
  let f := fun y : RealProjectiveSpace n => normalizedRepresentative i (projectiveRatios i y)
  let c := Projective.projectiveChart i
  have hc : c ∈ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas n)
      ⟨i, Projective.projectiveChart_spec i⟩
  have hfc : ContinuousAt f p :=
    (Projective.continuous_normalizedRepresentative i).continuousAt.comp
      (continuous_subtype_val.continuousAt.comp (c.continuousAt hp))
  obtain ⟨j, b, hfp⟩ := SphereTorus.hemisphere_cover n (f p)
  let d := SphereTorus.hemisphereChart j b
  have hd := SphereTorus.hemisphereChart_spec j b
  have hdS : d ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas n) ⟨j, b, hd⟩
  have hfd : f p ∈ d.source := hd.1.symm ▸ hfp
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ Q.smoothStructure.property.1
    S.smoothStructure.property.1 f p).mpr
  refine ⟨hfc, c, hc, d, hdS, hp, hfd, univ, isOpen_univ, mem_univ _,
    (fun y => omitCoordinate j (normalizedRepresentative i y).val), ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro k
    exact (contDiff_pi.mp (normalizedRepresentative_contDiff n i) (j.succAbove k)).contDiffOn
  · filter_upwards [hfc.eventually (d.open_source.mem_nhds hfd)] with y hy
    exact (hd.2.2.1 (f y) hy).symm

end Examples
/-- The literal integer-translation quotient is the standard smooth torus. -/
theorem integer_translation :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.integer_translationType := by
  intro n
  obtain ⟨R, _hRA, hR⟩ := (SphereTorus.angleManifold n).2.2
  obtain ⟨T, _hTA, hT⟩ := (SphereTorus.torusManifold n).2.2
  obtain ⟨e, he, _⟩ := SphereTorus.latticeAngleHomeomorph n
  let E := euclideanManifold n
  let Q := transportedManifold R e.symm
  obtain ⟨hq, hsub⟩ := lattice_projection_geometry n R hR e he
  have hE : BoundaryData.intrinsicBoundary E = ∅ := intrinsicBoundary_euclidean E
  have hQ : BoundaryData.intrinsicBoundary Q = ∅ := intrinsicBoundary_euclidean Q
  have hfac : e.symm ∘ SphereTorusData.quotientProjection n = SphereTorusData.latticeProjection n := by
    funext x
    change e.symm (SphereTorusData.quotientProjection n x) = _
    rw [← he x, e.symm_apply_apply]
  have hcover : IsCoveringMap (SphereTorusData.latticeProjection n) := by
    rw [← hfac]
    exact (flat_torus_covering n).homeomorph_comp e.symm
  have hsurj : Function.Surjective (SphereTorusData.latticeProjection n) := Quotient.mk_surjective
  have hsec := smooth_local_sections_of_submersion E Q _ hsurj hE hQ hq hsub
  refine ⟨integer_translation_free n, integer_transport_proper n, E, Q, T,
    euclideanManifold_identity n, ?_, hT, hq, hsub,
    smooth_covering_of_submersion E Q _ hE hQ hq hsub hcover,
    unique_submersion_structure E Q _ hsurj hE hq hsec, ?_⟩
  · intro z
    apply smooth_euclidean_map
    unfold FreeProperQuotientData.integerTranslate
    fun_prop
  · obtain ⟨h, hh, hf, hg, _⟩ := SphereTorus.angleProductCompatibility n T R hT hR
    have hmaps := transportedManifold_maps R e.symm
    let d : Diffeomorph Q.smoothStructure.val T.smoothStructure.val := {
      toEquiv := e.toEquiv.trans h.toEquiv
      contDiff_toFun := manifoldContDiff_comp ⊤ Q.smoothStructure.val R.smoothStructure.val
        T.smoothStructure.val R.smoothStructure.property.1.1 e h hmaps.2 hf
      contDiff_invFun := manifoldContDiff_comp ⊤ T.smoothStructure.val R.smoothStructure.val
        Q.smoothStructure.val R.smoothStructure.property.1.1 h.symm e.symm hg hmaps.1 }
    refine ⟨d, ?_⟩
    intro x
    exact (congrArg h (he x)).trans (hh x)

open ModelData AtlasData MapData SphereTorusData ProjectiveData BoundaryData

/-- The standard sphere projection is a submersion, using the normalized
projective representatives or their antipodes as local right inverses. -/
lemma standard_projective_projection_submersion (n : ℕ)
    (S : SmoothManifold n .euclidean (Sphere n))
    (Q : SmoothManifold n .euclidean (RealProjectiveSpace n))
    (hS : S.smoothStructure.val = maximalExtension ⊤ (hemisphereAtlas n))
    (hQ : Q.smoothStructure.val = maximalExtension ⊤ (projectiveAtlas n)) :
    IsSubmersion S Q projectiveProjection := by
  have hq := standard_projective_projection_smooth n S Q hS hQ
  have ha := standard_sphere_antipode_smooth n S hS
  intro x
  obtain ⟨i, hi⟩ := Projective.locus_cover (projectiveProjection x)
  let f : RealProjectiveSpace n → Sphere n :=
    fun y => normalizedRepresentative i (projectiveRatios i y)
  have hf : ManifoldSmoothAt Q.smoothStructure.val S.smoothStructure.val
      f (projectiveProjection x) := normalized_section_smoothAt n S Q hS hQ i _ hi
  have hright : (projectiveProjection ∘ f) =ᶠ[𝓝 (projectiveProjection x)] id := by
    filter_upwards [(Projective.isOpen_locus i).mem_nhds hi] with y hy
    exact Projective.inverse_ratios i y hy
  have hfx : projectiveProjection (f (projectiveProjection x)) = projectiveProjection x :=
    Projective.inverse_ratios i _ hi
  rcases (Projective.projection_fiber _ _).mp hfx with hfx | hfx
  · exact submersionAt_of_local_right_inverse S Q projectiveProjection hq x f hf hfx hright
  · apply submersionAt_of_local_right_inverse S Q projectiveProjection hq x
      (antipode ∘ f)
    · exact manifoldContDiffAt_comp S.smoothStructure.property.1.1 hf (ha _)
    · dsimp only [Function.comp_apply]
      rw [hfx, antipode_antipode]
    · filter_upwards [hright] with y hy
      change projectiveProjection (antipode (f y)) = y
      exact ((Projective.projection_fiber _ _).mpr (Or.inr rfl)).trans hy

/-- The antipodal quotient has the standard projective smooth structure. -/
theorem antipodal_quotient :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.antipodal_quotientType := by
  intro n _hn
  obtain ⟨S, _hSA, hS⟩ := (SphereTorus.sphereManifold n).2.2
  let Q := Projective.projectiveManifold n
  have hQ : Q.smoothStructure.val = maximalExtension ⊤ (projectiveAtlas n) := rfl
  have hq := standard_projective_projection_smooth n S Q hS hQ
  have hsub := standard_projective_projection_submersion n S Q hS hQ
  have hbS : intrinsicBoundary S = ∅ := intrinsicBoundary_euclidean S
  have hbQ : intrinsicBoundary Q = ∅ := intrinsicBoundary_euclidean Q
  have hsurj : Function.Surjective (@projectiveProjection n) := Quotient.mk_surjective
  have hsections := smooth_local_sections_of_submersion S Q projectiveProjection
    hsurj hbS hbQ hq hsub
  exact ⟨fun x => antipode_ne_self x, antipodal_transport_proper n, S, Q,
    hS, standard_sphere_antipode_smooth n S hS, hQ, hbQ, hq, hsub,
    smooth_covering_of_submersion S Q projectiveProjection hbS hbQ hq hsub
      (projective_covering n),
    hsections, unique_submersion_structure S Q projectiveProjection hsurj hbS hq hsections⟩

section QuotientAtlas
open ModelData AtlasData MapData FreeProperSliceData FreeProperQuotientData
  BoundaryData MapClassData Set Filter Topology




local instance euclideanModelSpace_nonempty (k : ℕ) : Nonempty (ModelSpace k .euclidean) :=
  ⟨⟨0, mem_univ _⟩⟩

lemma lift_chart_germ {k : ℕ} {X Y N : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace N]
    (S : SmoothManifold k .euclidean X) (T : SmoothManifold k .euclidean Y)
    (f : X → N) (g : Y → N) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (c : ModelChart k .euclidean X) (d : ModelChart k .euclidean Y)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (x : X) (hxc : x ∈ c.source) (t : X → Y)
    (ht : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val t x)
    (hxd : t x ∈ d.source) (hcomm : (g ∘ t) =ᶠ[𝓝 x] f) :
    ChartContDiffAt ⊤ (c.lift_openEmbedding hf) (d.lift_openEmbedding hg) id (f x) := by
  obtain ⟨U, hU, hxU, F, hF, heq⟩ := ht.2 c hc d hd hxc hxd
  refine ⟨U, hU, ?_, F, hF, ?_⟩
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_apply] using hxU
  · rw [← hf.map_nhds_eq x]
    change ∀ᶠ z in 𝓝 x, _
    filter_upwards [heq, hcomm] with z hz hcommz
    simp only [Function.comp_apply] at hcommz
    simp only [id_eq]
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, ← hcommz,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact hz


lemma liftedAtlas_isContDiffAtlas {k : ℕ} {I : Type v} {X : I → Type u} {N : Type u}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace N]
    (S : ∀ i, SmoothManifold k .euclidean (X i))
    (f : ∀ i, X i → N) (hf : ∀ i, IsOpenEmbedding (f i))
    (hcover : ∀ q : N, ∃ i x, f i x = q)
    (htransition : ∀ i j x y, f i x = f j y →
      ∃ t : X i → X j,
        ManifoldSmoothAt (S i).smoothStructure.val (S j).smoothStructure.val t x ∧
        t x = y ∧ (f j ∘ t) =ᶠ[𝓝 x] (f i)) :
    IsContDiffAtlas ⊤ {c | ∃ i, ∃ e ∈ (S i).smoothStructure.val,
      c = e.lift_openEmbedding (hf i)} := by
  refine ⟨?_, ?_⟩
  · intro q
    obtain ⟨i, x, rfl⟩ := hcover q
    obtain ⟨e, he, hx⟩ := (S i).smoothStructure.property.1.1 x
    exact ⟨_, ⟨i, e, he, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro c ⟨i, e, he, rfl⟩ d ⟨j, e', he', rfl⟩
    apply contDiffCompatible_of_germs
    · intro q hqc hqd
      obtain ⟨x, hx, rfl⟩ := hqc
      obtain ⟨y, hy, hxy⟩ := hqd
      obtain ⟨t, ht, hty, hcomm⟩ := htransition i j x y hxy.symm
      exact lift_chart_germ (S i) (S j) (f i) (f j) (hf i) (hf j)
        e e' he he' x hx t ht (hty.symm ▸ hy) hcomm
    · intro q hqd hqc
      obtain ⟨y, hy, rfl⟩ := hqd
      obtain ⟨x, hx, hxy⟩ := hqc
      obtain ⟨t, ht, htx, hcomm⟩ := htransition j i y x hxy.symm
      exact lift_chart_germ (S j) (S i) (f j) (f i) (hf j) (hf i)
        e' e he' he y hy t ht (htx.symm ▸ hx) hcomm

lemma smooth_lifted_embedding {k : ℕ} {X N : Type u}
    [TopologicalSpace X] [TopologicalSpace N]
    (S : SmoothManifold k .euclidean X) (T : SmoothManifold k .euclidean N)
    (f : X → N) (hf : IsOpenEmbedding f)
    (hcharts : ∀ e ∈ S.smoothStructure.val, e.lift_openEmbedding hf ∈ T.smoothStructure.val) :
    IsSmoothMap S T f := by
  intro x
  obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 x
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ S.smoothStructure.property.1
    T.smoothStructure.property.1 f x).mpr
  refine ⟨hf.continuous.continuousAt, e, he, e.lift_openEmbedding hf, hcharts e he,
    hx, ⟨x, hx, rfl⟩, univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
  exact Eventually.of_forall (fun z => (congrArg Subtype.val
    (OpenPartialHomeomorph.lift_openEmbedding_apply e hf)).symm)


section GlobalSliceMaps
variable {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M) {p : M}

noncomputable def globalSliceProjection (s : GlobalSlice A B p) (x : M) : s.carrier := by
  classical
  exact if h : x ∈ saturation (G := G) s.carrier then
    (s.trivialization.toEquiv.symm ⟨x, h⟩).2 else ⟨p, s.contains⟩

lemma globalSliceProjection_on (s : GlobalSlice A B p)
    (x : saturation (G := G) s.carrier) :
    globalSliceProjection A B s x.val = (s.trivialization.toEquiv.symm x).2 := by
  simp only [globalSliceProjection, dite_eq_left x.property]

lemma globalSliceProjection_smoothOn (s : GlobalSlice A B p) :
    ManifoldSmoothOn B.smoothStructure.val s.slice.smoothStructure.val
      (globalSliceProjection A B s) (saturation (G := G) s.carrier) := by
  have hsnd := (boundarylessProduct_projections_smooth A s.slice s.product).2
  have htrans := manifoldContDiff_comp ⊤ _ _ _ s.product.manifold.smoothStructure.property.1.1
    s.trivialization.toEquiv.symm Prod.snd s.trivialization.contDiff_invFun hsnd
  apply (manifoldContDiff_restrict_open ⊤ B.smoothStructure.val s.slice.smoothStructure.val
    (globalSliceProjection A B s) _ s.saturated_open).mpr
  intro z
  have hsub : openSubsetAtlas B.smoothStructure.val (saturation (G := G) s.carrier)
      s.saturated_open ⊆ s.neighborhood.smoothStructure.val := by
    rw [s.neighborhood_atlas]
    exact subset_maximalExtension (openSubsetAtlas_isContDiffAtlas ⊤ B.smoothStructure.val
      B.smoothStructure.property.1 _ s.saturated_open)
  have heq : (fun x : saturation (G := G) s.carrier => globalSliceProjection A B s x.val) =
      Prod.snd ∘ s.trivialization.toEquiv.symm := by
    funext x
    exact globalSliceProjection_on A B s x
  rw [heq]
  exact ⟨(htrans z).1, fun e he c hc hx hfx =>
    (htrans z).2 e (hsub he) c hc hx hfx⟩

lemma globalSliceProjection_orbit (s : GlobalSlice A B p)
    (x : M) (hx : x ∈ saturation (G := G) s.carrier) :
    orbitProjection (G := G) (globalSliceProjection A B s x).val = orbitProjection (G := G) x := by
  let z := s.trivialization.toEquiv.symm ⟨x, hx⟩
  apply (projection_eq_iff _ _).mpr
  refine ⟨z.1, ?_⟩
  change z.1 • (globalSliceProjection A B s x).val = x
  rw [globalSliceProjection_on A B s ⟨x,hx⟩]
  have h := s.action_eq z
  rw [s.trivialization.toEquiv.apply_symm_apply] at h
  exact h.symm

end GlobalSliceMaps

section GlobalSliceQuotient
variable {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [ContinuousConstSMul G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)

lemma globalSlice_quotient_openEmbedding {p : M} (s : GlobalSlice A B p) :
    IsOpenEmbedding (fun x : s.carrier => orbitProjection (G := G) x.val) := by
  obtain ⟨e, he⟩ := quotient_slice_homeomorph s.carrier s.saturated_open
    s.trivialization.toHomeomorph s.action_eq
  have hcomp := (quotient_slice_open s.carrier s.saturated_open).isOpenEmbedding_subtypeVal.comp
    e.isOpenEmbedding
  have hfun : ((↑) : (orbitProjection (G := G) '' s.carrier) → OrbitSpace G M) ∘ e =
      (fun x : s.carrier => orbitProjection (G := G) x.val) := by
    funext x
    exact he x
  rwa [hfun] at hcomp

lemma globalSlice_quotient_transition {p p' : M}
    (s : GlobalSlice A B p) (t : GlobalSlice A B p')
    (x : s.carrier) (y : t.carrier)
    (hxy : orbitProjection (G := G) x.val = orbitProjection (G := G) y.val) :
    ∃ f : s.carrier → t.carrier,
      ManifoldSmoothAt s.slice.smoothStructure.val t.slice.smoothStructure.val f x ∧
      f x = y ∧
      ((fun z : t.carrier => orbitProjection (G := G) z.val) ∘ f) =ᶠ[𝓝 x]
        (fun z : s.carrier => orbitProjection (G := G) z.val) := by
  have hxt : x.val ∈ saturation (G := G) t.carrier := by
    obtain ⟨g, hg⟩ := (projection_eq_iff y.val x.val).mp hxy.symm
    exact ⟨g, y.val, y.property, hg⟩
  let f : s.carrier → t.carrier := globalSliceProjection A B t ∘ Subtype.val
  have hsm : ManifoldSmoothAt s.slice.smoothStructure.val t.slice.smoothStructure.val f x :=
    manifoldContDiffAt_comp B.smoothStructure.property.1.1 (s.embedding.1 x)
      (globalSliceProjection_smoothOn A B t x.val hxt)
  have hfx : f x = y := by
    apply (globalSlice_quotient_openEmbedding A B t).injective
    exact (globalSliceProjection_orbit A B t x.val hxt).trans hxy
  refine ⟨f, hsm, hfx, ?_⟩
  filter_upwards [(s.embedding.1 x).1.eventually (t.saturated_open.mem_nhds hxt)] with z hz
  exact globalSliceProjection_orbit A B t z.val hz

end GlobalSliceQuotient

lemma smooth_inverse_lifted_embeddingAt {k : ℕ} {X N : Type u}
    [TopologicalSpace X] [TopologicalSpace N] [Nonempty X]
    (S : SmoothManifold k .euclidean X) (T : SmoothManifold k .euclidean N)
    (f : X → N) (hf : IsOpenEmbedding f)
    (hcharts : ∀ e ∈ S.smoothStructure.val, e.lift_openEmbedding hf ∈ T.smoothStructure.val)
    (x : X) :
    ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val
      (hf.toOpenPartialHomeomorph f).symm (f x) := by
  let e := hf.toOpenPartialHomeomorph f
  obtain ⟨c, hc, hx⟩ := S.smoothStructure.property.1.1 x
  have hfex : e.symm (f x) = x := hf.toOpenPartialHomeomorph_left_inv
  have hfxt : f x ∈ e.target := ⟨x, mem_univ _, rfl⟩
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ T.smoothStructure.property.1
    S.smoothStructure.property.1 e.symm (f x)).mpr
  refine ⟨e.symm.continuousAt hfxt, c.lift_openEmbedding hf, hcharts c hc, c, hc,
    ⟨x, hx, rfl⟩, hfex.symm ▸ hx, univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
  filter_upwards [e.open_target.mem_nhds hfxt] with q hq
  change (c.lift_openEmbedding hf q).val = (c (e.symm q)).val
  have hqf : f (e.symm q) = q := e.right_inv hq
  rw [← hqf, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hqf]


lemma quotient_manifold_of_globalSlices {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [ContinuousConstSMul G M] [T2Space (OrbitSpace G M)]
    [SecondCountableTopology (OrbitSpace G M)]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (hs : ∀ p : M, Nonempty (GlobalSlice A B p)) :
    ∃ Q : SmoothManifold (n-d) .euclidean (OrbitSpace G M),
      IsSmoothMap B Q orbitProjection ∧ IsSubmersion B Q orbitProjection := by
  classical
  let s (p : M) : GlobalSlice A B p := Classical.choice (hs p)
  let f (p : M) : (s p).carrier → OrbitSpace G M := fun z => orbitProjection z.val
  have hf (p : M) : IsOpenEmbedding (f p) := globalSlice_quotient_openEmbedding A B (s p)
  let C : Set (ModelChart (n-d) .euclidean (OrbitSpace G M)) :=
    {c | ∃ p, ∃ e ∈ (s p).slice.smoothStructure.val, c = e.lift_openEmbedding (hf p)}
  have hC : IsContDiffAtlas ⊤ C := by
    apply liftedAtlas_isContDiffAtlas (fun p => (s p).slice) f hf
    · intro q
      obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
      exact ⟨p, ⟨p, (s p).contains⟩, rfl⟩
    · intro p p' x y hxy
      exact globalSlice_quotient_transition A B (s p) (s p') x y hxy
  let Q : SmoothManifold (n-d) .euclidean (OrbitSpace G M) :=
    ⟨⟨inferInstance, inferInstance, C, hC.1⟩,
      ⟨maximalExtension ⊤ C, maximalExtension_isMaximal hC⟩⟩
  have hcharts (p : M) (e : ModelChart (n-d) .euclidean (s p).carrier)
      (he : e ∈ (s p).slice.smoothStructure.val) :
      e.lift_openEmbedding (hf p) ∈ Q.smoothStructure.val :=
    subset_maximalExtension hC ⟨p, e, he, rfl⟩
  have hfsmooth (p : M) : IsSmoothMap (s p).slice Q (f p) :=
    smooth_lifted_embedding (s p).slice Q (f p) (hf p) (hcharts p)
  have hpsat (p : M) : p ∈ saturation (G := G) (s p).carrier :=
    ⟨1, p, (s p).contains, one_smul G p⟩
  have hq : IsSmoothMap B Q (orbitProjection (G := G)) := by
    intro p
    have hp := manifoldContDiffAt_comp (s p).slice.smoothStructure.property.1.1
      (globalSliceProjection_smoothOn A B (s p) p (hpsat p))
      (hfsmooth p (globalSliceProjection A B (s p) p))
    apply manifoldContDiffAt_congr hp
    filter_upwards [(s p).saturated_open.mem_nhds (hpsat p)] with z hz
    exact globalSliceProjection_orbit A B (s p) z hz
  refine ⟨Q, hq, ?_⟩
  intro p
  letI : Nonempty (s p).carrier := ⟨⟨p, (s p).contains⟩⟩
  let E := (hf p).toOpenPartialHomeomorph (f p)
  let sectionMap : OrbitSpace G M → M := Subtype.val ∘ E.symm
  have hinv := smooth_inverse_lifted_embeddingAt (s p).slice Q (f p) (hf p)
    (hcharts p) ⟨p, (s p).contains⟩
  have hsectionsmooth : ManifoldSmoothAt Q.smoothStructure.val B.smoothStructure.val
      sectionMap (orbitProjection p) :=
    manifoldContDiffAt_comp (s p).slice.smoothStructure.property.1.1 hinv
      ((s p).embedding.1 _)
  have hthrough : sectionMap (orbitProjection p) = p := by
    change ((E.symm (f p ⟨p, (s p).contains⟩)) : M) = p
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  apply submersionAt_of_local_right_inverse B Q orbitProjection hq p
    sectionMap hsectionsmooth hthrough
  have hpt : orbitProjection p ∈ E.target :=
    ⟨⟨p, (s p).contains⟩, mem_univ _, rfl⟩
  filter_upwards [E.open_target.mem_nhds hpt] with q hqt
  exact E.right_inv hqt


end QuotientAtlas

section QuotientClosure
open ModelData AtlasData MapData BoundaryData FreeProperSliceData FreeProperQuotientData
  MapClassData Set Topology
lemma discrete_covering_of_proper {G : Type u} {M : Type v}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [T2Space M] [LocallyCompactSpace M] [DiscreteTopology G]
    (hc : Continuous (fun z : G × M => z.1 • z.2))
    (hfree : FreeAction G M) (hp : IsProper (actionTransport (G := G) (M := M))) :
    IsCoveringMap (orbitProjection (G := G) (M := M)) := by
  let : ContinuousSMul G M := ⟨hc⟩
  have hcover : IsQuotientCoveringMap (orbitProjection (G := G) (M := M)) G := {
    toIsQuotientMap := MulAction.isOpenQuotientMap_quotientMk.isQuotientMap
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := Quotient.eq
    disjoint := by
      intro p
      obtain ⟨U, hU, hpU, htrans⟩ := FreeProperSlices.small_transporters hc hfree hp p {1}
        (isOpen_discrete _) rfl
      refine ⟨U, hU.mem_nhds hpU, ?_⟩
      rintro g ⟨y, ⟨x, hx, rfl⟩, hy⟩
      exact htrans g x (g • x) hx hy rfl }
  exact hcover.isCoveringMap

/-- Once actual smooth action slices are constructed, all remaining quotient
claims follow for the genuine orbit topology, including all-structure uniqueness. -/
lemma quotient_geometry_of_globalSlices {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (h : SmoothLieAction A B) (hfree : FreeAction G M)
    (hp : IsProper (actionTransport (G := G) (M := M)))
    (hdim : d ≤ n) (hs : ∀ p : M, Nonempty (GlobalSlice A B p)) :
    d ≤ n ∧ IsOpenQuotientMap (orbitProjection (G := G) (M := M)) ∧
    T2Space (OrbitSpace G M) ∧ SecondCountableTopology (OrbitSpace G M) ∧
    ∃ Q : SmoothManifold (n-d) .euclidean (OrbitSpace G M),
      intrinsicBoundary Q = ∅ ∧ IsSmoothMap B Q orbitProjection ∧ IsSubmersion B Q orbitProjection ∧
      SmoothDescentData.HasSmoothLocalSections B Q orbitProjection ∧
      SmoothMapTest.{u,v} B Q orbitProjection ∧ UniqueSubmersionStructure B Q orbitProjection ∧
      (DiscreteTopology G → IsSmoothCovering B Q orbitProjection) := by
  have hc : Continuous (fun z : G × M => z.1 • z.2) :=
    continuous_iff_continuousAt.mpr (fun z => (h.smooth_action z).1)
  let : ContinuousSMul G M := ⟨hc⟩
  let : T2Space M := B.topologicalManifold.hausdorff
  let : LocallyCompactSpace M := SmoothManifolds.TopologicalManifold.locallyCompactSpace B.topologicalManifold
  obtain ⟨hqopen, hT2, hSC⟩ := lie_action_quotient_topology A B h hp
  let : T2Space (OrbitSpace G M) := hT2
  let : SecondCountableTopology (OrbitSpace G M) := hSC
  obtain ⟨Q, hq, hsub⟩ := quotient_manifold_of_globalSlices A B hs
  have hbQ : intrinsicBoundary Q = ∅ := intrinsicBoundary_euclidean Q
  have hsurj : Function.Surjective (orbitProjection (G := G) (M := M)) := Quotient.mk_surjective
  have hsec := smooth_local_sections_of_submersion B Q orbitProjection hsurj
    h.space_boundary hbQ hq hsub
  refine ⟨hdim, hqopen, hT2, hSC, Q, hbQ, hq, hsub, hsec,
    smooth_map_test_of_sections B Q orbitProjection hq hsec,
    unique_submersion_structure B Q orbitProjection hsurj h.space_boundary hq hsec, ?_⟩
  intro hdisc
  let : DiscreteTopology G := hdisc
  exact smooth_covering_of_submersion B Q orbitProjection h.space_boundary hbQ hq hsub
    (discrete_covering_of_proper hc hfree hp)
end QuotientClosure

/-- The smooth orbit manifold, with its universal mapping property, uniqueness
among all submersion structures, and smooth covering conclusion for discrete G. -/
theorem free_proper_quotient :
    Specs.SmoothManifolds.Ch08.FreeProperQuotient.free_proper_quotientType.{u,v} := by
  intro d n a b G M _ _ _ _ _ A B h hfree hp
  obtain ⟨_horbit, hdim, hslices⟩ := FreeProperSlices.free_proper_slices A B h hfree hp
  exact quotient_geometry_of_globalSlices A B h hfree hp hdim hslices

end SmoothManifolds.FreeProperQuotient
