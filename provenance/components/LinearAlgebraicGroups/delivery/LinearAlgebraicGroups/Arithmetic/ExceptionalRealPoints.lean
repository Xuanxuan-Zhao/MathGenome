import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints
import LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
import LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterWallGroups
import LinearAlgebraicGroups.Arithmetic.ExceptionalRealCompletionTransport
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
import LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Filter Topology
open scoped unitInterval Matrix.Norms.Operator CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints

open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.ExceptionalCompactInner
open Specs.ExceptionalRealPoints
open Specs.ExceptionalOuterTorus (fixedCompact MaximalFixedTorusExistence OuterInvolutions)
open Specs.GeometricRadicals (IsReductive IsSplitReductive)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.ArchimedeanLieChart
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints cocharacterRadicalPoints)
open Specs.StandardParabolicLevi (IsContractingRadical)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage oppositeCocharacter)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.BorelProper (IsParabolic)
open LinearAlgebraicGroups.Specs (SubgroupSections)
open AdelicGroups (PointsIn asMatrix)

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private rankPositiveOfIsotropic from LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
open private top_of_simple subgroupRealization subgroupPoints subgroupMatrix subgroupDifferential
  expUnit_matrixConjugation matrixConjugation
  from LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
open private centralizes_hasLimit from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private cocharacter_parabolic testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

open private reductive_of_semisimple from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private torus_split_of_algClosed from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

/-- A real fixed point is joined by the compact retraction to the common fixed subgroup. -/
private theorem connected_of_compactRetraction {H : Type*} [Group H] [TopologicalSpace H]
    {ω θ : MulAut H} (r : CompactRetraction ω θ)
    (hJ : ConnectedSpace (fixedCompact ω θ)) :
    ConnectedSpace (fixedSubgroup (θ * ω)) := by
  let J := fixedCompact ω θ
  let F := fixedSubgroup (θ * ω)
  have hJ' : IsConnected (J : Set H) := isConnected_iff_connectedSpace.mpr hJ
  have hJF : (J : Set H) ⊆ F := by
    intro x hx
    obtain ⟨hω, hθ⟩ : ω x = x ∧ θ x = x := hx
    show θ (ω x) = x
    rw [hω, hθ]
  apply isConnected_iff_connectedSpace.mp
  refine ⟨⟨1, F.one_mem⟩, isPreconnected_of_forall 1 ?_⟩
  intro x hx
  let p : unitInterval → H := fun t => r.homotopy (t, x)
  have hp : Continuous p := r.homotopy.continuous.comp (continuous_id.prodMk continuous_const)
  have hpF : Set.range p ⊆ F := by
    rintro _ ⟨t, rfl⟩
    change θ (ω x) = x at hx
    change θ (ω (r.homotopy (t, x))) = r.homotopy (t, x)
    rw [← r.equivariant, hx]
  have hpJ : p 1 ∈ J := by
    have hω : ω (p 1) = p 1 := r.endpoint x
    have hθ : θ (ω (p 1)) = p 1 := hpF ⟨1, rfl⟩
    rw [hω] at hθ
    exact ⟨hω, hθ⟩
  refine ⟨(J : Set H) ∪ Set.range p, Set.union_subset hJF hpF,
    Or.inl J.one_mem, Or.inr ⟨0, r.start x⟩, ?_⟩
  exact hJ'.isPreconnected.union (p 1) hpJ ⟨1, rfl⟩ (isPreconnected_range hp)

/-- Transfer compact fixed-point connectedness to the original real point group. -/
private theorem realPointsConnected_of_compactFixed
    {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {ω θ c : MulAut (AdelicGroups.PointsIn i ℂ)}
    (hc : Continuous c) (hcs : Continuous c.symm)
    (hcomp : ∀ x, c (realConjugation G i x) = θ (ω (c x)))
    (hemb : IsEmbedding (realToComplex G i))
    (hrange : Set.range (realToComplex G i) = {x | realConjugation G i x = x})
    (r : CompactRetraction ω θ) (hJ : ConnectedSpace (fixedCompact ω θ)) :
    ConnectedSpace (AdelicGroups.PointsIn i ℝ) := by
  let e : AdelicGroups.PointsIn i ℂ ≃ₜ AdelicGroups.PointsIn i ℂ :=
    ⟨c.toEquiv, hc, hcs⟩
  have hce : IsEmbedding c := e.isEmbedding
  let f : AdelicGroups.PointsIn i ℝ → fixedSubgroup (θ * ω) := fun x =>
    ⟨c (realToComplex G i x), by
      have hx : realToComplex G i x ∈ {x | realConjugation G i x = x} :=
        hrange ▸ Set.mem_range_self x
      exact (hcomp _).symm.trans (congrArg c hx)⟩
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.of_comp_iff.mp (hce.comp hemb)
  have hsurj : Function.Surjective f := by
    intro y
    let x := c.symm y.val
    have hy : θ (ω y.val) = y.val := y.property
    have hxc : c x = y.val := c.apply_symm_apply _
    have hx : realConjugation G i x = x := c.injective (by rw [hcomp, hxc, hy])
    obtain ⟨z, hz⟩ := hrange.symm ▸ (show x ∈ {x | realConjugation G i x = x} from hx)
    exact ⟨z, Subtype.ext ((congrArg c hz).trans hxc)⟩
  exact (hf.toHomeomorphOfSurjective hsurj).connectedSpace_iff.mpr
    (connected_of_compactRetraction r hJ)


private theorem absoluteDynkin_iff {F : Type u} [Field F] (G : AffineAlgebraicGroup F) :
    IsAbsolutelyAlmostSimple G ↔ Specs.IsAbsolutelyAlmostSimple G := by
  constructor
  · intro h
    exact ⟨h.1, fun ⟨e⟩ => h.2.1 ((Grp.isZero_trivial _).of_iso e),
      fun N hN => (h.2.2 N hN).imp (fun hZ => ⟨hZ.iso (Grp.isZero_trivial _)⟩) id⟩
  · intro h
    exact ⟨h.1, fun hZ => h.2.1 ⟨hZ.iso (Grp.isZero_trivial _)⟩,
      fun N hN => (h.2.2 N hN).imp (fun ⟨e⟩ => (Grp.isZero_trivial _).of_iso e) id⟩

theorem outerCompact : OuterCompactStatement :=
  ⟨ExceptionalFoldedWeyl.foldedRootCalculation, ExceptionalFoldedWeyl.foldedWeylCalculation,
    ExceptionalOuterWallGroups.outerWallCalculation⟩

/-- Apply the polar comparison in both branches after the outer compact computation. -/
private theorem realPointsConnected_of_outerCompact
    (hinner : CompactInnerStatement) (houter : OuterCompactStatement)
    (hmax : MaximalFixedTorusExistence) :
    RealPointsConnected := by
  intro G i hG hsc htype
  have hG' := (absoluteDynkin_iff G).mpr hG
  obtain ⟨ω, θ, c, hω, hθ, hc, hcs, hωalg, hθalg, _, hωinv, hθinv, hcomm,
    hcomp, hemb, hrange, hKcmp, hKconn, ⟨r, _⟩, hinn⟩ :=
    hinner G i hG' hsc htype
  by_cases h : ∃ t, θ = MulAut.conj t
  · exact (hinn h).2.2
  · have hOuter : OuterInvolutions (i := i) ω θ :=
      ⟨hω, hθ, hωalg, hθalg, hωinv, hθinv, hcomm, hKcmp, hKconn, h⟩
    obtain ⟨S, hS⟩ := hmax G i hG' hsc htype ω θ hOuter
    have hJ := (houter.2.2 G i hG' hsc htype ω θ hOuter S hS).1
    exact realPointsConnected_of_compactFixed hc hcs hcomp hemb hrange r hJ

theorem realPointsConnected : RealPointsConnected :=
  realPointsConnected_of_outerCompact ExceptionalCompactInner.compactInner outerCompact
    ExceptionalOuterTorus.maximalFixedTorusExistence

theorem complexCompletionsSplit : ComplexCompletionsSplit.{u} := by
  intro K _ _ G hG _ _ w hw
  let L := w.Completion
  let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  letI : IsAlgClosed L := ⟨fun p => by
    have hp := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id L :=
      RingHom.ext fun x => e.symm_apply_apply x
    rwa [Polynomial.map_map, he, Polynomial.map_id] at hp⟩
  let H := baseChangedAlgebraicGroup L G
  have hr := reductive_of_semisimple G hG.1
  have hH : IsReductive H :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := L) G hr.1 hr.2.1).mpr hr
  letI := hH.2.1
  have hc : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := H.val.X.hom)
  obtain ⟨T, hT, hcl, hmax⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hH.1 hc
  exact ⟨hH, T, torus_split_of_algClosed (closedSubgroupAlgebraicGroup T) hT, hcl, hmax⟩


section ParabolicGeneration

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false

/-- A real closed normal subgroup containing a contracting tangent direction is open. -/
private theorem realNormalSubgroup_open
    (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G) (U : ClosedSubgroup G.val)
    (hv : ∃ v : Lie ℝ G.val, v ∈ lieImage U ∧ v ≠ 0)
    (H : Subgroup (PointsIn i ℝ)) [H.Normal] (hH : IsClosed (H : Set (PointsIn i ℝ)))
    (hU : (subgroupPoints i U).range ≤ H) :
    IsOpen (H : Set (PointsIn i ℝ)) := by
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : Module ℝ (Lie ℝ G.val) := Module.restrictScalars ℝ ℝ (Lie ℝ G.val)
  letI : IsTopologicalGroup (PointsIn i ℝ) :=
    IsInducing.isTopologicalGroup (asMatrix i ℝ) (.induced _)
  let m := asMatrix i ℝ
  have hm := asMatrix_isClosedEmbedding i ℝ
  obtain ⟨d, _, hentry, hamb, _, hderiv⟩ :=
    ArchimedeanLieChart.matrixTangentComparison ℝ G i s
  obtain ⟨chart⟩ := ArchimedeanLieChart.closedSubgroupExponential _
    (H.map m) (hm.isClosedMap _ hH)
  let W := chart.tangent.comap d
  have hstable (g : PointsIn i ℝ) (Y : _) (hY : Y ∈ chart.tangent) :
      conjugate (m g) Y ∈ chart.tangent := by
    apply (chart.mem_tangent _).mpr
    intro t
    obtain ⟨h, hh, he⟩ := (chart.mem_tangent Y).mp hY t
    refine ⟨g * h * g⁻¹, Subgroup.Normal.conj_mem inferInstance h hh g, ?_⟩
    rw [map_mul, map_mul, map_inv, he]
    rw [← expUnit_matrixConjugation]
    exact congrArg expUnit ((matrixConjugation (E := ℝ) (m g)).map_smul t Y)
  have hbracket (x y : Lie ℝ G.val) (hy : y ∈ W) : ⁅x, y⁆ ∈ W := by
    let f (t : ℝ) := conjugate (expUnit (t • d x)) (d y)
    have hmem (t : ℝ) : f t ∈ chart.tangent := by
      obtain ⟨g, hg⟩ := (hamb (d x)).mpr ⟨x, rfl⟩ t
      have he : f t = conjugate (m g) (d y) := by
        change conjugate (expUnit (t • d x)) (d y) = _
        rw [← hg]
      rw [he]
      exact hstable g _ hy
    exact chart.tangent.closed_of_finiteDimensional.mem_of_tendsto
      (hderiv x y).tendsto_slope_zero
      (Eventually.of_forall fun t => chart.tangent.smul_mem _
        (chart.tangent.sub_mem (hmem (0 + t)) (hmem 0)))
  have hne : W ≠ ⊥ := by
    obtain ⟨v, ⟨z, rfl⟩, hv⟩ := hv
    let j := subgroupRealization i U
    obtain ⟨dU, _, hentryU, hlines, _, _⟩ :=
      ArchimedeanLieChart.matrixTangentComparison ℝ (closedSubgroupAlgebraicGroup U) j
        (identityLieStructure (closedSubgroupAlgebraicGroup U))
    have hvW : mapPointKernel U.inclusion z ∈ W := by
      apply (chart.mem_tangent _).mpr
      intro t
      have hmat : dU z = d (mapPointKernel U.inclusion z) := by
        rw [hentryU, hentry]
        exact subgroupDifferential i U z
      obtain ⟨p, hp⟩ := (hlines (dU z)).mpr ⟨z, rfl⟩ t
      have hmem : subgroupPoints i U p ∈ H := hU ⟨p, rfl⟩
      exact ⟨subgroupPoints i U p, hmem, (subgroupMatrix i U p).symm.trans
        (hmat ▸ hp)⟩
    intro he
    exact hv ((Submodule.mem_bot ℝ).mp (he ▸ hvW))
  have hfull : W = ⊤ := top_of_simple
    (absoluteSimpleLocalLie ℝ G hG s) W hne hbracket
  obtain ⟨ambient⟩ := ArchimedeanLieChart.closedSubgroupExponential _ m.range hm.isClosed_range
  let e : PointsIn i ℝ ≃ₜ m.range := hm.isEmbedding.toHomeomorph
  apply H.isOpen_of_mem_nhds (g := (1 : PointsIn i ℝ))
  have h1 : e 1 ∈ ambient.expOpen.target := by
    have hz := ambient.exp_chart 0 ambient.zero_mem
    have heq : ambient.expOpen 0 = e 1 := by
      apply Subtype.ext
      change _ = m 1
      simpa only [map_one, Submodule.coe_zero, ArchimedeanLieChart.expUnit_zero] using hz
    rw [← heq]
    exact ambient.expOpen.map_source ambient.zero_mem
  refine mem_of_superset ((ambient.expOpen.open_target.preimage e.continuous).mem_nhds h1) ?_
  intro x hx
  let y := ambient.expOpen.symm (e x)
  have hy : y.val ∈ d.range :=
    (hamb _).mp ((ambient.mem_tangent _).mp y.property)
  have hyt : y.val ∈ chart.tangent := by
    obtain ⟨v, hv⟩ := hy
    rw [← hv]
    change v ∈ W
    rw [hfull]
    exact Submodule.mem_top
  obtain ⟨g, hg, he⟩ := (chart.mem_tangent _).mp hyt 1
  have hmx : m x = expUnit y.val := by
    have he' := ambient.exp_chart y (ambient.expOpen.map_target hx)
    change (ambient.expOpen (ambient.expOpen.symm (e x))).val = _ at he'
    rw [ambient.expOpen.right_inv hx] at he'
    exact he'
  rw [one_smul, ← hmx] at he
  exact hm.injective he ▸ hg


/-- A central cocharacter has no nonzero tangent in its contracting kernel. -/
private theorem noncentral_of_contracting_tangent {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hv : ∃ v : Lie F G.val, v ∈ lieImage D.contracting ∧ v ≠ 0) :
    IsNoncentral c := by
  classical
  by_contra h
  unfold IsNoncentral at h
  push Not at h
  obtain ⟨v, ⟨z, rfl⟩, hz⟩ := hv
  let R := CommAlgCat.of F (DualNumber F)
  let g : Specs.AdjointRepresentation.GroupPoints G.val R :=
    ((groupPointsFunctor F).map D.contracting.inclusion).app R z.toMul.val
  have hg := (D.contracting_points R g).mpr ⟨z.toMul.val, rfl⟩
  have hc := centralizes_hasLimit c (h _ g)
  letI := G.property.1
  exact hz (Subtype.ext (CocharacterDynamics.limitIsUnique c hc hg))

private theorem contracting_subset_parabolicRadicalPoints {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G) (h : IsReductive G)
    {c : Cocharacter G.val} (D : LimitDecomposition c) :
    ((subgroupPoints i D.contracting).range : Set (PointsIn i F)) ⊆ parabolicRadicalPoints G := by
  rintro _ ⟨p, rfl⟩
  refine ⟨D.parabolic, cocharacter_parabolic h c D, contractingSubgroup D,
    (Relative.SplitContractingRadical.contractingSubgroupIsRadical G h c D).1, p, ?_⟩
  change ((groupPointsFunctor F).map
    (D.contractingToParabolic ≫ D.parabolic.inclusion)).app _ p = _
  rw [D.contracting_in_G]
  rfl

/-- Density from an actual nonzero contracting tangent on a connected real group. -/
private theorem realGeneration_of_connected
    (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G) (hconn : ConnectedSpace (PointsIn i ℝ))
    (hnc : ¬ CompactSpace (PointsIn i ℝ)) :
    (∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      IsNoncentral c ∧ IsParabolic G D.parabolic ∧ IsContractingRadical D ∧
      (∃ v : Lie ℝ G.val, v ∈ lieImage D.contracting ∧ v ≠ 0) ∧
      Dense (Subgroup.normalClosure ((subgroupPoints i D.contracting).range :
        Set (PointsIn i ℝ)) : Set (PointsIn i ℝ))) ∧
    Dense (Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :
      Set (PointsIn i ℝ)) ∧
    Dense (Subgroup.closure (G := PointsIn i ℝ) (cocharacterRadicalPoints G) :
      Set (PointsIn i ℝ)) := by
  letI : IsTopologicalGroup (PointsIn i ℝ) :=
    IsInducing.isTopologicalGroup (asMatrix i ℝ) (.induced _)
  letI := hconn
  have hred := reductive_of_semisimple G hG.1
  have han : ¬ Specs.AnisotropicAdNilpotents.IsAnisotropic G.val :=
    fun h => hnc ((LocalCompactnessCriterion.localFieldCompactness G i hG.1).mpr h)
  obtain ⟨S, _, d, D, hv⟩ := LocalCocharacterEvaluation.isotropicContractingLie
    G hG.1 (rankPositiveOfIsotropic G han)
  let c : Cocharacter G.val := d ≫ S.inclusion
  have hfull (N : Subgroup (PointsIn i ℝ)) [N.Normal]
      (hU : (subgroupPoints i D.contracting).range ≤ N) :
      Dense (N : Set (PointsIn i ℝ)) := by
    let H := N.topologicalClosure
    letI : H.Normal := Subgroup.is_normal_topologicalClosure N
    have hclosed := N.isClosed_topologicalClosure
    have hopen := realNormalSubgroup_open G i hG D.contracting hv H hclosed
      (hU.trans N.le_topologicalClosure)
    apply dense_iff_closure_eq.mpr
    exact (show IsClopen (H : Set (PointsIn i ℝ)) from ⟨hclosed, hopen⟩).eq_univ
      ⟨1, H.one_mem⟩
  refine ⟨⟨c, D, noncentral_of_contracting_tangent D hv, cocharacter_parabolic hred c D,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hred c D, hv,
    hfull _ Subgroup.subset_normalClosure⟩, ?_⟩
  letI := hred.1
  letI := hred.2.1
  letI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨_, E, _⟩ := CocharacterDynamics.cocharacterDynamics G c
  let e : PointsIn i ℝ ≃* (𝟙_ (SchemeOver ℝ) ⟶ G.val.X) := testPointSections G.val
  let U := (subgroupPoints i D.contracting).range
  let V := (subgroupPoints i E.contracting).range
  have hmap (A : ClosedSubgroup G.val) :
      (subgroupPoints i A).range.map e.toMonoidHom = SubgroupSections A (𝟙_ (SchemeOver ℝ)) := by
    ext a
    constructor
    · rintro ⟨b, ⟨p, rfl⟩, rfl⟩
      refine ⟨testPointSections A.group p, ?_⟩
      change ((testPointSections A.group) p) ≫ A.inclusion.hom.hom =
        (testPointSections G.val) (subgroupPoints i A p)
      exact Category.assoc _ _ _
    · rintro ⟨b, rfl⟩
      obtain ⟨p, rfl⟩ := (testPointSections A.group).surjective b
      refine ⟨subgroupPoints i A p, ⟨p, rfl⟩, ?_⟩
      change (testPointSections G.val) (subgroupPoints i A p) =
        ((testPointSections A.group) p) ≫ A.inclusion.hom.hom
      symm
      exact Category.assoc _ _ _
  letI : (U ⊔ V).Normal := by
    apply (MulEquiv.normal_map_iff (f := e)).mp
    rw [Subgroup.map_sup]
    change ((subgroupPoints i D.contracting).range.map e.toMonoidHom ⊔
      (subgroupPoints i E.contracting).range.map e.toMonoidHom).Normal
    rw [hmap, hmap]
    exact RelativeRayGeneration.twoRadicals_normal hred D E
  have hle : U ⊔ V ≤ Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :=
    sup_le
      (fun _ h => Subgroup.subset_closure (contracting_subset_parabolicRadicalPoints i hred D h))
      (fun _ h => Subgroup.subset_closure (contracting_subset_parabolicRadicalPoints i hred E h))
  have hcochar : U ⊔ V ≤ Subgroup.closure (G := PointsIn i ℝ) (cocharacterRadicalPoints G) :=
    sup_le
      (fun _ h => Subgroup.subset_closure ⟨c, D, h⟩)
      (fun _ h => Subgroup.subset_closure ⟨oppositeCocharacter c, E, h⟩)
  exact ⟨(hfull (U ⊔ V) le_sup_left).mono hle, (hfull (U ⊔ V) le_sup_left).mono hcochar⟩

theorem noncompactRealParabolicGeneration : NoncompactRealParabolicGeneration := by
  intro G i hG hsc htype hnc
  obtain ⟨hwitness, hgen, _⟩ :=
    realGeneration_of_connected G i hG (realPointsConnected G i hG hsc htype) hnc
  exact ⟨hwitness, hgen⟩

end ParabolicGeneration

section AdelicApplication

open AdelicGroups (LocalPoints)
open Specs.Arithmetic.ProjectiveRecurrence (localPointSet)
open Specs.ExceptionalAdelicApproximation (numberPlaces CompletionHypotheses)
open Specs.ExceptionalRealCompletionTransport (realTest completionTestMap)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)

attribute [local instance] Specs.ExceptionalAdelicApproximation.numberCompletionField
  Specs.ExceptionalAdelicApproximation.numberCompletionTopology
  Specs.ExceptionalAdelicApproximation.numberCompletionAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem realExceptionalType {H : AffineAlgebraicGroup ℝ}
    (h : HasAbsoluteExceptionalType H) : HasExceptionalType H := by
  obtain ⟨t, ht, P, hP, A, hA⟩ := h
  refine ⟨P, hP, A, ?_⟩
  rcases ht with rfl | rfl | rfl
  · exact Or.inl hA
  · exact Or.inr (Or.inl hA)
  · exact Or.inr (Or.inr hA)

/-- Transport connectedness and density of the contracting radicals to the real completion. -/
private theorem realCompletionProperties {K : Type u} [Field K] [NumberField K]
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (htype : HasAbsoluteExceptionalType G) (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
    let D := numberPlaces K
    ConnectedSpace (LocalPoints D i (.inr w)) ∧
      (¬ CompactSpace (LocalPoints D i (.inr w)) →
        Dense (Subgroup.closure (localPointSet D i (.inr w) (cocharacterRadicalPoints
          (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
            Set (LocalPoints D i (.inr w)))) := by
  let D := numberPlaces K
  have hAlgebra : AdelicGroups.completionAlgebra D (.inr w) =
      NumberField.InfinitePlace.Completion.instAlgebra w K :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  obtain ⟨t, ht, htype⟩ := htype
  have htransport := ExceptionalRealCompletionTransport.realCompletionTransport G i
    ((absoluteDynkin_iff G).mpr hG) hsc t ht htype w hw
  dsimp only at htransport
  rw [← hAlgebra] at htransport
  obtain ⟨H, j, compare, q, _, hH, hscH, htypeH, _, hpoints, _, hrad⟩ := htransport
  let qv : PointsIn j ℝ ≃ₜ* LocalPoints D i (.inr w) := q
  have hH' := (absoluteDynkin_iff H).mp hH
  have hconn := realPointsConnected H j hH' hscH (realExceptionalType ⟨t, ht, htypeH⟩)
  refine ⟨qv.toHomeomorph.connectedSpace_iff.mp hconn, ?_⟩
  intro hnoncompact
  have hnoncompactH : ¬ CompactSpace (PointsIn j ℝ) := by
    intro hcompact
    letI := hcompact
    exact hnoncompact (qv.surjective.compactSpace qv.continuous)
  have hd := (realGeneration_of_connected H j hH' hconn hnoncompactH).2.2
  have hdImage : Dense (qv '' (Subgroup.closure (G := PointsIn j ℝ)
      (cocharacterRadicalPoints H) : Set (PointsIn j ℝ))) :=
    qv.toHomeomorph.isDenseEmbedding.dense_image.mpr hd
  let F := w.Completion
  letI : Algebra K F := AdelicGroups.completionAlgebra D (.inr w)
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let Gv := baseChangedAlgebraicGroup F G
  let b : RationalPoints Gv ≃* LocalPoints D i (.inr w) :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hradicalImage : b.toMonoidHom '' cocharacterRadicalPoints Gv ⊆
      localPointSet D i (.inr w) (cocharacterRadicalPoints Gv) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  apply hdImage.mono
  rintro _ ⟨p, hp, rfl⟩
  let z : RationalPoints Gv :=
    ((groupPointsFunctor F).obj Gv.val).map (completionTestMap e) (compare realTest p)
  have hz : z ∈ Subgroup.closure (cocharacterRadicalPoints Gv) := (hrad p).2.mp hp
  have hb := Subgroup.mem_map_of_mem b.toMonoidHom hz
  rw [MonoidHom.map_closure] at hb
  have hq : qv p = b z := Over.OverMorphism.ext (hpoints p)
  change qv p ∈ Subgroup.closure (localPointSet D i (.inr w) (cocharacterRadicalPoints Gv))
  rw [hq]
  exact Subgroup.closure_mono hradicalImage hb

theorem strongApproximation : StrongApproximationStatement.{u} := by
  intro K _ _ D hD G i hG hsc htype hfinite S hS hnoncompact
  subst D
  have hlocal : CompletionHypotheses G i := by
    refine ⟨hfinite, ?_, ?_, ?_⟩
    · exact complexCompletionsSplit G hG hsc htype
    · intro w hw
      exact (realCompletionProperties G i hG hsc htype w hw).1
    · intro w hw
      exact (realCompletionProperties G i hG hsc htype w hw).2
  by_cases h : Specs.AnisotropicAdNilpotents.IsAnisotropic G.val
  · exact ExceptionalAdelicApproximation.anisotropicStrongApproximation G i hG hsc
      hlocal h S hS hnoncompact
  · exact ExceptionalAdelicApproximation.isotropicStrongApproximation G i hG hsc
      hlocal h S hS hnoncompact

end AdelicApplication

end LinearAlgebraicGroups.Arithmetic.ExceptionalRealPoints
