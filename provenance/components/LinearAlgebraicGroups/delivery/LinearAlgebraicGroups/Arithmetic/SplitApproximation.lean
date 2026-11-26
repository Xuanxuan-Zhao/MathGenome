import Specs.LinearAlgebraicGroups.Arithmetic.SplitApproximation
import LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.SplitApproximation

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open AdelicGroups ApproximationOfLocalWords
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (absoluteRoots)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.Pinning (BasedRootDatum PinnedGroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (AdditiveLine IsRootSubgroup rootPoint)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)

open private reductive_of_semisimple rootPoint_id_bijective sameSubgroupIso forget_comp from
  LinearAlgebraicGroups.Classification.CentralIsogenies
open private splitBorelPair simplyConnectedDatum restrictCharacters_injective
  corootDatum_span liftFromCorootDatum realization_corootSpan of_fullCorootLattice
  model_simplyConnected from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private fibrePointsEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private def pointIso {J H : GroupScheme k} (e : J ≅ H) (R : TestAlgebra k) :
    GroupPoints J R ≃* GroupPoints H R :=
  (((groupPointsFunctor k).mapIso e).app R).groupIsoToMulEquiv

private theorem pointIso_apply {J H : GroupScheme k} (e : J ≅ H) (R : TestAlgebra k)
    (p : GroupPoints J R) : pointIso e R p = p ≫ e.hom.hom.hom := rfl

private theorem rootPoint_comp {A : AdditiveLine k} {H J : GroupScheme k}
    (x : A.group ⟶ H) (y : H ⟶ J) (R : TestAlgebra k) (r : R) :
    rootPoint (x ≫ y) R r = rootPoint x R r ≫ y.hom.hom :=
  (Category.assoc _ _ _).symm

/-- The chosen additive coordinates enumerate the same generators as all closed
root subgroups, by scheme-theoretic uniqueness over the ground field. -/
private theorem rootCoordinates_generate {T : ClosedSubgroup G.val}
    (hr : IsReductive G) (hs : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (U : RootSubgroupFamily T)
    {I : Type u} (b : I ≃ Root T) {A : AdditiveLine k}
    (z : ∀ a, A.group ≅ (U (b a)).val.group)
    (h : Subgroup.closure
      {g : GroupPoints G.val (CommAlgCat.of k k) |
        ∃ α ∈ absoluteRoots T, ∃ V : ClosedSubgroup G.val, IsRootSubgroup T V α ∧
          ∃ p : GroupPoints V.group (CommAlgCat.of k k), p ≫ V.inclusion.hom.hom = g} = ⊤) :
    Subgroup.closure
      {g : GroupPoints G.val (CommAlgCat.of k k) |
        ∃ (i : I) (a : k),
          rootPoint ((z i).hom ≫ (U (b i)).val.inclusion) (CommAlgCat.of k k) a = g} = ⊤ := by
  apply top_unique
  rw [← h]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨α, ha, V, hV, p, rfl⟩
  obtain ⟨i, hi⟩ := b.surjective ⟨α, ha⟩
  have hUi : IsRootSubgroup T (U (b i)).val α := hi ▸ (U (b i)).property
  obtain ⟨_, _, W, _, _, _, _, hu⟩ :=
    (RootData.RootGroups.rootSubgroups G hr T hs hm).2 α ha
  obtain ⟨a, ha⟩ := sameSubgroupIso (hu V hV)
  obtain ⟨c, hc⟩ := sameSubgroupIso (hu (U (b i)).val hUi)
  let e := a.symm ≪≫ c ≪≫ (z i).symm
  obtain ⟨t, ht⟩ := (rootPoint_id_bijective A (CommAlgCat.of k k)).surjective
    (p ≫ e.hom.hom.hom)
  apply Subgroup.subset_closure
  refine ⟨i, t, ?_⟩
  change rootPoint (𝟙 A.group) (CommAlgCat.of k k) t ≫
      (z i).hom.hom.hom ≫ (U (b i)).val.inclusion.hom.hom = _
  rw [ht]
  have he : e.hom ≫ (z i).hom ≫ (U (b i)).val.inclusion = V.inclusion := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, hc, ← ha]
  simpa only [forget_comp, Category.assoc] using
    congrArg (fun f : V.group ⟶ G.val => p ≫ f.hom.hom) he

/-- Recover the group from the integral split model of its simply connected datum,
with root coordinates matched over the ground field. -/
private theorem exists_integral_coordinates (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) :
    ∃ (B : BasedRootDatum.{u}) (M : Specs.IntegralSemisimpleModel.Model B)
      (A : AdditiveLine k) (e : (fibre k).obj M.group ≅ G.val)
      (U : B.I → ClosedSubgroup G.val) (z : ∀ a, A.group ≅ (U a).group),
      Submodule.span ℤ (Set.range B.datum.coroot) = ⊤ ∧
      (∀ a, ∃ α ∈ absoluteRoots T, IsRootSubgroup T (U a) α) ∧
      ∀ (a : B.I) (R : TestAlgebra k) (r : R),
        forgetFibrePoint M.group R
          (rootPoint ((z a).hom ≫ (U a).inclusion ≫ e.inv) R r) =
          M.line.point (CommAlgCat.of Specs.IntegralSemisimpleModel.Integers.{u} R) r ≫ (M.root a).hom.hom := by
  let P := splitBorelPair G (reductive_of_semisimple G hG) T hs hm
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hD : corootLattice D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.G hG P.T P.split P.maximal D.datum).mp hsc
  have hfin : Finite (Additive (Specs.CharacterDescent.Cocharacter P.T.group) ⧸ corootLattice D) :=
    (Submodule.finiteQuotient_iff _).mpr (by rw [hD, finrank_top])
  let B := simplyConnectedDatum D.toBased hfin
  have hB : Submodule.span ℤ (Set.range B.datum.coroot) = ⊤ :=
    corootDatum_span D.datum.rootDatum (restrictCharacters_injective D.datum.rootDatum hfin)
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization B
  obtain ⟨A, F, e, _, z, _, _, _, hz⟩ := M.fieldFibre k
  obtain ⟨V, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  let Q : PinnedGroup A := ⟨P, V, pin⟩
  obtain ⟨f, τ, hf, hτ, hfIso, _, _⟩ := liftFromCorootDatum Q D hfin F
  letI : IsIso f := hfIso hD
  obtain ⟨_, _, hb, hroot⟩ := Classification.CentralIsogenies.centralIsogenyComparison
    F.pinned.pair.G P.G F.pinned.pair.reductive P.reductive F.pinned.pair.T P.T
    F.pinned.pair.split F.pinned.pair.maximal P.split P.maximal f τ hf hτ.1 hτ.2.2
  have h (a : B.I) :
      ∃ (β : Root T) (U : ClosedSubgroup G.val) (_ : IsRootSubgroup T U β.val)
        (eU : (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.group ≅ U.group),
          eU.hom ≫ U.inclusion = (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ f := by
    let α := F.datumIso.val.indexEquiv a
    obtain ⟨β, hβ, he⟩ := hb.surjOn α.property
    let b : Root T := ⟨β, hβ⟩
    have he' : (⟨Specs.CentralIsogenies.characterPullback τ β, hb.mapsTo hβ⟩ : Root F.pinned.pair.T) = α :=
      Subtype.ext he
    obtain ⟨eU, heU⟩ := (hroot β hβ (hb.mapsTo hβ)).1 (F.pinned.roots α).val (V b).val
      (he'.symm ▸ (F.pinned.roots α).property) (V b).property
    exact ⟨b, (V b).val, (V b).property, eU, heU⟩
  choose β U hU eU heU using h
  let E := e ≪≫ asIso f
  refine ⟨B, M, A, E, U, fun a => (z a).val ≪≫ eU a, hB,
    fun a => ⟨(β a).val, (β a).property, hU a⟩, ?_⟩
  intro a R r
  have hcomp : ((z a).val ≪≫ eU a).hom ≫ (U a).inclusion ≫ E.inv =
      (z a).val.hom ≫ (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv := by
    simp only [E, Iso.trans_hom, Iso.trans_inv, Category.assoc, ← Category.assoc (eU a).hom,
      heU, Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [hcomp]
  exact hz a R r

/-- Generation in a field fibre transfers to the points of the original group over
that field because each marked root has the same evaluation on the integral model. -/
private theorem integralCoordinates_generate
    {B : BasedRootDatum.{u}} (M : Specs.IntegralSemisimpleModel.Model B)
    (hB : Submodule.span ℤ (Set.range B.datum.coroot) = ⊤)
    (A : AdditiveLine k) (e : (fibre k).obj M.group ≅ G.val)
    (U : B.I → ClosedSubgroup G.val) (z : ∀ a, A.group ≅ (U a).group)
    (hz : ∀ (a : B.I) (R : TestAlgebra k) (r : R),
      forgetFibrePoint M.group R
        (rootPoint ((z a).hom ≫ (U a).inclusion ≫ e.inv) R r) =
        M.line.point (CommAlgCat.of Specs.IntegralSemisimpleModel.Integers.{u} R) r ≫ (M.root a).hom.hom)
    (F : Type u) [Field F] [Algebra k F] :
    Subgroup.closure {g : GroupPoints G.val (CommAlgCat.of k F) |
      ∃ (a : B.I) (r : F), rootPoint ((z a).hom ≫ (U a).inclusion) (CommAlgCat.of k F) r = g} = ⊤ := by
  obtain ⟨A', P, e', _, z', _, _, _, hz'⟩ := M.fieldFibre F
  let J := P.pinned.pair
  have hP : IsSemisimple J.G := of_fullCorootLattice J P.attached (realization_corootSpan P hB)
  have hsc : GeometricallySimplyConnected J.G := model_simplyConnected M hB e'
  let R := CommAlgCat.of k F
  let R' := CommAlgCat.of F F
  let m := (pointIso e'.symm R').trans
    ((fibrePointsEquiv M.group R').trans ((fibrePointsEquiv M.group R).symm.trans (pointIso e R)))
  have hm (a : B.I) (r : F) :
      m (rootPoint ((z' a).val.hom ≫ (P.pinned.roots (P.datumIso.val.indexEquiv a)).val.inclusion) R' r) =
        rootPoint ((z a).hom ≫ (U a).inclusion) R r := by
    let g := rootPoint ((z a).hom ≫ (U a).inclusion ≫ e.inv) R r
    have hpoint : (pointIso e R) g = rootPoint ((z a).hom ≫ (U a).inclusion) R r := by
      dsimp only [g]
      rw [pointIso_apply, ← rootPoint_comp]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hpoint]
    have hsource :
        pointIso e'.symm R'
            (rootPoint ((z' a).val.hom ≫ (P.pinned.roots (P.datumIso.val.indexEquiv a)).val.inclusion) R' r) =
          rootPoint ((z' a).val.hom ≫
            (P.pinned.roots (P.datumIso.val.indexEquiv a)).val.inclusion ≫ e'.inv) R' r := by
      rw [pointIso_apply, ← rootPoint_comp, Category.assoc]
      rfl
    simp only [m, MulEquiv.trans_apply]
    rw [hsource]
    apply congrArg (pointIso e R)
    apply (fibrePointsEquiv M.group R).injective
    exact ((fibrePointsEquiv M.group R).apply_symm_apply _).trans
      ((hz' a R' r).trans (hz a R r).symm)
  let S : Set (GroupPoints J.G.val R') := {g |
    ∃ (a : B.I) (r : F),
      rootPoint ((z' a).val.hom ≫ (P.pinned.roots (P.datumIso.val.indexEquiv a)).val.inclusion) R' r = g}
  have hgen : Subgroup.closure S = ⊤ :=
    rootCoordinates_generate J.reductive J.split J.maximal P.pinned.roots
      P.datumIso.val.indexEquiv (fun a => (z' a).val)
      (SplitLocalGeneration.splitLocalGeneration J.G hP hsc J.T J.split J.maximal)
  apply top_unique
  intro g _
  obtain ⟨p, rfl⟩ := m.surjective g
  have hp : p ∈ Subgroup.closure S := hgen.symm ▸ Subgroup.mem_top p
  refine Subgroup.closure_induction (p := fun g _ => m g ∈ _) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨a, r, rfl⟩
    rw [hm]
    exact Subgroup.subset_closure ⟨a, r, rfl⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem rootGenerationOverExtensions : Specs.SplitApproximation.RootGenerationOverExtensions.{u} := by
  intro k _ G hG hsc T hs hm F _ _
  obtain ⟨B, M, A, e, U, z, hB, hU, hz⟩ := exists_integral_coordinates G hG hsc T hs hm
  apply top_unique
  rw [← integralCoordinates_generate M hB A e U z hz F]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, r, rfl⟩
  obtain ⟨α, hα, ha⟩ := hU a
  exact Subgroup.subset_closure ⟨α, hα, U a, ha, rootPoint (z a).hom _ r, Category.assoc _ _ _⟩

private def polynomialChart {U : GroupScheme k} (A : AdditiveLine k) (z : A.group ≅ U) :
    (testSpec k).obj (op (CommAlgCat.of k (Polynomial k))) ≅ U.X :=
  (Grp.forget (SchemeOver k)).mapIso z

theorem splitStrongApproximation : Specs.SplitApproximation.SplitStrongApproximation.{u, v} := by
  intro K _ G hG hsc T hs hm D i S hS
  obtain ⟨B, M, A, e, U, z, hB, _, hz⟩ := exists_integral_coordinates G hG hsc T hs hm
  have chart (a : B.I) : ParameterSpace K 1 ≅ (U a).group.X :=
    (testSpec K).mapIso (CommAlgCat.isoMk (MvPolynomial.uniqueAlgEquiv K (Fin 1))).symm.op ≪≫
      polynomialChart A (z a)
  apply (subgroupsWithAffineCoordinates D i S hS U chart).2
  intro w
  have gen := integralCoordinates_generate M hB A e U z hz (D.Completion w.1)
  have htop : generatedBySubgroups U D i w.1 = ⊤ := by
    apply top_unique
    rw [← gen]
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, r, rfl⟩
    exact Subgroup.subset_closure ⟨a, rootPoint (z a).hom _ r, Category.assoc _ _ _⟩
  rw [htop]
  exact dense_univ

open private rootFullRank_iff from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private charactersOfIso latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private dimension_of_iso standard_torus_dimension from LinearAlgebraicGroups.Descent.RelativeRank

private theorem exists_root_of_positive_dimension (G : AffineAlgebraicGroup k) (hG : IsSemisimple G)
    (hd : 0 < topologicalKrullDim G.val.X.left) (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) : (absoluteRoots T).Nonempty := by
  let hr := reductive_of_semisimple G hG
  let P := splitBorelPair G hr T hs hm
  let D := Classification.Pinning.attachedDatum P
  letI : IsCommMonObj T.group.X := D.comm
  obtain ⟨r, ⟨t⟩⟩ := hs
  obtain ⟨s⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨χ, _, _, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let c : (Fin r → ℤ) ≃ₗ[ℤ] Additive (Specs.CharacterDescent.Character T.group) :=
    (latticeCoordinates r).symm.trans
      ((χ.trans (charactersOfIso (s ≪≫ t.symm))).toAdditive.toIntLinearEquiv)
  by_contra h
  have empty : IsEmpty (Root T) := ⟨fun α => h ⟨α.val, α.property⟩⟩
  letI : IsEmpty (Root P.T) := empty
  have hz := (rootFullRank_iff P D).mp hG
  rw [Set.range_eq_empty, Submodule.span_empty, finrank_bot] at hz
  have hRank : Module.finrank ℤ (Additive (Specs.CharacterDescent.Character T.group)) = r :=
    c.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ)
  have hr0 : r = 0 := hRank.symm.trans hz.symm
  have hdT := (dimension_of_iso t).trans (standard_torus_dimension (k := k) r)
  have hroots : absoluteRoots T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hdim := (RootData.RootGroups.rootDimension G hr T ⟨r, ⟨t⟩⟩ hm).2
  rw [hroots, Set.ncard_empty, hdT, hr0] at hdim
  exact (not_lt_of_ge (by simpa using hdim.le)) hd

open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (closedSubgroupAlgebraicGroup Index)
open private matrixPresentation continuous_glEvaluation coordinateMap_of_map from
  LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation from LinearAlgebraicGroups.Affine.StandardGroups
open private completion_noncompact from LinearAlgebraicGroups.Arithmetic.AdditiveStrongApproximation

/-- Recover an additive root parameter by evaluating a global matrix coordinate.
The closed embedding of the subgroup then precludes compactness. -/
private theorem noncompact_of_additive_subgroup (D : GlobalFieldData.{u, v} k)
    (i : MatrixRealization G) (w : D.Place) (U : ClosedSubgroup G.val)
    (A : AdditiveLine k) (z : A.group ≅ U.group) : ¬ CompactSpace (LocalPoints D i w) := by
  let R := D.Completion w
  let H := closedSubgroupAlgebraicGroup U
  let j : MatrixRealization H :=
    { size := i.size
      ambient := i.ambient
      matrix := i.matrix
      embedding := U.inclusion ≫ i.embedding
      closed := by
        letI := U.isClosedImmersion
        letI := i.closed
        exact MorphismProperty.comp_mem (@IsClosedImmersion : MorphismProperty Scheme.{u}) _ _
          U.isClosedImmersion i.closed }
  let e := polynomialChart A z
  obtain ⟨b, hb, he⟩ := matrixPresentation (CommAlgCat.of k (Polynomial k)) e j
  obtain ⟨c, hc⟩ := hb Polynomial.X
  intro h
  letI := h
  have hG : IsCompact (Set.range (asMatrix i R)) :=
    isCompact_range (localMatrixEmbedding D i w).continuous
  have hsub : Set.range (asMatrix j R) ⊆ Set.range (asMatrix i R) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p ≫ U.inclusion.hom.hom, rfl⟩
  have hH := hG.of_isClosed_subset (localMatrixEmbedding D j w).isClosed_range hsub
  have hcompact := hH.image (continuous_glEvaluation (R := R) c)
  have hfull : (fun m : Matrix.GeneralLinearGroup (Index.{u} i.size) R => glEvaluation m c) ''
      Set.range (asMatrix j R) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro r
    let a := CommAlgCat.ofHom (Polynomial.aeval r : Polynomial k →ₐ[k] R)
    let p : PointsIn j R := (testSpec k).map a.op ≫ e.hom
    refine ⟨asMatrix j R p, ⟨p, rfl⟩, ?_⟩
    have hp : coordinateMap (k := k) (p ≫ e.inv) = a := by
      simp only [p, Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map]
    change glEvaluation (asMatrix j R p) c = r
    rw [he R p, hp]
    change a.hom (b.hom c) = r
    rw [hc]
    exact Polynomial.aeval_X r
  rw [hfull] at hcompact
  exact completion_noncompact D w hcompact

theorem splitLocalNoncompactness : Specs.SplitApproximation.SplitLocalNoncompactness.{u, v} := by
  intro K _ G hG hd T hs hm D i w
  obtain ⟨α, hα⟩ := exists_root_of_positive_dimension G hG hd T hs hm
  obtain ⟨_, _, U, _, _, _, ⟨A, z, _⟩, _⟩ :=
    (RootData.RootGroups.rootSubgroups G (reductive_of_semisimple G hG) T hs hm).2 α hα
  exact noncompact_of_additive_subgroup D i w U A z

theorem splitOmittedProductNoncompactness :
    Specs.SplitApproximation.SplitOmittedProductNoncompactness.{u, v} := by
  intro K _ G hG hd T hs hm D i S hS h
  letI := h
  obtain ⟨w, hw⟩ := hS
  let j : (↑S : Set D.Place) := ⟨w, hw⟩
  have hp : Function.Surjective (fun x : ∀ v : (↑S : Set D.Place), LocalPoints D i v.1 => x j) :=
    Function.surjective_eval j
  exact splitLocalNoncompactness G hG hd T hs hm D i w
    (hp.compactSpace (continuous_apply j))

end LinearAlgebraicGroups.Arithmetic.SplitApproximation
