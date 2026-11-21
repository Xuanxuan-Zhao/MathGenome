import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionHigherHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LefschetzRelativeCohomology
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits Set Topology

namespace P202.PlanarRegionHigherHomology
open P202Specs.PlanarRegionTopology P202Specs.PlanarRegionHigherHomology
open P202Specs.RelativeFundamentalClass P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass.EmbeddingLocal

/-- Change from the Euclidean norm model to the coordinate half-space without
changing the last coordinate or its zero locus. -/
def halfPlaneModelHomeomorph : HalfPlane ≃ₜ
    SmoothManifolds.ModelData.ModelSpace 2 .halfSpace :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.subtype
    (fun _ => Iff.rfl)

/-- Use precisely the supplied half-plane charts. Atlas membership records
only the geometric zero-locus condition, with no homological certificate. -/
def surfaceManifold (K B : Set Plane) (h : IsSurfaceWithBoundary K B) :
    SmoothManifolds.ModelData.TopologicalManifold 2 .halfSpace K where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := {e | ∃ c : OpenPartialHomeomorph K HalfPlane,
    (∀ y ∈ c.source, (c y).val 1 = 0 ↔ y.val ∈ B) ∧
      e = c.transHomeomorph halfPlaneModelHomeomorph}
  covers x := by
    obtain ⟨c, hx, hc⟩ := h x
    exact ⟨c.transHomeomorph halfPlaneModelHomeomorph, ⟨c, hc, rfl⟩, hx⟩

lemma surfaceManifold_boundary (K B : Set Plane) (h : IsSurfaceWithBoundary K B) :
    manifoldBoundary (surfaceManifold K B h) = {x : K | x.val ∈ B} := by
  ext x
  constructor
  · rintro ⟨e, ⟨c, hc, rfl⟩, hx, he⟩
    exact (hc x hx).mp he
  · intro hx
    obtain ⟨c, hxc, hc⟩ := h x
    exact ⟨c.transHomeomorph halfPlaneModelHomeomorph,
      ⟨c, hc, rfl⟩, hxc, (hc x hxc).mpr hx⟩

/-- Both versions of the boundary have their actual subspace topologies. -/
def boundaryCarrierHomeomorph {K B : Set Plane} (hBK : B ⊆ K) :
    B ≃ₜ {x : K | x.val ∈ B} where
  toFun b := ⟨⟨b.val, hBK b.property⟩, b.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Restriction of the closed interval product to times strictly below one. -/
def lowerProductHomeomorph (B : Type*) [TopologicalSpace B] :
    (B × CollarTime) ≃ₜ {z : B × unitInterval | (z.2 : ℝ) < 1} where
  toFun z := ⟨(z.1, ⟨z.2.val, z.2.property.1, z.2.property.2.le⟩), z.2.property.2⟩
  invFun z := (z.val.1, ⟨z.val.2.val, z.val.2.property.1, z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The closed-parameter geometric collar supplies exactly the upstream open
parameter collar, with the same zero section. -/
def boundaryCollarToDualityCollar {K B : Set Plane} (c : BoundaryCollar K B) :
    Collar ({x : K | x.val ∈ B} : Set K) where
  neighborhood := c.map '' {z : B × unitInterval | (z.2 : ℝ) < 1}
  isOpen_neighborhood := c.open_lower_image
  homeomorph :=
    ((boundaryCarrierHomeomorph c.boundary_subset).symm.prodCongr (Homeomorph.refl _)).trans
      ((lowerProductHomeomorph B).trans (c.embedding.homeomorphImage _))
  zero_section b := by
    apply Subtype.ext
    exact c.at_zero ⟨b.val.val, b.property⟩

/-- All geometric hypotheses of the half-space duality theorem follow from
the original region, with its genuine corner-compatible collar. -/
theorem dualityGeometry : Expected.dualityGeometry := by
  intro R
  obtain ⟨_, _, _, _, hs, _, ⟨c⟩, _⟩ :=
    P202.PlanarRegionTopology.planarRegionTopology R
  refine ⟨surfaceManifold R.carrier R.boundary hs, ?_, ?_⟩
  · exact surfaceManifold_boundary R.carrier R.boundary hs
  · rw [surfaceManifold_boundary]
    exact ⟨boundaryCollarToDualityCollar c⟩

open HomologicalComplex
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

lemma dualZeroAtZero (P : Pair) (hz : IsZero (relativeHomology ℚ ℚ P 0)) :
    IsZero (relativeCohomology ℚ ℚ P 0) := by
  let K := ordinary ℚ ℚ P
  have he : K.ExactAt 0 := (exactAt_iff_isZero_homology _ _).mpr hz
  have hneg := (P202.RelativeSingularChains.ordinary_negative ℚ ℚ P (-1) (by norm_num)).1
  have hd : K.d 0 (-1) = 0 := hneg.eq_zero_of_tgt _
  haveI : Epi (K.d 1 0) := by
    exact (ShortComplex.exact_iff_epi _ hd).mp ((exactAt_iff' K 1 0 (-1) (by simp) (by simp)).mp he)
  let D := relativeCochains ℚ ℚ P
  haveI : Mono (D.d 0 1) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro a b hab
    change (K.X 0 →ₗ[ℚ] ℚ) at a b
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (K.d 1 0)).mp inferInstance c
    exact congrArg (fun f : K.X 1 →ₗ[ℚ] ℚ => f x) hab
  have hDneg := (P202.CohomologyPairs.negative ℚ ℚ).2 P (-1) (by norm_num) |>.1
  have heD : D.ExactAt 0 := by
    apply (exactAt_iff' D (-1) 0 1 (by simp) (by simp)).mpr
    exact (ShortComplex.exact_iff_mono _ (hDneg.eq_zero_of_src _)).mpr
      (show Mono (D.d 0 1) from inferInstance)
  exact heD.isZero_homology

/-- Degree zero relative homology vanishes if the subspace meets the single
path component. The point inclusion splits the map to a point. -/
lemma relativeHomologyZero (P : Pair) [PathConnectedSpace P.space]
    (b : P.sub) : IsZero (relativeHomology ℚ ℚ P 0) := by
  let T := TopCat.of PUnit
  let j : T ⟶ P.sub := TopCat.ofHom (ContinuousMap.const _ b)
  let r : P.space ⟶ T := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let F := homologyFunctor ℚ ℚ 0
  obtain ⟨e⟩ := P202.SingularDegreeZero.degreeZero ℚ ℚ P.space
  let eX : homology ℚ ℚ P.space 0 ≃ₗ[ℚ] ℚ := e.trans
    (Finsupp.uniqueLinearEquiv ℚ ℚ
      (Classical.choice (inferInstance : Nonempty (ZerothHomotopy P.space))))
  let eT : homology ℚ ℚ T 0 ≃ₗ[ℚ] ℚ :=
    Classical.choice (P202.SingularDegreeZero.pointOrdinaryZero ℚ ℚ)
  have hjr : (j ≫ P.inclusion) ≫ r = 𝟙 T := by ext x
  haveI : Mono (F.map (j ≫ P.inclusion)) := by
    have he : F.map (j ≫ P.inclusion) ≫ F.map r = 𝟙 _ := by
      rw [← F.map_comp, hjr, F.map_id]
    exact mono_of_mono_fac he
  have hn : F.map (j ≫ P.inclusion) ≠ 0 := by
    intro hzero
    have hz := IsZero.of_mono_eq_zero (F.map (j ≫ P.inclusion)) hzero
    change IsZero (homology ℚ ℚ T 0) at hz
    haveI : Subsingleton (homology ℚ ℚ T 0) := ModuleCat.subsingleton_of_isZero hz
    have : Subsingleton ℚ := eT.surjective.subsingleton
    exact (zero_ne_one : (0 : ℚ) ≠ 1) (this.elim _ _)
  have hsurj : Function.Surjective (F.map (j ≫ P.inclusion)).hom := by
    apply surjective_of_nonzero_of_finrank_eq_one
      (by
        change Module.finrank ℚ (homology ℚ ℚ P.space 0) = 1
        simpa using eX.finrank_eq)
    exact fun h => hn (ModuleCat.hom_ext h)
  haveI : Epi (F.map P.inclusion) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨z, hz⟩ := hsurj x
    exact ⟨F.map j z, by simpa only [Functor.map_comp, ModuleCat.comp_apply] using hz⟩
  let S := sequence (ordinaryFunctor ℚ ℚ) P
  let hS := shortExact_of_degreewise_shortExact S
    (P202.RelativeSingularChains.ordinary_short_exact ℚ ℚ P)
  haveI : Epi (homologyMap S.f 0) := by
    change Epi (F.map P.inclusion)
    infer_instance
  have hpr : homologyMap S.g 0 = 0 := by
    apply (cancel_epi (homologyMap S.f 0)).mp
    simp only [← homologyMap_comp, S.zero, homologyMap_zero, comp_zero]
  have hneg := P202.SingularChains.ordinary_negative_homology ℚ ℚ P.sub (-1) (by norm_num)
  haveI : Epi (homologyMap S.g 0) :=
    (ShortComplex.exact_iff_epi _ (hneg.eq_zero_of_tgt _)).mp
      (hS.homology_exact₃ 0 (-1) (by simp))
  exact IsZero.of_epi_eq_zero (homologyMap S.g 0) hpr

/-- A homotopy equivalence transports path connectedness. The paths from
`f (g y)` to `y` come from the actual inverse homotopy. -/
lemma pathConnectedSpaceOfHomotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace Y := by
  obtain ⟨H⟩ := e.right_inv
  have hp (y : Y) : Joined (e (e.invFun y)) y := by
    exact ⟨{ toFun := fun t => H (t, y)
             continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
             source' := H.map_zero_left y
             target' := H.map_one_left y }⟩
  refine ⟨Nonempty.map e inferInstance, fun x y => ?_⟩
  exact (hp x).symm.trans
    (((PathConnectedSpace.joined (e.invFun x) (e.invFun y)).map e.continuous).trans (hp y))

lemma regionPathConnected (R : PlanarRegion) : PathConnectedSpace R.carrier := by
  obtain ⟨_, _, hi, _, _, _, _, ⟨e, _⟩, _⟩ :=
    P202.PlanarRegionTopology.planarRegionTopology R
  have hc : _root_.IsConnected (interior R.carrier) := hi.symm ▸ R.connected_domain
  haveI : ConnectedSpace (interior R.carrier) := isConnected_iff_connectedSpace.mp hc
  haveI : LocallyPathConnectedSpace (interior R.carrier) :=
    isOpen_interior.locallyPathConnectedSpace
  haveI : PathConnectedSpace (interior R.carrier) :=
    pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  exact pathConnectedSpaceOfHomotopyEquiv e

/-- No finite-CW or smooth-boundary assumption is used here. -/
theorem relativeDegreeZero : Expected.relativeDegreeZero := by
  intro R
  haveI : PathConnectedSpace (boundaryPair R.carrier (carrierBoundary R)).space :=
    regionPathConnected R
  obtain ⟨b, hb⟩ := P202.PlanarRegionTopology.boundary_nonempty R
  have hbK : b ∈ R.carrier := frontier_subset_closure hb
  exact dualZeroAtZero _
    (relativeHomologyZero (boundaryPair R.carrier (carrierBoundary R)) ⟨⟨b, hbK⟩, hb⟩)

section AmbientBall
variable {M E : Type} [TopologicalSpace M] [TopologicalSpace E] [T2Space E]

def embeddingSupportMap (f : C(M, E)) (hf : Function.Injective f) (K : Set M) :
    supportedPair M K ⟶ supportedPair E (f '' K) where
  map := TopCat.ofHom f
  mapsTo := by
    rintro x hx ⟨y, hy, he⟩
    exact hx (hf he ▸ hy)

lemma embeddingSupportMap_isIso (f : C(M, E)) (hf : IsOpenEmbedding f)
    (K : Set M) (hK : IsCompact K) (j : ℕ) :
    IsIso ((relativeHomologyFunctor ℚ ℚ (j : ℤ)).map
      (embeddingSupportMap f hf.injective K)) := by
  let U := Set.range f
  let e : M ≃ₜ U := hf.isEmbedding.toHomeomorph
  let L := f '' K
  have hL : IsClosed L := (hK.image f.continuous).isClosed
  have hLU : L ⊆ U := Set.image_subset_range _ _
  let i := P202.LocalOrientation.supportedPairIsoOfHomeomorph e K
    (Subtype.val ⁻¹' L) (by
      intro x
      change x ∈ K ↔ f x ∈ f '' K
      exact ⟨fun hx => ⟨x, hx, rfl⟩, by
        rintro ⟨y, hy, he⟩
        exact hf.injective he ▸ hy⟩)
  have he : embeddingSupportMap f hf.injective K =
      i.hom ≫ P202.LocalOrientation.openSupportInclusion U L := PairMap.ext _ _ rfl
  haveI := P202.LocalOrientation.openSupportInclusion_isIso ℚ U hf.isOpen_range
    L hL hLU j
  rw [he, Functor.map_comp]
  infer_instance

lemma embeddingSupportMap_point (f : C(M, E)) (hf : Function.Injective f)
    (K : Set M) (x : M) (hx : x ∈ K) :
    embeddingSupportMap f hf K ≫ pointMap (show f x ∈ f '' K from ⟨x, hx, rfl⟩) =
      pointMap hx ≫ localMap f hf x := PairMap.ext _ _ rfl

/-- A single ambient supported ball class orients every openly embedded
manifold contained in the interior of that ball. -/
lemma orientationFromAmbientBall (AI : Manifold 2 M) (AE : Manifold 2 E)
    (f : C(M, E)) (hf : IsOpenEmbedding f) (C : CoordinateBall AE)
    (hC : ∀ x, f x ∈ C.interior) : Nonempty (Orientation ℚ AI) := by
  obtain ⟨eC⟩ := (P202.LocalOrientation.ballRestriction ℚ 2 E AE C).1
  obtain ⟨gC, hgC⟩ := P202.LocalOrientation.exists_generator ℚ eC
  let F := relativeHomologyFunctor ℚ ℚ (2 : ℤ)
  have hlocal (x : M) : IsIso (F.map (localMap f hf.injective x)) :=
    P202.RelativeFundamentalClass.EmbeddingLocal.localMap_openEmbedding_isIso ℚ f hf x 2
  let o : LocalChoice ℚ 2 M := fun x =>
    (asIso (F.map (localMap f hf.injective x))).toLinearEquiv.symm
      (restrictPoint ℚ (C.interior_subset_closed (hC x)) 2 gC)
  have hval (x : M) : F.map (localMap f hf.injective x) (o x) =
      restrictPoint ℚ (C.interior_subset_closed (hC x)) 2 gC := by
    exact (asIso (F.map (localMap f hf.injective x))).toLinearEquiv.apply_symm_apply _
  have hgen (x : M) : IsGenerator ℚ (o x) := by
    apply (P202.LocalOrientation.generator_map_iff ℚ
      (asIso (F.map (localMap f hf.injective x))).toLinearEquiv _).mp
    rw [show (asIso (F.map (localMap f hf.injective x))).toLinearEquiv (o x) =
      restrictPoint ℚ (C.interior_subset_closed (hC x)) 2 gC from hval x]
    exact (P202.LocalOrientation.generator_map_iff ℚ
      (P202.LocalOrientation.ballPointEquiv P202.LocalOrientation.ballRestriction ℚ C (hC x)) gC).mpr hgC
  refine ⟨⟨o, hgen, ?_⟩⟩
  intro x
  obtain ⟨B, hxB, _⟩ := P202.LocalOrientation.coordinateBall_basis AI x
    isOpen_univ (Set.mem_univ x)
  let K := B.closed
  let L := f '' K
  have hLC : L ⊆ C.closed := by
    rintro _ ⟨y, _, rfl⟩
    exact C.interior_subset_closed (hC y)
  let gL : SupportedGroup ℚ E L 2 := F.map (supportMap hLC) gC
  haveI : IsIso (F.map (embeddingSupportMap f hf.injective K)) :=
    embeddingSupportMap_isIso f hf K (P202.LocalOrientation.ball_closed_compact B) 2
  let gB : SupportedGroup ℚ M K 2 :=
    (asIso (F.map (embeddingSupportMap f hf.injective K))).toLinearEquiv.symm gL
  have hgB (y : M) (hy : y ∈ K) : restrictPoint ℚ hy 2 gB = o y := by
    apply (asIso (F.map (localMap f hf.injective y))).toLinearEquiv.injective
    rw [show (asIso (F.map (localMap f hf.injective y))).toLinearEquiv (o y) = _ from hval y]
    have H := congrArg (fun a => a gB)
      (congrArg F.map (embeddingSupportMap_point f hf.injective K y hy))
    simp only [Functor.map_comp, ModuleCat.comp_apply] at H
    change restrictPoint ℚ _ 2 (F.map (embeddingSupportMap f hf.injective K) gB) =
      F.map (localMap f hf.injective y) (restrictPoint ℚ hy 2 gB) at H
    change F.map (localMap f hf.injective y) (restrictPoint ℚ hy 2 gB) = _
    rw [← H]
    change restrictPoint ℚ _ 2
      ((asIso (F.map (embeddingSupportMap f hf.injective K))).toLinearEquiv gB) = _
    rw [LinearEquiv.apply_symm_apply]
    exact P202.LocalOrientation.restrictPoint_support hLC ⟨y, hy, rfl⟩ 2 gC
  refine ⟨B, hxB, gB, ?_, fun y hy => hgB y (B.interior_subset_closed hy)⟩
  apply (P202.LocalOrientation.generator_map_iff ℚ
    (P202.LocalOrientation.ballPointEquiv P202.LocalOrientation.ballRestriction ℚ B hxB) gB).mp
  change IsGenerator ℚ (restrictPoint ℚ (B.interior_subset_closed hxB) 2 gB)
  rw [hgB]
  exact hgen x

end AmbientBall

open P202Specs.PlanarRegionTopology P202Specs.PlanarRegionHigherHomology

lemma interiorCarrierMem (R : PlanarRegion) (B : Set R.carrier)
    (hB : B = carrierBoundary R) (x : Interior B) : x.val.val ∈ interior R.carrier := by
  obtain ⟨_, _, _, hb⟩ := P202.PlanarRegionTopology.basicProperties R
  apply (mem_interior_iff_notMem_frontier x.val.property).mpr
  intro hx
  apply x.property
  apply (Set.ext_iff.mp hB x.val).mpr
  change x.val.val ∈ R.boundary
  exact hb ▸ hx

def interiorCarrierHomeomorph (R : PlanarRegion) (B : Set R.carrier)
    (hB : B = carrierBoundary R) : Interior B ≃ₜ interior R.carrier where
  toFun x := ⟨x.val.val, interiorCarrierMem R B hB x⟩
  invFun y := ⟨⟨y.val, interior_subset y.property⟩, by
    rw [hB]
    change y.val ∉ R.boundary
    obtain ⟨_, _, _, hb⟩ := P202.PlanarRegionTopology.basicProperties R
    rw [← hb]
    exact (mem_interior_iff_notMem_frontier (interior_subset y.property)).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma regionInteriorOrientation (R : PlanarRegion) (B : Set R.carrier)
    (hB : B = carrierBoundary R) (AI : Manifold 2 (Interior B)) :
    Nonempty (Orientation ℚ AI) := by
  let e := interiorCarrierHomeomorph R B hB
  let a := (P202.LocalOrientation.coordinateEuclideanHomeomorph 2).symm
  let f : C(Interior B, Coordinate 2) :=
    ⟨fun x => a (e x).val, a.continuous.comp (continuous_subtype_val.comp e.continuous)⟩
  have hf : IsOpenEmbedding f := a.isOpenEmbedding.comp
    (isOpen_interior.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding)
  have hK : IsCompact (a '' R.carrier) := R.compact_closure.image a.continuous
  obtain ⟨r, hr, hsub⟩ := hK.isBounded.subset_ball_lt 0 (coordinateOrigin 2)
  let AE : Manifold 2 (Coordinate 2) := {
    hausdorff := inferInstance
    secondCountable := inferInstance
    atlas := {OpenPartialHomeomorph.refl (Coordinate 2)}
    covers := fun x => ⟨_, rfl, Set.mem_univ x⟩ }
  let C : CoordinateBall AE := {
    chart := OpenPartialHomeomorph.refl (Coordinate 2)
    chart_mem := rfl
    center := coordinateOrigin 2
    radius := r
    radius_pos := hr
    closedBall_subset := Set.subset_univ _ }
  apply orientationFromAmbientBall AI AE f hf C
  intro x
  exact ⟨Set.mem_univ _, hsub ⟨x.val.val, x.val.property, rfl⟩⟩

/-- The ordinary local-homology orientation is constructed, rather than
identified with the boundary normal-side sign convention. -/
theorem interiorOrientable : Expected.interiorOrientable := regionInteriorOrientation

/-- The first cap isomorphism at degree zero and above-dimension vanishing,
with every geometric and cohomological hypothesis discharged. -/
theorem vanishingFromOrientation :
    P202Specs.PlanarRegionHigherHomology.Expected.vanishingFromOrientation := by
  intro horient R n hn
  obtain ⟨A, hB, ⟨c⟩⟩ := dualityGeometry R
  let AI := P202.RelativeFundamentalClass.Geometry.interiorManifold A
  obtain ⟨o⟩ := horient R (manifoldBoundary A) hB AI
  have hM : IsCompact (Set.univ : Set R.carrier) := by
    letI : CompactSpace R.carrier := isCompact_iff_compactSpace.mp R.compact_closure
    exact isCompact_univ
  by_cases h2 : n = 2
  · subst n
    have hz : IsZero (relativeCohomology ℚ ℚ
        (boundaryPair R.carrier (manifoldBoundary A)) 0) := by
      rw [hB]
      exact relativeDegreeZero R
    let f := P202Specs.LefschetzRelativeCohomology.cap ℚ
      (P202.CapProducts.pairProductsData ℚ) (manifoldBoundary A) 2 o.val 0
    have hf : Function.Bijective f :=
      (P202.LefschetzRelativeCohomology.duality ℚ
        (P202.CapProducts.pairProductsData ℚ) (P202.CompactSupport.dualityData ℚ)
        2 R.carrier A c AI o hM).1 0
    apply ModuleCat.isZero_iff_subsingleton.mpr
    haveI := ModuleCat.subsingleton_of_isZero hz
    exact hf.2.subsingleton
  · exact (P202.LefschetzRelativeCohomology.aboveDimension ℚ 2 R.carrier A
      c AI o hM (n : ℤ) (by omega)).1

/-- Every ordinary rational singular homology group of the original compact
planar region in degree at least two vanishes. -/
theorem higherHomology : Expected.higherHomology :=
  vanishingFromOrientation interiorOrientable

end P202.PlanarRegionHigherHomology
