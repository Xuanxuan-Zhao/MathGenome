import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConstructibleTriangles
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FiniteFaceDevissage
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainHomology
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Geometry TopologicalSpace Set Topology Opposite Filter
open TopCat.Presheaf
open scoped BigOperators

universe u v w

namespace RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

open Analytic

variable {σ : Type u}

private theorem interior_barycentricHalfspaces {I : Type*} [Finite I]
    {V : Type v} {P : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (b : AffineBasis I ℝ P) :
    interior (⋂ i : I, b.coord i ⁻¹' Ici 0) = ⋂ i : I, b.coord i ⁻¹' Ioi 0 := by
  cases subsingleton_or_nontrivial I with
  | inl h =>
    have h₁ (i : I) : (b.coord i : P → ℝ) ⁻¹' Ici 0 = Set.univ := by ext; simp
    have h₂ (i : I) : (b.coord i : P → ℝ) ⁻¹' Ioi 0 = Set.univ := by ext; simp
    simp only [h₁, h₂, iInter_univ, interior_univ]
  | inr h =>
    simp only [interior_iInter_of_finite, ←
      IsOpenMap.preimage_interior_eq_interior_preimage (isOpenMap_barycentric_coord b _)
        (continuous_barycentric_coord b _), interior_Ici]

set_option maxHeartbeats 600000 in
private theorem weightedSum_mem_faceInterior_iff [Fintype σ] {s : Finset (σ → ℝ)}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → (σ → ℝ)))
    (w : (σ → ℝ) → ℝ) (hw : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • i) ∈ faceInterior s ↔ ∀ i ∈ s, 0 < w i := by
  classical
  let E := σ → ℝ
  let A := affineSpan ℝ (s : Set E)
  let p : s → A := fun i => ⟨i.val, subset_affineSpan ℝ (s : Set E) i.property⟩
  have : Nonempty s := hs.coe_sort
  have : Nonempty A := Nonempty.map p inferInstance
  have hp : Set.range p = ((↑) : A → E) ⁻¹' (s : Set E) := by
    ext y
    refine ⟨?_, fun h => ⟨⟨y.val, h⟩, Subtype.ext rfl⟩⟩
    rintro ⟨i, rfl⟩
    exact i.property
  let b : AffineBasis s ℝ A :=
    ⟨p, AffineIndependent.of_comp A.subtype hind,
      hp ▸ affineSpan_coe_preimage_eq_top (s : Set E)⟩
  have sum_eq (v : E → ℝ) : ∑ i : s, v i.val = ∑ i ∈ s, v i := by
    rw [← Finset.attach_eq_univ, Finset.sum_attach]
  have combination_eq (v : E → ℝ) (hv : ∑ i ∈ s, v i = 1) :
      (Finset.univ.affineCombination ℝ b (fun i => v i.val) : A).val =
        ∑ i ∈ s, v i • i := by
    have hv' : ∑ i : s, v i.val = 1 := (sum_eq v).trans hv
    change A.subtype (Finset.univ.affineCombination ℝ b (fun i => v i.val)) = _
    rw [Finset.map_affineCombination _ b _ hv',
      Finset.affineCombination_eq_linear_combination _ _ _ hv']
    change (∑ i : s, v i.val • i.val) = _
    rw [← Finset.attach_eq_univ, Finset.sum_attach s (fun i => v i • i)]
  have hull_eq : ((↑) : A → E) ⁻¹' convexHull ℝ (s : Set E) =
      ⋂ i : s, b.coord i ⁻¹' Ici 0 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_Ici]
    constructor
    · intro hy
      obtain ⟨v, hv₀, hv₁, hv⟩ := Finset.mem_convexHull'.mp hy
      have hy' : Finset.univ.affineCombination ℝ b (fun i => v i.val) = y :=
        Subtype.ext ((combination_eq v hv₁).trans hv)
      intro i
      rw [← hy', b.coord_apply_combination_of_mem (Finset.mem_univ i) ((sum_eq v).trans hv₁)]
      exact hv₀ i.val i.property
    · intro hy
      rw [← b.affineCombination_coord_eq_self y]
      change A.subtype (Finset.univ.affineCombination ℝ b (fun i => b.coord i y)) ∈ _
      rw [Finset.map_affineCombination _ b _ (b.sum_coord_apply_eq_one y)]
      have hr : Set.range (A.subtype ∘ b) = (s : Set E) := Subtype.range_coe
      rw [← hr]
      exact affineCombination_mem_convexHull (fun i _ => hy i) (b.sum_coord_apply_eq_one y)
  let y : A := Finset.univ.affineCombination ℝ b (fun i => w i.val)
  have hy : y.val = ∑ i ∈ s, w i • i := combination_eq w hw
  have hy' (i : s) : b.coord i y = w i.val :=
    b.coord_apply_combination_of_mem (Finset.mem_univ i) ((sum_eq w).trans hw)
  have hface : faceInterior s =
      ((↑) : A → E) '' interior (((↑) : A → E) ⁻¹' convexHull ℝ (s : Set E)) := by
    unfold faceInterior intrinsicInterior
    rw [affineSpan_convexHull]
  rw [← hy, hface, hull_eq]
  have hb := interior_barycentricHalfspaces (V := A.direction) (P := A) b
  rw [hb]
  constructor
  · rintro ⟨z, hz, hzy⟩ i hi
    have e : z = y := Subtype.ext hzy
    have hpos : 0 < b.coord ⟨i, hi⟩ y := Set.mem_iInter.mp (e ▸ hz) ⟨i, hi⟩
    rwa [hy'] at hpos
  · intro h
    refine ⟨y, Set.mem_iInter.mpr fun i => ?_, rfl⟩
    change 0 < b.coord i y
    rw [hy']
    exact h i i.property

theorem faceInterior_subset_convexHull (s : Finset (σ → ℝ)) :
    faceInterior s ⊆ convexHull ℝ (s : Set (σ → ℝ)) :=
  intrinsicInterior_subset

/-- In a simplicial complex a point in the interior of one face belongs to the closed
hull of another face precisely when the second face contains the first. -/
theorem mem_convexHull_iff_face_subset [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    {s t : K.faces} {x : σ → ℝ} (hx : x ∈ faceInterior s.val) :
    x ∈ convexHull ℝ (t.val : Set (σ → ℝ)) ↔ s.val ⊆ t.val := by
  classical
  refine ⟨?_, fun h => convexHull_mono h (faceInterior_subset_convexHull _ hx)⟩
  intro ht i his
  have hst : x ∈ convexHull ℝ (s.val : Set (σ → ℝ)) ∩
      convexHull ℝ (t.val : Set (σ → ℝ)) := ⟨faceInterior_subset_convexHull _ hx, ht⟩
  rw [K.convexHull_inter_convexHull s.property t.property, ← Finset.coe_inter] at hst
  obtain ⟨w, _, hw, hsum⟩ := Finset.mem_convexHull'.mp hst
  let v : (σ → ℝ) → ℝ := fun z => if z ∈ t.val then w z else 0
  have hwv : ∑ z ∈ s.val, v z = 1 := by
    rwa [← Finset.filter_mem_eq_inter, Finset.sum_filter] at hw
  have hxv : ∑ z ∈ s.val, v z • z = x := by
    simpa [v, ite_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter] using hsum
  have hv := (weightedSum_mem_faceInterior_iff (K.nonempty_of_mem_faces s.property)
    (K.indep s.property) v hwv).mp (hxv.symm ▸ hx)
  by_contra hi
  simpa [v, hi] using hv i his

private theorem exists_faceInterior [Fintype σ] (K : SimplicialComplex ℝ (σ → ℝ))
    (x : K.space) : ∃ s : K.faces, x.val ∈ faceInterior s.val := by
  classical
  obtain ⟨s, hs, hx⟩ := K.mem_space_iff.mp x.property
  obtain ⟨w, hw₀, hw₁, hw⟩ := Finset.mem_convexHull'.mp hx
  let t := s.filter fun z => 0 < w z
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hw₁' : ∑ z ∈ t, w z = 1 := by
    rw [Finset.sum_subset hts (fun i hi hit =>
      le_antisymm (le_of_not_gt (fun h => hit (Finset.mem_filter.mpr ⟨hi, h⟩))) (hw₀ i hi))]
    exact hw₁
  have ht : t.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at hw₁'
    exact zero_ne_one hw₁'
  have htf := K.down_closed hs hts ht
  have hx' : ∑ z ∈ t, w z • z = x.val := by
    rw [Finset.sum_subset hts (fun i hi hit => by
      have hi₀ := le_antisymm
        (le_of_not_gt (fun h => hit (Finset.mem_filter.mpr ⟨hi, h⟩))) (hw₀ i hi)
      simp [hi₀])]
    exact hw
  exact ⟨⟨t, htf⟩, hx' ▸ (weightedSum_mem_faceInterior_iff ht (K.indep htf) w hw₁').mpr
    (fun z hz => (Finset.mem_filter.mp hz).2)⟩

theorem isLocallyClosed_faceInterior [Fintype σ] (s : Finset (σ → ℝ)) :
    IsLocallyClosed (faceInterior s) := by
  let H := convexHull ℝ (s : Set (σ → ℝ))
  have hH : IsClosed H := s.finite_toSet.isClosed_convexHull ℝ
  have hF : IsClosed (intrinsicFrontier ℝ H) :=
    isClosed_intrinsicFrontier (affineSpan ℝ H).closed_of_finiteDimensional
  refine ⟨(intrinsicFrontier ℝ H)ᶜ, H, hF.isOpen_compl, hH, ?_⟩
  rw [inter_comm, ← sdiff_eq]
  change intrinsicInterior ℝ H = _
  simpa only [hH.closure_eq] using (closure_sdiff_intrinsicFrontier (𝕜 := ℝ) H).symm

theorem faceInteriorsPartition : Expected.FaceInteriorsPartition.{u} := by
  intro σ hσ K hK
  let := Fintype.ofFinite σ
  have : Finite K.faces := hK.to_subtype
  have partition {X : TopCat.{u}} (f : X ⟶ TopCat.of K.space) :
      IsFiniteLocallyClosedPartition (fun s : K.faces => facePiece (f ≫ complexInclusion K) s.val) := by
    refine ⟨inferInstance, fun s => (isLocallyClosed_faceInterior s.val).preimage
      (f ≫ complexInclusion K).hom.continuous, ?_⟩
    intro x
    obtain ⟨s, hs⟩ := exists_faceInterior K (f x)
    refine ⟨s, hs, fun t ht => Subtype.ext (Finset.Subset.antisymm ?_ ?_)⟩
    · exact (mem_convexHull_iff_face_subset (s := t) (t := s) ht).mp
        (faceInterior_subset_convexHull _ hs)
    · exact (mem_convexHull_iff_face_subset (s := s) (t := t) hs).mp
        (faceInterior_subset_convexHull _ ht)
  refine ⟨?_, partition (𝟙 _), fun W _ => partition (openInclusion W)⟩
  intro s
  have hs : (s.val : Set (σ → ℝ)).Nonempty := K.nonempty_of_mem_faces s.property
  obtain ⟨x, hx⟩ := hs.mono (subset_convexHull ℝ (s.val : Set (σ → ℝ))) |>.intrinsicInterior
    (convex_convexHull ℝ _)
  exact ⟨⟨x, K.convexHull_subset_space s.property (faceInterior_subset_convexHull _ hx)⟩, hx⟩

theorem convex_faceInterior (s : Finset (σ → ℝ)) : Convex ℝ (faceInterior s) := by
  refine convex_iff_openSegment_subset.mpr fun _ hx _ hy => ?_
  exact (convex_convexHull ℝ _).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
    hx (subset_intrinsicClosure (faceInterior_subset_convexHull _ hy))

theorem closure_faceInterior [Fintype σ] {s : Finset (σ → ℝ)} (hs : s.Nonempty) :
    closure (faceInterior s) = convexHull ℝ (s : Set (σ → ℝ)) := by
  have hclosed := s.finite_toSet.isClosed_convexHull ℝ
  refine (closure_minimal (faceInterior_subset_convexHull s) hclosed).antisymm ?_
  have hin : (faceInterior s).Nonempty :=
    Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _)
      ((show (s : Set (σ → ℝ)).Nonempty from hs).mono (subset_convexHull ℝ _))
  obtain ⟨a, ha⟩ := hin
  intro x hx
  exact closure_mono
    ((convex_convexHull ℝ _).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      ha (subset_intrinsicClosure hx))
    (segment_subset_closure_openSegment (right_mem_segment ℝ a x))

theorem stageInclusion_isOpenEmbedding {K : SimplicialComplex ℝ (σ → ℝ)}
    {U Y : Opens (TopCat.of K.space)} (h : U ≤ Y) : IsOpenEmbedding (stageInclusion h) := by
  change IsOpenEmbedding (fun x : U => (⟨x.val, h x.property⟩ : Y))
  exact IsOpenEmbedding.of_comp _ Y.isOpenEmbedding U.isOpenEmbedding

/-- An open union of pieces contains the whole face interior as soon as it meets it. -/
theorem facePiece_subset_of_nonempty_inter {K : SimplicialComplex ℝ (σ → ℝ)}
    (hσ : Finite σ) (hK : K.faces.Finite) {W : Set K.space}
    (hW : IsUnionOfFaceInteriors K W) (s : K.faces)
    (hs : (facePiece (complexInclusion K) s.val ∩ W).Nonempty) :
    facePiece (complexInclusion K) s.val ⊆ W := by
  obtain ⟨T, rfl⟩ := hW
  obtain ⟨x, hxs, hxW⟩ := hs
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxW
  have e : t = s := (faceInteriorsPartition σ K hK).2.1.2.2 x |>.unique hxt hxs
  exact e ▸ Set.subset_iUnion₂_of_subset t ht (Set.Subset.rfl)

/-- A face interior meets every ball centered at a point of its closed hull. At a point
outside that hull all sufficiently small balls miss the interior. -/
theorem ball_inter_faceInterior [Fintype σ] {s : Finset (σ → ℝ)} (hs : s.Nonempty)
    (x : σ → ℝ) :
    (∀ r > 0, (Metric.ball x r ∩ faceInterior s).Nonempty) ↔
      x ∈ convexHull ℝ (s : Set (σ → ℝ)) := by
  rw [← closure_faceInterior hs, Metric.mem_closure_iff]
  simp only [Set.nonempty_def, Set.mem_inter_iff, Metric.mem_ball, dist_comm]
  exact forall₂_congr fun _ _ => exists_congr fun _ => and_comm

private abbrev constantPresheaf (X : TopCat.{u}) (V : Coeff.{u}) : X.Presheaf Coeff.{u} :=
  (Functor.const _).obj V

private abbrev constSection (X : TopCat.{u}) (V : Coeff.{u}) (U : Opens X) :
    V ⟶ (constant X V).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).app (op U)

private def constantGermIso (X : TopCat.{u}) (V : Coeff.{u}) (x : X) :
    (stalk x).obj (constant X V) ≅ V := by
  let P := constantPresheaf X V
  let C := TopCat.Presheaf.stalkFunctor Coeff.{u} x
  let η := toSheafify (Opens.grothendieckTopology X) P
  have : IsIso (C.map η) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  let J := (OpenNhds x)ᵒᵖ
  let h : IsColimit (constCocone J V) := isColimitConstCocone J V
  exact (asIso (C.map η)).symm ≪≫ (colimit.isColimit ((Functor.const J).obj V)).coconePointUniqueUpToIso h

private theorem constSection_germ (X : TopCat.{u}) (V : Coeff.{u}) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    constSection X V U ≫ germ (constant X V).obj U x hx ≫ (constantGermIso X V x).hom =
      𝟙 V := by
  let P := constantPresheaf X V
  let η := toSheafify (Opens.grothendieckTopology X) P
  change η.app (op U) ≫ germ (sheafify (Opens.grothendieckTopology X) P) U x hx ≫ _ = _
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_assoc U x hx η]
  rw [constantGermIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitConstCocone (OpenNhds x)ᵒᵖ V) (op ⟨U, hx⟩)

private theorem constSection_germ_apply {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X)
    (x : X) (hx : x ∈ U) (v : V) :
    (constantGermIso X V x).hom (germ (constant X V).obj U x hx (constSection X V U v)) = v :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (constSection_germ X V U x hx)) v

/-- On a nonempty connected open set the map from coefficients to sections of the actual
sheafified constant presheaf is bijective. -/
theorem constSection_bijective {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X)
    (hU : IsConnected (U : Set X)) : Function.Bijective (constSection X V U) := by
  obtain ⟨x, hx⟩ := hU.nonempty
  refine ⟨fun v w e => ?_, ?_⟩
  · rw [← constSection_germ_apply V U x hx v, ← constSection_germ_apply V U x hx w, e]
  intro t
  let F := constant X V
  let f : U → V := fun y => (constantGermIso X V y.val).hom (germ F.obj U y.val y.property t)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    obtain ⟨W, hyW, iWU, iWU', e⟩ := germ_eq F.obj y.val y.property y.property t
      (constSection X V U (f y)) (by
        apply (ModuleCat.mono_iff_injective (constantGermIso X V y.val).hom).mp inferInstance
        exact (constSection_germ_apply V U y.val y.property (f y)).symm)
    filter_upwards [(W.isOpen.preimage continuous_subtype_val).mem_nhds hyW] with z hz
    have ez := germ_ext F.obj (hxU := z.property) (hxV := z.property) W hz iWU iWU' e
    change (constantGermIso X V z.val).hom (germ F.obj U z.val z.property t) = f y
    rw [ez, constSection_germ_apply]
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.isPreconnected
  refine ⟨f ⟨x, hx⟩, ?_⟩
  apply TopCat.Presheaf.section_ext F U
  intro y hy
  apply (ModuleCat.mono_iff_injective (constantGermIso X V y).hom).mp inferInstance
  rw [constSection_germ_apply]
  exact hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

private def constantDirectImageMap {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Coeff.{u}) :
    constant Y V ⟶ (directImage f).obj (constant X V) := by
  let η : constantPresheaf Y V ⟶ ((directImage f).obj (constant X V)).obj :=
    { app := fun U => constSection X V ((Opens.map f).obj U.unop)
      naturality := by
        intro U W g
        have h := (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).naturality
          ((Opens.map f).op.map g)
        exact h }
  exact ⟨sheafifyLift _ η ((directImage f).obj (constant X V)).property⟩

private theorem constantDirectImageMap_app {X Y : TopCat.{u}} (f : X ⟶ Y)
    (V : Coeff.{u}) (U : Opens Y) :
    constSection Y V U ≫ (constantDirectImageMap f V).hom.app (op U) =
      constSection X V ((Opens.map f).obj U) := by
  unfold constantDirectImageMap
  exact congrArg (fun η : constantPresheaf Y V ⟶ _ => η.app (op U))
    (toSheafify_sheafifyLift _ _ _)

/-- If preimages of sufficiently small neighborhoods are nonempty and connected, the
ordinary pushforward of the constant sheaf is constant via the canonical restriction map. -/
theorem isIso_constantDirectImageMap {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Coeff.{u})
    (h : ∀ (y : Y) (U : Opens Y), y ∈ U → ∃ W : Opens Y, y ∈ W ∧ W ≤ U ∧
      IsConnected (((Opens.map f).obj W : Opens X) : Set X)) :
    IsIso (constantDirectImageMap f V) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro y
  let F := (directImage f).obj (constant X V)
  let G : Y.Presheaf Coeff.{u} := F.obj
  let P := (constant Y V).obj
  let η := (constantDirectImageMap f V).hom
  let C := stalkFunctor Coeff.{u} y
  change IsIso (C.map η)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have he (U : Opens Y) (hy : y ∈ U) (v : V) :
      C.map η (germ P U y hy (constSection Y V U v)) =
        germ G U y hy (constSection X V ((Opens.map f).obj U) v) := by
    rw [stalkFunctor_map_germ_apply]
    exact congrArg (fun z => germ G U y hy z)
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (constantDirectImageMap_app f V U)) v)
  have hg (U W : Opens Y) (i : W ⟶ U) (v : V) :
      G.map i.op (constSection X V ((Opens.map f).obj U) v) =
        constSection X V ((Opens.map f).obj W) v := by
    have e := (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).naturality
      ((Opens.map f).op.map i.op)
    simp only [Functor.const_obj_map] at e
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.symm) v
  constructor
  · intro a b hab
    let W : Opens Y := ⊤
    have hyW : y ∈ W := trivial
    let e := constantGermIso Y V y
    let v := e.hom a
    let w := e.hom b
    have hi := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    have hv : germ P W y hyW (constSection Y V W v) = a :=
      hi (constSection_germ_apply V W y hyW v)
    have hw : germ P W y hyW (constSection Y V W w) = b :=
      hi (constSection_germ_apply V W y hyW w)
    rw [← hv, ← hw, he, he] at hab
    obtain ⟨U, hyU, i, i', e'⟩ := germ_eq G y hyW hyW _ _ hab
    rw [hg, hg] at e'
    obtain ⟨T, _, hTU, hT⟩ := h y U hyU
    have h' := congrArg (G.map (homOfLE hTU).op) e'
    rw [hg, hg] at h'
    have evw := (constSection_bijective V _ hT).1 h'
    exact hi evw
  · intro c
    obtain ⟨U, hyU, s, hs⟩ := exists_germ_eq G c
    obtain ⟨W, hyW, hWU, hW⟩ := h y U hyU
    let i : W ⟶ U := homOfLE hWU
    obtain ⟨v, hv⟩ := (constSection_bijective V _ hW).2 (G.map i.op s)
    refine ⟨germ P W y hyW (constSection Y V W v), ?_⟩
    rw [he, hv, germ_res_apply, hs]

/-- The ordinary direct image from a face interior into any intermediate subspace of
its closed simplex is the constant sheaf on that subspace. -/
theorem constantDirectImage_faceInterior [Fintype σ] {s : Finset (σ → ℝ)}
    (hs : s.Nonempty) {Z : Set (σ → ℝ)}
    (h₁ : faceInterior s ⊆ Z) (h₂ : Z ⊆ convexHull ℝ (s : Set (σ → ℝ))) (V : Coeff.{u}) :
    let f : TopCat.of (faceInterior s) ⟶ TopCat.of Z :=
      TopCat.ofHom ⟨Set.inclusion h₁, continuous_subtype_val.subtype_mk _⟩
    Nonempty ((directImage f).obj (constant (TopCat.of (faceInterior s)) V) ≅
      constant (TopCat.of Z) V) := by
  intro f
  have h : IsIso (constantDirectImageMap f V) := by
    apply isIso_constantDirectImageMap
    intro x U hx
    obtain ⟨r, hr, hU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
    let B : Opens (TopCat.of Z) := ⟨Metric.ball x r, Metric.isOpen_ball⟩
    refine ⟨B, Metric.mem_ball_self hr, hU, ?_⟩
    let A := Metric.ball x.val r ∩ faceInterior s
    have hA := (ball_inter_faceInterior hs x.val).mpr (h₂ x.property) r hr
    have hconv : Convex ℝ A := (convex_ball _ _).inter (convex_faceInterior s)
    let m : A → faceInterior s := Set.inclusion (show A ⊆ faceInterior s from inter_subset_right)
    have hm : Continuous m := continuous_subtype_val.subtype_mk _
    have hconn : _root_.IsConnected (Set.range m) := by
      have : ConnectedSpace A := isConnected_iff_connectedSpace.mp (hconv.isConnected hA)
      simpa only [Set.image_univ] using (@isConnected_univ A _ _).image m hm.continuousOn
    have heq : Set.range m = (((Opens.map f).obj B : Opens (TopCat.of (faceInterior s))) :
        Set (faceInterior s)) := by
      ext z
      change (∃ a : A, m a = z) ↔ dist z.val x.val < r
      exact ⟨fun ⟨a, e⟩ => by rw [← e]; exact a.property.1,
        fun hz => ⟨⟨z.val, hz, z.property⟩, Subtype.ext rfl⟩⟩
    exact heq ▸ hconn
  exact ⟨(asIso (constantDirectImageMap f V)).symm⟩

private def sectionGerms {X : TopCat.{u}} (F : Sheaves X) (U : Opens X)
    (s : F.obj.obj (op U)) : C(U, EtaleSpace F.obj) :=
  ⟨fun x => ⟨x.val, germ F.obj U x.val x.property s⟩, by
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨W, t, rfl⟩
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxW, hx⟩
    obtain ⟨V, hxV, iVU, iVW, e⟩ := germ_eq F.obj x.val x.property hxW s t hx
    filter_upwards [(V.isOpen.preimage continuous_subtype_val).mem_nhds hxV] with y hy
    exact ⟨iVW.le hy, germ_ext F.obj (hxU := y.property) V hy iVU iVW e⟩⟩

/-- Any continuous section of the étale space of a sheaf gives a section over the whole space. -/
private theorem exists_globalSection_of_sectionGerms {X : TopCat.{u}} (F : Sheaves X)
    (g : C(X, EtaleSpace F.obj)) (hg : ∀ x, (g x).base = x) :
    ∃ s : F.obj.obj (op ⊤), ∀ x, (g x).germ = germ F.obj ⊤ (g x).base trivial s := by
  classical
  have localRep (x : X) : ∃ (W : Opens X), x ∈ W ∧
      ∃ s : F.obj.obj (op W), ∀ y (hy : y ∈ W),
        ∃ h : (g y).base ∈ W, (g y).germ = germ F.obj W (g y).base h s := by
    obtain ⟨U, _, s, hs⟩ := EtaleSpace.exists_section_of_tendsto g.continuous.continuousAt
      (g₀ := g x)
    obtain ⟨W', hW's, hW'o, hxW'⟩ := mem_nhds_iff.mp hs
    have hW'U : W' ⊆ U := fun y hy => hg y ▸ (hW's hy).1
    let W : Opens X := ⟨W', hW'o⟩
    let i : W ⟶ U := homOfLE hW'U
    refine ⟨W, hxW', F.obj.map i.op s, fun y hy => ⟨(hg y).symm ▸ hy, ?_⟩⟩
    rw [germ_res_apply]
    exact (hW's hy).2
  choose W hxW s hs using localRep
  have hcover : (⊤ : Opens X) ≤ iSup W := fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩
  let i (x : X) : W x ⟶ (⊤ : Opens X) := homOfLE le_top
  have comp : TopCat.Presheaf.IsCompatible F.obj W s := by
    intro x y
    apply section_ext F
    intro z hz
    have hx : z ∈ W x := (show W x ⊓ W y ≤ W x from inf_le_left) hz
    have hy : z ∈ W y := (show W x ⊓ W y ≤ W y from inf_le_right) hz
    obtain ⟨hx', ex⟩ := hs x z hx
    obtain ⟨hy', ey⟩ := hs y z hy
    rw [germ_res_apply, germ_res_apply]
    have transport (a b : X) (e : a = b) (ha₁ : a ∈ W x) (ha₂ : a ∈ W y)
        (hb₁ : b ∈ W x) (hb₂ : b ∈ W y)
        (h : germ F.obj (W x) a ha₁ (s x) = germ F.obj (W y) a ha₂ (s y)) :
        germ F.obj (W x) b hb₁ (s x) = germ F.obj (W y) b hb₂ (s y) := by
      subst b
      exact h
    exact transport _ _ (hg z) hx' hy' hx hy (ex.symm.trans ey)
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' W ⊤ i hcover s comp
  refine ⟨t, fun x => ?_⟩
  obtain ⟨h, e⟩ := hs x x (hxW x)
  rw [← germ_res_apply F.obj (i x) (g x).base h t, ht]
  exact e

private def globalSectionGerms {X : TopCat.{u}} (F : Sheaves X) (s : F.obj.obj (op ⊤)) :
    C(X, EtaleSpace F.obj) :=
  (sectionGerms F ⊤ s).comp ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk _⟩

private theorem globalGerm_bijective_of_covering {X : TopCat.{u}}
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (F : Sheaves X)
    (h : IsCoveringMap (EtaleSpace.base (F := F.obj))) (x : X) :
    Function.Bijective (germ F.obj ⊤ x trivial) := by
  constructor
  · intro s t e
    let p : EtaleSpace F.obj := ⟨x, germ F.obj ⊤ x trivial s⟩
    obtain ⟨g, _, hu⟩ := h.existsUnique_continuousMap_lifts (ContinuousMap.id X) x p rfl
    have es := hu (globalSectionGerms F s) ⟨rfl, rfl⟩
    have et := hu (globalSectionGerms F t) ⟨by
      change (⟨x, germ F.obj ⊤ x trivial t⟩ : EtaleSpace F.obj) = p
      rw [← e], rfl⟩
    apply section_ext F ⊤
    intro y _
    have e' := DFunLike.congr_fun (es.trans et.symm) y
    change (⟨y, germ F.obj ⊤ y trivial s⟩ : EtaleSpace F.obj) =
      ⟨y, germ F.obj ⊤ y trivial t⟩ at e'
    injection e'
  · intro a
    let p : EtaleSpace F.obj := ⟨x, a⟩
    obtain ⟨g, ⟨hx, hg⟩, _⟩ :=
      h.existsUnique_continuousMap_lifts (ContinuousMap.id X) x p rfl
    obtain ⟨s, hs⟩ := exists_globalSection_of_sectionGerms F g (fun y => congrFun hg y)
    have transport {k l : EtaleSpace F.obj} (e : k = l)
        (h : k.germ = germ F.obj ⊤ k.base trivial s) :
        l.germ = germ F.obj ⊤ l.base trivial s := e ▸ h
    exact ⟨s, (transport hx (hs x)).symm⟩

private theorem isIso_stalkMap_of_cofinal {X : TopCat.{u}} {P Q : X.Presheaf Coeff.{u}}
    (η : P ⟶ Q) (x : X) (h : ∀ (U : Opens X), x ∈ U →
      ∃ W : Opens X, W ≤ U ∧ x ∈ W ∧ IsIso (η.app (op W))) :
    IsIso ((stalkFunctor _ x).map η) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b e
    obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq a
    obtain ⟨V, hxV, t, rfl⟩ := P.exists_germ_eq b
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at e
    obtain ⟨T, hxT, i, j, e⟩ := Q.germ_eq x hxU hxV _ _ e
    obtain ⟨W, hWT, hxW, hW⟩ := h T hxT
    let k : W ⟶ T := homOfLE hWT
    have e' := congrArg (Q.map k.op) e
    simp only [← ConcreteCategory.comp_apply, Category.assoc, ← η.naturality] at e'
    have e'' := (ConcreteCategory.isIso_iff_bijective _).mp hW |>.injective e'
    apply P.germ_ext W hxW (k ≫ i) (k ≫ j)
    simp only [op_comp, P.map_comp, ConcreteCategory.comp_apply]
    exact e''
  · intro a
    obtain ⟨U, hxU, t, rfl⟩ := Q.exists_germ_eq a
    obtain ⟨W, hWU, hxW, hW⟩ := h U hxU
    let i : W ⟶ U := homOfLE hWU
    obtain ⟨s, hs⟩ := (ConcreteCategory.isIso_iff_bijective _).mp hW |>.surjective (Q.map i.op t)
    exact ⟨P.germ W x hxW s, by rw [stalkFunctor_map_germ_apply, hs, germ_res_apply]⟩

private theorem isIso_germ_of_constant {X : TopCat.{u}} {F : Sheaves X}
    {V : Coeff.{u}} (e : F ≅ constant X V) (U : Opens X)
    (hU : _root_.IsConnected (U : Set X)) (x : X) (hx : x ∈ U) :
    IsIso (germ F.obj U x hx) := by
  have hconst : IsIso (constSection X V U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (constSection_bijective V U hU)
  have hg : IsIso (germ (constant X V).obj U x hx) := by
    rw [← isIso_comp_right_iff _ (constantGermIso X V x).hom,
      ← isIso_comp_left_iff (constSection X V U), constSection_germ]
    infer_instance
  have : IsIso (e.hom.hom.app (op U)) := by
    change IsIso (((TopCat.Sheaf.forget Coeff.{u} X).mapIso e).hom.app (op U))
    infer_instance
  have : IsIso ((stalkFunctor Coeff.{u} x).map e.hom.hom) := by
    change IsIso ((stalk x).map e.hom)
    infer_instance
  rw [← isIso_comp_right_iff _ ((stalkFunctor Coeff.{u} x).map e.hom.hom),
    stalkFunctor_map_germ]
  infer_instance

private theorem etaleSpace_isCoveringMap_of_locallyConstant {X : TopCat.{u}}
    [LocallyConnectedSpace X] (F : Sheaves X) (hF : LocallyConstantFiniteRank F) :
    IsCoveringMap (EtaleSpace.base (F := F.obj)) := by
  apply EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨O, hxO, V, _, ⟨e⟩⟩ := hF x
  let j := openInclusion O
  have hj : IsOpenEmbedding j := O.isOpenEmbedding
  let L := hj.functor
  let R := Opens.map j
  let G := (hj.sheafPullback Coeff.{u}).obj F
  let η : F.obj ⟶ (TopCat.Presheaf.pushforward Coeff.{u} j).obj G.obj :=
    Functor.whiskerRight (NatTrans.op hj.isOpenMap.adjunction.counit) F.obj
  let eG : G ≅ constant (TopCat.of O) V := (hj.sheafPullbackIso Coeff.{u}).symm.app F ≪≫ e
  have appIso (W : Opens X) (hW : W ≤ O) : IsIso (η.app (op W)) := by
    have he : L.obj (R.obj W) = W := (Opens.functor_map_eq_inf O W).trans (inf_eq_left.mpr hW)
    change IsIso (F.obj.map ((hj.isOpenMap.adjunction.counit.app W).op))
    have eq : hj.isOpenMap.adjunction.counit.app W = eqToHom he := Subsingleton.elim _ _
    rw [eq]
    infer_instance
  have : LocallyConnectedSpace O := O.isOpen.locallyConnectedSpace
  let x' : O := ⟨x, hxO⟩
  obtain ⟨B, ⟨hBo, hxB, hBc⟩, _⟩ :=
    (LocallyConnectedSpace.open_connected_basis x').mem_iff.mp (show Set.univ ∈ 𝓝 x' from univ_mem)
  let W' : Opens (TopCat.of O) := ⟨B, hBo⟩
  let W := L.obj W'
  refine ⟨W, ⟨x', hxB, rfl⟩, ?_⟩
  rintro _ ⟨y, hyW', rfl⟩
  have hyW : j y ∈ W := ⟨y, hyW', rfl⟩
  have hη : IsIso ((stalkFunctor Coeff.{u} (j y)).map η) :=
    isIso_stalkMap_of_cofinal η (j y) (fun U hU =>
      ⟨U ⊓ O, inf_le_left, ⟨hU, y.property⟩, appIso _ inf_le_right⟩)
  have hpush : IsIso (stalkPushforward Coeff.{u} j G.obj y) :=
    stalkPushforward.stalkPushforward_iso_of_isInducing Coeff.{u} hj.isInducing G.obj y
  have hηW : IsIso (η.app (op W)) := appIso W (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  have hW' : R.obj W = W' := Opens.map_functor_eq' j hj W'
  have hg : IsIso (germ G.obj (R.obj W) y hyW) := by
    apply isIso_germ_of_constant eG
    exact hW'.symm ▸ hBc
  apply (ConcreteCategory.isIso_iff_bijective _).mp
  rw [← isIso_comp_right_iff _ ((stalkFunctor Coeff.{u} (j y)).map η),
    stalkFunctor_map_germ, ← isIso_comp_right_iff _ (stalkPushforward Coeff.{u} j G.obj y),
    Category.assoc, stalkPushforward_germ]
  infer_instance

/-- A finite-rank locally constant rational sheaf on a simply connected and locally
path-connected space is constant with a finite coefficient module. -/
theorem locallyConstantFiniteRank_constant_of_simplyConnected {X : TopCat.{u}}
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (F : Sheaves X) (hF : LocallyConstantFiniteRank F) :
    ∃ V : Coeff.{u}, Module.Finite ℚ V ∧ Nonempty (constant X V ≅ F) := by
  let x : X := Classical.choice inferInstance
  let V := (stalk x).obj F
  have hg (y : X) : IsIso (germ F.obj ⊤ y trivial) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (globalGerm_bijective_of_covering F (etaleSpace_isCoveringMap_of_locallyConstant F hF) y)
  let a : V ⟶ F.obj.obj (op ⊤) := inv (germ F.obj ⊤ x trivial)
  let τ : constantPresheaf X V ⟶ F.obj :=
    { app := fun U => a ≫ F.obj.map ((homOfLE (le_top : U.unop ≤ ⊤)).op)
      naturality := by
        intro U W g
        change 𝟙 V ≫ _ = _
        rw [Category.id_comp, Category.assoc, ← F.obj.map_comp]
        congr }
  let φ : constant X V ⟶ F := ⟨sheafifyLift _ τ F.property⟩
  have hτ : constSection X V ⊤ ≫ φ.hom.app (op ⊤) = a := by
    have h := congrArg (fun e : constantPresheaf X V ⟶ F.obj => e.app (op ⊤))
      (toSheafify_sheafifyLift _ τ F.property)
    refine h.trans ?_
    change a ≫ F.obj.map ((homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op) = a
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)) (𝟙 _)]
    simp
  have hφ : IsIso φ := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro y
    let b := stalkFunctor Coeff.{u} y
    change IsIso (b.map φ.hom)
    have hc : IsIso (constSection X V ⊤ ≫ germ (constant X V).obj ⊤ y trivial) := by
      rw [← isIso_comp_right_iff _ (constantGermIso X V y).hom, Category.assoc, constSection_germ]
      infer_instance
    rw [← isIso_comp_left_iff (constSection X V ⊤ ≫ germ (constant X V).obj ⊤ y trivial),
      Category.assoc, stalkFunctor_map_germ, ← Category.assoc, hτ]
    dsimp [a]
    infer_instance
  refine ⟨V, ?_, ⟨asIso φ⟩⟩
  obtain ⟨O, hxO, W, hW, ⟨eW⟩⟩ := hF x
  let y : TopCat.of O := ⟨x, hxO⟩
  let eV : V ≅ W := inverseImageStalkIso (openInclusion O) F y ≪≫
    (stalk (X := TopCat.of O) y).mapIso eW ≪≫ constantGermIso (TopCat.of O) W y
  exact Module.Finite.equiv eV.toLinearEquiv.symm

private theorem convex_locallyPathConnected [Fintype σ] {S : Set (σ → ℝ)} (hS : Convex ℝ S) :
    LocallyPathConnectedSpace S := by
  refine LocallyPathConnectedSpace.of_bases (fun x : S => Metric.nhds_basis_ball) ?_
  intro x r hr
  let A := Metric.ball x.val r ∩ S
  let m : A → S := Set.inclusion (show A ⊆ S from inter_subset_right)
  have hm : Continuous m := continuous_subtype_val.subtype_mk _
  have hA : A.Nonempty := ⟨x.val, Metric.mem_ball_self hr, x.property⟩
  have hconv : Convex ℝ A := (convex_ball _ _).inter hS
  have hc : IsPathConnected (Set.range m) := by
    have : PathConnectedSpace A := isPathConnected_iff_pathConnectedSpace.mp (hconv.isPathConnected hA)
    simpa only [Set.image_univ] using (@isPathConnected_univ A _ _).image hm
  have he : Set.range m = Metric.ball x r := by
    ext y
    change (∃ a : A, m a = y) ↔ dist y.val x.val < r
    exact ⟨fun ⟨a, e⟩ => by rw [← e]; exact a.property.1,
      fun hy => ⟨⟨y.val, hy, y.property⟩, Subtype.ext rfl⟩⟩
  exact he ▸ hc

/-- Local systems on an open simplex are trivial, with the same finite-rank condition. -/
theorem constant_on_faceInterior [Fintype σ] {s : Finset (σ → ℝ)} (hs : s.Nonempty)
    (F : Sheaves (TopCat.of (faceInterior s))) (hF : LocallyConstantFiniteRank F) :
    ∃ V : Coeff.{u}, Module.Finite ℚ V ∧ Nonempty (constant (TopCat.of (faceInterior s)) V ≅ F) := by
  have hne : (faceInterior s).Nonempty :=
    Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _)
      ((show (s : Set (σ → ℝ)).Nonempty from hs).mono (subset_convexHull ℝ _))
  have hS := convex_faceInterior s
  have : ContractibleSpace (TopCat.of (faceInterior s)) := hS.contractibleSpace hne
  have : LocallyPathConnectedSpace (TopCat.of (faceInterior s)) := convex_locallyPathConnected hS
  exact locallyConstantFiniteRank_constant_of_simplyConnected F hF

/-- Cofinal vanishing on inverse images of neighborhoods implies vanishing of the
cohomology sheaf of the actual bounded-below derived direct image. -/
theorem directImageCohomology_isZero_of_cofinal {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : BoundedBelow X) (q : ℤ) :
    let P := (Opens.map f).op ⋙ LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves X)) F q
    (∀ (y : Y) (U : Opens Y), y ∈ U → ∃ W : Opens Y, W ≤ U ∧ y ∈ W ∧
      IsZero (P.obj (op W))) →
    IsZero ((cohomology Y q).obj ((derivedDirectImage f).obj F).obj) := by
  dsimp only
  let P : Y.Presheaf Coeff.{u} :=
    (Opens.map f).op ⋙ LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves X)) F q
  intro h
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro y
  obtain ⟨e⟩ := DerivedLocalSheaves.higherDirectImageStalk f y q F
  refine IsZero.of_iso ?_ e
  change IsZero (P.stalk y)
  have hz (a : P.stalk y) : a = 0 := by
    obtain ⟨U, hyU, s, hs⟩ := P.exists_germ_eq a
    obtain ⟨W, hWU, hyW, hW⟩ := h y U hyU
    let i : W ⟶ U := homOfLE hWU
    have hi : P.map i.op = 0 := hW.eq_of_tgt _ _
    rw [← hs, ← germ_res_apply P i y hyW, hi]
    simp
  have : Subsingleton (P.stalk y) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Composition for the actual bounded-below derived direct images. -/
def derivedDirectImageComposition {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedDirectImage f ⋙ derivedDirectImage g ≅ derivedDirectImage (f ≫ g) := by
  let i := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := Sheaves X))).whiskeringRight (BoundedBelow Z)
  let e : boundedBelowInverseImage (f ≫ g) ≅ boundedBelowInverseImage g ⋙ boundedBelowInverseImage f :=
    i.preimageIso (Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := Sheaves Z))
      (derivedInverseImageComposition f g))
  exact (((DerivedLocalSheaves.derivedInverseDirectAdjunctionData g).comp
      (DerivedLocalSheaves.derivedInverseDirectAdjunctionData f)).ofNatIsoLeft e.symm).rightAdjointUniq
    (DerivedLocalSheaves.derivedInverseDirectAdjunctionData (f ≫ g))

open private mappedStalkIso from
  MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison in
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty in
/-- The actual direct image of a degree-zero sheaf with vanishing positive higher
direct images agrees with its ordinary pushforward placed in degree zero. -/
def derivedDirectImage_singleIso_of_positiveVanishing {X Y : TopCat.{u}}
    (f : X ⟶ Y) (F : Sheaves X)
    (h : ∀ n : ℕ, IsZero ((cohomology Y (n + 1 : ℕ)).obj
      ((derivedDirectImage f).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((directImage f).obj F) ≅
      (derivedDirectImage f).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) := by
  let T := directImage f
  let stalk := HomotopyCategory.Plus.singleFunctor (Sheaves X) 0
  let i := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := Sheaves X))).whiskeringRight (Sheaves X)
  let j := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := Sheaves Y))).whiskeringRight (Sheaves X)
  let e : stalk ⋙ DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.singleFunctor _ 0 :=
    i.preimageIso (DerivedCategory.singleFunctorIsoCompQh (Sheaves X) 0).symm
  let d : T ⋙ DerivedCategory.Plus.singleFunctor _ 0 ≅ stalk ⋙ plusUValue T :=
    j.preimageIso (mappedStalkIso T).symm
  have hA : rightAcyclicValue T F := by
    apply (AdvancedHomologicalAlgebra.AcyclicTermComparison.rightVanishing
      (Sheaves X) (Sheaves Y) T F).mpr
    intro n
    exact (h n).of_iso ((DerivedCategory.Plus.homologyFunctor (Sheaves Y) (n + 1 : ℕ)).mapIso
      (T.rightDerivedFunctorPlus.mapIso (e.app F)))
  have : IsIso (T.rightDerivedFunctorPlusUnith.app (stalk.obj F)) := hA
  exact d.app F ≪≫ asIso (T.rightDerivedFunctorPlusUnith.app (stalk.obj F)) ≪≫
    T.rightDerivedFunctorPlus.mapIso (e.app F)

/-- Local representatives of sections of the sheafification of a presheaf of rational
modules can be chosen with equality after restriction as sections. -/
theorem exists_localRepresentative {X : TopCat.{u}} (P : X.Presheaf Coeff.{u}) (U : Opens X)
    (s : (sheafify (Opens.grothendieckTopology X) P).obj (op U))
    (x : X) (hx : x ∈ U) :
    let η := toSheafify (Opens.grothendieckTopology X) P
    let Q := sheafify (Opens.grothendieckTopology X) P
    ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
      ∃ t : P.obj (op V), η.app (op V) t = Q.map i.op s := by
  dsimp only
  let η := toSheafify (Opens.grothendieckTopology X) P
  let Q : X.Presheaf Coeff.{u} := sheafify (Opens.grothendieckTopology X) P
  have h : IsIso ((stalkFunctor Coeff.{u} x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  obtain ⟨b, hb⟩ := (ConcreteCategory.isIso_iff_bijective _).mp h |>.surjective (Q.germ U x hx s)
  obtain ⟨W, hxW, t, ht⟩ := P.exists_germ_eq b
  rw [← ht, stalkFunctor_map_germ_apply] at hb
  obtain ⟨V, hxV, i, j, he⟩ := Q.germ_eq x hxW hx _ _ hb
  refine ⟨V, j, hxV, P.map i.op t, ?_⟩
  rw [← he]
  exact η.naturality_apply i.op t

open P202Specs.CohomologyPairs in
/-- Singular cochains with the actual pullback of cochains under inclusions of opens,
viewed as a cochain complex of presheaves. -/
def singularCochainPresheaves (X : TopCat.{u}) (V : Coeff.{u}) :
    CochainComplex (X.Presheaf Coeff.{u}) ℤ := by
  let C := (Opens.toTopCat X).op ⋙ ordinaryCochainFunctor ℚ V
  exact
    { X := fun q => C ⋙ HomologicalComplex.eval _ _ q
      d := fun i j =>
        { app := fun U => (C.obj U).d i j
          naturality := fun _ _ g => (C.map g).comm i j }
      shape := fun i j h =>
        NatTrans.ext (by funext U; exact (C.obj U).shape i j h)
      d_comp_d' := fun i j k _ _ =>
        NatTrans.ext (by funext U; exact (C.obj U).d_comp_d i j k) }

/-- The degreewise sheafification of the singular cochain presheaves. -/
def singularCochainSheaves (X : TopCat.{u}) (V : Coeff.{u}) :
    CochainComplex (Sheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (singularCochainPresheaves X V)

theorem singularCochainSheaves_isStrictlyGE (X : TopCat.{u}) (V : Coeff.{u}) :
    (singularCochainSheaves X V).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  change IsZero (T.obj ((singularCochainPresheaves X V).X q))
  apply T.map_isZero
  apply Functor.isZero
  intro U
  exact (P202.CohomologyPairs.negative ℚ V).1 ((Opens.toTopCat X).obj U.unop) q hq |>.1

open P202Specs.SingularChains P202Specs.CohomologyPairs

private abbrev stdSimplexSpace (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- Evaluation on affine singular simplices identifies the cochains with functions
on continuous maps from the standard simplex. -/
def singularCochainFunctionEquiv {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (n : ℕ) :
    ((singularCochainPresheaves X V).X (n : ℤ)).obj (op U) ≃ (C(stdSimplexSpace n, U) → V) :=
  (ordinaryCochainsEquiv ℚ V (TopCat.of U) n).toEquiv.trans
    ((Finsupp.lift V ℚ (Simplex (TopCat.of U) n)).symm.toEquiv.trans
      ((simplexEquiv (TopCat.of U) n).arrowCongr (Equiv.refl V)))

theorem singularCochainFunction_restrict {X : TopCat.{u}} (V : Coeff.{u})
    (n : ℕ) {U W : Opens X} (g : U ⟶ W)
    (a : ((singularCochainPresheaves X V).X (n : ℤ)).obj (op W))
    (s : C(stdSimplexSpace n, U)) :
    singularCochainFunctionEquiv V U n (((singularCochainPresheaves X V).X (n : ℤ)).map g.op a) s =
      singularCochainFunctionEquiv V W n a (((Opens.toTopCat X).map g).hom.comp s) := by
  let f : TopCat.of U ⟶ TopCat.of W := (Opens.toTopCat X).map g
  let t := (simplexEquiv (TopCat.of U) n).symm s
  have ht : (simplexEquiv (TopCat.of W) n).symm (f.hom.comp s) =
      ((TopCat.toSSet.map f).app _) t := by
    apply (simplexEquiv (TopCat.of W) n).injective
    calc
      _ = f.hom.comp s := Equiv.apply_symm_apply _ _
      _ = f.hom.comp (simplexEquiv (TopCat.of U) n t) :=
        congrArg (f.hom.comp ·) (Equiv.apply_symm_apply _ _).symm
      _ = _ := (P202.SingularChains.simplexEquiv_postcomp f n t).symm
  let u := ordinaryNonnegativeIso ℚ ℚ (TopCat.of U) n
  let w := ordinaryNonnegativeIso ℚ ℚ (TopCat.of W) n
  have he : u.inv ≫ ((ordinaryFunctor ℚ ℚ).map f).f (n : ℤ) =
      (chainMap ℚ ℚ f).f n ≫ w.inv := by
    change u.inv ≫ (HomologicalComplex.extendMap (chainMap ℚ ℚ f) (degreeEmbedding 0)).f _ = _
    rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by
      change (0 : ℤ) + n = n; omega)]
    change u.inv ≫ (u.hom ≫ (chainMap ℚ ℚ f).f n ≫ w.inv) = _
    rw [Iso.inv_hom_id_assoc]
  let b : (ordinaryComplex ℚ ℚ (TopCat.of W)).X (n : ℤ) →ₗ[ℚ] V := a
  change b
      ((u.inv ≫ ((ordinaryFunctor ℚ ℚ).map f).f (n : ℤ)) (Finsupp.single t 1)) =
    b (w.inv (Finsupp.single ((simplexEquiv (TopCat.of W) n).symm (f.hom.comp s)) 1))
  have hb := P202.SingularChains.chainMap_single ℚ ℚ f n t 1
  have hb' : (chainMap ℚ ℚ f).f n (Finsupp.single t 1) =
      Finsupp.single (((TopCat.toSSet.map f).app _) t) 1 := hb
  rw [he, ConcreteCategory.comp_apply, ht, hb']
  rfl

private abbrev openMap {X : TopCat.{u}} {U W : Opens X} (g : U ⟶ W) : C(U, W) :=
  ((Opens.toTopCat X).map g).hom

private theorem cochainRestrictions_agree {X : TopCat.{u}} (P : X.Presheaf Coeff.{u})
    {U W B N : Opens X} (a : P.obj (op U)) (b : P.obj (op W)) (i : B ⟶ U) (j : B ⟶ W)
    (h : P.map i.op a = P.map j.op b) (k : N ⟶ B) (l : N ⟶ U) (m : N ⟶ W) :
    P.map l.op a = P.map m.op b := by
  rw [Subsingleton.elim l (k ≫ i), Subsingleton.elim m (k ≫ j), op_comp, op_comp,
    Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]

set_option maxHeartbeats 1000000 in
/-- On metric spaces, every section of the sheafified singular cochain presheaf is
represented by an ordinary cochain. A locally finite shrinking makes the choices
on the individual simplices agree near each point. -/
theorem singularCochainSection_surjective (X : Type u) [MetricSpace X] (V : Coeff.{u})
    (U : Opens (TopCat.of X)) (n : ℕ) :
    Function.Surjective
      ((toSheafify (Opens.grothendieckTopology (TopCat.of X))
        ((singularCochainPresheaves (TopCat.of X) V).X (n : ℤ))).app (op U)) := by
  classical
  let P : (TopCat.of X).Presheaf Coeff.{u} := (singularCochainPresheaves (TopCat.of X) V).X (n : ℤ)
  let Q : Sheaves (TopCat.of X) := (presheafToSheaf (Opens.grothendieckTopology (TopCat.of X)) _).obj P
  let η := toSheafify (Opens.grothendieckTopology (TopCat.of X)) P
  intro s
  choose N i hm a ha using fun x : U =>
    exists_localRepresentative P U s x.val x.property
  let T (x : U) : Set U := Subtype.val ⁻¹' (N x : Set (TopCat.of X))
  have hTo (x : U) : IsOpen (T x) := (N x).isOpen.preimage continuous_subtype_val
  have hTc : ⋃ x, T x = Set.univ := iUnion_eq_univ_iff.mpr fun x => ⟨x, hm x⟩
  obtain ⟨A', hAo', hAc', hAl', hAT⟩ := precise_refinement T hTo hTc
  obtain ⟨B, hcover, hBo, hBA⟩ := exists_iUnion_eq_closure_subset hAo' hAl'.point_finite hAc'
  let I := U
  let c : I → U := id
  have hB : LocallyFinite B := hAl'.subset fun j => subset_closure.trans (hBA j)
  have hBN (j : I) (x : U) (hx : x ∈ closure (B j)) : x.val ∈ N (c j) := hAT j (hBA j hx)
  let fits (b : C(stdSimplexSpace n, U)) (j : I) : Prop := ∀ y, b y ∈ B j
  let lift (b : C(stdSimplexSpace n, U)) (j : I) (hb : fits b j) :
      C(stdSimplexSpace n, N (c j)) :=
    ⟨fun y => ⟨(b y).val, hBN j (b y) (subset_closure (hb y))⟩,
      (continuous_subtype_val.comp b.continuous).subtype_mk _⟩
  let value (b : C(stdSimplexSpace n, U)) : V :=
    if h : ∃ j, fits b j then
      singularCochainFunctionEquiv V (N (c h.choose)) n (a (c h.choose))
        (lift b h.choose h.choose_spec)
    else 0
  let t : P.obj (op U) := (singularCochainFunctionEquiv V U n).symm value
  refine ⟨t, ?_⟩
  apply section_ext Q U
  intro x hx
  let x' : U := ⟨x, hx⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, x' ∈ B j := by
    have he : x' ∈ ⋃ j, B j := hcover.symm ▸ Set.mem_univ x'
    exact Set.mem_iUnion.mp he
  let J := {j : I | x' ∈ closure (B j)}
  have hJ : J.Finite := hB.closure.point_finite x'
  let hj₀' := hBN j₀ x' (subset_closure hj₀)
  have agree (j : J) :
      P.germ (N (c j.val)) x (hBN j.val x' j.property) (a (c j.val)) =
        P.germ (N (c j₀)) x hj₀' (a (c j₀)) := by
    have hη := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
    apply ((ConcreteCategory.isIso_iff_bijective _).mp hη).1
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, ha, ha,
      germ_res_apply, germ_res_apply]
  choose D hDx l k he using fun j : J => P.germ_eq x (hBN j.val x' j.property) hj₀'
    (a (c j.val)) (a (c j₀)) (agree j)
  have := hJ.to_subtype
  have near : ∀ᶠ y : U in 𝓝 x', y ∈ B j₀ ∧
      (∀ j, y ∈ B j → j ∈ J) ∧ (∀ j : J, y.val ∈ D j) := by
    have hj₀n : ∀ᶠ y in 𝓝 x', y ∈ B j₀ := (hBo j₀).mem_nhds hj₀
    refine hj₀n.and ?_
    refine ((hB.closure.eventually_subset (fun _ => isClosed_closure) x').mono
      (fun y hy j hj => hy (subset_closure hj))).and ?_
    exact Filter.eventually_all.mpr fun j => ((D j).isOpen.preimage continuous_subtype_val).mem_nhds (hDx j)
  obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp near
  let O : Opens (TopCat.of U) := ⟨A, hAo⟩
  let W := U.isOpenEmbedding.functor.obj O
  have hWx : x ∈ W := ⟨x', hxA, rfl⟩
  have hWU : W ≤ U := by rintro _ ⟨y, _, rfl⟩; exact y.property
  let g : W ⟶ U := homOfLE hWU
  have good (y : W) : openMap g y ∈ B j₀ ∧
      (∀ j, openMap g y ∈ B j → j ∈ J) ∧ (∀ j : J, y.val ∈ D j) := by
    obtain ⟨z, hz, e⟩ := y.property
    change z.val = y.val at e
    have ez : openMap g y = z := Subtype.ext e.symm
    rw [ez, ← e]
    exact hA hz
  let g₀ : W ⟶ N (c j₀) := homOfLE fun y hy =>
    hBN j₀ ⟨y, hWU hy⟩ (subset_closure (good ⟨y, hy⟩).1)
  have hrestrict : P.map g.op t = P.map g₀.op (a (c j₀)) := by
    apply (singularCochainFunctionEquiv V W n).injective
    funext b
    erw [singularCochainFunction_restrict V n g t b, singularCochainFunction_restrict V n g₀ _ b]
    let bU := (openMap g).comp b
    have hfit : ∃ j, fits bU j := ⟨j₀, fun y => (good (b y)).1⟩
    change singularCochainFunctionEquiv V U n t bU =
      singularCochainFunctionEquiv V (N (c j₀)) n (a (c j₀)) ((openMap g₀).comp b)
    change (singularCochainFunctionEquiv V U n) ((singularCochainFunctionEquiv V U n).symm value) bU = _
    rw [Equiv.apply_symm_apply]
    dsimp only [value]
    rw [dite_eq_left hfit]
    let z : stdSimplexSpace n := Convexity.StdSimplex.single (0 : Fin (n + 1))
    let j : J := ⟨hfit.choose, (good (b z)).2.1 _ (hfit.choose_spec z)⟩
    let d : W ⟶ D j := homOfLE fun y hy => (good ⟨y, hy⟩).2.2 j
    let g₁ : W ⟶ N (c j.val) := d ≫ l j
    have hEq := cochainRestrictions_agree P _ _ (l j) (k j) (he j) d g₁ g₀
    have hEval := congrArg (fun co => singularCochainFunctionEquiv V W n co b) hEq
    erw [singularCochainFunction_restrict V n g₁ _ b, singularCochainFunction_restrict V n g₀ _ b] at hEval
    have hb : (openMap g₁).comp b = lift bU hfit.choose hfit.choose_spec := by
      ext y
      rfl
    exact (congrArg (singularCochainFunctionEquiv V (N (c j.val)) n (a (c j.val))) hb).symm.trans hEval
  apply germ_ext Q.obj (hxU := hx) (hxV := hx) W hWx g (g₀ ≫ i (c j₀))
  calc
    Q.obj.map g.op (η.app (op U) t) = η.app (op W) (P.map g.op t) :=
      (η.naturality_apply g.op t).symm
    _ = η.app (op W) (P.map g₀.op (a (c j₀))) := congrArg (η.app (op W)) hrestrict
    _ = Q.obj.map g₀.op (η.app (op (N (c j₀))) (a (c j₀))) := η.naturality_apply g₀.op (a (c j₀))
    _ = Q.obj.map (g₀ ≫ i (c j₀)).op s := by
      rw [ha, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains in
/-- A singular cochain on a smaller open extends to the larger open in each degree. -/
theorem singularCochainRestriction_surjective {X : TopCat.{u}} (V : Coeff.{u})
    (q : ℤ) {U W : Opens X} (g : U ⟶ W) :
    Function.Surjective (((singularCochainPresheaves X V).X q).map g.op) := by
  let P : Pair.{u} := ⟨TopCat.of W, Subtype.val ⁻¹' (U : Set X)⟩
  let e : TopCat.of U ≅ P.sub := TopCat.isoOfHomeo
    { toFun := fun x => ⟨⟨x.val, g.le x.property⟩, x.property⟩
      invFun := fun z => ⟨z.val.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let C := ordinaryCochainFunctor ℚ V ⋙ HomologicalComplex.eval _ _ q
  have hcomp : e.hom ≫ P.inclusion = (Opens.toTopCat X).map g := rfl
  change Function.Surjective (C.map ((Opens.toTopCat X).map g).op)
  rw [← hcomp, op_comp, Functor.map_comp]
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (Functor.map_isIso C e.hom.op)).2.comp (P202.CohomologyPairs.restriction_surjective ℚ V P q)

/-- Degreewise surjectivity from ordinary cochains to sheafified sections implies
flasqueness of those sheaves by degreewise extension of singular cochains. -/
theorem singularCochainSheaves_isFlasque_of_sectionSurjectivity (X : TopCat.{u}) (V : Coeff.{u})
    (q : ℤ) (h : ∀ U : Opens X, Function.Surjective
      ((toSheafify (Opens.grothendieckTopology X) ((singularCochainPresheaves X V).X q)).app (op U))) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheaves X V).X q) := by
  let F := (singularCochainPresheaves X V).X q
  let η := toSheafify (Opens.grothendieckTopology X) F
  constructor
  intro U W i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨t, ht⟩ := h W.unop s
  obtain ⟨b, hb⟩ := singularCochainRestriction_surjective V q i.unop t
  have hb' : F.map i b = t := hb
  refine ⟨η.app U b, ?_⟩
  change (sheafify (Opens.grothendieckTopology X) F).map i (η.app U b) = s
  exact (η.naturality_apply i b).symm.trans ((congrArg (η.app W) hb').trans ht)

theorem singularCochainSheaves_isFlasque (X : Type u) [MetricSpace X] (V : Coeff.{u}) (q : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheaves (TopCat.of X) V).X q) := by
  apply singularCochainSheaves_isFlasque_of_sectionSurjectivity
  intro U
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact singularCochainSection_surjective X V U n
  · have hzero : IsZero (((singularCochainSheaves (TopCat.of X) V).X q).obj.obj (op U)) := by
      have h := singularCochainSheaves_isStrictlyGE (TopCat.of X) V
      let A := (singularCochainSheaves (TopCat.of X) V).X q
      have hA : IsZero A :=
        (singularCochainSheaves (TopCat.of X) V).isZero_of_isStrictlyGE 0 q (lt_of_not_ge hq)
      rw [IsZero.iff_id_eq_zero]
      exact congrArg (fun f : A ⟶ A => f.hom.app (op U)) ((IsZero.iff_id_eq_zero A).mp hA)
    exact fun x => ⟨0, (ModuleCat.subsingleton_of_isZero hzero).elim _ _⟩

/-- Over a field a linear map that vanishes on the kernel of another map factors
through that map, with its factor extended to the entire target. -/
private theorem exists_linearMap_factor {A B V : Type u} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [AddCommGroup V] [Module ℚ V]
    (g : A →ₗ[ℚ] B) (a : A →ₗ[ℚ] V) (h : LinearMap.ker g ≤ LinearMap.ker a) :
    ∃ b : B →ₗ[ℚ] V, b.comp g = a := by
  let S := LinearMap.range g
  have h' : LinearMap.ker g.rangeRestrict ≤ LinearMap.ker a := by
    rwa [LinearMap.ker_rangeRestrict]
  obtain ⟨r, hr⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let l := g.rangeRestrict.liftOfSurjective g.surjective_rangeRestrict ⟨a, h'⟩
  refine ⟨l.comp r, ?_⟩
  apply LinearMap.ext
  intro x
  have er : r (g x) = g.rangeRestrict x :=
    LinearMap.congr_fun hr (g.rangeRestrict x)
  change l (r (g x)) = a x
  rw [er]
  exact LinearMap.equivOfSurjective_apply g.surjective_rangeRestrict h'

private theorem dual_isExactAt_of_isExactAt (V : Coeff.{u})
    (K : ChainComplex Coeff.{u} ℤ) (q : ℤ) (h : K.ExactAt q) :
    ((dualComplexFunctor ℚ V (ComplexShape.down ℤ)).obj (op K)).ExactAt q := by
  let C : CochainComplex Coeff.{u} ℤ := (dualComplexFunctor ℚ V (ComplexShape.down ℤ)).obj (op K)
  change C.ExactAt q
  have hK := (K.exactAt_iff' (q + 1) q (q - 1) (by simp) (by simp)).mp h
  rw [C.exactAt_iff' (q - 1) q (q + 1) (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro a ha
  let a' : K.X q →ₗ[ℚ] V := a
  change a'.comp (K.d (q + 1) q).hom = 0 at ha
  have hap (x : K.X (q + 1)) : a' ((K.d (q + 1) q) x) = 0 :=
    LinearMap.congr_fun ha x
  have ha' : LinearMap.ker (K.d q (q - 1)).hom ≤ LinearMap.ker a' := by
    intro x hx
    obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).mp hK x hx
    exact hap y
  exact exists_linearMap_factor (K.d q (q - 1)).hom a' ha'

private theorem singularCohomology_isZero_pos_of_contractible (X : TopCat.{u})
    [Nonempty X] [ContractibleSpace X] (V : Coeff.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (ordinaryCohomology ℚ V X (q : ℤ)) := by
  have h := (P202.SingularDegreeZero.reducedPositiveIso ℚ ℚ X q hq).isZero_iff.mp
    (P202.PrismHomotopy.contractible ℚ ℚ X (q : ℤ))
  exact (dual_isExactAt_of_isExactAt V _ _ ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h)).isZero_homology

private abbrev cochainDual {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (n : ℕ) :
    ((singularCochainPresheaves X V).X (n : ℤ)).obj (op U) ≃ₗ[ℚ] (Chains ℚ (TopCat.of U) n →ₗ[ℚ] V) :=
  ordinaryCochainsEquiv ℚ V (TopCat.of U) n

private theorem cochainDual_boundary {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (n : ℕ)
    (a : ((singularCochainPresheaves X V).X (n : ℤ)).obj (op U)) :
    cochainDual V U (n+1) (((singularCochainPresheaves X V).d (n : ℤ) ((n+1 : ℕ) : ℤ)).app (op U) a) =
      (cochainDual V U n a).comp (boundary ℚ ℚ (TopCat.of U) n) := by
  let T := TopCat.of U
  let l : (ordinaryComplex ℚ ℚ T).X (n : ℤ) →ₗ[ℚ] V := a
  let i := ordinaryNonnegativeIso ℚ ℚ T n
  let j := ordinaryNonnegativeIso ℚ ℚ T (n+1)
  apply LinearMap.ext
  intro c
  change l ((j.inv ≫ (ordinaryComplex ℚ ℚ T).d ((n+1 : ℕ) : ℤ) (n : ℤ)) c) =
    l (((complex ℚ ℚ T).d (n+1) n ≫ i.inv) c)
  have e : j.inv ≫ (ordinaryComplex ℚ ℚ T).d ((n+1 : ℕ) : ℤ) (n : ℤ) =
      (complex ℚ ℚ T).d (n+1) n ≫ i.inv := by
    apply (cancel_mono i.hom).mp
    rw [Category.assoc, P202.SingularChains.ordinary_boundary, Category.assoc, i.inv_hom_id, Category.comp_id]
  rw [e]

private theorem cochainFunction_eval {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (n : ℕ)
    (a : ((singularCochainPresheaves X V).X (n : ℤ)).obj (op U))
    (s : Simplex (TopCat.of U) n) :
    singularCochainFunctionEquiv V U n a (simplexEquiv (TopCat.of U) n s) =
      cochainDual V U n a (Finsupp.single s 1) := by
  change cochainDual V U n a
    (Finsupp.single ((simplexEquiv (TopCat.of U) n).symm (simplexEquiv (TopCat.of U) n s)) 1) = _
  rw [Equiv.symm_apply_apply]

private theorem exists_zero_restriction_cover {X : TopCat.{u}} (P : X.Presheaf Coeff.{u})
    (U : Opens X) (a : P.obj (op U))
    (ha : (toSheafify (Opens.grothendieckTopology X) P).app (op U) a = 0) :
    ∃ B : U → Opens X, ∃ i : ∀ x, B x ⟶ U,
      (∀ x : U, x.val ∈ B x) ∧ (∀ x, P.map (i x).op a = 0) := by
  let η := toSheafify (Opens.grothendieckTopology X) P
  let Q : X.Presheaf Coeff.{u} := sheafify (Opens.grothendieckTopology X) P
  have ex (x : U) : ∃ (B : Opens X) (i : B ⟶ U), x.val ∈ B ∧ P.map i.op a = 0 := by
    have hη := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x.val _ P
    have hg : P.germ U x.val x.property a = P.germ U x.val x.property 0 := by
      apply ((ConcreteCategory.isIso_iff_bijective _).mp hη).1
      rw [stalkFunctor_map_germ_apply U x.val x.property η,
        stalkFunctor_map_germ_apply U x.val x.property η, ha]
      simp
    obtain ⟨B, hxB, i, _, h⟩ := P.germ_eq x.val x.property x.property a 0 hg
    exact ⟨B, i, hxB, h.trans (map_zero _)⟩
  choose B i hx h using ex
  exact ⟨B, i, hx, h⟩

private theorem sheafifySection_eq_of_restrict_eq {X : TopCat.{u}} (P : X.Presheaf Coeff.{u})
    (U : Opens X) (a b : P.obj (op U))
    (B : U → Opens X) (i : ∀ x, B x ⟶ U) (hx : ∀ x : U, x.val ∈ B x)
    (h : ∀ x, P.map (i x).op a = P.map (i x).op b) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op U) a =
      (toSheafify (Opens.grothendieckTopology X) P).app (op U) b := by
  let η := toSheafify (Opens.grothendieckTopology X) P
  let Q : Sheaves X := (presheafToSheaf (Opens.grothendieckTopology X) _).obj P
  apply section_ext Q U
  intro y hy
  let x : U := ⟨y, hy⟩
  apply germ_ext Q.obj (B x) (hx x) (i x) (i x)
  rw [← η.naturality_apply, ← η.naturality_apply, h]

open P202Specs.SmallChainHomology

private def coverOfOpenRestriction {X : TopCat.{u}} (U : Opens X) (B : U → Opens X)
    (hx : ∀ x : U, x.val ∈ B x) : OpenCover (TopCat.of U) U where
  sets x := Subtype.val ⁻¹' (B x : Set X)
  isOpen x := (B x).isOpen.preimage continuous_subtype_val
  covers x := ⟨x, hx x⟩

private theorem cochainFunction_zero {X : TopCat.{u}} (U : Opens X) (V : Coeff.{u}) (n : ℕ)
    (s : C(stdSimplexSpace n, U)) :
    singularCochainFunctionEquiv V U n 0 s = 0 := by
  change cochainDual V U n 0 (Finsupp.single ((simplexEquiv (TopCat.of U) n).symm s) 1) = 0
  rw [map_zero]
  rfl

private theorem cochainDual_kills_small_iff {X : TopCat.{u}} (U : Opens X) (V : Coeff.{u}) (n : ℕ)
    (t : ((singularCochainPresheaves X V).X (n : ℤ)).obj (op U))
    (B : U → Opens X) (i : ∀ x, B x ⟶ U) (hx : ∀ x : U, x.val ∈ B x) :
    smallModule ℚ (coverOfOpenRestriction U B hx) n ≤ LinearMap.ker (cochainDual V U n t) ↔
      ∀ x, ((singularCochainPresheaves X V).X (n : ℤ)).map (i x).op t = 0 := by
  let C := (singularCochainPresheaves X V).X (n : ℤ)
  let S := coverOfOpenRestriction U B hx
  constructor
  · intro h x
    apply (singularCochainFunctionEquiv V (B x) n).injective
    funext b
    rw [cochainFunction_zero, singularCochainFunction_restrict V n (i x)]
    let s := (simplexEquiv (TopCat.of U) n).symm ((openMap (i x)).comp b)
    have hs : simplexEquiv (TopCat.of U) n s = (openMap (i x)).comp b := Equiv.apply_symm_apply _ _
    have hr : Set.range (simplexEquiv (TopCat.of U) n s) ⊆ S.sets x := by
      rw [hs]
      rintro _ ⟨z, rfl⟩
      exact (b z).property
    have hm : Finsupp.single s (1 : ℚ) ∈ smallModule ℚ S n :=
      Finsupp.single_mem_supported ℚ _ ⟨x, hr⟩
    rw [← hs, cochainFunction_eval]
    exact h hm
  · intro h
    change Finsupp.supported ℚ ℚ _ ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, ⟨x, hs⟩, rfl⟩
    let f := simplexEquiv (TopCat.of U) n s
    let b : C(stdSimplexSpace n, B x) :=
      ⟨fun z => ⟨(f z).val, hs ⟨z, rfl⟩⟩, (continuous_subtype_val.comp f.continuous).subtype_mk _⟩
    have eq : (openMap (i x)).comp b = f := by ext z; rfl
    have ev := singularCochainFunction_restrict V n (i x) t b
    rw [h x, cochainFunction_zero, eq] at ev
    change cochainDual V U n t (Finsupp.single s 1) = 0
    rw [← cochainFunction_eval]
    exact ev.symm

private abbrev cochainUnit {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (q : ℤ) :
    ((singularCochainPresheaves X V).X q).obj (op U) ⟶
      ((singularCochainSheaves X V).X q).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology X) ((singularCochainPresheaves X V).X q)).app (op U)

private abbrev singularCochainSections {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) :
    CochainComplex Coeff.{u} ℤ :=
  ((sectionsOn (X := X) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj (singularCochainSheaves X V)

private theorem cochainUnit_comm {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X) (q r : ℤ)
    (a : ((singularCochainPresheaves X V).X q).obj (op U)) :
    cochainUnit V U r (((singularCochainPresheaves X V).d q r).app (op U) a) =
      (singularCochainSections V U).d q r (cochainUnit V U q a) := by
  let η := (singularCochainPresheaves X V).d q r
  have h := congrArg (fun t => t.app (op U)) (toSheafify_naturality (Opens.grothendieckTopology X) η)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) a

set_option maxHeartbeats 900000 in
/-- The sections of the cochain sheaves on a contractible open are exact in positive
degrees. The small-chain comparison supplies primitives after shrinking the cover. -/
theorem singularCochainSections_exact_pos (X : Type u) [MetricSpace X] (V : Coeff.{u})
    (U : Opens (TopCat.of X)) [ContractibleSpace (TopCat.of U)] (k : ℕ) :
    (singularCochainSections V U).ExactAt ((k+1 : ℕ) : ℤ) := by
  let q : ℤ := ((k+1 : ℕ) : ℤ)
  let P := singularCochainPresheaves (TopCat.of X) V
  let S := singularCochainSections V U
  have hp : (ComplexShape.up ℤ).prev q = (k : ℤ) := by simp [q]
  have hn : (ComplexShape.up ℤ).next q = ((k+2 : ℕ) : ℤ) := by push_cast; simp [q, add_assoc]
  rw [S.exactAt_iff' (k : ℤ) q ((k+2 : ℕ) : ℤ) hp hn]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro a ha
  change S.d q ((k+2 : ℕ) : ℤ) a = 0 at ha
  obtain ⟨t, ht⟩ := singularCochainSection_surjective X V U (k+1) a
  let dt := ((P.d q ((k+2 : ℕ) : ℤ)).app (op U)) t
  have hdt : cochainUnit V U ((k+2 : ℕ) : ℤ) dt = 0 := by
    exact (cochainUnit_comm V U q ((k+2 : ℕ) : ℤ) t).trans (ht.symm ▸ ha)
  obtain ⟨B, i, hx, h⟩ := exists_zero_restriction_cover (P.X ((k+2 : ℕ) : ℤ)) U dt hdt
  let D := coverOfOpenRestriction U B hx
  have hz := (cochainDual_kills_small_iff U V (k+2) dt B i hx).mpr h
  let T := TopCat.of U
  let L := smallComplex ℚ D
  let inc := smallInclusion ℚ D
  have hL : L.ExactAt (k+1) := by
    have h₁ := (P202.SingularDegreeZero.reducedPositiveIso ℚ ℚ T (k+1) (by omega)).isZero_iff.mp
      (P202.PrismHomotopy.contractible ℚ ℚ T q)
    have h₂ : IsZero ((complex ℚ ℚ T).homology (k+1)) := by
      let e := (complex ℚ ℚ T).extendHomologyIso (degreeEmbedding 0)
        (j := k+1) (j' := q) (by change (0 : ℤ) + ((k+1 : ℕ) : ℤ) = q; omega)
      exact h₁.of_iso e.symm
    have hi : IsIso (HomologicalComplex.homologyMap inc (k+1)) :=
      P202.SmallChainHomology.absoluteComparison ℚ T U D (k+1)
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (h₂.of_iso (asIso (HomologicalComplex.homologyMap inc (k+1))))
  let d := (inc.f (k+1) ≫ (complex ℚ ℚ T).d (k+1) k).hom
  let b := (cochainDual V U (k+1) t).comp (inc.f (k+1)).hom
  have hb : LinearMap.ker d ≤ LinearMap.ker b := by
    intro x hx'
    have hxL : L.d (k+1) k x = 0 := by
      let T' := (complex ℚ ℚ T).X k
      have e := congrArg (fun f : L.X (k+1) ⟶ T' => f x) ((inc.comm (k+1) k).symm)
      have hx'' : (inc.f (k+1) ≫ (complex ℚ ℚ T).d (k+1) k) x = 0 := hx'
      have he : (inc.f k).hom (L.d (k+1) k x) = 0 := by
        exact e.trans hx''
      exact Subtype.ext he
    have hex := (L.exactAt_iff' (k+2) (k+1) k (by simp) (by simp)).mp hL
    obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex x hxL
    change cochainDual V U (k+1) t (inc.f (k+1) (L.d (k+2) (k+1) y)) = 0
    have he := congrArg (fun f : L.X (k+2) ⟶ (complex ℚ ℚ T).X (k+1) => f y)
      (inc.comm (k+2) (k+1))
    change (complex ℚ ℚ T).d (k+2) (k+1) (inc.f (k+2) y) =
      inc.f (k+1) (L.d (k+2) (k+1) y) at he
    rw [← he]
    have hd : cochainDual V U (k+2) dt =
        (cochainDual V U (k+1) t).comp (boundary ℚ ℚ T (k+1)) :=
      cochainDual_boundary V U (k+1) t
    exact (LinearMap.congr_fun hd (inc.f (k+2) y)).symm.trans (hz y.property)
  obtain ⟨c, hc⟩ := exists_linearMap_factor d b hb
  let p := (cochainDual V U k).symm c
  let dp := ((P.d (k : ℤ) q).app (op U)) p
  have hdp : cochainDual V U (k+1) dp = c.comp (boundary ℚ ℚ T k) := by
    have he := cochainDual_boundary V U k p
    rw [LinearEquiv.apply_symm_apply] at he
    exact he
  have ha' : smallModule ℚ D (k+1) ≤ LinearMap.ker (cochainDual V U (k+1) (dp - t)) := by
    intro x hx'
    have e := LinearMap.congr_fun hc ⟨x, hx'⟩
    change c (boundary ℚ ℚ T k x) = cochainDual V U (k+1) t x at e
    change cochainDual V U (k+1) (dp - t) x = 0
    rw [map_sub, LinearMap.sub_apply, hdp, LinearMap.comp_apply]
    exact sub_eq_zero.mpr e
  have hr := (cochainDual_kills_small_iff U V (k+1) (dp - t) B i hx).mp ha'
  have he : cochainUnit V U q dp = cochainUnit V U q t :=
    sheafifySection_eq_of_restrict_eq (P.X q) U dp t B i hx fun x =>
      sub_eq_zero.mp (by simpa only [map_sub] using hr x)
  exact ⟨cochainUnit V U (k : ℤ) p, (cochainUnit_comm V U (k : ℤ) q p).symm.trans (he.trans ht)⟩

private abbrev pointSpace := P202Specs.SingularDegreeZero.point.{u}

private instance : Subsingleton (Simplex pointSpace.{u} 0) :=
  Function.Injective.subsingleton (simplexEquiv pointSpace 0).injective

private def pointCochainZeroIso (V : Coeff.{u}) :
    (ordinaryCochains ℚ V pointSpace.{u}).X 0 ≅ V := by
  let s : Simplex pointSpace.{u} 0 :=
    (simplexEquiv pointSpace 0).symm (ContinuousMap.const _ PUnit.unit)
  let e : Chains ℚ pointSpace.{u} 0 ≃ₗ[ℚ] ℚ := Finsupp.uniqueLinearEquiv ℚ ℚ s
  exact ((ordinaryCochainsEquiv ℚ V pointSpace 0).trans
    ((LinearEquiv.arrowCongr e (LinearEquiv.refl ℚ V)).trans (LinearMap.ringLmapEquivSelf ℚ ℚ V))).toModuleIso

private theorem pointCochain_d_zero_one (V : Coeff.{u}) :
    (ordinaryCochains ℚ V pointSpace.{u}).d 0 1 = 0 := by
  let X := pointSpace.{u}
  have hb : boundary ℚ ℚ X 0 = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    have e : face (0 : Fin 2) s = face (1 : Fin 2) s :=
      Subsingleton.elim _ _
    calc
      _ = ∑ k : Fin 2, (-1 : ℤ)^k.val • Finsupp.single (face k s) r :=
        P202.SingularChains.boundary_single ℚ ℚ X 0 s r
      _ = _ := by rw [Fin.sum_univ_two, e]; simp
  let K := ordinaryComplex ℚ ℚ X
  let i := ordinaryNonnegativeIso ℚ ℚ X 0
  let j := ordinaryNonnegativeIso ℚ ℚ X 1
  have he := P202.SingularChains.ordinary_boundary ℚ ℚ X 0
  have hz : (complex ℚ ℚ X).d 1 0 = 0 := ModuleCat.hom_ext hb
  change j.inv ≫ K.d 1 0 ≫ i.hom = (complex ℚ ℚ X).d 1 0 at he
  have hK : K.d 1 0 = 0 := by
    apply (cancel_epi j.inv).mp
    apply (cancel_mono i.hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp, hz] using he
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  let f' : K.X 0 →ₗ[ℚ] V := f
  change f' ((K.d 1 0) x) = 0
  rw [hK]
  simp

private def pointCochainAugmentation (V : Coeff.{u}) :
    (CochainComplex.singleFunctor Coeff.{u} 0).obj V ⟶ ordinaryCochains ℚ V pointSpace.{u} :=
  HomologicalComplex.mkHomFromSingle (pointCochainZeroIso V).inv (by
    intro j hj
    have e : j = (1 : ℤ) := by change (0 : ℤ) + 1 = j at hj; omega
    rw [e, pointCochain_d_zero_one, comp_zero])

private instance (V : Coeff.{u}) : QuasiIso (pointCochainAugmentation V) := by
  constructor
  intro q
  by_cases hq : q = 0
  · subst q
    let A := (CochainComplex.singleFunctor Coeff.{u} 0).obj V
    let B := ordinaryCochains ℚ V pointSpace.{u}
    let a := pointCochainAugmentation V
    rw [quasiIsoAt_iff]
    let e := (HomologicalComplex.shortComplexFunctor Coeff.{u} (ComplexShape.up ℤ) 0).map a
    change ShortComplex.QuasiIso e
    have h₁ : (A.sc 0).f = 0 := by
      exact HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 V _ _
    have h₂ : (A.sc 0).g = 0 := by
      exact HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 V _ _
    have h₃ : (B.sc 0).f = 0 := by
      change B.d ((ComplexShape.up ℤ).prev 0) 0 = 0
      apply ((P202.CohomologyPairs.negative ℚ V).1 pointSpace _ (by simp)).1.eq_of_src
    have h₄ : (B.sc 0).g = 0 := by
      change B.d 0 ((ComplexShape.up ℤ).next 0) = 0
      rw [show (ComplexShape.up ℤ).next 0 = (1 : ℤ) by simp]
      exact pointCochain_d_zero_one V
    have hi : IsIso e.τ₂ := by
      change IsIso (a.f 0)
      unfold a pointCochainAugmentation
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    rw [ShortComplex.quasiIso_iff_of_zeros e h₁ h₂ h₃]
    refine ⟨?_, inferInstance⟩
    let D := ShortComplex.mk e.τ₂ (B.sc 0).g (by rw [h₄, comp_zero])
    change D.Exact
    exact (ShortComplex.exact_iff_epi D h₄).mpr (show Epi e.τ₂ from inferInstance)
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have hA := HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 V q hq
    have hB : IsZero ((ordinaryCochains ℚ V pointSpace.{u}).homology q) := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact (P202.CohomologyPairs.negative ℚ V).1 pointSpace q h |>.2
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
        exact singularCohomology_isZero_pos_of_contractible pointSpace V n (by omega)
    exact hA.isIso hB _

private def pointOpenMap (Y : TopCat.{u}) : Y ⟶ pointSpace.{u} :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

private theorem pointOpenMap_quasiIso (V : Coeff.{u}) (Y : TopCat.{u}) [ContractibleSpace Y] :
    QuasiIso ((ordinaryCochainFunctor ℚ V).map (pointOpenMap Y).op) := by
  obtain ⟨y, ⟨h⟩⟩ := id_nullhomotopic Y
  let p := pointOpenMap Y
  let i : pointSpace.{u} ⟶ Y := TopCat.ofHom (ContinuousMap.const _ y)
  have H₁ : TopCat.Homotopy (p ≫ i) (𝟙 Y) := h.symm
  have ei : i ≫ p = 𝟙 _ := TopCat.ext fun a => Subsingleton.elim _ _
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := ordinaryCohomologyFunctor ℚ V q
  change IsIso (F.map p.op)
  refine ⟨F.map i.op, ?_, ?_⟩
  · rw [← F.map_comp, ← op_comp, ei, op_id]
    exact F.map_id _
  · rw [← F.map_comp, ← op_comp]
    have e := (P202.CohomologyPairs.homotopy_invariant ℚ V).1 H₁ q
    change F.map (p ≫ i).op = F.map (𝟙 Y).op at e
    rw [e, op_id]
    exact F.map_id _

private abbrev pointCochainPresheaves (X : TopCat.{u}) (V : Coeff.{u}) :
    CochainComplex (X.Presheaf Coeff.{u}) ℤ :=
  ((Functor.const (Opens X)ᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (ordinaryCochains ℚ V pointSpace.{u})

private def pointCochainPresheafMap (X : TopCat.{u}) (V : Coeff.{u}) :
    pointCochainPresheaves X V ⟶ singularCochainPresheaves X V := by
  let C := ordinaryCochainFunctor ℚ V
  let p (U : Opens X) : (Opens.toTopCat X).obj U ⟶ pointSpace := pointOpenMap _
  refine
    { f := fun n =>
        { app := fun U => (C.map (p U.unop).op).f n
          naturality := ?_ }
      comm' := ?_ }
  · intro U W g
    change 𝟙 _ ≫ (C.map (p W.unop).op).f _ =
      (C.map (p U.unop).op).f _ ≫ (C.map ((Opens.toTopCat X).map g.unop).op).f _
    rw [Category.id_comp, ← HomologicalComplex.comp_f, ← C.map_comp, ← op_comp]
    congr 3
  · intro i j _
    apply NatTrans.ext
    funext U
    exact (C.map (p U.unop).op).comm i j

private theorem isIso_sheafifiedMap_of_stalk {X : TopCat.{u}} {K L : X.Presheaf Coeff.{u}}
    (f : K ⟶ L) (h : ∀ x : X, IsIso ((stalkFunctor Coeff.{u} x).map f)) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).map f) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let J := Opens.grothendieckTopology X
  let S := stalkFunctor Coeff.{u} x
  have hK : IsIso (S.map (toSheafify J K)) := stalkFunctor_map_unit_toSheafify_isIso x _ K
  have hL : IsIso (S.map (toSheafify J L)) := stalkFunctor_map_unit_toSheafify_isIso x _ L
  have hx := h x
  change IsIso (S.map (sheafifyMap J f))
  rw [← isIso_comp_left_iff (S.map (toSheafify J K)), ← S.map_comp, ← toSheafify_naturality,
    S.map_comp]
  infer_instance

private theorem pointCochainSheafMap_quasiIso (X : TopCat.{u}) (V : Coeff.{u})
    (hX : ∀ (x : X) (U : Opens X), x ∈ U → ∃ W : Opens X,
      W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W)) :
    let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map (pointCochainPresheafMap X V)) := by
  dsimp only
  let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  have : T.Additive := by dsimp only [T]; infer_instance
  have : T.PreservesHomology := by dsimp only [T]; infer_instance
  let A := pointCochainPresheaves X V
  let B := singularCochainPresheaves X V
  let e := pointCochainPresheafMap X V
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let f := HomologicalComplex.homologyMap e q
  have hF : IsIso (T.map f) := by
    apply isIso_sheafifiedMap_of_stalk
    intro x
    apply isIso_stalkMap_of_cofinal f x
    intro U hxU
    obtain ⟨W, hWU, hxW, hW⟩ := hX x U hxU
    refine ⟨W, hWU, hxW, ?_⟩
    let F := (evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op W)
    have : F.Additive := by dsimp only [F]; infer_instance
    have : F.PreservesHomology := by dsimp only [F]; infer_instance
    have hm : F.map f = f.app (op W) := rfl
    rw [← hm]
    let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) q).map e
    change IsIso (F.map (ShortComplex.homologyMap φ))
    have hQ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map e) :=
      pointOpenMap_quasiIso V (TopCat.of W)
    have hφ : ShortComplex.QuasiIso (F.mapShortComplex.map φ) :=
      (quasiIsoAt_iff _ q).mp (hQ.quasiIsoAt q)
    rw [← isIso_comp_left_iff ((A.sc q).mapHomologyIso F).hom,
      ← ShortComplex.mapHomologyIso_hom_naturality φ F]
    infer_instance
  let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) q).map e
  change IsIso (ShortComplex.homologyMap (T.mapShortComplex.map φ))
  rw [← isIso_comp_right_iff _ ((B.sc q).mapHomologyIso T).hom,
    ShortComplex.mapHomologyIso_hom_naturality φ T]
  change IsIso (((A.sc q).mapHomologyIso T).hom ≫ T.map f)
  infer_instance

open private isIsoDerivedSectionsOfFlasque plusHomologyFactors from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private def singularCochainResolutionIso (X : TopCat.{u}) (V : Coeff.{u})
    (hX : ∀ (x : X) (U : Opens X), x ∈ U → ∃ W : Opens X,
      W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W)) :
    let C : CochainComplex.Plus (Sheaves X) :=
      ⟨singularCochainSheaves X V, 0, singularCochainSheaves_isStrictlyGE X V⟩
    (DerivedCategory.Plus.singleFunctor (Sheaves X) 0).obj (constant X V) ≅
      DerivedCategory.Plus.Q.obj C := by
  intro C
  let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  let E := (Functor.const (Opens X)ᵒᵖ : Coeff.{u} ⥤ ((Opens X)ᵒᵖ ⥤ Coeff.{u}))
  have : E.Additive := ⟨by intros; rfl⟩
  have : T.Additive := by dsimp only [T]; infer_instance
  have : PreservesLimits E := preservesLimits_const
  have : PreservesColimits E := preservesColimits_const
  have : T.PreservesHomology := by dsimp only [T]; infer_instance
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  let H : Coeff.{u} ⥤ Sheaves X := E ⋙ T
  have : H.Additive := by change (E ⋙ T).Additive; infer_instance
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits E T
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits E T
  have : H.PreservesHomology := inferInstance
  let e := (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).app V
  let b₁ := (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (pointCochainAugmentation V)
  let b₂ := (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (pointCochainPresheafMap X V)
  let b : (CochainComplex.singleFunctor (Sheaves X) 0).obj (constant X V) ⟶ C.obj :=
    e.inv ≫ b₁ ≫ b₂
  have hB₂ : QuasiIso b₂ := pointCochainSheafMap_quasiIso X V hX
  have hB₁ : QuasiIso b₁ := inferInstance
  have hb : QuasiIso b := by dsimp only [b]; infer_instance
  let A : CochainComplex.Plus (Sheaves X) :=
    ⟨(CochainComplex.singleFunctor (Sheaves X) 0).obj (constant X V), 0, inferInstance⟩
  let a : A ⟶ C := (CochainComplex.plus (Sheaves X)).homMk b
  have ha : CochainComplex.Plus.quasiIso (Sheaves X) a := hb
  have : IsIso ((DerivedCategory.Plus.Q (C := Sheaves X)).map a) :=
    Localization.inverts _ _ a ha
  exact asIso ((DerivedCategory.Plus.Q (C := Sheaves X)).map a)

private abbrev derivedSectionsOn {X : TopCat.{u}} (U : Opens X) :
    BoundedBelow X ⥤ DerivedCategory.Plus Coeff.{u} :=
  (sectionsOn (X := X) U).rightDerivedFunctorPlus

/-- On a metric space with a basis of contractible opens, positive derived sections
of a constant sheaf vanish on each contractible open. -/
theorem derivedSectionsConstant_isZero_pos (X : Type u) [MetricSpace X] (V : Coeff.{u})
    (hX : ∀ (x : X) (U : Opens (TopCat.of X)), x ∈ U → ∃ W : Opens (TopCat.of X),
      W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W))
    (U : Opens (TopCat.of X)) [ContractibleSpace (TopCat.of U)] (k : ℕ) :
    IsZero ((DerivedCategory.Plus.homologyFunctor Coeff.{u} ((k+1 : ℕ) : ℤ)).obj
      ((derivedSectionsOn (X := TopCat.of X) U).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (constant (TopCat.of X) V)))) := by
  let T := sectionsOn (X := TopCat.of X) U
  have : T.Additive := ⟨by intros; rfl⟩
  let C : CochainComplex.Plus (Sheaves (TopCat.of X)) :=
    ⟨singularCochainSheaves (TopCat.of X) V, 0, singularCochainSheaves_isStrictlyGE (TopCat.of X) V⟩
  let q : ℤ := (k+1 : ℕ)
  let r := DerivedCategory.Plus.homologyFunctor Coeff.{u} q
  let e := (T.rightDerivedFunctorPlus ⋙ r).mapIso (singularCochainResolutionIso (TopCat.of X) V hX)
  have hfl : IsIso (T.rightDerivedFunctorPlusUnit.app C) :=
    isIsoDerivedSectionsOfFlasque U C (singularCochainSheaves_isFlasque X V)
  let d := r.mapIso (asIso (T.rightDerivedFunctorPlusUnit.app C)).symm
  let f := (plusHomologyFactors Coeff.{u} q).app (T.mapCochainComplexPlus.obj C)
  exact (singularCochainSections_exact_pos X V U k).isZero_homology.of_iso (e ≪≫ d ≪≫ f)

open private constantPullbackIso zero_locallyConstantFiniteRank locallyConstantFiniteRank_of_iso from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

/-- Pulling back a constant sheaf extended by a closed inclusion gives locally constant
finite rank when the entire image lands inside or outside the closed subset. -/
theorem pullback_closedConstant_locallyConstantFiniteRank {X Y : TopCat.{u}}
    {Z : Set Y} (hZ : IsClosed Z) (f : X ⟶ Y) (V : Coeff.{u}) (hV : Module.Finite ℚ V)
    (hf : (∀ x : X, f x ∈ Z) ∨ (∀ x : X, f x ∉ Z)) :
    LocallyConstantFiniteRank
      ((inverseImage f).obj ((directImage (closedInclusion Z)).obj (constant (TopCat.of Z) V))) := by
  let i := closedInclusion (X := Y) Z
  let E := constant (TopCat.of Z) V
  rcases hf with hf | hf
  · let g : X ⟶ TopCat.of Z := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
    have hgi : g ≫ i = f := rfl
    have hc := inducedCounit_isIso (f := i) IsInducing.subtypeVal E
    let b := (inverseDirectAdjunction i).counit.app E
    let e : (inverseImage f).obj ((directImage i).obj E) ≅ constant X V :=
      eqToIso (congrArg (fun m : X ⟶ Y => (inverseImage m).obj ((directImage i).obj E)) hgi.symm) ≪≫
        (inverseImageComposition g i).app _ ≪≫
        (inverseImage g).mapIso (asIso b) ≪≫ constantPullbackIso g V
    apply locallyConstantFiniteRank_of_iso e.symm
    intro x
    exact ⟨⊤, trivial, V, hV, ⟨constantPullbackIso (openInclusion ⊤) V⟩⟩
  · apply zero_locallyConstantFiniteRank
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    exact (closedDirectImage_supported hZ E (f x) (hf x)).of_iso
      (inverseImageStalkIso f ((directImage i).obj E) x).symm

/-- The closed hull of a face intersected with a receiving open stage. -/
def closedFacePiece (K : SimplicialComplex ℝ (σ → ℝ)) (W : Opens (TopCat.of K.space))
    (s : K.faces) : Set W :=
  (openInclusion W ≫ complexInclusion K) ⁻¹' convexHull ℝ (s.val : Set (σ → ℝ))

theorem isClosed_closedFacePiece (K : SimplicialComplex ℝ (σ → ℝ))
    (W : Opens (TopCat.of K.space)) (s : K.faces) : IsClosed (closedFacePiece K W s) :=
  (s.val.finite_toSet.isClosed_convexHull ℝ).preimage
    (openInclusion W ≫ complexInclusion K).hom.continuous

/-- The elementary extension by zero of a constant sheaf on the closed hull of one
face is locally constant of finite rank on all face interiors of the receiving stage. -/
theorem closedFaceConstant_locallyConstant [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s t : K.faces) (V : Coeff.{u}) (hV : Module.Finite ℚ V) :
    LocallyConstantFiniteRank
      ((inverseImage (pieceInclusion (facePiece (openInclusion W ≫ complexInclusion K) t.val))).obj
        ((directImage (closedInclusion (closedFacePiece K W s))).obj
          (constant (TopCat.of (closedFacePiece K W s)) V))) := by
  apply pullback_closedConstant_locallyConstantFiniteRank (isClosed_closedFacePiece K W s) _ V hV
  by_cases h : t.val ⊆ s.val
  · exact Or.inl (fun x => (mem_convexHull_iff_face_subset (s := t) (t := s) x.property).mpr h)
  · exact Or.inr (fun x hx => h ((mem_convexHull_iff_face_subset (s := t) (t := s) x.property).mp hx))

private def ballOnSubspace [Fintype σ] (S : Set (σ → ℝ)) (x : σ → ℝ) (r : ℝ) :
    Opens (TopCat.of S) :=
  ⟨Subtype.val ⁻¹' Metric.ball x r, Metric.isOpen_ball.preimage continuous_subtype_val⟩

private theorem contractibleSpace_ballOnSubspace [Fintype σ] {S : Set (σ → ℝ)}
    (hS : Convex ℝ S) (x : σ → ℝ) (r : ℝ) (hn : (Metric.ball x r ∩ S).Nonempty) :
    ContractibleSpace (TopCat.of (ballOnSubspace S x r)) := by
  let A := Metric.ball x r ∩ S
  let B := ballOnSubspace S x r
  let e : B ≃ₜ A :=
    { toFun := fun y => ⟨y.val.val, y.property, y.val.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have : ContractibleSpace A := ((convex_ball x r).inter hS).contractibleSpace hn
  exact e.contractibleSpace

private theorem convex_contractibleBasis [Fintype σ] {S : Set (σ → ℝ)} (hS : Convex ℝ S)
    (x : TopCat.of S) (U : Opens (TopCat.of S)) (hx : x ∈ U) :
    ∃ W : Opens (TopCat.of S), W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W) := by
  obtain ⟨r, hr, hU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  exact ⟨ballOnSubspace S x.val r, hU, Metric.mem_ball_self hr,
    contractibleSpace_ballOnSubspace hS x.val r ⟨x.val, Metric.mem_ball_self hr, x.property⟩⟩

private theorem exists_contractible_open_preimage_face [Fintype σ] {s : Finset (σ → ℝ)}
    (hs : s.Nonempty) {Y : Type u} [MetricSpace Y]
    (e : Y → (σ → ℝ)) (he : Isometry e) (hY : Set.range e ⊆ convexHull ℝ (s : Set (σ → ℝ)))
    (f : TopCat.of (faceInterior s) ⟶ TopCat.of Y) (hf : ∀ x, e (f x) = x.val)
    (y : Y) (U : Opens (TopCat.of Y)) (hy : y ∈ U) :
    ∃ W : Opens (TopCat.of Y), W ≤ U ∧ y ∈ W ∧
      ContractibleSpace (TopCat.of ((Opens.map f).obj W)) := by
  obtain ⟨r, hr, hU⟩ := Metric.isOpen_iff.mp U.isOpen y hy
  let W : Opens (TopCat.of Y) := ⟨Metric.ball y r, Metric.isOpen_ball⟩
  have eq : (Opens.map f).obj W = ballOnSubspace (faceInterior s) (e y) r := by
    ext z
    change dist (f z) y < r ↔ dist z.val (e y) < r
    rw [← he.dist_eq, hf]
  have hne := (ball_inter_faceInterior hs (e y)).mpr (hY (Set.mem_range_self y)) r hr
  exact ⟨W, hU, Metric.mem_ball_self hr, eq.symm ▸
    contractibleSpace_ballOnSubspace (convex_faceInterior s) (e y) r hne⟩

private def faceInStage {K : SimplicialComplex ℝ (σ → ℝ)} (s : K.faces)
    (W : Opens (TopCat.of K.space)) (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) :
    TopCat.of (faceInterior s.val) ⟶ TopCat.of W :=
  TopCat.ofHom
    ⟨fun x =>
      ⟨⟨x.val, K.convexHull_subset_space s.property (faceInterior_subset_convexHull _ x.property)⟩,
        h (show (⟨x.val, _⟩ : K.space) ∈ facePiece (complexInclusion K) s.val from x.property)⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩

private def faceInClosedPiece {K : SimplicialComplex ℝ (σ → ℝ)} (s : K.faces)
    (W : Opens (TopCat.of K.space)) (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) :
    TopCat.of (faceInterior s.val) ⟶ TopCat.of (closedFacePiece K W s) :=
  TopCat.ofHom ⟨fun x => ⟨faceInStage s W h x, faceInterior_subset_convexHull _ x.property⟩,
    (faceInStage s W h).hom.continuous.subtype_mk _⟩

private def faceStageFactor {K : SimplicialComplex ℝ (σ → ℝ)} (s : K.faces)
    (W : Opens (TopCat.of K.space)) (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) :
    TopCat.of (faceInterior s.val) ⟶
      TopCat.of (facePiece (openInclusion W ≫ complexInclusion K) s.val) :=
  TopCat.ofHom ⟨fun x => ⟨faceInStage s W h x, x.property⟩,
    (faceInStage s W h).hom.continuous.subtype_mk _⟩

private theorem faceInStage_isInducing {K : SimplicialComplex ℝ (σ → ℝ)} (s : K.faces)
    (W : Opens (TopCat.of K.space)) (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) :
    IsInducing (faceInStage s W h) := by
  apply IsInducing.of_comp (g := fun w : W => w.val.val)
    (faceInStage s W h).hom.continuous (continuous_subtype_val.comp continuous_subtype_val)
  exact IsInducing.subtypeVal

private def constantFaceInClosedPiece [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (s : K.faces) (W : Opens (TopCat.of K.space))
    (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) (V : Coeff.{u}) :
    (directImage (faceInClosedPiece s W h)).obj (constant (TopCat.of (faceInterior s.val)) V) ≅
      constant (TopCat.of (closedFacePiece K W s)) V := by
  let Z := closedFacePiece K W s
  let f := faceInClosedPiece s W h
  let e : Z → (σ → ℝ) := fun z => z.val.val.val
  have he : Isometry e := Isometry.of_dist_eq fun _ _ => rfl
  have hY : Set.range e ⊆ convexHull ℝ (s.val : Set (σ → ℝ)) := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have hconst : IsIso (constantDirectImageMap f V) := by
    apply isIso_constantDirectImageMap
    intro y U hy
    obtain ⟨O, hO, hyO, hC⟩ := exists_contractible_open_preimage_face
      (K.nonempty_of_mem_faces s.property) e he hY f (fun _ => rfl) y U hy
    exact ⟨O, hyO, hO, isConnected_iff_connectedSpace.mpr inferInstance⟩
  exact (asIso (constantDirectImageMap f V)).symm

private def directImageComposition {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImage f ⋙ directImage g ≅ directImage (f ≫ g) :=
  (((inverseDirectAdjunction g).comp (inverseDirectAdjunction f)).ofNatIsoLeft
    (inverseImageComposition f g).symm).rightAdjointUniq (inverseDirectAdjunction (f ≫ g))

private def constantFaceInStage [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (s : K.faces) (W : Opens (TopCat.of K.space))
    (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) (V : Coeff.{u}) :
    (directImage (faceInStage s W h)).obj (constant (TopCat.of (faceInterior s.val)) V) ≅
      (directImage (closedInclusion (closedFacePiece K W s))).obj
        (constant (TopCat.of (closedFacePiece K W s)) V) := by
  let f := faceInClosedPiece s W h
  let i := closedInclusion (X := TopCat.of W) (closedFacePiece K W s)
  let C := constant (TopCat.of (faceInterior s.val)) V
  have hfi : faceInStage s W h = f ≫ i := rfl
  exact eqToIso (congrArg (fun g => (directImage g).obj C) hfi) ≪≫
    (directImageComposition f i).symm.app C ≪≫
    (directImage i).mapIso (constantFaceInClosedPiece s W h V)

private def derivedOpenSectionsCohomologyIso {X : TopCat.{u}} (U : Opens X)
    (q : ℤ) (F : BoundedBelow X) :
    (LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves X)) F q).obj (op U) ≅
      (DerivedCategory.Plus.homologyFunctor Coeff.{u} q).obj ((derivedSectionsOn U).obj F) := by
  let G := sectionsOn (X := X) U
  let a := G.leftUnitor
  let f := a.hom.rightDerivedFunctorPlus
  have : IsIso f := by
    refine ⟨⟨a.inv.rightDerivedFunctorPlus, ?_, ?_⟩⟩
    · rw [← NatTrans.rightDerivedFunctorPlus_comp, a.hom_inv_id, NatTrans.rightDerivedFunctorPlus_id]
    · rw [← NatTrans.rightDerivedFunctorPlus_comp, a.inv_hom_id, NatTrans.rightDerivedFunctorPlus_id]
  exact (DerivedCategory.Plus.homologyFunctor _ q).mapIso ((asIso f).app F)

private def derivedConstantFaceInClosedPiece [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (s : K.faces) (W : Opens (TopCat.of K.space))
    (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) (V : Coeff.{u}) :
    (derivedDirectImage (faceInClosedPiece s W h)).obj
      (LocalSheaf.sheafInDegreeZero (constant (TopCat.of (faceInterior s.val)) V)) ≅
    LocalSheaf.sheafInDegreeZero (constant (TopCat.of (closedFacePiece K W s)) V) := by
  let X := TopCat.of (faceInterior s.val)
  let Z := closedFacePiece K W s
  let f := faceInClosedPiece s W h
  let e : Z → (σ → ℝ) := fun z => z.val.val.val
  have he : Isometry e := Isometry.of_dist_eq fun _ _ => rfl
  have hY : Set.range e ⊆ convexHull ℝ (s.val : Set (σ → ℝ)) := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have hW (y : Z) (U : Opens (TopCat.of Z)) (hy : y ∈ U) :
      ∃ O : Opens (TopCat.of Z), O ≤ U ∧ y ∈ O ∧
        ContractibleSpace (TopCat.of ((Opens.map f).obj O)) :=
    exists_contractible_open_preimage_face (K.nonempty_of_mem_faces s.property)
      e he hY f (fun _ => rfl) y U hy
  have hvan (n : ℕ) : IsZero ((cohomology (TopCat.of Z) (n+1 : ℕ)).obj
      ((derivedDirectImage f).obj (LocalSheaf.sheafInDegreeZero (constant X V))).obj) := by
    apply directImageCohomology_isZero_of_cofinal
    intro y U hy
    obtain ⟨O, hO, hyO, hC⟩ := hW y U hy
    let L := (Opens.map f).obj O
    exact ⟨O, hO, hyO,
      (derivedSectionsConstant_isZero_pos (faceInterior s.val) V
        (convex_contractibleBasis (convex_faceInterior s.val)) L n).of_iso
          (derivedOpenSectionsCohomologyIso L (n+1 : ℕ)
            (LocalSheaf.sheafInDegreeZero (constant X V)))⟩
  exact (derivedDirectImage_singleIso_of_positiveVanishing f (constant X V) hvan).symm ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso (constantFaceInClosedPiece s W h V)

open private exactPlusFactors from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private def rightDerivedSingleIsoOfExact {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] (M : C) :
    T.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (T.obj M) := by
  let F := LocalSheaf.exactDerivedPlus T
  let α := (exactPlusFactors T).inv
  let P := CochainComplex.Plus.quasiIso C
  have : F.IsRightDerivedFunctor α P :=
    (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus T).isRightDerivedFunctor_of_isIso
      α (fun I => ((exactPlusFactors T).app _).isIso_inv)
  let e := T.rightDerivedFunctorPlus.rightDerivedUnique _ T.rightDerivedFunctorPlusUnit α P
  let A : CochainComplex.Plus C := ⟨(CochainComplex.singleFunctor C 0).obj M, 0, inferInstance⟩
  let B : CochainComplex.Plus D :=
    ⟨(CochainComplex.singleFunctor D 0).obj (T.obj M), 0, inferInstance⟩
  let g : T.mapCochainComplexPlus.obj A ≅ B := (CochainComplex.Plus.ι D).preimageIso
    ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).app M)
  change T.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj A) ≅ DerivedCategory.Plus.Q.obj B
  exact e.app _ ≪≫ (exactPlusFactors T).app A ≪≫ DerivedCategory.Plus.Q.mapIso g

private def derivedConstantFaceInStage [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (s : K.faces) (W : Opens (TopCat.of K.space))
    (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) (V : Coeff.{u}) :
    (derivedDirectImage (faceInStage s W h)).obj
      (LocalSheaf.sheafInDegreeZero (constant (TopCat.of (faceInterior s.val)) V)) ≅
    LocalSheaf.sheafInDegreeZero ((directImage (closedInclusion (closedFacePiece K W s))).obj
      (constant (TopCat.of (closedFacePiece K W s)) V)) := by
  let f := faceInClosedPiece s W h
  let i := closedInclusion (X := TopCat.of W) (closedFacePiece K W s)
  have hfi : faceInStage s W h = f ≫ i := rfl
  let T := directImage i
  have hT : T.PreservesHomology := DerivedLocalSheaves.closedDirectImagePreservesHomology
    (isClosed_closedFacePiece K W s)
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  let M := constant (TopCat.of (closedFacePiece K W s)) V
  let C := LocalSheaf.sheafInDegreeZero (constant (TopCat.of (faceInterior s.val)) V)
  exact eqToIso (congrArg (fun g => (derivedDirectImage g).obj C) hfi) ≪≫
    (derivedDirectImageComposition f i).symm.app C ≪≫
    (derivedDirectImage i).mapIso (derivedConstantFaceInClosedPiece s W h V) ≪≫
    rightDerivedSingleIsoOfExact T M

private abbrev stagePieceInclusion {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s : K.faces) :
    TopCat.of (facePiece (openInclusion W ≫ complexInclusion K) s.val) ⟶ TopCat.of W :=
  pieceInclusion (facePiece (openInclusion W ≫ complexInclusion K) s.val)

private def faceStageHomeomorph {K : SimplicialComplex ℝ (σ → ℝ)} (s : K.faces)
    (W : Opens (TopCat.of K.space)) (h : facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)) :
    faceInterior s.val ≃ₜ facePiece (openInclusion W ≫ complexInclusion K) s.val where
  toFun := faceStageFactor s W h
  invFun := fun x => ⟨x.val.val.val, x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (faceStageFactor s W h).hom.continuous
  continuous_invFun := (continuous_subtype_val.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

private theorem stagePiece_locallyConnected [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (hK : K.faces.Finite) (W : Opens (TopCat.of K.space))
    (hW : IsUnionOfFaceInteriors K (W : Set K.space)) (s : K.faces) :
    LocallyConnectedSpace (facePiece (openInclusion W ≫ complexInclusion K) s.val) := by
  by_cases hs : (facePiece (openInclusion W ≫ complexInclusion K) s.val).Nonempty
  · obtain ⟨x, hx⟩ := hs
    have h := facePiece_subset_of_nonempty_inter (inferInstance : Finite σ) hK hW s
      ⟨x.val, hx, x.property⟩
    have : LocallyPathConnectedSpace (faceInterior s.val) :=
      convex_locallyPathConnected (convex_faceInterior _)
    exact (faceStageHomeomorph s W h).symm.isOpenEmbedding.locallyConnectedSpace
  · exact ⟨fun x => (hs ⟨x.val, x.property⟩).elim⟩

/-- The indices of the face interiors present in an open stage. -/
private abbrev StageFace {K : SimplicialComplex ℝ (σ → ℝ)} (W : Opens (TopCat.of K.space)) :=
  {s : K.faces // facePiece (complexInclusion K) s.val ⊆ (W : Set K.space)}

private abbrev stageFaceInclusion {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s : StageFace W) :
    TopCat.of (faceInterior s.val.val) ⟶ TopCat.of W :=
  faceInStage s.val W s.property

private theorem stageFace_connected [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s : StageFace W) :
    ConnectedSpace (TopCat.of (faceInterior s.val.val)) := by
  have hs : (s.val.val : Set (σ → ℝ)).Nonempty := K.nonempty_of_mem_faces s.val.property
  have hn : (faceInterior s.val.val).Nonempty :=
    (hs.mono (subset_convexHull ℝ (s.val.val : Set (σ → ℝ)))).intrinsicInterior
      (convex_convexHull ℝ _)
  exact isConnected_iff_connectedSpace.mp ((convex_faceInterior s.val.val).isConnected hn)

private theorem stageFaces_cover [Finite σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (hK : K.faces.Finite) (W : Opens (TopCat.of K.space))
    (hW : IsUnionOfFaceInteriors K (W : Set K.space)) (x : W) :
    ∃ (s : StageFace W) (z : faceInterior s.val.val), stageFaceInclusion W s z = x := by
  obtain ⟨s, hs, _⟩ := (faceInteriorsPartition σ K hK).2.1.2.2 x.val
  have h := facePiece_subset_of_nonempty_inter (inferInstance : Finite σ) hK hW s
    ⟨x.val, hs, x.property⟩
  exact ⟨⟨s, h⟩, ⟨x.val.val, hs⟩, rfl⟩

open private pullback_locallyConstantFiniteRank plusIsGE_iff plusIsLE_iff from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem stageFace_restriction_constant [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s : StageFace W) (M : Sheaves (TopCat.of W))
    (hM : ∀ t : K.faces, LocallyConstantFiniteRank ((inverseImage (stagePieceInclusion W t)).obj M)) :
    ∃ V : Coeff.{u}, Module.Finite ℚ V ∧
      Nonempty ((inverseImage (stageFaceInclusion W s)).obj M ≅
        constant (TopCat.of (faceInterior s.val.val)) V) := by
  let f := faceStageFactor s.val W s.property
  let g := stagePieceInclusion W s.val
  have hfg : f ≫ g = stageFaceInclusion W s := rfl
  have hC : LocallyConstantFiniteRank ((inverseImage (stageFaceInclusion W s)).obj M) :=
    locallyConstantFiniteRank_of_iso ((inverseImageComposition f g).symm.app M ≪≫
      eqToIso (congrArg (fun k => (inverseImage k).obj M) hfg))
      (pullback_locallyConstantFiniteRank f (hM s.val))
  obtain ⟨V, hV, ⟨e⟩⟩ := constant_on_faceInterior (K.nonempty_of_mem_faces s.val.property) _ hC
  exact ⟨V, hV, ⟨e.symm⟩⟩

private abbrev closedFaceConstant {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s : K.faces) (V : Coeff.{u}) : Sheaves (TopCat.of W) :=
  (directImage (closedInclusion (closedFacePiece K W s))).obj
    (constant (TopCat.of (closedFacePiece K W s)) V)

private theorem stageFace_elementary_restrictions [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (s t : StageFace W) (V : Coeff.{u}) (hV : Module.Finite ℚ V) :
    let R := (inverseImage (stageFaceInclusion W t)).obj
      ((directImage (stageFaceInclusion W s)).obj (constant (TopCat.of (faceInterior s.val.val)) V))
    (¬ t ≤ s → IsZero R) ∧ (t ≤ s → ∃ V' : Coeff.{u}, Module.Finite ℚ V' ∧
      Nonempty (R ≅ constant (TopCat.of (faceInterior t.val.val)) V')) := by
  dsimp only
  let f := stageFaceInclusion W t
  let E := closedFaceConstant W s.val V
  let e := (inverseImage f).mapIso (constantFaceInStage s.val W s.property V)
  constructor
  · intro h
    refine IsZero.of_iso ?_ e
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro z
    have hz : f z ∉ closedFacePiece K W s.val := fun hz =>
      h ((mem_convexHull_iff_face_subset (s := t.val) (t := s.val) z.property).mp hz)
    exact (closedDirectImage_supported (isClosed_closedFacePiece K W s.val) _ (f z) hz).of_iso
      (inverseImageStalkIso f E z).symm
  · intro _
    obtain ⟨V', hV', ⟨a⟩⟩ := stageFace_restriction_constant W t E
      (fun r => closedFaceConstant_locallyConstant W s.val r V hV)
    exact ⟨V', hV', ⟨e ≪≫ a⟩⟩

private theorem stageSingle_constructible {K : SimplicialComplex ℝ (σ → ℝ)}
    (W : Opens (TopCat.of K.space)) (M : Sheaves (TopCat.of W))
    (hM : ∀ s : K.faces, LocallyConstantFiniteRank ((inverseImage (stagePieceInclusion W s)).obj M)) :
    ConstructibleTriangles.IsConstructibleAlong (stagePieceInclusion W)
      (LocalSheaf.sheafInDegreeZero M) := by
  let S := LocalSheaf.sheafInDegreeZero M
  have hz {q : ℤ} (hq : q ≠ 0) : IsZero ((cohomology (TopCat.of W) q).obj S.obj) := by
    rcases lt_or_gt_of_ne hq with h | h
    · exact (plusIsGE_iff S 0).mp inferInstance q h
    · exact (plusIsLE_iff S 0).mp inferInstance q h
  refine ⟨(Set.finite_singleton (0 : ℤ)).subset ?_, ?_⟩
  · intro q hq
    by_contra hn
    exact hq (hz hn)
  · intro s q
    by_cases hq : q = 0
    · subst q
      let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves (TopCat.of W)) 0).app M
      exact locallyConstantFiniteRank_of_iso ((inverseImage (stagePieceInclusion W s)).mapIso e.symm)
        (hM s)
    · exact zero_locallyConstantFiniteRank ((inverseImage (stagePieceInclusion W s)).map_isZero (hz hq))

private def stageFaceDirectImageIso [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    {U Y : Opens (TopCat.of K.space)} (h : U ≤ Y) (s : StageFace U) (V : Coeff.{u}) :
    (derivedDirectImage (stageInclusion h)).obj (LocalSheaf.sheafInDegreeZero
      ((directImage (stageFaceInclusion U s)).obj (constant (TopCat.of (faceInterior s.val.val)) V))) ≅
    LocalSheaf.sheafInDegreeZero (closedFaceConstant Y s.val V) := by
  let j := stageInclusion h
  let f := stageFaceInclusion U s
  let A := LocalSheaf.sheafInDegreeZero (constant (TopCat.of (faceInterior s.val.val)) V)
  have hY : facePiece (complexInclusion K) s.val.val ⊆ (Y : Set K.space) := s.property.trans h
  have hfj : f ≫ j = faceInStage s.val Y hY := rfl
  let d := derivedConstantFaceInStage s.val U s.property V ≪≫
    (DerivedCategory.Plus.singleFunctor (Sheaves (TopCat.of U)) 0).mapIso
      (constantFaceInStage s.val U s.property V).symm
  exact (derivedDirectImage j).mapIso d.symm ≪≫ (derivedDirectImageComposition f j).app A ≪≫
    eqToIso (congrArg (fun g => (derivedDirectImage g).obj A) hfj) ≪≫
    derivedConstantFaceInStage s.val Y hY V

open CategoryTheory.Pretriangulated in
open scoped ZeroObject in
theorem openInclusionConstructibility : Expected.OpenInclusionConstructibility.{u} := by
  intro σ _ K hK U Y h hU hY F hF
  let := Fintype.ofFinite σ
  have : Finite K.faces := hK.to_subtype
  have (s : StageFace U) : ConnectedSpace (TopCat.of (faceInterior s.val.val)) :=
    stageFace_connected U s
  have (s : K.faces) : LocallyConnectedSpace
      (TopCat.of (facePiece (openInclusion Y ≫ complexInclusion K) s.val)) :=
    stagePiece_locallyConnected hK Y hY s
  let R := (directImage (stageInclusion h)).rightDerivedFunctorPlus
  let P (G : BoundedBelow (TopCat.of U)) :=
    ConstructibleTriangles.IsConstructibleAlong (stagePieceInclusion Y) (R.obj G)
  have hZero : P 0 := ConstructibleTriangles.constructible_of_iso (stagePieceInclusion Y)
    R.mapZeroObject.symm (ConstructibleTriangles.constructible_zero (stagePieceInclusion Y))
  have hIso {G H : BoundedBelow (TopCat.of U)} (a : G ≅ H) (hG : P G) : P H :=
    ConstructibleTriangles.constructible_of_iso (stagePieceInclusion Y) (R.mapIso a) hG
  have hShift (G : BoundedBelow (TopCat.of U)) (n : ℤ) (hG : P G) : P (G⟦n⟧) :=
    ConstructibleTriangles.constructible_of_iso (stagePieceInclusion Y)
      ((R.commShiftIso n).app G).symm
      (ConstructibleTriangles.constructible_shift (stagePieceInclusion Y) n hG)
  have hTriangle (T : Triangle (BoundedBelow (TopCat.of U))) (ht : T ∈ distTriang _) :
      (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧ (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
        (P T.obj₂ → P T.obj₃ → P T.obj₁) :=
    ConstructibleTriangles.constructible_triangle (stagePieceInclusion Y)
      (R.mapTriangle.obj T) (R.map_distinguished T ht)
  let J := DerivedCategory.Plus.singleFunctor (Sheaves (TopCat.of U)) 0
  let Q (M : Sheaves (TopCat.of U)) := P (J.obj M)
  have hQZero : Q 0 := hIso J.mapZeroObject.symm hZero
  have hQIso ⦃M N : Sheaves (TopCat.of U)⦄ (a : M ≅ N) (hM : Q M) : Q N :=
    hIso (J.mapIso a) hM
  have hQShort (S : ShortComplex (Sheaves (TopCat.of U))) (hs : S.ShortExact) :
      (Q S.X₁ → Q S.X₂ → Q S.X₃) ∧ (Q S.X₁ → Q S.X₃ → Q S.X₂) ∧
        (Q S.X₂ → Q S.X₃ → Q S.X₁) := by
    let T := Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.plusTriangle
      (Sheaves (TopCat.of U)) hs
    have ht := AdvancedHomologicalAlgebra.ClassicalDerivedValues.plusTriangle_distinguished hs
    have hP := hTriangle T ht
    exact ⟨hP.2.1, hP.1, hP.2.2⟩
  have hQElementary (s : StageFace U) (V : Coeff.{u}) (hV : Module.Finite ℚ V) :
      Q ((directImage (stageFaceInclusion U s)).obj (constant (TopCat.of (faceInterior s.val.val)) V)) :=
    ConstructibleTriangles.constructible_of_iso (stagePieceInclusion Y)
      (stageFaceDirectImageIso h s V).symm
      (stageSingle_constructible Y (closedFaceConstant Y s.val V)
        (fun t => closedFaceConstant_locallyConstant Y s.val t V hV))
  have hSingle (M : Sheaves (TopCat.of U))
      (hM : ∀ s : K.faces, LocallyConstantFiniteRank ((inverseImage (stagePieceInclusion U s)).obj M)) :
      P (LocalSheaf.sheafInDegreeZero M) :=
    FiniteFaceDevissage.finiteFaceGeneration (StageFace U) (TopCat.of U)
      (fun s => TopCat.of (faceInterior s.val.val)) (stageFaceInclusion U)
      (fun s => faceInStage_isInducing s.val U s.property) (stageFaces_cover hK U hU)
      (stageFace_elementary_restrictions U) Q hQZero hQIso hQShort hQElementary M
      (fun s => stageFace_restriction_constant U s M hM)
  exact ConstructibleTriangles.constructible_truncation_induction (stagePieceInclusion U)
    P hZero hIso hShift (fun T ht => (hTriangle T ht).1) hSingle F hF

end RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage
