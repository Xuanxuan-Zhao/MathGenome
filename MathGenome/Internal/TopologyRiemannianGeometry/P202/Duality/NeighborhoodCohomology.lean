import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.NeighborhoodCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.EuclideanNeighborhoodRetraction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Filtered.Connected

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Set Topology ContinuousMap

namespace P202.Duality.NeighborhoodCohomology
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
universe u v w
variable {X : Type w} [TopologicalSpace X] {K : Set X}

/-- The shrinking homotopies give the universal property directly. This uses
no unproved continuity assertion about singular cohomology. -/
def ordinaryRestriction_isColimit_of_shrinking
    (h : HasShrinkingRetraction K)
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A] (q : ℤ) :
    IsColimit (ordinaryRestrictionCocone K R A q) := by
  classical
  apply Classical.choice
  obtain ⟨U₀, r, hr, hshrink⟩ := h
  let F := ordinaryCohomologyFunctor R A q
  let r' : TopCat.of U₀.1 ⟶ TopCat.of K := TopCat.ofHom r
  refine ⟨
    { desc := fun s => F.map r'.op ≫ s.ι.app U₀
      fac := ?_
      uniq := ?_ }⟩
  · intro s U
    obtain ⟨V, hVU, hV₀, ⟨H⟩⟩ := hshrink U
    let a : U ⟶ V := homOfLE hVU
    let b : U₀ ⟶ V := homOfLE hV₀
    have heq : F.map (neighborhoodInclusion K a).op =
        F.map ((neighborhoodInclusion K b ≫ r') ≫ compactInclusion K U).op :=
      (P202.CohomologyPairs.homotopy_invariant R A).1 H q
    change F.map (compactInclusion K U).op ≫ (F.map r'.op ≫ s.ι.app U₀) = _
    rw [← s.w b]
    change F.map (compactInclusion K U).op ≫
      (F.map r'.op ≫ (F.map (neighborhoodInclusion K b).op ≫ s.ι.app V)) = _
    rw [← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp]
    change F.map ((neighborhoodInclusion K b ≫ r') ≫ compactInclusion K U).op ≫ _ = _
    rw [← heq]
    exact s.w a
  · intro s m hm
    have hid : compactInclusion K U₀ ≫ r' = 𝟙 (TopCat.of K) := by
      apply TopCat.hom_ext
      exact ContinuousMap.ext hr
    calc
      m = (𝟙 _) ≫ m := (Category.id_comp m).symm
      _ = (F.map r'.op ≫ F.map (compactInclusion K U₀).op) ≫ m := by
        rw [← F.map_comp, ← op_comp, hid, op_id, F.map_id]
        rfl
      _ = F.map r'.op ≫ s.ι.app U₀ := by
        rw [Category.assoc]
        exact congrArg (fun f => F.map r'.op ≫ f) (hm U₀)

theorem ordinaryComparison_of_shrinking
    (h : HasShrinkingRetraction K)
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A] (q : ℤ) :
    IsIso (ordinaryComparison K R A q) := by
  let e := (colimit.isColimit (ordinaryDiagram K R A q)).coconePointUniqueUpToIso
    (ordinaryRestriction_isColimit_of_shrinking h R A q)
  change IsIso e.hom
  infer_instance

/-- Compactness of the parameter interval lets a homotopy fixing `K` be
restricted to a sufficiently small neighborhood inside any prescribed one. -/
theorem hasShrinkingRetraction_of_local_homotopy
    (U₀ : OpenNeighborhood K) (r : C(U₀.1, K))
    (hr : ∀ x : K, r ⟨x.1, U₀.2 x.2⟩ = x)
    (H : C(unitInterval × U₀.1, X))
    (hzero : ∀ x, H (0, x) = x.1)
    (hone : ∀ x, H (1, x) = (r x).1)
    (hfix : ∀ (t : unitInterval) (x : K), H (t, ⟨x.1, U₀.2 x.2⟩) = x.1) :
    HasShrinkingRetraction K := by
  classical
  refine ⟨U₀, r, hr, ?_⟩
  intro U
  let W : Set U₀.1 := (Prod.snd '' (H ⁻¹' (U.1 : Set X)ᶜ))ᶜ
  have hW : IsOpen W :=
    (isClosedMap_snd_of_compactSpace _ (U.1.isOpen.isClosed_compl.preimage H.continuous)).isOpen_compl
  have hmem (x : U₀.1) : x ∈ W ↔ ∀ t : unitInterval, H (t, x) ∈ U.1 := by
    constructor
    · intro hx t
      by_contra ht
      exact hx ⟨(t, x), ht, rfl⟩
    · intro hx ⟨⟨t, y⟩, hy, heq⟩
      have heq' : y = x := heq
      subst y
      exact hy (hx t)
  let Vset : Set X := Subtype.val '' W
  have hVopen : IsOpen Vset := U₀.1.isOpen.isOpenMap_subtype_val W hW
  have hKV : K ⊆ Vset := by
    intro x hx
    refine ⟨⟨x, U₀.2 hx⟩, (hmem _).mpr ?_, rfl⟩
    intro t
    rw [hfix t ⟨x, hx⟩]
    exact U.2 hx
  let V : OpenNeighborhood K := ⟨⟨Vset, hVopen⟩, hKV⟩
  have hV₀ : (V.1 : Set X) ⊆ U₀.1 := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have hVH (x : V.1) (t : unitInterval) :
      H (t, ⟨x.1, hV₀ x.2⟩) ∈ U.1 := by
    obtain ⟨y, hy, hxy⟩ := x.2
    have heq : (⟨x.1, hV₀ x.2⟩ : U₀.1) = y := Subtype.ext hxy.symm
    rw [heq]
    exact (hmem y).mp hy t
  have hVU : (V.1 : Set X) ⊆ U.1 := by
    intro x hx
    have hh := hVH ⟨x, hx⟩ 0
    rw [hzero] at hh
    exact hh
  refine ⟨V, hVU, hV₀, ⟨?_⟩⟩
  refine
    { toFun := fun p => ⟨H (p.1, ⟨p.2.1, hV₀ p.2.2⟩), hVH p.2 p.1⟩
      continuous_toFun := (H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd |>.subtype_mk _))).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    exact Subtype.ext (hzero _)
  · intro x
    exact Subtype.ext (hone _)

/-- Transport classical local contractibility along an actual homeomorphism. -/
theorem locallyContractible_of_homeomorph
    {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)
    (h : LocallyContractibleSpace X) : LocallyContractibleSpace Y := by
  intro y U hU
  obtain ⟨V, hVU, hV, hnull⟩ := h (e.symm y) (e ⁻¹' U)
    (e.continuous.continuousAt.preimage_mem_nhds (by simpa using hU))
  let W : Set Y := e.symm ⁻¹' V
  have hWU : W ⊆ U := by
    intro z hz
    have hz' : e (e.symm z) ∈ U := hVU hz
    simpa only [Homeomorph.apply_symm_apply] using hz'
  refine ⟨W, hWU, e.symm.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  let a : C(W, V) := ⟨fun x => ⟨e.symm x.1, x.2⟩,
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let b : C(e ⁻¹' U, U) := ⟨fun x => ⟨e x.1, x.2⟩,
    (e.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hn := (hnull.comp_left a).comp_right b
  have heq : b.comp ((ContinuousMap.inclusion hVU).comp a) =
      ContinuousMap.inclusion hWU := by
    ext x
    exact e.apply_symm_apply x.1
  rwa [heq] at hn

/-- A Euclidean chart with full target supplies both the retraction and the
ambient straight-line homotopy. No regularity of the embedding of `K` is used. -/
theorem hasShrinkingRetraction_of_openEmbedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E → X) (he : IsOpenEmbedding e) (hKr : K ⊆ Set.range e)
    (hK : IsCompact K) (hLC : LocallyContractibleSpace K) :
    HasShrinkingRetraction K := by
  classical
  let L : Set E := e ⁻¹' K
  let c : L ≃ₜ K := he.toIsEmbedding.homeomorphOfSubsetRange hKr
  have hL : IsCompact L := he.toIsEmbedding.isCompact_iff.mpr (by
    rwa [Set.image_preimage_eq_of_subset hKr])
  have hLLC : LocallyContractibleSpace L := locallyContractible_of_homeomorph c.symm hLC
  obtain ⟨N, hN, hLN, s, hs⟩ :=
    P202.Duality.compact_locallyContractible_hasOpenNeighborhoodRetraction hL hLLC
  let eN : N → X := fun x => e x.1
  have heN : IsOpenEmbedding eN := he.comp hN.isOpenEmbedding_subtypeVal
  let b : N ≃ₜ Set.range eN := heN.toIsEmbedding.toHomeomorph
  have hKN : K ⊆ Set.range eN := by
    intro x hx
    refine ⟨⟨(c.symm ⟨x, hx⟩).1, hLN (c.symm ⟨x, hx⟩).2⟩, ?_⟩
    exact congrArg Subtype.val (c.apply_symm_apply ⟨x, hx⟩)
  let U₀ : OpenNeighborhood K := ⟨⟨Set.range eN, heN.isOpen_range⟩, hKN⟩
  let r : C(U₀.1, K) := (⟨c, c.continuous⟩ : C(L, K)).comp (s.comp ⟨b.symm, b.symm.continuous⟩)
  have hbK (x : K) : b.symm ⟨x.1, hKN x.2⟩ =
      ⟨(c.symm x).1, hLN (c.symm x).2⟩ := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val (c.apply_symm_apply x)).symm
  have hr (x : K) : r ⟨x.1, U₀.2 x.2⟩ = x := by
    change c (s (b.symm ⟨x.1, hKN x.2⟩)) = x
    rw [hbK, hs]
    exact c.apply_symm_apply x
  let H : C(unitInterval × U₀.1, X) :=
    ⟨fun p => e ((1 - (p.1 : ℝ)) • (b.symm p.2).1 +
        (p.1 : ℝ) • (s (b.symm p.2)).1),
      he.continuous.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp (b.symm.continuous.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp (s.continuous.comp (b.symm.continuous.comp continuous_snd)))))⟩
  apply hasShrinkingRetraction_of_local_homotopy U₀ r hr H
  · intro x
    change e ((1 - (0 : ℝ)) • (b.symm x).1 + (0 : ℝ) • _) = x.1
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact congrArg Subtype.val (b.apply_symm_apply x)
  · intro x
    change e ((1 - (1 : ℝ)) • (b.symm x).1 + (1 : ℝ) • _) = _
    simp only [sub_self, zero_smul, one_smul, zero_add]
    rfl
  · intro t x
    change e ((1 - (t : ℝ)) • (b.symm ⟨x.1, hKN x.2⟩).1 +
      (t : ℝ) • (s (b.symm ⟨x.1, hKN x.2⟩)).1) = x.1
    rw [hbK, hs]
    simp only [← add_smul, sub_add_cancel, one_smul]
    exact congrArg Subtype.val (c.apply_symm_apply x)

/-- A missing point provides the Euclidean chart required by the source. -/
theorem sphereShrinkingRetraction :
    P202Specs.Duality.NeighborhoodCohomology.sphereShrinkingRetraction := by
  intro n K _hn _hne hproper hK hLC
  obtain ⟨p, hp⟩ : ∃ p, p ∉ K := by
    exact (Set.ne_univ_iff_exists_notMem K).mp hproper
  let chart := stereographic (norm_eq_of_mem_sphere p)
  apply hasShrinkingRetraction_of_openEmbedding chart.symm
    (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere p)) ?_ hK hLC
  intro x hx
  rw [range_stereographic_symm]
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    (show x ≠ p from fun h => hp (h ▸ hx))

theorem sphereOrdinaryComparison :
    P202Specs.Duality.NeighborhoodCohomology.ordinaryComparison.{u,v} := by
  intro n K hn hne hproper hK hLC R _ A _ _ q
  exact ordinaryComparison_of_shrinking
    (sphereShrinkingRetraction n K hn hne hproper hK hLC) R A q

section ColimitLemmas
variable {J : Type*} [SmallCategory J] {C : Type*} [Category C] [Abelian C]

private theorem shortComplex_exact_of_evaluations (S : ShortComplex (J ⥤ C))
    (h : ∀ j, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro j
  exact ((S.map ((evaluation J C).obj j)).exact_iff_isZero_homology.mp (h j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

private theorem exact_flip_of_pointwise (D : J ⥤ ComposableArrows C 4)
    (h : ∀ j, (D.obj j).Exact) : ComposableArrows.Exact D.flip := by
  have hc : ComposableArrows.IsComplex D.flip := ⟨by
    intro i hi
    apply NatTrans.ext
    funext j
    exact (h j).zero i hi⟩
  refine ⟨hc, ?_⟩
  intro i hi
  apply shortComplex_exact_of_evaluations
  intro j
  exact (h j).exact i hi

private theorem exact_map_colim [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (S : ComposableArrows (J ⥤ C) 4) (h : S.Exact) :
    ComposableArrows.Exact (S ⋙ (colim : (J ⥤ C) ⥤ C)) := by
  have hc : ComposableArrows.IsComplex (S ⋙ (colim : (J ⥤ C) ⥤ C)) := ⟨by
    intro i hi
    change colim.map (S.map' i (i+1)) ≫ colim.map (S.map' (i+1) (i+2)) = 0
    rw [← Functor.map_comp, h.zero i hi, Functor.map_zero]⟩
  refine ⟨hc, ?_⟩
  intro i hi
  exact (h.exact i hi).map colim

/-- Componentwise descent from the colimits of a diagram of five-term sequences. -/
private def fiveTermDescent [HasColimitsOfShape J C]
    (D : J ⥤ ComposableArrows C 4) (c : Cocone D) :
    D.flip ⋙ (colim : (J ⥤ C) ⥤ C) ⟶ c.pt where
  app i := colimit.desc (D.flip.obj i) (((evaluation (Fin 5) C).obj i).mapCocone c)
  naturality {i k} f := by
    apply colimit.hom_ext
    intro j
    simp only [Functor.comp_map, colim_map, ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc,
      Functor.mapCocone_ι_app]
    exact (c.ι.app j).naturality f

private theorem fiveTermDescent_isIso_middle
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (D : J ⥤ ComposableArrows C 4) (c : Cocone D)
    (h : ∀ j, (D.obj j).Exact) (hc : c.pt.Exact)
    (h₀ : IsColimit (((evaluation (Fin 5) C).obj 0).mapCocone c))
    (h₁ : IsColimit (((evaluation (Fin 5) C).obj 1).mapCocone c))
    (h₃ : IsColimit (((evaluation (Fin 5) C).obj 3).mapCocone c))
    (h₄ : IsColimit (((evaluation (Fin 5) C).obj 4).mapCocone c)) :
    IsIso ((fiveTermDescent D c).app 2) := by
  have iso_desc (i : Fin 5)
      (hi : IsColimit (((evaluation (Fin 5) C).obj i).mapCocone c)) :
      IsIso ((fiveTermDescent D c).app i) := by
    let e := (colimit.isColimit (D.flip.obj i)).coconePointUniqueUpToIso hi
    change IsIso e.hom
    infer_instance
  have : IsIso (ComposableArrows.app' (fiveTermDescent D c) 0) := iso_desc 0 h₀
  have : IsIso (ComposableArrows.app' (fiveTermDescent D c) 1) := iso_desc 1 h₁
  have : IsIso (ComposableArrows.app' (fiveTermDescent D c) 3) := iso_desc 3 h₃
  have : IsIso (ComposableArrows.app' (fiveTermDescent D c) 4) := iso_desc 4 h₄
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (exact_map_colim D.flip (exact_flip_of_pointwise D h)) hc
    (fiveTermDescent D c) inferInstance inferInstance inferInstance inferInstance

private def isColimit_of_iso_legs [HasColimitsOfShape J C] [IsConnected J]
    {F : J ⥤ C} (c : Cocone F) (h : ∀ j, IsIso (c.ι.app j)) : IsColimit c := by
  haveI (j : J) : IsIso (c.ι.app j) := h j
  haveI : IsIso c.ι := NatIso.isIso_of_isIso_app _
  exact c.isColimitOfIsIsoColimMapι

end ColimitLemmas

section RelativeComparison
open HomologicalComplex P202Specs.ChainLES

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The five consecutive terms surrounding relative cohomology in degree `q`. -/
def pairFiveTerms (q : ℤ) (P : Pair.{w}) : ComposableArrows (ModuleCat.{max u v w} R) 4 :=
  ComposableArrows.mk₄
    (homologyMap (restriction R A P) (q-1))
    (connecting (P202.CohomologyPairs.short_exact R A P) (q-1) q (by simp))
    (homologyMap (relativeToAbsolute R A P) q)
    (homologyMap (restriction R A P) q)

theorem pairFiveTerms_exact (q : ℤ) (P : Pair.{w}) : (pairFiveTerms R A q P).Exact := by
  have h := (P202.ChainLES.exactness (cochainSequence R A P)
    (P202.CohomologyPairs.short_exact R A P)).2 (q-1) q (by simp)
  exact ((ComposableArrows.exact_iff_δ₀ _).mp h).2

def pairFiveTermsMap (q : ℤ) {P Q : Pair.{w}} (f : P ⟶ Q) :
    pairFiveTerms R A q Q ⟶ pairFiveTerms R A q P := by
  have hn := P202.ChainLES.naturality (cochainSequenceMap R A f)
    (P202.CohomologyPairs.short_exact R A Q) (P202.CohomologyPairs.short_exact R A P)
  exact ComposableArrows.homMk₄
    ((ordinaryCohomologyFunctor R A (q-1)).map f.map.op)
    ((ordinaryCohomologyFunctor R A (q-1)).map f.restrict.op)
    ((relativeCohomologyFunctor R A q).map f.op)
    ((ordinaryCohomologyFunctor R A q).map f.map.op)
    ((ordinaryCohomologyFunctor R A q).map f.restrict.op)
    (hn.2.1 (q-1)) (hn.2.2 (q-1) q (by simp)) (hn.1 q) (hn.2.1 q)

def pairFiveTermsFunctor (q : ℤ) : Pair.{w}ᵒᵖ ⥤ ComposableArrows (ModuleCat.{max u v w} R) 4 where
  obj P := pairFiveTerms R A q P.unop
  map f := pairFiveTermsMap R A q f.unop
  map_id P := by
    apply NatTrans.ext
    funext i
    fin_cases i
    · exact (ordinaryCohomologyFunctor R A (q-1)).map_id _
    · exact (ordinaryCohomologyFunctor R A (q-1)).map_id _
    · exact (relativeCohomologyFunctor R A q).map_id _
    · exact (ordinaryCohomologyFunctor R A q).map_id _
    · exact (ordinaryCohomologyFunctor R A q).map_id _
  map_comp f g := by
    apply NatTrans.ext
    funext i
    fin_cases i
    · change (ordinaryCohomologyFunctor R A (q-1)).map _ =
        (ordinaryCohomologyFunctor R A (q-1)).map _ ≫
          (ordinaryCohomologyFunctor R A (q-1)).map _
      rw [← Functor.map_comp]
      rfl
    · change (ordinaryCohomologyFunctor R A (q-1)).map _ =
        (ordinaryCohomologyFunctor R A (q-1)).map _ ≫
          (ordinaryCohomologyFunctor R A (q-1)).map _
      rw [← Functor.map_comp]
      rfl
    · change (relativeCohomologyFunctor R A q).map _ =
        (relativeCohomologyFunctor R A q).map _ ≫
          (relativeCohomologyFunctor R A q).map _
      rw [← Functor.map_comp]
      rfl
    · change (ordinaryCohomologyFunctor R A q).map _ =
        (ordinaryCohomologyFunctor R A q).map _ ≫
          (ordinaryCohomologyFunctor R A q).map _
      rw [← Functor.map_comp]
      rfl
    · change (ordinaryCohomologyFunctor R A q).map _ =
        (ordinaryCohomologyFunctor R A q).map _ ≫
          (ordinaryCohomologyFunctor R A q).map _
      rw [← Functor.map_comp]
      rfl

instance openNeighborhood_isFiltered : IsFiltered (OpenNeighborhood K) where
  nonempty := ⟨⟨⊤, Set.subset_univ _⟩⟩
  cocone_objs U V :=
    ⟨⟨U.1 ⊓ V.1, fun _ hx => ⟨U.2 hx, V.2 hx⟩⟩,
      homOfLE (show (U.1 ⊓ V.1 : Opens X) ≤ U.1 from inf_le_left),
      homOfLE (show (U.1 ⊓ V.1 : Opens X) ≤ V.1 from inf_le_right), trivial⟩
  cocone_maps {_ Y} _f _g := ⟨Y, 𝟙 _, Subsingleton.elim _ _⟩

attribute [local instance] IsFiltered.isConnected

/-- Restriction to `K` is already a cocone of opposite pairs. -/
def neighborhoodPairRestrictionCocone : Cocone (neighborhoodPairs K) where
  pt := op (ambientPair K)
  ι :=
    { app := fun U => (ambientPairInclusion U.2).op
      naturality := fun _ _ _ => rfl }

/-- The source pair long exact sequences and their restriction cocone. -/
def fiveTermRestrictionCocone (q : ℤ) :
    Cocone (neighborhoodPairs K ⋙ pairFiveTermsFunctor R A q) :=
  (pairFiveTermsFunctor R A q).mapCocone (neighborhoodPairRestrictionCocone (K := K))

/-- The relative comparison follows from the ordinary comparison by filtered
exactness and the five lemma. This works for an arbitrary ambient space once
the shrinking retraction has been constructed. -/
theorem relativeComparison_of_shrinking
    (h : HasShrinkingRetraction K) (q : ℤ) : IsIso (relativeComparison K R A q) := by
  let : HasExactColimitsOfShape (OpenNeighborhood K) (ModuleCat.{max u v w} R) :=
    HasExactColimitsOfShape.domain_of_functor (OpenNeighborhood K)
      (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w})
  let D := neighborhoodPairs K ⋙ pairFiveTermsFunctor R A q
  let c := fiveTermRestrictionCocone (K := K) R A q
  have h₀ : IsColimit (((evaluation (Fin 5) (ModuleCat R)).obj 0).mapCocone c) := by
    apply isColimit_of_iso_legs
    intro U
    change IsIso ((ordinaryCohomologyFunctor R A (q-1)).map (𝟙 (TopCat.of X)).op)
    infer_instance
  have h₁ : IsColimit (((evaluation (Fin 5) (ModuleCat R)).obj 1).mapCocone c) :=
    ordinaryRestriction_isColimit_of_shrinking h R A (q-1)
  have h₃ : IsColimit (((evaluation (Fin 5) (ModuleCat R)).obj 3).mapCocone c) := by
    apply isColimit_of_iso_legs
    intro U
    change IsIso ((ordinaryCohomologyFunctor R A q).map (𝟙 (TopCat.of X)).op)
    infer_instance
  have h₄ : IsColimit (((evaluation (Fin 5) (ModuleCat R)).obj 4).mapCocone c) :=
    ordinaryRestriction_isColimit_of_shrinking h R A q
  exact fiveTermDescent_isIso_middle D c
    (fun U => pairFiveTerms_exact R A q (ambientPair (U.1 : Set X)))
    (pairFiveTerms_exact R A q (ambientPair K)) h₀ h₁ h₃ h₄

end RelativeComparison

theorem sphereRelativeComparison :
    P202Specs.Duality.NeighborhoodCohomology.relativeComparison.{u,v} := by
  intro n K hn hne hproper hK hLC R _ A _ _ q
  exact relativeComparison_of_shrinking R A
    (sphereShrinkingRetraction n K hn hne hproper hK hLC) q

end P202.Duality.NeighborhoodCohomology
