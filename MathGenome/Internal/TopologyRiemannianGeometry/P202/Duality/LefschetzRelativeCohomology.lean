import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LefschetzRelativeCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.RelativeFundamentalClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.PoincareDuality

/-! Collar-core cohomology comparisons for the first isomorphism of T31. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped TensorProduct
universe u v
namespace P202.LefschetzRelativeCohomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass P202Specs.CompactSupport
open P202Specs.LefschetzRelativeCohomology

variable (R : Type u) [CommRing R]

/-- For the bounded-below free relative singular complexes a homology
isomorphism is a chain homotopy equivalence. Dualizing preserves that
homotopy equivalence even over a noninjective coefficient ring. -/
theorem cohomology_isIso_of_homology_isIso {P Q : Pair.{v}} (f : P ⟶ Q)
    (hf : ∀ j : ℤ, IsIso ((relativeHomologyFunctor R R j).map f)) (p : ℤ) :
    IsIso ((relativeCohomologyFunctor R R p).map f.op) := by
  haveI : QuasiIso (relativeMap (ordinaryFunctor R R) f) := by
    rw [quasiIso_iff]
    intro j
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (hf j)
  haveI : ∀ j, Module.Free R ((ordinary R R P).X j) :=
    P202.CohomologyExcisionMV.relative_ordinary_free R P
  haveI : ∀ j, Module.Free R ((ordinary R R Q).X j) :=
    P202.CohomologyExcisionMV.relative_ordinary_free R Q
  obtain ⟨e, he⟩ := P202.FreeChainDual.homotopy_equivalence
    (ordinary R R P) (ordinary R R Q)
    ⟨0, fun j hj => (P202.RelativeSingularChains.ordinary_negative R R P j hj).1⟩
    ⟨0, fun j hj => (P202.RelativeSingularChains.ordinary_negative R R Q j hj).1⟩
    (relativeMap (ordinaryFunctor R R) f)
  haveI : QuasiIso ((relativeCochainFunctor R R).map f.op) := by
    have h := (P202.CohomologyExcisionMV.dualHomotopyEquiv R R e).quasiIso_hom
    change QuasiIso ((dualComplexFunctor R R (.down ℤ)).map e.hom.op) at h
    rw [he] at h
    exact h
  change IsIso (homologyMap ((relativeCochainFunctor R R).map f.op) p)
  infer_instance

/-- The relative-to-core cohomology arrow, with its contravariant direction,
is an isomorphism in every integer degree. -/
theorem corePullback_isIso {M : Type v} [TopologicalSpace M]
    {B : Set M} (c : Collar B) {t : ℝ} (ht : 0 < t) (p : ℤ) :
    IsIso ((relativeCohomologyFunctor R R p).map
      (relativeToCompact B (c.interiorCore t)).op) := by
  apply cohomology_isIso_of_homology_isIso R
  intro j
  haveI := P202.RelativeFundamentalClass.Collar.relativeToEarly_isIso c R ht j
  have he : P202.RelativeFundamentalClass.Collar.boundaryToEarly c ht ≫
      (P202.RelativeFundamentalClass.Collar.corePairIso c ht).hom =
        relativeToCompact B (c.interiorCore t) := PairMap.ext _ _ rfl
  rw [← he, Functor.map_comp]
  infer_instance

/-- Excision in cohomology at an arbitrary compact interior support. -/
theorem compactPullback_isIso {M : Type v} [TopologicalSpace M] [T2Space M]
    (B : Set M) (hB : IsClosed B) (K : Set (Interior B)) (hK : IsCompact K) (p : ℤ) :
    IsIso ((relativeCohomologyFunctor R R p).map (compactSupportInclusion B K).op) := by
  let D := P202.RelativeFundamentalClass.compactExcisionData B hB K hK
  haveI := P202.CohomologyExcisionMV.excision R R D p
  have he : (P202.RelativeFundamentalClass.compactExcisionIso B hB K hK).hom ≫ D.inclusion =
      compactSupportInclusion B K := PairMap.ext _ _ rfl
  rw [← he, op_comp, Functor.map_comp]
  infer_instance

variable {M : Type v} [TopologicalSpace M] [T2Space M]
  (B : Set M) (hB : IsClosed B)

/-- Restriction from ambient supported cohomology to the same interior support. -/
abbrev compactPullback (K : Support (Interior B)) (p : ℤ) :=
  (relativeCohomologyFunctor R R p).map
    (compactSupportInclusion B (K : Set (Interior B))).op

/-- The canonical map from a single compact interior support into H^p(M,B).
Its inverse-excision step is justified by the geometric theorem above. -/
def supportedToRelative (K : Support (Interior B)) (p : ℤ) :
    supportedCohomology R (Interior B) p K ⟶
      relativeCohomology R R (boundaryPair M B) p := by
  haveI := compactPullback_isIso R B hB K K.isCompact p
  exact inv (compactPullback R B K p) ≫
    (relativeCohomologyFunctor R R p).map (relativeToCompact B (K : Set (Interior B))).op

@[simp] theorem supportedToRelative_pullback (K : Support (Interior B)) (p : ℤ)
    (a : relativeCohomology R R (supportedPair M (Subtype.val '' (K : Set (Interior B)))) p) :
    supportedToRelative R B hB K p (compactPullback R B K p a) =
      ((relativeCohomologyFunctor R R p).map
        (relativeToCompact B (K : Set (Interior B))).op) a := by
  haveI := compactPullback_isIso R B hB K K.isCompact p
  change (compactPullback R B K p ≫ supportedToRelative R B hB K p) a = _
  simp [supportedToRelative, Category.assoc] <;> rfl

/-- Both pair-map squares commute strictly before passing to cohomology. -/
theorem supportedToRelative_transition (p : ℤ)
    (K L : Support (Interior B)) (h : K ≤ L) :
    ModuleCat.ofHom (transition R (Interior B) p K L h) ≫
      supportedToRelative R B hB L p = supportedToRelative R B hB K p := by
  haveI := compactPullback_isIso R B hB K K.isCompact p
  haveI := compactPullback_isIso R B hB L L.isCompact p
  let f : supportedPair M (Subtype.val '' (L : Set (Interior B))) ⟶
      supportedPair M (Subtype.val '' (K : Set (Interior B))) :=
    supportMap (Set.image_mono h)
  have hs : compactSupportInclusion B (L : Set (Interior B)) ≫ f =
      supportPairMap (Interior B) h ≫ compactSupportInclusion B (K : Set (Interior B)) :=
    PairMap.ext _ _ rfl
  have hr : relativeToCompact B (L : Set (Interior B)) ≫ f =
      relativeToCompact B (K : Set (Interior B)) := PairMap.ext _ _ rfl
  apply (cancel_epi (compactPullback R B K p)).mp
  dsimp only [supportedToRelative]
  rw [← Category.assoc]
  have hc : compactPullback R B K p ≫ ModuleCat.ofHom (transition R (Interior B) p K L h) =
      (relativeCohomologyFunctor R R p).map f.op ≫ compactPullback R B L p := by
    change (relativeCohomologyFunctor R R p).map _ ≫
        (relativeCohomologyFunctor R R p).map _ = _
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hs]
  rw [hc]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
    Category.id_comp]
  rw [← Functor.map_comp, ← op_comp, hr]

/-- Descent through the actual filtered colimit over all compact supports. -/
def compactToRelative (p : ℤ) : CompactCohomology R (Interior B) p →ₗ[R]
    relativeCohomology R R (boundaryPair M B) p :=
  descend R (Interior B) p (fun K => (supportedToRelative R B hB K p).hom) (by
    intro K L h a
    exact congrArg (fun f => f a) (supportedToRelative_transition R B hB p K L h))

@[simp] theorem compactToRelative_ofSupport (p : ℤ) (K : Support (Interior B))
    (a : supportedCohomology R (Interior B) p K) :
    compactToRelative R B hB p (ofSupport R (Interior B) p K a) =
      supportedToRelative R B hB K p a := by
  exact P202.CompactSupport.descend_ofSupport R (Interior B) p _ _ K a

/-- On a core the single-support comparison is an isomorphism. -/
theorem supportedToRelative_core_isIso [CompactSpace M] (c : Collar B)
    {t : ℝ} (ht : 0 < t) (p : ℤ) :
    IsIso (supportedToRelative R B hB
      ⟨c.interiorCore t, P202.RelativeFundamentalClass.Collar.interiorCore_isCompact c ht⟩ p) := by
  haveI := compactPullback_isIso R B hB (c.interiorCore t)
    (P202.RelativeFundamentalClass.Collar.interiorCore_isCompact c ht) p
  haveI := corePullback_isIso R c ht p
  dsimp only [supportedToRelative]
  infer_instance

/-- A cofinal collection of supports on which the comparison is an isomorphism
makes the descended map bijective. No injectivity of arbitrary support
transition maps is needed. -/
theorem compactToRelative_bijective (c : Collar B)
    (hM : IsCompact (Set.univ : Set M)) (p : ℤ) :
    Function.Bijective (compactToRelative R B hB p) := by
  letI : CompactSpace M := isCompact_univ_iff.mp hM
  have hcofinal (K : Support (Interior B)) :
      ∃ (L : Support (Interior B)), K ≤ L ∧ IsIso (supportedToRelative R B hB L p) := by
    obtain ⟨t, ht, _, hKt⟩ :=
      P202.RelativeFundamentalClass.Collar.cores_cofinal c hB.isCompact K K.isCompact
    refine ⟨⟨c.interiorCore t,
      P202.RelativeFundamentalClass.Collar.interiorCore_isCompact c ht⟩, hKt, ?_⟩
    exact supportedToRelative_core_isIso R B hB c ht p
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro a ha
      obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R (Interior B) p a
      change compactToRelative R B hB p (ofSupport R (Interior B) p K b) = 0 at ha
      rw [compactToRelative_ofSupport] at ha
      obtain ⟨L, hKL, hL⟩ := hcofinal K
      haveI := hL
      have hb : supportedToRelative R B hB L p (transition R (Interior B) p K L hKL b) = 0 := by
        rw [← compactToRelative_ofSupport,
          P202.CompactSupport.ofSupport_transition, compactToRelative_ofSupport]
        exact ha
      have hz := (ModuleCat.mono_iff_injective (supportedToRelative R B hB L p)).mp
        inferInstance (hb.trans (map_zero _).symm)
      change ofSupport R (Interior B) p K b = 0
      rw [← P202.CompactSupport.ofSupport_transition R (Interior B) p K L hKL b, hz,
        map_zero]
    · exact bot_le
  · intro a
    obtain ⟨K, _, hK⟩ := hcofinal ⊥
    haveI := hK
    obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (supportedToRelative R B hB K p)).mp
      inferInstance a
    exact ⟨ofSupport R (Interior B) p K b, by simpa using hb⟩

/-- The complete collar-core cohomology comparison, on the original theories. -/
theorem coreComparison : P202Specs.LefschetzRelativeCohomology.Expected.coreComparison.{u,v} := by
  intro R _ M _ _ B hB c hM
  refine ⟨fun t ht _ p => corePullback_isIso R c ht p,
    fun K hK p => compactPullback_isIso R B hB K hK p, ?_⟩
  intro p
  refine ⟨LinearEquiv.ofBijective (compactToRelative R B hB p)
    (compactToRelative_bijective R B hB c hM p), ?_⟩
  intro K a
  change compactToRelative R B hB p
    (ofSupport R (Interior B) p K (compactPullback R B K p a)) = _
  rw [compactToRelative_ofSupport, supportedToRelative_pullback]

namespace CollarPush
variable (c : Collar B)

/-- A compact half-collar is used only to glue the explicit collar motion
to the identity; it is not a homological certificate. -/
def stripTime (s : unitInterval) : CollarTime :=
  ⟨s.val / 2, div_nonneg s.property.1 (by norm_num), by have := s.property.2; linarith⟩

def stripMap : C(B × unitInterval, M) :=
  c.map.comp ⟨fun z => (z.1, stripTime z.2),
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).div_const 2 |>.subtype_mk _)⟩

def strip : Set M := Set.range (stripMap B c)

lemma strip_subset : strip B c ⊆ c.neighborhood := by
  rintro _ ⟨z, rfl⟩
  exact (c.homeomorph (z.1, stripTime z.2)).property

include hB in
lemma strip_isCompact (hM : IsCompact (Set.univ : Set M)) : IsCompact (strip B c) := by
  letI : CompactSpace M := isCompact_univ_iff.mp hM
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  exact isCompact_range (stripMap B c).continuous

/-- Raise time at least to one quarter of the homotopy parameter. -/
def pushTime (s : unitInterval) (t : CollarTime) : CollarTime :=
  ⟨max t.val (s.val/4), le_trans t.property.1 (le_max_left _ _),
    max_lt t.property.2 (by have := s.property.2; linarith)⟩

lemma pushTime_zero (t : CollarTime) : pushTime 0 t = t := by
  apply Subtype.ext
  simp [pushTime, max_eq_left t.property.1]

lemma pushTime_ne_zero (s : unitInterval) (t : CollarTime) (ht : t ≠ collarZero) :
    pushTime s t ≠ collarZero := by
  intro he
  apply ht
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change max t.val (s.val/4) = 0 at hh
  exact le_antisymm (le_trans (le_max_left _ _) hh.le) t.property.1

lemma pushTime_one_ne_zero (t : CollarTime) : pushTime 1 t ≠ collarZero := by
  intro he
  have hh := congrArg Subtype.val he
  change max t.val ((1:ℝ)/4) = 0 at hh
  have := le_max_right t.val ((1:ℝ)/4)
  linarith

/-- The continuous motion while inside the original collar neighborhood. -/
def inside : C(unitInterval × c.neighborhood, M) :=
  c.map.comp ⟨fun z => ((c.homeomorph.symm z.2).1,
    pushTime z.1 (c.homeomorph.symm z.2).2), by
      have hc := c.homeomorph.symm.continuous.comp
        (continuous_snd : Continuous (Prod.snd : unitInterval × c.neighborhood → _))
      exact (continuous_fst.comp hc).prodMk
        (((continuous_subtype_val.comp (continuous_snd.comp hc)).max
          ((continuous_subtype_val.comp continuous_fst).div_const 4)).subtype_mk _)⟩

lemma inside_zero (x : c.neighborhood) : inside B c (0,x) = x.val := by
  change c.map ((c.homeomorph.symm x).1, pushTime 0 (c.homeomorph.symm x).2) = x.val
  rw [pushTime_zero]
  exact congrArg Subtype.val (c.homeomorph.apply_symm_apply x)

lemma inside_outside (s : unitInterval) (x : c.neighborhood) (hx : x.val ∉ strip B c) :
    inside B c (s,x) = x.val := by
  have ht : 1/2 < (c.homeomorph.symm x).2.val := by
    by_contra hn
    have ht := le_of_not_gt hn
    let t : unitInterval := ⟨2*(c.homeomorph.symm x).2.val,
      by have := (c.homeomorph.symm x).2.property.1; linarith, by linarith⟩
    have he : stripTime t = (c.homeomorph.symm x).2 := by
      apply Subtype.ext
      dsimp [stripTime, t]
      ring
    apply hx
    refine ⟨((c.homeomorph.symm x).1,t), ?_⟩
    change c.map ((c.homeomorph.symm x).1,stripTime t) = x.val
    rw [he]
    exact congrArg Subtype.val (c.homeomorph.apply_symm_apply x)
  have he : pushTime s (c.homeomorph.symm x).2 = (c.homeomorph.symm x).2 := by
    apply Subtype.ext
    dsimp [pushTime]
    apply max_eq_left
    have := s.property.2
    linarith
  change c.map ((c.homeomorph.symm x).1,pushTime s (c.homeomorph.symm x).2) = x.val
  rw [he]
  exact congrArg Subtype.val (c.homeomorph.apply_symm_apply x)

/-- An open cover on which both formulas are ordinary continuous maps. -/
def patchSet : Bool → Set (unitInterval × M)
  | true => Prod.snd ⁻¹' c.neighborhood
  | false => Prod.snd ⁻¹' (strip B c)ᶜ

def patchMap : (i : Bool) → C(patchSet B c i, M)
  | true => (inside B c).comp ⟨fun z => (z.val.1, ⟨z.val.2,z.property⟩),
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩
  | false => ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

lemma patch_agree (i j : Bool) (z : unitInterval × M)
    (hi : z ∈ patchSet B c i) (hj : z ∈ patchSet B c j) :
    patchMap B c i ⟨z,hi⟩ = patchMap B c j ⟨z,hj⟩ := by
  cases i <;> cases j
  · rfl
  · exact (inside_outside B c z.1 ⟨z.2,hj⟩ hi).symm
  · exact inside_outside B c z.1 ⟨z.2,hi⟩ hj
  · rfl

include hB in
lemma patch_cover (hM : IsCompact (Set.univ : Set M)) (z : unitInterval × M) :
    ∃ i, patchSet B c i ∈ nhds z := by
  by_cases hz : z.2 ∈ c.neighborhood
  · exact ⟨true, (c.isOpen_neighborhood.preimage continuous_snd).mem_nhds hz⟩
  · refine ⟨false, (((strip_isCompact B hB c hM).isClosed.isOpen_compl).preimage
      continuous_snd).mem_nhds ?_⟩
    exact fun hs => hz (strip_subset B c hs)

/-- The global explicit inward motion, glued in the ordinary product topology. -/
def motion (hM : IsCompact (Set.univ : Set M)) : C(unitInterval × M, M) :=
  ContinuousMap.liftCover (patchSet B c) (patchMap B c) (patch_agree B c)
    (patch_cover B hB c hM)

lemma motion_inside (hM : IsCompact (Set.univ : Set M))
    (s : unitInterval) (x : c.neighborhood) :
    motion B hB c hM (s,x.val) = inside B c (s,x) := by
  exact ContinuousMap.liftCover_coe (i := true) ⟨(s,x.val),x.property⟩

lemma motion_outside (hM : IsCompact (Set.univ : Set M))
    (s : unitInterval) (x : M) (hx : x ∉ c.neighborhood) :
    motion B hB c hM (s,x) = x := by
  have hx' : x ∉ strip B c := fun hs => hx (strip_subset B c hs)
  exact ContinuousMap.liftCover_coe (S := patchSet B c) (i := false) ⟨(s,x),hx'⟩

lemma motion_zero (hM : IsCompact (Set.univ : Set M)) (x : M) :
    motion B hB c hM (0,x) = x := by
  by_cases hx : x ∈ c.neighborhood
  · rw [motion_inside B hB c hM 0 ⟨x,hx⟩, inside_zero]
  · exact motion_outside B hB c hM 0 x hx

lemma motion_preserves_interior (hM : IsCompact (Set.univ : Set M))
    (s : unitInterval) (x : Interior B) : motion B hB c hM (s,x.val) ∉ B := by
  by_cases hx : x.val ∈ c.neighborhood
  · rw [motion_inside B hB c hM s ⟨x.val,hx⟩]
    change c.map (_,pushTime s _) ∉ B
    rw [P202.RelativeFundamentalClass.Collar.map_mem_boundary_iff]
    apply pushTime_ne_zero
    intro he
    apply x.property
    have hh := congrArg Subtype.val (c.homeomorph.apply_symm_apply ⟨x.val,hx⟩)
    change c.map ((c.homeomorph.symm ⟨x.val,hx⟩).1,
      (c.homeomorph.symm ⟨x.val,hx⟩).2) = x.val at hh
    rw [he] at hh
    have hb : c.map ((c.homeomorph.symm ⟨x.val,hx⟩).1,collarZero) ∈ B := by
      exact (P202.RelativeFundamentalClass.Collar.map_mem_boundary_iff c _ _).2 rfl
    exact hh ▸ hb
  · rw [motion_outside B hB c hM s x.val hx]
    exact x.property

lemma motion_one_interior (hM : IsCompact (Set.univ : Set M)) (x : M) :
    motion B hB c hM (1,x) ∉ B := by
  by_cases hx : x ∈ c.neighborhood
  · rw [motion_inside B hB c hM 1 ⟨x,hx⟩]
    change c.map (_,pushTime 1 _) ∉ B
    rw [P202.RelativeFundamentalClass.Collar.map_mem_boundary_iff]
    exact pushTime_one_ne_zero _
  · rw [motion_outside B hB c hM 1 x hx]
    intro hb
    exact hx ((P202.RelativeFundamentalClass.Collar.boundary_subset_earlyRegion c
      (by norm_num : (0:ℝ)<1)) hb |>
        P202.RelativeFundamentalClass.Collar.earlyRegion_subset_neighborhood c 1)

/-- The homotopy inverse of the actual interior inclusion. -/
def retract (hM : IsCompact (Set.univ : Set M)) :
    TopCat.of M ⟶ TopCat.of (Interior B) :=
  TopCat.ofHom ⟨fun x => ⟨motion B hB c hM (1,x),motion_one_interior B hB c hM x⟩,
    ((motion B hB c hM).continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

def ambientHomotopy (hM : IsCompact (Set.univ : Set M)) :
    TopCat.Homotopy (𝟙 (TopCat.of M)) (retract B hB c hM ≫ interiorInclusion B) where
  toFun := motion B hB c hM
  continuous_toFun := (motion B hB c hM).continuous
  map_zero_left := motion_zero B hB c hM
  map_one_left _ := rfl

def interiorHomotopy (hM : IsCompact (Set.univ : Set M)) :
    TopCat.Homotopy (𝟙 (TopCat.of (Interior B)))
      (interiorInclusion B ≫ retract B hB c hM) where
  toFun z := ⟨motion B hB c hM (z.1,z.2.val),motion_preserves_interior B hB c hM z.1 z.2⟩
  continuous_toFun := ((motion B hB c hM).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (motion_zero B hB c hM x.val)
  map_one_left _ := rfl

end CollarPush

/-- Inward collar push proves the homotopy equivalence and all-degree
homology comparison without imposing connectedness or a nonempty boundary. -/
theorem interiorEquivalence :
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] (B : Set M),
    IsClosed B → ∀ (_c : Collar B), IsCompact (Set.univ : Set M) →
    (∃ r : TopCat.of M ⟶ TopCat.of (Interior B),
      Nonempty (TopCat.Homotopy (interiorInclusion B ≫ r) (𝟙 _)) ∧
      Nonempty (TopCat.Homotopy (r ≫ interiorInclusion B) (𝟙 _))) ∧
    ∀ (R : Type u) [CommRing R] (i : ℤ),
      IsIso ((homologyFunctor R R i).map (interiorInclusion B)) := by
  intro M _ _ B hB c hM
  refine ⟨⟨CollarPush.retract B hB c hM,
    ⟨(CollarPush.interiorHomotopy B hB c hM).symm⟩,
    ⟨(CollarPush.ambientHomotopy B hB c hM).symm⟩⟩, ?_⟩
  intro R _ i
  exact (P202.PrismHomotopy.equivalence R R (interiorInclusion B)
    (CollarPush.retract B hB c hM) (CollarPush.interiorHomotopy B hB c hM).symm
    (CollarPush.ambientHomotopy B hB c hM).symm i).1


/-- The universal representative law fixes any implementation of the pair
cap product to the already-constructed singular cap system. -/
theorem relativeCap_eq (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ)
    (a : relativeCohomology R R P (p : ℤ)) (z : relativeHomology R R P q) :
    c.relative P p q (a ⊗ₜ[R] z) =
      (P202.CapProducts.relativeSystem R P).homologyOp p q a z := by
  change c.relative P p q (a ⊗ₜ[R] z) =
    (P202.CapProducts.pairProductsData R).relative P p q (a ⊗ₜ[R] z)
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R P).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R P).homologyπ q)).mp inferInstance z
  obtain ⟨b, hb⟩ := P202.CapProducts.projection_surjective R P q ((ordinary R R P).iCycles q z)
  obtain ⟨v, hv, hc⟩ := c.relative_represents P p q a z b hb
  obtain ⟨w, hw, hd⟩ := (P202.CapProducts.pairProductsData R).relative_represents P p q a z b hb
  have he : v = w := (ModuleCat.mono_iff_injective
    ((ordinaryComplex R R P.space).iCycles (q-p))).mp inferInstance (hv.trans hw.symm)
  exact hc.trans (he ▸ hd.symm)

@[simp] theorem cap_nat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (n : ℕ) (o : LocalChoice R n (Interior B)) (p : ℕ) :
    cap R c B n o (p : ℤ) = capNat R c B n o p := by
  simp [cap]

/-- Cap compatibility on one compact interior support. The two applications
of cap naturality use exactly the pair maps in AgreesOnCompact. -/
theorem cap_compactToRelative_nat
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (d : DualityData.{u,v} R) (n : ℕ) (collar : Collar B)
    (AI : Manifold n (Interior B)) (o : Orientation R AI)
    (hM : IsCompact (Set.univ : Set M)) (p : ℕ)
    (a : CompactCohomology R (Interior B) (p : ℤ)) :
    cap R c B n o.val (p : ℤ) (compactToRelative R B hB (p : ℤ) a) =
      ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
        (d.D n (Interior B) AI o (p : ℤ) a) := by
  rw [P202.PoincareDuality.dualityMap_unique R (Interior B) d
    (P202.CompactSupport.dualityData R) AI o (p : ℤ)]
  change _ = ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
    (P202.CompactSupport.dualityInt R (Interior B) AI o (p : ℤ) a)
  rw [P202.CompactSupport.dualityInt_nat]
  obtain ⟨K, a, rfl⟩ := P202.CompactSupport.representatives R (Interior B) (p : ℤ) a
  haveI := compactPullback_isIso R B hB K K.isCompact (p : ℤ)
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (compactPullback R B K (p : ℤ))).mp
    inferInstance a
  rw [compactToRelative_ofSupport, supportedToRelative_pullback,
    P202.CompactSupport.duality_ofSupport, cap_nat]
  change c.relative (boundaryPair M B) p (n : ℤ)
      ((((relativeCohomologyFunctor R R (p : ℤ)).map (relativeToCompact B (K : Set (Interior B))).op) b)
        ⊗ₜ[R] fundamentalClass R B n o.val) = _
  rw [relativeCap_eq]
  have hr := P202.CompactSupport.homologyCap_natural R
    (relativeToCompact B (K : Set (Interior B))) p (n : ℤ) b
    (fundamentalClass R B n o.val)
  have hi := P202.CompactSupport.homologyCap_natural R
    (compactSupportInclusion B (K : Set (Interior B))) p (n : ℤ) b
    (P202.CompactSupport.fundamentalClass R (Interior B) AI o K)
  have hμ := P202.RelativeFundamentalClass.fundamentalClass_agreesOnCompact R n M B hB collar
    AI o hM K K.isCompact (P202.CompactSupport.fundamentalClass R (Interior B) AI o K)
    (P202.CompactSupport.fundamentalClass_values R (Interior B) AI o K)
  dsimp only [AgreesOnCompact] at hμ
  have hid : homologyMap (P202.CompactSupport.ordinaryMap R
      (relativeToCompact B (K : Set (Interior B))).map) ((n : ℤ)-p) = 𝟙 _ := by
    change homologyMap ((ordinaryFunctor R R).map (𝟙 _)) ((n : ℤ)-p) = _
    simp <;> rfl
  rw [hid] at hr
  change (P202.CapProducts.relativeSystem R (boundaryPair M B)).homologyOp p (n : ℤ)
    (((relativeCohomologyFunctor R R (p : ℤ)).map
      (relativeToCompact B (K : Set (Interior B))).op) b) (fundamentalClass R B n o.val) = _ at hr
  rw [hμ] at hr
  exact hr.trans hi.symm

/-- The comparison and cap diagram in all integer degrees, including the
zero negative-cohomology branches of both actual cap maps. -/
theorem cap_compactToRelative
    (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (d : DualityData.{u,v} R) (n : ℕ) (collar : Collar B)
    (AI : Manifold n (Interior B)) (o : Orientation R AI)
    (hM : IsCompact (Set.univ : Set M)) (p : ℤ)
    (a : CompactCohomology R (Interior B) p) :
    cap R c B n o.val p (compactToRelative R B hB p a) =
      ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
        (d.D n (Interior B) AI o p a) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact cap_compactToRelative_nat R B hB c d n collar AI o hM p a
  · rw [d.negative n (Interior B) AI o p (by omega), LinearMap.zero_apply, map_zero]
    simp [cap, hp]

/-- All-degree Poincaré–Lefschetz duality for the first cap map. -/
theorem duality : P202Specs.LefschetzRelativeCohomology.Expected.duality.{u,v} := by
  intro R _ c d n M _ A
  letI : T2Space M := A.hausdorff
  dsimp only
  intro collar AI o hM
  let B := manifoldBoundary A
  have hB : IsClosed B := P202.RelativeFundamentalClass.Geometry.manifoldBoundary_isClosed A
  let e (p : ℤ) := LinearEquiv.ofBijective (compactToRelative R B hB p)
    (compactToRelative_bijective R B hB collar hM p)
  have hcap (p : ℤ) (a : CompactCohomology R (Interior B) p) :
      cap R c B n o.val p (e p a) =
        ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
          (d.D n (Interior B) AI o p a) :=
    cap_compactToRelative R B hB c d n collar AI o hM p a
  refine ⟨?_, ?_⟩
  · intro p
    haveI := (interiorEquivalence M B hB collar hM).2 R ((n : ℤ)-p)
    have hi := (ConcreteCategory.isIso_iff_bijective
      ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))).mp inferInstance
    have hd := P202.PoincareDuality.duality R d n (Interior B) AI o p
    have hc : (fun a => cap R c B n o.val p (e p a)) =
        (fun a => ((homologyFunctor R R ((n : ℤ)-p)).map (interiorInclusion B))
          (d.D n (Interior B) AI o p a)) := funext (hcap p)
    apply (Function.Bijective.of_comp_iff (cap R c B n o.val p) (e p).bijective).mp
    change Function.Bijective (fun a => cap R c B n o.val p (e p a))
    rw [hc]
    exact hi.comp hd
  · intro p
    refine ⟨e p, ?_, hcap p⟩
    intro K a
    change compactToRelative R B hB p
      (ofSupport R (Interior B) p K (compactPullback R B K p a)) = _
    rw [compactToRelative_ofSupport, supportedToRelative_pullback]

include hB in
/-- Relative homology above dimension vanishes already at any compact core,
by excision and the orientation-independent compact-support dimension theorem. -/
theorem relative_aboveDimension (n : ℕ) (c : Collar B)
    (AI : Manifold n (Interior B)) (hM : IsCompact (Set.univ : Set M))
    (i : ℤ) (hi : (n : ℤ) < i) :
    IsZero (relativeHomology R R (boundaryPair M B) i) := by
  letI : CompactSpace M := isCompact_univ_iff.mp hM
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i by omega)
  let K := c.interiorCore (1/2)
  have hK : IsCompact K :=
    P202.RelativeFundamentalClass.Collar.interiorCore_isCompact c (by norm_num)
  haveI := P202.RelativeFundamentalClass.Collar.relativeToCompact_core_isIso c R
    (by norm_num : (0:ℝ)<1/2) j
  haveI := P202.RelativeFundamentalClass.compactSupportInclusion_isIso R B hB K hK j
  have hzero := P202.CompactOrientation.aboveDimension R n (Interior B) AI K hK j (by omega)
  have hz : IsZero (relativeHomology R R (supportedPair M (Subtype.val '' K)) (j : ℤ)) :=
    hzero.of_iso (asIso ((relativeHomologyFunctor R R (j : ℤ)).map
      (compactSupportInclusion B K))).symm
  exact hz.of_iso (asIso ((relativeHomologyFunctor R R (j : ℤ)).map
    (relativeToCompact B K)))

/-- The two above-dimension vanishing conclusions, as proved consequences.
The relative assertion does not need the second Lefschetz cap isomorphism. -/
theorem aboveDimension :
    P202Specs.LefschetzRelativeCohomology.Expected.aboveDimension.{u,v} := by
  intro R _ n M _ A
  letI : T2Space M := A.hausdorff
  dsimp only
  intro collar AI o hM i hi
  let B := manifoldBoundary A
  have hB : IsClosed B := P202.RelativeFundamentalClass.Geometry.manifoldBoundary_isClosed A
  haveI := (interiorEquivalence M B hB collar hM).2 R i
  exact ⟨(P202.PoincareDuality.aboveDimension R n (Interior B) AI o i hi).of_iso
      (asIso ((homologyFunctor R R i).map (interiorInclusion B))).symm,
    relative_aboveDimension R B hB n collar AI hM i hi⟩

end P202.LefschetzRelativeCohomology
