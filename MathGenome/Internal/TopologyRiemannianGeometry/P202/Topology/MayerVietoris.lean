import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainEquivalence
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainHomology

/-! The Mayer–Vietoris sequences of paper.tex `thm:p202-mv`.
The signed small-chain rows are identified with the actual singular and relative
complexes. The ordinary and reduced versions use the same source conventions,
including the augmentation of the empty space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
universe u v w
namespace P202.MayerVietoris
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains

lemma intersection_square (C : CoverPair.{v,w}) :
    C.toLeft ≫ C.leftInclusion = C.toRight ≫ C.rightInclusion := by
  apply PairMap.ext
  rfl

lemma left_square {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.leftInclusion ≫ f.map = f.onLeft ≫ D.leftInclusion := by
  apply PairMap.ext
  rfl

lemma right_square {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.rightInclusion ≫ f.map = f.onRight ≫ D.rightInclusion := by
  apply PairMap.ext
  rfl

lemma intersection_left_square {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.toLeft ≫ f.onLeft = f.onIntersection ≫ D.toLeft := by
  apply PairMap.ext
  rfl

lemma intersection_right_square {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    C.toRight ≫ f.onRight = f.onIntersection ≫ D.toRight := by
  apply PairMap.ext
  rfl

section Functor
variable {R : Type u} [CommRing R]
  (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)

lemma chainFirst_sum (C : CoverPair.{v,w}) : chainFirst F C ≫ chainSum F C = 0 := by
  simp only [chainFirst, chainSum, biprod.lift_desc, Preadditive.neg_comp,
    ← F.map_comp, intersection_square, add_neg_cancel]

lemma chainFirst_naturality {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    chainFirst F C ≫ middleMap F f = F.map f.onIntersection ≫ chainFirst F D := by
  apply biprod.hom_ext <;>
    simp only [chainFirst, middleMap, Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd, Preadditive.neg_comp,
      Preadditive.comp_neg, ← F.map_comp, intersection_left_square,
      intersection_right_square]

lemma chainSum_naturality {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    chainSum F C ≫ F.map f.map = middleMap F f ≫ chainSum F D := by
  apply biprod.hom_ext' <;>
    simp only [chainSum, middleMap, Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, ← F.map_comp, left_square, right_square]

lemma first_sum (C : CoverPair.{v,w}) (n : ℤ) : first F C n ≫ sum F C n = 0 := by
  simp only [first, sum, biprod.lift_desc, Preadditive.neg_comp,
    ← homologyMap_comp, ← F.map_comp, intersection_square, add_neg_cancel]

lemma first_naturality {C D : CoverPair.{v,w}} (f : CoverMap C D) (n : ℤ) :
    first F C n ≫ homologyMiddleMap F f n =
      homologyMap (F.map f.onIntersection) n ≫ first F D n := by
  apply biprod.hom_ext <;>
    simp only [first, homologyMiddleMap, Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd, Preadditive.neg_comp,
      Preadditive.comp_neg, ← homologyMap_comp, ← F.map_comp,
      intersection_left_square, intersection_right_square]

lemma sum_naturality {C D : CoverPair.{v,w}} (f : CoverMap C D) (n : ℤ) :
    sum F C n ≫ homologyMap (F.map f.map) n = homologyMiddleMap F f n ≫ sum F D n := by
  apply biprod.hom_ext' <;>
    simp only [sum, homologyMiddleMap, Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, ← homologyMap_comp, ← F.map_comp,
      left_square, right_square]

/-- The homology of the middle chain complex is canonically the direct sum
of the two homology modules appearing in the statement. -/
def middleHomologyIso (C : CoverPair.{v,w}) (n : ℤ) :
    (middle F C).homology n ≅ homologyMiddle F C n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℤ) n).mapBiprod _ _

lemma first_middleHomologyIso (C : CoverPair.{v,w}) (n : ℤ) :
    homologyMap (chainFirst F C) n ≫ (middleHomologyIso F C n).hom = first F C n := by
  dsimp only [homologyMiddle, middle, first, chainFirst, middleHomologyIso]
  simpa only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_obj, HomologicalComplex.homologyMap_neg] using
    biprod.map_lift_mapBiprod (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℤ) n)
      (F.obj C.leftPair) (F.obj C.rightPair) (F.map C.toLeft) (-F.map C.toRight)

lemma middleHomologyIso_sum (C : CoverPair.{v,w}) (n : ℤ) :
    (middleHomologyIso F C n).hom ≫ sum F C n = homologyMap (chainSum F C) n := by
  exact biprod.mapBiprod_hom_desc (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℤ) n)
    (F.obj C.leftPair) (F.obj C.rightPair) _ _

/-- Cokernel model of the complex generated by the two cover members. -/
abbrev presentation (C : CoverPair.{v,w}) : ShortComplex
    (ChainComplex (ModuleCat.{max u v} R) ℤ) :=
  ShortComplex.cokernelSequence (chainFirst F C)

def comparison (C : CoverPair.{v,w}) :
    (presentation F C).X₃ ⟶ F.obj C.pair :=
  cokernel.desc (chainFirst F C) (chainSum F C) (chainFirst_sum F C)

@[reassoc (attr := simp)] lemma presentation_comparison (C : CoverPair.{v,w}) :
    (presentation F C).g ≫ comparison F C = chainSum F C :=
  cokernel.π_desc _ _ _

/-- A cover map induces the actual map between cokernel presentations. -/
def presentationMap {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    presentation F C ⟶ presentation F D :=
  ShortComplex.Hom.mk (F.map f.onIntersection) (middleMap F f)
    (cokernel.map _ _ (F.map f.onIntersection) (middleMap F f)
      (chainFirst_naturality F f))
    (chainFirst_naturality F f).symm (by simp [presentation])

lemma comparison_naturality {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    comparison F C ≫ F.map f.map = (presentationMap F f).τ₃ ≫ comparison F D := by
  letI : Epi (presentation F C).g := inferInstanceAs (Epi (cokernel.π (chainFirst F C)))
  apply (cancel_epi (presentation F C).g).mp
  simp only [← Category.assoc, presentation_comparison]
  change chainSum F C ≫ F.map f.map =
    cokernel.π (chainFirst F C) ≫
      cokernel.map _ _ (F.map f.onIntersection) (middleMap F f)
        (chainFirst_naturality F f) ≫ comparison F D
  rw [cokernel.π_desc_assoc]
  simpa only [Category.assoc, show cokernel.π (chainFirst F D) ≫ comparison F D = chainSum F D from presentation_comparison F D] using chainSum_naturality F f

lemma presentation_shortExact (C : CoverPair.{v,w}) [Mono (chainFirst F C)] :
    (presentation F C).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := inferInstanceAs (Mono (chainFirst F C))
  epi_g := inferInstanceAs (Epi (cokernel.π (chainFirst F C)))

/-- Algebraic connecting map, transported along the small-to-ordinary comparison. -/
def connecting (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    Connecting.{u,v,w} F :=
  fun C n => by
    letI := hm C
    letI := hq C (n+1)
    exact inv (homologyMap (comparison F C) (n+1)) ≫
      (presentation_shortExact F C).δ (n+1) n rfl

lemma comparison_connecting
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n))
    (C : CoverPair.{v,w}) (n : ℤ) :
    homologyMap (comparison F C) (n+1) ≫ connecting F hm hq C n =
      (by letI := hm C; exact (presentation_shortExact F C).δ (n+1) n rfl) := by
  letI := hm C
  letI := hq C (n+1)
  dsimp only [connecting]
  rw [IsIso.hom_inv_id_assoc]

lemma connecting_natural
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    Natural F (connecting F hm hq) := by
  intro C D f
  refine ⟨fun n => first_naturality F f n, fun n => sum_naturality F f n, ?_⟩
  intro n
  letI := hm C
  letI := hm D
  letI := hq C (n+1)
  apply (cancel_epi (homologyMap (comparison F C) (n+1))).mp
  rw [← Category.assoc, comparison_connecting]
  rw [← Category.assoc, ← homologyMap_comp, comparison_naturality, homologyMap_comp]
  rw [Category.assoc, comparison_connecting]
  exact HomologicalComplex.HomologySequence.δ_naturality (presentationMap F f)
    (presentation_shortExact F C) (presentation_shortExact F D) (n+1) n rfl

lemma connecting_exact
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    Exact F (connecting F hm hq) := by
  have step : ∀ (C : CoverPair.{v,w}) (n : ℤ),
      homologyMap (presentation F C).g n ≫ homologyMap (comparison F C) n =
        (middleHomologyIso F C n).hom ≫ sum F C n := by
    intro C n
    rw [← homologyMap_comp, presentation_comparison, middleHomologyIso_sum]
  constructor
  · intro C n
    letI := hm C
    letI := hq C (n+1)
    letI := hq C n
    apply ComposableArrows.exact_of_iso (S₁ :=
      HomologicalComplex.HomologySequence.composableArrows₅ (presentation_shortExact F C)
        (n+1) n rfl) (ComposableArrows.isoMk₅
      (f := HomologicalComplex.HomologySequence.composableArrows₅ (presentation_shortExact F C)
        (n+1) n rfl)
      (g := ComposableArrows.mk₅ (first F C (n+1)) (sum F C (n+1))
        (connecting F hm hq C n) (first F C n) (sum F C n))
      (Iso.refl _) (middleHomologyIso F C (n+1))
      (asIso (homologyMap (comparison F C) (n+1)))
      (Iso.refl _) (middleHomologyIso F C n)
      (asIso (homologyMap (comparison F C) n))
      (by
        change homologyMap (chainFirst F C) (n+1) ≫ (middleHomologyIso F C (n+1)).hom =
          𝟙 _ ≫ first F C (n+1)
        rw [Category.id_comp]
        exact first_middleHomologyIso F C (n+1))
      (step C (n+1))
      (by
        change (presentation_shortExact F C).δ (n+1) n rfl ≫ 𝟙 _ =
          homologyMap (comparison F C) (n+1) ≫ connecting F hm hq C n
        rw [Category.comp_id]
        exact (comparison_connecting F hm hq C n).symm)
      (by
        change homologyMap (chainFirst F C) n ≫ (middleHomologyIso F C n).hom =
          𝟙 _ ≫ first F C n
        rw [Category.id_comp]
        exact first_middleHomologyIso F C n)
      (step C n))
    exact HomologicalComplex.HomologySequence.composableArrows₅_exact
      (presentation_shortExact F C) (n+1) n rfl
  · intro C n
    letI := hm C
    letI := hq C n
    apply ComposableArrows.exact_of_iso (S₁ :=
      HomologicalComplex.HomologySequence.composableArrows₂ (presentation F C) n)
      (ComposableArrows.isoMk₂
      (f := HomologicalComplex.HomologySequence.composableArrows₂ (presentation F C) n)
      (g := ComposableArrows.mk₂ (first F C n) (sum F C n))
      (Iso.refl _) (middleHomologyIso F C n)
      (asIso (homologyMap (comparison F C) n))
      (by
        change homologyMap (chainFirst F C) n ≫ (middleHomologyIso F C n).hom =
          𝟙 _ ≫ first F C n
        rw [Category.id_comp]
        exact first_middleHomologyIso F C n)
      (step C n))
    exact HomologicalComplex.HomologySequence.composableArrows₂_exact
      (presentation_shortExact F C) n

lemma classOf_iCycles (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (y : K.cycles n) (hy : K.d n (n-1) (K.iCycles n y) = 0) :
    classOf.{u,v} (R := R) K n (K.iCycles n y) hy = K.homologyπ n y := by
  change K.homologyπ n (K.cyclesMk _ (n-1) _ hy) = _
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk _ _ _ _

lemma classOf_surjective (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (y : K.homology n) :
    ∃ z : K.X n, ∃ hz : K.d n (n-1) z = 0,
      classOf.{u,v} (R := R) K n z hz = y := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance y
  have hc : K.d n (n-1) (K.iCycles n z) = 0 :=
    congrArg (fun f => f z) (K.iCycles_d n (n-1))
  exact ⟨K.iCycles n z, hc, (classOf_iCycles K n z hc).trans hz⟩

lemma classOf_map {K L : ChainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ L)
    (n : ℤ) (z : K.X n) (hz : K.d n (n-1) z = 0)
    (hfz : L.d n (n-1) (f.f n z) = 0) :
    homologyMap f n (classOf.{u,v} (R := R) K n z hz) =
      classOf.{u,v} (R := R) L n (f.f n z) hfz := by
  change homologyMap f n (K.homologyπ n (K.cyclesMk z (n-1) _ hz)) =
    L.homologyπ n (L.cyclesMk (f.f n z) (n-1) _ hfz)
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]
  have hn : (ComplexShape.down ℤ).next n = n-1 :=
    (ComplexShape.down ℤ).next_eq' (by simp)
  have hK : K.iCycles n (K.cyclesMk z (n-1) hn hz) = z := K.i_cyclesMk _ _ _ _
  have hL : L.iCycles n (L.cyclesMk (f.f n z) (n-1) hn hfz) = f.f n z := L.i_cyclesMk _ _ _ _
  rw [hK, hL]

lemma connecting_boundaryLifts
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hi : ∀ C : CoverPair.{v,w}, Mono (comparison F C)) : BoundaryLifts.{u,v,w} F := by
  intro C n c hc
  letI := hm C
  letI := hi C
  let hS := presentation_shortExact F C
  have hd : (presentation F C).X₃.d (n+1) n ((presentation F C).g.f (n+1) c) = 0 := by
    apply (ModuleCat.mono_iff_injective ((comparison F C).f n)).mp inferInstance
    rw [map_zero]
    rw [← ModuleCat.comp_apply, ← (comparison F C).comm, ModuleCat.comp_apply]
    have he : (comparison F C).f (n+1) ((presentation F C).g.f (n+1) c) =
        (chainSum F C).f (n+1) c :=
      congrArg (fun k => k.f (n+1) c) (presentation_comparison F C)
    rw [he]
    exact hc
  -- We already have a lift, so exactness directly supplies its boundary preimage.
  have hker : (presentation F C).g.f n ((middle F C).d (n+1) n c) = 0 := by
    exact (congrArg (fun k => k c) ((presentation F C).g.comm (n+1) n)).symm.trans hd
  obtain ⟨x, hx⟩ := ((ShortComplex.moduleCat_exact_iff _).mp
    (((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n).exact)) _ hker
  have hxcycle : (F.obj C.intersectionPair).d n (n-1) x = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply (n+1) n c x hx (n-1)
  refine ⟨x, ⟨hx, hxcycle⟩, ?_⟩
  intro y hy
  exact (ModuleCat.mono_iff_injective ((chainFirst F C).f n)).mp inferInstance
    (hy.1.trans hx.symm)

lemma connecting_boundaryFormula
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hi : ∀ C : CoverPair.{v,w}, Mono (comparison F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    BoundaryFormula F (connecting F hm hq) := by
  intro C n c hc x hx hxc
  letI := hm C
  letI := hi C
  let hS := presentation_shortExact F C
  let z := (presentation F C).g.f (n+1) c
  have hz : (presentation F C).X₃.d (n+1) n z = 0 := by
    apply (ModuleCat.mono_iff_injective ((comparison F C).f n)).mp inferInstance
    rw [map_zero]
    rw [← ModuleCat.comp_apply, ← (comparison F C).comm, ModuleCat.comp_apply]
    have he : (comparison F C).f (n+1) z = (chainSum F C).f (n+1) c :=
      congrArg (fun k => k.f (n+1) c) (presentation_comparison F C)
    rw [he]
    exact hc
  have hz' : (presentation F C).X₃.d (n+1) ((n+1)-1) z = 0 := by
    rw [add_sub_cancel_right]; exact hz
  have hs : (comparison F C).f (n+1) z = (chainSum F C).f (n+1) c :=
    congrArg (fun k => k.f (n+1) c) (presentation_comparison F C)
  have hcm := classOf_map (comparison F C) (n+1) z hz'
    (by rw [hs, add_sub_cancel_right]; exact hc)
  simp only [hs] at hcm
  rw [← hcm, ← ModuleCat.comp_apply, comparison_connecting]
  exact hS.δ_apply (n+1) n rfl z hz c rfl x hx (n-1)
    ((ComplexShape.down ℤ).next_eq' (by simp))

lemma smallRepresentatives_of_comparison
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    SmallRepresentatives.{u,v,w} F := by
  intro C n z hz
  letI := hq C n
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (homologyMap (comparison F C) n)).mp
    inferInstance (classOf.{u,v} (R := R) (F.obj C.pair) n z hz)
  obtain ⟨b, hb, hby⟩ := classOf_surjective (presentation F C).X₃ n y
  have hg : Epi ((presentation F C).g.f n) :=
    inferInstanceAs (Epi ((cokernel.π (chainFirst F C)).f n))
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective _).mp hg b
  have hbc : (comparison F C).f n b = (chainSum F C).f n c := by
    rw [← hc]
    exact congrArg (fun k => k.f n c) (presentation_comparison F C)
  have hcycle : (F.obj C.pair).d n (n-1) ((chainSum F C).f n c) = 0 := by
    rw [← hbc, ← ModuleCat.comp_apply, (comparison F C).comm, ModuleCat.comp_apply,
      hb, map_zero]
  refine ⟨c, hcycle, ?_⟩
  rw [← hy, ← hby]
  have hmap := classOf_map (comparison F C) n b hb (by rw [hbc]; exact hcycle)
  simp only [hbc] at hmap
  exact hmap.symm

/-- Complete algebraic assembly. Its hypotheses are local geometric obligations,
not additional assumptions in the original independent target. -/
theorem assemble
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hi : ∀ C : CoverPair.{v,w}, Mono (comparison F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n)) :
    (∃ δ : Connecting.{u,v,w} F, Exact F δ ∧ Natural F δ ∧ BoundaryFormula F δ) ∧
      SmallRepresentatives.{u,v,w} F ∧ BoundaryLifts.{u,v,w} F :=
  ⟨⟨connecting F hm hq, connecting_exact F hm hq, connecting_natural F hm hq,
      connecting_boundaryFormula F hm hi hq⟩,
    smallRepresentatives_of_comparison F hq, connecting_boundaryLifts F hm hi⟩

lemma endpoint_of_negative
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ), IsIso (homologyMap (comparison F C) n))
    (hz : ∀ C : CoverPair.{v,w}, IsZero ((F.obj C.intersectionPair).homology (-1)))
    (C : CoverPair.{v,w}) : Epi (sum F C 0) := by
  letI := hm C
  letI := hq C 0
  have hg : Epi (homologyMap (presentation F C).g 0) :=
    ((presentation_shortExact F C).homology_exact₃ 0 (-1) (by simp)).epi_f_iff.mpr
      ((hz C).eq_of_tgt _ _)
  have hfac : (middleHomologyIso F C 0).hom ≫ sum F C 0 =
      homologyMap (presentation F C).g 0 ≫ homologyMap (comparison F C) 0 := by
    rw [← homologyMap_comp, presentation_comparison, middleHomologyIso_sum]
  have : Epi ((middleHomologyIso F C 0).hom ≫ sum F C 0) := by
    rw [hfac]
    infer_instance
  exact epi_of_epi (middleHomologyIso F C 0).hom (sum F C 0)

lemma comparison_properties_of_shortExact (C : CoverPair.{v,w})
    {Q : ChainComplex (ModuleCat.{max u v} R) ℤ}
    (p : middle F C ⟶ Q) (j : Q ⟶ F.obj C.pair)
    (hpj : p ≫ j = chainSum F C)
    (hfp : chainFirst F C ≫ p = 0)
    (he : (ShortComplex.mk (chainFirst F C) p hfp).Exact)
    [Epi p] [Mono j]
    (hq : ∀ n, IsIso (homologyMap j n)) :
    Mono (comparison F C) ∧ ∀ n, IsIso (homologyMap (comparison F C) n) := by
  let d := cokernel.desc (chainFirst F C) p hfp
  have hd : cokernel.π (chainFirst F C) ≫ d = p := cokernel.π_desc _ _ _
  haveI : Mono d := he.mono_cokernelDesc
  haveI : Epi d := epi_of_epi_fac hd
  haveI : IsIso d := isIso_of_mono_of_epi d
  have hfac : comparison F C = d ≫ j := by
    apply (cancel_epi (cokernel.π (chainFirst F C))).mp
    rw [← Category.assoc, hd]
    exact (presentation_comparison F C).trans hpj.symm
  constructor
  · rw [hfac]
    infer_instance
  · intro n
    letI := hq n
    rw [hfac, homologyMap_comp]
    infer_instance

end Functor
/-- Ordinary absolute and relative theories vanish in degree -1, including
empty spaces and empty second terms. -/
lemma ordinary_negative (R : Type u) [CommRing R] (t : Theory)
    (ht : t = .ordinary ∨ t = .relative) (P : Pair.{v}) :
    IsZero (((theoryFunctor R t).obj P).homology (-1)) := by
  rcases ht with rfl | rfl
  · exact P202.SingularChains.ordinary_negative_homology R R P.space (-1) (by omega)
  · exact (P202.RelativeSingularChains.ordinary_negative R R P (-1) (by omega)).2

/-- The generic construction has the ordinary H₀ endpoint for both of the
ordinary theories once the presentation comparison is established. -/
lemma ordinary_endpoint_of_presentations (R : Type u) [CommRing R] (t : Theory)
    (ht : t = .ordinary ∨ t = .relative)
    (hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst (theoryFunctor R t) C))
    (hq : ∀ (C : CoverPair.{v,w}) (n : ℤ),
      IsIso (homologyMap (comparison (theoryFunctor R t) C) n))
    (C : CoverPair.{v,w}) : Epi (sum (theoryFunctor R t) C 0) :=
  endpoint_of_negative (theoryFunctor R t) hm hq
    (fun D => ordinary_negative R t ht D.intersectionPair) C

/-- In both absolute theories, the first chain arrow is injective because its
left component, followed by inclusion in X, is the actual intersection inclusion. -/
lemma absolute_chainFirst_mono (R : Type u) [CommRing R] (t : Theory)
    (ht : t = .ordinary ∨ t = .reduced) (C : CoverPair.{v,w}) :
    Mono (chainFirst (theoryFunctor R t) C) := by
  let F := theoryFunctor R t
  have hm : Mono (F.map (pieceInclusion C.pair (C.left ∩ C.right))) := by
    rcases ht with rfl | rfl
    · change Mono (inclusion (P202Specs.SingularChains.ordinaryFunctor R R)
        ⟨C.pair.space, C.left ∩ C.right⟩)
      infer_instance
    · change Mono (inclusion (P202Specs.SingularChains.reducedFunctor R R)
        ⟨C.pair.space, C.left ∩ C.right⟩)
      infer_instance
  have hfac : chainFirst F C ≫
      ((biprod.fst : middle F C ⟶ F.obj C.leftPair) ≫ F.map C.leftInclusion) =
        F.map (pieceInclusion C.pair (C.left ∩ C.right)) := by
    rw [chainFirst, biprod.lift_fst_assoc, ← F.map_comp]
    rfl
  exact mono_of_mono_fac hfac

section LinearDiagram
variable {R : Type u} [CommRing R]
  {A B D E : ModuleCat.{max u v} R}

lemma biprod_element_ext {x y : (B ⊞ D : ModuleCat.{max u v} R)}
    (h₁ : (biprod.fst : B ⊞ D ⟶ B) x = (biprod.fst : B ⊞ D ⟶ B) y)
    (h₂ : (biprod.snd : B ⊞ D ⟶ D) x = (biprod.snd : B ⊞ D ⟶ D) y) : x = y := by
  have h := congrArg (fun k : B ⊞ D ⟶ B ⊞ D => k x - k y)
    (biprod.total (X := B) (Y := D))
  have he : x - y = 0 := by
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
      h₁, h₂, sub_self, ModuleCat.id_apply] using h.symm
  exact sub_eq_zero.mp he

/-- The signed overlap diagram is exact as soon as its embedded ranges have
intersection equal to the overlap range. -/
lemma signed_biprod_exact (i : A ⟶ B) (j : A ⟶ D) (l : B ⟶ E) (r : D ⟶ E)
    (hcomm : i ≫ l = j ≫ r) (hl : Function.Injective l) (hr : Function.Injective r)
    (hinf : (i ≫ l).hom.range = l.hom.range ⊓ r.hom.range) :
    (ShortComplex.mk (biprod.lift i (-j)) (biprod.desc l r)
      (by simp only [biprod.lift_desc, Preadditive.neg_comp, hcomm, add_neg_cancel])).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  have hs : l ((biprod.fst : B ⊞ D ⟶ B) y) +
      r ((biprod.snd : B ⊞ D ⟶ D) y) = 0 := by
    simpa only [biprod.desc_eq, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.comp_apply] using hy
  have hneg : -r ((biprod.snd : B ⊞ D ⟶ D) y) =
      l ((biprod.fst : B ⊞ D ⟶ B) y) := by
    exact (eq_neg_of_add_eq_zero_left hs).symm
  have hmem : l ((biprod.fst : B ⊞ D ⟶ B) y) ∈ l.hom.range ⊓ r.hom.range :=
    ⟨⟨_, rfl⟩, ⟨-(biprod.snd : B ⊞ D ⟶ D) y, by rw [map_neg]; exact hneg⟩⟩
  rw [← hinf] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, biprod_element_ext ?_ ?_⟩
  · have hi : (biprod.fst : B ⊞ D ⟶ B) ((biprod.lift i (-j)) x) = i x :=
      congrArg (fun k : A ⟶ B => k x) (biprod.lift_fst i (-j))
    rw [hi]
    exact hl hx
  · have hj : (biprod.snd : B ⊞ D ⟶ D) ((biprod.lift i (-j)) x) = -j x :=
      congrArg (fun k : A ⟶ D => k x) (biprod.lift_snd i (-j))
    rw [hj]
    apply hr
    rw [map_neg]
    have hx' : r (j x) = l ((biprod.fst : B ⊞ D ⟶ B) y) :=
      (congrArg (fun k : A ⟶ E => k x) hcomm).symm.trans hx
    rw [hx', ← hneg, neg_neg]

end LinearDiagram

section Supports
open P202Specs.SingularChains P202Specs.SmallChainHomology
open scoped Simplicial
open Opposite
variable (R : Type u) [CommRing R]

/-- Simplices lying in a specified subspace, in the ambient simplex basis. -/
def simplexSet (X : TopCat.{v}) (B : Set X) (n : ℕ) : Set (Simplex X n) :=
  {s | Set.range (simplexEquiv X n s) ⊆ B}

lemma simplexSet_inter (X : TopCat.{v}) (B D : Set X) (n : ℕ) :
    simplexSet X (B ∩ D) n = simplexSet X B n ∩ simplexSet X D n := by
  ext s
  simp only [simplexSet, Set.mem_ofPred_eq, Set.subset_inter_iff, Set.mem_inter_iff]

/-- The actual subspace inclusion identifies chains with supported chains;
this holds for arbitrary subspaces, without any openness assumption. -/
lemma range_subspaceInclusion (X : TopCat.{v}) (B : Set X) (n : ℕ) :
    ((chainMap R R (Pair.inclusion ⟨X, B⟩)).f n).hom.range =
      Finsupp.supported R R (simplexSet X B n) := by
  let P : Pair := ⟨X, B⟩
  have hs : ∀ s : Simplex X n,
      s ∈ Set.range ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌)) ↔
        s ∈ simplexSet X B n := by
    intro s
    rw [P202.RelativeSingularChains.simplex_image]
    exact Set.range_subset_iff.symm
  ext c
  change c ∈ Set.range (Finsupp.mapDomain
    ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌))) ↔ _
  rw [Finsupp.mem_range_mapDomain_iff _
    (P202.RelativeSingularChains.simplex_injective P n), Finsupp.mem_supported']
  simp only [hs]
  rfl

/-- Duplicate simplex generators are precisely the intersection generators. -/
lemma range_intersection (X : TopCat.{v}) (B D : Set X) (n : ℕ) :
    ((chainMap R R (Pair.inclusion ⟨X, B ∩ D⟩)).f n).hom.range =
      ((chainMap R R (Pair.inclusion ⟨X, B⟩)).f n).hom.range ⊓
        ((chainMap R R (Pair.inclusion ⟨X, D⟩)).f n).hom.range := by
  rw [range_subspaceInclusion R, range_subspaceInclusion R, range_subspaceInclusion R,
    simplexSet_inter, Finsupp.supported_inter]

lemma smallModule_eq_sup (C : CoverPair.{v,w}) (n : ℕ) :
    smallModule R C.cover n =
      ((chainMap R R C.leftInclusion.map).f n).hom.range ⊔
        ((chainMap R R C.rightInclusion.map).f n).hom.range := by
  have hs : ({s | ∃ i, Set.range (simplexEquiv C.pair.space n s) ⊆ C.cover.sets i} :
      Set (Simplex C.pair.space n)) =
      simplexSet C.pair.space C.left n ∪ simplexSet C.pair.space C.right n := by
    ext s
    constructor
    · rintro ⟨⟨i⟩, hi⟩
      cases i with
      | false => exact Or.inl hi
      | true => exact Or.inr hi
    · rintro (h | h)
      · exact ⟨⟨false⟩, h⟩
      · exact ⟨⟨true⟩, h⟩
  change Finsupp.supported R R _ = _
  rw [hs, Finsupp.supported_union]
  change Finsupp.supported R R _ ⊔ Finsupp.supported R R _ =
    ((chainMap R R (Pair.inclusion ⟨C.pair.space, C.left⟩)).f n).hom.range ⊔
      ((chainMap R R (Pair.inclusion ⟨C.pair.space, C.right⟩)).f n).hom.range
  rw [range_subspaceInclusion, range_subspaceInclusion]

/-- Linear coordinates for actual chains on a subspace, retaining the ambient
simplex basis rather than replacing its index by an unrelated set. -/
def subspaceChainsEquiv (X : TopCat.{v}) (B : Set X) (n : ℕ) :
    Chains R (TopCat.of B) n ≃ₗ[R] Finsupp.supported R R (simplexSet X B n) :=
  (LinearEquiv.ofInjective ((chainMap R R (Pair.inclusion ⟨X, B⟩)).f n).hom
    (P202.RelativeSingularChains.inclusion_injective R R ⟨X, B⟩ n)).trans
      (LinearEquiv.ofEq _ _ (range_subspaceInclusion R X B n))

lemma subspaceChainsEquiv_val (X : TopCat.{v}) (B : Set X) (n : ℕ)
    (c : Chains R (TopCat.of B) n) :
    (subspaceChainsEquiv R X B n c).val =
      (chainMap R R (Pair.inclusion ⟨X, B⟩)).f n c := rfl

end Supports

section Nonnegative
open P202Specs.SingularChains P202Specs.SmallChainHomology
variable (R : Type u) [CommRing R]

abbrev middleN (C : CoverPair.{v,w}) :=
  complex R R C.leftPair.space ⊞ complex R R C.rightPair.space

def firstN (C : CoverPair.{v,w}) : complex R R C.intersectionPair.space ⟶ middleN R C :=
  biprod.lift (chainMap R R C.toLeft.map) (-chainMap R R C.toRight.map)

def sumN (C : CoverPair.{v,w}) : middleN R C ⟶ complex R R C.pair.space :=
  biprod.desc (chainMap R R C.leftInclusion.map) (chainMap R R C.rightInclusion.map)

lemma firstN_sumN (C : CoverPair.{v,w}) : firstN R C ≫ sumN R C = 0 := by
  simp only [firstN, sumN, biprod.lift_desc, Preadditive.neg_comp,
    ← (chainFunctor R R).map_comp]
  have h : C.toLeft.map ≫ C.leftInclusion.map =
      C.toRight.map ≫ C.rightInclusion.map := rfl
  rw [h, add_neg_cancel]

/-- The actual degree of a chain biproduct has the expected signed coordinates. -/
lemma firstN_degree (C : CoverPair.{v,w}) (n : ℕ) :
    (firstN R C).f n ≫ (biprodXIso _ _ n).hom =
      biprod.lift ((chainMap R R C.toLeft.map).f n)
        (-((chainMap R R C.toRight.map).f n)) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, biprodXIso_hom_fst, biprodXIso_hom_snd,
      firstN, biprod_lift_fst_f, biprod_lift_snd_f, biprod.lift_fst,
      biprod.lift_snd, neg_f_apply]

lemma sumN_degree (C : CoverPair.{v,w}) (n : ℕ) :
    (biprodXIso _ _ n).inv ≫ (sumN R C).f n =
      biprod.desc ((chainMap R R C.leftInclusion.map).f n)
        ((chainMap R R C.rightInclusion.map).f n) := by
  apply biprod.hom_ext' <;>
    simp only [← Category.assoc, inl_biprodXIso_inv, inr_biprodXIso_inv,
      sumN, biprod_inl_desc_f, biprod_inr_desc_f, biprod.inl_desc, biprod.inr_desc]

lemma firstN_mono (C : CoverPair.{v,w}) : Mono (firstN R C) := by
  have hfac : firstN R C ≫
      ((biprod.fst : middleN R C ⟶ complex R R C.leftPair.space) ≫
        chainMap R R C.leftInclusion.map) =
      chainMap R R (Pair.inclusion ⟨C.pair.space, C.left ∩ C.right⟩) := by
    rw [firstN, biprod.lift_fst_assoc, ← (chainFunctor R R).map_comp]
    rfl
  have : Mono (chainMap R R (Pair.inclusion ⟨C.pair.space, C.left ∩ C.right⟩)) :=
    inferInstanceAs (Mono (inclusion (chainFunctor R R) _))
  exact mono_of_mono_fac hfac

lemma nonnegative_overlap_exact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (firstN R C) (sumN R C) (firstN_sumN R C)).Exact := by
  apply HomologicalComplex.exact_of_degreewise_exact
  intro n
  have hc : (chainMap R R C.toLeft.map).f n ≫
      (chainMap R R C.leftInclusion.map).f n =
      (chainMap R R C.toRight.map).f n ≫
      (chainMap R R C.rightInclusion.map).f n := by
    rw [← comp_f, ← comp_f, ← (chainFunctor R R).map_comp,
      ← (chainFunctor R R).map_comp]
    rfl
  have hi : ((chainMap R R C.toLeft.map).f n ≫
      (chainMap R R C.leftInclusion.map).f n).hom.range =
      ((chainMap R R C.leftInclusion.map).f n).hom.range ⊓
      ((chainMap R R C.rightInclusion.map).f n).hom.range := by
    rw [← comp_f, ← (chainFunctor R R).map_comp]
    exact range_intersection R C.pair.space C.left C.right n
  have he := signed_biprod_exact _ _ _ _ hc
    (P202.RelativeSingularChains.inclusion_injective R R ⟨C.pair.space, C.left⟩ n)
    (P202.RelativeSingularChains.inclusion_injective R R ⟨C.pair.space, C.right⟩ n) hi
  let S := (ShortComplex.mk (firstN R C) (sumN R C) (firstN_sumN R C)).map
    (eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n)
  let T := ShortComplex.mk
    (biprod.lift ((chainMap R R C.toLeft.map).f n) (-((chainMap R R C.toRight.map).f n)))
    (biprod.desc ((chainMap R R C.leftInclusion.map).f n)
      ((chainMap R R C.rightInclusion.map).f n))
    (by simp only [biprod.lift_desc, Preadditive.neg_comp, hc, add_neg_cancel])
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (biprodXIso _ _ n) (Iso.refl _)
    (by
      change 𝟙 _ ≫ _ = (firstN R C).f n ≫ (biprodXIso _ _ n).hom
      rw [Category.id_comp]
      exact (firstN_degree R C n).symm)
    (by
      change (biprodXIso _ _ n).hom ≫
        biprod.desc ((chainMap R R C.leftInclusion.map).f n)
          ((chainMap R R C.rightInclusion.map).f n) = (sumN R C).f n ≫ 𝟙 _
      rw [← sumN_degree R C n, Iso.hom_inv_id_assoc, Category.comp_id])
  exact (ShortComplex.exact_iff_of_iso e).mpr he

/-- Each summand maps to the actual small subcomplex. -/
def pieceToSmall (C : CoverPair.{v,w}) (b : Bool) :
    complex R R (TopCat.of (C.cover.sets ⟨b⟩)) ⟶ smallComplex R C.cover :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (((chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩)).f n).hom.codRestrict
      (smallModule R C.cover n) (by
        intro c
        have hc : (chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩)).f n c ∈
            Finsupp.supported R R (simplexSet C.pair.space (C.cover.sets ⟨b⟩) n) := by
          rw [← range_subspaceInclusion R]; exact ⟨c, rfl⟩
        intro s hs
        exact ⟨⟨b⟩, hc hs⟩))) (by
    intro n
    simp only [smallComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (complex R R C.pair.space).d (n+1) n
        ((chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩)).f (n+1) c) =
      (chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩)).f n
        ((complex R R (TopCat.of (C.cover.sets ⟨b⟩))).d (n+1) n c)
    exact congrArg (fun f => f c)
      ((chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩)).comm (n+1) n))

@[reassoc (attr := simp)] lemma pieceToSmall_inclusion (C : CoverPair.{v,w}) (b : Bool) :
    pieceToSmall R C b ≫ smallInclusion R C.cover =
      chainMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩) := by
  ext n c
  rfl

def smallSumN (C : CoverPair.{v,w}) : middleN R C ⟶ smallComplex R C.cover :=
  biprod.desc (pieceToSmall R C false) (pieceToSmall R C true)

@[reassoc (attr := simp)] lemma smallSumN_inclusion (C : CoverPair.{v,w}) :
    smallSumN R C ≫ smallInclusion R C.cover = sumN R C := by
  apply biprod.hom_ext' <;>
    simp only [smallSumN, sumN, ← Category.assoc, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc, pieceToSmall_inclusion] <;> rfl

instance smallInclusion_mono (C : CoverPair.{v,w}) : Mono (smallInclusion R C.cover) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

lemma firstN_smallSumN (C : CoverPair.{v,w}) : firstN R C ≫ smallSumN R C = 0 := by
  apply (cancel_mono (smallInclusion R C.cover)).mp
  rw [Category.assoc, smallSumN_inclusion, firstN_sumN, zero_comp]

lemma smallSumN_epi (C : CoverPair.{v,w}) : Epi (smallSumN R C) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro c
  have hc := (show smallModule R C.cover n ≤ _ from
    (smallModule_eq_sup R C n).le) c.property
  obtain ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := Submodule.mem_sup.mp hc
  let z : (middleN R C).X n := (biprod.inl : _ ⟶ middleN R C).f n x +
    (biprod.inr : _ ⟶ middleN R C).f n y
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hz : (sumN R C).f n z = c.val := by
    dsimp only [z]
    rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      sumN, biprod_inl_desc_f, biprod_inr_desc_f]
    exact hab
  exact (congrArg (fun f => f.f n z) (smallSumN_inclusion R C)).trans hz

lemma nonnegative_small_shortExact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (firstN R C) (smallSumN R C) (firstN_smallSumN R C)).ShortExact := by
  letI := firstN_mono R C
  letI := smallSumN_epi R C
  refine {exact := ?_, mono_f := inferInstance, epi_g := inferInstance}
  let φ : ShortComplex.mk (firstN R C) (smallSumN R C) (firstN_smallSumN R C) ⟶
      ShortComplex.mk (firstN R C) (sumN R C) (firstN_sumN R C) :=
    ShortComplex.Hom.mk (𝟙 _) (𝟙 _) (smallInclusion R C.cover)
      (by simp) (by simpa using (smallSumN_inclusion R C).symm)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (nonnegative_overlap_exact R C)

end Nonnegative

lemma extend_shortExact {A ι ι' : Type*} [Category* A] [Abelian A]
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (S : ShortComplex (HomologicalComplex A c)) (hS : S.ShortExact) :
    (S.map (e.extendFunctor A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    let z : ((S.map (e.extendFunctor A)).map (eval A c' j)) ≅ S.map (eval A c i) :=
      ShortComplex.isoMk (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi)
        (S.X₃.extendXIso e hi)
        (by simp only [ShortComplex.map_f, ComplexShape.Embedding.extendFunctor_map,
          eval_map, extendMap_f _ e hi, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
        (by simp only [ShortComplex.map_g, ComplexShape.Embedding.extendFunctor_map,
          eval_map, extendMap_f _ e hi, Category.assoc, Iso.inv_hom_id,
          Category.comp_id])
    exact (ShortComplex.shortExact_iff_of_iso z).mpr
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS i)
  · have h₁ := S.X₁.isZero_extend_X e j (by simpa using hj)
    have h₂ := S.X₂.isZero_extend_X e j (by simpa using hj)
    have h₃ := S.X₃.isZero_extend_X e j (by simpa using hj)
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
            mono_f := h₁.mono _
            epi_g := h₃.epi _ }

lemma extendMap_mono {A ι ι' : Type*} [Category* A] [Abelian A]
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {K L : HomologicalComplex A c} (f : K ⟶ L) [Mono f] :
    Mono (HomologicalComplex.extendMap f e) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    rw [HomologicalComplex.extendMap_f f e hi]
    infer_instance
  · exact (K.isZero_extend_X e j (by simpa using hj)).mono _

def extendBiprodDesc {A ι ι' : Type*} [Category* A] [Abelian A]
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {K L Q : HomologicalComplex A c} (p : K ⊞ L ⟶ Q) :
    K.extend e ⊞ L.extend e ⟶ Q.extend e :=
  ((e.extendFunctor A).mapBiprod K L).inv ≫ HomologicalComplex.extendMap p e

lemma extend_signed_zero {A ι ι' : Type*} [Category* A] [Abelian A]
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {I K L Q : HomologicalComplex A c} (i : I ⟶ K) (j : I ⟶ L)
    (p : K ⊞ L ⟶ Q) (h : biprod.lift i (-j) ≫ p = 0) :
    biprod.lift (HomologicalComplex.extendMap i e) (-HomologicalComplex.extendMap j e) ≫
      extendBiprodDesc e p = 0 := by
  let E := e.extendFunctor A
  have hf : E.map (biprod.lift i (-j)) ≫ (E.mapBiprod K L).hom =
      biprod.lift (E.map i) (-E.map j) := by
    simpa only [E.map_neg] using biprod.map_lift_mapBiprod E K L i (-j)
  change biprod.lift (E.map i) (-E.map j) ≫
    ((E.mapBiprod K L).inv ≫ E.map p) = 0
  rw [← hf, Category.assoc, Iso.hom_inv_id_assoc, ← E.map_comp, h, E.map_zero]

lemma extend_signed_shortExact {A ι ι' : Type*} [Category* A] [Abelian A]
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {I K L Q : HomologicalComplex A c} (i : I ⟶ K) (j : I ⟶ L)
    (p : K ⊞ L ⟶ Q) (h : biprod.lift i (-j) ≫ p = 0)
    (hS : (ShortComplex.mk (biprod.lift i (-j)) p h).ShortExact) :
    (ShortComplex.mk
      (biprod.lift (HomologicalComplex.extendMap i e) (-HomologicalComplex.extendMap j e))
      (extendBiprodDesc e p) (extend_signed_zero e i j p h)).ShortExact := by
  let E := e.extendFunctor A
  let S := ShortComplex.mk (biprod.lift i (-j)) p h
  let T := ShortComplex.mk
    (biprod.lift (HomologicalComplex.extendMap i e) (-HomologicalComplex.extendMap j e))
    (extendBiprodDesc e p) (extend_signed_zero e i j p h)
  refine ShortComplex.shortExact_of_iso (S₁ := S.map E) (S₂ := T) ?_
    (extend_shortExact e S hS)
  refine ShortComplex.isoMk (S₁ := S.map E) (S₂ := T)
    (Iso.refl _) (E.mapBiprod K L) (Iso.refl _) ?_ ?_
  · symm
    change E.map (biprod.lift i (-j)) ≫ (E.mapBiprod K L).hom =
      𝟙 _ ≫ biprod.lift (E.map i) (-E.map j)
    rw [Category.id_comp]
    simpa only [E.map_neg] using biprod.map_lift_mapBiprod E K L i (-j)
  · symm
    change E.map p ≫ 𝟙 _ = (E.mapBiprod K L).hom ≫
      ((E.mapBiprod K L).inv ≫ E.map p)
    rw [Category.comp_id, Iso.hom_inv_id_assoc]

section Ordinary
open P202Specs.MayerVietoris P202Specs.SingularChains P202Specs.SmallChainHomology
variable (R : Type u) [CommRing R]

def ordinarySmallComplex (C : CoverPair.{v,w}) :=
  (smallComplex R C.cover).extend (degreeEmbedding 0)

def ordinarySmallSum (C : CoverPair.{v,w}) :
    middle (theoryFunctor R .ordinary) C ⟶ ordinarySmallComplex R C :=
  extendBiprodDesc (degreeEmbedding 0) (smallSumN R C)

def ordinarySmallInclusion (C : CoverPair.{v,w}) :
    ordinarySmallComplex R C ⟶ (theoryFunctor R .ordinary).obj C.pair :=
  HomologicalComplex.extendMap (smallInclusion R C.cover) (degreeEmbedding 0)

lemma ordinaryFirst_smallSum (C : CoverPair.{v,w}) :
    chainFirst (theoryFunctor R .ordinary) C ≫ ordinarySmallSum R C = 0 :=
  extend_signed_zero (degreeEmbedding 0)
    (chainMap R R C.toLeft.map) (chainMap R R C.toRight.map)
    (smallSumN R C) (firstN_smallSumN R C)

lemma ordinarySmall_shortExact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (chainFirst (theoryFunctor R .ordinary) C)
      (ordinarySmallSum R C) (ordinaryFirst_smallSum R C)).ShortExact :=
  extend_signed_shortExact (degreeEmbedding 0)
    (chainMap R R C.toLeft.map) (chainMap R R C.toRight.map)
    (smallSumN R C) (firstN_smallSumN R C) (nonnegative_small_shortExact R C)

lemma ordinarySmallSum_inclusion (C : CoverPair.{v,w}) :
    ordinarySmallSum R C ≫ ordinarySmallInclusion R C =
      chainSum (theoryFunctor R .ordinary) C := by
  let E := (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R)
  change (E.mapBiprod _ _).inv ≫ E.map (smallSumN R C) ≫
    E.map (smallInclusion R C.cover) = _
  rw [← E.map_comp, smallSumN_inclusion]
  exact biprod.mapBiprod_inv_map_desc E _ _ _ _

lemma ordinarySmallInclusion_mono (C : CoverPair.{v,w}) :
    Mono (ordinarySmallInclusion R C) :=
  extendMap_mono (degreeEmbedding 0) (smallInclusion R C.cover)

lemma ordinarySmallInclusion_quasiIso (C : CoverPair.{v,w}) :
    QuasiIso (ordinarySmallInclusion R C) := by
  have h : QuasiIso (smallInclusion R C.cover) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
      (P202.SmallChainHomology.absoluteComparison R C.pair.space _ C.cover n)
  exact (quasiIso_extendMap_iff (smallInclusion R C.cover) (degreeEmbedding 0)).mpr h

end Ordinary



section
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.SmallChainHomology

variable (R : Type u) [CommRing R]
variable {X : TopCat.{v}} {ι : Type w}

lemma smallModule_zero_all (U : OpenCover X ι) (c : Chains R X 0) :
    c ∈ smallModule R U 0 := by
  intro s hs
  let a : Convexity.StdSimplex ℝ (Fin 1) := Convexity.StdSimplex.single 0
  obtain ⟨i, hi⟩ := U.covers (simplexEquiv X 0 s a)
  refine ⟨i, ?_⟩
  rintro y ⟨x, rfl⟩
  have hxa : x = a := by apply Convexity.StdSimplex.ext; ext j; simp
  simpa only [hxa] using hi

def smallAugmentation (U : OpenCover X ι) :
    (smallComplex R U).X 0 ⟶ coefficientModule.{u,u,v} R R :=
  (smallInclusion R U).f 0 ≫ augmentation R R X

lemma smallAugmentation_boundary (U : OpenCover X ι) :
    (smallComplex R U).d 1 0 ≫ smallAugmentation R U = 0 := by
  rw [smallAugmentation, ← Category.assoc, ← (smallInclusion R U).comm,
    Category.assoc, augmentation_boundary, comp_zero]

def augmentedSmall (U : OpenCover X ι) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.augment (smallComplex R U) (smallAugmentation R U)
    (smallAugmentation_boundary R U)

def augmentedSmallInclusion (U : OpenCover X ι) :
    augmentedSmall R U ⟶ augmentedShifted R R X :=
  ChainComplex.ofHom (fun n => match n with
    | 0 => 𝟙 _
    | n+1 => (smallInclusion R U).f n) (by
    intro n
    cases n with
    | zero => simp [augmentedSmall, augmentedShifted, smallAugmentation]
    | succ n => simpa [augmentedSmall, augmentedShifted] using
        (smallInclusion R U).comm (n+1) n)

lemma boundary_lift_of_quasiIso {S T : ShortComplex (ModuleCat.{v} R)}
    (f : S ⟶ T) (hf : ShortComplex.QuasiIso f)
    (x : S.X₂) (hx : S.g x = 0) (y : T.X₁) (hy : T.f y = f.τ₂ x) :
    ∃ a : S.X₁, S.f a = x := by
  let γ : ShortComplex.LeftHomologyMapData f
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (z : S.g.hom.ker) : (γ.φK z).val = f.τ₂ z.val := by
    exact congrArg (fun g => g z) γ.commi
  have hH (z : S.g.hom.ker) :
      γ.φH (Submodule.Quotient.mk z) = Submodule.Quotient.mk (γ.φK z) := by
    exact congrArg (fun g => g z) γ.commπ
  letI : IsIso γ.φH := γ.quasiIso_iff.mp hf
  have hinj := (ConcreteCategory.isIso_iff_bijective γ.φH).mp inferInstance
  have hz : γ.φH (Submodule.Quotient.mk (⟨x,hx⟩ : S.g.hom.ker)) = 0 := by
    rw [hH]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨y, Subtype.ext (hy.trans (hK ⟨x,hx⟩).symm)⟩
  have hzero := hinj.1 (hz.trans (map_zero _).symm)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
  exact ⟨a, congrArg Subtype.val ha⟩

lemma augmentedSmallInclusion_quasiIso (U : OpenCover X ι) :
    QuasiIso (augmentedSmallInclusion R U) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    apply (quasiIsoAt_iff' _ 1 0 0 (by simp) (by simp)).mpr
    apply (ShortComplex.quasiIso_iff _).mpr
    apply P202.SmallChainHomology.shortComplex_comparison
    · intro z hz
      refine ⟨z, ?_, 0, ?_⟩
      · change (augmentedSmall R U).d 0 0 z = 0
        rw [(augmentedSmall R U).shape 0 0 (by simp)]
        rfl
      · change z - z = augmentation R R X 0
        rw [sub_self, map_zero]
    · intro x hx y hy
      refine ⟨⟨y, smallModule_zero_all R U y⟩, ?_⟩
      change (smallAugmentation R U) _ = x
      change augmentation R R X y = x at hy
      exact hy
  | succ n =>
    cases n with
    | zero =>
      apply (quasiIsoAt_iff' _ 2 1 0 (by simp) (by simp)).mpr
      apply (ShortComplex.quasiIso_iff _).mpr
      apply P202.SmallChainHomology.shortComplex_comparison
      · intro z hz
        refine ⟨⟨z, smallModule_zero_all R U z⟩, ?_, 0, ?_⟩
        · exact hz
        · change z - z = (complex R R X).d 1 0 0
          rw [sub_self, map_zero]
      · intro x hx y hy
        have hq : QuasiIsoAt (smallInclusion R U) 0 :=
          (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
            (P202.SmallChainHomology.absoluteComparison R X ι U 0)
        have hq' := (quasiIsoAt_iff' (smallInclusion R U) 1 0 0 (by simp) (by simp)).mp hq
        apply boundary_lift_of_quasiIso R _ hq' x
        · change (smallComplex R U).d 0 0 x = 0
          rw [(smallComplex R U).shape 0 0 (by simp)]
          rfl
        · exact hy
    | succ n =>
      apply (quasiIsoAt_iff' _ (n+3) (n+2) (n+1) (by simp) (by simp)).mpr
      have hq : QuasiIsoAt (smallInclusion R U) (n+1) :=
        (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
          (P202.SmallChainHomology.absoluteComparison R X ι U (n+1))
      have hq' := (quasiIsoAt_iff' (smallInclusion R U) (n+2) (n+1) n
        (by simp) (by simp)).mp hq
      exact hq'

def pieceToAugmentedSmall (C : CoverPair.{v,w}) (b : Bool) :
    augmentedShifted R R (TopCat.of (C.cover.sets ⟨b⟩)) ⟶ augmentedSmall R C.cover :=
  ChainComplex.ofHom (fun n => match n with
    | 0 => 𝟙 _
    | n+1 => (pieceToSmall R C b).f n) (by
    intro n
    cases n with
    | zero =>
      change (pieceToSmall R C b).f 0 ≫
        ((smallInclusion R C.cover).f 0 ≫ augmentation R R C.pair.space) =
          augmentation R R (TopCat.of (C.cover.sets ⟨b⟩)) ≫ 𝟙 _
      rw [← Category.assoc, ← comp_f, pieceToSmall_inclusion,
        augmentation_naturality, Category.comp_id]
    | succ n => simpa [augmentedSmall, augmentedShifted] using
        (pieceToSmall R C b).comm (n+1) n)

@[reassoc (attr := simp)] lemma pieceToAugmentedSmall_inclusion
    (C : CoverPair.{v,w}) (b : Bool) :
    pieceToAugmentedSmall R C b ≫ augmentedSmallInclusion R C.cover =
      augmentedShiftedMap R R (Pair.inclusion ⟨C.pair.space, C.cover.sets ⟨b⟩⟩) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => simp [pieceToAugmentedSmall, augmentedSmallInclusion, augmentedShiftedMap]
  | succ n => exact congrArg (fun f => f.f n) (pieceToSmall_inclusion R C b)

abbrev middleAugN (C : CoverPair.{v,w}) :=
  augmentedShifted R R C.leftPair.space ⊞ augmentedShifted R R C.rightPair.space

def firstAugN (C : CoverPair.{v,w}) :
    augmentedShifted R R C.intersectionPair.space ⟶ middleAugN R C :=
  biprod.lift (augmentedShiftedMap R R C.toLeft.map) (-augmentedShiftedMap R R C.toRight.map)

def sumAugN (C : CoverPair.{v,w}) :
    middleAugN R C ⟶ augmentedShifted R R C.pair.space :=
  biprod.desc (augmentedShiftedMap R R C.leftInclusion.map)
    (augmentedShiftedMap R R C.rightInclusion.map)

def smallSumAugN (C : CoverPair.{v,w}) : middleAugN R C ⟶ augmentedSmall R C.cover :=
  biprod.desc (pieceToAugmentedSmall R C false) (pieceToAugmentedSmall R C true)

@[reassoc (attr := simp)] lemma smallSumAugN_inclusion (C : CoverPair.{v,w}) :
    smallSumAugN R C ≫ augmentedSmallInclusion R C.cover = sumAugN R C := by
  apply biprod.hom_ext' <;>
    simp only [smallSumAugN, sumAugN, ← Category.assoc, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc,
      pieceToAugmentedSmall_inclusion] <;> rfl

instance augmentedSmallInclusion_mono (U : OpenCover X ι) :
    Mono (augmentedSmallInclusion R U) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  cases n with
  | zero => change Mono (𝟙 _); infer_instance
  | succ n => exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

lemma firstAugN_smallSumAugN (C : CoverPair.{v,w}) :
    firstAugN R C ≫ smallSumAugN R C = 0 := by
  apply (cancel_mono (augmentedSmallInclusion R C.cover)).mp
  rw [Category.assoc, smallSumAugN_inclusion, zero_comp]
  change biprod.lift ((augmentedShiftedFunctor R R).map C.toLeft.map)
    (-((augmentedShiftedFunctor R R).map C.toRight.map)) ≫
    biprod.desc ((augmentedShiftedFunctor R R).map C.leftInclusion.map)
      ((augmentedShiftedFunctor R R).map C.rightInclusion.map) = 0
  simp only [biprod.lift_desc, Preadditive.neg_comp,
    ← (augmentedShiftedFunctor R R).map_comp]
  have h : C.toLeft.map ≫ C.leftInclusion.map =
      C.toRight.map ≫ C.rightInclusion.map := rfl
  rw [h, add_neg_cancel]

lemma firstAugN_degree (C : CoverPair.{v,w}) (n : ℕ) :
    (firstAugN R C).f n ≫ (biprodXIso _ _ n).hom =
      biprod.lift ((augmentedShiftedMap R R C.toLeft.map).f n)
        (-((augmentedShiftedMap R R C.toRight.map).f n)) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, biprodXIso_hom_fst, biprodXIso_hom_snd,
      firstAugN, biprod_lift_fst_f, biprod_lift_snd_f, biprod.lift_fst,
      biprod.lift_snd, neg_f_apply]

lemma smallSumAugN_degree (C : CoverPair.{v,w}) (n : ℕ) :
    (biprodXIso _ _ n).inv ≫ (smallSumAugN R C).f n =
      biprod.desc ((pieceToAugmentedSmall R C false).f n)
        ((pieceToAugmentedSmall R C true).f n) := by
  apply biprod.hom_ext' <;>
    simp only [← Category.assoc, inl_biprodXIso_inv, inr_biprodXIso_inv,
      smallSumAugN, biprod_inl_desc_f, biprod_inr_desc_f,
      biprod.inl_desc, biprod.inr_desc]

lemma smallSumN_degree (C : CoverPair.{v,w}) (n : ℕ) :
    (biprodXIso _ _ n).inv ≫ (smallSumN R C).f n =
      biprod.desc ((pieceToSmall R C false).f n)
        ((pieceToSmall R C true).f n) := by
  apply biprod.hom_ext' <;>
    simp only [← Category.assoc, inl_biprodXIso_inv, inr_biprodXIso_inv,
      smallSumN, biprod_inl_desc_f, biprod_inr_desc_f,
      biprod.inl_desc, biprod.inr_desc]

lemma augmented_small_shortExact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (firstAugN R C) (smallSumAugN R C)
      (firstAugN_smallSumAugN R C)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    let A := coefficientModule.{u,u,v} R R
    let T : ShortComplex (ModuleCat.{max u v} R) :=
      ShortComplex.mk (biprod.lift (𝟙 A) (-𝟙 A)) (biprod.desc (𝟙 A) (𝟙 A))
        (by simp only [biprod.lift_desc, Category.id_comp, Preadditive.neg_comp, add_neg_cancel])
    let S := (ShortComplex.mk (firstAugN R C) (smallSumAugN R C)
      (firstAugN_smallSumAugN R C)).map (eval _ _ 0)
    let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (biprodXIso _ _ 0) (Iso.refl _)
      (by
        change 𝟙 _ ≫ _ = (firstAugN R C).f 0 ≫ (biprodXIso _ _ 0).hom
        rw [Category.id_comp, firstAugN_degree]
        rfl)
      (by
        change (biprodXIso (augmentedShifted R R C.leftPair.space)
          (augmentedShifted R R C.rightPair.space) 0).hom ≫
          biprod.desc ((pieceToAugmentedSmall R C false).f 0)
            ((pieceToAugmentedSmall R C true).f 0) = (smallSumAugN R C).f 0 ≫ 𝟙 _
        erw [← smallSumAugN_degree R C 0, Iso.hom_inv_id_assoc, Category.comp_id])
    apply (ShortComplex.shortExact_iff_of_iso e).mpr
    have hm : Mono (biprod.lift (𝟙 A) (-𝟙 A)) :=
      mono_of_mono_fac (biprod.lift_fst (𝟙 A) (-𝟙 A))
    have he : Epi (biprod.desc (𝟙 A) (𝟙 A)) :=
      epi_of_epi_fac (biprod.inl_desc (𝟙 A) (𝟙 A))
    refine { exact := ?_, mono_f := hm, epi_g := he }
    apply signed_biprod_exact (𝟙 A) (𝟙 A) (𝟙 A) (𝟙 A) rfl
      (fun _ _ h => h) (fun _ _ h => h)
    simp only [Category.id_comp, ModuleCat.hom_id, LinearMap.range_id, top_inf_eq]
  | succ n =>
    let S := (ShortComplex.mk (firstAugN R C) (smallSumAugN R C)
      (firstAugN_smallSumAugN R C)).map (eval _ _ (n+1))
    let T := (ShortComplex.mk (firstN R C) (smallSumN R C)
      (firstN_smallSumN R C)).map (eval _ _ n)
    let e : S ≅ T := ShortComplex.isoMk (Iso.refl _)
      ((biprodXIso (augmentedShifted R R C.leftPair.space)
          (augmentedShifted R R C.rightPair.space) (n+1)) ≪≫
        (biprodXIso (complex R R C.leftPair.space) (complex R R C.rightPair.space) n).symm) (Iso.refl _)
      (by
        change 𝟙 _ ≫ (firstN R C).f n = (firstAugN R C).f (n+1) ≫ _
        rw [Category.id_comp]
        apply (cancel_mono (biprodXIso (complex R R C.leftPair.space)
          (complex R R C.rightPair.space) n).hom).mp
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
        rw [firstN_degree, firstAugN_degree]
        rfl)
      (by
        change ((biprodXIso (augmentedShifted R R C.leftPair.space)
          (augmentedShifted R R C.rightPair.space) (n+1)).hom ≫
          (biprodXIso (complex R R C.leftPair.space) (complex R R C.rightPair.space) n).inv) ≫
          (smallSumN R C).f n = (smallSumAugN R C).f (n+1) ≫ 𝟙 _
        rw [Category.assoc, smallSumN_degree, Category.comp_id]
        change (biprodXIso (augmentedShifted R R C.leftPair.space)
          (augmentedShifted R R C.rightPair.space) (n+1)).hom ≫
          biprod.desc ((pieceToAugmentedSmall R C false).f (n+1))
            ((pieceToAugmentedSmall R C true).f (n+1)) = (smallSumAugN R C).f (n+1)
        erw [← smallSumAugN_degree R C (n+1), Iso.hom_inv_id_assoc])
    exact (ShortComplex.shortExact_iff_of_iso e).mpr
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
        (nonnegative_small_shortExact R C) n)

def reducedSmallComplex (C : CoverPair.{v,w}) :=
  (augmentedSmall R C.cover).extend (degreeEmbedding (-1))

def reducedSmallSum (C : CoverPair.{v,w}) :
    middle (theoryFunctor R .reduced) C ⟶ reducedSmallComplex R C :=
  extendBiprodDesc (degreeEmbedding (-1)) (smallSumAugN R C)

def reducedSmallInclusion (C : CoverPair.{v,w}) :
    reducedSmallComplex R C ⟶ (theoryFunctor R .reduced).obj C.pair :=
  HomologicalComplex.extendMap (augmentedSmallInclusion R C.cover) (degreeEmbedding (-1))

lemma reducedFirst_smallSum (C : CoverPair.{v,w}) :
    chainFirst (theoryFunctor R .reduced) C ≫ reducedSmallSum R C = 0 :=
  extend_signed_zero (degreeEmbedding (-1))
    (augmentedShiftedMap R R C.toLeft.map) (augmentedShiftedMap R R C.toRight.map)
    (smallSumAugN R C) (firstAugN_smallSumAugN R C)

lemma reducedSmall_shortExact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (chainFirst (theoryFunctor R .reduced) C)
      (reducedSmallSum R C) (reducedFirst_smallSum R C)).ShortExact :=
  extend_signed_shortExact (degreeEmbedding (-1))
    (augmentedShiftedMap R R C.toLeft.map) (augmentedShiftedMap R R C.toRight.map)
    (smallSumAugN R C) (firstAugN_smallSumAugN R C) (augmented_small_shortExact R C)

lemma reducedSmallSum_inclusion (C : CoverPair.{v,w}) :
    reducedSmallSum R C ≫ reducedSmallInclusion R C =
      chainSum (theoryFunctor R .reduced) C := by
  let E := (degreeEmbedding (-1)).extendFunctor (ModuleCat.{max u v} R)
  change (E.mapBiprod _ _).inv ≫ E.map (smallSumAugN R C) ≫
    E.map (augmentedSmallInclusion R C.cover) = _
  rw [← E.map_comp, smallSumAugN_inclusion]
  exact biprod.mapBiprod_inv_map_desc E _ _ _ _

lemma reducedSmallInclusion_mono (C : CoverPair.{v,w}) :
    Mono (reducedSmallInclusion R C) :=
  extendMap_mono (degreeEmbedding (-1)) (augmentedSmallInclusion R C.cover)

lemma reducedSmallInclusion_quasiIso (C : CoverPair.{v,w}) :
    QuasiIso (reducedSmallInclusion R C) :=
  (quasiIso_extendMap_iff (augmentedSmallInclusion R C.cover) (degreeEmbedding (-1))).mpr
    (augmentedSmallInclusion_quasiIso R C.cover)

lemma reduced_comparison_properties (C : CoverPair.{v,w}) :
    Mono (comparison (theoryFunctor R .reduced) C) ∧
      ∀ n, IsIso (homologyMap (comparison (theoryFunctor R .reduced) C) n) := by
  letI := (reducedSmall_shortExact R C).epi_g
  letI := reducedSmallInclusion_mono R C
  have hq := reducedSmallInclusion_quasiIso R C
  exact comparison_properties_of_shortExact (theoryFunctor R .reduced) C
    (reducedSmallSum R C) (reducedSmallInclusion R C) (reducedSmallSum_inclusion R C)
    (reducedFirst_smallSum R C) (reducedSmall_shortExact R C).exact
    (fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n))


end


section
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.SmallChainHomology P202Specs.SmallChainEquivalence

def subcover (C : CoverPair.{v,w}) : CoverPair.{v,w} where
  pair := ⟨C.pair.sub, Set.univ⟩
  cover := {
    sets i := Subtype.val ⁻¹' C.cover.sets i
    isOpen i := (C.cover.isOpen i).preimage continuous_subtype_val
    covers x := C.cover.covers x.val }

def subspacePieceHomeo (P : Pair.{v}) (B : Set P.space) :
    (piece P B).sub ≃ₜ {a : P.sub // a.val ∈ B} where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def subspacePieceIso (P : Pair.{v}) (B : Set P.space) :
    (piece P B).sub ≅ TopCat.of {a : P.sub // a.val ∈ B} :=
  TopCat.isoOfHomeo (subspacePieceHomeo P B)

variable (R : Type u) [CommRing R]

abbrev subspaceMiddleN (C : CoverPair.{v,w}) :=
  complex R R C.leftPair.sub ⊞ complex R R C.rightPair.sub

def subspaceFirstN (C : CoverPair.{v,w}) :
    complex R R C.intersectionPair.sub ⟶ subspaceMiddleN R C :=
  biprod.lift (chainMap R R C.toLeft.restrict) (-chainMap R R C.toRight.restrict)

def subspaceMiddleIso (C : CoverPair.{v,w}) :
    subspaceMiddleN R C ≅ middleN R (subcover C) :=
  biprod.mapIso ((chainFunctor R R).mapIso (subspacePieceIso C.pair C.left))
    ((chainFunctor R R).mapIso (subspacePieceIso C.pair C.right))

def subspaceSmallSumN (C : CoverPair.{v,w}) :
    subspaceMiddleN R C ⟶ smallComplex R (subcover C).cover :=
  (subspaceMiddleIso R C).hom ≫ smallSumN R (subcover C)

def smallSubspaceN (C : CoverPair.{v,w}) :
    smallComplex R (subcover C).cover ⟶ smallComplex R C.cover :=
  mapSmall R (subcover C).cover C.cover C.pair.inclusion
    (fun i => ⟨i, fun _ h => h⟩)

lemma smallSubspaceN_square (C : CoverPair.{v,w}) :
    smallSubspaceN R C ≫ smallInclusion R C.cover =
      smallInclusion R (subcover C).cover ≫ chainMap R R C.pair.inclusion :=
  mapSmall_square _ _ _ _ _

lemma subspaceFirstN_iso (C : CoverPair.{v,w}) :
    subspaceFirstN R C ≫ (subspaceMiddleIso R C).hom =
      (chainFunctor R R).map (subspacePieceIso C.pair (C.left ∩ C.right)).hom ≫
        firstN R (subcover C) := by
  apply biprod.hom_ext <;>
    simp only [subspaceFirstN, subspaceMiddleIso, biprod.mapIso_hom,
      Category.assoc, biprod.map_fst, biprod.map_snd, Functor.mapIso_hom, biprod.lift_fst_assoc,
      biprod.lift_snd_assoc, firstN, biprod.lift_fst, biprod.lift_snd,
      Preadditive.neg_comp, Preadditive.comp_neg, ← (chainFunctor R R).map_comp] <;> rfl

lemma subspaceFirstN_smallSumN (C : CoverPair.{v,w}) :
    subspaceFirstN R C ≫ subspaceSmallSumN R C = 0 := by
  rw [subspaceSmallSumN, ← Category.assoc, subspaceFirstN_iso,
    Category.assoc, firstN_smallSumN, comp_zero]

lemma subspace_small_shortExact (C : CoverPair.{v,w}) :
    (ShortComplex.mk (subspaceFirstN R C) (subspaceSmallSumN R C)
      (subspaceFirstN_smallSumN R C)).ShortExact := by
  let e : ShortComplex.mk (subspaceFirstN R C) (subspaceSmallSumN R C)
        (subspaceFirstN_smallSumN R C) ≅
      ShortComplex.mk (firstN R (subcover C)) (smallSumN R (subcover C))
        (firstN_smallSumN R (subcover C)) :=
    ShortComplex.isoMk ((chainFunctor R R).mapIso (subspacePieceIso C.pair (C.left ∩ C.right)))
      (subspaceMiddleIso R C) (Iso.refl _)
      (subspaceFirstN_iso R C).symm (by simp [subspaceSmallSumN])
  exact (ShortComplex.shortExact_iff_of_iso e).mpr (nonnegative_small_shortExact R (subcover C))

lemma smallSubspaceN_mono (C : CoverPair.{v,w}) : Mono (smallSubspaceN R C) := by
  haveI : Mono (smallInclusion R (subcover C).cover ≫ chainMap R R C.pair.inclusion) := by
    haveI : Mono (chainMap R R C.pair.inclusion) :=
      inferInstanceAs (Mono (inclusion (chainFunctor R R) C.pair))
    infer_instance
  exact mono_of_mono_fac (smallSubspaceN_square R C)

def subspaceMiddleInclusionN (C : CoverPair.{v,w}) :
    subspaceMiddleN R C ⟶ middleN R C :=
  biprod.map (chainMap R R C.leftPair.inclusion) (chainMap R R C.rightPair.inclusion)

lemma subspaceFirstN_inclusion (C : CoverPair.{v,w}) :
    subspaceFirstN R C ≫ subspaceMiddleInclusionN R C =
      chainMap R R C.intersectionPair.inclusion ≫ firstN R C := by
  apply biprod.hom_ext <;>
    simp only [subspaceFirstN, subspaceMiddleInclusionN, firstN,
      Category.assoc, biprod.map_fst, biprod.map_snd, Functor.mapIso_hom, biprod.lift_fst_assoc,
      biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
      Preadditive.neg_comp, Preadditive.comp_neg, ← (chainFunctor R R).map_comp] <;> rfl

lemma subspaceSmallSumN_inclusion (C : CoverPair.{v,w}) :
    subspaceSmallSumN R C ≫ smallSubspaceN R C =
      subspaceMiddleInclusionN R C ≫ smallSumN R C := by
  apply (cancel_mono (smallInclusion R C.cover)).mp
  simp only [Category.assoc, smallSubspaceN_square, smallSumN_inclusion]
  apply biprod.hom_ext' <;>
    simp only [subspaceSmallSumN, subspaceMiddleIso, subspaceMiddleInclusionN,
      biprod.mapIso_hom, Functor.mapIso_hom, ← Category.assoc, biprod.inl_map_assoc,
      biprod.inr_map_assoc, Category.assoc, smallSumN, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, sumN, biprod.inl_desc, biprod.inr_desc,
      pieceToSmall_inclusion_assoc, pieceToSmall_inclusion,
      ← (chainFunctor R R).map_comp] <;> rfl

def subspaceRowMapN (C : CoverPair.{v,w}) :
    ShortComplex.mk (subspaceFirstN R C) (subspaceSmallSumN R C)
      (subspaceFirstN_smallSumN R C) ⟶
    ShortComplex.mk (firstN R C) (smallSumN R C) (firstN_smallSumN R C) :=
  ShortComplex.Hom.mk (chainMap R R C.intersectionPair.inclusion)
    (subspaceMiddleInclusionN R C) (smallSubspaceN R C)
    (subspaceFirstN_inclusion R C).symm (subspaceSmallSumN_inclusion R C).symm


end


section
open P202Specs.MayerVietoris P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R]

lemma ordinaryDegreeIso_naturality {P Q : Pair.{v}} (f : P ⟶ Q) (n : ℕ) :
    (relativeMap (ordinaryFunctor R R) f).f (n : ℤ) ≫ (ordinaryDegreeIso R R Q n).hom =
      (ordinaryDegreeIso R R P n).hom ≫ (relativeMap (chainFunctor R R) f).f n := by
  apply (cancel_epi ((projection (ordinaryFunctor R R) P).f (n : ℤ))).mp
  have hnat : (projection (ordinaryFunctor R R) P).f (n : ℤ) ≫
      (relativeMap (ordinaryFunctor R R) f).f (n : ℤ) =
        ((ordinaryFunctor R R).map f.map).f (n : ℤ) ≫
          (projection (ordinaryFunctor R R) Q).f (n : ℤ) := by
    rw [← comp_f, projection_map, comp_f]
  have hnatN : (projection (chainFunctor R R) P).f n ≫
      (relativeMap (chainFunctor R R) f).f n =
        (chainMap R R f.map).f n ≫ (projection (chainFunctor R R) Q).f n := by
    rw [← comp_f, projection_map, comp_f]
  rw [← Category.assoc, hnat, Category.assoc,
    P202.RelativeSingularChains.ordinary_degree]
  conv_rhs =>
    rw [← Category.assoc, P202.RelativeSingularChains.ordinary_degree,
      Category.assoc, hnatN]
  simp only [← Category.assoc]
  congr 1
  change (HomologicalComplex.extendMap (chainMap R R f.map) (degreeEmbedding 0)).f _ ≫ _ = _
  rw [extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
  simp [ordinaryNonnegativeIso]

lemma reducedDegreeIso_naturality {P Q : Pair.{v}} (f : P ⟶ Q) (n : ℕ) :
    (relativeMap (reducedFunctor R R) f).f (n : ℤ) ≫ (reducedDegreeIso R R Q n).hom =
      (reducedDegreeIso R R P n).hom ≫ (relativeMap (chainFunctor R R) f).f n := by
  apply (cancel_epi ((projection (reducedFunctor R R) P).f (n : ℤ))).mp
  have hnat : (projection (reducedFunctor R R) P).f (n : ℤ) ≫
      (relativeMap (reducedFunctor R R) f).f (n : ℤ) =
        ((reducedFunctor R R).map f.map).f (n : ℤ) ≫
          (projection (reducedFunctor R R) Q).f (n : ℤ) := by
    rw [← comp_f, projection_map, comp_f]
  have hnatN : (projection (chainFunctor R R) P).f n ≫
      (relativeMap (chainFunctor R R) f).f n =
        (chainMap R R f.map).f n ≫ (projection (chainFunctor R R) Q).f n := by
    rw [← comp_f, projection_map, comp_f]
  rw [← Category.assoc, hnat, Category.assoc,
    P202.RelativeSingularChains.reduced_degree]
  conv_rhs =>
    rw [← Category.assoc, P202.RelativeSingularChains.reduced_degree,
      Category.assoc, hnatN]
  simp only [← Category.assoc]
  congr 1
  change (HomologicalComplex.extendMap (augmentedShiftedMap R R f.map) (degreeEmbedding (-1))).f _ ≫ _ = _
  rw [extendMap_f _ _ (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
  simp [reducedNonnegativeIso, augmentedShiftedMap]

def reducedOrdinaryRelativeIso (P : Pair.{v}) : reduced R R P ≅ ordinary R R P := by
  let e : ∀ i : ℤ, (reduced R R P).X i ≅ (ordinary R R P).X i := fun i =>
    match i with
    | .ofNat n => reducedDegreeIso R R P n ≪≫ (ordinaryDegreeIso R R P n).symm
    | .negSucc n => ((P202.RelativeSingularChains.reduced_negative R R P _ (by omega)).1).iso
        ((P202.RelativeSingularChains.ordinary_negative R R P _ (by omega)).1)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  cases j with
  | negSucc n => exact ((P202.RelativeSingularChains.ordinary_negative R R P _ (by omega)).1).eq_of_tgt _ _
  | ofNat n =>
    have hi : i = ((n+1 : ℕ) : ℤ) := by
      change (n : ℤ) + 1 = i at hij
      omega
    subst i
    change ((reducedDegreeIso R R P (n+1)).hom ≫ (ordinaryDegreeIso R R P (n+1)).inv) ≫
        (ordinary R R P).d ((n+1 : ℕ) : ℤ) (n : ℤ) =
      (reduced R R P).d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
        ((reducedDegreeIso R R P n).hom ≫ (ordinaryDegreeIso R R P n).inv)
    apply (cancel_epi (reducedDegreeIso R R P (n+1)).inv).mp
    apply (cancel_mono (ordinaryDegreeIso R R P n).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Category.comp_id] using
      (P202.RelativeSingularChains.ordinary_boundary R R P n).trans
        (P202.RelativeSingularChains.reduced_boundary R R P n).symm

def reducedOrdinaryRelativeNatIso :
    relativeFunctor (reducedFunctor R R : TopCat.{v} ⥤ _) ≅
      relativeFunctor (ordinaryFunctor R R) :=
  NatIso.ofComponents (reducedOrdinaryRelativeIso R) (by
    intro P Q f
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | negSucc n =>
      exact ((P202.RelativeSingularChains.ordinary_negative R R Q _ (by omega)).1).eq_of_tgt _ _
    | ofNat n =>
      change (relativeMap (reducedFunctor R R) f).f (n : ℤ) ≫
          ((reducedDegreeIso R R Q n).hom ≫ (ordinaryDegreeIso R R Q n).inv) =
        ((reducedDegreeIso R R P n).hom ≫ (ordinaryDegreeIso R R P n).inv) ≫
          (relativeMap (ordinaryFunctor R R) f).f (n : ℤ)
      apply (cancel_mono (ordinaryDegreeIso R R Q n).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [ordinaryDegreeIso_naturality, Iso.inv_hom_id_assoc]
      exact reducedDegreeIso_naturality R f n)

def relativeExtensionComparison (P : Pair.{v}) :
    ordinary R R P ⟶ (nonnegative R R P).extend (degreeEmbedding 0) :=
  cokernel.desc (inclusion (ordinaryFunctor R R) P)
    (HomologicalComplex.extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0)) (by
      change HomologicalComplex.extendMap (inclusion (chainFunctor R R) P) (degreeEmbedding 0) ≫
        HomologicalComplex.extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0) = 0
      rw [← extendMap_comp, cokernel.condition, extendMap_zero])

@[reassoc (attr := simp)] lemma relativeExtensionComparison_projection (P : Pair.{v}) :
    projection (ordinaryFunctor R R) P ≫ relativeExtensionComparison R P =
      HomologicalComplex.extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0) :=
  cokernel.π_desc _ _ _

instance relativeExtensionComparison_isIso (P : Pair.{v}) :
    IsIso (relativeExtensionComparison R P) := by
  have hSN : (sequence (chainFunctor R R) P).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R R) P)
  have hS := extend_shortExact (degreeEmbedding 0) _ hSN
  haveI : Mono (relativeExtensionComparison R P) := hS.exact.mono_cokernelDesc
  haveI : Epi (HomologicalComplex.extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0)) :=
    hS.epi_g
  haveI : Epi (relativeExtensionComparison R P) :=
    epi_of_epi_fac (relativeExtensionComparison_projection R P)
  exact isIso_of_mono_of_epi _

def ordinaryRelativeExtensionNatIso :
    relativeFunctor (ordinaryFunctor R R : TopCat.{v} ⥤ _) ≅
      relativeFunctor (chainFunctor R R) ⋙
        (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R) :=
  NatIso.ofComponents (fun P => asIso (relativeExtensionComparison R P)) (by
    intro P Q f
    change relativeMap (ordinaryFunctor R R) f ≫ relativeExtensionComparison R Q =
      relativeExtensionComparison R P ≫
        HomologicalComplex.extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0)
    apply (cancel_epi (projection (ordinaryFunctor R R) P)).mp
    rw [← Category.assoc, projection_map, Category.assoc,
      relativeExtensionComparison_projection]
    conv_rhs => rw [← Category.assoc, relativeExtensionComparison_projection]
    change HomologicalComplex.extendMap (chainMap R R f.map) (degreeEmbedding 0) ≫
        HomologicalComplex.extendMap (projection (chainFunctor R R) Q) (degreeEmbedding 0) =
      HomologicalComplex.extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0) ≫
        HomologicalComplex.extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0)
    rw [← extendMap_comp, ← extendMap_comp, projection_map])


end


section
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains

variable {R : Type u} [CommRing R]
  {F G : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ}

/-- A natural equivalence of chain theories identifies the actual two summands. -/
def theoryMiddleIso (e : F ≅ G) (C : CoverPair.{v,w}) : middle F C ≅ middle G C :=
  biprod.mapIso (e.app C.leftPair) (e.app C.rightPair)

lemma theoryMiddleIso_first (e : F ≅ G) (C : CoverPair.{v,w}) :
    chainFirst F C ≫ (theoryMiddleIso e C).hom =
      (e.app C.intersectionPair).hom ≫ chainFirst G C := by
  apply biprod.hom_ext <;>
    simp only [chainFirst, theoryMiddleIso, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.lift_fst, biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg]
  · exact e.hom.naturality C.toLeft
  · exact congrArg Neg.neg (e.hom.naturality C.toRight)

lemma theoryMiddleIso_sum (e : F ≅ G) (C : CoverPair.{v,w}) :
    chainSum F C ≫ (e.app C.pair).hom =
      (theoryMiddleIso e C).hom ≫ chainSum G C := by
  apply biprod.hom_ext' <;>
    simp only [chainSum, theoryMiddleIso, biprod.mapIso_hom, Category.assoc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc]
  · exact e.hom.naturality C.leftInclusion
  · exact e.hom.naturality C.rightInclusion

/-- Cokernel presentations respect natural equivalences of the underlying chain theory. -/
def theoryPresentationIso (e : F ≅ G) (C : CoverPair.{v,w}) :
    (presentation F C).X₃ ≅ (presentation G C).X₃ :=
  cokernel.mapIso (chainFirst F C) (chainFirst G C)
    (e.app C.intersectionPair) (theoryMiddleIso e C) (theoryMiddleIso_first e C)

lemma theoryPresentationIso_comparison (e : F ≅ G) (C : CoverPair.{v,w}) :
    comparison F C ≫ (e.app C.pair).hom =
      (theoryPresentationIso e C).hom ≫ comparison G C := by
  apply (cancel_epi (presentation F C).g).mp
  rw [← Category.assoc, presentation_comparison]
  change chainSum F C ≫ (e.app C.pair).hom =
    cokernel.π (chainFirst F C) ≫
      cokernel.map (chainFirst F C) (chainFirst G C) (e.app C.intersectionPair).hom
        (theoryMiddleIso e C).hom (theoryMiddleIso_first e C) ≫ comparison G C
  rw [cokernel.π_desc_assoc, Category.assoc]
  change chainSum F C ≫ (e.app C.pair).hom =
    (theoryMiddleIso e C).hom ≫ (presentation G C).g ≫ comparison G C
  rw [presentation_comparison]
  exact theoryMiddleIso_sum e C

lemma transfer_presentation_properties (e : F ≅ G) (C : CoverPair.{v,w})
    (hm : Mono (chainFirst G C)) (hi : Mono (comparison G C))
    (hq : ∀ n, IsIso (homologyMap (comparison G C) n)) :
    Mono (chainFirst F C) ∧ Mono (comparison F C) ∧
      ∀ n, IsIso (homologyMap (comparison F C) n) := by
  letI := hm
  letI := hi
  have hf : chainFirst F C = (e.app C.intersectionPair).hom ≫
      chainFirst G C ≫ (theoryMiddleIso e C).inv := by
    rw [← Category.assoc, ← theoryMiddleIso_first e C, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hc : comparison F C = (theoryPresentationIso e C).hom ≫
      comparison G C ≫ (e.app C.pair).inv := by
    rw [← Category.assoc, ← theoryPresentationIso_comparison e C, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [hf]
    infer_instance
  · rw [hc]
    infer_instance
  · intro n
    letI := hq n
    rw [hc, homologyMap_comp, homologyMap_comp]
    infer_instance


end


section
open P202Specs.MayerVietoris P202Specs.SingularChains P202Specs.RelativeSingularChains
variable {R : Type u} [CommRing R]

lemma extension_presentation_properties
    (FN : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ)
    (C : CoverPair.{v,w}) {Q : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (p : FN.obj C.leftPair ⊞ FN.obj C.rightPair ⟶ Q) (j : Q ⟶ FN.obj C.pair)
    (hpj : p ≫ j = biprod.desc (FN.map C.leftInclusion) (FN.map C.rightInclusion))
    (hfp : biprod.lift (FN.map C.toLeft) (-FN.map C.toRight) ≫ p = 0)
    (hS : (ShortComplex.mk (biprod.lift (FN.map C.toLeft) (-FN.map C.toRight)) p hfp).ShortExact)
    [Mono j] (hq : ∀ n, IsIso (homologyMap j n)) :
    let F := FN ⋙ (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R)
    Mono (chainFirst F C) ∧ Mono (comparison F C) ∧
      ∀ n, IsIso (homologyMap (comparison F C) n) := by
  let e := degreeEmbedding 0
  let E := e.extendFunctor (ModuleCat.{max u v} R)
  let F := FN ⋙ E
  let pZ := extendBiprodDesc e p
  let jZ := HomologicalComplex.extendMap j e
  have hfpZ : chainFirst F C ≫ pZ = 0 :=
    extend_signed_zero e (FN.map C.toLeft) (FN.map C.toRight) p hfp
  have hSZ : (ShortComplex.mk (chainFirst F C) pZ hfpZ).ShortExact :=
    extend_signed_shortExact e (FN.map C.toLeft) (FN.map C.toRight) p hfp hS
  have hpjZ : pZ ≫ jZ = chainSum F C := by
    change (E.mapBiprod _ _).inv ≫ E.map p ≫ E.map j = _
    rw [← E.map_comp, hpj]
    exact biprod.mapBiprod_inv_map_desc E _ _ _ _
  haveI : Epi pZ := hSZ.epi_g
  haveI : Mono jZ := extendMap_mono e j
  have hqN : QuasiIso j := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mpr (hq n)
  have hqZ : ∀ n, IsIso (homologyMap jZ n) := by
    have h : QuasiIso jZ := (quasiIso_extendMap_iff j e).mpr hqN
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp (h.quasiIsoAt n)
  exact ⟨hSZ.mono_f, comparison_properties_of_shortExact F C pZ jZ hpjZ hfpZ hSZ.exact hqZ⟩


end


namespace RelativeBridge
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Quotienting a map of short exact rows by its three vertical maps preserves
short exactness provided its right vertical map is monic. -/
lemma cokernel_shortExact {A B : ShortComplex C} (f : A ⟶ B)
    (hA : A.ShortExact) (hB : B.ShortExact) [Mono f.τ₃] :
    (cokernel f).ShortExact := by
  let S : ShortComplex.SnakeInput C := {
    L₀ := kernel f
    L₁ := A
    L₂ := B
    L₃ := cokernel f
    v₀₁ := kernel.ι f
    v₁₂ := f
    v₂₃ := cokernel.π f
    w₀₂ := kernel.condition f
    w₁₃ := cokernel.condition f
    h₀ := kernelIsKernel f
    h₃ := cokernelIsCokernel f
    L₁_exact := hA.exact
    epi_L₁_g := hA.epi_g
    L₂_exact := hB.exact
    mono_L₂_f := hB.mono_f }
  have hz : IsZero S.L₀.X₃ :=
    KernelFork.IsLimit.isZero_of_mono S.h₀τ₃
  have hδ : S.δ = 0 := hz.eq_of_src _ _
  refine { exact := S.L₃_exact, mono_f := ?_, epi_g := ?_ }
  · exact S.L₂'_exact.mono_g hδ
  · letI := hB.epi_g
    exact S.epi_L₃_g
end RelativeBridge

namespace RelativeBridge
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A quotient row is short exact when the two upper rows are short exact,
the columns are cokernel sequences, and the right vertical map is monic. -/
lemma quotient_row_shortExact {A B D : ShortComplex C} (f : A ⟶ B) (g : B ⟶ D)
    (w : f ≫ g = 0) (hA : A.ShortExact) (hB : B.ShortExact) [Mono f.τ₃]
    (h₁ : IsColimit (CokernelCofork.ofπ g.τ₁
      (show f.τ₁ ≫ g.τ₁ = 0 from congrArg ShortComplex.Hom.τ₁ w)))
    (h₂ : IsColimit (CokernelCofork.ofπ g.τ₂
      (show f.τ₂ ≫ g.τ₂ = 0 from congrArg ShortComplex.Hom.τ₂ w)))
    (h₃ : IsColimit (CokernelCofork.ofπ g.τ₃
      (show f.τ₃ ≫ g.τ₃ = 0 from congrArg ShortComplex.Hom.τ₃ w))) :
    D.ShortExact := by
  have hcol : IsColimit (CokernelCofork.ofπ g w) :=
    ShortComplex.isColimitOfIsColimitπ _
      ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ w).symm h₁)
      ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ w).symm h₂)
      ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ w).symm h₃)
  let e : cokernel f ≅ D := (cokernelIsCokernel f).coconePointUniqueUpToIso hcol
  exact ShortComplex.shortExact_of_iso e (cokernel_shortExact f hA hB)

/-- The direct sum of two cokernel projections is the cokernel of the direct sum
of the two original arrows. -/
def biprodCokernelIsColimit {A₁ A₂ B₁ B₂ : C} (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) :
    IsColimit (CokernelCofork.ofπ
      (biprod.map (cokernel.π f₁) (cokernel.π f₂))
      (show biprod.map f₁ f₂ ≫ biprod.map (cokernel.π f₁) (cokernel.π f₂) = 0 by
        apply biprod.hom_ext' <;> simp)) := by
  refine CokernelCofork.IsColimit.ofπ _ _ ?_ ?_ ?_
  · intro W k hk
    let k₁ := cokernel.desc f₁ ((biprod.inl : B₁ ⟶ B₁ ⊞ B₂) ≫ k) (by
      have h := congrArg (fun z => (biprod.inl : A₁ ⟶ A₁ ⊞ A₂) ≫ z) hk
      simpa using h)
    let k₂ := cokernel.desc f₂ ((biprod.inr : B₂ ⟶ B₁ ⊞ B₂) ≫ k) (by
      have h := congrArg (fun z => (biprod.inr : A₂ ⟶ A₁ ⊞ A₂) ≫ z) hk
      simpa using h)
    exact biprod.desc k₁ k₂
  · intro W k hk
    apply biprod.hom_ext' <;> simp
  · intro W k hk l hl
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π f₁)).mp
      have h := congrArg (fun z => (biprod.inl : B₁ ⟶ B₁ ⊞ B₂) ≫ z) hl
      simpa using h
    · apply (cancel_epi (cokernel.π f₂)).mp
      have h := congrArg (fun z => (biprod.inr : B₂ ⟶ B₁ ⊞ B₂) ≫ z) hl
      simpa using h
end RelativeBridge


section
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.SmallChainHomology
variable (R : Type u) [CommRing R]

abbrev relativeMiddleN (C : CoverPair.{v,w}) :=
  nonnegative R R C.leftPair ⊞ nonnegative R R C.rightPair

def relativeFirstN (C : CoverPair.{v,w}) :
    nonnegative R R C.intersectionPair ⟶ relativeMiddleN R C :=
  biprod.lift (relativeMap (chainFunctor R R) C.toLeft)
    (-relativeMap (chainFunctor R R) C.toRight)

def relativeMiddleProjectionN (C : CoverPair.{v,w}) :
    middleN R C ⟶ relativeMiddleN R C :=
  biprod.map (projection (chainFunctor R R) C.leftPair)
    (projection (chainFunctor R R) C.rightPair)

def relativeMiddleProjectionN_isCokernel (C : CoverPair.{v,w}) :
    IsColimit (CokernelCofork.ofπ (relativeMiddleProjectionN R C)
      (show subspaceMiddleInclusionN R C ≫ relativeMiddleProjectionN R C = 0 by
        apply biprod.hom_ext' <;> simp [subspaceMiddleInclusionN, relativeMiddleProjectionN,
          projection, inclusion])) :=
  RelativeBridge.biprodCokernelIsColimit _ _

lemma relativeFirstN_projection (C : CoverPair.{v,w}) :
    projection (chainFunctor R R) C.intersectionPair ≫ relativeFirstN R C =
      firstN R C ≫ relativeMiddleProjectionN R C := by
  apply biprod.hom_ext <;>
    simp [relativeFirstN, firstN, relativeMiddleProjectionN, projection_map]

def relativeSmallSumN (C : CoverPair.{v,w}) : relativeMiddleN R C ⟶ cokernel (smallSubspaceN R C) :=
  (relativeMiddleProjectionN_isCokernel R C).desc (CokernelCofork.ofπ
    (smallSumN R C ≫ cokernel.π (smallSubspaceN R C)) (by
      rw [← Category.assoc, ← subspaceSmallSumN_inclusion, Category.assoc, cokernel.condition,
        comp_zero]))

@[reassoc (attr := simp)]
lemma relativeSmallSumN_projection (C : CoverPair.{v,w}) :
    relativeMiddleProjectionN R C ≫ relativeSmallSumN R C =
      smallSumN R C ≫ cokernel.π (smallSubspaceN R C) :=
  Cofork.IsColimit.π_desc (relativeMiddleProjectionN_isCokernel R C)

lemma relativeFirstN_smallSumN (C : CoverPair.{v,w}) :
    relativeFirstN R C ≫ relativeSmallSumN R C = 0 := by
  apply (cancel_epi (projection (chainFunctor R R) C.intersectionPair)).mp
  rw [← Category.assoc, relativeFirstN_projection, Category.assoc,
    relativeSmallSumN_projection, ← Category.assoc, firstN_smallSumN, zero_comp, comp_zero]

def relativeRowProjectionN (C : CoverPair.{v,w}) :
    ShortComplex.mk (firstN R C) (smallSumN R C) (firstN_smallSumN R C) ⟶
      ShortComplex.mk (relativeFirstN R C) (relativeSmallSumN R C) (relativeFirstN_smallSumN R C) :=
  ShortComplex.Hom.mk (projection (chainFunctor R R) C.intersectionPair)
    (relativeMiddleProjectionN R C) (cokernel.π (smallSubspaceN R C))
    (relativeFirstN_projection R C) (relativeSmallSumN_projection R C)

lemma relative_small_shortExactN (C : CoverPair.{v,w}) :
    (ShortComplex.mk (relativeFirstN R C) (relativeSmallSumN R C)
      (relativeFirstN_smallSumN R C)).ShortExact := by
  haveI : Mono (subspaceRowMapN R C).τ₃ := smallSubspaceN_mono R C
  apply RelativeBridge.quotient_row_shortExact (subspaceRowMapN R C) (relativeRowProjectionN R C)
    (show subspaceRowMapN R C ≫ relativeRowProjectionN R C = 0 by
      apply ShortComplex.hom_ext
      · exact cokernel.condition _
      · change subspaceMiddleInclusionN R C ≫ relativeMiddleProjectionN R C = 0
        apply biprod.hom_ext' <;> simp [subspaceMiddleInclusionN, relativeMiddleProjectionN,
          projection, inclusion]
      · exact cokernel.condition _)
    (subspace_small_shortExact R C) (nonnegative_small_shortExact R C)
  · exact cokernelIsCokernel _
  · exact relativeMiddleProjectionN_isCokernel R C
  · exact cokernelIsCokernel _

open Opposite
open scoped Simplicial
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.SmallChainHomology
variable (R : Type u) [CommRing R]

lemma inclusion_small_iff_subcover (C : CoverPair.{v,w}) (n : ℕ) (c : Chains R C.pair.sub n) :
    (chainMap R R C.pair.inclusion).f n c ∈ smallModule R C.cover n ↔
      c ∈ smallModule R (subcover C).cover n := by
  classical
  constructor
  · intro hc s hs
    have hs' : ((TopCat.toSSet.map C.pair.inclusion).app (op ⦋n⦌)) s ∈
        (Finsupp.mapDomain ((TopCat.toSSet.map C.pair.inclusion).app (op ⦋n⦌)) c).support := by
      rw [Finsupp.mapDomain_support_of_injective
        (P202.RelativeSingularChains.simplex_injective C.pair n)]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    obtain ⟨i, hi⟩ := hc hs'
    exact ⟨i, fun _ ⟨p, hp⟩ => hp ▸ hi ⟨p, rfl⟩⟩
  · intro hc
    exact ((smallSubspaceN R C).f n ⟨c, hc⟩).property

lemma smallSubspaceN_isPullback (C : CoverPair.{v,w}) :
    IsPullback (smallSubspaceN R C) (smallInclusion R (subcover C).cover)
      (smallInclusion R C.cover) (chainMap R R C.pair.inclusion) := by
  apply IsPullback.mk' (smallSubspaceN_square R C)
  · intro T a b h₁ h₂
    ext n c
    apply Subtype.ext
    exact congrArg (fun z => z.f n c) h₂
  · intro T a b hab
    let lf (n : ℕ) : T.X n ⟶ (smallComplex R (subcover C).cover).X n :=
      ModuleCat.ofHom ((b.f n).hom.codRestrict
        (smallModule R (subcover C).cover n) (by
          intro c
          apply (inclusion_small_iff_subcover R C n _).mp
          have h := congrArg (fun z => z.f n c) hab
          change (a.f n c).val = (chainMap R R C.pair.inclusion).f n (b.f n c) at h
          change (chainMap R R C.pair.inclusion).f n (b.f n c) ∈ _
          exact h ▸ (a.f n c).property))
    have hf (n : ℕ) : lf n ≫ (smallInclusion R (subcover C).cover).f n = b.f n := rfl
    let l : T ⟶ smallComplex R (subcover C).cover := {
      f := lf
      comm' n m _ := by
        haveI : Mono ((smallInclusion R (subcover C).cover).f m) :=
          (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
        apply (cancel_mono ((smallInclusion R (subcover C).cover).f m)).mp
        rw [Category.assoc, ← (smallInclusion R (subcover C).cover).comm,
          ← Category.assoc, hf, Category.assoc, hf]
        exact b.comm n m }
    refine ⟨l, ?_, ?_⟩
    · ext n c
      apply Subtype.ext
      exact (congrArg (fun z => z.f n c) hab).symm
    · ext n c
      rfl

def relativeSmallComparisonN (C : CoverPair.{v,w}) :
    cokernel (smallSubspaceN R C) ⟶ nonnegative R R C.pair :=
  cokernel.map _ _ (smallInclusion R (subcover C).cover) (smallInclusion R C.cover)
    (smallSubspaceN_square R C)

lemma relativeSmallComparisonN_mono (C : CoverPair.{v,w}) :
    Mono (relativeSmallComparisonN R C) :=
  Abelian.mono_cokernel_map_of_isPullback (smallSubspaceN_isPullback R C)

lemma relativeSmallComparisonN_quasiIso (C : CoverPair.{v,w}) :
    QuasiIso (relativeSmallComparisonN R C) := by
  let φ : ShortComplex.cokernelSequence (smallSubspaceN R C) ⟶
      sequence (chainFunctor R R) C.pair :=
    ShortComplex.Hom.mk (smallInclusion R (subcover C).cover) (smallInclusion R C.cover)
      (relativeSmallComparisonN R C) (smallSubspaceN_square R C).symm
      (cokernel.π_desc _ _ _).symm
  have hsmall : (ShortComplex.cokernelSequence (smallSubspaceN R C)).ShortExact := by
    haveI := smallSubspaceN_mono R C
    exact { exact := ShortComplex.cokernelSequence_exact _, mono_f := smallSubspaceN_mono R C, epi_g := inferInstance }
  have hlarge : (sequence (chainFunctor R R) C.pair).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R R) C.pair)
  have ha : QuasiIso (smallInclusion R (subcover C).cover) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      (P202.SmallChainHomology.absoluteComparison R _ _ _ n)
  have hx : QuasiIso (smallInclusion R C.cover) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      (P202.SmallChainHomology.absoluteComparison R _ _ _ n)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hsmall hlarge ha hx

lemma relativeSmallSumN_comparison (C : CoverPair.{v,w}) :
    relativeSmallSumN R C ≫ relativeSmallComparisonN R C =
      biprod.desc (relativeMap (chainFunctor R R) C.leftInclusion)
        (relativeMap (chainFunctor R R) C.rightInclusion) := by
  haveI : Epi (relativeMiddleProjectionN R C) :=
    Cofork.IsColimit.epi (relativeMiddleProjectionN_isCokernel R C)
  apply (cancel_epi (relativeMiddleProjectionN R C)).mp
  rw [← Category.assoc, relativeSmallSumN_projection, Category.assoc]
  change smallSumN R C ≫ cokernel.π (smallSubspaceN R C) ≫
      cokernel.map _ _ _ _ (smallSubspaceN_square R C) = _
  rw [cokernel.π_desc, ← Category.assoc, smallSumN_inclusion]
  change sumN R C ≫ projection (chainFunctor R R) C.pair =
    relativeMiddleProjectionN R C ≫ biprod.desc
      (relativeMap (chainFunctor R R) C.leftInclusion)
      (relativeMap (chainFunctor R R) C.rightInclusion)
  apply biprod.hom_ext'
  · rw [sumN, biprod.inl_desc_assoc, relativeMiddleProjectionN,
      biprod.inl_map_assoc, biprod.inl_desc]
    exact (projection_map (chainFunctor R R) C.leftInclusion).symm
  · rw [sumN, biprod.inr_desc_assoc, relativeMiddleProjectionN,
      biprod.inr_map_assoc, biprod.inr_desc]
    exact (projection_map (chainFunctor R R) C.rightInclusion).symm

end


section
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202Specs.SingularChains
variable (R : Type u) [CommRing R]

lemma ordinary_comparison_properties (C : CoverPair.{v,w}) :
    Mono (comparison (theoryFunctor R .ordinary) C) ∧
      ∀ n, IsIso (homologyMap (comparison (theoryFunctor R .ordinary) C) n) := by
  letI := (ordinarySmall_shortExact R C).epi_g
  letI := ordinarySmallInclusion_mono R C
  have hq := ordinarySmallInclusion_quasiIso R C
  exact comparison_properties_of_shortExact (theoryFunctor R .ordinary) C
    (ordinarySmallSum R C) (ordinarySmallInclusion R C) (ordinarySmallSum_inclusion R C)
    (ordinaryFirst_smallSum R C) (ordinarySmall_shortExact R C).exact
    (fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n))

lemma relative_extension_presentation_properties (C : CoverPair.{v,w}) :
    let F := relativeFunctor (chainFunctor R R) ⋙
      (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R)
    Mono (chainFirst F C) ∧ Mono (comparison F C) ∧
      ∀ n, IsIso (homologyMap (comparison F C) n) := by
  letI := relativeSmallComparisonN_mono R C
  exact extension_presentation_properties (relativeFunctor (chainFunctor R R)) C
    (relativeSmallSumN R C) (relativeSmallComparisonN R C) (relativeSmallSumN_comparison R C)
    (relativeFirstN_smallSumN R C) (relative_small_shortExactN R C)
    (fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).mp
      ((relativeSmallComparisonN_quasiIso R C).quasiIsoAt n))

lemma relative_presentation_properties (C : CoverPair.{v,w}) :
    Mono (chainFirst (theoryFunctor R .relative) C) ∧
      Mono (comparison (theoryFunctor R .relative) C) ∧
      ∀ n, IsIso (homologyMap (comparison (theoryFunctor R .relative) C) n) := by
  have h := relative_extension_presentation_properties R C
  exact transfer_presentation_properties (ordinaryRelativeExtensionNatIso R) C h.1 h.2.1 h.2.2

lemma all_presentation_properties (t : Theory) (C : CoverPair.{v,w}) :
    Mono (chainFirst (theoryFunctor R t) C) ∧ Mono (comparison (theoryFunctor R t) C) ∧
      ∀ n, IsIso (homologyMap (comparison (theoryFunctor R t) C) n) := by
  cases t with
  | ordinary => exact ⟨absolute_chainFirst_mono R .ordinary (Or.inl rfl) C,
      ordinary_comparison_properties R C⟩
  | relative => exact relative_presentation_properties R C
  | reduced => exact ⟨absolute_chainFirst_mono R .reduced (Or.inr rfl) C,
      reduced_comparison_properties R C⟩
  | reducedRelative =>
    have h := relative_presentation_properties R C
    exact transfer_presentation_properties (reducedOrdinaryRelativeNatIso R) C h.1 h.2.1 h.2.2

/-- The natural ordinary and reduced Mayer–Vietoris sequences for open
covers, including arbitrary relative subspaces and empty intersections. -/
theorem mayerVietoris : mayerVietoris_type.{u,v,w} := by
  intro R _ t
  let F := theoryFunctor R t
  have hm : ∀ C : CoverPair.{v,w}, Mono (chainFirst F C) :=
    fun C => (all_presentation_properties R t C).1
  have hi : ∀ C : CoverPair.{v,w}, Mono (comparison F C) :=
    fun C => (all_presentation_properties R t C).2.1
  have hq : ∀ (C : CoverPair.{v,w}) n, IsIso (homologyMap (comparison F C) n) :=
    fun C => (all_presentation_properties R t C).2.2
  have h := assemble F hm hi hq
  exact ⟨h.1, h.2.1, h.2.2, fun ht C =>
    ordinary_endpoint_of_presentations R t ht hm hq C⟩


end

end P202.MayerVietoris
