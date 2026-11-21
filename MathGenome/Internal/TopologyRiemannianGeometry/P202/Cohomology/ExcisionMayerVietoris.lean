import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.ExcisionMayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.FreeChainDual
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
universe u v w t
namespace P202.CohomologyExcisionMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.ChainLES P202Specs.CohomologyExcisionMV

/-- Extending a complex by zero preserves colimits: evaluation is either
an evaluation of the original complex or the zero functor. -/
lemma extend_preserves_colimits {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] {ι κ : Type*} {c : ComplexShape ι} {d : ComplexShape κ}
    (e : c.Embedding d) (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro k
  by_cases hk : ∃ i, e.f i = k
  · obtain ⟨i, hi⟩ := hk
    exact preservesColimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hi).symm
  · apply Functor.preservesColimitsOfShape_of_isZero
    apply Functor.isZero
    intro K
    exact isZero_extend_X K e k (by simpa using hk)

/-- In particular extension commutes with the relative-chain quotient. -/
local instance extend_preserves_finite_colimits {C : Type*} [Category* C]
    [Preadditive C] [HasZeroObject C] [HasFiniteColimits C]
    {ι κ : Type*} {c : ComplexShape ι} {d : ComplexShape κ} (e : c.Embedding d) :
    PreservesFiniteColimits (e.extendFunctor C) :=
  ⟨fun _ _ _ => extend_preserves_colimits e _⟩

variable (R : Type u) [CommRing R]

/-- A natural isomorphism, not just an identification of degree modules. -/
def relativeExtensionIso (P : Pair.{v}) :
    (nonnegative R R P).extend (degreeEmbedding 0) ≅ ordinary R R P :=
  PreservesCokernel.iso ((degreeEmbedding 0).extendFunctor _) (inclusion (chainFunctor R R) P)

lemma relativeExtensionIso_natural {P Q : Pair.{v}} (f : P ⟶ Q) :
    (relativeExtensionIso R P).hom ≫ relativeMap (ordinaryFunctor R R) f =
      extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0) ≫
        (relativeExtensionIso R Q).hom := by
  exact preserves_cokernel_iso_comp_cokernel_map
    ((degreeEmbedding 0).extendFunctor _) (inclusion (chainFunctor R R) P)
    (inclusion (chainFunctor R R) Q) ((chainFunctor R R).map f.restrict)
    ((chainFunctor R R).map f.map) (inclusion_square (chainFunctor R R) f)

lemma relative_ordinary_free (P : Pair.{v}) (q : ℤ) :
    Module.Free R ((ordinary R R P).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P n
    exact Module.Free.of_basis (b.map (ordinaryDegreeIso R R P n).symm.toLinearEquiv)
  · have := ModuleCat.subsingleton_of_isZero
      (P202.RelativeSingularChains.ordinary_negative R R P q (by omega)).1
    infer_instance

/-- Excision is a quasi-isomorphism of the actual integer-graded free relative
complexes, including their zero terms in negative degrees. -/
lemma excision_chain_quasiIso (D : P202Specs.Excision.Data.{v}) :
    QuasiIso (relativeMap (ordinaryFunctor R R) D.inclusion) := by
  have hn : QuasiIso (relativeMap (chainFunctor R R) D.inclusion) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (P202.Excision.isomorphism R D n)
  have h := relativeExtensionIso_natural R D.inclusion
  have : QuasiIso ((relativeExtensionIso R D.excised).hom ≫
      relativeMap (ordinaryFunctor R R) D.inclusion) := by
    rw [h]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

/-- Homotopy equivalences remain homotopy equivalences under unrestricted Hom.
The coefficient module may lie in a different universe. -/
def dualHomotopyEquiv (A : Type w) [AddCommGroup A] [Module R A]
    {K L : ChainComplex (ModuleCat.{t} R) ℤ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((dualComplexFunctor R A (.down ℤ)).obj (op L))
      ((dualComplexFunctor R A (.down ℤ)).obj (op K)) :=
  (dualFunctor R A).mapHomotopyEquiv
    { hom := (opFunctor _ (.down ℤ)).map e.hom.op
      inv := (opFunctor _ (.down ℤ)).map e.inv.op
      homotopyHomInvId := by simpa using e.homotopyInvHomId.op
      homotopyInvHomId := by simpa using e.homotopyHomInvId.op }

/-- Excision follows by dualizing the homotopy equivalence of the free relative
chain complexes, for every coefficient module and every integer degree. -/
theorem excision :
    ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]
      (D : P202Specs.Excision.Data.{v}) (q : ℤ),
      IsIso ((relativeCohomologyFunctor R A q).map D.inclusion.op) := by
  intro R _ A _ _ D q
  haveI := excision_chain_quasiIso R D
  haveI : ∀ n, Module.Free R ((ordinary R R D.excised).X n) := relative_ordinary_free R D.excised
  haveI : ∀ n, Module.Free R ((ordinary R R D.pair).X n) := relative_ordinary_free R D.pair
  obtain ⟨e, he⟩ := P202.FreeChainDual.homotopy_equivalence
    (ordinary R R D.excised) (ordinary R R D.pair)
    ⟨0, fun n hn => (P202.RelativeSingularChains.ordinary_negative R R D.excised n hn).1⟩
    ⟨0, fun n hn => (P202.RelativeSingularChains.ordinary_negative R R D.pair n hn).1⟩
    (relativeMap (ordinaryFunctor R R) D.inclusion)
  have : QuasiIso ((relativeCochainFunctor R A).map D.inclusion.op) := by
    have h := (dualHomotopyEquiv R A e).quasiIso_hom
    change QuasiIso ((dualComplexFunctor R A (.down ℤ)).map e.hom.op) at h
    rw [he] at h
    exact h
  change IsIso (homologyMap ((relativeCochainFunctor R A).map D.inclusion.op) q)
  infer_instance

theorem excision_naturality :
    ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]
      (D E : P202Specs.Excision.Data.{v}) (f : P202Specs.Excision.Map D E) (q : ℤ),
      (relativeCohomologyFunctor R A q).map f.pairMap.op ≫
          (relativeCohomologyFunctor R A q).map D.inclusion.op =
        (relativeCohomologyFunctor R A q).map E.inclusion.op ≫
          (relativeCohomologyFunctor R A q).map f.excised.op := by
  intro R _ A _ _ D E f q
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, f.square]

open P202Specs.MayerVietoris

/-- An injective map of spaces gives a degreewise retraction on ordinary free
chains. It only selects simplex coordinates and need not commute with d. -/
lemma ordinary_map_split {X Y : TopCat.{v}} (f : X ⟶ Y) (hf : Function.Injective f) (q : ℤ) :
    ∃ r : (ordinaryComplex R R Y).X q ⟶ (ordinaryComplex R R X).X q,
      ((ordinaryFunctor R R).map f).f q ≫ r = 𝟙 _ := by
  have hs (n : ℕ) : Function.Injective ((TopCat.toSSet.map f).app (op ⦋n⦌)) := by
    intro s t h
    apply (simplexEquiv X n).injective
    ext x
    apply hf
    exact congrArg (fun z => simplexEquiv Y n z x) h
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let r : (complex R R Y).X n ⟶ (complex R R X).X n :=
      ModuleCat.ofHom (Finsupp.lcomapDomain ((TopCat.toSSet.map f).app (op ⦋n⦌)) (hs n))
    have hr : (chainMap R R f).f n ≫ r = 𝟙 _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := R) _ (hs n) c
    refine ⟨(ordinaryNonnegativeIso R R Y n).hom ≫ r ≫
      (ordinaryNonnegativeIso R R X n).inv, ?_⟩
    change (extendMap (chainMap R R f) (degreeEmbedding 0)).f _ ≫ _ = _
    rw [extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by
      change (0 : ℤ) + n = n; omega)]
    simp only [ordinaryNonnegativeIso, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc ((chainMap R R f).f n), hr, Category.id_comp, Iso.hom_inv_id]
    rfl
  · exact ⟨0, (P202.SingularChains.ordinary_negative_chains R R X q (by omega)).eq_of_src _ _⟩

lemma cover_first_split (C : CoverPair.{v,w}) (q : ℤ) :
    ∃ r : (middle (coverChains R) C).X q ⟶
        ((coverChains R).obj C.intersectionPair).X q,
      (chainFirst (coverChains R) C).f q ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := ordinary_map_split R C.toLeft.map (by
    intro a b h
    exact Subtype.ext (congrArg (fun x : C.leftPair.space => x.val) h)) q
  refine ⟨(biprod.fst : middle (coverChains R) C ⟶
    (coverChains R).obj C.leftPair).f q ≫ r, ?_⟩
  rw [← Category.assoc, ← comp_f]
  simp only [chainFirst, biprod.lift_fst]
  change ((ordinaryFunctor R R).map C.toLeft.map).f q ≫ r = 𝟙 _
  exact hr

lemma cover_chain_shortExact (C : CoverPair.{v,w}) :
    DegreewiseShortExact (ShortComplex.cokernelSequence (chainFirst (coverChains R) C)) := by
  have : Mono (chainFirst (coverChains R) C) := mono_of_mono_f _ (fun q => by
    obtain ⟨r, hr⟩ := cover_first_split R C q
    exact SplitMono.mono ⟨r, hr⟩)
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
  exact { exact := ShortComplex.cokernelSequence_exact _,
          mono_f := by change Mono (chainFirst (coverChains R) C); infer_instance
          epi_g := inferInstance }

/-- The dual sequence is short exact because the first chain arrow splits
in each degree, not because Hom is assumed exact on all modules. -/
lemma cover_cochain_shortExact (A : Type w) [AddCommGroup A] [Module R A]
    (C : CoverPair.{v,w}) : DegreewiseShortExact (coverCochainSequence R A C) := by
  intro q
  exact P202.CohomologyPairs.dual_shortExact R A
    ((ShortComplex.cokernelSequence (chainFirst (coverChains R) C)).map (eval _ _ q))
    (cover_chain_shortExact R C q) (cover_first_split R C q)

/-- Every homology class has a cycle representative in the actual complex. -/
lemma classOf_surjective (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.homology n) : ∃ x, ∃ hx : K.d n (n-1) x = 0, classOf K n x hx = z := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  let x := K.iCycles n a
  have hx : K.d n (n-1) x = 0 :=
    congrArg (fun f : K.cycles n ⟶ K.X (n-1) => f a) (K.iCycles_d n (n-1))
  refine ⟨x, hx, ?_⟩
  change K.homologyπ n (K.cyclesMk x (n-1) _ hx) = K.homologyπ n a
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk x (n-1) _ hx

lemma classOf_map {K L : ChainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ L)
    (n : ℤ) (x : K.X n) (hx : K.d n (n-1) x = 0)
    (hy : L.d n (n-1) (f.f n x) = 0) :
    homologyMap f n (classOf K n x hx) = classOf L n (f.f n x) hy := by
  change homologyMap f n (K.homologyπ n (K.cyclesMk x (n-1) _ hx)) =
    L.homologyπ n (L.cyclesMk (f.f n x) (n-1) _ hy)
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]
  have hK := K.i_cyclesMk x (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hx
  have hL := L.i_cyclesMk (f.f n x) (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hy
  change K.iCycles n (K.cyclesMk x (n-1) _ hx) = x at hK
  change L.iCycles n (L.cyclesMk (f.f n x) (n-1) _ hy) = f.f n x at hL
  rw [hK, hL]

abbrev chainHomologyMiddleIso (C : CoverPair.{v,w}) (n : ℤ) :
    (middle (coverChains R) C).homology n ≅ homologyMiddle (coverChains R) C n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapBiprod _ _

lemma chainHomologyMiddle_first (C : CoverPair.{v,w}) (n : ℤ) :
    homologyMap (chainFirst (coverChains R) C) n ≫ (chainHomologyMiddleIso R C n).hom =
      first (coverChains R) C n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map (biprod.lift _ _) ≫
    ((HomologicalComplex.homologyFunctor _ _ n).mapBiprod _ _).hom = _
  rw [biprod.map_lift_mapBiprod]
  simp only [Functor.map_neg, first]
  rfl

lemma chainHomologyMiddle_sum (C : CoverPair.{v,w}) (n : ℤ) :
    (chainHomologyMiddleIso R C n).hom ≫ sum (coverChains R) C n =
      homologyMap (chainSum (coverChains R) C) n := by
  exact biprod.mapBiprod_hom_desc (HomologicalComplex.homologyFunctor _ _ n)
    _ _ ((coverChains R).map C.leftInclusion) ((coverChains R).map C.rightInclusion)

/-- The boundary formula in the homological theorem identifies its
connecting arrow with that of the cokernel presentation. -/
lemma cover_connecting_comparison
    (δ : Connecting.{u,v,w} (coverChains R))
    (hδ : BoundaryFormula (coverChains R) δ) (C : CoverPair.{v,w}) (n : ℤ) :
    connecting (cover_chain_shortExact R C) (n+1) n (by simp) =
      homologyMap (coverComparison R C) (n+1) ≫ δ C n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, hx, rfl⟩ := classOf_surjective R (coverQuotient R C) (n+1) z
  have hx' : (coverQuotient R C).d (n+1) n x = 0 := by
    exact (congrArg (fun j : ℤ => (coverQuotient R C).d (n+1) j x = 0)
      (Int.add_sub_cancel n 1)).mp hx
  obtain ⟨c, hc, a, ⟨ha, hacycle⟩, _⟩ := P202.ChainLES.lifts_exist
    (ShortComplex.cokernelSequence (chainFirst (coverChains R) C))
    (cover_chain_shortExact R C) (n+1) n (by simp) x hx'
  have ha' : ((coverChains R).obj C.intersectionPair).d n (n-1) a = 0 := hacycle _
  have heq : (coverComparison R C).f (n+1) x =
      (chainSum (coverChains R) C).f (n+1) c := by
    rw [← hc]
    exact congrArg (fun f : middle (coverChains R) C ⟶ (coverChains R).obj C.pair =>
      f.f (n+1) c) (cokernel.π_desc _ _ _)
  have hy : ((coverChains R).obj C.pair).d (n+1) n
      ((chainSum (coverChains R) C).f (n+1) c) = 0 := by
    rw [← heq]
    have h := congrArg (fun f : (coverQuotient R C).X (n+1) ⟶ ((coverChains R).obj C.pair).X n => f x)
      ((coverComparison R C).comm (n+1) n)
    simpa only [ModuleCat.comp_apply, hx', map_zero] using h
  have hySum : ((coverChains R).obj C.pair).d (n+1) ((n+1)-1)
      ((chainSum (coverChains R) C).f (n+1) c) = 0 :=
    (congrArg (fun j : ℤ => ((coverChains R).obj C.pair).d (n+1) j
      ((chainSum (coverChains R) C).f (n+1) c) = 0) (Int.add_sub_cancel n 1)).mpr hy
  have hy' : ((coverChains R).obj C.pair).d (n+1) ((n+1)-1)
      ((coverComparison R C).f (n+1) x) = 0 := by
    have h := (congrArg (fun j : ℤ => ((coverChains R).obj C.pair).d (n+1) j
      ((chainSum (coverChains R) C).f (n+1) c) = 0) (Int.add_sub_cancel n 1)).mpr hy
    exact (congrArg (fun z => ((coverChains R).obj C.pair).d (n+1) ((n+1)-1) z = 0) heq).mpr h
  have hm := classOf_map R (coverComparison R C) (n+1) x hx hy'
  change (connecting (cover_chain_shortExact R C) (n+1) n (by simp))
    (classOf (coverQuotient R C) (n+1) x hx) =
    δ C n (homologyMap (coverComparison R C) (n+1) (classOf _ _ x hx))
  rw [hm]
  have hleft := P202.ChainLES.lift_formula
    (ShortComplex.cokernelSequence (chainFirst (coverChains R) C))
    (cover_chain_shortExact R C) (n+1) n (by simp) x hx' c hc a ha (hacycle _)
  have hright := hδ C n c hy a ha ha'
  have heleft : classOf (coverQuotient R C) (n+1) x hx =
      cycleClass (coverQuotient R C) n ((ComplexShape.down ℤ).next_eq' (by simp)) x hx' := by
    change (coverQuotient R C).homologyπ (n+1) _ = (coverQuotient R C).homologyπ (n+1) _
    congr 1
  rw [heleft]
  change (connecting (cover_chain_shortExact R C) (n+1) n (by simp))
    (cycleClass (coverQuotient R C) n _ x hx') =
      classOf ((coverChains R).obj C.intersectionPair) n a ha' at hleft
  change δ C n (classOf ((coverChains R).obj C.pair) (n+1)
    ((chainSum (coverChains R) C).f (n+1) c) hySum) =
      classOf ((coverChains R).obj C.intersectionPair) n a ha' at hright
  have hcclass : classOf ((coverChains R).obj C.pair) (n+1)
      ((coverComparison R C).f (n+1) x) hy' =
    classOf ((coverChains R).obj C.pair) (n+1)
      ((chainSum (coverChains R) C).f (n+1) c) hySum := by
    congr 1
  rw [hcclass]
  exact hleft.trans hright.symm

/-- Compare the two homology long exact sequences by the five lemma. No
exactness assertion about the algebraic dual of homology is used. -/
lemma cover_comparison_quasiIso
    (mv : P202Specs.MayerVietoris.mayerVietoris_type.{u,v,w}) (C : CoverPair.{v,w}) :
    QuasiIso (coverComparison R C) := by
  obtain ⟨⟨δ, hδ, _, hf⟩, _, _, _⟩ := mv R .ordinary
  rw [quasiIso_iff]
  intro k
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, k = n+1 := ⟨k-1, by omega⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let S := ShortComplex.cokernelSequence (chainFirst (coverChains R) C)
  let hS := cover_chain_shortExact R C
  let T := ComposableArrows.mk₅ (first (coverChains R) C (n+1))
    (sum (coverChains R) C (n+1)) (δ C n) (first (coverChains R) C n)
    (sum (coverChains R) C n)
  let B := P202Specs.ChainLES.segment hS (n+1) n (by simp)
  let φ : B ⟶ T := ComposableArrows.homMk₅ (𝟙 _)
    (chainHomologyMiddleIso R C (n+1)).hom (homologyMap (coverComparison R C) (n+1))
    (𝟙 _) (chainHomologyMiddleIso R C n).hom (homologyMap (coverComparison R C) n)
    (by simpa [B, T, S, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using
      chainHomologyMiddle_first R C (n+1))
    (by
      change homologyMap (cokernel.π _) (n+1) ≫ homologyMap (coverComparison R C) (n+1) = _
      rw [← homologyMap_comp]
      simp only [coverComparison, cokernel.π_desc]
      simpa [T, -Fin.reduceFinMk] using (chainHomologyMiddle_sum R C (n+1)).symm)
    (by simpa [B, T, S, hS, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using
      cover_connecting_comparison R δ hf C n)
    (by simpa [B, T, S, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using
      chainHomologyMiddle_first R C n)
    (by
      change homologyMap (cokernel.π _) n ≫ homologyMap (coverComparison R C) n = _
      rw [← homologyMap_comp]
      simp only [coverComparison, cokernel.π_desc]
      simpa [T, -Fin.reduceFinMk] using (chainHomologyMiddle_sum R C n).symm)
  have hB : B.Exact := (P202.ChainLES.exactness S hS).2 (n+1) n (by simp)
  have hT : T.Exact := hδ.1 C n
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (by decide : 0 + 4 ≤ 5)
    hB hT φ 0 1 2 3 4 rfl rfl rfl rfl rfl
    (by change Epi (𝟙 _); infer_instance)
    (by change IsIso (chainHomologyMiddleIso R C (n+1)).hom; infer_instance)
    (by change IsIso (𝟙 _); infer_instance)
    (by change Mono (chainHomologyMiddleIso R C n).hom; infer_instance)

/-- The small-chain presentation is degreewise projective: its quotient is
a retract of the direct sum of two free singular chain modules. -/
lemma cover_quotient_projective (C : CoverPair.{v,w}) (q : ℤ) :
    Projective ((coverQuotient R C).X q) := by
  have hf (X : TopCat.{v}) : Module.Free R ((ordinaryComplex R R X).X q) := by
    by_cases hq : 0 ≤ q
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact Module.Free.of_basis
        (Finsupp.basisSingleOne.map (ordinaryNonnegativeIso R R X n).symm.toLinearEquiv)
    · have := ModuleCat.subsingleton_of_isZero
        (P202.SingularChains.ordinary_negative_chains R R X q (by omega))
      infer_instance
  have : Projective (((coverChains R).obj C.leftPair).X q) := by
    have : Module.Free R (((coverChains R).obj C.leftPair).X q) := hf C.leftPair.space
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  have : Projective (((coverChains R).obj C.rightPair).X q) := by
    have : Module.Free R (((coverChains R).obj C.rightPair).X q) := hf C.rightPair.space
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  have : Projective ((middle (coverChains R) C).X q) :=
    Projective.of_iso (biprodXIso _ _ q).symm inferInstance
  obtain ⟨r, hr⟩ := cover_first_split R C q
  let S := (ShortComplex.cokernelSequence (chainFirst (coverChains R) C)).map (eval _ _ q)
  let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S
    (cover_chain_shortExact R C q).exact r hr (cover_chain_shortExact R C q).epi_g
  exact @Retract.projective _ _ S.X₃ S.X₂ ⟨σ.s, S.g, σ.s_g⟩
    (by change Projective ((middle (coverChains R) C).X q); infer_instance)

lemma cover_quotient_negative (C : CoverPair.{v,w}) (q : ℤ) (hq : q < 0) :
    IsZero ((coverQuotient R C).X q) := by
  have h : IsZero ((middle (coverChains R) C).X q) := by
    apply IsZero.of_iso _ (biprodXIso _ _ q)
    exact (biprod_isZero_iff _ _).mpr
      ⟨P202.SingularChains.ordinary_negative_chains R R _ q hq,
        P202.SingularChains.ordinary_negative_chains R R _ q hq⟩
  exact IsZero.of_epi ((cokernel.π (chainFirst (coverChains R) C)).f q) h

/-- The projective version of the free-comparison argument, allowing a
projective cokernel presentation over any commutative ring. -/
lemma projective_comparison_homotopy
    {K L : ChainComplex (ModuleCat.{t} R) ℤ}
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K)
    (hL : P202Specs.FreeChainDual.BoundedBelow L) (f : K ⟶ L) [QuasiIso f] :
    ∃ e : HomotopyEquiv K L, e.hom = f := by
  have hi (C : ChainComplex (ModuleCat.{t} R) ℤ) [∀ n, Projective (C.X n)]
      (hC : P202Specs.FreeChainDual.BoundedBelow C) : CochainComplex.IsKInjective C.op := by
    obtain ⟨b, hb⟩ := hC
    have : CochainComplex.IsStrictlyGE C.op b := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact (hb n hn).op
    have (n : ℤ) : Injective (C.op.X n) := by
      change Injective (op (C.X n))
      infer_instance
    exact CochainComplex.isKInjective_of_injective C.op b
  have := hi K hK
  have := hi L hL
  let fo : L.op ⟶ K.op := (opFunctor _ (.down ℤ)).map f.op
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff fo).mp inferInstance
  let g : L ⟶ K := (unopFunctor _ (.up ℤ)).map e.inv.op
  refine ⟨⟨f, g, ?_, ?_⟩, rfl⟩
  · convert e.homotopyInvHomId.unop using 1 <;>
      (try simp [fo, g, he, opFunctor, unopFunctor]) <;> rfl
  · convert e.homotopyHomInvId.unop using 1 <;>
      (try simp [fo, g, he, opFunctor, unopFunctor]) <;> rfl

lemma cover_comparison_homotopy
    (mv : P202Specs.MayerVietoris.mayerVietoris_type.{u,v,w}) (C : CoverPair.{v,w}) :
    ∃ e : HomotopyEquiv (coverQuotient R C) ((coverChains R).obj C.pair),
      e.hom = coverComparison R C := by
  have : ∀ q, Projective ((coverQuotient R C).X q) := cover_quotient_projective R C
  have : ∀ q, Projective (((coverChains R).obj C.pair).X q) := by
    intro q
    by_cases hq : 0 ≤ q
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact ModuleCat.projective_of_free
        (Finsupp.basisSingleOne.map (ordinaryNonnegativeIso R R C.pair.space n).symm.toLinearEquiv)
    · exact (P202.SingularChains.ordinary_negative_chains R R C.pair.space q (by omega)).projective
  have := cover_comparison_quasiIso R mv C
  exact projective_comparison_homotopy R (K := coverQuotient R C)
    (L := (coverChains R).obj C.pair)
    ⟨0, cover_quotient_negative R C⟩
    ⟨0, P202.SingularChains.ordinary_negative_chains R R C.pair.space⟩ (coverComparison R C)

lemma cover_dual_comparison_quasiIso
    (mv : P202Specs.MayerVietoris.mayerVietoris_type.{u,v,w})
    (A : Type w) [AddCommGroup A] [Module R A] (C : CoverPair.{v,w}) :
    QuasiIso (coverDualComparison R A C) := by
  obtain ⟨e, he⟩ := cover_comparison_homotopy R mv C
  have h := (dualHomotopyEquiv R A e).quasiIso_hom
  change QuasiIso ((dualComplexFunctor R A (.down ℤ)).map e.hom.op) at h
  rw [he] at h
  exact h

section ContravariantBiproduct
variable {B D : Type*} [Category* B] [Category* D] [Preadditive B] [Preadditive D]
  (F : Bᵒᵖ ⥤ D) [F.Additive] (X Y : B) [HasBinaryBiproduct X Y]
  [HasBinaryBiproduct (op X) (op Y)] [HasBinaryBiproduct (F.obj (op X)) (F.obj (op Y))]

/-- Hom sends a binary direct sum to the binary direct sum, by restriction
to its two inclusions. This remains valid for infinite-rank summands. -/
def contravariantBiprodIso : F.obj (op (X ⊞ Y)) ≅ F.obj (op X) ⊞ F.obj (op Y) :=
  F.mapIso (biprod.opIso X Y) ≪≫ F.mapBiprod _ _

lemma contravariantBiprodIso_fst :
    (contravariantBiprodIso F X Y).hom ≫ biprod.fst = F.map biprod.inl.op := by
  simp [contravariantBiprodIso, ← F.map_comp]

lemma contravariantBiprodIso_snd :
    (contravariantBiprodIso F X Y).hom ≫ biprod.snd = F.map biprod.inr.op := by
  simp [contravariantBiprodIso, ← F.map_comp]

lemma contravariantBiprodIso_desc {Z : B} (f : X ⟶ Z) (g : Y ⟶ Z) :
    F.map (biprod.desc f g).op ≫ (contravariantBiprodIso F X Y).hom =
      biprod.lift (F.map f.op) (F.map g.op) := by
  apply biprod.hom_ext
  · rw [Category.assoc, contravariantBiprodIso_fst, ← F.map_comp, ← op_comp]
    simp
  · rw [Category.assoc, contravariantBiprodIso_snd, ← F.map_comp, ← op_comp]
    simp

lemma contravariantBiprodIso_lift {Z : B} (f : Z ⟶ X) (g : Z ⟶ Y) :
    (contravariantBiprodIso F X Y).hom ≫ biprod.desc (F.map f.op) (F.map g.op) =
      F.map (biprod.lift f g).op := by
  apply (cancel_epi (contravariantBiprodIso F X Y).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  · have h : biprod.inl ≫ (contravariantBiprodIso F X Y).inv = F.map biprod.fst.op := by
      simp [contravariantBiprodIso, ← F.map_comp]
    rw [biprod.inl_desc, ← Category.assoc, h, ← F.map_comp, ← op_comp]
    simp
  · have h : biprod.inr ≫ (contravariantBiprodIso F X Y).inv = F.map biprod.snd.op := by
      simp [contravariantBiprodIso, ← F.map_comp]
    rw [biprod.inr_desc, ← Category.assoc, h, ← F.map_comp, ← op_comp]
    simp
end ContravariantBiproduct

variable (A : Type w) [AddCommGroup A] [Module R A]

abbrev dualHomologyFunctor (q : ℤ) :=
  dualComplexFunctor R A (.down ℤ) ⋙ HomologicalComplex.homologyFunctor _ _ q

abbrev cohomologyMiddleIso (C : CoverPair.{v,w}) (q : ℤ) :
    ((coverCochainSequence R A C).X₂).homology q ≅ cohomologyMiddle R A C q :=
  contravariantBiprodIso (dualHomologyFunctor R A q)
    ((coverChains R).obj C.leftPair) ((coverChains R).obj C.rightPair)

lemma cohomologyMiddle_restrictions (C : CoverPair.{v,w}) (q : ℤ) :
    homologyMap (coverDualComparison R A C) q ≫
        homologyMap (coverCochainSequence R A C).f q ≫ (cohomologyMiddleIso R A C q).hom =
      restrictions R A C q := by
  change (dualHomologyFunctor R A q).map (coverComparison R C).op ≫
    (dualHomologyFunctor R A q).map (cokernel.π _).op ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  simp only [coverComparison, cokernel.π_desc]
  exact contravariantBiprodIso_desc _ _ _
    ((coverChains R).map C.leftInclusion) ((coverChains R).map C.rightInclusion)

lemma cohomologyMiddle_difference (C : CoverPair.{v,w}) (q : ℤ) :
    (cohomologyMiddleIso R A C q).hom ≫ difference R A C q =
      homologyMap (coverCochainSequence R A C).g q := by
  have h := contravariantBiprodIso_lift (dualHomologyFunctor R A q)
    ((coverChains R).obj C.leftPair) ((coverChains R).obj C.rightPair)
    ((coverChains R).map C.toLeft) (- (coverChains R).map C.toRight)
  simp only [op_neg, Functor.map_neg] at h
  exact h

lemma cover_first_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    chainFirst (coverChains R) C ≫ middleMap (coverChains R) f =
      (coverChains R).map f.onIntersection ≫ chainFirst (coverChains R) D := by
  have hl : C.toLeft ≫ f.onLeft = f.onIntersection ≫ D.toLeft := by
    apply PairMap.ext
    rfl
  have hr : C.toRight ≫ f.onRight = f.onIntersection ≫ D.toRight := by
    apply PairMap.ext
    rfl
  apply biprod.hom_ext <;>
    simp [chainFirst, middleMap, Category.assoc, ← Functor.map_comp, hl, hr]

lemma cover_sum_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    middleMap (coverChains R) f ≫ chainSum (coverChains R) D =
      chainSum (coverChains R) C ≫ (coverChains R).map f.map := by
  have hl : f.onLeft ≫ D.leftInclusion = C.leftInclusion ≫ f.map := by
    apply PairMap.ext
    rfl
  have hr : f.onRight ≫ D.rightInclusion = C.rightInclusion ≫ f.map := by
    apply PairMap.ext
    rfl
  apply biprod.hom_ext' <;>
    simp [chainSum, middleMap, Category.assoc, ← Functor.map_comp, hl, hr]

def coverQuotientMap {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    coverQuotient R C ⟶ coverQuotient R D :=
  cokernel.map _ _ ((coverChains R).map f.onIntersection) (middleMap (coverChains R) f)
    (cover_first_natural R f)

lemma cover_quotient_projection_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    cokernel.π (chainFirst (coverChains R) C) ≫ coverQuotientMap R f =
      middleMap (coverChains R) f ≫ cokernel.π (chainFirst (coverChains R) D) :=
  cokernel.π_desc _ _ _

lemma cover_comparison_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    coverQuotientMap R f ≫ coverComparison R D =
      coverComparison R C ≫ (coverChains R).map f.map := by
  apply (cancel_epi (cokernel.π (chainFirst (coverChains R) C))).mp
  rw [← Category.assoc, cover_quotient_projection_natural]
  simp only [Category.assoc, coverComparison, cokernel.π_desc, cokernel.π_desc_assoc]
  exact cover_sum_natural R f

/-- Pullback gives a morphism of the canonical three-term cochain sequences. -/
def coverCochainSequenceMap {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    coverCochainSequence R A D ⟶ coverCochainSequence R A C :=
  ShortComplex.Hom.mk
    ((dualComplexFunctor R A (.down ℤ)).map (coverQuotientMap R f).op)
    ((dualComplexFunctor R A (.down ℤ)).map (middleMap (coverChains R) f).op)
    ((ordinaryCochainFunctor R A).map f.onIntersection.map.op)
    (by
      change (dualComplexFunctor R A (.down ℤ)).map (coverQuotientMap R f).op ≫
        (dualComplexFunctor R A (.down ℤ)).map (cokernel.π _).op =
          (dualComplexFunctor R A (.down ℤ)).map (cokernel.π _).op ≫
            (dualComplexFunctor R A (.down ℤ)).map (middleMap (coverChains R) f).op
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        cover_quotient_projection_natural])
    (by
      change (dualComplexFunctor R A (.down ℤ)).map (middleMap (coverChains R) f).op ≫
        (dualComplexFunctor R A (.down ℤ)).map (chainFirst (coverChains R) C).op =
          (dualComplexFunctor R A (.down ℤ)).map (chainFirst (coverChains R) D).op ≫
            (dualComplexFunctor R A (.down ℤ)).map ((coverChains R).map f.onIntersection).op
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        cover_first_natural])

lemma cover_dual_comparison_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) :
    (ordinaryCochainFunctor R A).map f.map.map.op ≫ coverDualComparison R A C =
      coverDualComparison R A D ≫
        (dualComplexFunctor R A (.down ℤ)).map (coverQuotientMap R f).op := by
  change (dualComplexFunctor R A (.down ℤ)).map ((coverChains R).map f.map).op ≫
    (dualComplexFunctor R A (.down ℤ)).map (coverComparison R C).op = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    cover_comparison_natural]

section NaturalBiproductMaps
variable {B D : Type*} [Category* B] [Category* D] [Preadditive D]
  (F : Bᵒᵖ ⥤ D)
  {X U V X' U' V' : B}
  (i : U ⟶ X) (j : V ⟶ X) (i' : U' ⟶ X') (j' : V' ⟶ X')
  (f : X ⟶ X') (a : U ⟶ U') (b : V ⟶ V')
  [HasBinaryBiproduct (F.obj (op U)) (F.obj (op V))]
  [HasBinaryBiproduct (F.obj (op U')) (F.obj (op V'))]

lemma restrictionBiprod_natural (hi : i ≫ f = a ≫ i') (hj : j ≫ f = b ≫ j') :
    biprod.lift (F.map i'.op) (F.map j'.op) ≫ biprod.map (F.map a.op) (F.map b.op) =
      F.map f.op ≫ biprod.lift (F.map i.op) (F.map j.op) := by
  apply biprod.hom_ext <;>
    simp [Category.assoc, ← F.map_comp, ← op_comp, ← hi, ← hj]

end NaturalBiproductMaps

lemma differenceBiprod_natural {B D : Type*} [Category* B] [Category* D] [Preadditive D]
    (F : Bᵒᵖ ⥤ D) {W U V W' U' V' : B}
    (i : W ⟶ U) (j : W ⟶ V) (i' : W' ⟶ U') (j' : W' ⟶ V')
    (f : W ⟶ W') (a : U ⟶ U') (b : V ⟶ V')
    [HasBinaryBiproduct (F.obj (op U)) (F.obj (op V))]
    [HasBinaryBiproduct (F.obj (op U')) (F.obj (op V'))]
    (hi : i ≫ a = f ≫ i') (hj : j ≫ b = f ≫ j') :
    biprod.desc (F.map i'.op) (-F.map j'.op) ≫ F.map f.op =
      biprod.map (F.map a.op) (F.map b.op) ≫ biprod.desc (F.map i.op) (-F.map j.op) := by
  apply biprod.hom_ext' <;>
    simp [Category.assoc, ← F.map_comp, ← op_comp, hi, hj]

lemma restrictions_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) (q : ℤ) :
    restrictions R A D q ≫
        biprod.map ((ordinaryCohomologyFunctor R A q).map f.onLeft.map.op)
          ((ordinaryCohomologyFunctor R A q).map f.onRight.map.op) =
      (ordinaryCohomologyFunctor R A q).map f.map.map.op ≫ restrictions R A C q := by
  exact restrictionBiprod_natural (ordinaryCohomologyFunctor R A q)
    C.leftInclusion.map C.rightInclusion.map D.leftInclusion.map D.rightInclusion.map
    f.map.map f.onLeft.map f.onRight.map rfl rfl

lemma difference_natural {C D : CoverPair.{v,w}} (f : CoverMap C D) (q : ℤ) :
    difference R A D q ≫ (ordinaryCohomologyFunctor R A q).map f.onIntersection.map.op =
      biprod.map ((ordinaryCohomologyFunctor R A q).map f.onLeft.map.op)
        ((ordinaryCohomologyFunctor R A q).map f.onRight.map.op) ≫ difference R A C q := by
  exact differenceBiprod_natural (ordinaryCohomologyFunctor R A q)
    C.toLeft.map C.toRight.map D.toLeft.map D.toRight.map
    f.onIntersection.map f.onLeft.map f.onRight.map rfl rfl

/-- The homological sequence proves the chain comparison is a quasi-isomorphism;
its homotopy equivalence then gives the cohomological sequence. -/
lemma mayer_vietoris_of_homological
    (mv : P202Specs.MayerVietoris.mayerVietoris_type.{u,v,w}) :
    P202Specs.CohomologyExcisionMV.mayer_vietoris_type.{u,v,w} := by
  intro R _ A _ _
  refine ⟨?_, ?_⟩
  · intro C
    exact ⟨cover_comparison_homotopy R mv C, cover_first_split R C,
      cover_dual_comparison_quasiIso R mv A C⟩
  · let h := cover_cochain_shortExact R A
    have hc (C : CoverPair.{v,w}) (q : ℤ) : IsIso (homologyMap (coverDualComparison R A C) q) := by
      have := cover_dual_comparison_quasiIso R mv A C
      infer_instance
    let δ : CohomologyConnecting R A := fun C q =>
      connecting (h C) q (q+1) (by simp) ≫ inv (homologyMap (coverDualComparison R A C) (q+1))
    have hres (C : CoverPair.{v,w}) (q : ℤ) :
        homologyMap (coverCochainSequence R A C).f q ≫ (cohomologyMiddleIso R A C q).hom =
          inv (homologyMap (coverDualComparison R A C) q) ≫ restrictions R A C q := by
      apply (cancel_epi (homologyMap (coverDualComparison R A C) q)).mp
      simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using cohomologyMiddle_restrictions R A C q
    refine ⟨h, fun C => P202.ChainLES.module_lift _ (h C), δ, ?_, ?_, ?_⟩
    · constructor
      · intro C q
        let S := coverCochainSequence R A C
        let T := ComposableArrows.mk₅ (restrictions R A C q) (difference R A C q) (δ C q)
          (restrictions R A C (q+1)) (difference R A C (q+1))
        let B := P202Specs.ChainLES.segment (h C) q (q+1) (by simp)
        let e : B ≅ T := ComposableArrows.isoMk₅
          (asIso (homologyMap (coverDualComparison R A C) q)).symm
          (cohomologyMiddleIso R A C q) (Iso.refl _)
          (asIso (homologyMap (coverDualComparison R A C) (q+1))).symm
          (cohomologyMiddleIso R A C (q+1)) (Iso.refl _)
          (by simpa [B, T, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using hres C q)
          (by simpa [B, T, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using
            (cohomologyMiddle_difference R A C q).symm)
          (by simp [B, T, P202Specs.ChainLES.segment, δ, -Fin.reduceFinMk])
          (by simpa [B, T, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using hres C (q+1))
          (by simpa [B, T, P202Specs.ChainLES.segment, -Fin.reduceFinMk] using
            (cohomologyMiddle_difference R A C (q+1)).symm)
        exact ComposableArrows.exact_of_iso e
          ((P202.ChainLES.exactness S (h C)).2 q (q+1) (by simp))
      · intro C q
        let S := coverCochainSequence R A C
        let T := ComposableArrows.mk₂ (restrictions R A C q) (difference R A C q)
        let B := HomologicalComplex.HomologySequence.composableArrows₂ S q
        let e : B ≅ T := ComposableArrows.isoMk₂
          (asIso (homologyMap (coverDualComparison R A C) q)).symm
          (cohomologyMiddleIso R A C q) (Iso.refl _)
          (by simpa [B, T, HomologicalComplex.HomologySequence.composableArrows₂,
            -Fin.reduceFinMk] using hres C q)
          (by simpa [B, T, HomologicalComplex.HomologySequence.composableArrows₂,
            -Fin.reduceFinMk] using (cohomologyMiddle_difference R A C q).symm)
        exact ComposableArrows.exact_of_iso e ((P202.ChainLES.exactness S (h C)).1 q)
    · intro C D f
      refine ⟨restrictions_natural R A f, difference_natural R A f, ?_⟩
      intro q
      apply (cancel_mono (homologyMap (coverDualComparison R A C) (q+1))).mp
      have hn : (ordinaryCohomologyFunctor R A (q+1)).map f.map.map.op ≫
          homologyMap (coverDualComparison R A C) (q+1) =
        homologyMap (coverDualComparison R A D) (q+1) ≫
          homologyMap ((dualComplexFunctor R A (.down ℤ)).map (coverQuotientMap R f).op) (q+1) := by
        change homologyMap ((ordinaryCochainFunctor R A).map f.map.map.op) (q+1) ≫ _ = _
        rw [← homologyMap_comp, ← homologyMap_comp, cover_dual_comparison_natural]
      have hnδ := (P202.ChainLES.naturality (coverCochainSequenceMap R A f) (h D) (h C)).2.2
        q (q+1) (by simp)
      simp only [δ, Category.assoc, hn, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hnδ
    · intro C q
      simp only [δ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]


/-- Natural ordinary cohomological Mayer–Vietoris for all open two-set covers
and arbitrary coefficient modules, including degree zero. -/
theorem mayer_vietoris :
  ∀ (R : Type u) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A],
    (∀ C : CoverPair.{v,w},
      (∃ e : HomotopyEquiv (coverQuotient R C) ((coverChains R).obj C.pair),
        e.hom = coverComparison R C) ∧
      (∀ q : ℤ, ∃ r : (middle (coverChains R) C).X q ⟶
          ((coverChains R).obj C.intersectionPair).X q,
        (chainFirst (coverChains R) C).f q ≫ r = 𝟙 _) ∧
      QuasiIso (coverDualComparison R A C)) ∧
    ∃ h : ∀ C : CoverPair.{v,w}, DegreewiseShortExact (coverCochainSequence R A C),
      (∀ C, LiftsExist (coverCochainSequence R A C) (h C) ∧
        LiftFormula (coverCochainSequence R A C) (h C) ∧
        Independence (coverCochainSequence R A C) (h C)) ∧
      ∃ δ : CohomologyConnecting R A,
        CohomologyExact R A δ ∧ CohomologyNatural R A δ ∧
          CohomologyConnectingFormula R A h δ :=
  mayer_vietoris_of_homological P202.MayerVietoris.mayerVietoris

end P202.CohomologyExcisionMV
