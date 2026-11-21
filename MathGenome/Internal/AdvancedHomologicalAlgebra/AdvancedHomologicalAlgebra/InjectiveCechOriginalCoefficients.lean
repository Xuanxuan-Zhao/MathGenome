import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveCechExactness
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafUniverseTransport
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.HomCongr

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.CechOriginal
open scoped AdvancedHomologicalAlgebra.CechOriginal

universe u r m v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
set_option maxRecDepth 3500

namespace AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)

lemma sectionAt_restrict {V W : Opens X}
    {V' W' : Opens (liftedSpace.{max m u r} X)}
    (hV : opensEquiv.{max m u r} X V' = V) (hW : opensEquiv.{max m u r} X W' = W)
    (i : V ⟶ W) (i' : V' ⟶ W') (s : M.val.obj (op W)) :
    sectionAt.{u,r,m} R M V' V hV (M.val.map i.op s) =
      ((transport.{m} R).obj M).val.map i'.op (sectionAt.{u,r,m} R M W' W hW s) := by
  subst V W
  rfl

theorem cochain_comparison :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.cochainComparisonType.{u,r,m,v} := by
  intro X R M U I c
  constructor
  · intro s
    funext t
    exact sectionAt_restrict.{u,r,m} R M (liftCover_tuple.{u,r,m,v} c t) ((opensEquiv X).apply_symm_apply U)
      (homOfLE (tupleOpen_le c t)) (homOfLE (tupleOpen_le _ t)) s
  · intro p s
    simp only [Cech.differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    funext t
    exact sectionAt_restrict.{u,r,m} R M (liftCover_tuple.{u,r,m,v} c t)
      (liftCover_tuple.{u,r,m,v} c (t ∘ a.succAbove))
      (homOfLE (tupleOpen_reindex_le c _ t)) (homOfLE (tupleOpen_reindex_le _ _ t))
      (s (t ∘ a.succAbove))

theorem injective_exact :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.injectiveExactness.{u,r,m,v} := by
  intro X R U I c M hM
  let N := (transport.{m} R).obj M
  let d := liftCover.{u,m,r,v} c
  have hN : Injective N := ((transportEquivalence.{m} R).map_injective_iff M).2 hM
  obtain ⟨ha, hz, hp⟩ := InjectiveCechExactness.injective_exact (liftedRing.{m} R) d N hN
  obtain ⟨haug, hd⟩ := cochain_comparison.{u,r,m,v} R M c
  let e := sectionAt.{u,r,m} R M _ U ((opensEquiv.{max m u r} X).apply_symm_apply U)
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    apply e.injective
    apply ha
    rw [← haug, ← haug, h]
  · intro z h
    have hc : differential (liftedRing.{m} R) N.val d 0 (cochainComparison.{u,r,m,v} R M c 0 z) = 0 := by
      rw [← hd, h, map_zero]
    obtain ⟨s, hs⟩ := hz _ hc
    refine ⟨e.symm s, (cochainComparison.{u,r,m,v} R M c 0).injective ?_⟩
    rw [haug]
    exact (congrArg (augmentation (liftedRing.{m} R) N.val d) (e.apply_symm_apply s)).trans hs
  · intro p z h
    have hc : differential (liftedRing.{m} R) N.val d (p + 1)
        (cochainComparison.{u,r,m,v} R M c (p + 1) z) = 0 := by
      rw [← hd, h, map_zero]
    obtain ⟨y, hy⟩ := hp p _ hc
    refine ⟨(cochainComparison.{u,r,m,v} R M c p).symm y, (cochainComparison.{u,r,m,v} R M c (p + 1)).injective ?_⟩
    rwa [hd, AddEquiv.apply_symm_apply]


section OriginalChain

variable (D : OpenUnits.{u,r,m} R)

private lemma cast_evaluation {V W : Opens X} (h : V = W) {A B : AmbientSheaves.{m} R}
    (e : (A ⟶ B) ≃+ B.val.obj (op V)) (s : A.val.obj (op V))
    (f : A ⟶ B) (he : e f = f.val.app (op V) s) :
    (h ▸ e : (A ⟶ B) ≃+ B.val.obj (op W)) f = f.val.app (op W) (h ▸ s) := by
  cases h
  exact he

lemma unitEvaluation_apply (V : Opens X) (B : AmbientSheaves.{m} R) (f : extendedUnit.{u,r,m} R D V ⟶ B) :
    unitEvaluation.{u,r,m} R D V B f = f.val.app (op V) (unitGenerator.{u,r,m} R D V) :=
  cast_evaluation.{u,r,m} R ((opensEquiv.{max m u r} X).apply_symm_apply V) _ _ f
    ((D _).sectionRepresentation_apply _ _)

lemma unitMap_generator {V W : Opens X} (h : V ≤ W) :
    (unitMap.{u,r,m} R D h).val.app (op V) (unitGenerator.{u,r,m} R D V) =
      (extendedUnit.{u,r,m} R D W).val.map (homOfLE h).op (unitGenerator.{u,r,m} R D W) := by
  rw [← unitEvaluation_apply, unitMap, AddEquiv.apply_symm_apply]

lemma unitEvaluation_restrict {V W : Opens X} (h : V ≤ W)
    (B : AmbientSheaves.{m} R) (f : extendedUnit.{u,r,m} R D W ⟶ B) :
    unitEvaluation.{u,r,m} R D V B (unitMap.{u,r,m} R D h ≫ f) =
      B.val.map (homOfLE h).op (unitEvaluation.{u,r,m} R D W B f) := by
  rw [unitEvaluation_apply, unitEvaluation_apply]
  change f.val.app (op V) ((unitMap.{u,r,m} R D h).val.app (op V) (unitGenerator.{u,r,m} R D V)) = _
  rw [unitMap_generator]
  exact PresheafOfModules.naturality_apply f.val (homOfLE h).op (unitGenerator.{u,r,m} R D W)

lemma unitRightMul_generator (V : Opens X) (a : sectionRing R V) :
    (unitRightMul.{u,r,m} R D V a).val.app (op V) (unitGenerator.{u,r,m} R D V) = a • unitGenerator.{u,r,m} R D V := by
  rw [← unitEvaluation_apply, unitRightMul, AddEquiv.apply_symm_apply]

variable {U : Opens X} {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R)
variable (B : AmbientSheaves.{max m v} R)

lemma original_hom_face {p q : ℕ} (i : Fin (p + 1) → Fin (q + 1)) (f : term.{u,r,m,v} R c E p ⟶ B) :
    homCochains.{u,r,m,v} R c E B q (face.{u,r,m,v} R c E i ≫ f) =
      reindex R B.val c i (homCochains.{u,r,m,v} R c E B p f) := by
  funext t
  change unitEvaluation.{u,r,max m v} R E (tupleOpen c t) B
    (Sigma.ι (tupleUnits.{u,r,m,v} R c E q) t ≫ face.{u,r,m,v} R c E i ≫ f) = _
  rw [← Category.assoc, face, Sigma.ι_comp_desc, Category.assoc, unitEvaluation_restrict]
  rfl

lemma original_hom_boundary (p : ℕ) (f : term.{u,r,m,v} R c E p ⟶ B) :
    homCochains.{u,r,m,v} R c E B (p + 1) (boundary.{u,r,m,v} R c E p ≫ f) =
      differential R B.val c p (homCochains.{u,r,m,v} R c E B p f) := by
  rw [boundary, Preadditive.sum_comp, map_sum]
  simp only [Preadditive.zsmul_comp, map_zsmul, original_hom_face, differential,
    LinearMap.sum_apply, LinearMap.smul_apply]

lemma original_hom_augmentation (f : extendedUnit.{u,r,max m v} R E U ⟶ B) :
    homCochains.{u,r,m,v} R c E B 0 (chainAugmentation.{u,r,m,v} R c E ≫ f) =
      augmentation R B.val c (unitEvaluation.{u,r,max m v} R E U B f) := by
  funext t
  change unitEvaluation.{u,r,max m v} R E (tupleOpen c t) B
    (Sigma.ι (tupleUnits.{u,r,m,v} R c E 0) t ≫ chainAugmentation.{u,r,m,v} R c E ≫ f) = _
  rw [← Category.assoc, chainAugmentation, Sigma.ι_comp_desc, unitEvaluation_restrict]
  rfl

lemma original_hom_rightMul (p : ℕ) (a : sectionRing R U) (f : term.{u,r,m,v} R c E p ⟶ B) :
    homCochains.{u,r,m,v} R c E B p (termRightMul.{u,r,m,v} R c E p a ≫ f) = a • homCochains.{u,r,m,v} R c E B p f := by
  funext t
  change unitEvaluation.{u,r,max m v} R E (tupleOpen c t) B
    (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ termRightMul.{u,r,m,v} R c E p a ≫ f) = _
  rw [← Category.assoc, termRightMul, Sigma.ι_comp_desc, Category.assoc, unitEvaluation_apply]
  change (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ f).val.app (op (tupleOpen c t))
    ((unitRightMul.{u,r,max m v} R E (tupleOpen c t) _).val.app (op (tupleOpen c t))
      (unitGenerator.{u,r,max m v} R E (tupleOpen c t))) = _
  rw [unitRightMul_generator, (SheafOfModules.Hom.val _ |>.app _).hom.map_smul]
  change (R.obj.map (homOfLE (tupleOpen_le c t)).op a) • (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ f).val.app _ (unitGenerator.{u,r,max m v} R E _) =
    (R.obj.map (homOfLE (tupleOpen_le c t)).op a) • unitEvaluation.{u,r,max m v} R E (tupleOpen c t) B (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ f)
  rw [unitEvaluation_apply]

theorem original_hom :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalHomType.{u,r,m,v} := by
  intro X R U I c E B
  refine ⟨original_hom_augmentation R c E B, original_hom_boundary.{u,r,m,v} R c E B, ?_⟩
  intro p
  let e := homCochains.{u,r,m,v} R c E B p
  refine ⟨fun f t ↦ unitEvaluation_apply.{u,r,max m v} R E _ _ _, ?_, e.module (sectionRing R U), ?_, ?_⟩
  · intro N g f t
    change unitEvaluation.{u,r,max m v} R E (tupleOpen c t) N (_ ≫ _) =
      g.val.app (op (tupleOpen c t)) (unitEvaluation.{u,r,max m v} R E (tupleOpen c t) B (_ ≫ _))
    rw [unitEvaluation_apply, unitEvaluation_apply, ← Category.assoc]
    rfl
  · letI := e.module (sectionRing R U)
    intro a f
    apply e.injective
    change e (a • f) = homCochains.{u,r,m,v} R c E B p (termRightMul.{u,r,m,v} R c E p a ≫ f)
    rw [original_hom_rightMul]
    exact (e.linearEquiv (sectionRing R U)).map_smul a f
  · exact ⟨e.linearEquiv (sectionRing R U), fun _ ↦ rfl⟩

theorem original_chain :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalChainType.{u,r,m,v} := by
  intro X R U I c E
  have hA : boundary.{u,r,m,v} R c E 0 ≫ chainAugmentation.{u,r,m,v} R c E = 0 := by
    let B := extendedUnit.{u,r,max m v} R E U
    let eval := homCochains.{u,r,m,v} R c E B 1
    let s := unitEvaluation.{u,r,max m v} R E U B (𝟙 B)
    have ha : homCochains.{u,r,m,v} R c E B 0 (chainAugmentation.{u,r,m,v} R c E) =
        augmentation R B.val c s := by
      let a := chainAugmentation.{u,r,m,v} R c E
      exact (congrArg (fun f : term.{u,r,m,v} R c E 0 ⟶ B ↦ homCochains.{u,r,m,v} R c E B 0 f)
        (Category.comp_id a)).symm.trans (original_hom_augmentation.{u,r,m,v} R c E B (𝟙 B))
    apply eval.injective
    calc
      _ = differential R B.val c 0 (homCochains.{u,r,m,v} R c E B 0
          (chainAugmentation.{u,r,m,v} R c E)) := original_hom_boundary.{u,r,m,v} R c E B 0 _
      _ = differential R B.val c 0 (augmentation R B.val c s) :=
        congrArg (fun z ↦ differential R B.val c 0 z) ha
      _ = 0 := LinearMap.congr_fun (CechCochains.augmentation_closed R B.val c) s
      _ = eval 0 := (map_zero eval).symm
  have hD (p : ℕ) : boundary.{u,r,m,v} R c E (p + 1) ≫ boundary.{u,r,m,v} R c E p = 0 := by
    let B := term.{u,r,m,v} R c E p
    let eval := homCochains.{u,r,m,v} R c E B (p + 2)
    let s := homCochains.{u,r,m,v} R c E B p (𝟙 B)
    have hd : homCochains.{u,r,m,v} R c E B (p + 1) (boundary.{u,r,m,v} R c E p) =
        differential R B.val c p s := by
      let a := boundary.{u,r,m,v} R c E p
      exact (congrArg (fun f : term.{u,r,m,v} R c E (p + 1) ⟶ B ↦ homCochains.{u,r,m,v} R c E B (p + 1) f)
        (Category.comp_id a)).symm.trans (original_hom_boundary.{u,r,m,v} R c E B p (𝟙 B))
    apply eval.injective
    calc
      _ = differential R B.val c (p + 1) (homCochains.{u,r,m,v} R c E B (p + 1)
          (boundary.{u,r,m,v} R c E p)) := original_hom_boundary.{u,r,m,v} R c E B (p + 1) _
      _ = differential R B.val c (p + 1) (differential R B.val c p s) :=
        congrArg (fun z ↦ differential R B.val c (p + 1) z) hd
      _ = 0 := LinearMap.congr_fun (CechCochains.differential_squared R B.val c p) s
      _ = eval 0 := (map_zero eval).symm
  refine ⟨hA, hD, ChainComplex.of (term.{u,r,m,v} R c E) (boundary.{u,r,m,v} R c E) hD,
    fun _ ↦ Iso.refl _, ?_⟩
  intro p
  change ChainComplex.of.d (term.{u,r,m,v} R c E) (boundary.{u,r,m,v} R c E) (p + 1) p ≫ 𝟙 _ =
    𝟙 _ ≫ boundary.{u,r,m,v} R c E p
  rw [ChainComplex.of_d, Category.comp_id, Category.id_comp]

end OriginalChain


section Contraction

variable {U : Opens X} {I : Type v} (c : Cover U I) (x : X)
  (A : Type m) [Ring A] (i : I) (hi : x ∈ c.opens i)

private lemma face_prepend_zero {p : ℕ} (t : SupportedTuple c x p) :
    supportedFace c x (0 : Fin (p + 2)).succAbove (supportedPrepend c x i hi t) = t := by
  apply Subtype.ext
  funext a
  simp [supportedFace, supportedPrepend]

private lemma face_prepend_succ {p : ℕ} (t : SupportedTuple c x (p + 1)) (a : Fin (p + 2)) :
    supportedFace c x a.succ.succAbove (supportedPrepend c x i hi t) =
      supportedPrepend c x i hi (supportedFace c x a.succAbove t) :=
  Subtype.ext (Fin.cons_comp_succ_succAbove i t.val a)

private lemma face_prepend_one (t : SupportedTuple c x 0) :
    supportedFace c x (1 : Fin 2).succAbove (supportedPrepend c x i hi t) =
      (⟨fun _ ↦ i, hi⟩ : SupportedTuple c x 0) := by
  apply Subtype.ext
  funext a
  change Fin 1 at a
  rw [Subsingleton.elim a 0]
  rfl

theorem prepend_contraction :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.prependContractionType.{u,m,v} := by
  intro X U I c x A _ i hi
  refine ⟨?_, ?_, ?_⟩
  · ext
    simp [freeAugmentation, freePrependAugmentation, Finsupp.linearCombination_single]
  · apply (Finsupp.lift _ A _).symm.injective
    funext t
    simp only [Finsupp.lift_symm_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, freePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      freeBoundary, LinearMap.smul_apply, Nat.reduceAdd, Fin.sum_univ_two,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, neg_zsmul,
      face_prepend_zero, face_prepend_one, freePrependAugmentation, freeAugmentation,
      Finsupp.linearCombination_single, one_smul, Finsupp.lsingle_apply]
    abel
  · intro p
    apply (Finsupp.lift _ A _).symm.injective
    funext t
    simp only [Finsupp.lift_symm_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, freePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      freeBoundary, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_zsmul, face_prepend_zero, Fin.val_succ, pow_succ,
      mul_neg, mul_one, neg_zsmul, face_prepend_succ]
    rw [Finset.sum_neg_distrib]
    rw [← Finsupp.lmapDomain_apply (M := A) (R := A), map_sum]
    simp only [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    abel

end Contraction


section TupleStalks

variable {U : Opens X} {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R)
variable (x : X) (p : ℕ)
variable (N : ModuleCat.{max u r m v} (originalStalkRing.{max m v} R x))

private def tupleStalkEvaluation :
    (((originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p)) ⟶ N) ≃
      (SupportedTuple c x p → N) :=
  (originalStalkSkyscraperHomEquiv.{max m v} R x (term.{u,r,m,v} R c E p) N).trans
    ((homCochains.{u,r,m,v} R c E ((originalSkyscraperFunctor.{max m v} R x).obj N) p).toEquiv.trans
      { toFun := fun s t ↦ s t.val ⟨t.property⟩
        invFun := fun a t hx ↦ a ⟨t, hx.down⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

private lemma tupleStalkEvaluation_apply
    (f : (originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p) ⟶ N)
    (t : SupportedTuple c x p) :
    tupleStalkEvaluation.{u,r,m,v} R c E x p N f t = f (tupleGerm.{u,r,m,v} R c E x p t) := by
  change unitEvaluation.{u,r,max m v} R E (tupleOpen c t.val)
    ((originalSkyscraperFunctor.{max m v} R x).obj N)
    (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t.val ≫ toOriginalSkyscraper.{max m v} R x f)
      ⟨t.property⟩ = _
  rw [unitEvaluation_apply]
  rfl

lemma tupleStalkMap_single (t : SupportedTuple c x p) :
    tupleStalkMap.{u,r,m,v} R c E x p (Finsupp.single t 1) = tupleGerm.{u,r,m,v} R c E x p t := by
  change Finsupp.linearCombination _ (tupleGerm.{u,r,m,v} R c E x p) (Finsupp.single t 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

theorem original_tuple_stalk :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalTupleStalkType.{u,r,m,v} := by
  intro X R U I c E x p
  refine ⟨?_, tupleStalkMap_single.{u,r,m,v} R c E x p⟩
  apply isIso_of_coyoneda_map_bijective
  intro N
  let S := originalStalkRing.{max m v} R x
  let L := (ModuleCat.homEquiv (M := ModuleCat.of S (SupportedTuple c x p →₀ S))
    (N := N)).trans (Finsupp.lift N S (SupportedTuple c x p)).symm.toEquiv
  have h : (fun f : (originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p) ⟶ N ↦
      tupleStalkMap.{u,r,m,v} R c E x p ≫ f) = L.symm ∘ tupleStalkEvaluation.{u,r,m,v} R c E x p N := by
    funext f
    apply L.injective
    funext t
    change f (tupleStalkMap.{u,r,m,v} R c E x p (Finsupp.single t 1)) =
      L (L.symm (tupleStalkEvaluation.{u,r,m,v} R c E x p N f)) t
    rw [L.apply_symm_apply, tupleStalkEvaluation_apply, tupleStalkMap_single]
  rw [h]
  exact L.symm.bijective.comp (tupleStalkEvaluation.{u,r,m,v} R c E x p N).bijective

end TupleStalks


section StalkBoundary

instance originalStalkAdditive (x : X) :
    (originalStalkFunctor.{m} R x).Additive where
  map_add {M N} f g := by
    ext s
    obtain ⟨V, hV, z, rfl⟩ := originalModuleGerm_exists.{m} R x M.val s
    change originalModuleStalkMap.{m} R x (f + g).val
        (originalModuleGerm.{m} R x M.val V hV z) =
      originalModuleStalkMap.{m} R x f.val (originalModuleGerm.{m} R x M.val V hV z) +
        originalModuleStalkMap.{m} R x g.val (originalModuleGerm.{m} R x M.val V hV z)
    simp only [originalModuleStalkMap_germ]
    change originalModuleGerm.{m} R x N.val V hV (f.val.app (op V) z + g.val.app (op V) z) = _
    exact map_add (originalModuleGerm.{m} R x N.val V hV) _ _

variable {U : Opens X} {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R) (x : X)

lemma original_stalk_face {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (t : SupportedTuple c x q) :
    (originalStalkFunctor.{max m v} R x).map (face.{u,r,m,v} R c E f) (tupleGerm.{u,r,m,v} R c E x q t) =
      tupleGerm.{u,r,m,v} R c E x p (supportedFace c x f t) := by
  let V := tupleOpen c t.val
  let W := tupleOpen c (t.val ∘ f)
  let h : V ≤ W := tupleOpen_reindex_le c f t.val
  let g := unitGenerator.{u,r,max m v} R E W
  let e := Sigma.ι (tupleUnits.{u,r,m,v} R c E p) (t.val ∘ f)
  unfold tupleGerm
  change originalModuleStalkMap.{max m v} R x (face.{u,r,m,v} R c E f).val
    (originalModuleGerm.{max m v} R x _ V t.property _) =
      originalModuleGerm.{max m v} R x _ W (h t.property) (e.val.app (op W) g)
  rw [originalModuleStalkMap_germ]
  have he : Sigma.ι (tupleUnits.{u,r,m,v} R c E q) t.val ≫ face.{u,r,m,v} R c E f = unitMap.{u,r,max m v} R E h ≫ e :=
    Sigma.ι_comp_desc _ _
  change originalModuleGerm.{max m v} R x _ V t.property
      ((Sigma.ι (tupleUnits.{u,r,m,v} R c E q) t.val ≫ face.{u,r,m,v} R c E f).val.app _ (unitGenerator.{u,r,max m v} R E V)) = _
  rw [he]
  change originalModuleGerm.{max m v} R x _ V t.property
      (e.val.app (op V) ((unitMap.{u,r,max m v} R E h).val.app (op V) (unitGenerator.{u,r,max m v} R E V))) = _
  rw [unitMap_generator]
  exact (congrArg (fun s : (term.{u,r,m,v} R c E p).val.obj (op V) ↦
      originalModuleGerm.{max m v} R x _ V t.property s)
    (PresheafOfModules.naturality_apply e.val (homOfLE h).op g)).trans
      (originalModuleGerm_restrict R x _ (homOfLE h).op t.property (e.val.app (op W) g))

theorem original_stalk_boundary :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalStalkBoundaryType.{u,r,m,v} := by
  intro X R U I c E x p
  apply ModuleCat.hom_ext
  apply (Finsupp.lift _ _ _).symm.injective
  funext t
  simp only [Finsupp.lift_symm_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  change (originalStalkFunctor.{max m v} R x).map (boundary.{u,r,m,v} R c E p) (tupleStalkMap.{u,r,m,v} R c E x (p + 1) (Finsupp.single t 1)) =
    tupleStalkMap.{u,r,m,v} R c E x p (freeBoundary c x _ p (Finsupp.single t 1))
  rw [tupleStalkMap_single]
  change ((originalStalkFunctor.{max m v} R x).map (boundary.{u,r,m,v} R c E p)).hom
      (tupleGerm.{u,r,m,v} R c E x (p + 1) t) =
    (tupleStalkMap.{u,r,m,v} R c E x p).hom (freeBoundary c x _ p (Finsupp.single t 1))
  simp only [boundary, freeBoundary, Functor.map_sum, Functor.map_zsmul,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun s : (originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p) ↦
    ((-1 : ℤ) ^ a.val) • s) ((original_stalk_face R c E x a.succAbove t).trans
      (tupleStalkMap_single R c E x p (supportedFace c x a.succAbove t)).symm)

end StalkBoundary


section TopUnit

private def structureSection (M : AmbientSheaves.{m} R) (s : M.val.obj (op (⊤ : Opens X))) :
    ambientUnit.{u,r,m} R ⟶ M where
  val :=
    { app V := ModuleCat.ofHom (X := (ambientUnit.{u,r,m} R).val.obj V) (Y := M.val.obj V)
        { toFun := fun c ↦ (show R.obj.obj V from c.down) •
            (show M.val.obj V from M.val.map (homOfLE (show V.unop ≤ (⊤ : Opens X) from le_top)).op s)
          map_add' := fun _ _ ↦ add_smul _ _ _
          map_smul' := fun _ _ ↦ mul_smul _ _ _ }
      naturality := by
        intro V W f
        ext c
        symm
        change M.val.map f ((show R.obj.obj V from c.down) •
          (show M.val.obj V from M.val.map (homOfLE (show V.unop ≤ (⊤ : Opens X) from le_top)).op s)) =
          R.obj.map f (show R.obj.obj V from c.down) •
            (show M.val.obj W from M.val.map (homOfLE (show W.unop ≤ (⊤ : Opens X) from le_top)).op s)
        rw [M.val.map_smul, ← M.val.map_comp_apply]
        rfl }

private lemma structureSection_eval (M : AmbientSheaves.{m} R) (s : M.val.obj (op (⊤ : Opens X))) :
    (structureSection.{u,r,m} R M s).val.app (op ⊤) (ULift.up (1 : sectionRing R (⊤ : Opens X))) =
      s := by
  change (1 : sectionRing R (⊤ : Opens X)) •
    (show M.val.obj (op (⊤ : Opens X)) from M.val.map (𝟙 (op (⊤ : Opens X))) s) = s
  rw [one_smul]
  exact congr($(M.val.presheaf.map_id (op (⊤ : Opens X))) s)

private lemma structureSection_ext (M : AmbientSheaves.{m} R) {f g : ambientUnit.{u,r,m} R ⟶ M}
    (h : f.val.app (op ⊤) (ULift.up (1 : sectionRing R (⊤ : Opens X))) =
      g.val.app (op ⊤) (ULift.up (1 : sectionRing R (⊤ : Opens X)))) : f = g := by
  ext V c
  let a : R.obj.obj V := c.down
  let i : op (⊤ : Opens X) ⟶ V := (homOfLE (show V.unop ≤ (⊤ : Opens X) from le_top)).op
  let one := ULift.up.{max m u r} (1 : sectionRing R (⊤ : Opens X))
  have h1 : (ambientUnit.{u,r,m} R).val.map i one =
      ULift.up (1 : R.obj.obj V) := by
    change ULift.up (R.obj.map i (1 : sectionRing R (⊤ : Opens X))) = _
    rw [map_one]
  have hc : c = a •
      (ULift.up (1 : R.obj.obj V) : (ambientUnit.{u,r,m} R).val.obj V) := by
    apply ULift.ext
    exact (mul_one a).symm
  have hf := PresheafOfModules.naturality_apply f.val i one
  have hg := PresheafOfModules.naturality_apply g.val i one
  rw [h1] at hf hg
  rw [show f.val.app V c = f.val.app V
        (a • (ULift.up (1 : R.obj.obj V) : (ambientUnit.{u,r,m} R).val.obj V))
      from congrArg (fun s ↦ f.val.app V s) hc,
    show g.val.app V c = g.val.app V
        (a • (ULift.up (1 : R.obj.obj V) : (ambientUnit.{u,r,m} R).val.obj V))
      from congrArg (fun s ↦ g.val.app V s) hc,
    (f.val.app V).hom.map_smul, (g.val.app V).hom.map_smul]
  exact congrArg (fun t : M.val.obj V ↦ a • t)
    (hf.trans ((congrArg (fun s : M.val.obj (op ⊤) ↦ M.val.map i s) h).trans hg.symm))

def topUnitComparison :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.topUnitComparisonType.{u,r,m} := by
  intro X R E
  let A := extendedUnit.{u,r,m} R E ⊤
  let B := ambientUnit.{u,r,m} R
  let one : B.val.obj (op ⊤) := ULift.up (1 : sectionRing R (⊤ : Opens X))
  let f : A ⟶ B := (unitEvaluation.{u,r,m} R E ⊤ B).symm one
  let g : B ⟶ A := structureSection.{u,r,m} R A (unitGenerator.{u,r,m} R E ⊤)
  have hf : f.val.app (op ⊤) (unitGenerator.{u,r,m} R E ⊤) = one := by
    rw [← unitEvaluation_apply]
    exact (unitEvaluation.{u,r,m} R E ⊤ B).apply_symm_apply one
  have hg : g.val.app (op ⊤) one = unitGenerator.{u,r,m} R E ⊤ :=
    structureSection_eval.{u,r,m} R A _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (unitEvaluation.{u,r,m} R E ⊤ A).injective
    rw [unitEvaluation_apply, unitEvaluation_apply]
    change g.val.app (op ⊤) (f.val.app (op ⊤) (unitGenerator.{u,r,m} R E ⊤)) = _
    rw [hf, hg]
    rfl
  · apply structureSection_ext.{u,r,m} R B
    change f.val.app (op ⊤) (g.val.app (op ⊤) one) = _
    rw [hg, hf]
    rfl

end TopUnit


section StalkAugmentation

private lemma unitStalkMap_one (E : OpenUnits.{u,r,m} R) (x : X) (U : Opens X) (hx : x ∈ U) :
    unitStalkMap.{u,r,m} R E x U hx (1 : originalStalkRing.{m} R x) =
      unitGerm.{u,r,m} R E x U hx :=
  one_smul _ _

theorem unitStalkMap_isIso (E : OpenUnits.{u,r,m} R) (x : X) (U : Opens X) (hx : x ∈ U) :
    IsIso (unitStalkMap.{u,r,m} R E x U hx) := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  let A := extendedUnit.{u,r,m} R E U
  let K := (originalSkyscraperFunctor.{m} R x).obj N
  let e : ((originalStalkFunctor.{m} R x).obj A ⟶ N) ≃ N :=
    (originalStalkSkyscraperHomEquiv.{m} R x A N).trans
      ((unitEvaluation.{u,r,m} R E U K).toEquiv.trans
        { toFun := fun s ↦ s ⟨hx⟩
          invFun := fun n _ ↦ n
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl })
  let ee : (ModuleCat.of (originalStalkRing.{m} R x) (originalStalkRing.{m} R x) ⟶ N) ≃ N :=
    ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf (originalStalkRing.{m} R x) ℕ N).toEquiv
  have h : (fun f : (originalStalkFunctor.{m} R x).obj A ⟶ N ↦
      unitStalkMap.{u,r,m} R E x U hx ≫ f) = ee.symm ∘ e := by
    funext f
    apply ee.injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    change f (unitStalkMap.{u,r,m} R E x U hx (1 : originalStalkRing.{m} R x)) =
      unitEvaluation.{u,r,m} R E U K (toOriginalSkyscraper.{m} R x f) ⟨hx⟩
    rw [unitStalkMap_one, unitEvaluation_apply]
    rfl
  rw [h]
  exact ee.symm.bijective.comp e.bijective

theorem original_stalk_augmentation :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalStalkAugmentationType.{u,r,m,v} := by
  intro X R U I c E x hx
  refine ⟨unitStalkMap_isIso.{u,r,max m v} R E x U hx, ?_⟩
  apply ModuleCat.hom_ext
  apply (Finsupp.lift _ _ _).symm.injective
  funext t
  simp only [Finsupp.lift_symm_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    freeAugmentation, Finsupp.linearCombination_single, one_smul]
  change (originalStalkFunctor.{max m v} R x).map (chainAugmentation.{u,r,m,v} R c E)
    (tupleStalkMap.{u,r,m,v} R c E x 0 (Finsupp.single t 1)) =
      unitStalkMap.{u,r,max m v} R E x U hx (1 : originalStalkRing.{max m v} R x)
  rw [tupleStalkMap_single, unitStalkMap_one]
  unfold tupleGerm unitGerm
  rw [show (originalStalkFunctor.{max m v} R x).map (chainAugmentation.{u,r,m,v} R c E)
      (originalModuleGerm.{max m v} R x _ _ t.property _) =
    originalModuleGerm.{max m v} R x _ _ t.property
      ((chainAugmentation.{u,r,m,v} R c E).val.app _ _) from originalModuleStalkMap_germ _ _ _ _ _ _]
  have he : Sigma.ι (tupleUnits.{u,r,m,v} R c E 0) t.val ≫ chainAugmentation.{u,r,m,v} R c E =
      unitMap.{u,r,max m v} R E (tupleOpen_le c t.val) := Sigma.ι_comp_desc _ _
  change originalModuleGerm.{max m v} R x _ _ t.property
    ((Sigma.ι (tupleUnits.{u,r,m,v} R c E 0) t.val ≫ chainAugmentation.{u,r,m,v} R c E).val.app _
      (unitGenerator.{u,r,max m v} R E (tupleOpen c t.val))) = _
  rw [he, unitMap_generator, originalModuleGerm_restrict]

end StalkAugmentation


section TransportUnits

theorem normalized_units :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.normalizedUnitsType.{u,r,m} := by
  intro X R
  exact ⟨show OpenUnits.{u,r,m} R from openTransportData X R⟩

open AdvancedHomologicalAlgebra.CechChains (largeOpenUnit largeOpenUnitGenerator SectionPresentation)
open AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction (homOpenUnit homOpenUnit_eval)

private def liftedUnitIso {Y : TopCat.{max m v}} (S : RingSheaf Y) (W : Opens Y) :
    openUnit S W ≅ largeOpenUnit.{max m v,v} S W := by
  let P := InjectiveCechExactness.presentation.{max m v,v} S
  let A := openUnit S W
  let B := largeOpenUnit.{max m v,v} S W
  let f : A ⟶ B := (homOpenUnit S W B).symm (largeOpenUnitGenerator.{max m v,v} S W)
  let g : B ⟶ A := (P.equiv W A).symm (openUnitGenerator S W)
  have hf : f.val.app (op W) (openUnitGenerator S W) = largeOpenUnitGenerator.{max m v,v} S W :=
    (homOpenUnit_eval S W B f).symm.trans ((homOpenUnit S W B).apply_symm_apply _)
  have hg : g.val.app (op W) (largeOpenUnitGenerator.{max m v,v} S W) = openUnitGenerator S W :=
    (P.evaluation W A g).symm.trans ((P.equiv W A).apply_symm_apply _)
  refine ⟨f, g, ?_, ?_⟩
  · apply (homOpenUnit S W A).injective
    rw [homOpenUnit_eval, homOpenUnit_eval]
    change g.val.app (op W) (f.val.app (op W) (openUnitGenerator S W)) = _
    rw [hf, hg]
    rfl
  · apply (P.equiv W B).injective
    rw [P.evaluation, P.evaluation]
    change f.val.app (op W) (g.val.app (op W) (largeOpenUnitGenerator.{max m v,v} S W)) = _
    rw [hg, hf]
    rfl

private lemma liftedUnitIso_generator {Y : TopCat.{max m v}} (S : RingSheaf Y) (W : Opens Y) :
    (liftedUnitIso.{m,v} S W).hom.val.app (op W) (openUnitGenerator S W) =
      largeOpenUnitGenerator.{max m v,v} S W :=
  (homOpenUnit_eval S W _ _).symm.trans ((homOpenUnit S W _).apply_symm_apply _)

private lemma sectionAt_cast (W : Opens (liftedSpace.{max m u r} X)) (V : Opens X)
    (h : opensEquiv.{max m u r} X W = V) (s : M.val.obj (op (opensEquiv.{max m u r} X W))) :
    sectionAt.{u,r,m} R M W V h (h ▸ s) = sectionEquiv.{m} R M W s := by
  subst V
  rfl

private lemma sectionAt_map {A B : AmbientSheaves.{m} R} (f : A ⟶ B)
    (W : Opens (liftedSpace.{max m u r} X)) (V : Opens X)
    (h : opensEquiv.{max m u r} X W = V) (s : A.val.obj (op V)) :
    sectionAt.{u,r,m} R B W V h (f.val.app (op V) s) =
      ((transport.{m} R).map f).val.app (op W) (sectionAt.{u,r,m} R A W V h s) := by
  subst V
  rfl

private lemma iso_inv_apply_hom {Y : TopCat.{u}} {S : Y.Sheaf RingCat.{r}}
    {A B : SheafOfModules.{m} S} (j : A ≅ B) (W : Opens Y) (s : A.val.obj (op W)) :
    j.inv.val.app (op W) (j.hom.val.app (op W) s) = s :=
  congrArg (fun f : A ⟶ A ↦ f.val.app (op W) s) j.hom_inv_id

theorem unit_transport :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.unitTransportType.{u,r,m,v} := by
  intro X R E
  let e := opensEquiv.{max m v u r} X
  let S := liftedRing.{max m v} R
  let T := transport.{max m v} R
  let J (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (h : e V' = V) :
      T.obj (extendedUnit.{u,r,max m v} R E V) ≅ largeOpenUnit.{max m v u r,v} S V' :=
    (E (e.symm V)).unitComparison ≪≫
      eqToIso (congrArg (openUnit S) (e.injective ((e.apply_symm_apply V).trans h.symm))) ≪≫
        liftedUnitIso.{max m u r,v} S V'
  have hgen (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (h : e V' = V) :
      (J V V' h).hom.val.app (op V')
        (sectionAt.{u,r,max m v} R (extendedUnit.{u,r,max m v} R E V) V' V h
          (unitGenerator.{u,r,max m v} R E V)) =
        largeOpenUnitGenerator.{max m v u r,v} S V' := by
    have he : V' = e.symm V := e.injective (h.trans (e.apply_symm_apply V).symm)
    subst V'
    have hD := (E (e.symm V)).generatorComparison
    rw [unitGenerator, sectionAt_cast]
    have heq : e.injective ((e.apply_symm_apply V).trans h.symm) =
        (rfl : e.symm V = e.symm V) := Subsingleton.elim _ _
    dsimp only [J]
    rw [heq]
    simp only [eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp]
    change (liftedUnitIso.{max m u r,v} S (e.symm V)).hom.val.app _
      ((E (e.symm V)).unitComparison.hom.val.app _ _) = _
    rw [hD]
    exact liftedUnitIso_generator S _
  refine ⟨J, hgen, ?_⟩
  intro P V W V' W' hV hW h h'
  apply (cancel_epi (J V V' hV).inv).mp
  apply (P.equiv V' _).injective
  rw [P.evaluation, P.evaluation]
  simp only [Iso.inv_hom_id_assoc] 
  rw [SectionPresentation.inclusion_on_generator]
  have hinv : (J V V' hV).inv.val.app (op V') (largeOpenUnitGenerator.{max m v u r,v} S V') =
      sectionAt.{u,r,max m v} R (extendedUnit.{u,r,max m v} R E V) V' V hV
        (unitGenerator.{u,r,max m v} R E V) := by
    rw [← hgen V V' hV]
    exact iso_inv_apply_hom (J V V' hV) V' _
  change (J W W' hW).hom.val.app (op V')
    ((T.map (unitMap.{u,r,max m v} R E h)).val.app (op V')
      ((J V V' hV).inv.val.app (op V') (largeOpenUnitGenerator.{max m v u r,v} S V'))) = _
  rw [hinv, ← sectionAt_map, unitMap_generator,
    sectionAt_restrict.{u,r,max m v} R _ hV hW (homOfLE h) (homOfLE h'),
    PresheafOfModules.naturality_apply, hgen]

end TransportUnits


theorem prepend_transport :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.prependTransportType.{u,r,m,v} := by
  intro X U I c x i hi
  exact ⟨fun _ _ ↦ rfl, rfl⟩


section TransportStalk

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (OriginalStalkSkyscraperComparison)
open AdvancedHomologicalAlgebra.CechChains (largeOpenUnit largeOpenUnitGenerator largeGerm)

private lemma originalGerm_transport (x : X) (D : OriginalStalkSkyscraperComparison.{m} R x)
    {W : Opens (liftedSpace.{max m u r} X)} {V : Opens X}
    (h : opensEquiv.{max m u r} X W = V)
    (hx : x ∈ V) (hy : X.uliftFunctorObjHomeo.{max m u r} x ∈ W)
    (s : M.val.obj (op V)) :
    (D.stalkIso.inv.app M) (originalModuleGerm.{m} R x M.val V hx s) =
      TopCat.Presheaf.germ ((transport.{m} R).obj M).val.presheaf W _ hy
        (sectionAt.{u,r,m} R M W V h s) := by
  subst V
  rw [← D.stalkGerm M W hy s]
  change ((D.stalkIso.app M).hom ≫ (D.stalkIso.app M).inv) _ = _
  rw [Iso.hom_inv_id]
  rfl

variable {U : Opens X} {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R)

set_option hygiene false in
local notation "Y" => liftedSpace.{max m v u r} X
set_option hygiene false in
local notation "T" => transport.{max m v} R
set_option hygiene false in
local notation "S" => liftedRing.{max m v} R
set_option hygiene false in
local notation "d" => liftCover.{u,max m v,r,v} c
set_option hygiene false in
local notation "e" => opensEquiv.{max m v u r} X
set_option hygiene false in
local notation "B" => fun (p : ℕ) (t : Fin (p + 1) → I) ↦
  largeOpenUnit.{max m v u r,v} S (tupleOpen d t)

set_option maxHeartbeats 600000 in
private lemma transportedTupleGerm
    (J : ∀ (V : Opens X) (V' : Opens Y) (_ : e V' = V),
        (T).obj (extendedUnit.{u,r,max m v} R E V) ≅ largeOpenUnit.{max m v u r,v} S V')
    (L : ∀ p, (T).obj (term.{u,r,m,v} R c E p) ≅
        AdvancedHomologicalAlgebra.CechChains.term S d p)
    (hgen : ∀ (V : Opens X) (V' : Opens Y) (h : e V' = V),
      (J V V' h).hom.val.app (op V')
        (sectionAt.{u,r,max m v} R (extendedUnit.{u,r,max m v} R E V) V' V h
          (unitGenerator.{u,r,max m v} R E V)) = largeOpenUnitGenerator.{max m v u r,v} S V')
    (hL : ∀ p (t : Fin (p + 1) → I),
      (T).map (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t) ≫ (L p).hom =
        (J (tupleOpen c t) (tupleOpen d t) (liftCover_tuple.{u,r,max m v,v} c t)).hom ≫ Sigma.ι (B p) t)
    (x : X) (D : OriginalStalkSkyscraperComparison.{max m v} R x)
    (p : ℕ) (t : SupportedTuple c x p) :
    let y := X.uliftFunctorObjHomeo.{max m v u r} x
    let t' := liftSupportedTuple.{u,r,max m v,v} c x p t
    (stalkFunctor S y).map (L p).hom
        ((D.stalkIso.inv.app (term.{u,r,m,v} R c E p))
          (tupleGerm.{u,r,m,v} R c E x p t)) =
      largeGerm S (AdvancedHomologicalAlgebra.CechChains.term S d p) y
        (tupleOpen d t.val) t'.property
        ((Sigma.ι (B p) t.val).val.app (op (tupleOpen d t.val))
          (largeOpenUnitGenerator.{max m v u r,v} S (tupleOpen d t.val))) := by
  dsimp only
  unfold tupleGerm
  rw [originalGerm_transport R _ x D (liftCover_tuple.{u,r,max m v,v} c t.val) t.property
    (liftSupportedTuple.{u,r,max m v,v} c x p t).property]
  let y := X.uliftFunctorObjHomeo.{max m v u r} x
  let V := tupleOpen c t.val
  let W := tupleOpen d t.val
  let hy := (liftSupportedTuple.{u,r,max m v,v} c x p t).property
  let M := (T).obj (term.{u,r,m,v} R c E p)
  let N := AdvancedHomologicalAlgebra.CechChains.term S d p
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{max m v u r} y).map
      ((PresheafOfModules.toPresheaf (S).obj).map (L p).hom.val)
      (TopCat.Presheaf.germ M.val.presheaf W y hy _) =
    TopCat.Presheaf.germ N.val.presheaf W y hy _
  let s : M.val.obj (op W) :=
    sectionAt.{u,r,max m v} R _ W V (liftCover_tuple.{u,r,max m v,v} c t.val)
      ((Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t.val).val.app (op V)
        (unitGenerator.{u,r,max m v} R E V))
  calc
    _ = TopCat.Presheaf.germ N.val.presheaf W y hy ((L p).hom.val.app (op W) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
        ((PresheafOfModules.toPresheaf (S).obj).map (L p).hom.val) s
    _ = _ := ?_
  refine congrArg (fun z : N.val.obj (op W) ↦ TopCat.Presheaf.germ N.val.presheaf W y hy z) ?_
  dsimp only [s]
  rw [sectionAt_map]
  change ((T).map (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t.val) ≫ (L p).hom).val.app (op W) _ = _
  rw [hL]
  change (Sigma.ι (B p) t.val).val.app (op W) ((J V W _).hom.val.app (op W) _) = _
  rw [hgen]

end TransportStalk


section TransportChain

open AdvancedHomologicalAlgebra.CechChains (largeOpenUnit largeOpenUnitGenerator SectionPresentation)

private instance transportAdditive : (transport.{m} R).Additive where
  map_add := by intros; rfl

set_option maxHeartbeats 900000 in
theorem chain_transport :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.chainTransportType.{u,r,m,v} := by
  intro X R U I c E
  dsimp only
  intro P
  let S := liftedRing.{max m v} R
  let T := transport.{max m v} R
  let d := liftCover.{u,max m v,r,v} c
  obtain ⟨J, hgen, hface⟩ := unit_transport.{u,r,m,v} R E
  let h {p : ℕ} (t : Fin (p + 1) → I) := liftCover_tuple.{u,r,max m v,v} c t
  let C (p : ℕ) := tupleUnits.{u,r,m,v} R c E p
  let B (p : ℕ) (t : Fin (p + 1) → I) := largeOpenUnit.{max m v u r,v} S (tupleOpen d t)
  let j (p : ℕ) (t : Fin (p + 1) → I) : T.obj (C p t) ≅ B p t :=
    J (tupleOpen c t) (tupleOpen d t) (h t)
  let L (p : ℕ) : T.obj (term.{u,r,m,v} R c E p) ≅
      _root_.AdvancedHomologicalAlgebra.CechChains.term S d p :=
    PreservesCoproduct.iso T (C p) ≪≫ Sigma.mapIso (j p)
  have hL (p : ℕ) (t : Fin (p + 1) → I) :
      T.map (Sigma.ι (C p) t) ≫ (L p).hom = (j p t).hom ≫ Sigma.ι (B p) t := by
    have hh : T.map (Sigma.ι (C p) t) ≫ (PreservesCoproduct.iso T (C p)).hom =
        Sigma.ι (fun t ↦ T.obj (C p t)) t := by
      apply (cancel_mono (PreservesCoproduct.iso T (C p)).inv).mp
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom,
        ι_comp_sigmaComparison]
    rw [show (L p).hom = (PreservesCoproduct.iso T (C p)).hom ≫ (Sigma.mapIso (j p)).hom from rfl,
      ← Category.assoc, hh, Sigma.ι_mapIso_hom]
  have ext {p : ℕ} {A : Modules S} {f g : T.obj (term.{u,r,m,v} R c E p) ⟶ A}
      (hfg : ∀ t, T.map (Sigma.ι (C p) t) ≫ f = T.map (Sigma.ι (C p) t) ≫ g) : f = g :=
    (isColimitOfHasCoproductOfPreservesColimit T (C p)).hom_ext
      (fun ⟨t⟩ ↦ hfg t)
  have hF (p q : ℕ) (f : Fin (p + 1) → Fin (q + 1)) :
      T.map (face.{u,r,m,v} R c E f) ≫ (L p).hom = (L q).hom ≫ P.reindex d f := by
    apply ext
    intro t
    have h1 : Sigma.ι (C q) t ≫ face.{u,r,m,v} R c E f =
        unitMap.{u,r,max m v} R E (tupleOpen_reindex_le c f t) ≫ Sigma.ι (C p) (t ∘ f) :=
      Sigma.ι_comp_desc _ _
    have h2 : Sigma.ι (B q) t ≫ P.reindex d f =
        P.inclusion (tupleOpen_reindex_le d f t) ≫ Sigma.ι (B p) (t ∘ f) :=
      Sigma.ι_comp_desc _ _
    rw [← Category.assoc, ← T.map_comp, h1, T.map_comp, Category.assoc, hL,
      ← Category.assoc, hface P (h t) (h (t ∘ f)), Category.assoc]
    rw [← Category.assoc (T.map (Sigma.ι (C q) t)), hL, Category.assoc, h2]
  refine ⟨J, L, hgen, hL, hF, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [boundary, SectionPresentation.boundary, Functor.map_sum, Functor.map_zsmul,
      Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun f ↦ (-1 : ℤ) ^ a.val • f) (hF p (p + 1) a.succAbove)
  · apply ext
    intro t
    have h1 : Sigma.ι (C 0) t ≫ chainAugmentation.{u,r,m,v} R c E =
        unitMap.{u,r,max m v} R E (tupleOpen_le c t) := Sigma.ι_comp_desc _ _
    have h2 : Sigma.ι (B 0) t ≫ P.augmentation d = P.inclusion (tupleOpen_le d t) :=
      Sigma.ι_comp_desc _ _
    rw [← Category.assoc, ← T.map_comp, h1, hface P (h t) _,
      ← Category.assoc (T.map (Sigma.ι (C 0) t)), hL, Category.assoc, h2]
  · intro M p f
    funext t
    have hi : Sigma.ι (B p) t ≫ (L p).inv = (j p t).inv ≫ T.map (Sigma.ι (C p) t) := by
      apply (cancel_mono (L p).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hL, Iso.inv_hom_id_assoc]
    change P.equiv _ _ (Sigma.ι (B p) t ≫ (L p).inv ≫ T.map f) =
      sectionAt.{u,r,max m v} R M _ _ (h t)
        (unitEvaluation.{u,r,max m v} R E _ M (Sigma.ι (C p) t ≫ f))
    rw [P.evaluation, unitEvaluation_apply, sectionAt_map, T.map_comp,
      ← Category.assoc, hi, Category.assoc]
    change (T.map (Sigma.ι (C p) t) ≫ T.map f).val.app _
        ((j p t).inv.val.app _ (largeOpenUnitGenerator.{max m v u r,v} S _)) =
      (T.map (Sigma.ι (C p) t) ≫ T.map f).val.app _ _
    congr 1
    rw [← hgen (tupleOpen c t) (tupleOpen d t) (h t)]
    exact iso_inv_apply_hom (j p t) (tupleOpen d t) _
  · intro x
    let D := originalStalkSkyscraperData.{max m v} R x
    refine ⟨D, ?_⟩
    intro p t
    exact transportedTupleGerm.{u,r,m,v} R c E J L hgen hL x D p t

end TransportChain


section Scalars

theorem coefficient_cochains :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.coefficientCochainsType.{u,r,m,v} := by
  intro X R M U I c
  constructor
  · intro s
    rfl
  · intro p s
    let e := (coefficientCochains.{u,r,m,v} R M c (p + 1)).toAddEquiv
    change e _ = _
    simp only [Cech.differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    rfl

private lemma sectionAt_scalar {V W : Opens X} {V' W' : Opens (liftedSpace.{max m u r} X)}
    (hV : opensEquiv.{max m u r} X V' = V) (hW : opensEquiv.{max m u r} X W' = W)
    (i : V ⟶ W) (i' : V' ⟶ W') (a : sectionRing R W) (s : M.val.obj (op V)) :
    sectionAt.{u,r,m} R M V' V hV (R.obj.map i.op a • s) =
      (liftedRing.{m} R).obj.map i'.op (ringAt.{u,r,m} R W' W hW a) •
        sectionAt.{u,r,m} R M V' V hV s := by
  subst V W
  rfl

theorem cochain_scalars :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.cochainScalarsType.{u,r,m,v} := by
  intro X R M U I c a p s
  funext t
  exact sectionAt_scalar.{u,r,m} R M (liftCover_tuple.{u,r,m,v} c t)
    ((opensEquiv.{max m u r} X).apply_symm_apply U)
    (homOfLE (tupleOpen_le c t)) (homOfLE (tupleOpen_le _ t)) a (s t)

end Scalars

theorem original_chain_exact :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.originalChainExactType.{u,r,m,v} := by
  intro X R U I c E
  let e := opensEquiv.{max m v u r} X
  let S := liftedRing.{max m v} R
  let T := transport.{max m v} R
  let d := liftCover.{u,max m v,r,v} c
  let P := InjectiveCechExactness.presentation.{max m v u r,v} S
  let : Abelian (AmbientSheaves.{max m v} R) := abelianOfEquivalence (transport.{max m v} R)
  have : T.Additive := transportAdditive R
  obtain ⟨hA, hD, _⟩ := original_chain.{u,r,m,v} R c E
  obtain ⟨J, L, _, _, _, hB, hAug, _⟩ := chain_transport.{u,r,m,v} R c E P
  refine ⟨?_, ⟨hA, ?_⟩, fun p ↦ ⟨hD p, ?_⟩⟩
  · apply T.epi_of_epi_map
    have := InjectiveCechExactness.augmentation_epi P d
    have : Epi (T.map (chainAugmentation.{u,r,m,v} R c E) ≫
        (J U _ (e.apply_symm_apply U)).hom) := by
      rw [hAug]
      infer_instance
    exact (epi_comp_iff_of_isIso _ (J U _ (e.apply_symm_apply U)).hom).mp inferInstance
  · let C := ShortComplex.mk (boundary.{u,r,m,v} R c E 0)
      (chainAugmentation.{u,r,m,v} R c E) hA
    let D := ShortComplex.mk (P.boundary d 0) (P.augmentation d)
      (InjectiveCechExactness.boundary_augmentation P d)
    let j : C.map T ≅ D := ShortComplex.isoMk (L 1) (L 0)
      (J U _ (e.apply_symm_apply U)) (hB 0).symm hAug.symm
    exact (C.exact_map_iff_of_faithful T).mp
      ((ShortComplex.exact_iff_of_iso j).mpr (InjectiveCechExactness.augmented_chain_exact P d))
  · let C := ShortComplex.mk (boundary.{u,r,m,v} R c E (p + 1))
      (boundary.{u,r,m,v} R c E p) (hD p)
    let D := ShortComplex.mk (P.boundary d (p + 1)) (P.boundary d p)
      (InjectiveCechExactness.boundary_squared P d p)
    let j : C.map T ≅ D := ShortComplex.isoMk (L (p + 2)) (L (p + 1)) (L p)
      (hB (p + 1)).symm (hB p).symm
    exact (C.exact_map_iff_of_faithful T).mp
      ((ShortComplex.exact_iff_of_iso j).mpr (InjectiveCechExactness.positive_chain_exact P d p))


theorem on_open_chain :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.onOpenChainType.{u,r,m,v} := by
  intro X R U I c
  let Y := (Opens.toTopCat X).obj U
  let S : Y.Sheaf RingCat.{r} := U.sheafRestrict.obj R
  let d := _root_.AdvancedHomologicalAlgebra.CechChains.internalCover c
  let E : OpenUnits.{u,r,max m v} S := openTransportData Y S
  obtain ⟨hA, _, K, b, hb⟩ := original_chain.{u,r,m,v} S d E
  obtain ⟨j, hj⟩ := topUnitComparison.{u,r,max m v} S E
  refine ⟨E, K, b, j, hb, hj, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hA, zero_comp]
  · intro M f
    rw [Category.assoc, original_hom_augmentation, unitEvaluation_apply]
    have h : (j.hom ≫ f).val.app (op ⊤) (unitGenerator.{u,r,max m v} S E ⊤) =
        f.val.app (op ⊤) (ULift.up (1 : sectionRing S (⊤ : Opens Y))) :=
      congrArg (fun s ↦ f.val.app (op ⊤) s) hj
    rw [h]
  · intro x
    have hx : x ∈ (⊤ : Opens Y) := trivial
    have hcover : x ∈ iSup d.opens := d.covers.symm ▸ hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hcover
    obtain ⟨hq, hm⟩ := original_stalk_augmentation.{u,r,m,v} S d E x hx
    obtain ⟨h0, h1, hs⟩ := prepend_contraction.{u,max u r m v,v} d x
      (originalStalkRing.{max m v} S x) i hi
    refine ⟨i, hi, ?_, fun p ↦ (original_tuple_stalk.{u,r,m,v} S d E x p).1, ?_,
      original_stalk_boundary.{u,r,m,v} S d E x, h0, h1, hs⟩
    · let := hq
      infer_instance
    · rw [Functor.map_comp, ← Category.assoc, hm, Category.assoc]

section CarrierComparison

open AdvancedHomologicalAlgebra.CechChains
  (largeOpenUnit largeOpenUnitGenerator liftSheaf liftSheafMap)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Reindex the enlarged category using the site and rings at the native
level. The target can therefore use the lifted-unit representation for
that same site and ring. -/
private def reindexEnlarged :
    AmbientSheaves.{max m v} R ≌ SheafOfModules.{max m v u r} (liftedRing.{m} R) :=
  (sheafScalarEquivalence.{m,u,r,max m v u r} R).trans
    (reindexSheafEquivalence (opensEquiv.{max m u r} X).equivalence (liftRingSheaf.{m} R))

private def reindexLiftIso (A : AmbientSheaves.{m} R) :
    (reindexEnlarged.{u,r,m,v} R).functor.obj ((liftSheafCoefficients.{v} R).obj A) ≅
      liftSheaf.{max m u r,v} (liftedRing.{m} R) ((transport.{m} R).obj A) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ ModuleCat.isoMk (Iso.refl _) (by intros; rfl)) (by intros; rfl))

private def reindexNativeUnit (D : OpenUnits.{u,r,m} R)
    (W : Opens (liftedSpace.{max m u r} X)) :
    (reindexEnlarged.{u,r,m,v} R).functor.obj
        ((liftSheafCoefficients.{v} R).obj (originalExtendedUnitOf.{m} R W (D W).overExtension)) ≅
      largeOpenUnit.{max m u r,v} (liftedRing.{m} R) W :=
  reindexLiftIso.{u,r,m,v} R _ ≪≫
    { hom := liftSheafMap.{max m u r,v} _ (D W).unitComparison.hom
      inv := liftSheafMap.{max m u r,v} _ (D W).unitComparison.inv
      hom_inv_id := by
        ext1
        ext1 T
        ext s
        exact congrArg ULift.up (congrArg (fun f ↦ f.val.app T s.down) (D W).unitComparison.hom_inv_id)
      inv_hom_id := by
        ext1
        ext1 T
        ext s
        exact congrArg ULift.up (congrArg (fun f ↦ f.val.app T s.down) (D W).unitComparison.inv_hom_id) }

private lemma reindexNativeUnit_generator (D : OpenUnits.{u,r,m} R)
    (W : Opens (liftedSpace.{max m u r} X)) :
    (reindexNativeUnit.{u,r,m,v} R D W).hom.val.app (op W)
      (ULift.up (originalExtendedGeneratorOf.{m} R W (D W).overExtension (D W).overAdjunction)) =
      largeOpenUnitGenerator.{max m u r,v} (liftedRing.{m} R) W := by
  exact congrArg ULift.up (D W).generatorComparison

private def reindexNativeEvaluation (D : OpenUnits.{u,r,m} R)
    (W : Opens (liftedSpace.{max m u r} X)) (M : AmbientSheaves.{max m v} R) :
    (((liftSheafCoefficients.{v} R).obj (originalExtendedUnitOf.{m} R W (D W).overExtension)) ⟶ M) ≃
      M.val.obj (op (opensEquiv.{max m u r} X W)) :=
  let Q := reindexEnlarged.{u,r,m,v} R
  let J := reindexNativeUnit.{u,r,m,v} R D W
  let P := InjectiveCechExactness.presentation.{max m u r,v} (liftedRing.{m} R)
  Q.fullyFaithfulFunctor.homEquiv.trans
    ((J.homCongr (Iso.refl _)).trans (P.equiv W (Q.functor.obj M)).toEquiv)

private lemma reindexNativeEvaluation_apply (D : OpenUnits.{u,r,m} R)
    (W : Opens (liftedSpace.{max m u r} X)) (M : AmbientSheaves.{max m v} R)
    (f : ((liftSheafCoefficients.{v} R).obj (originalExtendedUnitOf.{m} R W (D W).overExtension)) ⟶ M) :
    reindexNativeEvaluation.{u,r,m,v} R D W M f =
      f.val.app (op (opensEquiv.{max m u r} X W))
        (ULift.up (originalExtendedGeneratorOf.{m} R W (D W).overExtension (D W).overAdjunction)) := by
  let Q := reindexEnlarged.{u,r,m,v} R
  let J := reindexNativeUnit.{u,r,m,v} R D W
  let P := InjectiveCechExactness.presentation.{max m u r,v} (liftedRing.{m} R)
  change P.equiv W (Q.functor.obj M) (J.inv ≫ Q.functor.map f ≫ 𝟙 _) = _
  rw [Category.comp_id, P.evaluation, ← reindexNativeUnit_generator.{u,r,m,v} R D W]
  let s : (Q.functor.obj ((liftSheafCoefficients.{v} R).obj
      (originalExtendedUnitOf.{m} R W (D W).overExtension))).val.obj (op W) :=
    ULift.up (originalExtendedGeneratorOf.{m} R W (D W).overExtension (D W).overAdjunction)
  have h : J.inv.val.app (op W) (J.hom.val.app (op W) s) = s :=
    congrArg (fun k ↦ k.val.app (op W) s) J.hom_inv_id
  change (Q.functor.map f).val.app (op W) (J.inv.val.app (op W) (J.hom.val.app (op W) s)) = _
  rw [h]
  rfl

private lemma cast_reindexNativeEvaluation_apply (D : OpenUnits.{u,r,m} R)
    (W : Opens (liftedSpace.{max m u r} X)) (V : Opens X) (h : opensEquiv.{max m u r} X W = V)
    (M : AmbientSheaves.{max m v} R)
    (f : ((liftSheafCoefficients.{v} R).obj (originalExtendedUnitOf.{m} R W (D W).overExtension)) ⟶ M) :
    (h ▸ reindexNativeEvaluation.{u,r,m,v} R D W M :
        _ ≃ M.val.obj (op V)) f =
      f.val.app (op V)
        (ULift.up (h ▸ originalExtendedGeneratorOf.{m} R W (D W).overExtension (D W).overAdjunction)) := by
  subst V
  exact reindexNativeEvaluation_apply.{u,r,m,v} R D W M f

private def nativeLiftEvaluation (D : OpenUnits.{u,r,m} R) (V : Opens X)
    (M : AmbientSheaves.{max m v} R) :
    (liftedNativeUnit.{u,r,m,v} R D V ⟶ M) ≃ M.val.obj (op V) :=
  (opensEquiv.{max m u r} X).apply_symm_apply V ▸ reindexNativeEvaluation.{u,r,m,v} R D _ M

private lemma nativeLiftEvaluation_apply (D : OpenUnits.{u,r,m} R) (V : Opens X)
    (M : AmbientSheaves.{max m v} R) (f : liftedNativeUnit.{u,r,m,v} R D V ⟶ M) :
    nativeLiftEvaluation.{u,r,m,v} R D V M f =
      f.val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V) :=
  cast_reindexNativeEvaluation_apply.{u,r,m,v} R D _ V
    ((opensEquiv.{max m u r} X).apply_symm_apply V) M f

theorem unit_carrier_comparison :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.unitCarrierComparisonType.{u,r,m,v} := by
  intro X R D E
  let j (V : Opens X) :
      {i : liftedNativeUnit.{u,r,m,v} R D V ≅ extendedUnit.{u,r,max m v} R E V //
        i.hom.val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V) =
          unitGenerator.{u,r,max m v} R E V} := by
    let A := liftedNativeUnit.{u,r,m,v} R D V
    let B := extendedUnit.{u,r,max m v} R E V
    let a := liftedNativeGenerator.{u,r,m,v} R D V
    let b := unitGenerator.{u,r,max m v} R E V
    let f : A ⟶ B := (nativeLiftEvaluation.{u,r,m,v} R D V B).symm b
    let g : B ⟶ A := (unitEvaluation.{u,r,max m v} R E V A).symm a
    have hf : f.val.app (op V) a = b :=
      (nativeLiftEvaluation_apply.{u,r,m,v} R D V B f).symm.trans
        ((nativeLiftEvaluation.{u,r,m,v} R D V B).apply_symm_apply b)
    have hg : g.val.app (op V) b = a :=
      (unitEvaluation_apply.{u,r,max m v} R E V A g).symm.trans
        ((unitEvaluation.{u,r,max m v} R E V A).apply_symm_apply a)
    refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
    · apply (nativeLiftEvaluation.{u,r,m,v} R D V A).injective
      simp only [nativeLiftEvaluation_apply]
      change g.val.app (op V) (f.val.app (op V) a) = a
      rw [hf, hg]
    · apply (unitEvaluation.{u,r,max m v} R E V B).injective
      simp only [unitEvaluation_apply]
      change f.val.app (op V) (g.val.app (op V) b) = b
      rw [hg, hf]
  let J (V : Opens X) := (j V).val
  have hJ (V : Opens X) :
      (J V).hom.val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V) =
        unitGenerator.{u,r,max m v} R E V := (j V).property
  refine ⟨⟨J, hJ, ?_, ?_⟩⟩
  · intro V W h
    let i := (liftSheafCoefficients.{v} R).map (unitMap.{u,r,m} R D h)
    let a := liftedNativeGenerator.{u,r,m,v} R D V
    have hi : i.val.app (op V) a =
        (liftedNativeUnit.{u,r,m,v} R D W).val.map (homOfLE h).op
          (liftedNativeGenerator.{u,r,m,v} R D W) :=
      congrArg ULift.up (unitMap_generator.{u,r,m} R D h)
    apply (nativeLiftEvaluation.{u,r,m,v} R D V _).injective
    simp only [nativeLiftEvaluation_apply]
    change (J W).hom.val.app (op V) (i.val.app (op V) a) =
      (unitMap.{u,r,max m v} R E h).val.app (op V) ((J V).hom.val.app (op V) a)
    rw [hi, PresheafOfModules.naturality_apply, hJ W, hJ V, unitMap_generator]
  · intro V s
    let i := (liftSheafCoefficients.{v} R).map (unitRightMul.{u,r,m} R D V s)
    let a := liftedNativeGenerator.{u,r,m,v} R D V
    have hi : i.val.app (op V) a = s • a :=
      congrArg ULift.up (unitRightMul_generator.{u,r,m} R D V s)
    apply (nativeLiftEvaluation.{u,r,m,v} R D V _).injective
    simp only [nativeLiftEvaluation_apply]
    change (J V).hom.val.app (op V) (i.val.app (op V) a) =
      (unitRightMul.{u,r,max m v} R E V s).val.app (op V) ((J V).hom.val.app (op V) a)
    rw [hi, ((J V).hom.val.app (op V)).hom.map_smul, hJ V, unitRightMul_generator]

theorem chain_carrier_comparison :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.chainCarrierComparisonType.{u,r,m,v} := by
  intro X R U I c D E
  obtain ⟨J⟩ := unit_carrier_comparison.{u,r,m,v} R D E
  let A := liftedNativeTupleUnits.{u,r,m,v} R c D
  let B := tupleUnits.{u,r,m,v} R c E
  let L (p : ℕ) : liftedNativeTerm.{u,r,m,v} R c D p ≅ term.{u,r,m,v} R c E p :=
    Sigma.mapIso (fun t ↦ J.iso (tupleOpen c t))
  have hL (p : ℕ) (t : Fin (p + 1) → I) :
      Sigma.ι (A p) t ≫ (L p).hom = (J.iso (tupleOpen c t)).hom ≫ Sigma.ι (B p) t :=
    Sigma.ι_mapIso_hom _ _
  have hface {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
      liftedNativeFace.{u,r,m,v} R c D f ≫ (L p).hom = (L q).hom ≫ face.{u,r,m,v} R c E f := by
    apply Sigma.hom_ext
    intro t
    have h₁ : Sigma.ι (A q) t ≫ liftedNativeFace.{u,r,m,v} R c D f =
        (liftSheafCoefficients.{v} R).map (unitMap.{u,r,m} R D (tupleOpen_reindex_le c f t)) ≫
          Sigma.ι (A p) (t ∘ f) := Sigma.ι_comp_desc _ _
    have h₂ : Sigma.ι (B q) t ≫ face.{u,r,m,v} R c E f =
        unitMap.{u,r,max m v} R E (tupleOpen_reindex_le c f t) ≫ Sigma.ι (B p) (t ∘ f) :=
      Sigma.ι_comp_desc _ _
    rw [← Category.assoc, h₁, Category.assoc, hL, ← Category.assoc, J.inclusion, Category.assoc]
    rw [← Category.assoc (Sigma.ι (A q) t), hL, Category.assoc, h₂]
  have hgenInv (V : Opens X) :
      (J.iso V).inv.val.app (op V) (unitGenerator.{u,r,max m v} R E V) =
        liftedNativeGenerator.{u,r,m,v} R D V := by
    rw [← J.generator V]
    exact iso_inv_apply_hom (J.iso V) V _
  refine ⟨J, ⟨L, hL, hface, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p
    simp only [liftedNativeBoundary, boundary, Preadditive.sum_comp, Preadditive.zsmul_comp,
      Preadditive.comp_sum, Preadditive.comp_zsmul, hface]
  · apply Sigma.hom_ext
    intro t
    rw [← Category.assoc, liftedNativeAugmentation, Sigma.ι_comp_desc, J.inclusion,
      ← Category.assoc (Sigma.ι (A 0) t), hL, Category.assoc, chainAugmentation, Sigma.ι_comp_desc]
  · intro p a
    apply Sigma.hom_ext
    intro t
    rw [← Category.assoc, liftedNativeRightMul, Sigma.ι_comp_desc, Category.assoc, hL,
      ← Category.assoc, J.rightMul, Category.assoc,
      ← Category.assoc (Sigma.ι (A p) t), hL, Category.assoc, termRightMul, Sigma.ι_comp_desc]
  · intro M f
    rw [unitEvaluation_apply]
    change f.val.app (op U) _ = f.val.app (op U) ((J.iso U).inv.val.app (op U) _)
    rw [hgenInv]
  · intro M p f
    funext t
    let V := tupleOpen c t
    have hi : Sigma.ι (B p) t ≫ (L p).inv = (J.iso V).inv ≫ Sigma.ι (A p) t := by
      apply (cancel_mono (L p).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hL, V, Iso.inv_hom_id_assoc]
    change (Sigma.ι (A p) t ≫ f).val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V) =
      unitEvaluation.{u,r,max m v} R E V M (Sigma.ι (B p) t ≫ (L p).inv ≫ f)
    rw [unitEvaluation_apply, ← Category.assoc, hi, Category.assoc]
    change _ = (Sigma.ι (A p) t ≫ f).val.app (op V)
      ((J.iso V).inv.val.app (op V) (unitGenerator.{u,r,max m v} R E V))
    rw [hgenInv]
  · intro x p t
    let V := tupleOpen c t.val
    unfold liftedNativeTupleGerm tupleGerm
    change originalModuleStalkMap.{max m v} R x (L p).hom.val _ = _
    rw [originalModuleStalkMap_germ]
    change originalModuleGerm.{max m v} R x _ V t.property
      ((Sigma.ι (A p) t.val ≫ (L p).hom).val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V)) = _
    rw [hL]
    change originalModuleGerm.{max m v} R x _ V t.property
      ((Sigma.ι (B p) t.val).val.app (op V)
        ((J.iso V).hom.val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V))) = _
    rw [J.generator]

private def liftStructureUnitLinear (W : (Opens X)ᵒᵖ) :
    ((liftSheafCoefficients.{v} R).obj (ambientUnit.{u,r,m} R)).val.obj W ≃ₗ[R.obj.obj W]
      (ambientUnit.{u,r,max m v} R).val.obj W where
  toFun s := ULift.up s.down.down
  invFun s := ULift.up (ULift.up s.down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def liftStructureUnitIso :
    (liftSheafCoefficients.{v} R).obj (ambientUnit.{u,r,m} R) ≅ ambientUnit.{u,r,max m v} R :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ (liftStructureUnitLinear.{u,r,m,v} R W).toModuleIso)
      (by intros; rfl))

theorem top_unit_carrier_comparison :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients.topUnitCarrierComparisonType.{u,r,m,v} := by
  intro X R D E J j k
  let F := liftSheafCoefficients.{v} R
  let K := liftStructureUnitIso.{u,r,m,v} R
  have hK : F.map j.val.hom ≫ K.hom = (J.iso ⊤).hom ≫ k.val.hom := by
    let a := liftedNativeGenerator.{u,r,m,v} R D ⊤
    have hj : (F.map j.val.hom).val.app (op ⊤) a =
        ULift.up (ULift.up (1 : sectionRing R (⊤ : Opens X))) :=
      congrArg ULift.up j.property
    apply (nativeLiftEvaluation.{u,r,m,v} R D ⊤ _).injective
    simp only [nativeLiftEvaluation_apply]
    change K.hom.val.app (op ⊤) ((F.map j.val.hom).val.app (op ⊤) a) =
      k.val.hom.val.app (op ⊤) ((J.iso ⊤).hom.val.app (op ⊤) a)
    rw [hj, J.generator, k.property]
    rfl
  refine ⟨K, fun _ _ ↦ rfl, hK, ?_⟩
  intro I c L
  rw [Category.assoc, hK, ← Category.assoc, L.augmentation, Category.assoc]

end CarrierComparison

end AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients
