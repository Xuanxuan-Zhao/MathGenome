import Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Affine.HopfFaithfulFlatness
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.HopfAlgebras
import LinearAlgebraicGroups.Flag.RightQuotientSheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

open Specs (GroupScheme AffineAlgebraicGroup IsImageFactorization IsSchemeKernel fppfOver
  schemeFppfSheaf SubgroupSections coordinateMap coordinates)

variable {k : Type u} [Field k]

open private liftHopfQuotient specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem hopfImageIdeal {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    (RingHom.ker a.hom.toAlgHom).IsHopfIdeal k := by
  let I := RingHom.ker a.hom.toAlgHom
  let q := Ideal.Quotient.mkₐ k I
  let b := Ideal.Quotient.liftₐ I a.hom.toAlgHom (fun _ hx ↦ hx)
  have hb : Function.Injective b := RingHom.kerLift_injective a.hom.toAlgHom.toRingHom
  have ht : Function.Injective (TensorProduct.map b.toLinearMap b.toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat _ _ hb hb
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro x hx
    rw [← CoalgHomClass.counit_comp_apply a.hom x, show a.hom x = 0 from hx, map_zero]
  · intro x hx
    change TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul x) = 0
    apply ht
    rw [map_zero, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    change TensorProduct.map a.hom.toAlgHom.toLinearMap a.hom.toAlgHom.toLinearMap
      (Coalgebra.comul x) = 0
    exact (CoalgHomClass.map_comp_comul_apply a.hom x).trans (by
      rw [show a.hom x = 0 from hx, map_zero])
  · intro x hx
    change a.hom (HopfAlgebra.antipode k x) = 0
    have h := DFunLike.congr_fun (hopfSpecMorphism k a).2 x
    change a.hom (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (a.hom x) at h
    rw [h, show a.hom x = 0 from hx, map_zero]

private theorem specImageFactorization {A B : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] (a : A ⟶ B) :
    ∃ (I : AffineAlgebraicGroup k) (p : specGroup B ⟶ I.val) (i : I.val ⟶ specGroup A),
      IsImageFactorization (specGroupMap a) p i := by
  let J := RingHom.ker a.hom.toAlgHom
  let : J.IsHopfIdeal k := hopfImageIdeal a
  let Q := hopfQuotient A J
  let q := hopfQuotientMap A J
  let b := liftHopfQuotient J a (fun _ hx ↦ hx)
  have hb : Function.Injective b.hom.toAlgHom :=
    RingHom.kerLift_injective a.hom.toAlgHom.toRingHom
  have : Algebra.FiniteType k Q := inferInstanceAs (Algebra.FiniteType k (A ⧸ J))
  let I : AffineAlgebraicGroup k := (finiteTypeHopfSpec k).obj (op ⟨Q, inferInstance⟩)
  let b' := CommRingCat.ofHom b.hom.toAlgHom.toRingHom
  have hflat := (flat_and_surjective_SpecMap_iff b').mpr (hopfFaithfulFlatness k b hb)
  have : IsNoetherianRing Q := Algebra.FiniteType.isNoetherianRing k Q
  have hbft : b'.hom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k Q) (by
      rw [show b'.hom.comp (algebraMap k Q) = algebraMap k B from b.hom.toAlgHom.comp_algebraMap]
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation (Spec.map b') :=
    (LocallyOfFinitePresentation.SpecMap_iff b').mpr (RingHom.FinitePresentation.of_finiteType.mp hbft)
  refine ⟨I, specGroupMap b, specGroupMap q, ?_, hflat.1, hflat.2, hfp,
    inferInstanceAs (IsAffineHom (Spec.map b')), (hopfMapClosedImmersion k q).mpr
      Ideal.Quotient.mk_surjective⟩
  change specGroupMap b ≫ specGroupMap q = specGroupMap a
  rw [← specGroupMap_comp q b]
  rfl

private theorem groupPresentation (G : AffineAlgebraicGroup k) :
    ∃ (A : HopfAlgebraCategory k) (_ : Algebra.FiniteType k A), Nonempty (specGroup A ≅ G.val) := by
  let := finiteTypeHopfSpecEquivalence k
  let E := (finiteTypeHopfSpec k).asEquivalence
  let A := (E.inverse.obj G).unop
  exact ⟨A.val, A.property, ⟨(inducedFunctor Subtype.val).mapIso (E.counitIso.app G)⟩⟩

private theorem existsImageFactorization (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val) :
    ∃ (I : AffineAlgebraicGroup k) (p : G.val ⟶ I.val) (i : I.val ⟶ H.val),
      IsImageFactorization f p i := by
  obtain ⟨A, hA, ⟨eG⟩⟩ := groupPresentation G
  obtain ⟨B, hB, ⟨eH⟩⟩ := groupPresentation H
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : B ⟶ A := (ff.preimage (eG.hom ≫ f ≫ eH.inv)).unop
  have ha : specGroupMap a = eG.hom ≫ f ≫ eH.inv :=
    ff.map_preimage _
  obtain ⟨I, p, i, hpi, flat, surj, fp, aff, closed⟩ := specImageFactorization a
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsIso eG.inv.hom.hom.left := F.map_isIso eG.inv
  have : IsIso eH.hom.hom.hom.left := F.map_isIso eH.hom
  refine ⟨I, eG.inv ≫ p, i ≫ eH.hom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc, ← Category.assoc p i, hpi, ha, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · change Flat (eG.inv.hom.hom.left ≫ p.hom.hom.left)
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) flat
  · change Surjective (eG.inv.hom.hom.left ≫ p.hom.hom.left)
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) surj
  · change LocallyOfFinitePresentation (eG.inv.hom.hom.left ≫ p.hom.hom.left)
    have : IsOpenImmersion eG.inv.hom.hom.left := by infer_instance
    exact locallyOfFinitePresentation_comp _ _
  · change IsAffineHom (eG.inv.hom.hom.left ≫ p.hom.hom.left)
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) aff
  · change IsClosedImmersion (i.hom.hom.left ≫ eH.hom.hom.hom.left)
    exact MorphismProperty.comp_mem _ _ _ closed (MorphismProperty.of_isIso _ _)

private theorem closedFactor_kernel {X Y Z : Scheme.{u}} [IsAffine Z]
    (p : X ⟶ Y) (i : Y ⟶ Z) (hp : Function.Injective p.appTop) :
    (p ≫ i).ker = i.ker := by
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hp]

private theorem closedFactor_image {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : X ⟶ Z) (p : X ⟶ Y) (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : p ≫ i = f) (hp : Function.Injective p.appTop) :
    ∃ e : Y ≅ f.image, e.hom ≫ f.imageι = i ∧ p ≫ e.hom = f.toImage := by
  have hk : i.ker = f.ker := h ▸ (closedFactor_kernel p i hp).symm
  let e' : i.image ≅ f.image := eqToIso (congrArg Scheme.IdealSheafData.subscheme hk)
  have compat {A B : Z.IdealSheafData} (hAB : A = B) :
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme hAB)).hom ≫ B.subschemeι =
        A.subschemeι := by
    subst B
    simp
  have he' : e'.hom ≫ f.imageι = i.imageι := compat hk
  let e := asIso i.toImage ≪≫ e'
  have he : e.hom ≫ f.imageι = i := by
    change (i.toImage ≫ e'.hom) ≫ f.imageι = i
    rw [Category.assoc, he', Scheme.Hom.toImage_imageι]
  exact ⟨e, he, (cancel_mono f.imageι).mp (by rw [Category.assoc, he, h,
    Scheme.Hom.toImage_imageι])⟩

private theorem factor_coordinates {X Y Z : SchemeOver k} (p : X ⟶ Y) (i : Y ⟶ Z)
    (hp : Function.Injective p.left.appTop) (hi : Function.Surjective i.left.appTop) :
    ∃ e : coordinates Y ≃ₐ[k] (coordinateMap (p ≫ i)).range,
      ∀ a, (e a : coordinates X) = coordinateMap p a := by
  let a := coordinateMap p
  let b := coordinateMap i
  have hcomp : coordinateMap (p ≫ i) = a.comp b := by
    change ((algΓ (CommRingCat.of k)).map (p ≫ i)).unop.hom = _
    rw [Functor.map_comp]
    rfl
  have h : a.range = (coordinateMap (p ≫ i)).range := by
    rw [hcomp]
    ext x
    change (∃ y, a y = x) ↔ (∃ z, a (b z) = x)
    exact ⟨fun ⟨y, hy⟩ ↦ by obtain ⟨z, rfl⟩ := hi y; exact ⟨z, hy⟩,
      fun ⟨z, hz⟩ ↦ ⟨b z, hz⟩⟩
  refine ⟨(AlgEquiv.ofInjective a hp).trans (Subalgebra.equivOfEq _ _ h), ?_⟩
  intro x
  exact AlgEquiv.ofInjective_apply a hp x

theorem schemeImageFactorization : Specs.SchemeImageFactorization.{u} := by
  intro k _ G H f
  obtain ⟨I, p, i, hp⟩ := existsImageFactorization G H f
  have ⟨hc, hflat, hsurj, _, _, hclosed⟩ := hp
  have := G.property.1
  have := H.property.1
  have := I.property.1
  have := hclosed
  have hcomp : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom.left) hc
  have hinj : Function.Injective p.hom.hom.left.appTop :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨hflat, hsurj⟩).injective
  refine ⟨I, p, i, hp, closedFactor_image _ _ _ hcomp hinj, ?_⟩
  have he := factor_coordinates p.hom.hom i.hom.hom hinj
    (IsClosedImmersion.isAffine_surjective_of_isAffine i.hom.hom.left).2
  rwa [show p.hom.hom ≫ i.hom.hom = f.hom.hom from
    congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom) hc] at he

private theorem isMonHom_of_comp_closed {I J H : GroupScheme k} (g : I.X ⟶ J.X)
    (i : I ⟶ H) (j : J ⟶ H) [IsClosedImmersion j.hom.hom.left]
    (h : g ≫ j.hom.hom = i.hom.hom) : IsMonHom g := by
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  constructor
  · apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, h, IsMonHom.mul_hom (f := i.hom.hom), Category.assoc,
      IsMonHom.mul_hom (f := j.hom.hom), ← Category.assoc, tensorHom_comp_tensorHom, h]

theorem schemeImageUniqueness : Specs.SchemeImageUniqueness.{u} := by
  intro k _ G H f I J p i q j hp hq hpf hps hi hqf hqs hj
  have := G.property.1
  have := H.property.1
  have : IsAffine I.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : IsAffine J.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have hp' : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom.left) hp
  have hq' : q.hom.hom.left ≫ j.hom.hom.left = f.hom.hom.left :=
    congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom.left) hq
  obtain ⟨eI, heI, _⟩ := closedFactor_image _ _ _ hp'
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨hpf, hps⟩).injective
  obtain ⟨eJ, heJ, _⟩ := closedFactor_image _ _ _ hq'
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨hqf, hqs⟩).injective
  let e := eI ≪≫ eJ.symm
  have he : e.hom ≫ j.hom.hom.left = i.hom.hom.left := by
    change (eI.hom ≫ eJ.inv) ≫ j.hom.hom.left = i.hom.hom.left
    rw [← heJ, Category.assoc, Iso.inv_hom_id_assoc, heI]
  let e' : I.X ≅ J.X := Over.isoMk e (by rw [← Over.w j.hom.hom, ← Category.assoc, he, Over.w])
  have he' : e'.hom ≫ j.hom.hom = i.hom.hom := Over.OverMorphism.ext he
  have := isMonHom_of_comp_closed e'.hom i j he'
  let e'' : I ≅ J := Grp.mkIso' e'
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hj' : e''.hom ≫ j = i := Grp.hom_ext _ _ he'
  refine ⟨e'', ⟨?_, hj'⟩, ?_⟩
  · apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    have heq : (p ≫ e''.hom) ≫ j = q ≫ j := by rw [Category.assoc, hj', hp, hq]
    exact congrArg (fun a : G.val ⟶ H.val ↦ a.hom.hom) heq
  · intro e₀ he₀
    apply Iso.ext
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    exact congrArg (fun a : I ⟶ H.val ↦ a.hom.hom) (he₀.2.trans hj'.symm)

private theorem schemeKernel_exists {G H : GroupScheme k}
    [IsAffine H.X.left] (f : G ⟶ H) :
    ∃ N : ClosedSubgroup G, IsSchemeKernel f N := by
  let C := SchemeOver k
  let e : Grp.trivial C ⟶ H := default
  have he : e.hom.hom = η[H.X] := by
    change (default : Mon.trivial C ⟶ H.toMon).hom = _
    rfl
  have hi : IsClosedImmersion (η[H.X]).left := by
    have ha : IsAffine (𝟙_ C).left := inferInstanceAs
      (IsAffine (Spec (CommRingCat.of k)))
    apply IsClosedImmersion.of_surjective_of_isAffine
    have hw : (η[H.X]).left ≫ H.X.hom = 𝟙 _ := (η[H.X]).w
    have happ := congrArg Scheme.Hom.appTop hw
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at happ
    exact Function.RightInverse.surjective
      (fun x ↦ ConcreteCategory.congr_hom happ x)
  let U := Grp.forget C
  have hp := U.map_isPullback (IsPullback.of_hasPullback f e)
  change IsPullback (pullback.fst f e).hom.hom (pullback.snd f e).hom.hom f.hom.hom e.hom.hom at hp
  rw [he] at hp
  have hleft := (Over.forget (Spec (CommRingCat.of k))).map_isPullback hp
  have hc : IsClosedImmersion (pullback.fst f e).hom.hom.left :=
    MorphismProperty.of_isPullback hleft.flip hi
  let N : ClosedSubgroup G := ⟨_, pullback.fst f e, hc⟩
  have hs : (pullback.snd f e).hom.hom = toUnit N.group.X :=
    (isTerminalTensorUnit (C := C)).hom_ext _ _
  refine ⟨N, ?_⟩
  change IsPullback _ (toUnit N.group.X) _ _
  rwa [← hs]

private theorem schemeKernel_sections {G H : GroupScheme k} {f : G ⟶ H}
    {N : ClosedSubgroup G} (h : IsSchemeKernel f N)
    {T : SchemeOver k} (g : T ⟶ G.X) :
    g ∈ SubgroupSections N T ↔ g ≫ f.hom.hom = 1 := by
  change (∃ n : T ⟶ N.group.X, n ≫ N.inclusion.hom.hom = g) ↔
    g ≫ f.hom.hom = toUnit T ≫ η[H.X]
  constructor
  · rintro ⟨n, rfl⟩
    rw [Category.assoc, h.w, ← Category.assoc, comp_toUnit]
  · intro hg
    exact ⟨h.lift g (toUnit T) hg, h.lift_fst _ _ _⟩

private theorem sameImage_iff {G H I : GroupScheme k} {f : G ⟶ H}
    {p : G ⟶ I} {i : I ⟶ H} (hpi : p ≫ i = f)
    [IsClosedImmersion i.hom.hom.left] {N : ClosedSubgroup G} (hN : IsSchemeKernel f N)
    {T : SchemeOver k} (g g' : T ⟶ G.X) :
    g ≫ p.hom.hom = g' ≫ p.hom.hom ↔ g⁻¹ * g' ∈ SubgroupSections N T := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hc : p.hom.hom ≫ i.hom.hom = f.hom.hom :=
    congrArg (fun a : G ⟶ H ↦ a.hom.hom) hpi
  rw [schemeKernel_sections hN]
  let F : (T ⟶ G.X) →* (T ⟶ H.X) := ((yonedaGrp.map f).app (op T)).hom
  change g ≫ p.hom.hom = g' ≫ p.hom.hom ↔ F (g⁻¹ * g') = 1
  rw [map_mul, map_inv, inv_mul_eq_one]
  change g ≫ p.hom.hom = g' ≫ p.hom.hom ↔ g ≫ f.hom.hom = g' ≫ f.hom.hom
  constructor
  · intro h
    rw [← hc, ← Category.assoc, ← Category.assoc, h]
  · intro h
    apply (cancel_mono i.hom.hom).mp
    simpa only [Category.assoc, hc] using h

private theorem fppfYoneda_locallySurjective {X Y : SchemeOver k} (p : X ⟶ Y)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left] :
    Presheaf.IsLocallySurjective (fppfOver k) ((fppfOver k).uliftYoneda.map p).hom where
  imageSieve_mem {T} t := by
    let a : T ⟶ Y := t.down
    let r₀ := pullback.fst a.left p.left
    let s₀ := pullback.snd a.left p.left
    let V : SchemeOver k := Over.mk (r₀ ≫ T.hom)
    let r : V ⟶ T := Over.homMk r₀
    let s : V ⟶ X := Over.homMk s₀ (by
      change s₀ ≫ X.hom = r₀ ≫ T.hom
      rw [← Over.w p, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a])
    apply (fppfOver k).superset_covering (S := Sieve.ofArrows (fun _ : PUnit.{1} ↦ V) (fun _ ↦ r))
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro U _ ⟨⟩
      exact ⟨⟨s⟩, congrArg ULift.up (Over.OverMorphism.ext pullback.condition.symm)⟩
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows, Sieve.ofArrows,
        Presieve.ofArrows_pUnit]
      exact Precoverage.generate_mem_toGrothendieck r₀.singleton_mem_fppfPrecoverage

private def rightCosetToImage {G H I : GroupScheme k} {f : G ⟶ H}
    {p : G ⟶ I} {i : I ⟶ H} (hpi : p ≫ i = f)
    [IsClosedImmersion i.hom.hom.left] {N : ClosedSubgroup G} (hN : IsSchemeKernel f N) :
    Specs.rightCosetPresheaf N ⟶ (schemeFppfSheaf I.X).obj where
  app T := ↾fun x ↦ Quotient.lift
    (fun g : T.unop ⟶ G.X ↦ ULift.up (g ≫ p.hom.hom))
    (fun g g' hg ↦ congrArg ULift.up
      ((sameImage_iff hpi hN g g').mpr (QuotientGroup.leftRel_apply.mp hg))) x.down
  naturality T U b := by
    ext ⟨x⟩
    induction x using QuotientGroup.induction_on with
    | H g =>
      change ULift.up ((b.unop ≫ g) ≫ p.hom.hom) =
        ULift.up (b.unop ≫ g ≫ p.hom.hom)
      rw [Category.assoc]

private theorem quotientRepresentsImage {G H I : GroupScheme k} {f : G ⟶ H}
    {p : G ⟶ I} {i : I ⟶ H} (hp : IsImageFactorization f p i)
    {N : ClosedSubgroup G} (hN : IsSchemeKernel f N) :
    ∃ e : rightQuotientSheaf N ≅ schemeFppfSheaf I.X,
      rightQuotientProjection N ≫ e.hom = (fppfOver k).uliftYoneda.map p.hom.hom := by
  obtain ⟨hpi, hflat, hsurj, hfp, _, hclosed⟩ := hp
  let J := fppfOver k
  let C := Specs.rightCosetPresheaf N
  let Y := schemeFppfSheaf I.X
  let c : C ⟶ Y.obj := rightCosetToImage hpi hN
  have hc : Specs.rightCosetProjection N ≫ c = (J.uliftYoneda.map p.hom.hom).hom := rfl
  have hinj : Presheaf.IsLocallyInjective J c := by
    apply Presheaf.isLocallyInjective_of_injective
    rintro T ⟨x⟩ ⟨y⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    intro h
    exact congrArg ULift.up (QuotientGroup.eq.mpr
      ((sameImage_iff hpi hN g g').mp (congrArg ULift.down h)))
  have hsurj' := fppfYoneda_locallySurjective p.hom.hom
  have hloc : Presheaf.IsLocallySurjective J c :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hc
  let e : rightQuotientSheaf N ⟶ Y := ⟨sheafifyLift J c Y.property⟩
  let unit : C ⟶ (rightQuotientSheaf N).obj := toSheafify J C
  have he : unit ≫ e.hom = c := toSheafify_sheafifyLift J c Y.property
  have hq : Presheaf.IsLocallySurjective J
      (Specs.rightCosetProjection N ≫ unit) := rightQuotientLocalLifts N
  have hunit : Presheaf.IsLocallySurjective J unit :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J (Specs.rightCosetProjection N) unit
  have hei : Presheaf.IsLocallyInjective J e.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J (f₁ := unit) c he
  have hes : Presheaf.IsLocallySurjective J e.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J he
  have : IsIso e := (Sheaf.isLocallyBijective_iff_isIso e).mp ⟨hei, hes⟩
  refine ⟨asIso e, ?_⟩
  apply Sheaf.hom_ext
  change (Specs.rightCosetProjection N ≫ unit) ≫ e.hom = _
  rw [Category.assoc, he, hc]

theorem schemeImageQuotient : Specs.SchemeImageQuotient.{u} := by
  intro k _ G H f
  have := H.property.1
  obtain ⟨I, p, i, hp, hi, _⟩ := schemeImageFactorization G H f
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  exact ⟨I, p, i, N, hp, hi, hN, quotientRepresentsImage hp hN⟩

end

end LinearAlgebraicGroups
