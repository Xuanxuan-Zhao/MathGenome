import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeBorelAlignment
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

universe u

namespace LinearAlgebraicGroups.Descent.RelativeBorelAlignment

open LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup AffineAlgebraicGroup)
open Specs.RelativeBorelAlignment
open Specs.ParabolicFamilyTransporter
open Specs.Pinning (SplitBorelPair)
open Specs.Fppf (schemeTopology IsFppf)
open Specs.GeometricBorelConjugacy
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
  (conjugates_iff_factorizations)

open private relativePoint relativePoint_natural relativePoint_mul
  familyAmbient_left factors_relative_iff overBase from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {S U : SchemeOver k} {G : GroupScheme k}

private abbrev relativeTest {S : SchemeOver k} (V : Over S) : Over S.left :=
  (Over.iteratedSliceForward S).obj V

private def sliceSourceIso (V : Over S) :
    V.left ≅ (Over.map S.hom).obj (relativeTest V) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (V.hom.left ≫ S.hom) = V.left.hom
    rw [Category.id_comp, Over.w])

private def sectionEquiv (V : Over S) (H : GroupScheme k) :
    (relativeTest V ⟶ (relativeGroup H S).X) ≃* (V.left ⟶ H.X) where
  toEquiv := (((Over.mapPullbackAdj S.hom).homEquiv (relativeTest V) H.X).symm).trans
    { toFun := fun p => (sliceSourceIso V).hom ≫ p
      invFun := fun p => (sliceSourceIso V).inv ≫ p
      left_inv := fun p => (sliceSourceIso V).inv_hom_id_assoc p
      right_inv := fun p => (sliceSourceIso V).hom_inv_id_assoc p }
  map_mul' p q := by
    change (sliceSourceIso V).hom ≫ relativePoint (p * q) =
      ((sliceSourceIso V).hom ≫ relativePoint p) * ((sliceSourceIso V).hom ≫ relativePoint q)
    rw [relativePoint_mul, MonObj.comp_mul]

private theorem sectionEquiv_natural (V : Over S) {X Y : GroupScheme k} (f : X ⟶ Y)
    (p : relativeTest V ⟶ (relativeGroup X S).X) :
    sectionEquiv V Y (p ≫ (Over.pullback S.hom).map f.hom.hom) =
      sectionEquiv V X p ≫ f.hom.hom := by
  change (sliceSourceIso V).hom ≫ relativePoint (p ≫ (Over.pullback S.hom).map f.hom.hom) =
    ((sliceSourceIso V).hom ≫ relativePoint p) ≫ f.hom.hom
  rw [relativePoint_natural, Category.assoc]

private def relativeYonedaIso (S : SchemeOver k) (H : GroupScheme k) :
    (Over.iteratedSliceForward S).op ⋙ yonedaGrp.obj (relativeGroup H S) ≅ relativePoints H S :=
  NatIso.ofComponents (fun V => (sectionEquiv V.unop H).toGrpIso) (by
    intro V W a
    apply GrpCat.ext
    intro x
    apply Over.OverMorphism.ext
    change (𝟙 _ ≫ ((a.unop.left.left ≫ x.left) ≫ pullback.fst H.X.hom S.hom)) =
      a.unop.left.left ≫ (𝟙 _ ≫ (x.left ≫ pullback.fst H.X.hom S.hom))
    simp only [Category.id_comp, Category.assoc])

private abbrev relativeYoneda (S : SchemeOver k) :
    Grp (Over S.left) ⥤ (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.iteratedSliceForward S).op

private def relativeYonedaFullyFaithful (S : SchemeOver k) : (relativeYoneda S).FullyFaithful :=
  yonedaGrpFullyFaithful.comp
    ((S.iteratedSliceEquiv.op.congrLeft (E := GrpCat.{u})).symm.fullyFaithfulFunctor)

private def schemeAut (e : relativePoints G S ≅ relativePoints G S) :
    relativeGroup G S ≅ relativeGroup G S :=
  (relativeYonedaFullyFaithful S).preimageIso
    (relativeYonedaIso S G ≪≫ e ≪≫ (relativeYonedaIso S G).symm)

private theorem schemeAut_apply (e : relativePoints G S ≅ relativePoints G S)
    (V : Over S) (p : relativeTest V ⟶ (relativeGroup G S).X) :
    sectionEquiv V G (p ≫ (schemeAut e).hom.hom.hom) =
      (e.hom.app (op V)).hom (sectionEquiv V G p) := by
  let j := relativeYonedaIso S G
  have h := (relativeYonedaFullyFaithful S).map_preimage (j ≪≫ e ≪≫ j.symm).hom
  let b := (j.app (op V)).groupIsoToMulEquiv
  have eq : p ≫ (schemeAut e).hom.hom.hom =
      b.symm ((e.hom.app (op V)).hom (sectionEquiv V G p)) :=
    congrArg (fun n => (n.app (op V)).hom p) h
  change b (p ≫ (schemeAut e).hom.hom.hom) = _
  rw [eq, b.apply_symm_apply]

private theorem pullback_map_square {X Y : SchemeOver k} (f : X ⟶ Y) :
    IsPullback ((Over.pullback S.hom).map f).left (pullback.fst X.hom S.hom)
      (pullback.fst Y.hom S.hom) f.left := by
  have hXY : IsPullback (pullback.fst X.hom S.hom) (pullback.snd X.hom S.hom)
      (f.left ≫ Y.hom) S.hom := by
    rw [Over.w f]
    exact IsPullback.of_hasPullback _ _
  have h₁ : ((Over.pullback S.hom).map f).left ≫ pullback.fst Y.hom S.hom =
      pullback.fst X.hom S.hom ≫ f.left := pullback.lift_fst _ _ _
  have h₂ := Over.w ((Over.pullback S.hom).map f)
  exact (IsPullback.of_bot (h₂.symm ▸ hXY) h₁.symm (IsPullback.of_hasPullback Y.hom S.hom)).flip

private def imageFamily (B : ClosedSubgroup G) (hB : Smooth B.group.X.hom)
    (e : relativePoints G S ≅ relativePoints G S) : Family G S := by
  let i := (Over.pullback S.hom).mapGrp.map B.inclusion
  let j := (schemeAut e).hom
  have hi : IsClosedImmersion i.hom.hom.left :=
    MorphismProperty.of_isPullback
      (pullback_map_square (S := S) B.inclusion.hom.hom).flip
      B.isClosedImmersion
  letI : IsClosedImmersion i.hom.hom.left := hi
  haveI : IsIso j.hom.hom.left :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso (schemeAut e)).isIso_hom
  exact ⟨relativeGroup B.group S, i ≫ j, IsClosedImmersion.comp _ _,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback B.group.X.hom S.hom) hB⟩

private theorem factors_imageFamily (B : ClosedSubgroup G) (hB : Smooth B.group.X.hom)
    (e : relativePoints G S ≅ relativePoints G S)
    (V : SchemeOver k) (v : V ⟶ S) (z : V ⟶ G.X) :
    (∃ y : V ⟶ (imageFamily B hB e).overField,
      y ≫ (imageFamily B hB e).ambient = lift z v) ↔
      ∃ p : V ⟶ B.group.X,
        (e.hom.app (op (Over.mk v))).hom (p ≫ B.inclusion.hom.hom) = z := by
  let Q := imageFamily B hB e
  let W : Over S := Over.mk v
  let j := Q.inclusion.hom.hom
  let b := sectionEquiv W G
  let c := sectionEquiv W B.group
  let d := sliceSourceIso W
  have hz : relativePoint (b.symm z) = d.inv ≫ z := by
    have hz' : d.hom ≫ relativePoint (b.symm z) = z := b.apply_symm_apply z
    exact (d.inv_hom_id_assoc _).symm.trans (congrArg (d.inv ≫ ·) hz')
  have hv : overBase S (relativeTest W) = d.inv ≫ v := by
    apply Over.OverMorphism.ext
    change v.left = 𝟙 _ ≫ v.left
    simp
  have h := factors_relative_iff j (familyAmbient_left Q) (p := b.symm z)
  rw [hz, hv, ← comp_lift] at h
  have hh : (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z v) ↔
      ∃ y : (Over.map S.hom).obj (relativeTest W) ⟶ Q.overField,
        y ≫ Q.ambient = d.inv ≫ lift z v := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨d.inv ≫ y, by rw [Category.assoc, hy]⟩
    · rintro ⟨y, hy⟩
      exact ⟨d.hom ≫ y, by rw [Category.assoc, hy, d.hom_inv_id_assoc]⟩
  change (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z v) ↔ _
  rw [hh, ← h]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨c p, ?_⟩
    have he := schemeAut_apply e W (p ≫ (Over.pullback S.hom).map B.inclusion.hom.hom)
    rw [show sectionEquiv W G (p ≫ (Over.pullback S.hom).map B.inclusion.hom.hom) =
      c p ≫ B.inclusion.hom.hom from sectionEquiv_natural W B.inclusion p] at he
    have hp' : (p ≫ (Over.pullback S.hom).map B.inclusion.hom.hom) ≫
        (schemeAut e).hom.hom.hom = b.symm z := by
      change p ≫ ((Over.pullback S.hom).map B.inclusion.hom.hom ≫
        (schemeAut e).hom.hom.hom) = b.symm z at hp
      simpa only [Category.assoc] using hp
    rw [hp', b.apply_symm_apply] at he
    exact he.symm
  · rintro ⟨p, hp⟩
    refine ⟨c.symm p, b.injective ?_⟩
    change b (c.symm p ≫ ((Over.pullback S.hom).map B.inclusion.hom.hom ≫
      (schemeAut e).hom.hom.hom)) = b (b.symm z)
    rw [← Category.assoc]
    change sectionEquiv W G _ = _
    rw [schemeAut_apply]
    rw [show sectionEquiv W G (c.symm p ≫ (Over.pullback S.hom).map B.inclusion.hom.hom) =
      c (c.symm p) ≫ B.inclusion.hom.hom from sectionEquiv_natural W B.inclusion (c.symm p)]
    simpa only [c.apply_symm_apply, b.apply_symm_apply] using hp

private def conjugationIso (g : U ⟶ G.X) : relativePoints G U ≅ relativePoints G U where
  hom := conjugationHom g
  inv := conjugationHom g⁻¹
  hom_inv_id := by
    ext V x
    change V.unop.left ⟶ G.X at x
    change MulAut.conj (V.unop.hom ≫ g⁻¹) (MulAut.conj (V.unop.hom ≫ g) x) = x
    simp [GrpObj.comp_inv, MulAut.conj_apply, mul_assoc]
  inv_hom_id := by
    ext V x
    change V.unop.left ⟶ G.X at x
    change MulAut.conj (V.unop.hom ≫ g) (MulAut.conj (V.unop.hom ≫ g⁻¹) x) = x
    simp [GrpObj.comp_inv, MulAut.conj_apply, mul_assoc]

private theorem restrictRange {D : Type (u + 1)} [Category.{u} D]
    {A F : D ⥤ GrpCat.{u}} (i : A ⟶ F) (e : F ≅ F)
    (hi : ∀ V, Function.Injective (i.app V).hom)
    (he : ∀ (V : D) (x : F.obj V), (e.hom.app V).hom x ∈ (i.app V).hom.range ↔
      x ∈ (i.app V).hom.range) :
    ∃ b : A ≅ A, i ≫ e.hom = b.hom ≫ i := by
  let liftAt (V : D) : A.obj V ≃* A.obj V := by
    let j := MonoidHom.ofInjective (hi V)
    let E := (e.app V).groupIsoToMulEquiv
    have h : (i.app V).hom.range.map E.toMonoidHom = (i.app V).hom.range := by
      ext x
      change (∃ y, y ∈ (i.app V).hom.range ∧ E y = x) ↔ _
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (he V y).mpr hy
      · intro hx
        exact ⟨E.symm x, (he V (E.symm x)).mp (by change E (E.symm x) ∈ _; simpa using hx),
          E.apply_symm_apply x⟩
    exact j.trans ((E.subgroupMap _).trans (MulEquiv.subgroupCongr h)) |>.trans j.symm
  have hl (V : D) (x : A.obj V) :
      (i.app V).hom (liftAt V x) = (e.hom.app V).hom ((i.app V).hom x) := by
    change ((MonoidHom.ofInjective (hi V)) (liftAt V x)).val = _
    dsimp only [liftAt, MulEquiv.trans_apply]
    rw [MulEquiv.apply_symm_apply]
    rfl
  let b : A ≅ A := NatIso.ofComponents (fun V => (liftAt V).toGrpIso) (by
    intro V W f
    apply GrpCat.ext
    intro x
    apply hi W
    change (i.app W).hom (liftAt W ((A.map f).hom x)) =
      (i.app W).hom ((A.map f).hom (liftAt V x))
    have h₁ (p : A.obj V) : (i.app W).hom ((A.map f).hom p) =
        (F.map f).hom ((i.app V).hom p) :=
      ConcreteCategory.congr_hom (i.naturality f) p
    have h₂ (p : F.obj V) : (e.hom.app W).hom ((F.map f).hom p) =
        (F.map f).hom ((e.hom.app V).hom p) :=
      ConcreteCategory.congr_hom (e.hom.naturality f) p
    rw [hl, h₁, h₁, hl, h₂])
  exact ⟨b, NatTrans.ext (funext fun V => GrpCat.ext fun x => (hl V x).symm)⟩

private theorem aligned_of_conjugates (P : SplitBorelPair k) (hB : Smooth P.B.group.X.hom)
    (e : relativePoints P.G.val S ≅ relativePoints P.G.val S)
    (a : U ⟶ S) (g : U ⟶ P.G.val.X)
    (h : Conjugates P.B (imageFamily P.B hB e) a g) :
    ∃ b : relativePoints P.B.group U ≅ relativePoints P.B.group U,
      borelInclusion P U ≫ (restrictIso a e).hom ≫ conjugationHom g⁻¹ =
        b.hom ≫ borelInclusion P U := by
  rw [conjugates_iff_factorizations] at h
  let F := restrictIso a e ≪≫ conjugationIso g⁻¹
  apply restrictRange (borelInclusion P U) F
  · intro V
    have : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
    have : Mono P.B.inclusion.hom.hom := Over.mono_of_mono_left _
    exact fun x y hxy => (cancel_mono P.B.inclusion.hom.hom).mp hxy
  · intro V x
    let v := V.unop.hom
    let L := (e.hom.app (op (Over.mk (v ≫ a)))).hom
    have hconj (z : V.unop.left ⟶ P.G.val.X) :
        (∃ p : V.unop.left ⟶ P.B.group.X, L (p ≫ P.B.inclusion.hom.hom) = z) ↔
        ∃ p : V.unop.left ⟶ P.B.group.X,
          MulAut.conj (v ≫ g) (p ≫ P.B.inclusion.hom.hom) = z := by
      rw [← factors_imageFamily P.B hB e]
      exact h _ v z
    change (∃ q : V.unop.left ⟶ P.B.group.X, q ≫ P.B.inclusion.hom.hom =
      MulAut.conj (v ≫ g⁻¹) (L x)) ↔
      ∃ p : V.unop.left ⟶ P.B.group.X, p ≫ P.B.inclusion.hom.hom = x
    have hc (q : V.unop.left ⟶ P.B.group.X) :
        q ≫ P.B.inclusion.hom.hom = MulAut.conj (v ≫ g⁻¹) (L x) ↔
          MulAut.conj (v ≫ g) (q ≫ P.B.inclusion.hom.hom) = L x := by
      rw [GrpObj.comp_inv]
      simp only [MulAut.conj_apply, inv_inv]
      constructor
      · intro hq
        rw [hq]
        group
      · intro hq
        rw [← hq]
        group
    simp only [hc, ← hconj]
    exact exists_congr (fun p =>
      (e.app (op (Over.mk (v ≫ a)))).groupIsoToMulEquiv.injective.eq_iff)

private theorem openCover_mem {S : SchemeOver k} (C : S.left.OpenCover) :
    Sieve.ofArrows (fun i => Over.mk (C.f i ≫ S.hom))
      (fun i => (Over.homMk (C.f i) : Over.mk (C.f i ≫ S.hom) ⟶ S)) ∈ schemeTopology k S := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
    C.mem_grothendieckTopology

private theorem fppf_mem (a : U ⟶ S) (ha : IsFppf a.left) {C : Sieve S} (h : C a) :
    C ∈ schemeTopology k S := by
  obtain ⟨hf, hs, hl⟩ := ha
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.fppfTopology.superset_covering
    ((Sieve.generate_le_iff _ _).mpr (fun _ _ hb => ?_))
    (Precoverage.generate_mem_toGrothendieck a.left.singleton_mem_fppfPrecoverage)
  cases hb
  exact ⟨U, a, 𝟙 U.left, h, by simp⟩

private theorem covering_of_affine_tests (C : Sieve S)
    (h : ∀ (R : TestAlgebra k) (a : (testSpec k).obj (op R) ⟶ S),
      (schemeTopology k).Covers C a) : C ∈ schemeTopology k S := by
  let J := schemeTopology k
  let A := S.left.affineCover
  let V (i : A.I₀) : SchemeOver k := Over.mk (A.f i ≫ S.hom)
  let a (i : A.I₀) : V i ⟶ S := Over.homMk (A.f i)
  refine J.transitive (openCover_mem A) C ?_
  rintro U b ⟨W, c, v, hW, rfl⟩
  cases hW with
  | mk i =>
    obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
      (show IsAffine (V i).left from Scheme.isAffine_affineCover _ _)
    have hc : J.Covers C (e.hom ≫ a i) := h R.unop _
    have ha : J.Covers C (a i) := by
      simpa only [Iso.inv_hom_id_assoc] using J.arrow_stable _ C hc e.inv
    exact J.arrow_stable _ C ha c

open Specs.SchemeDerivedGroup (DerivedSeries IsSolvable)
open LinearAlgebraicGroups.SchemeDerivedGroup (commutatorMap)
open private comp_commutatorMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private extendSubgroup smooth_extend_iff isKBorel_iff_of_isAlgClosed
  smoothConnectedSolvable_extend_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private group_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private transportSubgroup borel_transport
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private compareRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private borel_of_containing_borel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem series_le_sections {H : GroupScheme k} {n : ℕ} (h : DerivedSeries G n H)
    (V : SchemeOver k) :
    ∃ i : H ⟶ G, derivedSeries (V ⟶ G.X) n ≤ ((yonedaGrp.map i).app (op V)).hom.range := by
  induction h with
  | zero =>
    refine ⟨𝟙 _, fun x _ => ⟨x, ?_⟩⟩
    change x ≫ 𝟙 _ = x
    simp
  | @succ n H prev D hD ih =>
    obtain ⟨i, hi⟩ := ih
    refine ⟨D.inclusion ≫ i, ?_⟩
    rw [derivedSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨p, rfl⟩ := hi hx
    obtain ⟨q, rfl⟩ := hi hy
    change V ⟶ H.X at p q
    obtain ⟨f, hf⟩ := hD.2.1
    refine ⟨lift p q ≫ f, ?_⟩
    let m : (V ⟶ H.X) →* (V ⟶ G.X) := ((yonedaGrp.map i).app (op V)).hom
    change m ((lift p q ≫ f) ≫ D.inclusion.hom.hom) = ⁅m p, m q⁆
    change f ≫ D.inclusion.hom.hom = commutatorMap (𝟙 H) (𝟙 H) at hf
    have hcomm : lift p q ≫ commutatorMap (𝟙 H) (𝟙 H) = ⁅p, q⁆ := by
      rw [comp_commutatorMap]
      change ⁅(p ≫ 𝟙 H.X : V ⟶ H.X), (q ≫ 𝟙 H.X : V ⟶ H.X)⁆ = ⁅p, q⁆
      simp only [Category.comp_id]
    rw [Category.assoc, hf, hcomm, map_commutatorElement]

private theorem sections_solvable (h : IsSolvable G) (V : SchemeOver k) :
    Group.IsSolvable (V ⟶ G.X) := by
  obtain ⟨n, H, hH, ⟨e⟩⟩ := h
  obtain ⟨i, hi⟩ := series_le_sections hH V
  refine ⟨n, le_antisymm (fun x hx => ?_) bot_le⟩
  obtain ⟨p, rfl⟩ := hi hx
  have hp : p = 1 := (cancel_mono e.hom.hom.hom).mp
    ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
  rw [hp, map_one, Subgroup.mem_bot]

private theorem borel_parabolic (P : SplitBorelPair k) :
    Specs.BorelProper.IsParabolic P.G P.B := by
  obtain ⟨hc, hB⟩ := P.borel
  exact ⟨P.reductive, (smooth_extend_iff (AlgebraicClosure k) P.B.group.X).mp hB.1.1,
    hc, _, hB, ⟨𝟙 _, Category.id_comp _⟩⟩

private def relativePointEquiv {T : SchemeOver k} (V : Over T.left) (H : GroupScheme k) :
    (V ⟶ (relativeGroup H T).X) ≃* ((Over.map T.hom).obj V ⟶ H.X) where
  toEquiv := ((Over.mapPullbackAdj T.hom).homEquiv V H.X).symm
  map_mul' := relativePoint_mul

/-- Solvability of the geometric Borel gives solvability of its points over
each algebraically closed extension by extending the embedding of the ground field. -/
private theorem borel_extended_sections (B : ClosedSubgroup G) (hB : IsKBorel B)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    Group.IsSolvable (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj B.group).X) := by
  let L := AlgebraicClosure k
  obtain ⟨hc, hgeo⟩ := hB
  let f : L →ₐ[k] K := IsAlgClosed.lift
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom f.toRingHom)
  have hb : b ≫ fieldSpecMap k L = fieldSpecMap k K := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.commutes x
  let X : SchemeOver k := Over.mk (fieldSpecMap k L)
  let Y : SchemeOver k := Over.mk (fieldSpecMap k K)
  let V : Over X.left := Over.mk b
  let W := 𝟙_ (SchemeOver K)
  let j : (Over.map Y.hom).obj W ≅ (Over.map X.hom).obj V :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (b ≫ fieldSpecMap k L) = 𝟙 _ ≫ fieldSpecMap k K
      rw [hb])
  let m := ((yonedaGrp.obj B.group).mapIso j.op).groupIsoToMulEquiv
  let e := (relativePointEquiv (T := Y) W B.group).trans
    (m.symm.trans (relativePointEquiv (T := X) V B.group).symm)
  have : Group.IsSolvable (V ⟶ (relativeGroup B.group X).X) :=
    sections_solvable hgeo.1.2.2 V
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem extended_borel (P : SplitBorelPair k)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    IsBorel (extendSubgroup K P.B) := by
  let A := baseChangedAlgebraicGroup K P.G
  let B := extendSubgroup K P.B
  have hs : Smooth A.val.X.hom := (smooth_extend_iff K P.G.val.X).mpr P.reductive.1
  have hc : ConnectedSpace A.val.X.left := by
    letI := P.reductive.2.1
    letI : GeometricallyConnected A.val.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd P.G.val.X.hom (fieldSpecMap k K)))
    exact GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  have hsB : Smooth B.group.X.hom :=
    (smooth_extend_iff K P.B.group.X).mpr (borel_parabolic P).2.1
  have hcB : ConnectedSpace B.group.X.left := by
    obtain ⟨h, hB⟩ := P.borel
    let D := closedSubgroupAlgebraicGroup P.B
    let a := fieldSpecMap k (AlgebraicClosure k)
    have hsur : Surjective a := ⟨fun x => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ x⟩⟩
    letI : ConnectedSpace (pullback P.B.group.X.hom a : Scheme.{u}) := hB.1.2.1
    letI : ConnectedSpace D.val.X.left :=
      ((MorphismProperty.pullback_fst _ _ hsur).surj.connectedSpace
        (pullback.fst P.B.group.X.hom a).continuous)
    letI := group_geometricallyIrreducible D
    letI : Smooth D.val.X.hom := (borel_parabolic P).2.1
    exact inferInstanceAs (ConnectedSpace (pullback D.val.X.hom (fieldSpecMap k K) : Scheme.{u}))
  have hvB : Specs.SchemeDerivedGroup.IsSolvable B.group := by
    exact (solvable_iff_sections (closedSubgroupAlgebraicGroup (G := A) B) hsB hcB).mpr
      (borel_extended_sections P.B P.borel K)
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient k P.G P.B).1
  have hconn : ConnectedSpace P.G.val.X.left := by
    letI := P.reductive.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton P.G.val.X.hom
  have hproper : IsProper Q.scheme.hom :=
    (BorelProper.quotientProperIff P.G P.reductive.1 hconn P.B
      (borel_parabolic P).2.1 Q).mpr (borel_parabolic P).2.2
  obtain ⟨_, e, _⟩ := HomogeneousQuotient.quotientBaseChange k K Q
  obtain ⟨Q'⟩ := (HomogeneousQuotient.homogeneousQuotient K A B).1
  let j : Q'.scheme ≅ (baseChange k K).obj Q.scheme := compareRepresentatives Q' e
  have hproper' : IsProper Q'.scheme.hom := by
    haveI : IsIso j.hom.left := ((Over.forget _).mapIso j).isIso_hom
    rw [← Over.w j.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper j.hom.left _).mpr
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback Q.scheme.hom (fieldSpecMap k K)) hproper)
  obtain ⟨h, D, hD, hDB⟩ := (BorelProper.quotientProperIff A hs hc B hsB Q').mp hproper'
  exact (isKBorel_iff_of_isAlgClosed A B).mp
    ⟨h, borel_of_containing_borel hD
      ((smoothConnectedSolvable_extend_iff (closedSubgroupAlgebraicGroup (G := A) B)).mpr
        ⟨hsB, hcB, hvB⟩) hDB⟩

private theorem sectionEquiv_precomp {V W : Over S} (f : V ⟶ W)
    (p : relativeTest W ⟶ (relativeGroup G S).X) :
    sectionEquiv V G ((Over.iteratedSliceForward S).map f ≫ p) =
      f.left ≫ sectionEquiv W G p := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((f.left.left ≫ p.left) ≫ pullback.fst G.X.hom S.hom) =
    f.left.left ≫ 𝟙 _ ≫ (p.left ≫ pullback.fst G.X.hom S.hom)
  simp only [Category.id_comp, Category.assoc]

set_option maxHeartbeats 800000 in
private theorem imageFamily_geomType (P : SplitBorelPair k) (hB : Smooth P.B.group.X.hom)
    (e : relativePoints P.G.val S ≅ relativePoints P.G.val S) :
    SameGeometricType P.B (imageFamily P.B hB e) := by
  intro K _ _ _ a
  let U := (testSpec k).obj (op (CommAlgCat.of k K))
  let A := baseChangedAlgebraicGroup K P.G
  let B := extendSubgroup K P.B
  let E : A.val ≅ A.val := schemeAut (restrictIso a e)
  let C := transportSubgroup B E
  have hs : Smooth A.val.X.hom := (smooth_extend_iff K P.G.val.X).mpr P.reductive.1
  have hc : ConnectedSpace A.val.X.left := by
    let := P.reductive.2.1
    let : GeometricallyConnected A.val.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd P.G.val.X.hom (fieldSpecMap k K)))
    exact GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  have hb : IsBorel B := extended_borel P K
  obtain ⟨g₀, j, hj⟩ := GeometricBorelConjugacy.borelsConjugate A hs hc B C hb (borel_transport hb E)
  let O : Over U := Over.mk (𝟙 U)
  let g : U ⟶ P.G.val.X := sectionEquiv O P.G.val g₀
  refine ⟨g, conjugates_iff_factorizations.mpr ?_⟩
  intro V v z
  rw [factors_imageFamily]
  let W : Over U := Over.mk v
  let b := sectionEquiv W P.G.val
  let c := sectionEquiv W P.B.group
  have hv : b (toUnit (relativeTest W) ≫ g₀) = v ≫ g := by
    let f : W ⟶ O := Over.homMk v (by simp [W, O])
    have h : (Over.iteratedSliceForward U).map f = toUnit (relativeTest W) :=
      (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    exact h ▸ sectionEquiv_precomp f g₀
  have he (p : relativeTest W ⟶ B.group.X) :
      b (p ≫ C.inclusion.hom.hom) =
        (e.hom.app (op (Over.mk (v ≫ a)))).hom (c p ≫ P.B.inclusion.hom.hom) := by
    change b (p ≫ ((Over.pullback U.hom).map P.B.inclusion.hom.hom ≫ E.hom.hom.hom)) = _
    rw [← Category.assoc]
    exact (schemeAut_apply (restrictIso a e) W _).trans (congrArg _
      (sectionEquiv_natural W P.B.inclusion p))
  have hconj (p : relativeTest W ⟶ B.group.X) :
      b ((p ≫ j.hom.hom.hom) ≫ C.inclusion.hom.hom) =
        (v ≫ g) * (c p ≫ P.B.inclusion.hom.hom : V ⟶ P.G.val.X) * (v ≫ g)⁻¹ := by
    have hj' : j.hom.hom.hom ≫ C.inclusion.hom.hom = _ := hj
    rw [Category.assoc, hj', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    have h : p ≫ toUnit B.group.X = toUnit (relativeTest W) :=
      (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    have h' : p ≫ toUnit B.group.X ≫ g₀ = toUnit (relativeTest W) ≫ g₀ := by
      rw [← Category.assoc, h]
    simp only [h', map_mul, map_inv, hv]
    exact congrArg (fun x : V ⟶ P.G.val.X => (v ≫ g) * x * (v ≫ g)⁻¹)
      (sectionEquiv_natural W P.B.inclusion p)
  constructor
  · rintro ⟨p, hp⟩
    let q : relativeTest W ⟶ B.group.X := c.symm p ≫ j.inv.hom.hom
    refine ⟨c q, (hconj q).symm.trans ?_⟩
    have hji : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 B.group.X :=
      ((Grp.forget (SchemeOver K)).mapIso j).inv_hom_id
    have hq : q ≫ j.hom.hom.hom = c.symm p := by
      change (c.symm p ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = c.symm p
      rw [Category.assoc, hji]
      exact Category.comp_id (c.symm p)
    calc
      b ((q ≫ j.hom.hom.hom) ≫ C.inclusion.hom.hom) =
          b (c.symm p ≫ C.inclusion.hom.hom) := congrArg (fun t => b (t ≫ C.inclusion.hom.hom)) hq
      _ = (e.hom.app (op (Over.mk (v ≫ a)))).hom (c (c.symm p) ≫ P.B.inclusion.hom.hom) := he _
      _ = z := by rw [c.apply_symm_apply]; exact hp
  · rintro ⟨p, hp⟩
    let q : relativeTest W ⟶ B.group.X := c.symm p
    refine ⟨c (q ≫ j.hom.hom.hom), ?_⟩
    rw [← he, hconj, c.apply_symm_apply]
    exact hp

private theorem conjugates_restricted (P : SplitBorelPair k) (hB : Smooth P.B.group.X.hom)
    (e : relativePoints P.G.val S ≅ relativePoints P.G.val S)
    {T : SchemeOver k} (a : T ⟶ S) (q : U ⟶ T) (g : U ⟶ P.G.val.X)
    (h : Conjugates P.B (imageFamily P.B hB (restrictIso a e)) q g) :
    Conjugates P.B (imageFamily P.B hB e) (q ≫ a) g := by
  rw [conjugates_iff_factorizations] at h ⊢
  intro V v z
  have hz := h V v z
  rw [factors_imageFamily] at hz ⊢
  rw [← Category.assoc]
  exact hz

/-- The relative automorphism is conjugate locally to one preserving the Borel. -/
theorem localBorelAlignment : LocalBorelAlignment.{u} := by
  intro k _ P S e
  have hp := borel_parabolic P
  have hB := hp.2.1
  let Q := imageFamily P.B hB e
  let C : Sieve S :=
    { arrows := fun U a => ∃ g : U ⟶ P.G.val.X, Conjugates P.B Q a g
      downward_closed := fun ⟨g, hg⟩ v =>
        ⟨v ≫ g, LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter.conjugates_pullback hg v⟩ }
  refine ⟨C, ?_, ?_⟩
  · apply covering_of_affine_tests C
    intro R a
    let T := (testSpec k).obj (op R)
    let Q' := imageFamily P.B hB (restrictIso a e)
    obtain ⟨Z, j, _, hrepr, _, hflat, hsurj, hlfp, _, _⟩ :=
      LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter.parabolicTransporter
        P.G P.B hp R Q' (imageFamily_geomType P hB (restrictIso a e))
    let q : Z ⟶ T := j ≫ snd _ _
    let g : Z ⟶ P.G.val.X := j ≫ fst _ _
    have h : Conjugates P.B Q' q g :=
      (hrepr Z q g).mpr ⟨𝟙 _, by
        rw [Category.id_comp]
        apply CartesianMonoidalCategory.hom_ext <;> simp [g, q]⟩
    rw [GrothendieckTopology.covers_iff]
    exact fppf_mem q ⟨hflat, hsurj, hlfp⟩
      (show C (q ≫ a) from ⟨g, conjugates_restricted P hB e a q g h⟩)
  · rintro U a ⟨g, hg⟩
    obtain ⟨b, hb⟩ := aligned_of_conjugates P hB e a g hg
    exact ⟨g⁻¹, b, hb⟩

#print axioms localBorelAlignment

end

end LinearAlgebraicGroups.Descent.RelativeBorelAlignment
