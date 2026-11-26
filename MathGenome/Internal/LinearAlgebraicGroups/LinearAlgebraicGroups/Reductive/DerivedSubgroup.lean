import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.DerivedSubgroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

universe u

namespace LinearAlgebraicGroups.Reductive.DerivedSubgroup

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Specs.SchemeDerivedGroup (commutatorMap IsDerivedSubgroup IsNormalClosure FactorsThrough
  IsCommutative RepresentsQuotient)
open Specs.FiniteWordClosure (power wordDomain evaluate)
open private affine_tensor affine_power evaluate_precomp ker_comp_eq liftClosed liftClosed_fac
  isMonHom_of_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private comp_commutatorMap comp_commutatorMap_projections commutatorMap_conjugationStable
  power_geometry closedSubgroupAlgebraic locallySurjective_pair_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k : Type u} [Field k]

/-- The morphism obtained by multiplying the commutators of successive pairs. -/
abbrev commutatorProduct : Specs.Reductive.DerivedSubgroup.CommutatorProductType.{u} :=
  @Specs.Reductive.DerivedSubgroup.commutatorProduct

private abbrev commutatorDomain (G : GroupScheme k) := G.X ⊗ G.X
private abbrev commutator (G : GroupScheme k) := commutatorMap (𝟙 G) (𝟙 G)

private theorem commutator_swap (G : GroupScheme k) :
    (β_ G.X G.X).hom ≫ commutator G = (commutator G)⁻¹ := by
  rw [comp_commutatorMap_projections (𝟙 G) (𝟙 G), braiding_hom_fst_assoc, braiding_hom_snd_assoc]
  exact (commutatorElement_inv (fst G.X G.X ≫ (𝟙 G : G ⟶ G).hom.hom)
    (snd G.X G.X ≫ (𝟙 G : G ⟶ G).hom.hom)).symm

/-- Reversing the inputs in every even slot replaces the corresponding inverse
commutators by ordinary commutators. -/
private def reverseEvenPairs (G : GroupScheme k) :
    (n : ℕ) → wordDomain (commutatorDomain G) n ≅ wordDomain (commutatorDomain G) n
  | 0 => Iso.refl _
  | n + 1 =>
    Iso.refl (commutatorDomain G) ⊗ᵢ ((β_ G.X G.X) ⊗ᵢ reverseEvenPairs G n)

private theorem evaluate_commutator (G : GroupScheme k) (n : ℕ) :
    evaluate (commutator G) n (𝟙 _) =
      (reverseEvenPairs G n).hom ≫ commutatorProduct G (2 * n) := by
  induction n with
  | zero => simp [evaluate, reverseEvenPairs, commutatorProduct,
      Specs.Reductive.DerivedSubgroup.commutatorProduct]
  | succ n ih =>
    let X := commutatorDomain G
    let W := wordDomain X n
    let f := commutator G
    let b := (β_ G.X G.X).hom
    let e := (reverseEvenPairs G n).hom
    let r := snd X (X ⊗ W) ≫ snd X W
    let a := 𝟙 X ⊗ₘ (b ⊗ₘ e)
    have htail : evaluate f n r = r ≫ (e ≫ commutatorProduct G (2 * n)) := by
      have hi : evaluate f n (𝟙 W) = e ≫ commutatorProduct G (2 * n) := ih
      simpa only [Category.comp_id, hi] using evaluate_precomp f r n (𝟙 W)
    have hfst : a ≫ fst X (X ⊗ W) = fst X (X ⊗ W) :=
      (tensorHom_fst (𝟙 X) (b ⊗ₘ e)).trans (Category.comp_id _)
    have hsnd : a ≫ snd X (X ⊗ W) = snd X (X ⊗ W) ≫ (b ⊗ₘ e) :=
      tensorHom_snd (𝟙 X) (b ⊗ₘ e)
    have hfst' : (b ⊗ₘ e) ≫ fst X W = fst X W ≫ b := tensorHom_fst b e
    have hsnd' : (b ⊗ₘ e) ≫ snd X W = snd X W ≫ e := tensorHom_snd b e
    have hb : b ≫ f = f⁻¹ := commutator_swap G
    change ((fst X (X ⊗ W) ≫ f) *
        ((snd X (X ⊗ W) ≫ fst X W) ≫ f)⁻¹) * evaluate f n r =
      a ≫ ((fst X (X ⊗ W) ≫ f) *
        (snd X (X ⊗ W) ≫ ((fst X W ≫ f) * (snd X W ≫ commutatorProduct G (2 * n)))))
    simp only [htail, r, MonObj.comp_mul, Category.assoc, reassoc_of% hfst, reassoc_of% hsnd,
      reassoc_of% hfst', reassoc_of% hsnd', hb, ← GrpObj.comp_inv, mul_assoc]

private theorem exists_dominant_commutatorProduct (G : AffineAlgebraicGroup k)
    (D : ClosedSubgroup G.val) (hd : IsDerivedSubgroup D)
    (hs : Smooth G.val.X.hom) (hc : GeometricallyConnected G.val.X.hom) :
    ∃ (n : ℕ) (w : power (commutatorDomain G.val) n ⟶ D.group.X),
      0 < n ∧ IsAffine (power (commutatorDomain G.val) n).left ∧
      Smooth (power (commutatorDomain G.val) n).hom ∧
      GeometricallyIrreducible (power (commutatorDomain G.val) n).hom ∧
      IsSchemeTheoreticallyDominant w.left ∧
      w ≫ D.inclusion.hom.hom = commutatorProduct G.val n := by
  let X := commutatorDomain G.val
  let f := commutator G.val
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx₀ : x₀ ≫ f = 1 := by
    change lift 1 1 ≫ commutatorMap (𝟙 G.val) (𝟙 G.val) = 1
    rw [comp_commutatorMap]
    simp
  have hn : IsNormalSubgroup (𝟙 G.val) :=
    ⟨subgroupConjugation (𝟙 G.val), by simp⟩
  have haG := G.property.1
  have hcG := @GeometricallyConnected.connectedSpace_of_subsingleton _ _ G.val.X.hom hc
    inferInstance inferInstance
  have hiG := geometricallyIrreducible_of_connected G
  have ha : IsAffine X.left := affine_tensor
  obtain ⟨hsX, hiX⟩ := smooth_geometricallyIrreducible_tensor G.val.X G.val.X
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨hs', hi'⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  obtain ⟨N, n, v, hnpos, hN, hv, hf, hmin, hword⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x₀ ha inferInstance inferInstance
      hx₀ hpow (commutatorMap_conjugationStable (𝟙 G.val) hn)
  have hN' : IsNormalClosure f N := ⟨hN, hf, fun E _ hE ↦ hmin E hE⟩
  obtain ⟨e, he⟩ := SchemeDerivedGroup.normalClosure_unique hN' hd
  let a := reverseEvenPairs G.val n
  let F := Grp.forget (SchemeOver k)
  let U := Over.forget (Spec (CommRingCat.of k))
  let w := a.inv ≫ v ≫ F.map e.hom
  have hw : IsSchemeTheoreticallyDominant w.left := by
    have ha' : IsIso a.inv.left := U.map_isIso a.inv
    have he' : IsIso (F.map e.hom).left := (F ⋙ U).map_isIso e.hom
    change IsSchemeTheoreticallyDominant (a.inv.left ≫ v.left ≫ (F.map e.hom).left)
    infer_instance
  obtain ⟨hsW, hiW⟩ := power_geometry X (2 * n)
  refine ⟨2 * n, w, by omega, affine_power (X := X) (2 * n), hsW, hiW, hw, ?_⟩
  have hword' : v ≫ N.inclusion.hom.hom = evaluate f n (𝟙 _) := by
    simpa only [Category.id_comp] using hword _ (𝟙 _)
  have he' : F.map e.hom ≫ D.inclusion.hom.hom = N.inclusion.hom.hom := congrArg F.map he
  change (a.inv ≫ v ≫ F.map e.hom) ≫ D.inclusion.hom.hom = _
  rw [Category.assoc, Category.assoc, he', hword', evaluate_commutator]
  exact a.inv_hom_id_assoc _

private theorem baseChange_isPullback (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (p : X ⟶ Y) :
    IsPullback ((baseChange k K).map p).left (pullback.fst X.hom (fieldSpecMap k K))
      (pullback.fst Y.hom (fieldSpecMap k K)) p.left := by
  let g := fieldSpecMap k K
  let b := ((baseChange k K).map p).left
  have hX : IsPullback (pullback.fst X.hom g) (pullback.snd X.hom g) (p.left ≫ Y.hom) g := by
    rw [Over.w p]
    exact IsPullback.of_hasPullback _ _
  have h₁ : b ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ p.left :=
    pullback.lift_fst _ _ _
  have h₂ : b ≫ pullback.snd Y.hom g = pullback.snd X.hom g :=
    pullback.lift_snd _ _ _
  exact (IsPullback.of_bot (h₂.symm ▸ hX) h₁.symm (IsPullback.of_hasPullback _ _)).flip

private theorem dominant_baseChange (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (p : X ⟶ Y) [QuasiCompact p.left]
    [IsSchemeTheoreticallyDominant p.left] :
    IsSchemeTheoreticallyDominant ((baseChange k K).map p).left := by
  have : Flat (pullback.fst Y.hom (fieldSpecMap k K)) := inferInstance
  exact IsSchemeTheoreticallyDominant.of_isPullback (baseChange_isPullback K p).flip

private theorem kernel_baseChange_closed (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (i : X ⟶ Y) [IsClosedImmersion i.left] :
    ((baseChange k K).map i).left.ker =
      i.left.ker.comap (pullback.fst Y.hom (fieldSpecMap k K)) := by
  let e := (baseChange_isPullback K i).isoPullback
  rw [← (baseChange_isPullback K i).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The defining ideal equals the kernel of the coordinate map of a finite
commutator product, and flat scalar extension preserves that image. -/
theorem finiteCommutatorProductImage : Specs.Reductive.DerivedSubgroup.FiniteCommutatorProductImage.{u} := by
  intro k _ G D hd hs hg
  obtain ⟨n, w, hn, ha, _, _, hw, he⟩ := exists_dominant_commutatorProduct G D hd hs hg
  have haD := (closedSubgroupAlgebraic G D).property.1
  have hq : QuasiCompact w.left := inferInstance
  have hi : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosedImmersion
  change w ≫ D.inclusion.hom.hom = Specs.Reductive.DerivedSubgroup.commutatorProduct G.val n at he
  refine ⟨n, w, hn, hw, he, ?_, ?_⟩
  · rw [← he]
    change RingHom.ker (w.left ≫ D.inclusion.hom.hom.left).appTop.hom =
      RingHom.ker D.inclusion.hom.hom.left.appTop.hom
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.ker_comp_of_injective _ (w.left.app_injective ⊤)]
  · intro K _ _
    let F := baseChange k K
    have := dominant_baseChange K w
    rw [← he, ker_comp_eq w, F.map_comp, ker_comp_eq (F.map w), kernel_baseChange_closed]

/-- The scheme-theoretic derived subgroup of a smooth geometrically connected
affine algebraic group is smooth and geometrically connected. -/
theorem derivedSubgroupGeometry : Specs.Reductive.DerivedSubgroup.DerivedSubgroupGeometry.{u} := by
  intro k _ G D hd hs hg
  obtain ⟨n, w, _, ha, hsW, hiW, hw, _⟩ := exists_dominant_commutatorProduct G D hd hs hg
  have haD := (closedSubgroupAlgebraic G D).property.1
  have hft := (closedSubgroupAlgebraic G D).property.2.1
  have hq : QuasiCompact w.left := inferInstance
  have hred : GeometricallyReduced D.group.X.hom := by
    constructor
    apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := IsReduced) (f := D.group.X.hom)).mpr
    intro K _ _
    let p := ((baseChange k K).map w).left
    have : IsSchemeTheoreticallyDominant p := dominant_baseChange K w
    have : QuasiCompact p :=
      MorphismProperty.of_isPullback (baseChange_isPullback K w).flip hq
    have : Smooth (pullback.snd (power (commutatorDomain G.val) n).hom (fieldSpecMap k K)) :=
      inferInstance
    have : IsReduced ((baseChange k K).obj (power (commutatorDomain G.val) n)).left :=
      isReduced_of_smooth_over_field
        (pullback.snd (power (commutatorDomain G.val) n).hom (fieldSpecMap k K))
    exact IsSchemeTheoreticallyDominant.isReduced p
  have hconn : GeometricallyConnected D.group.X.hom := by
    constructor
    apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := fun X : Scheme.{u} ↦ ConnectedSpace X) (f := D.group.X.hom)).mpr
    intro K _ _
    let p := ((baseChange k K).map w).left
    have : IsSchemeTheoreticallyDominant p := dominant_baseChange K w
    have : QuasiCompact p :=
      MorphismProperty.of_isPullback (baseChange_isPullback K w).flip hq
    let W := (baseChange k K).obj (power (commutatorDomain G.val) n)
    have hi : IrreducibleSpace W.left :=
      pullback_of_geometrically hiW.geometrically_irreducibleSpace K (fieldSpecMap k K)
    have hpre := p.denseRange.preconnectedSpace p.continuous
    exact @ConnectedSpace.mk _ _ hpre (Nonempty.map p (inferInstance : Nonempty W.left))
  exact ⟨((groupSmoothnessCriteria k D.group).1).mpr hred, hconn⟩

private theorem baseChange_commutator (K : Type u) [Field K] [Algebra k K]
    (G : GroupScheme k) :
    let F := baseChange k K
    F.map (commutator G) =
      CartesianMonoidalCategory.prodComparison F G.X G.X ≫
        commutator ((groupBaseChange k K).obj G) := by
  let F := baseChange k K
  let H := (groupBaseChange k K).obj G
  let p := CartesianMonoidalCategory.prodComparison F G.X G.X
  change F.map (commutator G) = p ≫ commutator H
  rw [comp_commutatorMap_projections (𝟙 H) (𝟙 H)]
  have hf : p ≫ fst H.X H.X ≫ (𝟙 H : H ⟶ H).hom.hom = F.map (fst G.X G.X) :=
    (congrArg (p ≫ ·) (Category.comp_id (fst (F.obj G.X) (F.obj G.X)))).trans
      (CartesianMonoidalCategory.prodComparison_fst F G.X G.X)
  have hs : p ≫ snd H.X H.X ≫ (𝟙 H : H ⟶ H).hom.hom = F.map (snd G.X G.X) :=
    (congrArg (p ≫ ·) (Category.comp_id (snd (F.obj G.X) (F.obj G.X)))).trans
      (CartesianMonoidalCategory.prodComparison_snd F G.X G.X)
  have hG : (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.X := rfl
  simp only [commutator, commutatorMap, commutatorElement_def, Functor.map_mul,
    Functor.map_inv', hG, Category.comp_id, hf, hs]

private theorem baseChange_commutatorProduct_mem (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (N : ClosedSubgroup ((groupBaseChange k K).obj G))
    (hN : FactorsThrough N (commutator ((groupBaseChange k K).obj G))) (n : ℕ) :
    FactorsThrough N ((baseChange k K).map (commutatorProduct G n)) := by
  let F := baseChange k K
  have comp_mem {X Y : SchemeOver K} (p : X ⟶ Y)
      {f : Y ⟶ ((groupBaseChange k K).obj G).X} (hf : FactorsThrough N f) :
      FactorsThrough N (p ≫ f) := by
    obtain ⟨y, hy⟩ := hf
    exact ⟨p ≫ y, Category.assoc _ _ _ |>.trans (congrArg (p ≫ ·) hy)⟩
  induction n with
  | zero =>
    change F.map (1 : power (commutatorDomain G) 0 ⟶ G.X) ∈ SubgroupSections N _
    rw [F.map_one]
    exact (SubgroupSections N _).one_mem
  | succ n ih =>
    change F.map ((fst (commutatorDomain G) _ ≫ commutator G) *
      (snd (commutatorDomain G) _ ≫ commutatorProduct G n)) ∈ SubgroupSections N _
    rw [F.map_mul, F.map_comp, F.map_comp, baseChange_commutator]
    exact (SubgroupSections N _).mul_mem (comp_mem _ (comp_mem _ hN)) (comp_mem _ ih)

/-- After any field extension the pulled-back subgroup has the derived
subgroup's universal property, so it agrees with the derived subgroup there. -/
theorem derivedSubgroupBaseChange : Specs.Reductive.DerivedSubgroup.DerivedSubgroupBaseChange.{u} := by
  intro k _ K _ _ G D hd hs hg
  let F := baseChange k K
  let B := groupBaseChange k K
  have hclosed := baseChangeClosedSubgroup k K D.inclusion D.isClosedImmersion
  let DK : ClosedSubgroup (B.obj G.val) := ⟨B.obj D.group, B.map D.inclusion, hclosed⟩
  have hn := baseChangeNormalSubgroup k K D.inclusion hd.1
  obtain ⟨n, w, _, ha, _, _, hw, he⟩ := exists_dominant_commutatorProduct G D hd hs hg
  have haD := (closedSubgroupAlgebraic G D).property.1
  have hq : QuasiCompact w.left := inferInstance
  have hdom : IsSchemeTheoreticallyDominant (F.map w).left := dominant_baseChange K w
  have hDK : IsDerivedSubgroup DK := by
    refine ⟨hn, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hd.2.1
      change c ≫ D.inclusion.hom.hom = commutator G.val at hc
      let e := prodComparisonIso F G.val.X G.val.X
      refine ⟨e.inv ≫ F.map c, ?_⟩
      change (e.inv ≫ F.map c) ≫ F.map D.inclusion.hom.hom = commutator (B.obj G.val)
      rw [Category.assoc, ← F.map_comp, hc, baseChange_commutator, ← prodComparisonIso_hom,
        Iso.inv_hom_id_assoc]
    · intro N _ hN
      obtain ⟨z, hz⟩ := baseChange_commutatorProduct_mem K N hN n
      change z ≫ N.inclusion.hom.hom = F.map (commutatorProduct G.val n) at hz
      have hNclosed : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
      have hker : N.inclusion.hom.hom.left.ker ≤ DK.inclusion.hom.hom.left.ker := by
        have h := z.left.le_ker_comp N.inclusion.hom.hom.left
        rw [← Over.comp_left, hz, ← he, F.map_comp, ker_comp_eq (F.map w)] at h
        exact h
      have hmono : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
      let j := liftClosed N.inclusion.hom.hom DK.inclusion.hom.hom hker
      have hj := liftClosed_fac N.inclusion.hom.hom DK.inclusion.hom.hom hker
      have : IsMonHom j := isMonHom_of_factor DK.inclusion N.inclusion j hj
      exact ⟨Grp.homMk j, Grp.hom_ext _ _ hj⟩
  exact ⟨hclosed, hDK, fun E hE ↦ SchemeDerivedGroup.normalClosure_unique hDK hE⟩

/-- A represented fppf quotient is commutative exactly when the commutator
morphism factors through its scheme-theoretic kernel. -/
theorem commutativeQuotientIff : Specs.Reductive.DerivedSubgroup.CommutativeQuotientIff.{u} := by
  intro k _ G Q N q hker hrep
  constructor
  · intro hc
    apply (schemeKernel_sections hker _).2
    let T := commutatorDomain G
    let qT : (T ⟶ G.X) →* (T ⟶ Q.X) := ((yonedaGrp.map q).app (op T)).hom
    change qT (commutator G) = 1
    have h : commutator G = ⁅fst G.X G.X, snd G.X G.X⁆ := by
      simp [commutator, commutatorMap, commutatorElement_def]
    rw [h, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc T _ _
  · intro hN T x y
    obtain ⟨e, he⟩ := hrep
    let J := fppfOver k
    have : Sheaf.IsLocallySurjective (rightQuotientProjection N) :=
      rightQuotientLocalLifts N
    have hloc : Sheaf.IsLocallySurjective ((J.uliftYoneda.{u + 1}).map q.hom.hom) := by
      rw [← he]
      infer_instance
    apply locallySurjective_pair_ext q hloc x y
    intro U a x' y' hx hy
    obtain ⟨d, hd⟩ := hN
    change d ≫ N.inclusion.hom.hom = commutator G at hd
    have hc : FactorsThrough N ⁅x', y'⁆ := by
      refine ⟨lift x' y' ≫ d, ?_⟩
      change (lift x' y' ≫ d) ≫ N.inclusion.hom.hom = _
      rw [Category.assoc, hd, comp_commutatorMap]
      simp
    have hq := (schemeKernel_sections hker _).1 hc
    let qU : (U ⟶ G.X) →* (U ⟶ Q.X) := ((yonedaGrp.map q).app (op U)).hom
    change qU ⁅x', y'⁆ = 1 at hq
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hq
    change (x' ≫ q.hom.hom) * (y' ≫ q.hom.hom) =
      (y' ≫ q.hom.hom) * (x' ≫ q.hom.hom) at hq
    simpa only [hx, hy, MonObj.comp_mul] using hq

end

end LinearAlgebraicGroups.Reductive.DerivedSubgroup
