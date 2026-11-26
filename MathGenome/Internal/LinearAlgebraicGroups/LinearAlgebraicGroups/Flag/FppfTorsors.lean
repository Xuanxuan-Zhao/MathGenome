import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Sites.LocallyBijective

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups
namespace Fppf

open Specs.Fppf

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}

private theorem res_comp (P : RightAction J G) {U V W : C} (f : V ⟶ U)
    (g : W ⟶ V) (x : P.Section U) : P.res (g ≫ f) x = P.res g (P.res f x) := by
  change P.sheaf.obj.map (g ≫ f).op x = _
  rw [op_comp, Functor.map_comp]
  rfl

abbrev baseChangeAction (J : GrothendieckTopology C) : RestrictType.{u,v,w} J :=
  restrict

theorem baseChangePreservesTorsors (J : GrothendieckTopology C) : RestrictTorsor.{u,v,w} J := by
  intro X Y f K P hP
  refine ⟨fun U x ↦ hP.1 ((Over.map f).obj U) x, fun U ↦ ?_⟩
  have heq : (restrict f P).sectionSieve U =
      Sieve.functorPullback (Over.map f) (P.sectionSieve ((Over.map f).obj U)) := by
    ext V g
    rfl
  rw [heq]
  exact (Over.map f).cover_lift (J.over X) (J.over Y) (hP.2 _)

def trivializeAtSection (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :
    SectionTrivialization J G := by
  intro hG P U x hP
  let F := (regularAction (groupSheafOnSlice hG U)).sheaf
  let Q := (onSlice P U).sheaf
  let t : F.obj ⟶ Q.obj := {
    app W := ↾fun g ↦ P.act (P.res W.unop.hom x) g
    naturality Y Z f := by
      ext g
      change (G.obj (op Y.unop.left) : Type w) at g
      change P.act (P.res Z.unop.hom x) (G.map f.unop.left.op g) =
        P.sheaf.obj.map f.unop.left.op (P.act (P.res Y.unop.hom x) g)
      rw [P.map_act]
      exact congrArg (fun y ↦ P.act y (G.map f.unop.left.op g))
        ((congrArg (fun q ↦ P.res q x) (Over.w f.unop)).symm.trans
          (res_comp P Y.unop.hom f.unop.left x))
  }
  have ht : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    rw [isIso_iff_bijective]
    exact hP.1 _ (P.res W.unop.hom x)
  let a : F ⟶ Q := ⟨t⟩
  have : IsIso ((sheafToPresheaf (J.over U) (Type w)).map a) := ht
  have : IsIso a := isIso_of_reflects_iso a (sheafToPresheaf (J.over U) (Type w))
  exact ⟨⟨asIso a, fun x g ↦ (P.act_mul _ x g).symm⟩, fun _ _ ↦ rfl⟩

theorem torsorIffLocallyTrivial (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :
    TorsorIffLocallyTrivial J G := by
  intro hG P
  constructor
  · intro hp U
    refine ⟨_, hp.2 U, ?_⟩
    rintro V f ⟨x⟩
    exact ⟨(trivializeAtSection J G hG P V x hp).1⟩
  · intro hP
    have hlocal (U : C) : ∃ R ∈ J U, ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, R f →
        (Nonempty (P.Section V) ∧ ∀ x : P.Section V, Function.Bijective (P.act x)) := by
      obtain ⟨R, hR, he⟩ := hP U
      refine ⟨R, hR, ?_⟩
      intro V f hf
      obtain ⟨e⟩ := he hf
      let W := Over.mk (𝟙 V)
      let E : (G.obj (op V) : Type w) ≃ P.Section V :=
        (asIso (e.iso.hom.hom.app (op W))).toEquiv
      refine ⟨⟨E 1⟩, fun x ↦ ?_⟩
      obtain ⟨g, rfl⟩ := E.surjective x
      have heq : P.act (E g) = E ∘ (g * ·) := by
        funext a
        exact (e.equivariant (U := W) g a).symm
      rw [heq]
      exact E.bijective.comp (Equiv.mulLeft g).bijective
    have hcover : ∀ U, P.sectionSieve U ∈ J U := by
      intro U
      obtain ⟨R, hR, h⟩ := hlocal U
      exact J.superset_covering (fun _ _ hf ↦ (h hf).1) hR
    refine ⟨fun U x ↦ ?_, hcover⟩
    obtain ⟨R, hR, h⟩ := hlocal U
    have hg := hG R hR
    have hp := ((isSheaf_iff_isSheaf_of_type _ _).1 P.sheaf.property) R hR
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply hg.isSeparatedFor.ext
      intro V f hf
      change G.map f.op a = G.map f.op b
      apply ((h hf).2 (P.res f x)).1
      rw [← P.map_act, ← P.map_act, hab]
    · intro y
      let t : Presieve.FamilyOfElements (G ⋙ forget GrpCat) R.arrows :=
        fun V f hf ↦ Classical.choose (((h hf).2 (P.res f x)).2 (P.res f y))
      have ht {V : C} (f : V ⟶ U) (hf : R f) :
          P.act (P.res f x) (t f hf) = P.res f y :=
        Classical.choose_spec (((h hf).2 (P.res f x)).2 (P.res f y))
      have hc : t.Compatible := by
        intro V₁ V₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ e
        have hW : R (g₁ ≫ f₁) := R.downward_closed hf₁ g₁
        apply ((h hW).2 (P.res (g₁ ≫ f₁) x)).1
        change P.act (P.res (g₁ ≫ f₁) x) (G.map g₁.op (t f₁ hf₁)) =
          P.act (P.res (g₁ ≫ f₁) x) (G.map g₂.op (t f₂ hf₂))
        rw [show P.res (g₁ ≫ f₁) x = P.res g₁ (P.res f₁ x) by
          simp [RightAction.res, ← Functor.map_comp_apply, ← op_comp]]
        rw [← P.map_act, ht _ hf₁]
        rw [show P.res g₁ (P.res f₁ x) = P.res g₂ (P.res f₂ x) by
          simp [RightAction.res, ← Functor.map_comp_apply, ← op_comp, e]]
        rw [← P.map_act, ht _ hf₂]
        simp [RightAction.res, ← Functor.map_comp_apply, ← op_comp, e]
      refine ⟨hg.amalgamate t hc, ?_⟩
      apply hp.isSeparatedFor.ext
      intro V f hf
      rw [show P.sheaf.obj.map f.op (P.act x (hg.amalgamate t hc)) =
        P.act (P.res f x) (G.map f.op (hg.amalgamate t hc)) from P.map_act f _ _]
      rw [show G.map f.op (hg.amalgamate t hc) = t f hf from hg.valid_glue hc f hf]
      exact ht f hf

theorem schemeGroupSectionsAreSheaf : GroupSectionsSheaf.{u} := by
  intro k _ S H
  have h : Presieve.IsSheaf (schemeTopology k)
      (CategoryTheory.uliftYoneda.{u+1}.obj H.X) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((schemeTopology k).uliftYoneda.{u+1}.obj H.X).property
  exact groupSheafOnSlice (G := yonedaGrp.obj H ⋙ liftGroups.{u,u+1}) h S

theorem globalSectionTrivialization (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :
    GlobalSectionTrivialization J G := by
  intro hG P T hT x
  let a : (regularAction hG).sheaf ⟶ P.1.sheaf :=
    ⟨{ app U := ↾fun g ↦ P.1.act (P.1.res (hT.from U.unop) x) g
       naturality U V f := by
         apply ConcreteCategory.hom_ext
         intro g
         change (G.obj U : Type w) at g
         change P.1.act (P.1.res (hT.from V.unop) x) (G.map f g) =
           P.1.sheaf.obj.map f (P.1.act (P.1.res (hT.from U.unop) x) g)
         exact (congrArg (fun y ↦ P.1.act y (G.map f g))
           ((congrArg (fun q ↦ P.1.res q x)
             (hT.hom_ext (f.unop ≫ hT.from U.unop) (hT.from V.unop))).symm.trans
               (res_comp P.1 (hT.from U.unop) f.unop x))).trans
                 (P.1.map_act f.unop (P.1.res (hT.from U.unop) x) g).symm }⟩
  have : IsIso ((sheafToPresheaf J (Type w)).map a) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    exact P.2.1 U.unop (P.1.res (hT.from U.unop) x)
  have : IsIso a := isIso_of_reflects_iso a (sheafToPresheaf J (Type w))
  exact ⟨⟨asIso a, fun g h ↦ (P.1.act_mul _ g h).symm⟩, fun _ _ ↦ rfl⟩

abbrev H1fppf : H1fppfType.{u} := Specs.Fppf.H1fppf

abbrev neutralClass : NeutralClassType.{u} := @Specs.Fppf.neutralClass

theorem rationalPointCriterion : RationalPointCriterion.{u} := by
  intro k _ H hG P
  constructor
  · intro h
    obtain ⟨e⟩ : Nonempty (RightActionIso P.1 (regularAction hG)) := Quotient.exact h
    exact ⟨e.iso.inv.hom.app (op (fieldTest k)) (1 : (groupSections (fieldBase k) H).obj (op (fieldTest k)))⟩
  · rintro ⟨x⟩
    obtain ⟨e, _⟩ := globalSectionTrivialization _ _ hG P (fieldTest k)
      Over.mkIdTerminal x
    exact Quotient.sound ⟨e.symm⟩

section Represented

variable {k : Type u} [Field k] {S : SchemeOver k} {H : Specs.GroupScheme k} {X : Over S}

private def comparisonOver (a : SchemeRightAction X H) :
    actionSource X H ⟶ Over.mk (pullback.fst X.hom X.hom ≫ X.hom) :=
  Over.homMk (comparison a) (by simp [comparison])

private def actionSourcePoints (T : Over S) :
    (T ⟶ actionSource X H) ≃ (T ⟶ X) × (T.left ⟶ H.X) where
  toFun f := (Over.homMk (f.left ≫ prod.fst) (by simpa using Over.w f), f.left ≫ prod.snd)
  invFun p := actionPair p.1 p.2
  left_inv f := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp [actionPair]
  right_inv p := by
    apply Prod.ext
    · apply Over.OverMorphism.ext
      simp [actionPair]
    · simp [actionPair]

private def comparisonTargetPoints (T : Over S) :
    (T ⟶ Over.mk (pullback.fst X.hom X.hom ≫ X.hom)) ≃ (T ⟶ X) × (T ⟶ X) where
  toFun f :=
    (Over.homMk (f.left ≫ pullback.fst _ _) (by simpa using Over.w f),
      Over.homMk (f.left ≫ pullback.snd _ _) (by simpa [← pullback.condition] using Over.w f))
  invFun p := Over.homMk (pullback.lift p.1.left p.2.left (by simp)) (by simp)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  right_inv p := by
    apply Prod.ext <;> apply Over.OverMorphism.ext <;> simp

private theorem comparison_iff (a : SchemeRightAction X H) :
    IsIso (comparison a) ↔ ∀ (T : Over S) (x : (representedAction a).Section T),
      Function.Bijective ((representedAction a).act x) := by
  have hIso : IsIso (comparison a) ↔ IsIso (comparisonOver a) := by
    constructor
    · intro h
      have : IsIso ((Over.forget S).map (comparisonOver a)) := h
      exact isIso_of_reflects_iso _ (Over.forget S)
    · intro h
      exact (Over.forget S).map_isIso (comparisonOver a)
  rw [hIso, ← isIso_iff_of_reflects_iso (comparisonOver a) yoneda, NatTrans.isIso_iff_isIso_app]
  have hT (T : Over S) :
      Function.Bijective (fun f : T ⟶ actionSource X H ↦ f ≫ comparisonOver a) ↔
      ∀ x : T ⟶ X, Function.Bijective (fun g : T.left ⟶ H.X ↦ actionPair x g ≫ a.action) := by
    let F := fun p : (T ⟶ X) × (T.left ⟶ H.X) ↦ (p.1, actionPair p.1 p.2 ≫ a.action)
    have heq (p : (T ⟶ X) × (T.left ⟶ H.X)) :
        comparisonTargetPoints T ((actionSourcePoints T).symm p ≫ comparisonOver a) = F p := by
      apply Prod.ext <;> apply Over.OverMorphism.ext <;> simp [comparisonTargetPoints,
        actionSourcePoints, F, comparisonOver, comparison, actionPair]
    have hb : Function.Bijective (fun f : T ⟶ actionSource X H ↦ f ≫ comparisonOver a) ↔
        Function.Bijective F := by
      let m := fun f : T ⟶ actionSource X H ↦ f ≫ comparisonOver a
      let l := (actionSourcePoints T (X := X) (H := H)).symm
      let r := comparisonTargetPoints T (X := X)
      have e : r ∘ (m ∘ l) = F := funext heq
      exact ((r.bijective.of_comp_iff' (m ∘ l)).trans
        (Function.Bijective.of_comp_iff m l.bijective)).symm.trans (e ▸ Iff.rfl)
    rw [hb]
    constructor
    · intro h x
      refine ⟨fun g h' e ↦ congrArg Prod.snd (h.1 (show F (x,g) = F (x,h') by simp [F, e])), ?_⟩
      intro y
      obtain ⟨⟨x', g⟩, e⟩ := h.2 (x, y)
      have hx : x' = x := congrArg Prod.fst e
      subst x'
      exact ⟨g, congrArg Prod.snd e⟩
    · intro h
      refine ⟨?_, ?_⟩
      · rintro ⟨x,g⟩ ⟨x',g'⟩ e
        have hx : x = x' := congrArg Prod.fst e
        subst x'
        exact Prod.ext rfl ((h x).1 (congrArg Prod.snd e))
      · rintro ⟨x,y⟩
        obtain ⟨g,hg⟩ := (h x).2 y
        exact ⟨(x,g), Prod.ext rfl hg⟩
  have key (T : Over S) :
      IsIso ((yoneda.map (comparisonOver a)).app (op T)) ↔
      ∀ x : (representedAction a).Section T, Function.Bijective ((representedAction a).act x) := by
    rw [isIso_iff_bijective]
    change Function.Bijective (fun f : T ⟶ actionSource X H ↦ f ≫ comparisonOver a) ↔ _
    rw [hT]
    constructor
    · intro h x
      change Function.Bijective (fun g : ULift (T.left ⟶ H.X) ↦
        (ULift.up (actionPair x.down g.down ≫ a.action) : ULift (T ⟶ X)))
      exact Equiv.ulift.symm.bijective.comp ((h x.down).comp Equiv.ulift.bijective)
    · intro h x
      have hh := h (ULift.up x)
      exact Equiv.ulift.bijective.comp (hh.comp Equiv.ulift.symm.bijective)
  exact ⟨fun h T ↦ (key T).1 (h (op T)), fun h T ↦ (key T.unop).2 (h T.unop)⟩

private theorem flatCodescends : RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R B A _ _ _ _ _ hf hg ↦ ?_
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hf
  rw [RingHom.flat_algebraMap_iff] at hg ⊢
  exact Module.Flat.of_flat_tensorProduct R A B

private theorem sectionSieve_iff_fppf (a : SchemeRightAction X H) [IsIso (comparison a)]
    (hH : LocallyOfFiniteType H.X.hom) :
    (representedAction a).sectionSieve (Over.mk (𝟙 S)) ∈
      torsorTopology S (Over.mk (𝟙 S)) ↔ IsFppf X.hom.left := by
  let T : Over S := Over.mk (𝟙 S)
  let R := (representedAction a).sectionSieve T
  let R' := Sieve.overEquiv T R
  let R'' := Sieve.overEquiv T.left R'
  have hmem : R ∈ torsorTopology S T ↔ R'' ∈ Scheme.fppfTopology S.left := Iff.rfl
  have liftOfMem {W : Scheme.{u}} (f : W ⟶ S.left) (hf : R'' f) :
      ∃ x : W ⟶ X.left.left, x ≫ X.hom.left = f := by
    let Wk : SchemeOver k := Over.mk (f ≫ S.hom)
    let F : Wk ⟶ S := Over.homMk f
    let WS : Over S := Over.mk F
    have hf' : R' F := (Sieve.overEquiv_iff R' f).1 hf
    have hf'' : R (Over.homMk (U := WS) F (Category.comp_id F) : WS ⟶ T) :=
      (Sieve.overEquiv_iff R F).1 hf'
    obtain ⟨x⟩ := hf''
    exact ⟨x.down.left.left, congrArg Over.Hom.left (Over.w x.down)⟩
  have memOfLift {W : Scheme.{u}} (f : W ⟶ S.left) (x : W ⟶ X.left.left)
      (hx : x ≫ X.hom.left = f) : R'' f := by
    let Wk : SchemeOver k := Over.mk (f ≫ S.hom)
    let F : Wk ⟶ S := Over.homMk f
    let WS : Over S := Over.mk F
    apply (Sieve.overEquiv_iff R' f).2
    apply (Sieve.overEquiv_iff R F).2
    change Nonempty (ULift (WS ⟶ X))
    refine ⟨⟨Over.homMk (Over.homMk x ?_) ?_⟩⟩
    · change x ≫ X.left.hom = f ≫ S.hom
      exact congrArg (x ≫ ·) (Over.w X.hom).symm |>.trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ S.hom) hx))
    · exact Over.OverMorphism.ext hx
  rw [hmem]
  constructor
  · intro h
    let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
    obtain ⟨V, hV, hle⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := Scheme.fppfPrecoverage)).1 h
    obtain ⟨𝒰, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hV
    let 𝒰' : S.left.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
    let 𝒱 := 𝒰'.ulift
    choose x hx using fun i : 𝒱.I₀ ↦ liftOfMem (𝒱.f i) (hle _ _ ⟨𝒰'.idx i⟩)
    let W := 𝒱.sigma.X default
    let f : W ⟶ S.left := 𝒱.sigma.f default
    let x' : W ⟶ X.left.left := Sigma.desc x
    have hx' : x' ≫ X.hom.left = f := by
      apply Sigma.hom_ext
      intro i
      simpa [x', f] using hx i
    let Wk : SchemeOver k := Over.mk (f ≫ S.hom)
    let b : Wk ⟶ X.left := Over.homMk x' (by
      change x' ≫ X.left.hom = f ≫ S.hom
      exact congrArg (x' ≫ ·) (Over.w X.hom).symm |>.trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ S.hom) hx')))
    have hs : Surjective f := by
      refine ⟨fun s ↦ ?_⟩
      obtain ⟨_, y, rfl⟩ := 𝒱.sigma.exists_eq s
      exact ⟨y, rfl⟩
    have hp : Flat f ∧ LocallyOfFinitePresentation f := 𝒱.sigma.map_prop default
    have hcomp : IsPullback (prod.fst : X.left ⨯ H.X ⟶ X.left) a.action.left X.hom X.hom :=
      .of_iso_pullback ⟨(Over.w a.action).symm⟩ (asIso (comparison a))
        (by simp [comparison]) (by simp [comparison])
    have hproduct := ((IsPullback.of_prod_fst_with_id b H.X).flip.paste_horiz hcomp.flip).flip
    have hpb := hproduct.map (Over.forget (Spec (CommRingCat.of k)))
    have heqb : (b ≫ X.hom).left = f := hx'
    rw [show (Over.forget (Spec (CommRingCat.of k))).map (b ≫ X.hom) = f from heqb] at hpb
    have hgroup := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Wk H.X)).flip
    have : Flat H.X.hom := inferInstance
    have : LocallyOfFiniteType H.X.hom := hH
    have hfprod : Flat (prod.fst : Wk ⨯ H.X ⟶ Wk).left :=
      MorphismProperty.of_isPullback hgroup inferInstance
    have hpprod : LocallyOfFinitePresentation (prod.fst : Wk ⨯ H.X ⟶ Wk).left :=
      MorphismProperty.of_isPullback hgroup inferInstance
    let : MorphismProperty.DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
      HasRingHomProperty.descendsAlong_flat flatCodescends
    have hc : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) f := ⟨⟨hs, hp.1⟩, hp.2⟩
    exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hpb hc hfprod,
      ⟨fun s ↦ by
        obtain ⟨y,hy⟩ := hs.1 s
        exact ⟨x' y, by simpa [← Scheme.Hom.comp_apply, hx'] using hy⟩⟩,
      MorphismProperty.of_isPullback_of_descendsAlong hpb hc hpprod⟩
  · intro ⟨hp, hs, hl⟩
    apply Scheme.fppfTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (fun _ _ h ↦ ?_))
      (Precoverage.generate_mem_toGrothendieck X.hom.left.singleton_mem_fppfPrecoverage)
    cases h
    exact memOfLift _ (𝟙 _) (Category.id_comp _)

theorem representedTorsorCriterion : RepresentedTorsorCriterion.{u} := by
  intro k _ S H hH X a
  constructor
  · intro h
    have : IsIso (comparison a) := (comparison_iff a).2 h.1
    exact ⟨(sectionSieve_iff_fppf a hH.1).1 (h.2 _), inferInstance⟩
  · rintro ⟨h, hi⟩
    refine ⟨(comparison_iff a).1 hi, fun T ↦ ?_⟩
    have hcover := (sectionSieve_iff_fppf a hH.1).2 h
    refine (torsorTopology S).superset_covering ?_
      ((torsorTopology S).pullback_stable (Over.mkIdTerminal.from T) hcover)
    exact fun _ _ hf ↦ hf

theorem representSheafAction : RepresentSheafAction.{u} := by
  intro k _ S H P X e
  let D := actionSource X H
  let x₀ : D ⟶ X := Over.homMk prod.fst rfl
  let g₀ : D.left ⟶ H.X := prod.snd
  let E (U : Over S) : ULift.{u+1} (U ⟶ X) ≃ P.Section U :=
    (((evaluation _ _).obj (op U)).mapIso
      ((sheafToPresheaf _ (Type (u+1))).mapIso e)).toEquiv
  have hres {U V : Over S} (f : V ⟶ U) (x : U ⟶ X) :
      E V ⟨f ≫ x⟩ = P.res f (E U ⟨x⟩) := by
    let y : (representedSheaf X).obj.obj (op U) := ULift.up x
    exact NatTrans.naturality_apply e.hom.hom f.op y
  let m : D ⟶ X := ((E D).symm (P.act (E D ⟨x₀⟩) ⟨g₀⟩)).down
  have hm (U : Over S) (x : U ⟶ X) (g : (groupSections S H).obj (op U)) :
      E U ⟨actionPair x g.down ≫ m⟩ = P.act (E U ⟨x⟩) g := by
    have hx : actionPair x g.down ≫ x₀ = x := by
      apply Over.OverMorphism.ext
      change prod.lift x.left g.down ≫ prod.fst = x.left
      exact prod.lift_fst _ _
    have hg : (groupSections S H).map (actionPair x g.down).op ⟨g₀⟩ = g := by
      apply ULift.ext
      change prod.lift x.left g.down ≫ prod.snd = g.down
      exact prod.lift_snd _ _
    have hE : E D ⟨m⟩ = P.act (E D ⟨x₀⟩) ⟨g₀⟩ :=
      (E D).apply_symm_apply _
    calc
      _ = P.res (actionPair x g.down) (E D ⟨m⟩) := hres _ _
      _ = P.act (P.res (actionPair x g.down) (E D ⟨x₀⟩)) g := by
        rw [hE]
        exact (P.map_act (actionPair x g.down) _ _).trans (congrArg _ hg)
      _ = _ := by rw [← hres, hx]
  let a : SchemeRightAction X H := {
    action := m
    one := by
      intro U x
      apply ULift.up_injective
      apply (E U).injective
      exact (hm U x 1).trans (P.act_one _)
    mul := by
      intro U x g h
      apply ULift.up_injective
      apply (E U).injective
      rw [hm, hm, hm, P.act_mul]
  }
  exact ⟨a, ⟨e, fun x g ↦ hm _ x.down g⟩, rfl⟩

end Represented

section ContractedProduct

variable {K : Cᵒᵖ ⥤ GrpCat.{w}}

private def pairPresheaf (A B : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := A.obj U × B.obj U
  map f := ↾fun p ↦ (A.map f p.1, B.map f p.2)
  map_id U := by ext p <;> simp
  map_comp f g := by ext p <;> simp

private def pairMap {A B A' B' : Cᵒᵖ ⥤ Type w} (f : A ⟶ A') (g : B ⟶ B') :
    pairPresheaf A B ⟶ pairPresheaf A' B' where
  app U := ↾fun p ↦ (f.app U p.1, g.app U p.2)
  naturality U V h := by
    apply ConcreteCategory.hom_ext
    intro p
    change (f.app V (A.map h p.1), g.app V (B.map h p.2)) =
      (A'.map h (f.app U p.1), B'.map h (g.app U p.2))
    exact Prod.ext (f.naturality_apply h p.1) (g.naturality_apply h p.2)

private theorem pairSheaf {A B : Cᵒᵖ ⥤ Type w} (hA : Presieve.IsSheaf J A)
    (hB : Presieve.IsSheaf J B) : Presieve.IsSheaf J (pairPresheaf A B) := by
  intro U R hR t ht
  let a : Presieve.FamilyOfElements A R.arrows := fun _ f hf ↦ (t f hf).1
  let b : Presieve.FamilyOfElements B R.arrows := fun _ f hf ↦ (t f hf).2
  have ha : a.Compatible := fun _ _ _ _ _ _ _ p q e ↦ congrArg Prod.fst (ht _ _ p q e)
  have hb : b.Compatible := fun _ _ _ _ _ _ _ p q e ↦ congrArg Prod.snd (ht _ _ p q e)
  obtain ⟨x,hx,hxu⟩ := hA R hR a ha
  obtain ⟨y,hy,hyu⟩ := hB R hR b hb
  exact ⟨(x,y), fun _ f hf ↦ Prod.ext (hx f hf) (hy f hf),
    fun p hp ↦ Prod.ext (hxu p.1 (fun _ f hf ↦ congrArg Prod.fst (hp f hf)))
      (hyu p.2 (fun _ f hf ↦ congrArg Prod.snd (hp f hf)))⟩

private theorem pairLocallySurjective {A B A' B' : Cᵒᵖ ⥤ Type w} (f : A ⟶ A') (g : B ⟶ B')
    [Presheaf.IsLocallySurjective J f] [Presheaf.IsLocallySurjective J g] :
    Presheaf.IsLocallySurjective J (pairMap f g) := by
  constructor
  intro U s
  apply J.superset_covering ?_ (J.intersection_covering
    (Presheaf.imageSieve_mem J f (U := op U) s.1)
    (Presheaf.imageSieve_mem J g (U := op U) s.2))
  rintro V h ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  exact ⟨(x,y), Prod.ext hx hy⟩

private theorem pairLocallyInjective {A B A' B' : Cᵒᵖ ⥤ Type w} (f : A ⟶ A') (g : B ⟶ B')
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallyInjective J g] :
    Presheaf.IsLocallyInjective J (pairMap f g) := by
  constructor
  intro U x y h
  change (f.app U x.1, g.app U x.2) = (f.app U y.1, g.app U y.2) at h
  apply J.superset_covering ?_ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J f (X := U) x.1 y.1 (congrArg Prod.fst h))
    (Presheaf.equalizerSieve_mem J g (X := U) x.2 y.2 (congrArg Prod.snd h)))
  exact fun V i ⟨hi,hj⟩ ↦ Prod.ext hi hj

private theorem eq_of_local {A : Cᵒᵖ ⥤ Type w} (hA : Presieve.IsSheaf J A)
    {U : C} {x y : A.obj (op U)} {R : Sieve U} (hR : R ∈ J U)
    (h : ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, R f → A.map f.op x = A.map f.op y) :
    x = y :=
  (Presieve.IsSheafFor.isSeparatedFor (hA R hR)).ext (fun _ _ hf ↦ h hf)

private def rawAction (φ : G ⟶ K) (P : RightAction J G) :
    pairPresheaf (contractedPresheaf φ P) (K ⋙ forget GrpCat) ⟶ contractedPresheaf φ P where
  app U := ↾fun p ↦ Quotient.map (fun z ↦ (z.1,z.2 * (show K.obj U from p.2)))
    (by
      rintro x y ⟨g,hx,hy⟩
      exact ⟨g,hx, by rw [← mul_assoc, hy]⟩) p.1
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨p,c⟩
    change (K.obj U : Type w) at c
    refine Quotient.inductionOn p ?_
    intro x
    change Quotient.mk _ (P.sheaf.obj.map f x.1, K.map f x.2 * K.map f c) =
      Quotient.mk _ (P.sheaf.obj.map f x.1, K.map f (x.2 * c))
    rw [map_mul]

private def compareAction {A B : Cᵒᵖ ⥤ Type w} (a : pairPresheaf A B ⟶ A) :
    pairPresheaf A B ⟶ pairPresheaf A A where
  app U := ↾fun p ↦ (p.1, a.app U p)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro p
    change ((A.map f p.1), a.app V ((pairPresheaf A B).map f p)) =
      (A.map f p.1, A.map f (a.app U p))
    exact Prod.ext rfl (a.naturality_apply f p)

private theorem compareAction_bijective {A B : Cᵒᵖ ⥤ Type w} (a : pairPresheaf A B ⟶ A)
    (U : Cᵒᵖ) :
    Function.Bijective ((compareAction a).app U) ↔
      ∀ x : A.obj U, Function.Bijective (fun b : B.obj U ↦ a.app U (x,b)) := by
  change Function.Bijective (fun p : A.obj U × B.obj U ↦ (p.1,a.app U p)) ↔ _
  constructor
  · intro h x
    constructor
    · intro b c e
      have he : (x,b) = (x,c) := h.1 (Prod.ext rfl e)
      exact congrArg Prod.snd he
    intro y
    obtain ⟨⟨x', b⟩,e⟩ := h.2 (x,y)
    have hxx : x' = x := congrArg Prod.fst e
    subst x'
    exact ⟨b,congrArg Prod.snd e⟩
  · intro h
    constructor
    · rintro ⟨x,b⟩ ⟨y,c⟩ e
      have he : x = y := congrArg Prod.fst e
      subst y
      exact Prod.ext rfl ((h x).1 (congrArg Prod.snd e))
    · rintro ⟨x,y⟩
      obtain ⟨b,hb⟩ := (h x).2 y
      exact ⟨(x,b), Prod.ext rfl hb⟩

private theorem rawAction_bijective (φ : G ⟶ K) (P : Torsor J G) (U : Cᵒᵖ) :
    ∀ x : (contractedPresheaf φ P.1).obj U,
      Function.Bijective (fun b : K.obj U ↦ (rawAction φ P.1).app U (x,b)) := by
  intro x
  refine Quotient.inductionOn x ?_
  rintro ⟨p,c⟩
  constructor
  · intro b b' h
    change Quotient.mk (contractedRelation φ P.1 U.unop) (p,c*b) = Quotient.mk _ (p,c*b') at h
    obtain ⟨g,hg,hb⟩ := Quotient.exact h
    have hg' : g = 1 := (P.2.1 U.unop p).1 (hg.trans (P.1.act_one p).symm)
    exact mul_left_cancel (a := c) (by simpa only [hg', map_one, one_mul] using hb.symm)
  · intro y
    refine Quotient.inductionOn y ?_
    rintro ⟨q,d⟩
    obtain ⟨g,hg⟩ := (P.2.1 U.unop p).2 q
    refine ⟨c⁻¹ * (φ.app U g * d), Quotient.sound ?_⟩
    exact ⟨g,hg, by simp⟩

variable (J) [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

abbrev contractedProduct : ContractedProductType.{u,v,w} := @Specs.Fppf.contractedProduct

theorem extensionOfStructureGroup : ExtensionOfStructureGroup J := by
  intro G K φ hK P
  let R := contractedPresheaf φ P.1
  let F := Specs.Fppf.contractedProduct J φ P.1
  let B := K ⋙ forget GrpCat
  let i : R ⟶ F.obj := toSheafify J R
  have hF : Presieve.IsSheaf J F.obj := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hF' : Presheaf.IsSheaf J F.obj := F.property
  have : Presheaf.IsLocallySurjective J i := inferInstanceAs
    (Presheaf.IsLocallySurjective J (toSheafify J R))
  have : Presheaf.IsLocallyInjective J i := inferInstanceAs
    (Presheaf.IsLocallyInjective J (toSheafify J R))
  let q := pairMap i (𝟙 B)
  let q' := pairMap i i
  have wq : J.W q := (J.W_iff_isLocallyBijective _).2
    ⟨pairLocallyInjective _ _, pairLocallySurjective _ _⟩
  have wq' : J.W q' := (J.W_iff_isLocallyBijective _).2
    ⟨pairLocallyInjective _ _, pairLocallySurjective _ _⟩
  obtain ⟨a, ha⟩ := (wq F.obj hF').2 (rawAction φ P.1 ≫ i)
  have happ (U : Cᵒᵖ) (x : R.obj U) (b : K.obj U) :
      a.app U (i.app U x,b) = i.app U ((rawAction φ P.1).app U (x,b)) :=
    congrArg (fun t : pairPresheaf R B ⟶ F.obj ↦ t.app U (x,b)) ha
  have oneRaw (U : Cᵒᵖ) (x : R.obj U) : (rawAction φ P.1).app U (x,1) = x := by
    refine Quotient.inductionOn x ?_
    intro p
    change Quotient.mk _ (p.1,p.2 * 1) = Quotient.mk _ p
    simp
  have mulRaw (U : Cᵒᵖ) (x : R.obj U) (g h : K.obj U) :
      (rawAction φ P.1).app U ((rawAction φ P.1).app U (x,g),h) =
        (rawAction φ P.1).app U (x,g*h) := by
    refine Quotient.inductionOn x ?_
    intro p
    change Quotient.mk _ (p.1,(p.2*g)*h) = Quotient.mk _ (p.1,p.2*(g*h))
    rw [mul_assoc]
  let A : RightAction J K := {
    sheaf := F
    act x g := a.app _ (x,g)
    act_one := by
      intro U x
      apply eq_of_local hF (Presheaf.imageSieve_mem J i (U := op U) x)
      rintro V f ⟨y,hy⟩
      rw [← a.naturality_apply]
      change a.app (op V) (F.obj.map f.op x, K.map f.op 1) = F.obj.map f.op x
      rw [map_one, ← hy, happ, oneRaw]
    act_mul := by
      intro U x g h
      apply eq_of_local hF (Presheaf.imageSieve_mem J i (U := op U) x)
      rintro V f ⟨y,hy⟩
      rw [← a.naturality_apply, ← a.naturality_apply]
      change a.app (op V) (F.obj.map f.op (a.app (op U) (x,g)), K.map f.op h) =
        a.app (op V) (F.obj.map f.op x, K.map f.op (g*h))
      rw [← a.naturality_apply]
      change a.app (op V) (a.app (op V) (F.obj.map f.op x, K.map f.op g), K.map f.op h) =
        a.app (op V) (F.obj.map f.op x, K.map f.op (g*h))
      rw [map_mul, ← hy, happ, happ, happ, mulRaw]
    map_act := by
      intro U V f x g
      rw [← a.naturality_apply]
      rfl
  }
  have rawIso : IsIso (compareAction (rawAction φ P.1)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective, compareAction_bijective]
    exact rawAction_bijective φ P U
  have square : q ≫ compareAction a = compareAction (rawAction φ P.1) ≫ q' := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext rfl (happ U x.1 x.2)
  have wCompare : J.W (compareAction a) := by
    apply (J.W (A := Type w)).of_precomp q _ wq
    rw [square]
    exact (J.W (A := Type w)).comp_mem _ _ (ObjectProperty.isLocal_of_isIso _ _) wq'
  have hsheaf1 := (isSheaf_iff_isSheaf_of_type _ _).2 (pairSheaf hF hK)
  have hsheaf2 := (isSheaf_iff_isSheaf_of_type _ _).2 (pairSheaf hF hF)
  have compIso : IsIso (compareAction a) :=
    (ObjectProperty.isLocal_iff_isIso _ _ hsheaf1 hsheaf2).1 wCompare
  refine ⟨⟨A, ?_, ?_⟩, Iso.refl F, ?_⟩
  · intro U
    apply (compareAction_bijective a (op U)).1
    rw [← isIso_iff_bijective]
    infer_instance
  · intro U
    apply J.superset_covering ?_ (P.2.2 U)
    rintro V f ⟨p⟩
    exact ⟨i.app (op V) (contractedPair φ P.1 p 1)⟩
  · intro U p b c
    exact happ (op U) (contractedPair φ P.1 p b) c

end ContractedProduct

theorem localSectionTrivialization (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :
    LocalSectionTrivialization J G :=
  ⟨trivializeAtSection J G⟩

abbrev FppfTorsor : FppfTorsorType.{u} := @Specs.Fppf.FppfTorsor
abbrev SchemeRightAction : SchemeRightActionType.{u} := @Specs.Fppf.SchemeRightAction
abbrev representedAction : RepresentedActionType.{u} := @Specs.Fppf.representedAction
abbrev comparison : ComparisonType.{u} := @Specs.Fppf.comparison
abbrev schemeBaseChange : SchemeBaseChangeType.{u} := @Specs.Fppf.schemeBaseChange

theorem schemeBaseChangePreservesTorsors : SchemeBaseChangePreservesTorsors.{u} := by
  intro k _ S T H f P h
  exact baseChangePreservesTorsors (schemeTopology k) f P h

theorem representedRationalPointCriterion : RepresentedRationalPointCriterion.{u} := by
  intro k _ H hG X a ha
  rw [show
    (Quotient.mk _ (⟨representedAction a, ha⟩ : FppfTorsor (fieldBase k) H) : H1fppf k H) =
        neutralClass hG ↔ Nonempty ((representedAction a).Section (fieldTest k))
    from rationalPointCriterion hG ⟨representedAction a, ha⟩]
  constructor
  · rintro ⟨x⟩
    exact ⟨x.down.left⟩
  · rintro ⟨x⟩
    exact ⟨⟨Over.homMk x (Over.mkIdTerminal.hom_ext _ _)⟩⟩

abbrev groupSectionsMap : GroupSectionsMapType.{u} := @Specs.Fppf.groupSectionsMap

theorem schemeContractedExtension : SchemeContractedExtension.{u} := by
  intro k _ S H K f P
  exact extensionOfStructureGroup (torsorTopology S) (groupSectionsMap S f)
    (schemeGroupSectionsAreSheaf S K) P

/-- Extend the structure group of a right fppf torsor along a group scheme homomorphism. -/
def extendStructureGroup {k : Type u} [Field k] {S : SchemeOver k} {H K : Specs.GroupScheme k}
    (f : H ⟶ K) (P : FppfTorsor S H) : FppfTorsor S K :=
  (schemeContractedExtension S f P).choose

theorem extendStructureGroup_spec {k : Type u} [Field k]
    {S : SchemeOver k} {H K : Specs.GroupScheme k} (f : H ⟶ K) (P : FppfTorsor S H) :
    IsStructureGroupExtension S f P (extendStructureGroup f P) :=
  (schemeContractedExtension S f P).choose_spec

private theorem torsorOfIso {P Q : RightAction J G} (e : RightActionIso P Q)
    (hP : IsTorsor P) : IsTorsor Q := by
  let E (U : C) : P.Section U ≃ Q.Section U :=
    (((evaluation _ _).obj (op U)).mapIso ((sheafToPresheaf J (Type w)).mapIso e.iso)).toEquiv
  refine ⟨?_, fun U ↦ J.superset_covering ?_ (hP.2 U)⟩
  · intro U x
    have heq : Q.act x = E U ∘ P.act ((E U).symm x) := by
      funext g
      have h := e.equivariant ((E U).symm x) g
      change E U (P.act ((E U).symm x) g) = Q.act (E U ((E U).symm x)) g at h
      rw [(E U).apply_symm_apply] at h
      exact h.symm
    rw [heq]
    exact (E U).bijective.comp (hP.1 U ((E U).symm x))
  · rintro V f ⟨x⟩
    exact ⟨E V x⟩

theorem torsorInvariantUnderIso : TorsorInvariantUnderIso.{u,v,w} := by
  intro C _ J G P Q e
  exact ⟨torsorOfIso e, torsorOfIso e.symm⟩

theorem representedBaseChange : RepresentedBaseChange.{u} := by
  intro k _ S T f X
  let F := ((schemeTopology k).overMapPullback (Type (u + 1)) f).obj (representedSheaf X)
  let Q := representedSheaf ((Over.pullback f).obj X)
  let t : F.obj ⟶ Q.obj := {
    app U := ↾fun x ↦ ⟨(Over.mapPullbackAdj f).homEquiv U.unop X x.down⟩
    naturality U V g := by
      apply ConcreteCategory.hom_ext
      intro x
      apply ULift.ext
      exact (Over.mapPullbackAdj f).homEquiv_naturality_left g.unop x.down }
  have ht : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    exact (Equiv.ulift.trans (((Over.mapPullbackAdj f).homEquiv U.unop X).trans Equiv.ulift.symm)).bijective
  let a : F ⟶ Q := ⟨t⟩
  have : IsIso ((sheafToPresheaf (torsorTopology T) (Type (u + 1))).map a) := ht
  have : IsIso a := isIso_of_reflects_iso a (sheafToPresheaf (torsorTopology T) (Type (u + 1)))
  exact ⟨asIso a⟩

end
end Fppf
end LinearAlgebraicGroups
