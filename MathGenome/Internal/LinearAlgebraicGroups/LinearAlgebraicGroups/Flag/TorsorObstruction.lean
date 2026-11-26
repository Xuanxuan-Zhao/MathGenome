import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FppfTorsors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.RightQuotientSheaf
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups.TorsorObstruction

open Specs (ClosedSubgroup GroupScheme fppfOver projectSection actOnSection
  rightQuotientSheaf rightQuotientProjection rightQuotientAction schemeFppfSheaf)
open Specs.Fppf Specs.TorsorObstruction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section TorsorMaps

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A B : Cᵒᵖ ⥤ GrpCat.{w}}

/-- Equivariance on sections for a map of sheaves and a change of acting group. -/
private def Equivariant (φ : A ⟶ B) (P : RightAction J A) (Q : RightAction J B)
    (f : P.sheaf.obj ⟶ Q.sheaf.obj) : Prop :=
  ∀ {U : C} (p : P.Section U) (a : A.obj (op U)),
    f.app (op U) (P.act p a) = Q.act (f.app (op U) p) (φ.app (op U) a)

private def torsorIso {P Q : Torsor J A}
    (f : P.1.sheaf.obj ⟶ Q.1.sheaf.obj) (hf : Equivariant (𝟙 A) P.1 Q.1 f) :
    RightActionIso P.1 Q.1 := by
  let f' : P.1.sheaf ⟶ Q.1.sheaf := ⟨f⟩
  have hinj : Presheaf.IsLocallyInjective J f :=
    Presheaf.isLocallyInjective_of_injective J f (fun U ↦ by
      intro p q hpq
      obtain ⟨a, ha⟩ := (P.2.1 U.unop p).2 q
      have h : Q.1.act (f.app U p) a = Q.1.act (f.app U p) 1 := by
        rw [Q.1.act_one]
        exact (hf p a).symm.trans (congrArg (f.app U) ha |>.trans hpq.symm)
      rw [(Q.2.1 U.unop (f.app U p)).1 h, P.1.act_one] at ha
      exact ha)
  have hsurj : Presheaf.IsLocallySurjective J f := by
    constructor
    intro U y
    apply J.superset_covering ?_ (P.2.2 U)
    rintro V g ⟨p⟩
    obtain ⟨a, ha⟩ := (Q.2.1 V (f.app (op V) p)).2 (Q.1.res g y)
    exact ⟨P.1.act p a, (hf p a).trans ha⟩
  have : IsIso f' := (Sheaf.isLocallyBijective_iff_isIso f').1 ⟨hinj, hsurj⟩
  exact ⟨asIso f', hf⟩

private lemma eq_of_local {F : Sheaf J (Type w)} {U : C} {x y : F.obj.obj (op U)}
    {R : Sieve U} (hR : R ∈ J U)
    (h : ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, R f → F.obj.map f.op x = F.obj.map f.op y) :
    x = y :=
  (F.property.isSheafFor R hR).isSeparatedFor.ext (fun _ _ hf ↦ h hf)

/-- A natural function on the sections of a torsor that is constant along its
action descends to the base. -/
private lemma descendAlongTorsor {P : Torsor J A} {F : Sheaf J (Type w)}
    {T : C} (hT : IsTerminal T) (f : P.1.sheaf.obj ⟶ F.obj)
    (hf : ∀ {U : C} (p : P.1.Section U) (a : A.obj (op U)),
      f.app (op U) (P.1.act p a) = f.app (op U) p) :
    ∃ x : F.obj.obj (op T), ∀ {U : C} (p : P.1.Section U),
      F.obj.map (hT.from U).op x = f.app (op U) p := by
  classical
  have const {U : C} (p q : P.1.Section U) : f.app (op U) p = f.app (op U) q := by
    obtain ⟨a, rfl⟩ := (P.2.1 U p).2 q
    exact (hf p a).symm
  let R := P.1.sectionSieve T
  let t : Presieve.FamilyOfElements F.obj R.arrows := fun U g hg ↦
    f.app (op U) (Classical.choice hg)
  have ht : t.Compatible := by
    intro U V W g h a b ha hb e
    change F.obj.map g.op (f.app (op U) (Classical.choice ha)) =
      F.obj.map h.op (f.app (op V) (Classical.choice hb))
    rw [← f.naturality_apply, ← f.naturality_apply]
    exact const _ _
  obtain ⟨x, hx, _⟩ := F.property.isSheafFor R (P.2.2 T) t ht
  exact ⟨x, fun {U} p ↦ (hx (hT.from U) ⟨p⟩).trans (const _ p)⟩

variable [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  (φ : A ⟶ B) {P : Torsor J A} {Q : Torsor J B}

private def contractedUnit : P.1.sheaf.obj ⟶ contractedPresheaf φ P.1 where
  app U := ↾fun p ↦ contractedPair φ P.1 (U := U.unop) p 1
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro p
    change Quotient.mk _ (P.1.sheaf.obj.map f p, (1 : B.obj V)) =
      Quotient.mk _ (P.1.sheaf.obj.map f p, B.map f 1)
    rw [map_one]

private def contractedMap {R : Torsor J B}
    (f : P.1.sheaf.obj ⟶ R.1.sheaf.obj) (hf : Equivariant φ P.1 R.1 f) :
    contractedPresheaf φ P.1 ⟶ R.1.sheaf.obj where
  app U := ↾(Quotient.lift (fun p ↦ R.1.act (f.app U p.1) p.2) (by
    rintro ⟨p,b⟩ ⟨q,c⟩ ⟨a, ha, hbc⟩
    change R.1.act (f.app U p) b = R.1.act (f.app U q) c
    change P.1.act p a = q at ha
    change φ.app U a * c = b at hbc
    rw [← ha, show f.app U (P.1.act p a) = _ from hf p a, R.1.act_mul, hbc]))
  naturality U V g := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Quotient.inductionOn p ?_
    rintro ⟨a,b⟩
    change R.1.act (f.app V (P.1.sheaf.obj.map g a)) (B.map g b) =
      R.1.sheaf.obj.map g (R.1.act (f.app U a) b)
    exact congrArg (fun r ↦ R.1.act r (B.map g b)) (f.naturality_apply g a) |>.trans
      (R.1.map_act g.unop (f.app U a) b).symm

private lemma extensionUniversal
    (E : Q.1.sheaf ≅ contractedProduct J φ P.1)
    (hE : ∀ (U : C) (p : P.1.Section U) (b c : B.obj (op U)),
      let j := (toSheafify J (contractedPresheaf φ P.1)).app (op U)
      E.hom.hom.app (op U) (Q.1.act (E.inv.hom.app (op U) (j (contractedPair φ P.1 p b))) c)
        = j (contractedPair φ P.1 p (b * c))) :
    (∃ f : P.1.sheaf.obj ⟶ Q.1.sheaf.obj, Equivariant φ P.1 Q.1 f) ∧
    ∀ {R : Torsor J B} (f : P.1.sheaf.obj ⟶ R.1.sheaf.obj), Equivariant φ P.1 R.1 f →
      Nonempty (RightActionIso Q.1 R.1) := by
  let D := contractedPresheaf φ P.1
  let j := toSheafify J D
  have EI (U : C) (x : Q.1.Section U) :
      E.inv.hom.app (op U) (E.hom.hom.app (op U) x) = x := by
    exact congrArg (fun (f : Q.1.sheaf ⟶ Q.1.sheaf) ↦ f.hom.app (op U) x) E.hom_inv_id
  have IE (U : C) (y : (contractedProduct J φ P.1).obj.obj (op U)) :
      E.hom.hom.app (op U) (E.inv.hom.app (op U) y) = y := by
    exact congrArg (fun f ↦ f.hom.app (op U) y) E.inv_hom_id
  constructor
  · refine ⟨contractedUnit φ ≫ j ≫ E.inv.hom, ?_⟩
    intro U p a
    change E.inv.hom.app (op U) (j.app (op U) (contractedPair φ P.1 (P.1.act p a) 1)) =
      Q.1.act (E.inv.hom.app (op U) (j.app (op U) (contractedPair φ P.1 p 1))) (φ.app (op U) a)
    have he : contractedPair φ P.1 (P.1.act p a) 1 =
        contractedPair φ P.1 p (φ.app (op U) a) := by
      symm
      exact Quotient.sound ⟨a, rfl, mul_one _⟩
    rw [he]
    simpa only [one_mul, EI] using congrArg (E.inv.hom.app (op U)) (hE U p 1 (φ.app (op U) a)).symm
  · intro R f hf
    let l := sheafifyLift J (contractedMap φ f hf) R.1.sheaf.property
    have hl (U : C) (p : P.1.Section U) (b : B.obj (op U)) :
        l.app (op U) (j.app (op U) (contractedPair φ P.1 p b)) = R.1.act (f.app (op U) p) b := by
      exact congrArg (fun t : D ⟶ R.1.sheaf.obj ↦ t.app (op U) (contractedPair φ P.1 p b))
        (toSheafify_sheafifyLift J (contractedMap φ f hf) R.1.sheaf.property)
    let F := E.hom.hom ≫ l
    have hF : Equivariant (𝟙 B) Q.1 R.1 F := by
      intro U x b
      apply eq_of_local (F := R.1.sheaf) (Presheaf.imageSieve_mem J j (E.hom.hom.app (op U) x))
      intro V g hg
      obtain ⟨z, hz⟩ := hg
      obtain ⟨⟨p,c⟩, rfl⟩ := Quotient.exists_rep z
      change j.app (op V) (contractedPair φ P.1 p c) =
        (contractedProduct J φ P.1).obj.map g.op (E.hom.hom.app (op U) x) at hz
      have hx : Q.1.res g x =
          E.inv.hom.app (op V) (j.app (op V) (contractedPair φ P.1 p c)) := by
        rw [hz, ← E.hom.hom.naturality_apply, EI]
      rw [← F.naturality_apply, Q.1.map_act]
      change F.app (op V) (Q.1.act (Q.1.res g x) (B.map g.op b)) =
        R.1.res g (R.1.act (F.app (op U) x) b)
      rw [show R.1.res g (R.1.act (F.app (op U) x) b) = _ from R.1.map_act g _ _,
        ← F.naturality_apply]
      change l.app (op V) (E.hom.hom.app (op V) (Q.1.act (Q.1.res g x) (B.map g.op b))) =
        R.1.act (l.app (op V) (E.hom.hom.app (op V) (Q.1.res g x))) (B.map g.op b)
      rw [hx, hE, hl, IE, hl, R.1.act_mul]
    exact ⟨torsorIso F hF⟩

end TorsorMaps

section Field

variable {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)

local notation "S" => fieldBase k
local notation "T" => fieldTest k
local notation "Jₖ" => torsorTopology S
local notation "Aₕ" => groupSections S H.group
local notation "Aᵍ" => groupSections S G

private abbrev inclusion := Specs.Fppf.groupSectionsMap S H.inclusion

private lemma schemeExtensionUniversal {P : FppfTorsor S H.group} {Q : FppfTorsor S G}
    (hQ : IsStructureGroupExtension S H.inclusion P Q) :
    (∃ f : P.1.sheaf.obj ⟶ Q.1.sheaf.obj, Equivariant (inclusion H) P.1 Q.1 f) ∧
    ∀ {R : FppfTorsor S G} (f : P.1.sheaf.obj ⟶ R.1.sheaf.obj),
      Equivariant (inclusion H) P.1 R.1 f → Nonempty (RightActionIso Q.1 R.1) := by
  obtain ⟨E, hE⟩ := hQ
  exact extensionUniversal (inclusion H) E hE

/-- On cohomology classes, extend a right torsor by the given subgroup inclusion. -/
def extendClass : H1fppf k H.group → H1fppf k G :=
  Quotient.map (Fppf.extendStructureGroup H.inclusion) (by
    intro P P' h
    obtain ⟨e⟩ := h
    obtain ⟨f, hf⟩ := (schemeExtensionUniversal H
      (Fppf.extendStructureGroup_spec H.inclusion P')).1
    apply (schemeExtensionUniversal H (Fppf.extendStructureGroup_spec H.inclusion P)).2
      (e.iso.hom.hom ≫ f)
    intro U p a
    change f.app (op U) (e.iso.hom.hom.app (op U) (P.1.act p a)) = _
    rw [e.equivariant]
    exact hf _ _)

theorem extendClass_spec : IsExtensionMap H (extendClass H) := by
  intro P Q hQ
  obtain ⟨f, hf⟩ := (schemeExtensionUniversal H hQ).1
  exact Quotient.sound ((schemeExtensionUniversal H (Fppf.extendStructureGroup_spec H.inclusion P)).2 f hf)

private lemma extendClass_eq_neutral_iff
    (hG : Presieve.IsSheaf Jₖ (Aᵍ ⋙ forget GrpCat)) (P : FppfTorsor S H.group) :
    extendClass H (Quotient.mk _ P) = neutralClass hG ↔
      ∃ f : P.1.sheaf.obj ⟶ (regularAction hG).sheaf.obj,
        Equivariant (inclusion H) P.1 (regularAction hG) f := by
  have hQ := schemeExtensionUniversal H (Fppf.extendStructureGroup_spec H.inclusion P)
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    obtain ⟨f, hf⟩ := hQ.1
    refine ⟨f ≫ e.iso.hom.hom, ?_⟩
    intro U p a
    change e.iso.hom.hom.app (op U) (f.app (op U) (P.1.act p a)) = _
    rw [hf p a]
    exact e.equivariant _ _
  · rintro ⟨f, hf⟩
    exact Quotient.sound (hQ.2 (R := regularTorsor hG) f hf)

private lemma extendClass_neutral (hH : Presieve.IsSheaf Jₖ (Aₕ ⋙ forget GrpCat))
    (hG : Presieve.IsSheaf Jₖ (Aᵍ ⋙ forget GrpCat)) : extendClass H (neutralClass hH) = neutralClass hG := by
  apply (extendClass_eq_neutral_iff H hG (regularTorsor hH)).2
  refine ⟨Functor.whiskerRight (inclusion H) (forget GrpCat), ?_⟩
  intro U a b
  let a' : (Aₕ).obj (op U) := a
  let b' : (Aₕ).obj (op U) := b
  exact map_mul ((inclusion H).app (op U)).hom a' b'

private theorem fibreIsTorsor (x : RationalPoints H) : IsTorsor (quotientFibreAction H x) := by
  have hclosed : AlgebraicGeometry.IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  constructor
  · intro U p
    change FibreSection H x U at p
    constructor
    · intro a b hab
      let a' : U.left ⟶ H.group.X := a.down
      let b' : U.left ⟶ H.group.X := b.down
      have he : p.val.down * (a' ≫ H.inclusion.hom.hom) =
          p.val.down * (b' ≫ H.inclusion.hom.hom) :=
        congrArg (fun t : FibreSection H x U ↦ t.val.down) hab
      have h : a' = b' := (cancel_mono H.inclusion.hom.hom).mp (mul_left_cancel he)
      exact ULift.ext h
    · intro q
      change FibreSection H x U at q
      obtain ⟨a, ha⟩ := (rightQuotientProjectionEquality H p.val.down q.val.down).1
        (p.property.trans q.property.symm)
      refine ⟨ULift.up a, Subtype.ext (ULift.ext ?_)⟩
      change p.val.down * (a ≫ H.inclusion.hom.hom) = q.val.down
      rw [ha, mul_inv_cancel_left]
  · intro U
    let q := (rightQuotientProjection H).hom
    let y := (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op x
    have : Presheaf.IsLocallySurjective (fppfOver k) q := rightQuotientLocalLifts H
    apply (Jₖ).superset_covering ?_ ((fppfOver k).overEquiv_symm_mem_over U _
      (Presheaf.imageSieve_mem (fppfOver k) q y))
    intro V f hf
    obtain ⟨⟨g⟩, hg⟩ := (Sieve.overEquiv_symm_iff _ _).1 hf
    refine ⟨(⟨ULift.up g, ?_⟩ : FibreSection H x V)⟩
    change projectSection H g = (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from V).left.op x
    change projectSection H g = (rightQuotientSheaf H).obj.map f.left.op y at hg
    rw [hg, ← Functor.map_comp_apply, ← op_comp]
    simp only [Over.mkIdTerminal_from_left, Over.w]

/-- The right fppf torsor which is the fibre of the quotient over a rational point. -/
def fibreTorsor (x : RationalPoints H) : FppfTorsor S H.group :=
  ⟨quotientFibreAction H x, fibreIsTorsor H x⟩

/-- The pointed-set boundary sends a rational quotient point to its fibre torsor. -/
def boundary (x : RationalPoints H) : H1fppf k H.group :=
  Quotient.mk _ (fibreTorsor H x)

private lemma cosetMap_injective : Function.Injective (rationalCosetMap H) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H g =>
    induction b using QuotientGroup.induction_on with
    | H g' =>
      intro h
      change projectSection H g = projectSection H g' at h
      exact QuotientGroup.eq.mpr ((rightQuotientProjectionEquality H g g').1 h)

private lemma mem_range_cosetMap_iff
    (hH : Presieve.IsSheaf Jₖ (Aₕ ⋙ forget GrpCat)) (x : RationalPoints H) :
    x ∈ Set.range (rationalCosetMap H) ↔ boundary H x = neutralClass hH := by
  rw [show boundary H x = _ ↔ Nonempty ((fibreTorsor H x).1.Section T) from
    Fppf.rationalPointCriterion hH (fibreTorsor H x)]
  constructor
  · rintro ⟨a, rfl⟩
    induction a using QuotientGroup.induction_on with
    | H g =>
      refine ⟨(⟨ULift.up g, ?_⟩ : FibreSection H _ T)⟩
      change projectSection H g = (rightQuotientSheaf H).obj.map
        (Over.mkIdTerminal.from T).left.op (projectSection H g)
      simp
  · rintro ⟨p⟩
    change FibreSection H x T at p
    have hp := p.property
    change projectSection H p.val.down =
      (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from T).left.op x at hp
    refine ⟨QuotientGroup.mk p.val.down, ?_⟩
    change projectSection H p.val.down = x
    simpa using hp

private def fibreInclusion (x : RationalPoints H) :
    (fibreTorsor H x).1.sheaf.obj ⟶ (Aᵍ ⋙ forget GrpCat) where
  app U := ↾fun p ↦ (show FibreSection H x U.unop from p).val
  naturality _ _ _ := rfl

private abbrev fibreLift {x : RationalPoints H} {U : Over S}
    (p : (fibreTorsor H x).1.Section U) : U.left ⟶ G.X :=
  (show FibreSection H x U from p).val.down

private lemma fibreLift_spec {x : RationalPoints H} {U : Over S}
    (p : (fibreTorsor H x).1.Section U) :
    projectSection H (fibreLift H p) =
      (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op x :=
  (show FibreSection H x U from p).property

private lemma mem_range_boundary_iff
    (hG : Presieve.IsSheaf Jₖ (Aᵍ ⋙ forget GrpCat)) (c : H1fppf k H.group) :
    c ∈ Set.range (boundary H) ↔ extendClass H c = neutralClass hG := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (extendClass_eq_neutral_iff H hG (fibreTorsor H x)).2
      ⟨fibreInclusion H x, fun _ _ ↦ rfl⟩
  · refine Quotient.inductionOn c ?_
    intro P h
    obtain ⟨f, hf⟩ := (extendClass_eq_neutral_iff H hG P).1 h
    let q := fibreProjection H
    have hq : ∀ {U : Over S} (p : P.1.Section U) (a : (Aₕ).obj (op U)),
        (f ≫ q).app (op U) (P.1.act p a) = (f ≫ q).app (op U) p := by
      intro U p a
      change q.app (op U) (f.app (op U) (P.1.act p a)) = _
      rw [hf p a]
      let g : U.left ⟶ G.X := (f.app (op U) p).down
      let b : U.left ⟶ H.group.X := a.down
      exact projectSection_mul_inclusion H g b
    obtain ⟨x, hx⟩ := descendAlongTorsor Over.mkIdTerminal (f ≫ q) hq
    let m : P.1.sheaf.obj ⟶ (fibreTorsor H x).1.sheaf.obj := {
      app U := ↾fun p ↦ (⟨f.app U p, (hx p).symm⟩ : FibreSection H x U.unop)
      naturality U V g := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Subtype.ext
        change f.app V (P.1.sheaf.obj.map g p) =
          (regularAction hG).sheaf.obj.map g (f.app U p)
        exact f.naturality_apply g p
    }
    have hm : Equivariant (𝟙 Aₕ) P.1 (fibreTorsor H x).1 m := by
      intro U p a
      exact Subtype.ext (hf p a)
    exact ⟨x, Quotient.sound ⟨(torsorIso m hm).symm⟩⟩

open private actOnSection_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.RightQuotientSheaf

private lemma boundary_eq_iff_orbit (x y : RationalPoints H) :
    boundary H x = boundary H y ↔ ∃ g : S ⟶ G.X, actOnSection H g x = y := by
  let P := fibreTorsor H x
  let Q := fibreTorsor H y
  constructor
  · intro he
    obtain ⟨e⟩ := Quotient.exact he
    let m : P.1.sheaf.obj ⟶ Aᵍ ⋙ forget GrpCat := {
      app U := ↾fun p ↦ ULift.up
        (fibreLift H (e.iso.hom.hom.app U p) * (fibreLift H p)⁻¹)
      naturality U V f := by
        apply ConcreteCategory.hom_ext
        intro p
        apply ULift.ext
        have he := e.iso.hom.hom.naturality_apply f p
        change (fibreLift H (e.iso.hom.hom.app V (P.1.sheaf.obj.map f p)) *
          (f.unop.left ≫ fibreLift H p)⁻¹) =
          f.unop.left ≫ (fibreLift H (e.iso.hom.hom.app U p) * (fibreLift H p)⁻¹)
        rw [he, MonObj.comp_mul, GrpObj.comp_inv]
        rfl
    }
    have hm : ∀ {U : Over S} (p : P.1.Section U) (a : (Aₕ).obj (op U)),
        m.app (op U) (P.1.act p a) = m.app (op U) p := by
      intro U p a
      apply ULift.ext
      change fibreLift H (e.iso.hom.hom.app (op U) (P.1.act p a)) *
        (fibreLift H (P.1.act p a))⁻¹ = _
      rw [e.equivariant]
      let b : U.left ⟶ H.group.X := a.down
      let z := b ≫ H.inclusion.hom.hom
      change (fibreLift H (e.iso.hom.hom.app (op U) p) * z) * (fibreLift H p * z)⁻¹ =
        fibreLift H (e.iso.hom.hom.app (op U) p) * (fibreLift H p)⁻¹
      simp [mul_inv_rev, mul_assoc]
    let FG := (regularAction (Fppf.schemeGroupSectionsAreSheaf S G)).sheaf
    obtain ⟨g, hg⟩ := descendAlongTorsor (F := FG) Over.mkIdTerminal m hm
    refine ⟨g.down, ?_⟩
    let F := (fieldQuotient (k := k)).obj (rightQuotientSheaf H)
    apply eq_of_local (F := F) (P.2.2 T)
    rintro U f ⟨p⟩
    have ht : f = Over.mkIdTerminal.from U := Over.mkIdTerminal.hom_ext _ _
    subst f
    have h₁ := fibreLift_spec H p
    have h₂ := fibreLift_spec H (e.iso.hom.hom.app (op U) p)
    have hg' : (Over.mkIdTerminal.from U).left ≫ (show S ⟶ G.X from g.down) =
        fibreLift H (e.iso.hom.hom.app (op U) p) * (fibreLift H p)⁻¹ :=
      congrArg ULift.down (hg p)
    change (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op
      (actOnSection H g.down x) =
        (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op y
    rw [actOnSection_naturality, hg', ← h₁, rightQuotientActionOnLifts, inv_mul_cancel_right, h₂]
  · rintro ⟨g, rfl⟩
    let m : P.1.sheaf.obj ⟶ (fibreTorsor H (actOnSection H g x)).1.sheaf.obj := {
      app U := ↾fun p ↦ (⟨ULift.up ((Over.mkIdTerminal.from U.unop).left ≫ g * fibreLift H p),
        by
          change projectSection H (((Over.mkIdTerminal.from U.unop).left ≫ g) * fibreLift H p) =
            (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U.unop).left.op (actOnSection H g x)
          rw [actOnSection_naturality, ← fibreLift_spec H p, rightQuotientActionOnLifts]⟩ :
            FibreSection H (actOnSection H g x) U.unop)
      naturality U V f := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Subtype.ext
        apply ULift.ext
        change ((Over.mkIdTerminal.from V.unop).left ≫ g) *
          (f.unop.left ≫ fibreLift H p) =
          f.unop.left ≫ (((Over.mkIdTerminal.from U.unop).left ≫ g) * fibreLift H p)
        rw [MonObj.comp_mul, ← Category.assoc, Over.mkIdTerminal_from_left,
          Over.mkIdTerminal_from_left, Over.w]
    }
    have hm : Equivariant (𝟙 Aₕ) P.1 (fibreTorsor H (actOnSection H g x)).1 m := by
      intro U p a
      apply Subtype.ext
      apply ULift.ext
      let b : U.left ⟶ H.group.X := a.down
      change ((Over.mkIdTerminal.from U).left ≫ g) * (fibreLift H p * (b ≫ H.inclusion.hom.hom)) =
        (((Over.mkIdTerminal.from U).left ≫ g) * fibreLift H p) * (b ≫ H.inclusion.hom.hom)
      exact (mul_assoc _ _ _).symm
    exact Quotient.sound ⟨torsorIso m hm⟩

end Field

/-- The two neutral fibres and the orbit relation for a homogeneous fppf quotient. -/
theorem pointedExactness : PointedExactness.{u} := by
  intro k _ G H
  let hH := fieldGroupSectionsAreSheaf H.group
  let hG := fieldGroupSectionsAreSheaf G
  exact ⟨boundary H, extendClass H, fun x ↦ ⟨(fibreTorsor H x).2, rfl⟩, extendClass_spec H,
    cosetMap_injective H, (mem_range_cosetMap_iff H hH _).1 ⟨QuotientGroup.mk 1, rfl⟩,
    extendClass_neutral H hH hG, Set.ext (mem_range_cosetMap_iff H hH),
    Set.ext (mem_range_boundary_iff H hG), boundary_eq_iff_orbit H⟩

theorem rationalPointsOfPresentation : RationalPointsOfPresentation.{u} := by
  intro k _ G H Q
  let f := Q.quotientIso.hom.hom
  let e : RationalPoints H ≃ (fieldBase k ⟶ Q.scheme) :=
    (asIso (f.app (op (fieldBase k)))).toEquiv.trans Equiv.ulift
  have hq {U : SchemeOver k} (g : U ⟶ G.X) :
      f.app (op U) (projectSection H g) = ULift.up (g ≫ Q.projection) :=
    congrArg (fun m ↦ m.hom.app (op U) (ULift.up g)) Q.quotientProjection
  refine ⟨e, fun g ↦ congrArg ULift.down (hq g), ?_⟩
  intro x U g
  have hn := f.naturality_apply (Over.mkIdTerminal.from U).left.op x
  change f.app (op U.left)
    ((rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op x) =
      ULift.up ((Over.mkIdTerminal.from U).left ≫ e x) at hn
  simp only [Over.mkIdTerminal_from_left] at hn ⊢
  constructor
  · intro h
    exact ULift.up.inj ((hq g).symm.trans ((congrArg (f.app (op U.left)) h).trans hn))
  · intro h
    apply (ConcreteCategory.bijective_of_isIso (f.app (op U.left))).1
    exact (hq g).trans ((congrArg ULift.up h).trans hn.symm)

end

end LinearAlgebraicGroups.TorsorObstruction
