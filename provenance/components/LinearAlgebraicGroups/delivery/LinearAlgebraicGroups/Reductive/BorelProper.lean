import Specs.LinearAlgebraicGroups.Reductive.BorelProper
import Specs.LinearAlgebraicGroups.Solvable.BorelFixedPoint
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group
import LinearAlgebraicGroups.Affine.Components

import LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import LinearAlgebraicGroups.Solvable.BorelFixedPoint
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.BorelProper

open LinearAlgebraicGroups.Specs
open Specs.BorelProper
open Specs.GeometricBorelConjugacy
open Specs.GeometricRadicals (GeometricGroup baseChangedSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuotientEmbedding (Presentation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

open private projection_eq_iff represent_of_fppf
  from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private exists_rational_point from LinearAlgebraicGroups.Flag.SmoothOrbit
open private compareRepresentatives
  from LinearAlgebraicGroups.Flag.HomogeneousQuotient

variable {k : Type u} [Field k] {G : Specs.GroupScheme k}

private theorem descends {X Y Z : SchemeOver k} (q : X ⟶ Y) (f : X ⟶ Z)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (h : ∀ (T : SchemeOver k) (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃ p : Y ⟶ Z, q ≫ p = f := by
  have e {T : Scheme.{u}} (a b : T ⟶ X.left)
      (he : a ≫ q.left = b ≫ q.left) : a ≫ f.left = b ≫ f.left := by
    let T' : SchemeOver k := Over.mk (a ≫ X.hom)
    let a' : T' ⟶ X := Over.homMk a rfl
    let b' : T' ⟶ X := Over.homMk b (by
      change b ≫ X.hom = a ≫ X.hom
      rw [← Over.w q, ← Category.assoc, ← he, Category.assoc])
    exact congrArg Over.Hom.left (h T' a' b' (Over.OverMorphism.ext he))
  let p := EffectiveEpi.desc q.left f.left e
  have hp : q.left ≫ p = f.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  apply (cancel_epi q.left).mp
  rw [← Category.assoc, hp, Over.w, Over.w]

private theorem quotientDescends {H : ClosedSubgroup G} (Q : Presentation H)
    {Z : SchemeOver k} (f : G.X ⟶ Z)
    (hf : ∀ (T : SchemeOver k) (a b : T ⟶ G.X), a⁻¹ * b ∈ SubgroupSections H T →
      a ≫ f = b ≫ f) :
    ∃ p : Q.scheme ⟶ Z, Q.projection ≫ p = f := by
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  exact descends Q.projection f (fun T a b h ↦ hf T a b ((projection_eq_iff Q a b).mp h))

private theorem quotient_surjective_of_comp {X Y Z : SchemeOver k} (q : X ⟶ Y)
    (f : Y ⟶ Z) (h : Surjective (q ≫ f).left) : Surjective f.left := by
  exact ⟨Function.Surjective.of_comp h.1⟩

private theorem quotientProper_of_surjective {X Y : SchemeOver k} (f : X ⟶ Y)
    (hs : Surjective f.left) (hp : IsProper X.hom)
    (hsep : IsSeparated Y.hom) (hft : LocallyOfFiniteType Y.hom) :
    IsProper Y.hom := by
  letI := hs
  haveI : UniversallyClosed (f.left ≫ Y.hom) := by rw [Over.w]; exact hp.toUniversallyClosed
  exact (isProper_iff _).mpr ⟨hsep, UniversallyClosed.of_comp_surjective f.left Y.hom, hft⟩

private theorem quotientSeparatedFiniteType {H : ClosedSubgroup G} (Q : Presentation H) :
    IsSeparated Q.scheme.hom ∧ LocallyOfFiniteType Q.scheme.hom := by
  obtain ⟨V, _, _, _, j, hj⟩ := Q.quasiProjective
  letI := hj
  haveI : IsProper (Specs.ProjectiveSpaces.projectiveSpace k V).hom :=
    ProjectiveSpaces.projectiveSpaceProper k V
  rw [← Over.w j]
  exact ⟨inferInstance, inferInstance⟩

private theorem quotientMapExists {H J : ClosedSubgroup G}
    (Q : Presentation H) (R : Presentation J) (h : IsSubgroupOf H J) :
    ∃ f : Q.scheme ⟶ R.scheme, Q.projection ≫ f = R.projection := by
  obtain ⟨i, hi⟩ := h
  apply quotientDescends Q R.projection
  rintro T a b ⟨d, hd⟩
  apply (projection_eq_iff R a b).mpr
  refine ⟨d ≫ i.hom.hom, ?_⟩
  have hi' : i.hom.hom ≫ J.inclusion.hom.hom = H.inclusion.hom.hom :=
    congrArg (fun j : H.group ⟶ G ↦ j.hom.hom) hi
  change (d ≫ i.hom.hom) ≫ J.inclusion.hom.hom = _
  rwa [Category.assoc, hi']

private theorem rationalLift [IsAlgClosed k] {X Y : SchemeOver k} (q : X ⟶ Y)
    (hq : Surjective q.left) (hft : LocallyOfFiniteType q.left)
    (y : 𝟙_ (SchemeOver k) ⟶ Y) : ∃ x : 𝟙_ (SchemeOver k) ⟶ X, x ≫ q = y := by
  let D := pullback q y
  let p := pullback.snd q y
  have hp := (IsPullback.of_hasPullback q y).map (Over.forget _)
  haveI : Surjective p.left := MorphismProperty.of_isPullback (P := @Surjective) hp hq
  haveI : Nonempty (𝟙_ (SchemeOver k)).left := by
    change Nonempty (Spec (CommRingCat.of k))
    infer_instance
  haveI : Nonempty D.left := p.left.surjective.nonempty
  haveI : LocallyOfFiniteType p.left := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp hft
  haveI : LocallyOfFiniteType D.hom := by
    rw [← Over.w p]
    change LocallyOfFiniteType (p.left ≫ 𝟙 _)
    infer_instance
  obtain ⟨d⟩ := exists_rational_point D
  refine ⟨d ≫ pullback.fst q y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    toUnit_unique (d ≫ p) (𝟙 _), Category.id_comp]

private theorem proper_iff_baseChange (K : Type u) [Field K] [Algebra k K] (X : SchemeOver k)
    (hsep : IsSeparated X.hom) (hft : LocallyOfFiniteType X.hom) :
    IsProper X.hom ↔ IsProper ((baseChange k K).obj X).hom := by
  have hp : IsPullback (pullback.fst X.hom (fieldSpecMap k K))
      ((baseChange k K).obj X).hom X.hom (fieldSpecMap k K) := IsPullback.of_hasPullback _ _
  constructor
  · exact fun h ↦ MorphismProperty.of_isPullback (P := @IsProper) hp h
  · intro h
    have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (fieldSpecMap k K) := ⟨⟨⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩,
          inferInstance⟩, inferInstance⟩
    exact (isProper_iff _).mpr ⟨hsep, MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      hp.flip hf h.toUniversallyClosed, hft⟩

private theorem geometricSmooth (A : AffineAlgebraicGroup k) (hs : Smooth A.val.X.hom) :
    Smooth (GeometricGroup A).val.X.hom :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback A.val.X.hom (fieldSpecMap k (AlgebraicClosure k))) hs

private theorem geometricConnected (A : AffineAlgebraicGroup k)
    (hc : ConnectedSpace A.val.X.left) : ConnectedSpace (GeometricGroup A).val.X.left := by
  obtain ⟨E, H, q, i, h, _, _, hbase⟩ :=
    LinearAlgebraicGroups.identityComponentAndQuotient k A
  letI := hc
  have hr : Set.range i.hom.hom.left = Set.univ := by rw [h.identityComponent, PreconnectedSpace.connectedComponent_eq_univ]
  letI : Surjective i.hom.hom.left := ⟨Set.range_eq_univ.mp hr⟩
  letI := h.openImmersion
  haveI : IsIso i.hom.hom.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIso i.hom.hom := by
    haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map i.hom.hom) :=
      ‹IsIso i.hom.hom.left›
    exact isIso_of_reflects_iso i.hom.hom (Over.forget _)
  let j := (baseChange k (AlgebraicClosure k)).map i.hom.hom
  letI : GeometricallyConnected ((groupBaseChange k (AlgebraicClosure k)).obj H).X.hom :=
    (hbase (AlgebraicClosure k)).geometricallyConnected
  have hc' : ConnectedSpace ((groupBaseChange k (AlgebraicClosure k)).obj H).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := ((groupBaseChange k (AlgebraicClosure k)).obj H).X.hom)
  haveI : IsIso j.left := (Over.forget _).map_isIso j
  exact j.left.homeomorph.connectedSpace_iff.mp hc'

open private representedProjection_apply
  from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private actOnSection_naturality from LinearAlgebraicGroups.Flag.RightQuotientSheaf

private def quotientSection {H : ClosedSubgroup G} (Q : Presentation H) {T : SchemeOver k}
    (x : T ⟶ Q.scheme) :=
  Q.quotientIso.inv.hom.app (op T) (ULift.up x)

private def quotientAct {H : ClosedSubgroup G} (Q : Presentation H) {T : SchemeOver k}
    (a : T ⟶ G.X) (x : T ⟶ Q.scheme) : T ⟶ Q.scheme :=
  (Q.quotientIso.hom.hom.app (op T) (actOnSection H a (quotientSection Q x))).down

private theorem quotientSection_act {H : ClosedSubgroup G} (Q : Presentation H)
    {T : SchemeOver k} (a : T ⟶ G.X) (x : T ⟶ Q.scheme) :
    quotientSection Q (quotientAct Q a x) = actOnSection H a (quotientSection Q x) :=
  congrArg (fun f => f.hom.app (op T) (actOnSection H a (quotientSection Q x)))
    Q.quotientIso.hom_inv_id

private theorem quotientSection_injective {H : ClosedSubgroup G} (Q : Presentation H)
    {T : SchemeOver k} : Function.Injective (quotientSection Q (T := T)) := by
  intro a b h
  exact ULift.up.inj ((ConcreteCategory.bijective_of_isIso
    (Q.quotientIso.inv.hom.app (op T))).1 h)

private theorem quotientAct_one {H : ClosedSubgroup G} (Q : Presentation H) {T : SchemeOver k}
    (x : T ⟶ Q.scheme) : quotientAct Q 1 x = x := by
  apply quotientSection_injective Q
  rw [quotientSection_act, (rightQuotientActionLaws H (quotientSection Q x)).1]

private theorem quotientAct_mul {H : ClosedSubgroup G} (Q : Presentation H) {T : SchemeOver k}
    (a b : T ⟶ G.X) (x : T ⟶ Q.scheme) :
    quotientAct Q (a * b) x = quotientAct Q a (quotientAct Q b x) := by
  apply quotientSection_injective Q
  rw [quotientSection_act, quotientSection_act, quotientSection_act,
    (rightQuotientActionLaws H (quotientSection Q x)).2]

private theorem quotientSection_pull {H : ClosedSubgroup G} (Q : Presentation H)
    {T U : SchemeOver k} (f : U ⟶ T) (x : T ⟶ Q.scheme) :
    quotientSection Q (f ≫ x) = (rightQuotientSheaf H).obj.map f.op (quotientSection Q x) :=
  by
    let z : (schemeFppfSheaf Q.scheme).obj.obj (op T) := ⟨x⟩
    exact Q.quotientIso.inv.hom.naturality_apply f.op z

private theorem quotientAct_comp {H : ClosedSubgroup G} (Q : Presentation H)
    {T U : SchemeOver k} (f : U ⟶ T) (a : T ⟶ G.X) (x : T ⟶ Q.scheme) :
    f ≫ quotientAct Q a x = quotientAct Q (f ≫ a) (f ≫ x) := by
  apply quotientSection_injective Q
  rw [quotientSection_pull, quotientSection_act, actOnSection_naturality,
    quotientSection_act, quotientSection_pull]

private theorem quotientAct_projection {H : ClosedSubgroup G} (Q : Presentation H)
    {T : SchemeOver k} (a b : T ⟶ G.X) :
    quotientAct Q a (b ≫ Q.projection) = (a * b) ≫ Q.projection := by
  have h (c : T ⟶ G.X) : quotientSection Q (c ≫ Q.projection) = projectSection H c := by
    apply (ConcreteCategory.bijective_of_isIso (Q.quotientIso.hom.hom.app (op T))).1
    rw [representedProjection_apply]
    exact congrArg (fun f => f.hom.app (op T) (ULift.up (c ≫ Q.projection)))
      Q.quotientIso.inv_hom_id
  apply quotientSection_injective Q
  rw [quotientSection_act, h, h, rightQuotientActionOnLifts]

private theorem quotientAct_map {H J : ClosedSubgroup G} (Q : Presentation H)
    (R : Presentation J) (f : Q.scheme ⟶ R.scheme) (hf : Q.projection ≫ f = R.projection)
    {T : SchemeOver k} (a : T ⟶ G.X) (x : T ⟶ Q.scheme) :
    quotientAct Q a x ≫ f = quotientAct R a (x ≫ f) := by
  let p := pullback.snd Q.projection x
  have hp := (IsPullback.of_hasPullback Q.projection x).map (Over.forget _)
  haveI : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp Q.flat
  haveI : Surjective p.left := MorphismProperty.of_isPullback (P := @Surjective) hp Q.surjective
  haveI : LocallyOfFinitePresentation p.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp Q.finitePresentation
  haveI : Epi p := Over.epi_of_epi_left _
  apply (cancel_epi p).mp
  rw [← Category.assoc, quotientAct_comp, quotientAct_comp, ← Category.assoc,
    ← pullback.condition, quotientAct_projection, Category.assoc, hf, Category.assoc, hf,
    quotientAct_projection]

@[instance_reducible]
private def subgroupQuotientAction {B H : ClosedSubgroup G} (Q : Presentation H) :
    ModObj B.group.X Q.scheme where
  smul := quotientAct Q (fst _ _ ≫ B.inclusion.hom.hom) (snd _ _)
  one_smul := by
    change (η[B.group.X] ▷ Q.scheme) ≫ quotientAct Q _ _ = (λ_ Q.scheme).hom
    rw [quotientAct_comp, ← Category.assoc, whiskerRight_fst, whiskerRight_snd,
      Category.assoc, IsMonHom.one_hom, MonObj.one_eq_one,
      MonObj.comp_one, quotientAct_one, leftUnitor_hom]
  mul_smul := by
    let i := B.inclusion.hom.hom
    let act := quotientAct Q (fst B.group.X Q.scheme ≫ i) (snd _ _)
    change (μ[B.group.X] ▷ Q.scheme) ≫ act =
      (α_ B.group.X B.group.X Q.scheme).hom ≫ (B.group.X ◁ act) ≫ act
    simp only [act, quotientAct_comp, whiskerRight_fst_assoc, whiskerRight_snd,
      whiskerLeft_fst_assoc, whiskerLeft_snd, associator_hom_fst_assoc, MonObj.mul_eq_mul,
      associator_hom_snd_fst_assoc, associator_hom_snd_snd]
    simp only [← Category.assoc, MonObj.comp_mul, MonObj.mul_comp, quotientAct_mul]

private theorem fixed_subgroup_conjugate {B H : ClosedSubgroup G} (Q : Presentation H)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hf : IsFixedBy (subgroupQuotientAction (B := B) Q).smul (g ≫ Q.projection)) :
    ∃ b : B.group.X ⟶ H.group.X,
      b ≫ H.inclusion.hom.hom =
        (toUnit _ ≫ g)⁻¹ * B.inclusion.hom.hom * (toUnit _ ≫ g) := by
  let c : B.group.X ⟶ G.X := toUnit _ ≫ g
  have he : quotientAct Q B.inclusion.hom.hom (c ≫ Q.projection) = c ≫ Q.projection := by
    have hf' := congrArg ((lift (𝟙 B.group.X) (toUnit B.group.X)) ≫ ·) hf
    change lift (𝟙 B.group.X) (toUnit B.group.X) ≫
        (B.group.X ◁ (g ≫ Q.projection)) ≫
        quotientAct Q (fst _ _ ≫ B.inclusion.hom.hom) (snd _ _) =
      lift (𝟙 B.group.X) (toUnit B.group.X) ≫ snd _ _ ≫ g ≫ Q.projection at hf'
    rw [lift_whiskerLeft_assoc, quotientAct_comp, ← Category.assoc _ _ B.inclusion.hom.hom,
      lift_fst, Category.id_comp, lift_snd, lift_snd_assoc, ← Category.assoc _ g] at hf'
    exact hf'
  rw [quotientAct_projection] at he
  obtain ⟨b, hb⟩ := (projection_eq_iff Q c (B.inclusion.hom.hom * c)).mp he.symm
  exact ⟨b, by simpa [mul_assoc] using hb⟩


/-- The identity component is open in the stabilizer. Its image is an open singleton
in the quotient, and translation makes each closed point open. The Jacobson property
then gives a discrete underlying space, allowing the quotient to be finite even when
its scheme structure is nonreduced. -/
private theorem finite_component_quotient [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    {C : ClosedSubgroup A.val} (hc : IsReducedIdentityComponent C) (Q : Presentation C) :
    IsFinite Q.scheme.hom := by
  haveI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
  haveI : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
  letI : IsAffine A.val.X.left := A.property.1
  haveI : CompactSpace A.val.X.left := inferInstance
  haveI : IsNoetherian A.val.X.left := ⟨⟩
  haveI : LocallyOfFiniteType Q.scheme.hom := (quotientSeparatedFiniteType Q).2
  haveI : JacobsonSpace Q.scheme.left := LocallyOfFiniteType.jacobsonSpace Q.scheme.hom
  haveI : CompactSpace Q.scheme.left := Function.Surjective.compactSpace Q.projection.left.continuous Q.surjective.1
  letI := Q.flat
  letI := Q.finitePresentation
  let e : 𝟙_ (SchemeOver k) ⟶ A.val.X := 1
  let b := (e ≫ Q.projection).left (IsLocalRing.closedPoint k)
  have hC : IsOpen (Set.range C.inclusion.hom.hom.left) := by
    rw [hc.2]
    exact (LinearAlgebraicGroups.isClopenConnectedComponent _ _).2
  have he : C.inclusion.hom.hom ≫ Q.projection = toUnit C.group.X ≫ e ≫ Q.projection := by
    rw [← Category.assoc]
    apply ((projection_eq_iff Q (toUnit C.group.X ≫ e) C.inclusion.hom.hom).mpr ?_).symm
    have he' : toUnit C.group.X ≫ e = 1 := MonObj.comp_one _
    rw [he', inv_one, one_mul]
    refine ⟨𝟙 C.group.X, ?_⟩
    change 𝟙 _ ≫ C.inclusion.hom.hom = C.inclusion.hom.hom
    rw [Category.id_comp]
  have hpoint : IsOpen ({b} : Set Q.scheme.left) := by
    have heval : ∀ z : C.group.X.left, Q.projection.left (C.inclusion.hom.hom.left z) = b := by
      intro z
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
      change (e ≫ Q.projection).left ((toUnit C.group.X).left z) = _
      congr 1
      exact @Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance _ _
    have hne : Nonempty C.group.X.left := ⟨η[C.group.X].left (IsLocalRing.closedPoint k)⟩
    have himage : Q.projection.left '' Set.range C.inclusion.hom.hom.left = {b} := by
      letI := hne
      rw [← Set.range_comp, Set.range_eq_singleton]
      exact heval
    rw [← himage]
    exact Q.projection.left.isOpenMap _ hC
  have hopen (y : Q.scheme.left) (hy : IsClosed ({y} : Set Q.scheme.left)) :
      IsOpen ({y} : Set Q.scheme.left) := by
    let p : 𝟙_ (SchemeOver k) ⟶ Q.scheme := Over.homMk (pointOfClosedPoint Q.scheme.hom y hy)
      (pointOfClosedPoint_comp Q.scheme.hom y hy)
    obtain ⟨g, hg⟩ := rationalLift Q.projection Q.surjective
      (show LocallyOfFiniteType Q.projection.left from inferInstance) p
    let move (a : 𝟙_ (SchemeOver k) ⟶ A.val.X) :=
      quotientAct Q (toUnit Q.scheme ≫ a) (𝟙 Q.scheme)
    have hm (a d : 𝟙_ (SchemeOver k) ⟶ A.val.X) :
        move a ≫ move d = move (d * a) := by
      simp only [move, quotientAct_comp, Category.comp_id, comp_toUnit_assoc,
        ← quotientAct_mul, MonObj.comp_mul]
    have hone : move 1 = 𝟙 Q.scheme := by simp [move, MonObj.comp_one, quotientAct_one]
    let iso : Q.scheme ≅ Q.scheme := ⟨move g, move g⁻¹, by rw [hm, inv_mul_cancel, hone],
      by rw [hm, mul_inv_cancel, hone]⟩
    have hb : (e ≫ Q.projection) ≫ move g = p := by
      simp [move, quotientAct_comp, quotientAct_projection, e, hg, ← Category.assoc]
    have hb' : iso.hom.left b = y := by
      change (move g).left b = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb]
      exact pointOfClosedPoint_apply _ _ _ _
    rw [← hb', ← Set.image_singleton]
    haveI : IsIso iso.hom.left := ((Over.forget _).mapIso iso).isIso_hom
    exact iso.hom.left.isOpenMap _ hpoint
  have ht : ∀ y : Q.scheme.left, IsClosed ({y} : Set Q.scheme.left) := by
    have hO : IsOpen (closedPoints Q.scheme.left) := by
      rw [show closedPoints Q.scheme.left = ⋃ (y : closedPoints Q.scheme.left), {y.val} from by ext; simp]
      exact isOpen_iUnion fun y ↦ hopen y.val y.property
    intro y
    by_contra hy
    obtain ⟨z, hz, hz'⟩ := nonempty_inter_closedPoints
      (show (closedPoints Q.scheme.left)ᶜ.Nonempty from ⟨y, hy⟩)
      hO.isClosed_compl.isLocallyClosed
    exact hz hz'
  haveI : DiscreteTopology Q.scheme.left := discreteTopology_iff_isOpen_singleton.mpr
    (fun y ↦ hopen y (ht y))
  haveI : LocallyQuasiFinite Q.scheme.hom :=
    (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := Q.scheme.hom)).mpr
      (fun _ ↦ isDiscrete_iff_discreteTopology.mpr inferInstance)
  haveI : QuasiCompact Q.scheme.hom := (quasiCompact_iff_compactSpace _).mpr inferInstance
  exact IsFinite.of_locallyQuasiFinite _

/-- The fibre over the identity coset of `G/C → G/H` represents `H/C`. -/
private theorem subgroup_quotient_fiber {H : ClosedSubgroup G} (C : ClosedSubgroup H.group)
    (Q : Presentation (subgroupOfSubgroup H C)) (R : Presentation H)
    (f : Q.scheme ⟶ R.scheme) (hf : Q.projection ≫ f = R.projection) :
    let x : 𝟙_ (SchemeOver k) ⟶ R.scheme := (1 : _ ⟶ G.X) ≫ R.projection
    Nonempty (rightQuotientSheaf C ≅ schemeFppfSheaf (pullback f x)) := by
  intro x
  let D := pullback f x
  let j := pullback.fst f x
  let i := H.inclusion.hom.hom
  haveI := H.isClosedImmersion
  haveI : Mono i := Over.mono_of_mono_left _
  have hidentity {T : SchemeOver k} (g : T ⟶ G.X) :
      g ≫ R.projection = toUnit T ≫ x ↔ ∃ d : T ⟶ H.group.X, d ≫ i = g := by
    have h := projection_eq_iff R (1 : T ⟶ G.X) g
    rw [inv_one, one_mul] at h
    rw [show toUnit T ≫ x = (1 : T ⟶ G.X) ≫ R.projection by
      rw [show x = (1 : (𝟙_ (SchemeOver k)) ⟶ G.X) ≫ R.projection from rfl,
        ← Category.assoc, MonObj.comp_one], eq_comm]
    exact h
  let p : H.group.X ⟶ D := pullback.lift (i ≫ Q.projection) (toUnit _)
    (by rw [Category.assoc, hf]; exact (hidentity i).mpr ⟨𝟙 _, Category.id_comp _⟩)
  have hpj : p ≫ j = i ≫ Q.projection := pullback.lift_fst _ _ _
  have hp : IsPullback i p Q.projection j := by
    refine IsPullback.mk' hpj.symm (fun _ _ _ h _ ↦ (cancel_mono i).mp h) ?_
    intro T g d hd
    have hg : g ≫ R.projection = toUnit T ≫ x := by
      rw [← hf, ← Category.assoc, hd, Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ x) (Subsingleton.elim _ _)
    obtain ⟨l, hl⟩ := (hidentity g).mp hg
    refine ⟨l, hl, pullback.hom_ext ?_ (Subsingleton.elim _ _)⟩
    rw [Category.assoc, hpj, ← Category.assoc, hl, hd]
  have hp' := hp.map (Over.forget _)
  haveI : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp' Q.flat
  haveI : Surjective p.left := MorphismProperty.of_isPullback (P := @Surjective) hp' Q.surjective
  haveI : LocallyOfFinitePresentation p.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp' Q.finitePresentation
  obtain ⟨e, -⟩ := represent_of_fppf C p (by
    intro T a b
    have he : a ≫ p = b ≫ p ↔ (a ≫ i) ≫ Q.projection = (b ≫ i) ≫ Q.projection := by
      constructor
      · intro h
        simpa only [Category.assoc, hpj] using congrArg (· ≫ j) h
      · intro h
        apply pullback.hom_ext _ (Subsingleton.elim _ _)
        change (a ≫ p) ≫ j = (b ≫ p) ≫ j
        simpa only [Category.assoc, hpj] using h
    rw [he, projection_eq_iff]
    let φ := ((yonedaGrp.map H.inclusion).app (op T)).hom
    change (φ a)⁻¹ * φ b ∈ SubgroupSections (subgroupOfSubgroup H C) T ↔
      a⁻¹ * b ∈ SubgroupSections C T
    rw [← map_inv, ← map_mul]
    change (∃ t : T ⟶ C.group.X, t ≫ C.inclusion.hom.hom ≫ i = (a⁻¹ * b) ≫ i) ↔
      ∃ t : T ⟶ C.group.X, t ≫ C.inclusion.hom.hom = a⁻¹ * b
    simp only [← Category.assoc, cancel_mono])
  exact ⟨e⟩

/-- Pullback along the quotient projection trivializes the map between quotients.
On sections, a pair `(b, a)` in the pullback is sent to `(a, a⁻¹ • b)`. -/
private theorem subgroup_quotient_pullback {H J : ClosedSubgroup G}
    (Q : Presentation H) (R : Presentation J) (f : Q.scheme ⟶ R.scheme)
    (hf : Q.projection ≫ f = R.projection) :
    let x : 𝟙_ (SchemeOver k) ⟶ R.scheme := (1 : _ ⟶ G.X) ≫ R.projection
    let j := pullback.fst f x
    IsPullback (quotientAct Q prod.fst (prod.snd ≫ j))
      (prod.fst : G.X ⨯ pullback f x ⟶ G.X) f R.projection := by
  intro x j
  have base {T : SchemeOver k} (d : T ⟶ pullback f x) :
      (d ≫ j) ≫ f = (1 : T ⟶ G.X) ≫ R.projection := by
    rw [Category.assoc, show j = pullback.fst f x from rfl, pullback.condition, ← Category.assoc]
    change (d ≫ pullback.snd f x) ≫ (1 : (𝟙_ (SchemeOver k)) ⟶ G.X) ≫ R.projection = _
    rw [← Category.assoc, MonObj.comp_one]
  have undo {T : SchemeOver k} (a : T ⟶ G.X) (b : T ⟶ Q.scheme) :
      quotientAct Q a⁻¹ (quotientAct Q a b) = b := by
    rw [← quotientAct_mul, inv_mul_cancel, quotientAct_one]
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [quotientAct_map Q R f hf, base, quotientAct_projection, mul_one]
  · intro T p q h₁ h₂
    apply prod.hom_ext h₂
    apply pullback.hom_ext _ (Subsingleton.elim _ _)
    simpa only [quotientAct_comp, Category.assoc, ← h₂, undo] using
      congrArg (quotientAct Q (p ≫ prod.fst)⁻¹) h₁
  · intro T b a h
    have h' : quotientAct Q a⁻¹ b ≫ f = toUnit T ≫ x := by
      rw [quotientAct_map Q R f hf, h, quotientAct_projection, inv_mul_cancel]
      change _ = toUnit T ≫ (1 : (𝟙_ (SchemeOver k)) ⟶ G.X) ≫ R.projection
      rw [← Category.assoc, MonObj.comp_one]
    let d := pullback.lift (quotientAct Q a⁻¹ b) (toUnit T) h'
    refine ⟨prod.lift a d, ?_, prod.lift_fst _ _⟩
    rw [quotientAct_comp, prod.lift_fst, ← Category.assoc, prod.lift_snd,
      show d ≫ j = quotientAct Q a⁻¹ b from pullback.lift_fst _ _ _,
      ← quotientAct_mul, mul_inv_cancel, quotientAct_one]


private def innerMap (g : 𝟙_ (SchemeOver k) ⟶ G.X) : G ⟶ G := by
  let c := toUnit G.X ≫ g
  refine Grp.homMk'' (c * 𝟙 G.X * c⁻¹) ?_ ?_
  · rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv,
      MonObj.one_eq_one]
    group
  · have hc (T : SchemeOver k) (a : T ⟶ G.X) : a ≫ c = toUnit T ≫ g := by
      simp [c]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, hc, MonObj.mul_eq_mul,
      tensorHom_fst, tensorHom_snd]
    group

private theorem comp_innerMap (g : 𝟙_ (SchemeOver k) ⟶ G.X) {T : SchemeOver k}
    (f : T ⟶ G.X) :
    f ≫ (innerMap g).hom.hom = (toUnit T ≫ g) * f * (toUnit T ≫ g)⁻¹ := by
  change f ≫ ((toUnit G.X ≫ g) * 𝟙 G.X * (toUnit G.X ≫ g)⁻¹) = _
  simp [MonObj.comp_mul, GrpObj.comp_inv]

private def innerIso (g : 𝟙_ (SchemeOver k) ⟶ G.X) : G ≅ G where
  hom := innerMap g
  inv := innerMap g⁻¹
  hom_inv_id := by
    apply Grp.hom_ext
    change (innerMap g).hom.hom ≫ (innerMap g⁻¹).hom.hom = 𝟙 G.X
    rw [comp_innerMap, show (innerMap g).hom.hom =
      (toUnit G.X ≫ g) * 𝟙 G.X * (toUnit G.X ≫ g)⁻¹ from rfl, GrpObj.comp_inv]
    group
  inv_hom_id := by
    apply Grp.hom_ext
    change (innerMap g⁻¹).hom.hom ≫ (innerMap g).hom.hom = 𝟙 G.X
    rw [comp_innerMap, show (innerMap g⁻¹).hom.hom =
      (toUnit G.X ≫ g⁻¹) * 𝟙 G.X * (toUnit G.X ≫ g⁻¹)⁻¹ from rfl, GrpObj.comp_inv]
    group

private def transportSubgroup (B : ClosedSubgroup G) (e : G ≅ G) : ClosedSubgroup G := by
  letI := B.isClosedImmersion
  haveI : IsIso e.hom.hom.hom.left := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso e.hom
  exact ⟨B.group, B.inclusion ≫ e.hom, inferInstanceAs
    (IsClosedImmersion (B.inclusion.hom.hom.left ≫ e.hom.hom.hom.left))⟩

private theorem borel_transport {B : ClosedSubgroup G}
    (hB : IsBorel B) (e : G ≅ G) : IsBorel (transportSubgroup B e) := by
  refine ⟨hB.1, ?_⟩
  intro J hJ h
  obtain ⟨i, hi⟩ := h
  have hi' : i ≫ (transportSubgroup J e.symm).inclusion = B.inclusion := by
    change i ≫ J.inclusion ≫ e.inv = B.inclusion
    change i ≫ J.inclusion = B.inclusion ≫ e.hom at hi
    rw [← Category.assoc, hi, Category.assoc, e.hom_inv_id, Category.comp_id]
  obtain ⟨j, hj⟩ := hB.2 (transportSubgroup J e.symm) hJ ⟨i, hi'⟩
  refine ⟨j, ?_⟩
  change j ≫ B.inclusion ≫ e.hom = J.inclusion
  change j ≫ B.inclusion = J.inclusion ≫ e.inv at hj
  rw [← Category.assoc, hj, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem monHom_of_factor_subgroup {B H : ClosedSubgroup G} (b : B.group.X ⟶ H.group.X)
    (e : G ≅ G) (hb : b ≫ H.inclusion.hom.hom =
      (transportSubgroup B e).inclusion.hom.hom) :
    IsSubgroupOf (transportSubgroup B e) H := by
  letI := H.isClosedImmersion
  haveI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  refine ⟨Grp.homMk'' b ?_ ?_, ?_⟩
  · apply (cancel_mono H.inclusion.hom.hom).mp
    simp only [Category.assoc, hb, IsMonHom.one_hom]
  · apply (cancel_mono H.inclusion.hom.hom).mp
    rw [Category.assoc, hb, IsMonHom.mul_hom]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
    exact congrArg (fun v : B.group.X ⟶ G.X ↦ (v ⊗ₘ v) ≫ μ) hb.symm
  · exact Grp.hom_ext _ _ hb

private def rightTranslation (g : 𝟙_ (SchemeOver k) ⟶ G.X) : G.X ≅ G.X where
  hom := (𝟙 G.X) * (toUnit G.X ≫ g)
  inv := (𝟙 G.X) * (toUnit G.X ≫ g⁻¹)
  hom_inv_id := by
    simp only [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, comp_toUnit_assoc]
    group
  inv_hom_id := by
    simp only [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, comp_toUnit_assoc]
    group

private theorem proper_of_conjugate_quotient {B N : ClosedSubgroup G}
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (hg : ConjugatesSubgroups g B N)
    (Q : Presentation B) (R : Presentation N) (hp : IsProper R.scheme.hom) :
    IsProper Q.scheme.hom := by
  obtain ⟨e, he⟩ := hg
  let q := (rightTranslation g⁻¹).hom ≫ R.projection
  letI : Flat R.projection.left := R.flat
  letI : Surjective R.projection.left := R.surjective
  letI : LocallyOfFinitePresentation R.projection.left := R.finitePresentation
  haveI : IsIso (rightTranslation g⁻¹).hom.left :=
    (Over.forget _).map_isIso (rightTranslation g⁻¹).hom
  haveI : Flat q.left := inferInstanceAs (Flat ((rightTranslation g⁻¹).hom.left ≫ R.projection.left))
  haveI : Surjective q.left :=
    inferInstanceAs (Surjective ((rightTranslation g⁻¹).hom.left ≫ R.projection.left))
  haveI : LocallyOfFinitePresentation q.left :=
    inferInstanceAs (LocallyOfFinitePresentation ((rightTranslation g⁻¹).hom.left ≫ R.projection.left))
  have htest (T : SchemeOver k) (a b : T ⟶ G.X) :
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ SubgroupSections B T := by
    let c := toUnit T ≫ g
    have hconj (d : T ⟶ B.group.X) :
        d ≫ e.hom.hom.hom ≫ N.inclusion.hom.hom =
          c * (d ≫ B.inclusion.hom.hom) * c⁻¹ := by
      change e.hom.hom.hom ≫ N.inclusion.hom.hom =
        (toUnit B.group.X ≫ g) * B.inclusion.hom.hom * (toUnit B.group.X ≫ g)⁻¹ at he
      simp only [he, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc, c]
    have heq (d : T ⟶ G.X) : d ≫ (rightTranslation g⁻¹).hom = d * c⁻¹ := by
      simp [rightTranslation, MonObj.comp_mul, GrpObj.comp_inv, c]
    rw [show a ≫ q = (a * c⁻¹) ≫ R.projection by rw [← heq, Category.assoc],
      show b ≫ q = (b * c⁻¹) ≫ R.projection by rw [← heq, Category.assoc],
      projection_eq_iff]
    change (∃ t : T ⟶ N.group.X, t ≫ N.inclusion.hom.hom = (a * c⁻¹)⁻¹ * (b * c⁻¹)) ↔
      ∃ d : T ⟶ B.group.X, d ≫ B.inclusion.hom.hom = a⁻¹ * b
    rw [show (a * c⁻¹)⁻¹ * (b * c⁻¹) = c * (a⁻¹ * b) * c⁻¹ by group]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t ≫ e.inv.hom.hom, ?_⟩
      apply (MulAut.conj c).injective
      change c * ((t ≫ e.inv.hom.hom) ≫ B.inclusion.hom.hom) * c⁻¹ =
        c * (a⁻¹ * b) * c⁻¹
      have hcomp : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 N.group.X :=
        congrArg (fun f : N.group ⟶ N.group ↦ f.hom.hom) e.inv_hom_id
      rw [← hconj, Category.assoc, ← Category.assoc _ _ N.inclusion.hom.hom,
        hcomp, Category.id_comp]
      exact ht
    · rintro ⟨d, hd⟩
      exact ⟨d ≫ e.hom.hom.hom, by rw [Category.assoc, hconj, hd]⟩
  obtain ⟨E, _⟩ := represent_of_fppf B q htest
  let iso := compareRepresentatives Q E
  rw [← Over.w iso.hom]
  haveI : IsIso iso.hom.left := ((Over.forget _).mapIso iso).isIso_hom
  exact MorphismProperty.comp_mem @IsProper _ _ (inferInstanceAs (IsProper iso.hom.left)) hp

private theorem closed_flag_quotient_proper
    (horbit : ClosedFlagOrbitExists.{u}) (hstab : ClosedFlagStabilizerIsBorel.{u})
    {k : Type u} [Field k] [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) :
    ∃ (B : ClosedSubgroup A.val) (Q : Presentation B), IsBorel B ∧ IsProper Q.scheme.hom := by
  obtain ⟨n, v, F, x, O, ho⟩ := horbit A hs hc
  obtain ⟨C, hC, hB⟩ := hstab A hs hc F x O ho
  let H := O.stabilizer
  let B := subgroupOfSubgroup H C
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient k A B).1
  obtain ⟨R⟩ := (HomogeneousQuotient.homogeneousQuotient k A H).1
  obtain ⟨S⟩ := (HomogeneousQuotient.homogeneousQuotient k (closedSubgroupAlgebraicGroup H) C).1
  let j := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion F.action x
  haveI : IsClosedImmersion j.left := ho
  haveI : IsProper F.flags.scheme.hom := F.projective.proper
  haveI : IsProper O.orbit.hom := by rw [← Over.w j]; infer_instance
  let iso := compareRepresentatives R O.quotientIso
  haveI : IsIso iso.hom.left := ((Over.forget _).mapIso iso).isIso_hom
  have hR : IsProper R.scheme.hom := by rw [← Over.w iso.hom]; infer_instance
  obtain ⟨f, hf⟩ := quotientMapExists Q R ⟨C.inclusion, rfl⟩
  let x₀ : 𝟙_ (SchemeOver k) ⟶ R.scheme := (1 : _ ⟶ A.val.X) ≫ R.projection
  let D := pullback f x₀
  obtain ⟨E⟩ := subgroup_quotient_fiber C Q R f hf
  let Diso : S.scheme ≅ D := compareRepresentatives S E
  haveI : IsFinite S.scheme.hom := finite_component_quotient (closedSubgroupAlgebraicGroup H) hC S
  haveI : IsIso Diso.inv.left := ((Over.forget _).mapIso Diso).isIso_inv
  haveI : IsFinite D.hom := by rw [← Over.w Diso.inv]; infer_instance
  have hp := (subgroup_quotient_pullback Q R f hf).map (Over.forget _)
  have hprod := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A.val.X D)
  have hf' : IsFinite (prod.fst : A.val.X ⨯ D ⟶ A.val.X).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hprod.flip inferInstance
  haveI : QuasiCompact R.projection.left := by
    letI : IsAffine A.val.X.left := A.property.1
    letI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
    letI : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
    letI : IsNoetherian A.val.X.left := ⟨⟩
    infer_instance
  have hcl : UniversallyClosed f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) hp.flip
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨R.surjective, R.flat⟩, (show QuasiCompact R.projection.left from inferInstance)⟩ (by
        change UniversallyClosed (prod.fst : A.val.X ⨯ D ⟶ A.val.X).left
        letI := hf'
        infer_instance)
  have hcl' : UniversallyClosed Q.scheme.hom := by
    rw [← Over.w f]
    exact MorphismProperty.comp_mem _ _ _ hcl hR.toUniversallyClosed
  exact ⟨B, Q, hB, (isProper_iff _).mpr ⟨(quotientSeparatedFiniteType Q).1, hcl', (quotientSeparatedFiniteType Q).2⟩⟩

/-- Conditional properness of the right quotient by each geometric Borel. -/
theorem geometricBorelQuotientProper_conditional
    (_ : Specs.BorelFixedPoint.OverAlgClosed.{u})
    (_ : Specs.BorelFixedPoint.Split.{u})
    (_ : BorelExists.{u})
    (hconj : BorelsConjugate.{u})
    (horbit : ClosedFlagOrbitExists.{u})
    (hstab : ClosedFlagStabilizerIsBorel.{u})
    (_ : TorusContainedInBorel.{u}) : GeometricBorelQuotientProper.{u} := by
  intro k _ A hs hc B hB Q
  let A' := GeometricGroup A
  have hs' := geometricSmooth A hs
  have hc' := geometricConnected A hc
  obtain ⟨N, R, hN, hp⟩ := closed_flag_quotient_proper horbit hstab A' hs' hc'
  obtain ⟨g, hg⟩ := hconj A' hs' hc' B N hB hN
  exact proper_of_conjugate_quotient g hg Q R hp

/-- Conditional properness criterion for a quotient by a smooth closed subgroup. -/
theorem quotientProperIff_conditional
    (hfix : Specs.BorelFixedPoint.OverAlgClosed.{u})
    (hsplit : Specs.BorelFixedPoint.Split.{u})
    (hexists : BorelExists.{u})
    (hconj : BorelsConjugate.{u})
    (horbit : ClosedFlagOrbitExists.{u})
    (hstab : ClosedFlagStabilizerIsBorel.{u})
    (htorus : TorusContainedInBorel.{u}) : QuotientProperIff.{u} := by
  intro k _ A hs hc P _ Q
  let K := AlgebraicClosure k
  let A' := GeometricGroup A
  have hs' := geometricSmooth A hs
  have hc' := geometricConnected A hc
  obtain ⟨hp, E, hE⟩ := HomogeneousQuotient.quotientBaseChange k K Q
  let P' := baseChangedSubgroup K P hp
  obtain ⟨R⟩ := (HomogeneousQuotient.homogeneousQuotient K A' P').1
  let iso := compareRepresentatives R E
  haveI : IsIso iso.hom.left := ((Over.forget _).mapIso iso).isIso_hom
  have hproper : IsProper Q.scheme.hom ↔ IsProper R.scheme.hom := by
    rw [proper_iff_baseChange K Q.scheme (quotientSeparatedFiniteType Q).1 (quotientSeparatedFiniteType Q).2,
      ← Over.w iso.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) iso.hom.left _).symm
  rw [hproper]
  constructor
  · intro hr
    obtain ⟨B, hB⟩ := hexists A' hs' hc'
    have hn : Nonempty R.scheme.left :=
      ⟨((1 : 𝟙_ (SchemeOver K) ⟶ A'.val.X) ≫ R.projection).left (IsLocalRing.closedPoint K)⟩
    obtain ⟨Z, i, _, hi, ⟨z⟩⟩ :=
      hfix (closedSubgroupAlgebraicGroup B) R.scheme (subgroupQuotientAction (B := B) R)
        hB.1.1 hB.1.2.1 hB.1.2.2 hr hn
    obtain ⟨g, hg⟩ := rationalLift R.projection R.surjective
      (by letI := R.finitePresentation; infer_instance) (z ≫ i)
    have hz := (hi _ (z ≫ i)).mpr ⟨z, rfl⟩
    rw [← hg] at hz
    obtain ⟨b, hb⟩ := fixed_subgroup_conjugate R g hz
    let e := innerIso g⁻¹
    refine ⟨hp, transportSubgroup B e, borel_transport hB e, monHom_of_factor_subgroup b e ?_⟩
    change b ≫ P'.inclusion.hom.hom = B.inclusion.hom.hom ≫ (innerMap g⁻¹).hom.hom
    rw [comp_innerMap, GrpObj.comp_inv, inv_inv]
    exact hb
  · rintro ⟨hp', B, hB, hincl⟩
    have he : hp' = hp := Subsingleton.elim _ _
    subst hp'
    obtain ⟨S⟩ := (HomogeneousQuotient.homogeneousQuotient K A' B).1
    have hS := geometricBorelQuotientProper_conditional
      hfix hsplit hexists hconj horbit hstab htorus A hs hc B hB S
    obtain ⟨f, hf⟩ := quotientMapExists S R hincl
    haveI : Surjective f.left := quotient_surjective_of_comp S.projection f
      (hf.symm ▸ R.surjective)
    exact quotientProper_of_surjective f inferInstance hS
      (quotientSeparatedFiniteType R).1 (quotientSeparatedFiniteType R).2

end

end LinearAlgebraicGroups.BorelProper

universe v8_closure_ab0226e2dca86d9d_u0
theorem _root_.«LinearAlgebraicGroups».«BorelProper».«geometricBorelQuotientProper» : _root_.«LinearAlgebraicGroups».«Specs».«BorelProper».«GeometricBorelQuotientProper».{v8_closure_ab0226e2dca86d9d_u0} :=
  @_root_.«LinearAlgebraicGroups».«BorelProper».«geometricBorelQuotientProper_conditional».{v8_closure_ab0226e2dca86d9d_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_ab0226e2dca86d9d_u0})
theorem _root_.«LinearAlgebraicGroups».«BorelProper».«quotientProperIff» : _root_.«LinearAlgebraicGroups».«Specs».«BorelProper».«QuotientProperIff».{v8_closure_ab0226e2dca86d9d_u0} :=
  @_root_.«LinearAlgebraicGroups».«BorelProper».«quotientProperIff_conditional».{v8_closure_ab0226e2dca86d9d_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_ab0226e2dca86d9d_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_ab0226e2dca86d9d_u0})
