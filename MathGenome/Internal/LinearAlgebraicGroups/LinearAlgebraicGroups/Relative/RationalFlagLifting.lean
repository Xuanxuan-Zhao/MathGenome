import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RationalFlagLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Lang
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Relative.RationalFlagLifting

open _root_.LinearAlgebraicGroups.Specs
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter)
open Specs.Fppf (fieldBase)
open Specs.HomogeneousQuotient (rightMultiplication)
open Specs.QuotientEmbedding (Presentation)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Relative.RationalDensity (GeometricallyDenseRationalPoints rationalPointOver)
open Specs.TorsorObstruction
open LinearAlgebraicGroups.CocharacterDynamics

open private multiply_isOpenImmersion from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private actOnSection_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.RightQuotientSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : GroupScheme k}

private def sameSubgroupIso {P H : ClosedSubgroup G} (h : SameSubgroup P H) :
    {e : P.group ≅ H.group // e.hom ≫ H.inclusion = P.inclusion} := by
  let f := h.1.choose
  let g := h.2.choose
  have hf : f ≫ H.inclusion = P.inclusion := h.1.choose_spec
  have hg : g ≫ P.inclusion = H.inclusion := h.2.choose_spec
  let F := Grp.forget (SchemeOver k)
  have inclusionMono (B : ClosedSubgroup G) : Mono B.inclusion := by
    letI := B.isClosedImmersion
    haveI : Mono (F.map B.inclusion) := Over.mono_of_mono_left B.inclusion.hom.hom
    exact F.mono_of_mono_map (show Mono (F.map B.inclusion) from inferInstance)
  letI := inclusionMono P
  letI := inclusionMono H
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (cancel_mono P.inclusion).mp
    simp [Category.assoc, hg, hf]
  · apply (cancel_mono H.inclusion).mp
    simp [Category.assoc, hf, hg]

/-- Replacing the limit parabolic by the original closed subgroup preserves the open cell. -/
private theorem parabolicCellOpen (A : AffineAlgebraicGroup k) [Smooth A.val.X.hom]
    (P : ClosedSubgroup A.val) {c : Cocharacter A.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hP : SameSubgroup P D.parabolic) :
    IsOpenImmersion (multiplyFactors E.contracting.inclusion P.inclusion).left := by
  obtain ⟨e, he⟩ := sameSubgroupIso hP
  let F := Grp.forget (SchemeOver k)
  let V := E.contracting.group.X
  let e' : P.group.X ⟶ D.parabolic.group.X := F.map e.hom
  let a : V ⊗ P.group.X ⟶ V ⊗ D.parabolic.group.X := 𝟙 V ⊗ₘ e'
  letI : IsIso e' := F.map_isIso e.hom
  letI : IsIso a := by dsimp [a]; infer_instance
  have hi : e' ≫ D.parabolic.inclusion.hom.hom = P.inclusion.hom.hom :=
    congrArg (fun f ↦ F.map f) he
  have hf : a ≫ multiplyFactors E.contracting.inclusion D.parabolic.inclusion =
      multiplyFactors E.contracting.inclusion P.inclusion := by
    have hfst : a ≫ fst E.contracting.group.X D.parabolic.group.X =
        fst E.contracting.group.X P.group.X := by
      change (𝟙 V ⊗ₘ e') ≫ fst V D.parabolic.group.X = fst V P.group.X
      rw [tensorHom_fst, Category.comp_id]
    have hsnd : a ≫ snd E.contracting.group.X D.parabolic.group.X =
        snd E.contracting.group.X P.group.X ≫ e' :=
      tensorHom_snd (𝟙 V) e'
    simp only [multiplyFactors, MonObj.comp_mul]
    rw [← Category.assoc a (fst _ _), hfst, ← Category.assoc a (snd _ _), hsnd,
      Category.assoc, hi]
  rw [← hf, Over.comp_left]
  letI : IsIso a.left := (Over.forget _).map_isIso a
  letI := multiply_isOpenImmersion A c D E
  infer_instance

/-- Pullback of the orbit map of the opposite contracting group along the quotient. -/
private theorem cellPullback {P U : ClosedSubgroup G} (Q : Presentation P) :
    IsPullback (fst U.group.X P.group.X)
      (multiplyFactors U.inclusion P.inclusion)
      (U.inclusion.hom.hom ≫ Q.projection) Q.projection := by
  let X := U.group.X
  let Y := P.group.X
  let e : X ⊗ Y ≅ X ⨯ Y :=
    (tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso (limit.isLimit (pair X Y))
  have ef : e.hom ≫ prod.fst = fst X Y :=
    (tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair X Y)) (Discrete.mk WalkingPair.left)
  have es : e.hom ≫ prod.snd = snd X Y :=
    (tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair X Y)) (Discrete.mk WalkingPair.right)
  have htop : IsPullback (fst X Y) e.hom (𝟙 X) prod.fst :=
    IsPullback.of_vert_isIso ⟨by rw [ef, Category.comp_id]⟩
  have h := htop.paste_vert ((IsPullback.of_prod_fst_with_id U.inclusion.hom.hom Y).paste_vert
    (HomogeneousQuotient.quotientPullback Q))
  have hm : e.hom ≫ (prod.map U.inclusion.hom.hom (𝟙 Y) ≫ rightMultiplication P) =
      multiplyFactors U.inclusion P.inclusion := by
    simp only [rightMultiplication, multiplyFactors, MonObj.comp_mul]
    rw [prod.map_fst, prod.map_snd_assoc, Category.id_comp]
    rw [← Category.assoc e.hom prod.fst, ef, ← Category.assoc e.hom prod.snd, es]
  rwa [hm, Category.id_comp] at h

/-- The open product descends to an open chart with section given by the first factor. -/
private theorem cellChartOpen (A : AffineAlgebraicGroup k) {P U : ClosedSubgroup A.val}
    (Q : Presentation P) (hm : IsOpenImmersion (multiplyFactors U.inclusion P.inclusion).left) :
    IsOpenImmersion (U.inclusion.hom.hom ≫ Q.projection).left := by
  letI : IsAffine A.val.X.left := A.property.1
  letI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
  letI : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
  letI : IsNoetherian A.val.X.left := ⟨⟩
  have hcover : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      Q.projection.left := ⟨⟨Q.surjective, Q.flat⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    ((cellPullback (U := U) Q).flip.map (Over.forget _)) hcover hm

/-- A point over an algebraically closed field lifts along a surjective
locally finite type morphism. -/
private theorem geometricLift {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : SchemeOver k} (q : X ⟶ Y) [Surjective q.left] [LocallyOfFiniteType q.left]
    {s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    (x : Over.mk s ⟶ Y) : ∃ g : Over.mk s ⟶ X, g ≫ q = x := by
  let S := pullback q.left x.left
  let p : S ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
  have hp := IsPullback.of_hasPullback q.left x.left
  letI : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance
  letI : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp inferInstance
  haveI : Nonempty S := ⟨(p.surjective (IsLocalRing.closedPoint K)).choose⟩
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty (α := S)) isOpen_univ.isLocallyClosed
  let t := pointOfClosedPoint p z hz
  have ht : t ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z hz
  let g := t ≫ pullback.fst q.left x.left
  have hg : g ≫ q.left = x.left := by
    dsimp [g]
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← Over.w q, ← Category.assoc, hg, Over.w x]

/-- To factor a field-valued point through an open immersion it suffices to
check the image of the unique point of the field spectrum. -/
private theorem factorThroughOpen {K : Type u} [Field K]
    {X Y : SchemeOver k} (j : X ⟶ Y) [IsOpenImmersion j.left]
    {s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    (y : Over.mk s ⟶ Y) (hy : y.left (IsLocalRing.closedPoint K) ∈ Set.range j.left) :
    ∃ x : Over.mk s ⟶ X, x ≫ j = y := by
  have hy' : Set.range y.left ⊆ Set.range j.left := by
    rintro _ ⟨a, rfl⟩
    change Spec (CommRingCat.of K) at a
    simpa only [Subsingleton.elim a (IsLocalRing.closedPoint K)] using hy
  let f := IsOpenImmersion.lift j.left y.left hy'
  have hf : f ≫ j.left = y.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk f ?_, Over.OverMorphism.ext hf⟩
  rw [← Over.w j, ← Category.assoc, hf, Over.w y]


/-- A rational left multiplier moves a given geometric lift into the open product. -/
private theorem translateIntoCell {U P : ClosedSubgroup G}
    (hd : GeometricallyDenseRationalPoints G.X)
    (hm : IsOpenImmersion (multiplyFactors U.inclusion P.inclusion).left)
    (g : Over.mk (fieldSpecMap k (AlgebraicClosure k)) ⟶ G.X) :
    ∃ (a : fieldBase k ⟶ G.X) (b : Over.mk (fieldSpecMap k (AlgebraicClosure k)) ⟶
      U.group.X ⊗ P.group.X),
      (Over.mkIdTerminal.from _ ≫ a) * g = b ≫ multiplyFactors U.inclusion P.inclusion := by
  let K := AlgebraicClosure k
  let s := fieldSpecMap k K
  let S := Over.mk s
  let Y : SchemeOver k := Over.mk (pullback.snd G.X.hom s ≫ s)
  let f : Y ⟶ G.X := Over.homMk (pullback.fst G.X.hom s) pullback.condition
  let p : Y ⟶ S := Over.homMk (pullback.snd G.X.hom s)
  let m := multiplyFactors U.inclusion P.inclusion
  letI : IsOpenImmersion m.left := hm
  let F := f * (p ≫ g)
  let liftPoint (y : S ⟶ G.X) : S ⟶ Y :=
    Over.homMk (pullback.lift y.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w y))
      (by simp [Y, S])
  have lift_f (y : S ⟶ G.X) : liftPoint y ≫ f = y := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have lift_p (y : S ⟶ G.X) : liftPoint y ≫ p = 𝟙 S := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have lift_F (y : S ⟶ G.X) : liftPoint y ≫ F = y * g := by
    simp only [F, MonObj.comp_mul, lift_f, ← Category.assoc, lift_p, Category.id_comp]
  let O : Set Y.left := F.left ⁻¹' Set.range m.left
  have hopen : IsOpen O := (m.left.isOpenEmbedding.isOpen_range).preimage F.left.continuous
  have hunit : (1 : S ⟶ G.X).left (IsLocalRing.closedPoint K) ∈ Set.range m.left := by
    let e := lift (1 : S ⟶ U.group.X) (1 : S ⟶ P.group.X)
    have he : e ≫ m = 1 := by
      simp [e, m, multiplyFactors, MonObj.comp_mul]
    exact ⟨e.left (IsLocalRing.closedPoint K),
      congrArg (fun z : S ⟶ G.X ↦ z.left (IsLocalRing.closedPoint K)) he⟩
  have hnonempty : O.Nonempty := by
    refine ⟨(liftPoint g⁻¹).left (IsLocalRing.closedPoint K), ?_⟩
    change F.left ((liftPoint g⁻¹).left (IsLocalRing.closedPoint K)) ∈ Set.range m.left
    rwa [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_F, inv_mul_cancel]
  change Dense (Set.range (rationalPointOver K (X := G.X))) at hd
  obtain ⟨_, ha, ⟨a, rfl⟩⟩ := hd.inter_open_nonempty O hopen hnonempty
  have hpoint : rationalPointOver K a =
      (liftPoint (Over.mkIdTerminal.from S ≫ a)).left (IsLocalRing.closedPoint K) := by
    unfold rationalPointOver
    let z : Spec (CommRingCat.of K) ⟶ Y.left :=
      pullback.lift (s ≫ a.left) (𝟙 _) (by simp [Category.assoc, Over.w a])
    change z (IsLocalRing.closedPoint K) = _
    have hz : z = (liftPoint (Over.mkIdTerminal.from S ≫ a)).left := by
      apply pullback.hom_ext <;> simp [z, liftPoint, S, s]
    exact congrArg (fun v : Spec (CommRingCat.of K) ⟶ Y.left ↦ v (IsLocalRing.closedPoint K)) hz
  rw [hpoint] at ha
  have hmem : ((Over.mkIdTerminal.from S ≫ a) * g).left (IsLocalRing.closedPoint K) ∈
      Set.range m.left := by
    rw [← lift_F, Over.comp_left, Scheme.Hom.comp_apply]
    exact ha
  obtain ⟨b, hb⟩ := factorThroughOpen m _ hmem
  exact ⟨a, b, hb.symm⟩

/-- Once a rational translate is in the chart geometrically, the original
point lifts over the ground field. -/
private theorem surjectiveOfOpenCell (A : AffineAlgebraicGroup k) {P U : ClosedSubgroup A.val}
    (hd : GeometricallyDenseRationalPoints A.val.X)
    (hm : IsOpenImmersion (multiplyFactors U.inclusion P.inclusion).left) :
    Function.Surjective (rationalCosetMap P) := by
  obtain ⟨Q⟩ := QuotientEmbedding.quotientEmbedding k A P
  obtain ⟨e, he, hcompat⟩ := TorsorObstruction.rationalPointsOfPresentation Q
  let K := AlgebraicClosure k
  let S := Over.mk (fieldSpecMap k K)
  let r : S ⟶ fieldBase k := Over.mkIdTerminal.from _
  let T : Over (fieldBase k) := Over.mk r
  have hcompat' (x : RationalPoints P) (g : S ⟶ A.val.X) :
      projectSection P g = (rightQuotientSheaf P).obj.map r.op x ↔
        g ≫ Q.projection = r ≫ e x := by
    have hh := hcompat x T g
    rw [Over.mkIdTerminal_from_left] at hh
    exact hh
  letI : Surjective Q.projection.left := Q.surjective
  letI : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
  let j := U.inclusion.hom.hom ≫ Q.projection
  letI : IsOpenImmersion j.left := cellChartOpen A Q hm
  intro x
  obtain ⟨g, hg⟩ := geometricLift Q.projection (r ≫ e x)
  obtain ⟨a, b, hb⟩ := translateIntoCell hd hm g
  let x' := actOnSection P a x
  have hg' : projectSection P g = (rightQuotientSheaf P).obj.map r.op x :=
    (hcompat' x g).2 hg
  have hx' : projectSection P ((r ≫ a) * g) = (rightQuotientSheaf P).obj.map r.op x' := by
    rw [show x' = actOnSection P a x from rfl, actOnSection_naturality, ← hg',
      rightQuotientActionOnLifts]
  have hq' : ((r ≫ a) * g) ≫ Q.projection = r ≫ e x' :=
    (hcompat' x' _).1 hx'
  have hc' : b ≫ fst U.group.X P.group.X ≫ j = r ≫ e x' := by
    rw [← hq', hb, Category.assoc]
    rw [(cellPullback (U := U) Q).w]
  have hopen : (e x').left (IsLocalRing.closedPoint k) ∈ Set.range j.left := by
    have hpoint : r.left (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint k :=
      Subsingleton.elim (α := ↥(Spec (CommRingCat.of k))) _ _
    refine ⟨(b ≫ fst U.group.X P.group.X).left (IsLocalRing.closedPoint K), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hc', Over.comp_left,
      Scheme.Hom.comp_apply, hpoint]
  obtain ⟨t, ht⟩ := factorThroughOpen j (e x') hopen
  have ht' : projectSection P (t ≫ U.inclusion.hom.hom) = x' := by
    apply e.injective
    change e (rationalCosetMap P (QuotientGroup.mk (t ≫ U.inclusion.hom.hom))) = e x'
    rw [he, Category.assoc]
    exact ht
  refine ⟨QuotientGroup.mk (a⁻¹ * (t ≫ U.inclusion.hom.hom)), ?_⟩
  change projectSection P (a⁻¹ * (t ≫ U.inclusion.hom.hom)) = x
  rw [← rightQuotientActionOnLifts, ht']
  change actOnSection P a⁻¹ (actOnSection P a x) = x
  rw [← (rightQuotientActionLaws P x).2, inv_mul_cancel, (rightQuotientActionLaws P x).1]

/-- The canonical map from rational right cosets to rational flag points is bijective. -/
theorem rationalFlagLifting :
    Specs.Relative.RationalFlagLifting.CanonicalCosetMapBijective.{u} := by
  intro k _ A P hP
  obtain ⟨δ, _, hδ, _, hinj, _, _, hrange, _, _⟩ := TorsorObstruction.pointedExactness P
  refine ⟨hinj, ?_⟩
  obtain ⟨c, D, hPD, _, _⟩ := RationalCocharacter.rationalParabolic A P hP
  letI : Smooth A.val.X.hom := hP.1.1
  letI : GeometricallyConnected A.val.X.hom := hP.1.2.1
  letI : ConnectedSpace A.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton
    (f := A.val.X.hom)
  classical
  rcases finite_or_infinite k with hk | hk
  · letI : Fintype k := Fintype.ofFinite k
    letI : IsClosedImmersion P.inclusion.hom.hom.left := P.isClosedImmersion
    letI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
    letI : QuasiCompact A.val.X.hom := A.property.2.2
    haveI : LocallyOfFiniteType P.group.X.hom := by
      rw [← Over.w P.inclusion.hom.hom]
      infer_instance
    haveI : QuasiCompact P.group.X.hom := by
      rw [← Over.w P.inclusion.hom.hom]
      infer_instance
    letI : GeometricallyConnected D.parabolic.group.X.hom :=
      (geometricallyConnectedLimitSubgroups A c D).1
    haveI hconnD : ConnectedSpace D.parabolic.group.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := D.parabolic.group.X.hom)
    obtain ⟨pIso, _⟩ := sameSubgroupIso hPD
    let Xiso := ((Grp.forget (SchemeOver k)) ⋙ (Over.forget _)).mapIso pIso
    letI : ConnectedSpace P.group.X.left :=
      Xiso.schemeIsoToHomeo.connectedSpace_iff.mpr hconnD
    intro x
    change x ∈ Set.range (rationalCosetMap P)
    rw [hrange]
    change δ x = fieldNeutralClass P.group
    obtain ⟨h, hh⟩ := hδ x
    rw [hh]
    exact langFppfTorsor k P.group (fieldGroupSectionsAreSheaf P.group) ⟨_, h⟩
  · letI : Infinite k := hk
    obtain ⟨E⟩ := existsLimitDecomposition A (oppositeCocharacter c)
    exact surjectiveOfOpenCell A (RationalDensity.reductiveRationalPointsDense k A hP.1)
      (parabolicCellOpen A P D E hPD)

end

end LinearAlgebraicGroups.Relative.RationalFlagLifting
