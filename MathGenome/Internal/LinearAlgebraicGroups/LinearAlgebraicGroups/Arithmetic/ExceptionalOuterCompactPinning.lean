import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactPinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactPinning

open Specs.ExceptionalOuterCompactPinning


open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AbstractPairing (Root)
open Specs.AbsoluteDynkinTypes (E6Reflection HasDynkinType PreservesCartan)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open Specs.AutomorphismSequence
open Specs.CharacterDescent (Character Cocharacter)
open Specs.ComplexExceptionalDatum (HasExceptionalCartan)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints)
open Specs.IntegralModels (MatrixRealization)
open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso SplitBorelPair)
open Specs.RootGroups (AdditiveLine)
open Specs.SimplyConnectedLattice (corootLattice)
open LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes (exceptionalPermutations
  cartanPermutationTransport)
open private pointAut pointAut_acts pointAut_eq_id_of_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private continuous_of_algebraicAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
open private recognizesBasedAction_of_lattices pinnedScalarAligned Aligned.mul Aligned.inv
  scalarAut_injective_of_nonempty relativeEvaluate relativeInclusion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private geometricLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalFlagLifting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private abbrev pointSource := (testSpec ℂ).obj (op complexTest)

private def alignedScalar {A : AdditiveLine ℂ} {P : PinnedGroup A} (a : PairAction P.pair) :
    Aligned P (scalarAut a.group pointSource) where
  torus := scalarAut a.torus pointSource
  borel := scalarAut a.borel pointSource
  torus_comm := by
    let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget pointSource).op
    change F.map P.pair.T.inclusion ≫ F.map a.group.asIso.hom =
      F.map a.torus.asIso.hom ≫ F.map P.pair.T.inclusion
    rw [← F.map_comp, ← F.map_comp, a.torus_comm]
  borel_comm := by
    let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget pointSource).op
    change F.map P.pair.B.inclusion ≫ F.map a.group.asIso.hom =
      F.map a.borel.asIso.hom ≫ F.map P.pair.B.inclusion
    rw [← F.map_comp, ← F.map_comp, a.borel_comm]

private theorem relativeFactorization {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (a : PairAction P.pair) :
    ∃ (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P),
      (∀ d : Aut D.toBased,
        let f := (l d).asIso.hom
        (∀ χ : Character P.pair.T.group,
          d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (Specs.Pinning.transportCharacter f.torus χ)) ∧
        (∀ c : Cocharacter P.pair.T.group,
          d.asIso.hom.val.coweightEquiv (Additive.ofMul c) = Additive.ofMul (c ≫ f.torus.inv))) ∧
      ∃ (d : Aut D.toBased) (t : GroupPoints P.pair.T.group complexTest),
        a.torus.asIso = (l d).asIso.hom.torus ∧
        scalarAut a.group pointSource =
          innerAut (S := pointSource) (t ≫ P.pair.T.inclusion.hom.hom) *
            (show RelativeAut P.pair.G.val pointSource from
              scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) pointSource) := by
  let S := pointSource
  have hS : Nonempty S.left := ⟨IsLocalRing.closedPoint ℂ⟩
  obtain ⟨D, l, Q, E, hl, _⟩ :=
    LinearAlgebraicGroups.Descent.AutomorphismSequence.automorphismSequence P
  let f := scalarAut a.group S
  let c := alignedScalar (P := P) a
  obtain ⟨d, hd⟩ := recognizesBasedAction_of_lattices l hl complexTest hS f c a.torus rfl
  let g : RelativeAut P.pair.G.val S := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S
  let a' : Aligned P (f * g⁻¹) := Aligned.mul c (Aligned.inv (pinnedScalarAligned (l d) S))
  have ht : a'.torus = 1 := by
    change c.torus * (scalarAut (Aut.of (l d).asIso.hom.torus) S)⁻¹ = 1
    rw [hd, mul_inv_cancel]
  obtain ⟨t', ht'⟩ := LinearAlgebraicGroups.Descent.AutomorphismSequence.inner_of_fixed_torus
    D E.toExactSequence E.adjointTorus a' ht
  let p := E.adjointTorus.projection.hom.hom
  letI : Surjective p.left := E.adjointTorus.fppf.2.1
  letI : LocallyOfFinitePresentation p.left := E.adjointTorus.fppf.2.2
  obtain ⟨t, ht₁⟩ := geometricLift p t'
  have hq : t' ≫ E.adjointTorus.subgroup.inclusion.hom.hom =
      (t ≫ P.pair.T.inclusion.hom.hom) ≫ Q.projection.hom.hom := by
    rw [← ht₁, Category.assoc]
    exact (congrArg (fun u => t ≫ u.hom.hom) E.adjointTorus.comm).trans
      (Category.assoc _ _ _).symm
  rw [hq, E.onLift] at ht'
  refine ⟨D, l, hl, d, t, ?_, ?_⟩
  · exact congrArg Aut.asIso (scalarAut_injective_of_nonempty (S := S) hd)
  · exact (inv_mul_cancel_right f g).symm.trans (congrArg (· * g) ht')

private def pointMap {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val) : GroupPoints Q complexTest →* PointsIn i ℂ :=
  (baseChangePointGroupEquiv ℂ G.val complexTest).toMonoidHom.comp
    (((groupPointsFunctor ℂ).map (f ≫ e.hom)).app complexTest).hom

private theorem pointMap_apply {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val) (x : GroupPoints Q complexTest) :
    pointMap (i := i) e f x = onPoints (i := i) e f x := rfl

private theorem pointMap_id_surjective {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) :
    Function.Surjective (pointMap (i := i) e (𝟙 _)) := by
  let F := groupPointsFunctor ℂ ⋙ (CategoryTheory.evaluation (TestAlgebra ℂ) GrpCat).obj complexTest
  let b := (forget GrpCat).mapIso (F.mapIso e)
  exact (baseChangePointGroupEquiv ℂ G.val complexTest).surjective.comp (by
    simp only [Category.id_comp]
    exact b.toEquiv.surjective)

private theorem acts_onPoints {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) (b : P.G.val ≅ P.G.val)
    {φ : PointsIn i ℂ → PointsIn i ℂ}
    (hφ : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ b ≪≫ e)) φ)
    (x : GroupPoints P.G.val complexTest) :
    φ (pointMap (i := i) e (𝟙 _) x) =
      pointMap (i := i) e (𝟙 _) (x ≫ b.hom.hom.hom) := by
  let z : GroupPoints (complexGroup G) complexTest := x ≫ e.hom.hom.hom
  have hh : e.hom ≫ (e.symm ≪≫ b ≪≫ e).hom = b.hom ≫ e.hom := by simp
  have hp := hφ z
  change φ (baseChangePoint ℝ ℂ G.val.X complexTest z) =
    baseChangePoint ℝ ℂ G.val.X complexTest (z ≫ (e.symm ≪≫ b ≪≫ e).hom.hom.hom) at hp
  have hz : z ≫ (e.symm ≪≫ b ≪≫ e).hom.hom.hom =
      (x ≫ b.hom.hom.hom) ≫ e.hom.hom.hom := by
    change (x ≫ e.hom.hom.hom) ≫ (e.symm ≪≫ b ≪≫ e).hom.hom.hom = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m : P.G.val ⟶ complexGroup G => x ≫ m.hom.hom) hh).trans
        (Category.assoc _ _ _).symm)
  rw [hz] at hp
  change φ (baseChangePoint ℝ ℂ G.val.X complexTest (x ≫ (𝟙 _ ≫ e.hom).hom.hom)) =
    baseChangePoint ℝ ℂ G.val.X complexTest ((x ≫ b.hom.hom.hom) ≫ (𝟙 _ ≫ e.hom).hom.hom)
  simpa only [Category.id_comp] using hp

set_option maxHeartbeats 750000 in
private theorem implements_onPoints {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (e : P.pair.G.val ≅ complexGroup G) (a : PairAction P.pair)
    (f : Aut P) (t : GroupPoints P.pair.T.group complexTest)
    (ht : scalarAut a.group pointSource = innerAut (S := pointSource) (t ≫ P.pair.T.inclusion.hom.hom) *
        (show RelativeAut P.pair.G.val pointSource from
          scalarAut (Functor.mapAut P (forgetPinning (A := A)) f) pointSource))
    {θ δ : MulAut (PointsIn i ℂ)}
    (hθ : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ a.group.asIso ≪≫ e)) θ)
    (hδ : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ f.asIso.hom.group ≪≫ e)) δ) :
    θ = MulAut.conj (onPoints (i := i) e P.pair.T.inclusion t) * δ := by
  apply MulEquiv.ext
  intro y
  let M := pointMap (i := i) e (𝟙 _)
  obtain ⟨x, rfl⟩ := pointMap_id_surjective (i := i) e y
  change θ (M x) = (MulAut.conj (onPoints (i := i) e P.pair.T.inclusion t)) (δ (M x))
  rw [acts_onPoints e _ hθ x, acts_onPoints e _ hδ x]
  let U : Over pointSource := Over.mk (𝟙 pointSource)
  have hp := congrArg (fun v : RelativeAut P.pair.G.val pointSource =>
    relativeEvaluate v.asIso.hom U x) ht
  let tG : GroupPoints P.pair.G.val complexTest := t ≫ P.pair.T.inclusion.hom.hom
  let g : GroupPoints P.pair.G.val complexTest := x ≫ f.asIso.hom.group.hom.hom.hom
  let tG' : GroupPoints P.pair.G.val complexTest := (𝟙 pointSource) ≫ tG
  change x ≫ a.group.asIso.hom.hom.hom = tG' * g * tG'⁻¹ at hp
  have htg : tG' = tG := Category.id_comp _
  rw [htg] at hp
  change M (x ≫ a.group.asIso.hom.hom.hom) =
    MulAut.conj (M (t ≫ P.pair.T.inclusion.hom.hom)) (M (x ≫ f.asIso.hom.group.hom.hom.hom))
  rw [hp]
  simp only [map_mul, map_inv, MulAut.conj_apply, tG, g]


section Diagram

variable {P : SplitBorelPair ℂ} (D : AttachedDatum P)

private def diagramPermutation (d : Aut D.toBased) :
    letI := D.comm; Equiv.Perm D.base.support := by
  letI := D.comm
  let e : Equiv.Perm (Root P.T) := d.asIso.hom.val.indexEquiv
  let B : Set (Root P.T) := D.base.support
  have h : e '' B = B := d.asIso.hom.property
  exact e.subtypeEquiv (fun x => by
    constructor
    · intro hx
      change e x ∈ B
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      change e x ∈ B at hx
      rw [← h] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact e.injective he ▸ hy)

private theorem diagramPermutation_cartan (d : Aut D.toBased) :
    letI := D.comm
    PreservesCartan (RootData.integralCartan D.datum.rootDatum D.base)
      (RootData.integralCartan D.datum.rootDatum D.base) (diagramPermutation D d) := by
  letI := D.comm
  intro i j
  exact d.asIso.hom.val.toHom.pairing.symm

private theorem basedAut_eq_one_of_simple (full : corootLattice D = ⊤) (d : Aut D.toBased)
    (h : letI := D.comm; diagramPermutation D d = Equiv.refl _) : d = 1 := by
  letI := D.comm
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply RootPairing.Equiv.coweightHom_injective D.datum.rootDatum
  apply MulOpposite.unop_injective
  apply LinearEquiv.toLinearMap_injective
  let L := d.asIso.hom.val.toHom.coweightMap
  change L = LinearMap.id
  have hspan : Submodule.span ℤ (D.datum.rootDatum.coroot '' (D.base.support : Set _)) = ⊤ :=
    D.base.span_int_coroot_support.trans full
  apply LinearMap.ext_on hspan
  rintro _ ⟨j, hj, rfl⟩
  let k : D.base.support := ⟨j, hj⟩
  have hk : d.asIso.hom.val.indexEquiv j = j :=
    congrArg Subtype.val (congrFun (congrArg Equiv.toFun h) k)
  have hj' := RootPairing.Hom.coroot_coweightMap_apply _ _ j d.asIso.hom.val.toHom
  exact hj'.trans (congrArg D.datum.rootDatum.coroot
    (d.asIso.hom.val.indexEquiv.symm_apply_eq.mpr hk.symm))

private theorem diagramPermutation_mul (d f : Aut D.toBased) :
    letI := D.comm
    ∀ j : D.base.support,
      diagramPermutation D (d * f) j = diagramPermutation D d (diagramPermutation D f j) :=
  fun _ => rfl

private theorem exceptional_diagram (D : AttachedDatum P)
    (full : corootLattice D = ⊤) (hType : HasExceptionalCartan D) (d : Aut D.toBased)
    (hd : d ≠ 1) :
    letI := D.comm
    ∃ numbering : D.base.support ≃ Fin 6,
      PreservesCartan (RootData.integralCartan D.datum.rootDatum D.base)
        (CartanMatrix.E 6) numbering ∧
      ∀ j, diagramPermutation D d (numbering.symm j) = numbering.symm (E6Reflection j) := by
  letI := D.comm
  let σ := diagramPermutation D d
  have hσ := diagramPermutation_cartan D d
  have identify {n : ℕ} (e : D.base.support ≃ Fin n)
      (he : (e.symm.trans σ).trans e = Equiv.refl _) : False := by
    apply hd (basedAut_eq_one_of_simple D full d _)
    apply Equiv.ext
    intro k
    apply e.injective
    exact (congrArg (e ∘ σ) (e.symm_apply_apply k)).symm.trans
      (congrFun (congrArg Equiv.toFun he) (e k))
  rcases hType with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · have hc := (cartanPermutationTransport he σ).mp hσ
    rcases (exceptionalPermutations.1 _).mp hc with h | h
    · exact (identify e h).elim
    refine ⟨e, he, fun j => e.injective ?_⟩
    exact (congrFun (congrArg Equiv.toFun h) j).trans (e.apply_symm_apply _).symm
  · exact (identify e ((exceptionalPermutations.2.1 _).mp
      ((cartanPermutationTransport he σ).mp hσ))).elim
  · exact (identify e ((exceptionalPermutations.2.2.1 _).mp
      ((cartanPermutationTransport he σ).mp hσ))).elim

private theorem reflection_involutive : Function.Involutive E6Reflection := by
  intro j
  fin_cases j <;> decide

private theorem basedAut_square (full : corootLattice D = ⊤) (d : Aut D.toBased)
    (e : letI := D.comm; D.base.support ≃ Fin 6)
    (h : letI := D.comm; ∀ j, diagramPermutation D d (e.symm j) = e.symm (E6Reflection j)) :
    d * d = 1 := by
  letI := D.comm
  apply basedAut_eq_one_of_simple D full
  apply Equiv.ext
  intro j
  obtain ⟨k, rfl⟩ := e.symm.surjective j
  rw [diagramPermutation_mul, h, h, reflection_involutive]
  rfl

end Diagram


private theorem pinnedPermutesCoordinates {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P)
    (hl : ∀ χ : Character P.pair.T.group,
      d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (Specs.Pinning.transportCharacter f.torus χ))
    (e : letI := D.comm; D.base.support ≃ Fin 6)
    (he : ∀ j, letI := D.comm
      diagramPermutation D d (e.symm j) = e.symm (E6Reflection j)) (j : Fin 6) :
    simpleCoordinate P (simple D e j) ≫ f.group.hom =
      simpleCoordinate P (simple D e (E6Reflection j)) := by
  letI := D.comm
  let α := simple D e j
  let β := simple D e (E6Reflection j)
  let g := f.torus
  have hχ : Specs.Pinning.transportCharacter g α.val.val = β.val.val := by
    apply Additive.ofMul.injective
    rw [← hl]
    have hidx : d.asIso.hom.val.indexEquiv α.val = β.val := congrArg Subtype.val (he j)
    have hroot := RootPairing.Hom.root_weightMap_apply _ _ α.val d.asIso.hom.val.toHom
    change d.asIso.hom.val.weightEquiv (D.datum.rootDatum.root α.val) =
      D.datum.rootDatum.root (d.asIso.hom.val.indexEquiv α.val) at hroot
    rw [hidx, D.datum.root_eq, D.datum.root_eq] at hroot
    exact hroot
  have hm : (Specs.Pinning.transportCharacter g α.val.val,
      simpleCoordinate P α ≫ f.group.hom) ∈ Specs.Pinning.pinGraph P := by
    rw [← f.pin_comm]
    exact ⟨_, ⟨α, rfl⟩, rfl⟩
  obtain ⟨other, hother⟩ := hm
  have hotherβ : other = β := Subtype.ext (Subtype.ext ((congrArg Prod.fst hother).trans hχ))
  exact (congrArg Prod.snd (hotherβ ▸ hother)).symm

private theorem pinnedPermutesCoroots {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (d : Aut D.toBased) (f : PinnedIso P P)
    (hl : ∀ c : Cocharacter P.pair.T.group,
      d.asIso.hom.val.coweightEquiv (Additive.ofMul c) = Additive.ofMul (c ≫ f.torus.inv))
    (e : letI := D.comm; D.base.support ≃ Fin 6)
    (he : ∀ j, letI := D.comm
      diagramPermutation D d (e.symm j) = e.symm (E6Reflection j)) (j : Fin 6) :
    simpleCoroot D (simple D e j) ≫ f.torus.hom =
      simpleCoroot D (simple D e (E6Reflection j)) := by
  letI := D.comm
  let α := simple D e j
  let β := simple D e (E6Reflection j)
  have hidx : d.asIso.hom.val.indexEquiv α.val = β.val := congrArg Subtype.val (he j)
  have hcoroot := RootPairing.Hom.coroot_coweightMap_apply _ _ β.val d.asIso.hom.val.toHom
  change d.asIso.hom.val.coweightEquiv (D.datum.rootDatum.coroot β.val) =
    D.datum.rootDatum.coroot (d.asIso.hom.val.indexEquiv.symm β.val) at hcoroot
  rw [d.asIso.hom.val.indexEquiv.symm_apply_eq.mpr hidx.symm] at hcoroot
  have hc : simpleCoroot D β ≫ f.torus.inv = simpleCoroot D α :=
    Additive.ofMul.injective ((hl (simpleCoroot D β)).symm.trans hcoroot)
  change simpleCoroot D α ≫ f.torus.hom = simpleCoroot D β
  rw [← hc, Category.assoc, f.torus.inv_hom_id, Category.comp_id]

/-- The Borel-pair preserving outer action is of type E₆ and has its actual
pinned diagram factor and a complex torus implementer. -/
theorem diagramDecomposition : DiagramDecompositionStatement := by
  intro G i hs hsc hType A P h a θ hθ _ hOuter
  let e := comparison h
  obtain ⟨D, l, hl, d, t, hT, hFactor⟩ := relativeFactorization (P := P) a
  obtain ⟨hFull, hExceptional⟩ :=
    (LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum.complexExceptionalDatum G hs hsc hType).2
      P.pair h D
  let f := (l d).asIso.hom
  let φ := Aut.of (e.symm ≪≫ f.group ≪≫ e)
  let δ : MulAut (PointsIn i ℂ) := pointAut G φ
  have hδ : ActsOnComplexPoints (i := i) φ δ := pointAut_acts G φ
  have hθδ := implements_onPoints e a (l d) t hFactor hθ hδ
  have hd : d ≠ 1 := by
    intro hd
    have hf : f.group.hom = 𝟙 _ := by
      change (l d).asIso.hom.group.hom = _
      rw [hd, map_one]
      rfl
    have hφ : φ.asIso.hom = 𝟙 _ := by
      change e.inv ≫ f.group.hom ≫ e.hom = _
      simp [hf]
    have hδ₁ : δ = 1 := by
      ext x
      obtain ⟨z, rfl⟩ := (baseChangePointGroupEquiv ℂ G.val complexTest).surjective x
      change δ (baseChangePoint ℝ ℂ G.val.X complexTest z) =
        baseChangePoint ℝ ℂ G.val.X complexTest z
      exact (hδ z).trans (by simp [hφ])
    exact hOuter ⟨_, by simpa only [hδ₁, mul_one] using hθδ⟩
  obtain ⟨numbering, hC, hNumbering⟩ := exceptional_diagram D hFull hExceptional d hd
  have hfSq : f.group.hom ≫ f.group.hom = 𝟙 _ := by
    have hdd := basedAut_square D hFull d numbering hNumbering
    have he : l d * l d = 1 := by rw [← map_mul, hdd, map_one]
    exact congrArg (fun z : Aut P => z.asIso.hom.group.hom) he
  have hφSq : φ.asIso.hom ≫ φ.asIso.hom = 𝟙 _ := by
    change (e.inv ≫ f.group.hom ≫ e.hom) ≫ (e.inv ≫ f.group.hom ≫ e.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc f.group.hom, hfSq]
    simp
  refine ⟨⟨D, hFull, numbering, hC, f, δ, ?_, ?_, congrArg Iso.hom hT, hδ,
    pointAut_eq_id_of_comp G φ φ hφSq, continuous_of_algebraicAction hδ, t, hθδ⟩⟩
  · exact pinnedPermutesCoordinates D d f (hl d).1 numbering hNumbering
  · exact pinnedPermutesCoroots D d f (hl d).2 numbering hNumbering


section Torus

open Specs.CharacterPairing (pairing)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private unitPointHom unitPointHom_apply pointHom_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterUnit characterUnitOnPoints characterUnit_cocharacter characterEvaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private splitTorus_points_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates

private def cocharacterEvaluation {Q : GroupScheme ℂ} (c : Cocharacter Q) :
    ℂˣ →* GroupPoints Q complexTest :=
  (((groupPointsFunctor ℂ).map c).app complexTest).hom.comp (unitPointHom complexTest)

private theorem cocharacterEvaluation_apply {Q : GroupScheme ℂ} (c : Cocharacter Q) (z : ℂˣ) :
    cocharacterEvaluation c z = cocharacterPoint c complexTest z := by
  simp only [cocharacterEvaluation, MonoidHom.comp_apply, unitPointHom_apply]
  rfl

private theorem pointMap_inclusion_injective {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) :
    Function.Injective (pointMap (i := i) e P.T.inclusion) := by
  intro x y h
  apply pointHom_injective P.T complexTest
  let f := (Grp.forget (SchemeOver ℂ)).mapIso e
  apply (cancel_mono f.hom).mp
  have h' := (baseChangePointGroupEquiv ℂ G.val complexTest).injective h
  change x ≫ (P.T.inclusion ≫ e.hom).hom.hom =
    y ≫ (P.T.inclusion ≫ e.hom).hom.hom at h'
  exact (Category.assoc _ _ _).trans (h'.trans (Category.assoc _ _ _).symm)

variable {P : SplitBorelPair ℂ}

private def torusFromUnits {n : ℕ} (c : Fin n → Cocharacter P.T.group) (z : Fin n → ℂˣ) :
    GroupPoints P.T.group complexTest :=
  (List.ofFn fun j => cocharacterEvaluation (c j) (z j)).prod

private theorem torusFromUnits_bijective {n : ℕ} (D : AttachedDatum P)
    (c : Fin n → Cocharacter P.T.group)
    (b : letI := D.comm; Module.Basis (Fin n) ℤ (Additive (Cocharacter P.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (c j)) : Function.Bijective (torusFromUnits (P := P) c) := by
  letI := D.comm
  let a := b.dualBasis.map D.datum.rootDatum.toLinearMap.toPerfPair.symm
  have ha (j k : Fin n) :
      pairing P.T.group (a j).toMul (c k) = (Pi.single j 1 : Fin n → ℤ) k := by
    rw [← D.datum.pairing_eq, ← hb k]
    change D.datum.rootDatum.toLinearMap.toPerfPair
      (D.datum.rootDatum.toLinearMap.toPerfPair.symm (b.dualBasis j)) (b k) = _
    rw [LinearEquiv.apply_symm_apply]
    simp [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hcoord (z : Fin n → ℂˣ) (j : Fin n) :
      characterUnit (a j).toMul complexTest (torusFromUnits (P := P) c z) = z j := by
    have hm : characterUnit (a j).toMul complexTest (torusFromUnits (P := P) c z) =
        ∏ k, z k ^ pairing P.T.group (a j).toMul (c k) := by
      change characterUnitOnPoints (a j).toMul complexTest (torusFromUnits (P := P) c z) = _
      simp only [torusFromUnits, map_list_prod, List.map_ofFn, List.prod_ofFn]
      apply Finset.prod_congr rfl
      intro k _
      exact (congrArg (characterUnit (a j).toMul complexTest)
        (cocharacterEvaluation_apply (c k) (z k))).trans
        (characterUnit_cocharacter (a j).toMul (c k) complexTest (z k))
    rw [hm, Finset.prod_eq_single j]
    · rw [ha, Pi.single_eq_same, zpow_one]
    · intro k _ hk
      simp only [ha, Pi.single_eq_of_ne hk, zpow_zero]
    · simp
  constructor
  · intro u v huv
    funext j
    rw [← hcoord u j, ← hcoord v j, huv]
  · intro p
    let z (j : Fin n) := characterUnit (a j).toMul complexTest p
    use z
    apply splitTorus_points_ext P.split complexTest
    let F (q : GroupPoints P.T.group complexTest) :=
      (characterEvaluation complexTest q).toAdditive.toIntLinearMap
    have heq : F (torusFromUnits (P := P) c z) = F p := by
      apply a.ext
      intro j
      exact hcoord z j
    intro χ
    exact congrArg Additive.toMul (LinearMap.congr_fun heq (Additive.ofMul χ))

private theorem torusFromUnits_mul {n : ℕ} (D : AttachedDatum P)
    (c : Fin n → Cocharacter P.T.group) (u v : Fin n → ℂˣ) :
    torusFromUnits (P := P) c (u * v) = torusFromUnits (P := P) c u * torusFromUnits (P := P) c v := by
  letI := D.comm
  letI : IsMulCommutative (GroupPoints P.T.group complexTest) :=
    (isCommMonObj_iff_isMulCommutative _).mp D.comm _
  letI : CommGroup (GroupPoints P.T.group complexTest) :=
    { (inferInstance : Group (GroupPoints P.T.group complexTest)) with mul_comm := mul_comm' }
  simp only [torusFromUnits, List.prod_ofFn, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

private def torusCoordinates {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    (D : AttachedDatum P) {n : ℕ} (c : Fin n → Cocharacter P.T.group) :
    (Fin n → ℂˣ) →* PointsIn i ℂ where
  toFun z := pointMap (i := i) e P.T.inclusion (torusFromUnits (P := P) c z)
  map_one' := by simp [torusFromUnits]
  map_mul' u v := by rw [torusFromUnits_mul D, map_mul]

private theorem torusCoordinates_conjugateInversion {G : AffineAlgebraicGroup ℝ}
    {i : MatrixRealization G} {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    (D : AttachedDatum P) {n : ℕ} (c : Fin n → Cocharacter P.T.group)
    (ω : MulAut (PointsIn i ℂ)) (hω : ConjugateInversion (i := i) e ω) (z : Fin n → ℂˣ) :
    ω (torusCoordinates (i := i) e D c z) =
      torusCoordinates (i := i) e D c (conjugateInverseUnit ∘ z) := by
  change ω (pointMap e P.T.inclusion (torusFromUnits (P := P) c z)) =
    pointMap e P.T.inclusion (torusFromUnits (P := P) c (conjugateInverseUnit ∘ z))
  unfold torusFromUnits
  simp only [map_list_prod, List.map_ofFn, cocharacterEvaluation_apply]
  apply congrArg (fun f : Fin n → PointsIn i ℂ => (List.ofFn f).prod)
  funext j
  exact hω (c j) (z j)

private theorem eq_conjugateInverseUnit_of_torsion (z : ℂˣ)
    (h : IsOfFinOrder (z * (conjugateInverseUnit z)⁻¹)) : conjugateInverseUnit z = z := by
  obtain ⟨m, hm, he⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  let w := z * (conjugateInverseUnit z)⁻¹
  have hw : (w : ℂ) = (‖(z : ℂ)‖ ^ 2 : ℝ) := by
    change (z : ℂ) * (Complex.conjAe (z : ℂ)) = _
    simpa only [Complex.conjAe_coe, Complex.ofReal_pow] using Complex.mul_conj' (z : ℂ)
  have hn : ‖(w : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (congrArg Units.val he) hm.ne'
  rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hn
  have hw' : w = 1 := Units.ext (hw.trans (by rw [hn]; rfl))
  exact (mul_inv_eq_one.mp hw').symm

end Torus


section CompactImplementer

open Specs.ExceptionalCompactInner (HasCompactDifferential)
open Specs.ExceptionalLieAutomorphismTransport (ComplexPoints)
open private adjointConjugation_faithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport

private theorem isOfFinOrder_of_central {H Q : Type*} [Group H] [Group Q]
    (p : H →* Q) (hp : Function.Surjective p) [Finite p.ker]
    (hf : Function.Injective (MulAut.conj : Q → MulAut Q))
    (z : H) (hz : MulAut.conj z = 1) : IsOfFinOrder z := by
  have hz' : z ∈ p.ker := by
    change p z = 1
    apply hf
    rw [map_one]
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hp y
    have hx := congrArg (fun a : MulAut H => p (a x)) hz
    simpa only [MulAut.conj_apply, map_mul, map_inv, MulAut.one_apply] using hx
  exact p.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨z, hz'⟩ : p.ker))

set_option maxHeartbeats 500000 in
private theorem centralPoint_isOfFinOrder (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hs : Specs.GeometricRadicals.IsSemisimple G)
    (s : Specs.IdentityLieStructure (complexGroup G)) (z : PointsIn i ℂ)
    (hz : MulAut.conj z = 1) : IsOfFinOrder z := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨Z, Q, q, d, N, A, j, f, l, b, hAdj, hcentral, hZ, hClosed, _, hp, _, _, _, _⟩ :=
    ExceptionalLieAutomorphismTransport.complexAdjointComparison G hs s
  let iQ : MatrixRealization Q := ⟨d, N, l, j ≫ f, hClosed⟩
  let p := Specs.ExceptionalComplexPointGeometry.pointMap i iQ q
  have hf := adjointConjugation_faithful G Q hs Z q hAdj hZ hp
  obtain ⟨_, hp', hfin, _⟩ :=
    ExceptionalComplexPointGeometry.centralIsogenyCovering i iQ q hcentral
  letI : Finite p.ker := hfin
  exact isOfFinOrder_of_central p hp' hf z hz

private theorem innerFactor_commutes {H : Type*} [Group H] {ω θ δ : MulAut H} {t : H}
    (hθ : Function.Commute θ ω) (hδ : Function.Commute δ ω)
    (ht : θ = MulAut.conj t * δ) :
    MulAut.conj (t * (ω t)⁻¹) = 1 := by
  have he : MulAut.conj t = MulAut.conj (ω t) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := δ.surjective y
    obtain ⟨v, rfl⟩ := ω.surjective x
    have hh := hθ v
    rw [ht] at hh
    change MulAut.conj t (δ (ω v)) = ω (MulAut.conj t (δ v)) at hh
    rw [hδ v] at hh ⊢
    simpa only [MulAut.conj_apply, map_mul, map_inv] using hh
  rw [map_mul, map_inv, he, mul_inv_cancel]

open LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes (cartanCoordinates)

private theorem compactImplementer {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (e : P.pair.G.val ≅ complexGroup G) (a : PairAction P.pair)
    {ω θ : MulAut (PointsIn i ℂ)} (h : OuterInvolutions (i := i) ω θ)
    (hs : Specs.GeometricRadicals.IsSemisimple G) (hT : ConjugateInversion (i := i) e ω)
    (d : DiagramDecomposition (i := i) e a θ) (hd : Function.Commute d.pointDiagram ω) :
    ∃ t : GroupPoints P.pair.T.group complexTest,
      ω (onPoints (i := i) e P.pair.T.inclusion t) = onPoints (i := i) e P.pair.T.inclusion t ∧
      θ = MulAut.conj (onPoints (i := i) e P.pair.T.inclusion t) * d.pointDiagram := by
  obtain ⟨t, ht⟩ := d.implements
  let D := d.datum
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let c := fun j => simpleCoroot D (simple D d.numbering j)
  obtain ⟨b, _, hb, _, _, _⟩ := cartanCoordinates
    D.datum.rootDatum D.base d.full_coroot_lattice (CartanMatrix.E 6) d.numbering d.cartan
  have hcb (j : Fin 6) : b j = Additive.ofMul (c j) := hb j
  let M := torusCoordinates (i := i) e D c
  have hm : Function.Injective M := (pointMap_inclusion_injective (i := i) e).comp
    (torusFromUnits_bijective D c b hcb).1
  obtain ⟨z, rfl⟩ := (torusFromUnits_bijective D c b hcb).2 t
  have hcz : ω (M z) = M (conjugateInverseUnit ∘ z) :=
    torusCoordinates_conjugateInversion e D c ω hT z
  obtain ⟨aω, _, hc⟩ := h.compact_differential
  obtain ⟨s, _⟩ := hc
  have ht' : θ = MulAut.conj (M z) * d.pointDiagram := ht
  have hz := centralPoint_isOfFinOrder G i hs s _ (innerFactor_commutes h.commute hd ht')
  rw [hcz, ← map_inv M, ← map_mul M] at hz
  have hfin := hm.isOfFinOrder_iff.mp hz
  have he : conjugateInverseUnit ∘ z = z := by
    funext j
    exact eq_conjugateInverseUnit_of_torsion (z j) (hfin.apply j)
  refine ⟨_, ?_, ht⟩
  change ω (M z) = M z
  rw [hcz, he]

end CompactImplementer


section RankOneTangent

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure ClosedSubgroup)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (CorootReflection HasScalarAction rootPoint)
open InfinitesimalCommutator
open private rootPoint_eps_reduces rootPoint_natural characterValue_eq_unit characterUnit_inv characterUnit_cocharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private mapPoints_injective rootPoint_add rootPoint_neg
  changeRing torusPointHom torusPointHom_apply mapPoints_torusPointHom rankOneScalar gauss
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private liftST_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

variable {J : GroupScheme ℂ}
private abbrev dualTest := CommAlgCat.of ℂ (DualNumber ℂ)
private abbrev mixedTest := CommAlgCat.of ℂ (TwoVariables ℂ)

private def rootTangent {A : AdditiveLine ℂ} (x : A.group ⟶ J) : Lie ℂ J :=
  Additive.ofMul ⟨rootPoint x dualTest DualNumber.eps, rootPoint_eps_reduces x⟩

private def corootTangentUnit : (DualNumber ℂ)ˣ :=
  Units.mkOfMulEqOne (1 + DualNumber.eps) (1 - DualNumber.eps) (by
    ring_nf
    simp [pow_two, DualNumber.eps_mul_eps])

private def corootTangent (T : ClosedSubgroup J) (c : Cocharacter T.group) : Lie ℂ J := by
  refine Additive.ofMul ⟨torusPointHom T c dualTest corootTangentUnit, ?_⟩
  change changeRing (G := J) (dualReduction ℂ) (torusPointHom T c dualTest corootTangentUnit) = 1
  rw [mapPoints_torusPointHom]
  have hu : Units.map (dualReduction ℂ).hom.toMonoidHom corootTangentUnit = 1 := by
    apply Units.ext
    change (1 + DualNumber.eps : DualNumber ℂ).fst = 1
    simp
  simp only [hu, map_one]

private abbrev liftSMor : dualTest ⟶ mixedTest := CommAlgCat.ofHom (liftS ℂ)
private abbrev liftTMor : dualTest ⟶ mixedTest := CommAlgCat.ofHom (liftT ℂ)
private abbrev liftSTMor : dualTest ⟶ mixedTest := CommAlgCat.ofHom (liftST ℂ)

private theorem lie_eq_of_mixed {G : AffineAlgebraicGroup ℂ} {x y : Lie ℂ G.val}
    (h : mapPoints liftSTMor x.toMul.val =
      mapPoints liftSTMor y.toMul.val) : x = y := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact mapPoints_injective G.property.1 liftSTMor liftST_injective h

private theorem mixed_correlation :
    let s := liftS ℂ (DualNumber.eps : DualNumber ℂ)
    let t := liftT ℂ (DualNumber.eps : DualNumber ℂ)
    let u := liftST ℂ (DualNumber.eps : DualNumber ℂ)
    s * t = u ∧ s * u = 0 ∧ t * u = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext <;>
    simp [liftS, liftT, liftST, mapCoefficients]

private theorem corootTangent_mixed (T : ClosedSubgroup J) (c : Cocharacter T.group) :
    let u := liftST ℂ (DualNumber.eps : DualNumber ℂ)
    ∀ a : (TwoVariables ℂ)ˣ, (a : TwoVariables ℂ) = 1 + u →
      mapPoints liftSTMor (corootTangent T c).toMul.val =
        torusPointHom T c mixedTest a := by
  intro u a ha
  change changeRing (G := J) liftSTMor (torusPointHom T c dualTest corootTangentUnit) = _
  rw [mapPoints_torusPointHom]
  apply congrArg (torusPointHom T c mixedTest)
  apply Units.ext
  change liftST ℂ (1 + DualNumber.eps) = (a : TwoVariables ℂ)
  simp [ha, u]

set_option maxHeartbeats 500000 in
/-- The attached rank-one word identifies the mixed commutator of the two
infinitesimal root parameters with the coroot differential. -/
private theorem linked_tangent_bracket {G : AffineAlgebraicGroup ℂ} {A : AdditiveLine ℂ}
    {T : ClosedSubgroup G.val} {α : Character T.group} {x y : A.group ⟶ G.val}
    (r : CorootReflection T α x y) (hx : HasScalarAction T α x)
    (hy : HasScalarAction T α⁻¹ y) (l : IdentityLieStructure G.val) :
    letI := l.lieRing
    ⁅rootTangent x, rootTangent y⁆ = corootTangent T r.coroot := by
  letI := l.lieRing
  apply lie_eq_of_mixed
  let s := liftS ℂ (DualNumber.eps : DualNumber ℂ)
  let t := liftT ℂ (DualNumber.eps : DualNumber ℂ)
  let u := liftST ℂ (DualNumber.eps : DualNumber ℂ)
  obtain ⟨hst, hsu, htu⟩ := mixed_correlation
  have huu : u * u = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let a : (TwoVariables ℂ)ˣ :=
    ⟨1 + u, 1 - u, by linear_combination -huu, by linear_combination -huu⟩
  have hg := gauss r hx G.property.1 mixedTest s t a
    (show 1 + u = 1 + s * t from congrArg (1 + ·) hst.symm)
  have hs : s * (↑a⁻¹ : TwoVariables ℂ) = s := by
    change s * (1 - u) = s
    rw [mul_sub, mul_one, hsu, sub_zero]
  have ht : t * (↑a⁻¹ : TwoVariables ℂ) = t := by
    change t * (1 - u) = t
    rw [mul_sub, mul_one, htu, sub_zero]
  rw [hs, ht] at hg
  have hh := l.commutator_law (rootTangent x) (rootTangent y)
  change mapPoints liftSTMor (⁅rootTangent x, rootTangent y⁆ : Lie ℂ G.val).toMul.val =
    commutator ((groupPointsFunctor ℂ).obj G.val) (rootTangent x) (rootTangent y) at hh
  rw [hh, corootTangent_mixed T r.coroot a rfl]
  change
    (mapPoints liftSMor (rootPoint x dualTest DualNumber.eps) :
      GroupPoints G.val mixedTest) *
      mapPoints liftTMor (rootPoint y dualTest DualNumber.eps) *
      (mapPoints liftSMor (rootPoint x dualTest DualNumber.eps))⁻¹ *
      (mapPoints liftTMor (rootPoint y dualTest DualNumber.eps))⁻¹ = _
  rw [rootPoint_natural x liftSMor, rootPoint_natural y liftTMor]
  change rootPoint x mixedTest s * rootPoint y mixedTest t *
    (rootPoint x mixedTest s)⁻¹ * (rootPoint y mixedTest t)⁻¹ = _
  let c := LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint r.coroot mixedTest a
  have hvalue : characterValue α⁻¹ mixedTest c = (↑a⁻¹ : TwoVariables ℂ) ^ 2 := by
    rw [characterValue_eq_unit, characterUnit_inv, characterUnit_cocharacter, r.root_pairing,
      zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val]
  have hscale : (↑a⁻¹ : TwoVariables ℂ) ^ 2 * t = t := by
    change (1 - u) ^ 2 * t = t
    have he := mul_comm u t
    rw [htu] at he
    linear_combination (u - 2) * he
  have hneg := hy mixedTest c t
  rw [hvalue, hscale] at hneg
  have hcomm : torusPointHom T r.coroot mixedTest a * rootPoint y mixedTest t =
      rootPoint y mixedTest t * torusPointHom T r.coroot mixedTest a :=
    mul_inv_eq_iff_eq_mul.mp (by
      rw [torusPointHom_apply]
      exact hneg)
  calc
    _ = rootPoint y mixedTest t * torusPointHom T r.coroot mixedTest a *
        (rootPoint y mixedTest t)⁻¹ := by rw [hg]; group
    _ = torusPointHom T r.coroot mixedTest a := by rw [← hcomm]; group

private theorem rootTangent_smul {A : AdditiveLine ℂ} (x : A.group ⟶ J)
    (l : IdentityLieStructure J) (a : ℂ) :
    letI := l.lieRing
    letI := l.lieAlgebra
    (@SMul.smul ℂ (Lie ℂ J) l.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul a
      (rootTangent x)).toMul.val = rootPoint x dualTest (⟨0, a⟩ : DualNumber ℂ) := by
  rw [l.scalar_law]
  let m : dualTest ⟶ dualTest := CommAlgCat.ofHom (dualNumberScale a)
  change mapPoints m (rootPoint x dualTest DualNumber.eps) = _
  rw [rootPoint_natural]
  congr 1
  apply TrivSqZeroExt.ext <;> simp [m, dualNumberScale]

set_option maxHeartbeats 500000 in
private theorem coroot_tangent_bracket {G : AffineAlgebraicGroup ℂ} {A : AdditiveLine ℂ}
    {T : ClosedSubgroup G.val} {α : Character T.group} {x : A.group ⟶ G.val}
    (c : Cocharacter T.group) (hx : HasScalarAction T α x)
    (l : IdentityLieStructure G.val) (m : ℤ)
    (hc : Specs.CharacterPairing.pairing T.group α c = m) (hm : m = 2 ∨ m = -2) :
    letI := l.lieRing
    letI := l.lieAlgebra
    ⁅corootTangent T c, rootTangent x⁆ =
      @SMul.smul ℂ (Lie ℂ G.val) l.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
        (m : ℂ) (rootTangent x) := by
  letI := l.lieRing
  letI := l.lieAlgebra
  apply lie_eq_of_mixed
  let s := liftS ℂ (DualNumber.eps : DualNumber ℂ)
  let t := liftT ℂ (DualNumber.eps : DualNumber ℂ)
  let u := liftST ℂ (DualNumber.eps : DualNumber ℂ)
  obtain ⟨hst, _, _⟩ := mixed_correlation
  let a := Units.map liftSMor.hom.toMonoidHom corootTangentUnit
  have ha : (a : TwoVariables ℂ) = 1 + s := by simp [a, liftSMor, corootTangentUnit, s]
  have hai : (↑a⁻¹ : TwoVariables ℂ) = 1 - s := by
    change liftS ℂ (1 - DualNumber.eps) = _
    simp [s]
  have hsq : s ^ 2 = 0 := by rw [← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero]
  have hval : characterValue α mixedTest (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c mixedTest a) =
      1 + (m : TwoVariables ℂ) * s := by
    rw [characterValue_eq_unit, characterUnit_cocharacter, hc]
    rcases hm with rfl | rfl
    · rw [zpow_ofNat, Units.val_pow_eq_pow_val, ha]
      push_cast
      linear_combination hsq
    · rw [zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val, hai]
      push_cast
      linear_combination hsq
  have hh := l.commutator_law (corootTangent T c) (rootTangent x)
  change mapPoints liftSTMor (⁅corootTangent T c, rootTangent x⁆ : Lie ℂ G.val).toMul.val =
    commutator ((groupPointsFunctor ℂ).obj G.val) (corootTangent T c) (rootTangent x) at hh
  rw [hh, rootTangent_smul x l, rootPoint_natural x liftSTMor]
  let uT : GroupPoints G.val mixedTest := mapPoints liftTMor (rootPoint x dualTest DualNumber.eps)
  let uS : GroupPoints G.val mixedTest :=
      changeRing (G := G.val) liftSMor (torusPointHom T c dualTest corootTangentUnit)
  change uS * uT * uS⁻¹ * uT⁻¹ = _
  have ht : uT = rootPoint x mixedTest t := rootPoint_natural x liftTMor _
  have hs : uS = torusPointHom T c mixedTest a :=
    mapPoints_torusPointHom T c liftSMor corootTangentUnit
  rw [ht, hs]
  have hact := hx mixedTest (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c mixedTest a) t
  change torusPointHom T c mixedTest a * rootPoint x mixedTest t *
    (torusPointHom T c mixedTest a)⁻¹ = _ at hact
  change torusPointHom T c mixedTest a * rootPoint x mixedTest t *
    (torusPointHom T c mixedTest a)⁻¹ * (rootPoint x mixedTest t)⁻¹ = _
  rw [hact, hval]
  rw [← rootPoint_neg, ← rootPoint_add]
  congr 1
  change (1 + (m : TwoVariables ℂ) * s) * t + -t =
    liftST ℂ (⟨0, (m : ℂ)⟩ : DualNumber ℂ)
  have hz : liftST ℂ (⟨0, (m : ℂ)⟩ : DualNumber ℂ) = (m : TwoVariables ℂ) * u := by
    let v : DualNumber ℂ := TrivSqZeroExt.inr 1
    let q : TwoVariables ℂ := TrivSqZeroExt.inr v
    change TrivSqZeroExt.inr (TrivSqZeroExt.inr (m : ℂ)) = (m : TwoVariables ℂ) * q
    rw [← TrivSqZeroExt.inl_intCast, TrivSqZeroExt.inl_mul_inr]
    congr 1
    rw [smul_eq_mul, ← TrivSqZeroExt.inl_intCast, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]
  have hst' : s * t = u := hst
  rw [hz, ← hst']
  ring

end RankOneTangent

section CompactSign

open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact hermitian)
open private killing_fixed hermitian_positive
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

/-- For a linked root pair the scale of compact conjugation is negative real. -/
private theorem compactConjugation_scale_neg {L : Type} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (τ : Conjugation L) (hτ : IsCompact τ)
    (E F H : L) (hE : E ≠ 0) (hH : H ≠ 0)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E) (hanti : τ.map H = -H)
    (a : ℂ) (ha : a ≠ 0) (he : τ.map E = a • F) :
    a = (a.re : ℂ) ∧ a.re < 0 := by
  have hb : star a ≠ 0 := by simpa using ha
  have hf : τ.map F = (star a)⁻¹ • E := by
    have hh := congrArg τ.map he
    rw [τ.involutive, τ.antilinear] at hh
    rw [hh, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hLie := τ.map.map_lie E F
  rw [hEF, hanti, he, hf, smul_lie, lie_smul, smul_smul, ← lie_skew F E, hEF,
    smul_neg, neg_inj] at hLie
  have hsc : (1 : ℂ) = a * (star a)⁻¹ := by
    apply smul_left_injective ℂ hH
    exact (one_smul ℂ H).trans hLie
  have hreal : a = star a := by
    have h := congrArg (· * star a) hsc
    simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one] using h.symm
  have hre : a = (a.re : ℂ) := by
    apply Complex.ext
    · simp
    · have hh := congrArg Complex.im hreal
      change a.im = -a.im at hh
      simp only [Complex.ofReal_im]
      linarith
  have hiH : τ.map (Complex.I • H) = Complex.I • H := by
    rw [τ.antilinear, hanti, Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  let X : τ.fixed := ⟨Complex.I • H, hiH⟩
  have hX : X ≠ 0 := by
    intro h
    have hn : Complex.I • H = 0 := congrArg Subtype.val h
    exact hH ((smul_eq_zero.mp hn).resolve_left Complex.I_ne_zero)
  have hpos : 0 < (killingForm ℂ L H H).re := by
    have hK := killing_fixed τ X X
    change killingForm ℂ L (Complex.I • H) (Complex.I • H) = _ at hK
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, Complex.I_mul_I,
      neg_one_mul] at hK
    have hr := congrArg Complex.re hK
    simp only [Complex.neg_re, Complex.ofReal_re] at hr
    linarith [hτ X hX]
  have hpair : (0 : ℝ) < (killingForm ℂ L F E).re := by
    have hi : killingForm ℂ L ⁅H, E⁆ F = killingForm ℂ L H ⁅E, F⁆ :=
      LieModule.traceForm_apply_lie_apply ℂ L L H E F
    rw [hEF, hHE, map_smul, LinearMap.smul_apply, smul_eq_mul] at hi
    rw [show killingForm ℂ L E F = killingForm ℂ L F E from
      LieModule.traceForm_comm ℂ L L E F] at hi
    have hh := congrArg Complex.re hi
    norm_num [Complex.mul_re] at hh
    linarith
  refine ⟨hre, ?_⟩
  have hneg := hermitian_positive τ hτ hE
  change 0 < (-killingForm ℂ L (τ.map E) E).re at hneg
  rw [he, map_smul, LinearMap.smul_apply, smul_eq_mul, hre] at hneg
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hneg
  by_contra! hn
  linarith [mul_nonneg hn hpair.le]

end CompactSign

section CoefficientConjugation

open Specs.RootGroups (rootPoint)

open private twistGroupBaseChangeIso twistBaseChangeIso scalarSchemeMap twist fieldAutomorphismSpec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private conjugateTestPoint conjugateTestPoint_left coefficientSchemeMap_involutive
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private abbrev coefficientConj := Complex.conjAe

private def twistMorphism {H G : AffineAlgebraicGroup ℝ}
    (f : complexGroup H ⟶ complexGroup G) : complexGroup H ⟶ complexGroup G :=
  ((twistGroupBaseChangeIso coefficientConj).app H.val).inv ≫
    ((twist coefficientConj).mapGrp.map f) ≫ ((twistGroupBaseChangeIso coefficientConj).app G.val).hom

private theorem twistMorphism_commutes {H G : AffineAlgebraicGroup ℝ}
    (f : complexGroup H ⟶ complexGroup G) :
    f.hom.hom.left ≫ scalarSchemeMap coefficientConj G.val.X =
      scalarSchemeMap coefficientConj H.val.X ≫ (twistMorphism f).hom.hom.left := by
  let X := H.val.X
  let Y := G.val.X
  let S := (fieldAutomorphismSpec coefficientConj).hom
  let eX := (twistBaseChangeIso coefficientConj).app X
  let eY := (twistBaseChangeIso coefficientConj).app Y
  let pX := pullback.fst ((baseChange ℝ ℂ).obj X).hom S
  let pY := pullback.fst ((baseChange ℝ ℂ).obj Y).hom S
  let m := f.hom.hom
  have hmap : ((twist coefficientConj).map m).left ≫ pY = pX ≫ m.left :=
    pullback.lift_fst _ _ _
  have haux : (twistMorphism f).hom.hom.left ≫ scalarSchemeMap coefficientConj Y =
      scalarSchemeMap coefficientConj X ≫ m.left := by
    change (eX.inv.left ≫ ((twist coefficientConj).map m).left ≫ eY.hom.left) ≫
      (eY.inv.left ≫ pY) = (eX.inv.left ≫ pX) ≫ m.left
    let U := Over.forget (Spec (CommRingCat.of ℂ))
    have hi : eY.hom.left ≫ eY.inv.left = 𝟙 _ := (U.mapIso eY).hom_inv_id
    simp only [Category.assoc, reassoc_of% hi, hmap]
  let bX := scalarSchemeMap coefficientConj X
  let bY := scalarSchemeMap coefficientConj Y
  have hbX : bX ≫ bX = 𝟙 _ := coefficientSchemeMap_involutive X
  have hbY : bY ≫ bY = 𝟙 _ := coefficientSchemeMap_involutive Y
  change m.left ≫ bY = _
  calc
    m.left ≫ bY = bX ≫ (bX ≫ m.left) ≫ bY := by simp [← Category.assoc, hbX]
    _ = bX ≫ ((twistMorphism f).hom.hom.left ≫ bY) ≫ bY := by rw [haux]
    _ = bX ≫ (twistMorphism f).hom.hom.left := by
      simp only [Category.assoc, hbY]
      exact congrArg (bX ≫ ·) (Category.comp_id _)

private theorem twistMorphism_onTestPoints {H G : AffineAlgebraicGroup ℝ}
    (f : complexGroup H ⟶ complexGroup G) (R : TestAlgebra ℂ)
    (c : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj R)
    (hc : ∀ z : ℂ, c.hom (algebraMap ℂ R z) = algebraMap ℂ R (coefficientConj z))
    (x : GroupPoints (complexGroup H) R) :
    conjugateTestPoint G R c (x ≫ f.hom.hom) =
      conjugateTestPoint H R c x ≫ (twistMorphism f).hom.hom := by
  apply Over.OverMorphism.ext
  rw [conjugateTestPoint_left G R c hc]
  change Spec.map (CommRingCat.ofHom c.hom.toRingHom) ≫ (x.left ≫ f.hom.hom.left) ≫
    scalarSchemeMap coefficientConj G.val.X =
    (conjugateTestPoint H R c x).left ≫ (twistMorphism f).hom.hom.left
  rw [conjugateTestPoint_left H R c hc]
  simp only [Category.assoc, twistMorphism_commutes]


open private standardAdditiveModel additiveParameterBaseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open private additiveLinePointsIso rootPoint_natural rootPoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private def standardAdditiveGroup (A : AdditiveLine ℝ) : AffineAlgebraicGroup ℝ :=
  letI := A.operations.hopf
  Specs.StandardGroups.spectrum ℝ (Polynomial ℝ)

private theorem additiveLine_realModel (A : AdditiveLine ℂ) :
    ∃ (A₀ : AdditiveLine ℝ) (e : complexGroup (standardAdditiveGroup A₀) ≅ A.group),
      ∀ (R : TestAlgebra ℂ) (z : R),
        baseChangePoint ℝ ℂ (standardAdditiveGroup A₀).val.X R (rootPoint e.inv R z) =
          rootPoint (𝟙 A₀.group) ((restrictTestAlgebra ℝ ℂ).obj R) z := by
  obtain ⟨A₀, _, a, _, ha⟩ := standardAdditiveModel ℝ
  let b := (additiveLinePointsIso A).symm
  have hb (R : TestAlgebra ℂ) (z : R) :
      b.hom.app R (rootPoint (𝟙 A.group) R z) = Multiplicative.ofAdd z :=
    congrArg Multiplicative.ofAdd
      ((LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R).symm_apply_apply z)
  obtain ⟨e, he⟩ := additiveParameterBaseChange A₀ A a b ha hb
  exact ⟨A₀, e, he⟩

private theorem twistRootCoordinate {G : AffineAlgebraicGroup ℝ} {A : AdditiveLine ℂ}
    (f : A.group ⟶ complexGroup G) :
    ∃ y : A.group ⟶ complexGroup G,
      ∀ (R : TestAlgebra ℂ)
        (c : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj R)
        (_ : ∀ z : ℂ, c.hom (algebraMap ℂ R z) = algebraMap ℂ R (coefficientConj z)) (z : R),
      conjugateTestPoint G R c (rootPoint f R z) = rootPoint y R (c.hom z) := by
  obtain ⟨A₀, e, he⟩ := additiveLine_realModel A
  let H₀ := standardAdditiveGroup A₀
  let x : complexGroup H₀ ⟶ complexGroup G := e.hom ≫ f
  refine ⟨e.inv ≫ twistMorphism x, ?_⟩
  intro R c hc z
  have hz : conjugateTestPoint H₀ R c (rootPoint e.inv R z) = rootPoint e.inv R (c.hom z) := by
    let E := baseChangePointsEquiv ℂ H₀.val.X R
    apply E.injective
    change E (E.symm _) = _
    rw [E.apply_symm_apply]
    change mapPoints c (baseChangePoint ℝ ℂ H₀.val.X R (rootPoint e.inv R z)) =
      baseChangePoint ℝ ℂ H₀.val.X R (rootPoint e.inv R (c.hom z))
    rw [he, he]
    exact rootPoint_natural (𝟙 A₀.group) c z
  have hx := twistMorphism_onTestPoints x R c hc (rootPoint e.inv R z)
  rw [hz, ← rootPoint_comp, ← rootPoint_comp] at hx
  have hword : e.inv ≫ x = f := by simp [x]
  rwa [hword] at hx


end CoefficientConjugation


section RootEquivariance

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (HasScalarAction rootPoint)
open private eq_of_complexPoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private affine_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private rootPoint_natural rootPoint_comp characterValue_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private changeRing from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations

set_option maxHeartbeats 700000 in
private theorem scalarAction_of_complexPoints {Q : AffineAlgebraicGroup ℂ}
    {T : Specs.ClosedSubgroup Q.val} (hT : IsSplitTorus T.group) {A : AdditiveLine ℂ}
    (χ : Character T.group) (x : A.group ⟶ Q.val)
    (h : ∀ (t : GroupPoints T.group complexTest) (z : ℂ),
      let p : GroupPoints Q.val complexTest := t ≫ T.inclusion.hom.hom
      p * rootPoint x complexTest z * p⁻¹ = rootPoint x complexTest (characterValue χ complexTest t * z)) :
    HasScalarAction T χ x := by
  let Y := T.group.X ⊗ A.group.X
  letI : IsAffine T.group.X.left := affine_subgroup Q.property.1 T
  letI : IsAffine A.group.X.left := by
    change IsAffine (Spec (CommRingCat.of (Polynomial ℂ)))
    infer_instance
  have hY : IsAffine Y.left := affine_tensor
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hY
  let R := B.unop
  let t : GroupPoints T.group R := e.hom ≫ fst _ _
  let p : GroupPoints Q.val R := t ≫ T.inclusion.hom.hom
  let u : GroupPoints A.group R := e.hom ≫ snd _ _
  obtain ⟨z, hz⟩ := (additivePoints A R).surjective u
  let L : GroupPoints Q.val R := p * rootPoint x R z * p⁻¹
  let V : GroupPoints Q.val R := rootPoint x R (characterValue χ R t * z)
  have transfer {S : TestAlgebra ℂ} (b : R ⟶ S) :
      let t' := mapPoints b t
      let p' : GroupPoints Q.val S := t' ≫ T.inclusion.hom.hom
      mapPoints b L = p' * rootPoint x S (b.hom z) * p'⁻¹ ∧
        mapPoints b V = rootPoint x S (characterValue χ S t' * b.hom z) := by
    intro t' p'
    constructor
    · change (changeRing (G := Q.val) b) (p * rootPoint x R z * p⁻¹) = _
      simp only [map_mul, map_inv]
      have hp : (changeRing (G := Q.val) b) p = p' := rfl
      have hx : (changeRing (G := Q.val) b) (rootPoint x R z) =
          rootPoint x S (b.hom z) := rootPoint_natural x b z
      rw [hp, hx]
    · change mapPoints b (rootPoint x R (characterValue χ R t * z)) = _
      rw [rootPoint_natural, map_mul, characterValue_natural]
  letI : Smooth T.group.X.hom := splitTorusSmooth hT
  let AG : AffineAlgebraicGroup ℂ := letI := A.operations.hopf
    Specs.StandardGroups.spectrum ℂ (Polynomial ℂ)
  letI : Smooth A.group.X.hom := characteristicZeroSmoothness ℂ AG
  letI : Smooth Y.hom := by
    change Smooth (T.group.X ⊗ A.group.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  letI : IsReduced Y.left := isReduced_of_smooth_over_field Y.hom
  letI : LocallyOfFiniteType Q.val.X.hom := Q.property.2.1
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : IsAffineHom Q.val.X.hom := isAffineHom_of_isAffine _
  let FF := algSpec.fullyFaithful (R := CommRingCat.of ℂ)
  have he : e.inv ≫ L = e.inv ≫ V := by
    apply eq_of_complexPoints
    intro v
    let b : R ⟶ complexTest := (FF.preimage (v ≫ e.inv)).unop
    have hbs : (testSpec ℂ).map b.op = v ≫ e.inv := FF.map_preimage (v ≫ e.inv)
    have hv : mapPoints b L = mapPoints b V :=
      (transfer b).1.trans ((h (mapPoints b t) (b.hom z)).trans (transfer b).2.symm)
    simpa only [mapPoints, hbs, Category.assoc] using hv
  have hLV : L = V := (cancel_epi e.inv).mp he
  intro S t₀ z₀
  let w : Points Y S := lift t₀ (additivePoints A S z₀)
  let b : R ⟶ S := (FF.preimage (w ≫ e.inv)).unop
  have hbs : (testSpec ℂ).map b.op = w ≫ e.inv := FF.map_preimage (w ≫ e.inv)
  have ht : mapPoints b t = t₀ := by
    change (testSpec ℂ).map b.op ≫ e.hom ≫ fst _ _ = _
    rw [hbs, Category.assoc, Iso.inv_hom_id_assoc, lift_fst]
  have hu : mapPoints b (additivePoints A R z) = additivePoints A S z₀ := by
    rw [hz]
    change (testSpec ℂ).map b.op ≫ e.hom ≫ snd _ _ = _
    rw [hbs, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]
  change mapPoints b (rootPoint (𝟙 _) R z) = rootPoint (𝟙 _) S z₀ at hu
  rw [rootPoint_natural] at hu
  have hz₀ : b.hom z = z₀ := (additivePoints A S).injective hu
  have h₀ := (transfer b).1.symm.trans ((congrArg (mapPoints b) hLV).trans (transfer b).2)
  rwa [ht, hz₀] at h₀

end RootEquivariance


section AntiholomorphicRootMap

open Specs.RootGroups (rootPoint)
open Specs.ExceptionalCompactInner (realConjugation)
open Specs.ExceptionalLieAutomorphismTransport (onDual dualConjugation coefficientConjugation)
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open private conjugateTestPoint realConjugation_involutive
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

set_option maxHeartbeats 500000 in
private theorem compactAction_on_root {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} (x : A.group ⟶ complexGroup G)
    (ω : MulAut (PointsIn i ℂ)) (a : Aut (complexGroup G))
    (h : ActsOnComplexPoints (i := i) a (fun z => ω (realConjugation G i z)))
    (s : IdentityLieStructure (complexGroup G)) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (τ : Conjugation (Lie ℂ (complexGroup G))),
      (∀ p : Lie ℂ (complexGroup G), ∃ q : Lie ℂ (complexGroup G),
        onDual G q.toMul.val = mapPoints dualConjugation (onDual G p.toMul.val) ∧
        τ.map p = mapPointKernel a.asIso.hom q) →
      ∃ y : A.group ⟶ complexGroup G,
        (∀ z : ℂ,
          ω (baseChangePoint ℝ ℂ G.val.X complexTest (rootPoint x complexTest z)) =
            baseChangePoint ℝ ℂ G.val.X complexTest (rootPoint y complexTest (Complex.conjAe z))) ∧
        τ.map (rootTangent x) = rootTangent y := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro τ hτ
  obtain ⟨b, hb⟩ := twistRootCoordinate x
  let y := b ≫ a.asIso.hom
  refine ⟨y, ?_, ?_⟩
  · intro z
    let p := rootPoint x complexTest z
    let p' := conjugateTestPoint G complexTest coefficientConjugation p
    let E := baseChangePointsEquiv ℂ G.val.X complexTest
    have he : E p' = realConjugation G i (E p) :=
      E.apply_symm_apply _
    have ha := h p'
    change ω (realConjugation G i (E p')) = E (p' ≫ a.asIso.hom.hom.hom) at ha
    have hi : realConjugation G i (realConjugation G i (E p)) = E p :=
      realConjugation_involutive G (E p)
    rw [he, hi] at ha
    have hp : p' = rootPoint b complexTest (Complex.conjAe z) :=
      hb complexTest coefficientConjugation (fun _ => rfl) z
    rw [hp, ← rootPoint_comp] at ha
    exact ha
  · obtain ⟨q, hq, hmap⟩ := hτ (rootTangent x)
    have hc (z : ℂ) : dualConjugation.hom (algebraMap ℂ (DualNumber ℂ) z) =
        algebraMap ℂ (DualNumber ℂ) (Complex.conjAe z) := by
      apply TrivSqZeroExt.ext
      · rfl
      · exact map_zero Complex.conjAe
    have hp := hb dualTest dualConjugation hc (DualNumber.eps : DualNumber ℂ)
    have heps : dualConjugation.hom (DualNumber.eps : DualNumber ℂ) = DualNumber.eps := by
      apply TrivSqZeroExt.ext
      · exact map_zero Complex.conjAe
      · exact map_one Complex.conjAe
    rw [heps] at hp
    let E := baseChangePointsEquiv ℂ G.val.X dualTest
    have hq' : q.toMul.val =
        conjugateTestPoint G dualTest dualConjugation (rootPoint x dualTest DualNumber.eps) := by
      apply E.injective
      exact hq.trans (E.apply_symm_apply _).symm
    rw [hmap]
    apply Additive.toMul.injective
    apply Subtype.ext
    change q.toMul.val ≫ a.asIso.hom.hom.hom = rootPoint y dualTest DualNumber.eps
    rw [hq', hp, ← rootPoint_comp]

end AntiholomorphicRootMap


section TorusInversion

open Specs.CharacterPairing (characterValue)
open private characterUnit characterUnitOnPoints characterUnit_cocharacter characterValue_eq_unit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private def conjugateInverseHom : ℂˣ →* ℂˣ :=
  invMonoidHom.comp (Units.map Complex.conjAe.toMonoidHom)

private theorem characterUnit_coordinates {P : SplitBorelPair ℂ} {n : ℕ}
    (c : Fin n → Cocharacter P.T.group) (z : Fin n → ℂˣ) (χ : Character P.T.group) :
    characterUnit χ complexTest (torusFromUnits (P := P) c z) =
      (List.ofFn fun j => z j ^ Specs.CharacterPairing.pairing P.T.group χ (c j)).prod := by
  change characterUnitOnPoints χ complexTest (torusFromUnits (P := P) c z) = _
  simp only [torusFromUnits, map_list_prod, List.map_ofFn]
  apply congrArg (fun f : Fin n → ℂˣ => (List.ofFn f).prod)
  funext j
  exact (congrArg (characterUnit χ complexTest) (cocharacterEvaluation_apply (c j) (z j))).trans
    (characterUnit_cocharacter χ (c j) complexTest (z j))

private theorem character_torusInversion {P : SplitBorelPair ℂ} {n : ℕ}
    (c : Fin n → Cocharacter P.T.group) (z : Fin n → ℂˣ) (χ : Character P.T.group) :
    characterValue χ complexTest (torusFromUnits (P := P) c (conjugateInverseUnit ∘ z)) =
      (Complex.conjAe (characterValue χ complexTest (torusFromUnits (P := P) c z)))⁻¹ := by
  rw [characterValue_eq_unit, characterValue_eq_unit, characterUnit_coordinates, characterUnit_coordinates]
  have hn (u : ℂˣ) : (↑(conjugateInverseHom u) : ℂ) = (Complex.conjAe (u : ℂ))⁻¹ := by
    change (↑((Units.map Complex.conjAe.toMonoidHom u)⁻¹) : ℂ) = _
    rw [Units.val_inv_eq_inv_val]
    rfl
  rw [← hn]
  apply congrArg Units.val
  change (List.ofFn (fun j => conjugateInverseHom (z j) ^
      Specs.CharacterPairing.pairing P.T.group χ (c j))).prod =
    conjugateInverseHom (List.ofFn (fun j => z j ^
      Specs.CharacterPairing.pairing P.T.group χ (c j))).prod
  simp only [map_list_prod, List.map_ofFn]
  apply congrArg (fun f : Fin n → ℂˣ => (List.ofFn f).prod)
  funext j
  exact (map_zpow conjugateInverseHom (z j) _).symm

private theorem torusInversion_on_characters {G : AffineAlgebraicGroup ℝ}
    {i : MatrixRealization G} {A : AdditiveLine ℂ} {P : PinnedGroup A}
    (e : P.pair.G.val ≅ complexGroup G) {a : PairAction P.pair} {θ : MulAut (PointsIn i ℂ)}
    (d : DiagramDecomposition (i := i) e a θ) (ω : MulAut (PointsIn i ℂ))
    (h : ConjugateInversion (i := i) e ω) :
    ∀ t : GroupPoints P.pair.T.group complexTest,
      ∃ t' : GroupPoints P.pair.T.group complexTest,
        ω (pointMap (i := i) e P.pair.T.inclusion t) = pointMap (i := i) e P.pair.T.inclusion t' ∧
        ∀ χ : Character P.pair.T.group,
          characterValue χ complexTest t' = (Complex.conjAe (characterValue χ complexTest t))⁻¹ := by
  let D := d.datum
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let c := fun j => simpleCoroot D (simple D d.numbering j)
  obtain ⟨b, _, hb, _, _, _⟩ := RootData.AbsoluteDynkinTypes.cartanCoordinates D.datum.rootDatum D.base
    d.full_coroot_lattice (CartanMatrix.E 6) d.numbering d.cartan
  intro t
  obtain ⟨z, rfl⟩ := (torusFromUnits_bijective D c b hb).2 t
  refine ⟨torusFromUnits (P := P.pair) c (conjugateInverseUnit ∘ z), ?_, ?_⟩
  · exact torusCoordinates_conjugateInversion e D c ω h z
  · exact character_torusInversion c z

end TorusInversion


section RootLine

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure ClosedSubgroup)
open Specs.CharacterPairing (characterValue adjointWeightSpace adjointWeightVectors)
open Specs.RootGroups (rootPoint HasScalarAction)
open Specs.AdjointRepresentation (constants dualMap scale)
open Specs.GeometricRadicals (IsSplitTorus)
open private rootPoint_comp rootPoint_natural characterValue_natural characterUnit_inv
  characterValue_eq_unit rootPoint_injective_of_mono rootPoint_zero additiveLine_tangent_point base_change_root_eps
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private hom_eq_of_differential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport

private theorem pointMap_id_injective {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) :
    Function.Injective (pointMap (i := i) e (𝟙 _)) := by
  let F := groupPointsFunctor ℂ ⋙ (CategoryTheory.evaluation (TestAlgebra ℂ) GrpCat).obj complexTest
  let b := (forget GrpCat).mapIso (F.mapIso e)
  exact (baseChangePointGroupEquiv ℂ G.val complexTest).injective.comp (by
    simp only [Category.id_comp]
    exact b.toEquiv.injective)

private theorem pointMap_comp {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    {Q J : GroupScheme ℂ} (f : Q ⟶ J) (g : J ⟶ P.G.val)
    (v : GroupPoints Q complexTest) :
    pointMap (i := i) e g (v ≫ f.hom.hom) = pointMap (i := i) e (f ≫ g) v := by
  change baseChangePoint ℝ ℂ G.val.X complexTest ((v ≫ f.hom.hom) ≫ (g ≫ e.hom).hom.hom) =
    baseChangePoint ℝ ℂ G.val.X complexTest (v ≫ ((f ≫ g) ≫ e.hom).hom.hom)
  exact congrArg (baseChangePoint ℝ ℂ G.val.X complexTest)
    ((Category.assoc _ _ _).trans (congrArg (fun c : Q ⟶ complexGroup G => v ≫ c.hom.hom)
      (Category.assoc f g e.hom).symm))

set_option maxHeartbeats 550000 in
private theorem oppositeScalarAction {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    (ω : MulAut (PointsIn i ℂ)) (hω : Function.Involutive ω)
    (hT : ∀ t : GroupPoints P.T.group complexTest, ∃ t' : GroupPoints P.T.group complexTest,
      ω (pointMap (i := i) e P.T.inclusion t) = pointMap (i := i) e P.T.inclusion t' ∧
      ∀ χ : Character P.T.group,
        characterValue χ complexTest t' = (Complex.conjAe (characterValue χ complexTest t))⁻¹)
    {A : AdditiveLine ℂ} {α : Character P.T.group} {x y : A.group ⟶ P.G.val}
    (hx : HasScalarAction P.T α x)
    (hy : ∀ z : ℂ, ω (pointMap (i := i) e (𝟙 _) (rootPoint x complexTest z)) =
      pointMap (i := i) e (𝟙 _) (rootPoint y complexTest (Complex.conjAe z))) :
    HasScalarAction P.T α⁻¹ y := by
  apply scalarAction_of_complexPoints P.split
  intro t z
  let F := pointMap (i := i) e (𝟙 _)
  obtain ⟨t', ht, htχ⟩ := hT t
  have ht' : ω (pointMap (i := i) e P.T.inclusion t') =
      pointMap (i := i) e P.T.inclusion t := (congrArg ω ht).symm.trans (hω _)
  have hc (s : GroupPoints P.T.group complexTest) :
      F (s ≫ P.T.inclusion.hom.hom) = pointMap (i := i) e P.T.inclusion s := by
    rw [pointMap_comp, Category.comp_id]
  have he := congrArg (fun v => ω (F v)) (hx complexTest t' (Complex.conjAe z))
  simp only [map_mul, map_inv, hc, ht'] at he
  dsimp only [F] at he
  rw [hy, hy] at he
  have hcj (a : ℂ) : Complex.conjAe (Complex.conjAe a) = a := star_star a
  rw [hcj] at he
  apply pointMap_id_injective (i := i) e
  change F (_ * _ * _⁻¹) = F _
  simp only [map_mul, map_inv, hc]
  refine he.trans ?_
  have hχ : characterValue α⁻¹ complexTest t = (characterValue α complexTest t)⁻¹ := by
    rw [characterValue_eq_unit, characterValue_eq_unit, characterUnit_inv, Units.val_inv_eq_inv_val]
  have hparam : Complex.conjAe (characterValue α complexTest t' * Complex.conjAe z) =
      characterValue α⁻¹ complexTest t * z := by
    rw [map_mul, htχ α, map_inv₀, hcj, hcj, hχ]
  exact congrArg (fun v => F (rootPoint y complexTest v)) hparam

private theorem rootTangent_ne_zero {J : GroupScheme ℂ} {A : AdditiveLine ℂ} (x : A.group ⟶ J)
    [Mono x.hom.hom] : rootTangent x ≠ 0 := by
  intro h
  have hz := congrArg (fun v : Lie ℂ J => v.toMul.val) h
  change rootPoint x dualTest DualNumber.eps = 1 at hz
  rw [← rootPoint_zero x dualTest] at hz
  have he := rootPoint_injective_of_mono x dualTest hz
  exact one_ne_zero (congrArg (fun z : DualNumber ℂ => z.snd) he)

private theorem rootTangent_weight {J : GroupScheme ℂ} {A : AdditiveLine ℂ}
    {T : ClosedSubgroup J} {α : Character T.group} {x : A.group ⟶ J}
    (hx : HasScalarAction T α x) : rootTangent x ∈ adjointWeightVectors T α := by
  intro R t
  let B := CommAlgCat.of ℂ (DualNumber R)
  let f := dualMap (CommAlgCat.ofHom (Algebra.ofId ℂ R))
  let u := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
  change (u : GroupPoints J B) * (mapPoints f (rootPoint x dualTest DualNumber.eps) : GroupPoints J B) *
    u⁻¹ = mapPoints (scale R (characterValue α R t))
      (mapPoints f (rootPoint x dualTest DualNumber.eps))
  rw [base_change_root_eps, rootPoint_natural]
  have hp := hx B (mapPoints (constants R) t) (DualNumber.eps : DualNumber R)
  rw [characterValue_natural] at hp
  refine hp.trans (congrArg (rootPoint x B) ?_)
  apply TrivSqZeroExt.ext
  · change characterValue α R t * 0 = 0
    exact mul_zero _
  · change characterValue α R t * 1 + 0 * 0 = characterValue α R t * 1
    rw [mul_zero, add_zero]

private theorem rootHom_eq_of_tangent {Q : AffineAlgebraicGroup ℂ} {A : AdditiveLine ℂ}
    (x y : A.group ⟶ Q.val) (h : rootTangent x = rootTangent y) : x = y := by
  let A₀ : AffineAlgebraicGroup ℂ := letI := A.operations.hopf
    Specs.StandardGroups.spectrum ℂ (Polynomial ℂ)
  letI : IsIntegral A₀.val.X.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Polynomial ℂ))))
  apply hom_eq_of_differential (H := A₀) (N := Q)
  intro v
  obtain ⟨s, hs⟩ := additiveLine_tangent_point A (Iso.refl A.group) v
  apply Additive.toMul.injective
  apply Subtype.ext
  change v.toMul.val ≫ x.hom.hom = v.toMul.val ≫ y.hom.hom
  rw [hs, ← rootPoint_comp, ← rootPoint_comp, Iso.refl_hom, Category.id_comp, Category.id_comp]
  let b : dualTest ⟶ dualTest := CommAlgCat.ofHom (dualNumberScale s)
  have he := congrArg (fun p : Lie ℂ Q.val => mapPoints b p.toMul.val) h
  change mapPoints b (rootPoint x dualTest (DualNumber.eps : DualNumber ℂ)) =
    mapPoints b (rootPoint y dualTest (DualNumber.eps : DualNumber ℂ)) at he
  have hb : b.hom (DualNumber.eps : DualNumber ℂ) = (⟨0, s⟩ : DualNumber ℂ) := by
    change dualNumberScale s DualNumber.eps = (⟨0, s⟩ : DualNumber ℂ)
    apply TrivSqZeroExt.ext
    · exact TrivSqZeroExt.fst_map _ _
    · rw [dualNumberScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply]
      change s * 1 = s
      exact mul_one s
  rwa [rootPoint_natural, rootPoint_natural, hb] at he

end RootLine


section RootScale

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure ClosedSubgroup)
open Specs.RootGroups (rootPoint HasScalarAction CorootReflection)
open Specs.CharacterPairing (absoluteRoots characterValue pairing adjointWeightSpace)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open private scaleIso scaleIso_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private rootPoint_comp rootPoint_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem compactConjugation_coroot_neg {L : Type} [LieRing L] [LieAlgebra ℂ L]
    (τ : Conjugation L) (E F H : L) (hF : F ≠ 0)
    (hEF : ⁅E, F⁆ = H) (hHE : ⁅H, E⁆ = (2 : ℂ) • E)
    (hHF : ⁅H, F⁆ = (-2 : ℂ) • F)
    (a : ℂ) (ha : a ≠ 0) (he : τ.map E = a • F) : τ.map H = -H := by
  have hb : star a ≠ 0 := by simpa using ha
  have hf : τ.map F = (star a)⁻¹ • E := by
    have hh := congrArg τ.map he
    rw [τ.involutive, τ.antilinear] at hh
    rw [hh, smul_smul, inv_mul_cancel₀ hb, one_smul]
  let q := a * (star a)⁻¹
  have hH : τ.map H = (-q) • H := by
    have h := τ.map.map_lie E F
    rw [hEF, he, hf, smul_lie, lie_smul, smul_smul, ← lie_skew F E, hEF, smul_neg] at h
    exact h.trans (neg_smul q H).symm
  have h := τ.map.map_lie H E
  rw [hHE, τ.antilinear, show star (2 : ℂ) = 2 by norm_num, he, hH,
    smul_lie, lie_smul, hHF, smul_smul, smul_smul, smul_smul] at h
  have hq := (smul_left_injective ℂ hF) h
  have hq' : 1 * (a * 2) = q * (a * 2) := by linear_combination hq
  have hq₁ := mul_right_cancel₀ (mul_ne_zero ha (by norm_num)) hq'
  rw [hH, ← hq₁, neg_smul, one_smul]

private theorem scaledRootPoint {J : GroupScheme ℂ} {A : AdditiveLine ℂ}
    (x : A.group ⟶ J) (c : ℂˣ) (R : TestAlgebra ℂ) (z : R) :
    rootPoint ((scaleIso A A c).hom ≫ x) R z = rootPoint x R (algebraMap ℂ R (c : ℂ) * z) := by
  rw [rootPoint_comp, scaleIso_point, rootPoint_eq]

private theorem scaledRootTangent {J : GroupScheme ℂ} {A : AdditiveLine ℂ}
    (x : A.group ⟶ J) (c : ℂˣ) (s : IdentityLieStructure J) :
    rootTangent ((scaleIso A A c).hom ≫ x) =
      @SMul.smul ℂ (Lie ℂ J) s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul (c : ℂ)
        (rootTangent x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change rootPoint ((scaleIso A A c).hom ≫ x) dualTest DualNumber.eps = _
  rw [rootTangent_smul x s, scaledRootPoint]
  apply congrArg (rootPoint x dualTest)
  apply TrivSqZeroExt.ext
  · change (c : ℂ) * 0 = 0
    exact mul_zero _
  · change (c : ℂ) * 1 + 0 * 0 = (c : ℂ)
    simp

private theorem rootTangent_ne_zero_for {J : GroupScheme ℂ} {A : AdditiveLine ℂ}
    (x : A.group ⟶ J) [Mono x.hom.hom] (s : IdentityLieStructure J) :
    rootTangent x ≠ @Zero.zero (Lie ℂ J) s.lieRing.toAddCommGroup.toZero := by
  have hz := congrArg (fun a : AddGroup (Lie ℂ J) => a.toZero.zero) s.group_law
  rw [hz]
  exact rootTangent_ne_zero x

set_option maxHeartbeats 650000 in
private theorem scale_of_opposite_tangent {Q : AffineAlgebraicGroup ℂ} {A : AdditiveLine ℂ}
    (s : IdentityLieStructure Q.val) {T : ClosedSubgroup Q.val} {α : Character T.group}
    {x y y' : A.group ⟶ Q.val} [Mono x.hom.hom] [Mono y.hom.hom]
    (r : CorootReflection T α x y) (hx : HasScalarAction T α x)
    (hy : HasScalarAction T α⁻¹ y) (hy' : HasScalarAction T α⁻¹ y')
    (hpair : pairing T.group α⁻¹ r.coroot = -2)
    (hdim : letI := s.lieRing; letI := s.lieAlgebra; Module.finrank ℂ (adjointWeightSpace T α⁻¹ s) = 1) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (τ : Conjugation (Lie ℂ Q.val)),
      _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact τ →
      τ.map (rootTangent x) = rootTangent y' →
      ∃ c : ℂˣ, (c : ℂ) = ((c : ℂ).re : ℂ) ∧ (c : ℂ).re < 0 ∧
        y' = (scaleIso A A c).hom ≫ y := by
  letI : LieRing (Lie ℂ Q.val) := s.lieRing
  letI : LieAlgebra ℂ (Lie ℂ Q.val) := s.lieAlgebra
  letI : AddCommGroup (Lie ℂ Q.val) := s.lieRing.toAddCommGroup
  letI : Module ℂ (Lie ℂ Q.val) := s.lieAlgebra.toModule
  letI : Zero (Lie ℂ Q.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℂ (Lie ℂ Q.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  intro τ hτ hτE
  let E : Lie ℂ Q.val := rootTangent x
  let F : Lie ℂ Q.val := rootTangent y
  let H : Lie ℂ Q.val := corootTangent T r.coroot
  have hE : E ≠ 0 := rootTangent_ne_zero_for x s
  have hF : F ≠ 0 := rootTangent_ne_zero_for y s
  let W := adjointWeightSpace T α⁻¹ s
  have hW : W = ℂ ∙ F :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim (Submodule.subset_span (rootTangent_weight hy)) hF
  have hy'm : rootTangent y' ∈ ℂ ∙ F := hW ▸ Submodule.subset_span (rootTangent_weight hy')
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy'm
  have hτ' : τ.map E = b • F := hτE.trans hb.symm
  have hb₀ : b ≠ 0 := by
    intro hn
    apply hE
    apply τ.involutive.injective
    rw [hτ', hn, zero_smul, map_zero]
  have hEF : ⁅E, F⁆ = H := linked_tangent_bracket r hx hy s
  have hHE : ⁅H, E⁆ = (2 : ℂ) • E := by
    have hc := coroot_tangent_bracket r.coroot hx s 2 r.root_pairing (Or.inl rfl)
    exact hc
  have hHF : ⁅H, F⁆ = (-2 : ℂ) • F := by
    have hc := coroot_tangent_bracket r.coroot hy s (-2) hpair (Or.inr rfl)
    rw [show ((-2 : ℤ) : ℂ) = -2 by norm_num] at hc
    exact hc
  have hH : H ≠ 0 := by
    intro hn
    rw [hn, zero_lie] at hHE
    exact hE ((smul_eq_zero.mp hHE.symm).resolve_left (by norm_num))
  have hAnti := compactConjugation_coroot_neg τ E F H hF hEF hHE hHF b hb₀ hτ'
  obtain ⟨_, basis, _, _, _, _, _, _, _⟩ := adjointRepresentation ℂ Q s
  letI : FiniteDimensional ℂ (Lie ℂ Q.val) := Module.Finite.of_basis basis
  obtain ⟨hreal, hneg⟩ := compactConjugation_scale_neg τ hτ E F H hE hH hEF hHE hAnti b hb₀ hτ'
  let c := Units.mk0 b hb₀
  refine ⟨c, hreal, hneg, rootHom_eq_of_tangent (Q := Q) _ _ ?_⟩
  rw [scaledRootTangent y c s]
  exact hb.symm

set_option maxHeartbeats 750000 in
private theorem compactRootScale {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {ω θ : MulAut (PointsIn i ℂ)} (hOut : OuterInvolutions (i := i) ω θ)
    {P : SplitBorelPair ℂ} (h : P.G = Specs.Unipotent.baseChangedAlgebraicGroup ℂ G)
    (hT : ∀ t : GroupPoints P.T.group complexTest, ∃ t' : GroupPoints P.T.group complexTest,
      ω (pointMap (i := i) (comparison h) P.T.inclusion t) =
        pointMap (i := i) (comparison h) P.T.inclusion t' ∧
      ∀ χ : Character P.T.group,
        characterValue χ complexTest t' = (Complex.conjAe (characterValue χ complexTest t))⁻¹)
    {A : AdditiveLine ℂ} {α : Character P.T.group} {x y : A.group ⟶ P.G.val}
    [Mono x.hom.hom] [Mono y.hom.hom]
    (r : CorootReflection P.T α x y) (hx : HasScalarAction P.T α x)
    (hy : HasScalarAction P.T α⁻¹ y)
    (habs : α⁻¹ ∈ absoluteRoots P.T) (hpair : pairing P.T.group α⁻¹ r.coroot = -2) :
    ∃ a : ℝ, a < 0 ∧ ∀ z : ℂ,
      ω (pointMap (i := i) (comparison h) (𝟙 _) (rootPoint x complexTest z)) =
        pointMap (i := i) (comparison h) (𝟙 _) (rootPoint y complexTest (a * Complex.conjAe z)) := by
  cases P with
  | mk Q hQ T hsplit hmax B hb hc =>
    change Q = Specs.Unipotent.baseChangedAlgebraicGroup ℂ G at h
    subst Q
    let Q := Specs.Unipotent.baseChangedAlgebraicGroup ℂ G
    let P : SplitBorelPair ℂ := ⟨Q, hQ, T, hsplit, hmax, B, hb, hc⟩
    let e := comparison (P := P) (G := G) rfl
    let M := pointMap (i := i) e (𝟙 _)
    have hM (z : GroupPoints Q.val complexTest) : M z =
        baseChangePoint ℝ ℂ G.val.X complexTest z := by
      change pointMap (i := i) e (𝟙 _) z = _
      unfold pointMap
      change baseChangePoint ℝ ℂ G.val.X complexTest (z ≫ (𝟙 _ ≫ e.hom).hom.hom) = _
      change baseChangePoint ℝ ℂ G.val.X complexTest (z ≫ (𝟙 _ ≫ 𝟙 Q.val).hom.hom) = _
      rw [Category.id_comp]
      exact congrArg (baseChangePoint ℝ ℂ G.val.X complexTest) (Category.comp_id z)
    obtain ⟨a, ha, s, τ, hτ, hdual⟩ := hOut.compact_differential
    letI : LieRing (Lie ℂ (complexGroup G)) := s.lieRing
    letI : LieAlgebra ℂ (Lie ℂ (complexGroup G)) := s.lieAlgebra
    obtain ⟨y', hy', hτE⟩ := compactAction_on_root x ω a ha s τ hdual
    have hyval (z : ℂ) :
        ω (M (rootPoint x complexTest z)) =
          M (rootPoint y' complexTest (Complex.conjAe z)) := by
      rw [hM, hM]
      exact hy' z
    have hy'weight := oppositeScalarAction e ω hOut.compact_involutive hT hx hyval
    have hdim := ((RootData.RootGroups.rootSubgroups Q hQ T hsplit hmax).2 α⁻¹ habs).1 s
    obtain ⟨c, hreal, hneg, heq⟩ :=
      scale_of_opposite_tangent (Q := Q) s r hx hy hy'weight hpair hdim τ hτ hτE
    refine ⟨(c : ℂ).re, hneg, ?_⟩
    intro z
    have hz := hyval z
    rw [heq, scaledRootPoint, show algebraMap ℂ complexTest (c : ℂ) = (c : ℂ) from rfl, hreal] at hz
    exact hz

end RootScale


section NormalizePinning

open Specs.Pinning (RootCoordinate)
open Specs.CharacterPairing (absoluteRoots pairing characterValue)
open Specs.RootGroups (CorootReflection rootPoint)
open LinearAlgebraicGroups.Classification.RankTwoRelations (linkedOppositeCoordinate)
open private rescale rescale_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private rescaleLinkedPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoRelations
open private linked_coroot from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting

private theorem positiveRescaling (a : ℝ) (ha : a < 0) :
    ∃ c : ℂˣ, ∀ z : ℂ, (a : ℂ) * Complex.conjAe ((c : ℂ) * z) =
      (↑c⁻¹ : ℂ) * (-Complex.conjAe z) := by
  let v := Real.sqrt (-a)⁻¹
  have hv : 0 < v := Real.sqrt_pos_of_pos (inv_pos.mpr (neg_pos.mpr ha))
  have hv' : v ^ 2 = (-a)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr (neg_pos.mpr ha).le)
  have hvn : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  let c := Units.mk0 (v : ℂ) hvn
  have hmul : a * v = -v⁻¹ := by
    apply mul_right_cancel₀ hv.ne'
    calc
      a * v * v = a * v ^ 2 := by ring
      _ = -1 := by rw [hv', inv_neg, mul_neg, mul_inv_cancel₀ (ne_of_lt ha)]
      _ = (-v⁻¹) * v := by simp [hv.ne']
  have hmul' : (a : ℂ) * (v : ℂ) = -(v : ℂ)⁻¹ := by exact_mod_cast hmul
  refine ⟨c, fun z => ?_⟩
  change (a : ℂ) * Complex.conjAe ((v : ℂ) * z) = (v : ℂ)⁻¹ * (-Complex.conjAe z)
  rw [map_mul, show Complex.conjAe (v : ℂ) = (v : ℂ) by exact Complex.conj_ofReal v,
    ← mul_assoc, hmul']
  ring

set_option maxHeartbeats 800000 in
private theorem compactPinningExists {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {ω θ : MulAut (PointsIn i ℂ)} (hOut : OuterInvolutions (i := i) ω θ)
    {A : AdditiveLine ℂ} (P : PinnedGroup A)
    (h : P.pair.G = Specs.Unipotent.baseChangedAlgebraicGroup ℂ G)
    (a : PairAction P.pair) (d : DiagramDecomposition (i := i) (comparison h) a θ)
    (hT : ConjugateInversion (i := i) (comparison h) ω) :
    ∃ p : Specs.Pinning.Pinning A P.pair P.roots,
      let P' : PinnedGroup A := ⟨P.pair, P.roots, p⟩
      ∀ D : AttachedDatum P'.pair, CompactCompatible (P := P') (comparison h) D ω := by
  classical
  let D := d.datum
  letI := D.comm
  let e := comparison (P := P.pair) h
  have hInv := torusInversion_on_characters e d ω hT
  have perRoot (α : Specs.Pinning.SimpleRoot P.pair) :
      ∃ (p : RootCoordinate A P.pair.T (P.roots α.val).val α.val.val)
        (β : Root P.pair.T) (n : RootCoordinate A P.pair.T (P.roots β).val α.val.val⁻¹),
        β.val = α.val.val⁻¹ ∧
        let xp := p.val.hom ≫ (P.roots α.val).val.inclusion
        let xn := n.val.hom ≫ (P.roots β).val.inclusion
        Nonempty (CorootReflection P.pair.T α.val.val xp xn) ∧
        ∀ z : ℂ, ω (onPoints e (𝟙 _) (rootPoint xp complexTest z)) =
          onPoints e (𝟙 _) (rootPoint xn complexTest (-Complex.conjAe z)) := by
    let β := D.datum.rootDatum.reflectionPerm α.val α.val
    have hβ : β.val = α.val.val⁻¹ := by
      apply Additive.ofMul.injective
      rw [← D.datum.root_eq, D.datum.rootDatum.root_reflectionPerm,
        RootPairing.reflection_apply_self, D.datum.root_eq]
      rfl
    obtain ⟨v, ⟨r⟩⟩ := linkedOppositeCoordinate P α.val β hβ (P.pin α)
    let y := v.val.hom ≫ (P.roots β).val.inclusion
    let x := simpleCoordinate P α
    have hy : Specs.RootGroups.HasScalarAction P.pair.T α.val.val⁻¹ y := hβ ▸ v.property
    let v' : RootCoordinate A P.pair.T (P.roots β).val α.val.val⁻¹ := ⟨v.val, hy⟩
    haveI : IsClosedImmersion (P.roots α.val).val.inclusion.hom.hom.left :=
      (P.roots α.val).val.isClosedImmersion
    haveI : IsClosedImmersion (P.roots β).val.inclusion.hom.hom.left :=
      (P.roots β).val.isClosedImmersion
    haveI : Mono (P.roots α.val).val.inclusion.hom.hom := Over.mono_of_mono_left _
    haveI : Mono (P.roots β).val.inclusion.hom.hom := Over.mono_of_mono_left _
    haveI : Mono x.hom.hom := by
      change Mono ((P.pin α).val.hom.hom.hom ≫ (P.roots α.val).val.inclusion.hom.hom)
      infer_instance
    haveI : Mono y.hom.hom := by
      change Mono (v.val.hom.hom.hom ≫ (P.roots β).val.inclusion.hom.hom)
      infer_instance
    have hpair : pairing P.pair.T.group α.val.val⁻¹ r.coroot = -2 := by
      rw [← D.datum.pairing_eq, show Additive.ofMul α.val.val⁻¹ = -Additive.ofMul α.val.val from rfl,
        map_neg, LinearMap.neg_apply, D.datum.pairing_eq, r.root_pairing]
    have hβroot : α.val.val⁻¹ ∈ absoluteRoots P.pair.T := hβ ▸ β.property
    obtain ⟨rootScale, hrootScale, hval⟩ :=
      compactRootScale hOut h hInv (x := x) (y := y) r (P.pin α).property hy hβroot hpair
    obtain ⟨c, hc⟩ := positiveRescaling rootScale hrootScale
    let p : RootCoordinate A P.pair.T (P.roots α.val).val α.val.val := rescale (P.pin α) c
    let n : RootCoordinate A P.pair.T (P.roots β).val α.val.val⁻¹ := rescale v' c⁻¹
    refine ⟨p, β, n, hβ, rescaleLinkedPair P.pair.split (P.pin α) v' r c, ?_⟩
    intro z
    change ω (onPoints e (𝟙 _) (rootPoint (p.val.hom ≫ _) complexTest z)) =
      onPoints e (𝟙 _) (rootPoint (n.val.hom ≫ _) complexTest (-Complex.conjAe z))
    simp only [p, n, rescale_point]
    exact (hval ((c : ℂ) * z)).trans
      (congrArg (fun w : ℂ => onPoints e (𝟙 _) (rootPoint y complexTest w)) (hc z))
  choose p β n hβ hr hv using perRoot
  refine ⟨p, ?_⟩
  dsimp only
  intro D' α
  letI := D'.comm
  obtain ⟨r⟩ := hr α
  exact ⟨β α, n α, hβ α, r, linked_coroot D'.datum α.val r, hv α⟩

end NormalizePinning


section NegativeDiagram

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure ClosedSubgroup)
open Specs.CharacterPairing (characterValue adjointWeightSpace adjointWeightVectors)
open Specs.RootGroups (rootPoint HasScalarAction CorootReflection)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private rootPoint_comp rootPoint_injective_of_mono characterValue_eq_unit characterUnit characterUnit_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private torusPointHom torusPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations

private theorem rootTangent_comp_map {J L : GroupScheme ℂ} {A : AdditiveLine ℂ}
    (x : A.group ⟶ J) (f : J ⟶ L) :
    rootTangent (x ≫ f) = mapPointKernel f (rootTangent x) := by
  apply Additive.toMul.injective
  exact Subtype.ext (rootPoint_comp x f dualTest DualNumber.eps)

private theorem corootTangent_comp_map {J : GroupScheme ℂ} (T : ClosedSubgroup J)
    (f : J ⟶ J) (u : T.group ⟶ T.group) (hu : T.inclusion ≫ f = u ≫ T.inclusion)
    (c : Cocharacter T.group) :
    mapPointKernel f (corootTangent T c) = corootTangent T (c ≫ u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change torusPointHom T c dualTest corootTangentUnit ≫ f.hom.hom =
    torusPointHom T (c ≫ u) dualTest corootTangentUnit
  rw [torusPointHom_apply, torusPointHom_apply]
  change (cocharacterPoint c dualTest corootTangentUnit ≫ T.inclusion.hom.hom) ≫ f.hom.hom =
    (cocharacterPoint c dualTest corootTangentUnit ≫ u.hom.hom) ≫ T.inclusion.hom.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v : T.group ⟶ J => cocharacterPoint c dualTest corootTangentUnit ≫ v.hom.hom) hu).trans
      (Category.assoc _ _ _).symm)

set_option maxHeartbeats 600000 in
private theorem oppositeScalarAction_transport {J : GroupScheme ℂ} {A : AdditiveLine ℂ}
    {T : ClosedSubgroup J} {α β : Character T.group} {x y x' : A.group ⟶ J}
    (f : J ⟶ J) (u : T.group ≅ T.group) (hu : T.inclusion ≫ f = u.hom ≫ T.inclusion)
    (hx : HasScalarAction T α x) (hx' : HasScalarAction T β x')
    (hy : HasScalarAction T α⁻¹ y) (he : x ≫ f = x') [Mono x'.hom.hom] :
    HasScalarAction T β⁻¹ (y ≫ f) := by
  intro R t z
  let v : GroupPoints T.group R := t ≫ u.inv.hom.hom
  let p : GroupPoints J R := t ≫ T.inclusion.hom.hom
  let g : GroupPoints J R := v ≫ T.inclusion.hom.hom
  let M := (((groupPointsFunctor ℂ).map f).app R).hom
  have hp : M g = p := by
    change (t ≫ u.inv.hom.hom ≫ T.inclusion.hom.hom) ≫ f.hom.hom = _
    have h₀ : u.inv ≫ T.inclusion ≫ f = T.inclusion := by rw [hu, Iso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).trans (congrArg (fun a : T.group ⟶ J => t ≫ a.hom.hom) h₀)
  have hm {w : A.group ⟶ J} (s : R) : M (rootPoint w R s) = rootPoint (w ≫ f) R s :=
    (rootPoint_comp _ _ _ _).symm
  have h₁ := congrArg M (hx R v (1 : R))
  simp only [map_mul, map_inv, show (v ≫ T.inclusion.hom.hom : GroupPoints J R) = g from rfl,
    hp, hm, he, mul_one] at h₁
  have h₂ := hx' R t (1 : R)
  rw [mul_one] at h₂
  have hc : characterValue α R v = characterValue β R t :=
    rootPoint_injective_of_mono x' R (h₁.symm.trans h₂)
  have hunit : characterUnit α R v = characterUnit β R t := Units.ext (by
    simpa only [characterValue_eq_unit] using hc)
  have hχ : characterValue α⁻¹ R v = characterValue β⁻¹ R t := by
    rw [characterValue_eq_unit, characterValue_eq_unit, characterUnit_inv, characterUnit_inv, hunit]
  have hw := congrArg M (hy R v z)
  simp only [map_mul, map_inv, show (v ≫ T.inclusion.hom.hom : GroupPoints J R) = g from rfl,
    hp, hm, hχ] at hw
  exact hw

set_option maxHeartbeats 660000 in
private theorem diagram_maps_linked_opposite {P : SplitBorelPair ℂ} {A : AdditiveLine ℂ}
    {α β : Root P.T} {x y x' y' : A.group ⟶ P.G.val}
    (r : CorootReflection P.T α.val x y) (r' : CorootReflection P.T β.val x' y')
    (f : P.G.val ⟶ P.G.val) (u : P.T.group ≅ P.T.group)
    (hu : P.T.inclusion ≫ f = u.hom ≫ P.T.inclusion)
    (he : x ≫ f = x') (hc : r.coroot ≫ u.hom = r'.coroot)
    (hx : HasScalarAction P.T α.val x) (hy : HasScalarAction P.T α.val⁻¹ y)
    (hx' : HasScalarAction P.T β.val x') (hy' : HasScalarAction P.T β.val⁻¹ y')
    [Mono x'.hom.hom] [Mono y'.hom.hom] :
    y ≫ f = y' := by
  let s := identityLieStructure P.G
  letI : LieRing (Lie ℂ P.G.val) := s.lieRing
  letI : LieAlgebra ℂ (Lie ℂ P.G.val) := s.lieAlgebra
  letI : AddCommGroup (Lie ℂ P.G.val) := s.lieRing.toAddCommGroup
  letI : Module ℂ (Lie ℂ P.G.val) := s.lieAlgebra.toModule
  letI : Zero (Lie ℂ P.G.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℂ (Lie ℂ P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  let H := corootTangent P.T r'.coroot
  let E := rootTangent x'
  let F := rootTangent y'
  have hE : E ≠ 0 := rootTangent_ne_zero_for x' s
  have hF : F ≠ 0 := rootTangent_ne_zero_for y' s
  have hH' : ⁅H, E⁆ = (2 : ℂ) • E := by
    exact coroot_tangent_bracket r'.coroot hx' s 2 r'.root_pairing (Or.inl rfl)
  have hH : H ≠ 0 := by
    intro hz
    rw [hz, zero_lie] at hH'
    exact hE ((smul_eq_zero.mp hH'.symm).resolve_left (by norm_num))
  have hOpp := oppositeScalarAction_transport f u hu hx hx' hy he
  have hb : β.val⁻¹ ∈ Specs.CharacterPairing.absoluteRoots P.T :=
    ((RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2
      β.val β.property).2.1 _ |>.mpr (Or.inr rfl) |>.1
  let V := adjointWeightSpace P.T β.val⁻¹ s
  have hdim : Module.finrank ℂ V = 1 :=
    ((RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 β.val⁻¹ hb).1 s
  have hV : V = ℂ ∙ F :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim (Submodule.subset_span (rootTangent_weight hy')) hF
  have hv : rootTangent (y ≫ f) ∈ ℂ ∙ F := hV ▸ Submodule.subset_span (rootTangent_weight hOpp)
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hv
  have hbr : ⁅E, rootTangent (y ≫ f)⁆ = H := by
    letI : IsAffine P.G.val.X.left := P.G.property.1
    obtain ⟨b, hb⟩ := identityDifferentialLieHom ℂ P.G.val P.G.val f s s
    have h := congrArg b (linked_tangent_bracket r hx hy s)
    rw [b.map_lie, hb, hb, hb, ← rootTangent_comp_map, ← rootTangent_comp_map, he,
      corootTangent_comp_map P.T f u.hom hu, hc] at h
    exact h
  have hsc : c • H = (1 : ℂ) • H := by
    rw [← hc', lie_smul, linked_tangent_bracket r' hx' hy'] at hbr
    simpa only [one_smul] using hbr
  have hc₁ : c = 1 := smul_left_injective ℂ hH hsc
  apply rootHom_eq_of_tangent
  rw [← hc', hc₁, one_smul]

end NegativeDiagram


section DiagramCommutation

open Specs.RootGroups (rootPoint)
open Specs.ExceptionalCompactInner (realConjugation)
open private realConjugation_involutive coefficientTwist coefficientTwist_onPoints pointAut_comp eq_of_complexPoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private relativeAut_ext_torus_and_pins from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem acts_unique {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {a : Aut (complexGroup G)} {f g : PointsIn i ℂ → PointsIn i ℂ}
    (hf : ActsOnComplexPoints (i := i) a f) (hg : ActsOnComplexPoints (i := i) a g) : f = g := by
  funext x
  obtain ⟨z, hz⟩ := (baseChangePointGroupEquiv ℂ G.val complexTest).surjective x
  change baseChangePoint ℝ ℂ G.val.X complexTest z = x at hz
  rw [← hz]
  exact (hf z).trans (hg z).symm

private theorem acts_on_coordinate {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G)
    (b : P.G.val ≅ P.G.val) {φ : PointsIn i ℂ → PointsIn i ℂ}
    (hφ : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ b ≪≫ e)) φ)
    {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val) (x : GroupPoints Q complexTest) :
    φ (pointMap (i := i) e f x) = pointMap (i := i) e (f ≫ b.hom) x := by
  have h := acts_onPoints e b hφ (x ≫ f.hom.hom)
  rw [pointMap_comp, Category.comp_id] at h
  have hcomp : (x ≫ f.hom.hom) ≫ b.hom.hom.hom = x ≫ (f ≫ b.hom).hom.hom :=
    Category.assoc _ _ _
  rw [hcomp, pointMap_comp, Category.comp_id] at h
  exact h

private theorem compactConjugate_algebraic {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    (ω δ : MulAut (PointsIn i ℂ)) (hω : Function.Involutive ω)
    (a b : Aut (complexGroup G))
    (ha : ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)))
    (hb : ActsOnComplexPoints (i := i) b δ) :
    ∃ f : Aut (complexGroup G), ActsOnComplexPoints (i := i) f (fun x => ω (δ (ω x))) := by
  let σ := realConjugation G i
  have ha' : (fun x : PointsIn i ℂ => ω (σ x)) = pointAut G a :=
    acts_unique ha (pointAut_acts G a)
  have hw (x : PointsIn i ℂ) : ω x = pointAut G a (σ x) := by
    have h := congrFun ha' (σ x)
    change ω (σ (σ x)) = pointAut G a (σ x) at h
    have he : σ (σ x) = x := realConjugation_involutive G x
    rwa [he] at h
  have hδ : (δ : PointsIn i ℂ → PointsIn i ℂ) = pointAut G b :=
    acts_unique hb (pointAut_acts G b)
  let ai := Aut.of a.asIso.symm
  let b' := coefficientTwist G b
  let f := Aut.of (ai.asIso ≪≫ b'.asIso ≪≫ a.asIso)
  have hai : ∀ x : PointsIn i ℂ, pointAut G ai (pointAut G a x) = x :=
    pointAut_eq_id_of_comp G a ai (by simp [ai])
  have hh (x : PointsIn i ℂ) : ω (δ x) = pointAut G f (ω x) := by
    have hσ : σ (pointAut G b x) = pointAut G b' (σ x) :=
      coefficientTwist_onPoints G b x
    rw [hδ, hw (pointAut G b x), hσ]
    have h₀ := pointAut_comp G (Aut.of (ai.asIso ≪≫ b'.asIso)) a (ω x)
    have h₁ := pointAut_comp G ai b' (ω x)
    change pointAut G f (ω x) = _ at h₀
    rw [h₀, h₁, hw x, hai]
  have hf : (fun x : PointsIn i ℂ => ω (δ (ω x))) = pointAut G f := by
    funext x
    exact (hh (ω x)).trans (congrArg (pointAut G f) (hω x))
  refine ⟨f, ?_⟩
  rw [hf]
  exact pointAut_acts G f

private theorem algAut_eq_of_ambient_generators {A : AdditiveLine ℂ} (P : PinnedGroup A)
    (a b : Aut P.pair.G.val)
    (ha : P.pair.T.inclusion ≫ a.asIso.hom = P.pair.T.inclusion ≫ b.asIso.hom)
    (hv : ∀ α : Specs.Pinning.SimpleRoot P.pair,
      simpleCoordinate P α ≫ a.asIso.hom = simpleCoordinate P α ≫ b.asIso.hom) :
    a = b := by
  let S := pointSource
  have hS : Nonempty S.left := ⟨IsLocalRing.closedPoint ℂ⟩
  apply scalarAut_injective_of_nonempty (S := S)
  apply relativeAut_ext_torus_and_pins (P := P)
  · intro R c t
    change (t ≫ P.pair.T.inclusion.hom.hom) ≫ a.asIso.hom.hom.hom =
      (t ≫ P.pair.T.inclusion.hom.hom) ≫ b.asIso.hom.hom.hom
    exact (Category.assoc _ _ _).trans ((congrArg (fun f : P.pair.T.group ⟶ P.pair.G.val =>
      t ≫ f.hom.hom) ha).trans (Category.assoc _ _ _).symm)
  · intro R c α z
    change rootPoint (simpleCoordinate P α) R z ≫ a.asIso.hom.hom.hom =
      rootPoint (simpleCoordinate P α) R z ≫ b.asIso.hom.hom.hom
    rw [← rootPoint_comp, ← rootPoint_comp, hv]

private theorem hom_eq_of_actual_points {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) {Q : GroupScheme ℂ}
    [IsReduced Q.X.left] [LocallyOfFiniteType Q.X.hom] (a b : Q ⟶ P.G.val)
    (h : ∀ x : GroupPoints Q complexTest, pointMap (i := i) e a x = pointMap (i := i) e b x) :
    a = b := by
  letI : IsAffine P.G.val.X.left := P.G.property.1
  letI : LocallyOfFiniteType P.G.val.X.hom := P.G.property.2.1
  letI : IsAffineHom P.G.val.X.hom := isAffineHom_of_isAffine _
  apply Grp.hom_ext
  apply eq_of_complexPoints
  intro x
  apply pointMap_id_injective (i := i) e
  rw [pointMap_comp, pointMap_comp, Category.comp_id, Category.comp_id]
  exact h x

end DiagramCommutation


section CommuteByRestriction

open Specs.RootGroups (rootPoint)
open Specs.ExceptionalCompactInner (realConjugation)
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme

set_option maxHeartbeats 700000 in
private theorem commute_of_generators {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    {a : PairAction P.pair} {ω θ : MulAut (PointsIn i ℂ)}
    (hOut : OuterInvolutions (i := i) ω θ) (d : DiagramDecomposition (i := i) e a θ)
    (hT : ∀ t : GroupPoints P.pair.T.group complexTest,
      let w := pointMap (i := i) e P.pair.T.inclusion t
      ω (d.pointDiagram w) = d.pointDiagram (ω w))
    (hP : ∀ (α : Specs.Pinning.SimpleRoot P.pair) (z : ℂ),
      let w := pointMap (i := i) e (simpleCoordinate P α) (rootPoint (𝟙 A.group) complexTest z)
      ω (d.pointDiagram w) = d.pointDiagram (ω w)) :
    Function.Commute d.pointDiagram ω := by
  obtain ⟨aω, ha, _⟩ := hOut.compact_differential
  obtain ⟨b, hb⟩ := compactConjugate_algebraic ω d.pointDiagram hOut.compact_involutive
    aω (Aut.of (e.symm ≪≫ d.diagram.group ≪≫ e)) ha d.acts
  let f := e ≪≫ b.asIso ≪≫ e.symm
  have haf : Aut.of (e.symm ≪≫ f ≪≫ e) = b := by
    apply Aut.ext
    apply Iso.ext
    simp [f, Category.assoc]
  have hf : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ f ≪≫ e))
      (fun x => ω (d.pointDiagram (ω x))) := haf.symm ▸ hb
  have agree (w : PointsIn i ℂ) (h : ω (d.pointDiagram w) = d.pointDiagram (ω w)) :
      ω (d.pointDiagram (ω w)) = d.pointDiagram w := by
    rw [← h, hOut.compact_involutive]
  have hTT : P.pair.T.inclusion ≫ f.hom = P.pair.T.inclusion ≫ d.diagram.group.hom := by
    letI : Smooth P.pair.T.group.X.hom := splitTorusSmooth P.pair.split
    letI : IsReduced P.pair.T.group.X.left := isReduced_of_smooth_over_field P.pair.T.group.X.hom
    apply hom_eq_of_actual_points (i := i) e
    intro t
    rw [← acts_on_coordinate e f hf, ← acts_on_coordinate e d.diagram.group d.acts]
    exact agree _ (hT t)
  have hPP (α : Specs.Pinning.SimpleRoot P.pair) :
      simpleCoordinate P α ≫ f.hom = simpleCoordinate P α ≫ d.diagram.group.hom := by
    let A₀ : AffineAlgebraicGroup ℂ := letI := A.operations.hopf
      Specs.StandardGroups.spectrum ℂ (Polynomial ℂ)
    letI : Smooth A.group.X.hom := characteristicZeroSmoothness ℂ A₀
    letI : IsReduced A.group.X.left := isReduced_of_smooth_over_field A.group.X.hom
    apply hom_eq_of_actual_points (i := i) e
    intro z
    obtain ⟨t, rfl⟩ := (RootData.RootGroups.additivePoints A complexTest).surjective z
    rw [← acts_on_coordinate e f hf, ← acts_on_coordinate e d.diagram.group d.acts]
    exact agree _ (hP α t)
  have hf' : Aut.of f = Aut.of d.diagram.group :=
    algAut_eq_of_ambient_generators P _ _ hTT hPP
  have he : f = d.diagram.group := congrArg Aut.asIso hf'
  rw [he] at hf
  have hh := acts_unique d.acts hf
  intro x
  change d.pointDiagram (ω x) = ω (d.pointDiagram x)
  exact (congrFun hh (ω x)).trans (congrArg (fun z => ω (d.pointDiagram z)) (hOut.compact_involutive x))

end CommuteByRestriction


section CompactDiagram

open Specs.RootGroups (rootPoint CorootReflection)
open Specs.Pinning (RootCoordinate)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem diagram_torus_point {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    {a : PairAction P.pair} {θ : MulAut (PointsIn i ℂ)}
    (d : DiagramDecomposition (i := i) e a θ) (c : Cocharacter P.pair.T.group) (u : ℂˣ) :
    d.pointDiagram (pointMap (i := i) e P.pair.T.inclusion (cocharacterPoint c complexTest u)) =
      pointMap (i := i) e P.pair.T.inclusion
        (cocharacterPoint (c ≫ d.diagram.torus.hom) complexTest u) := by
  rw [acts_on_coordinate e d.diagram.group d.acts, d.diagram.torus_comm]
  exact (pointMap_comp e d.diagram.torus.hom P.pair.T.inclusion (cocharacterPoint c complexTest u)).symm

private theorem commute_torus_points {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    {a : PairAction P.pair} {ω θ : MulAut (PointsIn i ℂ)}
    (d : DiagramDecomposition (i := i) e a θ)
    (hT : ConjugateInversion (i := i) e ω) (t : GroupPoints P.pair.T.group complexTest) :
    ω (d.pointDiagram (pointMap (i := i) e P.pair.T.inclusion t)) =
      d.pointDiagram (ω (pointMap (i := i) e P.pair.T.inclusion t)) := by
  let D := d.datum
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let c := fun j => simpleCoroot D (simple D d.numbering j)
  obtain ⟨b, _, hb, _, _, _⟩ := RootData.AbsoluteDynkinTypes.cartanCoordinates D.datum.rootDatum D.base
    d.full_coroot_lattice (CartanMatrix.E 6) d.numbering d.cartan
  obtain ⟨z, rfl⟩ := (torusFromUnits_bijective D c b hb).2 t
  simp only [torusFromUnits, map_list_prod, List.map_ofFn, cocharacterEvaluation_apply]
  apply congrArg (fun f : Fin 6 → PointsIn i ℂ => (List.ofFn f).prod)
  funext j
  change ω (d.pointDiagram (pointMap (i := i) e P.pair.T.inclusion
    (cocharacterPoint (c j) complexTest (z j)))) =
    d.pointDiagram (ω (pointMap (i := i) e P.pair.T.inclusion (cocharacterPoint (c j) complexTest (z j))))
  rw [diagram_torus_point e d]
  have hω (c₀ : Cocharacter P.pair.T.group) (v : ℂˣ) :
      ω (pointMap (i := i) e P.pair.T.inclusion (cocharacterPoint c₀ complexTest v)) =
        pointMap (i := i) e P.pair.T.inclusion (cocharacterPoint c₀ complexTest (conjugateInverseUnit v)) :=
    hT c₀ v
  rw [hω, hω, diagram_torus_point e d]

set_option maxHeartbeats 800000 in
private theorem compactDiagram_commutes {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    {a : PairAction P.pair} {ω θ : MulAut (PointsIn i ℂ)}
    (hOut : OuterInvolutions (i := i) ω θ) (d : DiagramDecomposition (i := i) e a θ)
    (hT : ConjugateInversion (i := i) e ω) (hP : CompactCompatible (i := i) (P := P) e d.datum ω) :
    Function.Commute d.pointDiagram ω := by
  apply commute_of_generators e hOut d (commute_torus_points e d hT)
  classical
  letI := d.datum.comm
  intro α z
  let a₀ : d.datum.base.support :=
    ⟨α.val, (d.datum.simple_iff _).mpr α.property⟩
  let j := d.numbering a₀
  have hj : simple d.datum d.numbering j = α := by
    apply Subtype.ext
    change (d.numbering.symm (d.numbering a₀)).val = a₀.val
    exact congrArg (fun k : d.datum.base.support => k.val) (d.numbering.symm_apply_apply a₀)
  let α' := simple d.datum d.numbering (E6Reflection j)
  have hplus : simpleCoordinate P α ≫ d.diagram.group.hom = simpleCoordinate P α' := by
    rw [← hj]
    exact d.permutes_coordinates j
  have hcoroot : simpleCoroot d.datum α ≫ d.diagram.torus.hom = simpleCoroot d.datum α' := by
    rw [← hj]
    exact d.permutes_coroots j
  obtain ⟨β, y, _, r, hr, h⟩ := hP α
  obtain ⟨β', y', _, r', hr', h'⟩ := hP α'
  let n := y.val.hom ≫ (P.roots β).val.inclusion
  let n' := y'.val.hom ≫ (P.roots β').val.inclusion
  let x' := simpleCoordinate P α'
  haveI : IsClosedImmersion (P.roots α'.val).val.inclusion.hom.hom.left :=
    (P.roots α'.val).val.isClosedImmersion
  haveI : IsClosedImmersion (P.roots β').val.inclusion.hom.hom.left :=
    (P.roots β').val.isClosedImmersion
  haveI : Mono (P.roots α'.val).val.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : Mono (P.roots β').val.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : Mono x'.hom.hom := by
    change Mono ((P.pin α').val.hom.hom.hom ≫ (P.roots α'.val).val.inclusion.hom.hom)
    infer_instance
  haveI : Mono n'.hom.hom := by
    change Mono (y'.val.hom.hom.hom ≫ (P.roots β').val.inclusion.hom.hom)
    infer_instance
  have hneg : n ≫ d.diagram.group.hom = n' :=
    diagram_maps_linked_opposite (x' := x') (y' := n') r r' d.diagram.group.hom d.diagram.torus
      d.diagram.torus_comm hplus (by rw [hr, hr', hcoroot]) (P.pin α).property y.property
      (P.pin α').property y'.property
  let δ := d.pointDiagram
  let L (f : A.group ⟶ P.pair.G.val) (v : ℂ) :=
    pointMap (i := i) e f (rootPoint (𝟙 A.group) complexTest v)
  have hL (f : A.group ⟶ P.pair.G.val) (v : ℂ) :
      L f v = onPoints (i := i) e (𝟙 _) (rootPoint f complexTest v) := by
    change _ = pointMap (i := i) e (𝟙 _) (rootPoint f complexTest v)
    have hf := rootPoint_comp (𝟙 A.group) f complexTest v
    rw [Category.id_comp] at hf
    rw [hf, pointMap_comp, Category.comp_id]
  have hδ (f : A.group ⟶ P.pair.G.val) (v : ℂ) : δ (L f v) = L (f ≫ d.diagram.group.hom) v :=
    acts_on_coordinate e d.diagram.group d.acts f _
  have hlo : ω (L (simpleCoordinate P α) z) = L n (-Complex.conjAe z) := by
    rw [hL, hL]
    exact h z
  have hhi : ω (L x' z) = L n' (-Complex.conjAe z) := by
    rw [hL, hL]
    exact h' z
  change ω (δ (L (simpleCoordinate P α) z)) = δ (ω (L (simpleCoordinate P α) z))
  rw [hδ, hplus, hlo, hδ, hneg]
  exact hhi

end CompactDiagram

/-- The actual complex Borel pair admits a compact pinning and its pinned
diagram reflection differs from the given outer involution by compact torus conjugation. -/
theorem compactPinning : CompactPinningStatement := by
  intro G i hs hsc ht ω θ hOut P h a ha hT
  obtain ⟨A⟩ := Classification.Pinning.additiveLineExists ℂ
  obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  let P₀ : PinnedGroup A := ⟨P, U, p⟩
  obtain ⟨d₀⟩ := diagramDecomposition G i hs hsc ht A P₀ h a θ ha
    hOut.outer_involutive hOut.outer
  obtain ⟨p', hp'⟩ := compactPinningExists hOut P₀ h a d₀ hT
  let P' : PinnedGroup A := ⟨P, U, p'⟩
  obtain ⟨d⟩ := diagramDecomposition G i hs hsc ht A P' h a θ ha
    hOut.outer_involutive hOut.outer
  have hc := hp' d.datum
  have hcomm := compactDiagram_commutes (comparison h) hOut d hT hc
  refine ⟨A, U, p', d, hc, hcomm, ?_⟩
  exact compactImplementer (P := P') (comparison (G := G) (P := P) h) a hOut hs.1 hT d hcomm

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactPinning
