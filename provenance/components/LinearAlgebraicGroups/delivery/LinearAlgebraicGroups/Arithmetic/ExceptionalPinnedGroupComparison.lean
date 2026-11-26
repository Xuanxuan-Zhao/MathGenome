import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedGroupComparison
import LinearAlgebraicGroups.Affine.GroupSchemes
import LinearAlgebraicGroups.Affine.RationalRepresentations
import LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedGroupComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (BasedRootDatum)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.ExceptionalMarkedRootDescent
open Specs.ExceptionalValuedTorusNormalizer
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap)
open Specs.AdjointRepresentation (GroupPoints)

universe u

attribute [local instance] integerAlgebra

private abbrev ExtendsDiagram (F L k K : Type u) [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K]
    (σ : Gal(L/F)) (β : Gal(K/k)) (e : (L ⊗[F] k) ≃ₐ[F] K) : Prop :=
  (∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) ∧
  ∀ z : L, β (e (z ⊗ₜ[F] (1 : k))) = e ((σ z) ⊗ₜ[F] (1 : k))

section TensorTestAlgebras

open Algebra.TensorProduct

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]

variable {σ : Gal(L/F)} {β : Gal(K/k)} {e : (L ⊗[F] k) ≃ₐ[F] K}

/-- The compositum embedding of the original diagram field. -/
private def diagramEmbedding (e : (L ⊗[F] k) ≃ₐ[F] K) : L →ₐ[F] K :=
  e.toAlgHom.comp Algebra.TensorProduct.includeLeft

omit [IsScalarTower F k K] in
private theorem diagramEmbedding_equivariant (h : ExtendsDiagram F L k K σ β e) (x : L) :
    β (diagramEmbedding e x) = diagramEmbedding e (σ x) :=
  h.2 x

/-- The two scalar extensions of a coefficient test algebra agree by
associativity and the given compositum presentation. -/
private noncomputable def coefficientTensorEquiv (e : (L ⊗[F] k) ≃ₐ[F] K)
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) (R : TestAlgebra k) :
    L ⊗[F] (restrictTestAlgebra F k).obj R ≃ₐ[F] K ⊗[k] R := by
  let A := (restrictTestAlgebra F k).obj R
  letI : Algebra F R := A.algebra
  letI : IsScalarTower F k R := IsScalarTower.of_algebraMap_eq' rfl
  let b : (k ⊗[F] L) ≃ₐ[k] K :=
    { (Algebra.TensorProduct.comm F k L).trans e with
      commutes' := h }
  exact (Algebra.TensorProduct.comm F L ((restrictTestAlgebra F k).obj R)).trans
    (((cancelBaseChange F k k R L).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) b).trans
        (Algebra.TensorProduct.comm k R K))).restrictScalars F)

private theorem coefficientTensorEquiv_tmul (e : (L ⊗[F] k) ≃ₐ[F] K)
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) (R : TestAlgebra k)
    (z : L) (r : R) :
    coefficientTensorEquiv e h R (z ⊗ₜ[F] r) = diagramEmbedding e z ⊗ₜ[k] r := by
  simp only [coefficientTensorEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    comm_tmul, cancelBaseChange_symm_tmul, congr_apply, map_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reassociation acts naturally on the scalar-extended integral test rings. -/
private noncomputable def coefficientTestAlgebraIso (e : (L ⊗[F] k) ≃ₐ[F] K)
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) :
    restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L ≅ quadraticIntegralAlgebra k K :=
  NatIso.ofComponents (fun R => CommAlgCat.isoMk
    ({ (coefficientTensorEquiv e h R).toRingEquiv with
      commutes' := fun x => map_intCast (coefficientTensorEquiv e h R) x.down } :
      (restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L).obj R ≃ₐ[Integers.{u}]
        (quadraticIntegralAlgebra k K).obj R)) (by
      intro R S f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul z r =>
        change coefficientTensorEquiv e h S (z ⊗ₜ[F] f.hom r) =
          Algebra.TensorProduct.map (AlgHom.id k K) f.hom (coefficientTensorEquiv e h R (z ⊗ₜ[F] r))
        rw [coefficientTensorEquiv_tmul, coefficientTensorEquiv_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))

private theorem coefficientTestAlgebraIso_apply (e : (L ⊗[F] k) ≃ₐ[F] K)
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) (R : TestAlgebra k) (z) :
    ((coefficientTestAlgebraIso e h).hom.app R).hom z = coefficientTensorEquiv e h R z := rfl

private theorem coefficientTensorEquiv_diagram {σ : Gal(L/F)} {β : Gal(K/k)}
    {e : (L ⊗[F] k) ≃ₐ[F] K} (h : ExtendsDiagram F L k K σ β e)
    (R : TestAlgebra k) (z : L ⊗[F] (restrictTestAlgebra F k).obj R) :
    coefficientTensorEquiv e h.1 R (quadraticCoefficientEquiv σ ((restrictTestAlgebra F k).obj R) z) =
      quadraticCoefficientEquiv β R (coefficientTensorEquiv e h.1 R z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change coefficientTensorEquiv e h.1 R (σ x ⊗ₜ[F] y) = _
    rw [coefficientTensorEquiv_tmul, coefficientTensorEquiv_tmul]
    change diagramEmbedding e (σ x) ⊗ₜ[k] y = β (diagramEmbedding e x) ⊗ₜ[k] y
    rw [diagramEmbedding_equivariant h]
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorTestAlgebras

section MarkedFibreComparison

variable {F k : Type u} [Field F] [Field k] [Algebra F k]
  {D : BasedRootDatum.{u}} {M : Model D}

set_option backward.isDefEq.respectTransparency false in
/-- On each coefficient test algebra, the two split marked point functors
are identified through the integral marking. -/
private theorem markedFibreRestrictedPoints (C : MarkedFibre M F) (Ck : MarkedFibre M k) :
    ∃ e : (groupPointsFunctor k).obj Ck.realization.pinned.pair.G.val ≅
        restrictTestAlgebra F k ⋙ (groupPointsFunctor F).obj C.realization.pinned.pair.G.val,
      ∀ R p, markedFibrePoint C ((restrictTestAlgebra F k).obj R) (e.hom.app R p) =
        markedFibrePoint Ck R p := by
  obtain ⟨i, hi⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  obtain ⟨j, hj⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison Ck
  let b := restrictTestAlgebra F k
  let J := Specs.IntegralSemisimpleModel.integralPointFunctor M.group
  let h : b ⋙ (groupPointsFunctor F).obj C.realization.pinned.pair.G.val ≅
      integralTestAlgebra k ⋙ J := Functor.isoWhiskerLeft b i
  let e := j ≪≫ h.symm
  refine ⟨e, fun R p => ?_⟩
  rw [← hi, ← hj]
  exact ConcreteCategory.congr_hom (h.app R).inv_hom_id (j.hom.app R p)


set_option backward.isDefEq.respectTransparency false in
private theorem groupIsoOfPointIso {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val) :
    ∃ j : G.val ≅ H.val, (groupPointsFunctor k).map j.hom = e.hom := by
  have hGH := groupHomComparison k G.val H.val G.property.1
  have hHG := groupHomComparison k H.val G.val H.property.1
  obtain ⟨f, hf⟩ := hGH.surjective e.hom
  obtain ⟨g, hg⟩ := hHG.surjective e.inv
  change (groupPointsFunctor k).map f = e.hom at hf
  change (groupPointsFunctor k).map g = e.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (groupHomComparison k G.val G.val G.property.1).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G.val)
    calc
      _ = 𝟙 _ := by rw [Functor.map_comp, hf, hg, e.hom_inv_id]
      _ = _ := ((groupPointsFunctor k).map_id G.val).symm
  · apply (groupHomComparison k H.val H.val H.property.1).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H.val)
    calc
      _ = 𝟙 _ := by rw [Functor.map_comp, hf, hg, e.inv_hom_id]
      _ = _ := ((groupPointsFunctor k).map_id H.val).symm

end MarkedFibreComparison

section IntegralDiagramAction

open Specs.Pinning (transportCharacter)
open Specs.RootGroups (rootPoint)
open Specs.IntegralRootRelations (upper)
open Specs.ExceptionalIwahoriImageComparison (pointHom)
open LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedFibreTorusCoordinates markedPinnedDiagramAction)
open LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
  (pinnedSimpleRankOneEquivariance)
open private fibrePointEquiv markedFibrePoint_root
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private pinnedTorusValues markedRoots_of_simpleWallAgreement markedHom_ext
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

variable {F k : Type u} [Field F] [Field k] [Algebra F k]
  {D : BasedRootDatum.{u}} {M : Model D}

private noncomputable def integralPinnedLift (C : MarkedFibre M k) (f : Aut C.realization.pinned)
    (R : TestAlgebra k) :
    IntegralPoints M.group ((integralTestAlgebra k).obj R) →*
      IntegralPoints M.group ((integralTestAlgebra k).obj R) :=
  let u := fibrePointEquiv C R
  u.toMonoidHom.comp
    ((pointHom f.asIso.hom.group.hom (testSpec k |>.obj (Opposite.op R))).comp u.symm.toMonoidHom)

private theorem integralPinnedLift_apply (C : MarkedFibre M k) (f : Aut C.realization.pinned)
    (R : TestAlgebra k) (p : GroupPoints C.realization.pinned.pair.G.val R) :
    integralPinnedLift C f R (markedFibrePoint C R p) =
      markedFibrePoint C R (p ≫ f.asIso.hom.group.hom.hom.hom) := by
  let u := fibrePointEquiv C R
  change u (u.symm (u p) ≫ _) = _
  rw [u.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem integralPinnedLift_torus (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    (E : SplitSequence C.realization.pinned C.realization.attached l Q)
    (a : Aut C.realization.attached.toBased) (R : TestAlgebra k)
    (v : TorusValues D ((integralTestAlgebra k).obj R)) :
    let e := (markedDiagramEquiv C.realization a).asIso.hom
    integralPinnedLift C (l a) R (torusPoint D _ v ≫ M.torus.hom.hom) =
      torusPoint D _ (v.comp e.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) ≫
        M.torus.hom.hom := by
  intro e
  obtain ⟨x, hx, hi⟩ := markedFibreTorusCoordinates D M C.realization
    C.groupIso C.torusIso C.torus_comm C.torus_eval
  let t := x R v
  let T := C.realization.pinned.pair.T
  let s := (l a).asIso.hom
  have ht : markedFibrePoint C R (t ≫ T.inclusion.hom.hom) =
      torusPoint D _ v ≫ M.torus.hom.hom := by
    unfold markedFibrePoint
    rw [Category.assoc]
    exact hi R v
  rw [← ht, integralPinnedLift_apply]
  have hs : (t ≫ T.inclusion.hom.hom) ≫ s.group.hom.hom.hom =
      (t ≫ s.torus.hom.hom.hom) ≫ T.inclusion.hom.hom := by
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ u.hom.hom) s.torus_comm
  rw [hs]
  exact pinnedTorusValues C E a R t v (hx R v)

private theorem integralPinnedLift_rankOne (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    (E : SplitSequence C.realization.pinned C.realization.attached l Q)
    (a : Aut C.realization.attached.toBased) (R : TestAlgebra k)
    (i : D.base.support) (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    let S := (integralTestAlgebra k).obj R
    let e := (markedDiagramEquiv C.realization a).asIso.hom
    integralPinnedLift C (l a) R ((M.rankOne i).app S m) =
      (M.rankOne (simplePermutation D e i)).app S m := by
  intro S e
  let u := fibrePointEquiv C R
  let p := u.symm ((M.rankOne i).app S m)
  have hp : markedFibrePoint C R p = (M.rankOne i).app S m := u.apply_symm_apply _
  have hi := (markedPinnedDiagramAction C.realization E a).1 i
  rw [← hp, integralPinnedLift_apply]
  exact pinnedSimpleRankOneEquivariance C (l a) i (simplePermutation D e i) hi R m p hp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- The integral marking identifies the two lifts of the same based action
on every coefficient test algebra. -/
private theorem integralPinnedLift_baseChange (C : MarkedFibre M F) (Ck : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Qk : AdjointQuotient Ck.realization.pinned.pair.G}
    (E : SplitSequence C.realization.pinned C.realization.attached l Q)
    (Ek : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk)
    (a : Aut C.realization.attached.toBased) (ak : Aut Ck.realization.attached.toBased)
    (ha : (markedDiagramEquiv C.realization a).asIso.hom =
      (markedDiagramEquiv Ck.realization ak).asIso.hom)
    (R : TestAlgebra k) :
    integralPinnedLift C (l a) ((restrictTestAlgebra F k).obj R) =
      integralPinnedLift Ck (lk ak) R := by
  obtain ⟨e, he⟩ := markedFibreRestrictedPoints C Ck
  let P := C.realization.pinned.pair.G
  let H := Ck.realization.pinned.pair.G
  let b := restrictTestAlgebra F k
  let s := (l a).asIso.hom.group.hom
  let sk := (lk ak).asIso.hom.group.hom
  let τ := e.hom ≫ Functor.whiskerLeft b ((groupPointsFunctor F).map s) ≫ e.inv
  obtain ⟨f, hf⟩ := (groupHomComparison k H.val H.val H.property.1).surjective τ
  change (groupPointsFunctor k).map f = τ at hf
  have hpoint (R : TestAlgebra k) (p : GroupPoints H.val R) :
      markedFibrePoint Ck R (p ≫ f.hom.hom) =
        integralPinnedLift C (l a) (b.obj R) (markedFibrePoint Ck R p) := by
    let q : GroupPoints P.val (b.obj R) := e.hom.app R p
    let q' : GroupPoints P.val (b.obj R) := q ≫ s.hom.hom
    have h := ConcreteCategory.congr_hom (congrArg (fun m => m.app R) hf) p
    change p ≫ f.hom.hom = e.inv.app R q' at h
    calc
      _ = markedFibrePoint C (b.obj R) (e.hom.app R (e.inv.app R q')) :=
        (congrArg (markedFibrePoint Ck R) h).trans (he R _).symm
      _ = markedFibrePoint C (b.obj R) (q ≫ s.hom.hom) :=
        congrArg (markedFibrePoint C (b.obj R))
          (ConcreteCategory.congr_hom (e.app R).inv_hom_id q')
      _ = _ := (integralPinnedLift_apply C (l a) (b.obj R) q).symm.trans
        (congrArg (integralPinnedLift C (l a) (b.obj R)) (he R p))
  have hsk (R : TestAlgebra k) (p : GroupPoints H.val R) :
      markedFibrePoint Ck R (p ≫ sk.hom.hom) =
        integralPinnedLift Ck (lk ak) R (markedFibrePoint Ck R p) :=
    (integralPinnedLift_apply Ck (lk ak) R p).symm
  have hF : f = sk := by
    apply markedHom_ext Ck
    · intro S t
      let u := fibrePointEquiv Ck S
      apply u.injective
      change markedFibrePoint Ck S (_ ≫ f.hom.hom) = markedFibrePoint Ck S (_ ≫ sk.hom.hom)
      rw [hpoint, hsk]
      obtain ⟨x, _, hx⟩ := markedFibreTorusCoordinates D M Ck.realization
        Ck.groupIso Ck.torusIso Ck.torus_comm Ck.torus_eval
      obtain ⟨v, rfl⟩ := (x S).surjective t
      have ht : markedFibrePoint Ck S (x S v ≫ Ck.realization.pinned.pair.T.inclusion.hom.hom) =
          torusPoint D _ v ≫ M.torus.hom.hom := by
        unfold markedFibrePoint
        rw [Category.assoc]
        exact hx S v
      rw [ht, integralPinnedLift_torus C E, integralPinnedLift_torus Ck Ek, ha]
    · intro S i z
      let u := fibrePointEquiv Ck S
      let S₀ := (integralTestAlgebra k).obj S
      let p := integralPinnedLift C (l a) (b.obj S)
      let q := integralPinnedLift Ck (lk ak) S
      have hr (j : D.base.support) (t : S₀) :
          p (markedRootPoint M.toIntegralMarking S₀ j t) =
            q (markedRootPoint M.toIntegralMarking S₀ j t) := by
        have ht : (M.rankOne j).app S₀ (upper t) = markedRootPoint M.toIntegralMarking S₀ j t :=
          M.rankOneUpper j S₀ t
        rw [← ht]
        change integralPinnedLift C (l a) (b.obj S) _ = integralPinnedLift Ck (lk ak) S _
        rw [integralPinnedLift_rankOne C E, integralPinnedLift_rankOne Ck Ek, ha]
      have hn (j : D.base.support) :
          p (markedWall M.toIntegralMarking S₀ j 1) = q (markedWall M.toIntegralMarking S₀ j 1) := by
        change integralPinnedLift C (l a) (b.obj S) ((M.rankOne j).app S₀ (wallMatrix 1)) =
          integralPinnedLift Ck (lk ak) S ((M.rankOne j).app S₀ (wallMatrix 1))
        rw [integralPinnedLift_rankOne C E, integralPinnedLift_rankOne Ck Ek, ha]
      apply u.injective
      change markedFibrePoint Ck S (_ ≫ f.hom.hom) = markedFibrePoint Ck S (_ ≫ sk.hom.hom)
      rw [hpoint, hsk, markedFibrePoint_root]
      exact markedRoots_of_simpleWallAgreement M S₀ p q hr hn i z
  apply MonoidHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (fibrePointEquiv Ck R).surjective x
  change integralPinnedLift C (l a) (b.obj R) (markedFibrePoint Ck R p) =
    integralPinnedLift Ck (lk ak) R (markedFibrePoint Ck R p)
  rw [← hpoint, ← hsk, hF]

end IntegralDiagramAction

section FixedPoints

open Specs.AdjointBorelCohomology (PinnedTwist)
open private markedCellAction markedCellAction_apply markedCellAction_fixed_iff fibrePointEquiv
  coordinatePointsIso liftPointMorphism from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem changeRingHom_comp_apply {A B C : IntegralAlgebra.{u}} (G : IntegralGroup.{u})
    (f : A ⟶ B) (g : B ⟶ C) (p : IntegralPoints G A) :
    changeRingHom G g (changeRingHom G f p) = changeRingHom G (f ≫ g) p :=
  (ConcreteCategory.congr_hom ((integralPointFunctor G).map_comp f g) p).symm

private theorem changeRingHom_injective {A B : IntegralAlgebra.{u}} (G : IntegralGroup.{u})
    (i : A ≅ B) : Function.Injective (changeRingHom G i.hom) :=
  ((integralPointFunctor G).mapIso i).groupIsoToMulEquiv.injective

set_option backward.isDefEq.respectTransparency false in
private theorem integralPinnedLift_natural {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k) (f : Aut C.realization.pinned) {R S : TestAlgebra k} (g : R ⟶ S)
    (x : IntegralPoints M.group ((integralTestAlgebra k).obj R)) :
    changeRingHom M.group ((integralTestAlgebra k).map g) (integralPinnedLift C f R x) =
      integralPinnedLift C f S (changeRingHom M.group ((integralTestAlgebra k).map g) x) := by
  have hn (p : GroupPoints C.realization.pinned.pair.G.val R) :
      markedFibrePoint C S (mapPoints g p) = changeRingHom M.group
        ((integralTestAlgebra k).map g) (markedFibrePoint C R p) := by
    obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
    rw [← he, ← he]
    exact ConcreteCategory.congr_hom (e.hom.naturality g) p
  obtain ⟨p, hp⟩ := (fibrePointEquiv C R).surjective x
  change markedFibrePoint C R p = x at hp
  rw [← hp, integralPinnedLift_apply, ← hn, ← hn, integralPinnedLift_apply]
  exact congrArg (markedFibrePoint C S) (Category.assoc _ _ _).symm

private def coefficientInvolution {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) (R : TestAlgebra k) :
    (quadraticIntegralAlgebra k K).obj R ⟶ (quadraticIntegralAlgebra k K).obj R :=
  integralRingMap (quadraticCoefficientEquiv σ R).toRingHom

set_option backward.isDefEq.respectTransparency false in
private theorem markedCellAction_eq_lift {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T) (σ : Gal(K/k)) (R : TestAlgebra k)
    (x : IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R)) :
    markedCellAction C d σ R x =
      integralPinnedLift C (pinnedDiagram d σ) ((extendedTestAlgebra k K).obj R)
        (changeRingHom M.group (coefficientInvolution σ R) x) := by
  let S := (extendedTestAlgebra k K).obj R
  let g := conjugateTestAlgebra σ R
  have hg : (integralTestAlgebra k).map g = coefficientInvolution σ R := rfl
  obtain ⟨p, hp⟩ := (fibrePointEquiv C S).surjective x
  change markedFibrePoint C S p = x at hp
  have hn : markedFibrePoint C S (mapPoints g p) =
      changeRingHom M.group (coefficientInvolution σ R) (markedFibrePoint C S p) := by
    obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
    rw [← hg, ← he, ← he]
    exact ConcreteCategory.congr_hom (e.hom.naturality g) p
  rw [← hp, markedCellAction_apply, ← hn, integralPinnedLift_apply]
  rfl

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  {σ : Gal(L/F)} {β : Gal(K/k)} {e : (L ⊗[F] k) ≃ₐ[F] K}

private noncomputable def coefficientExtendedMap
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) (R : TestAlgebra k) :
    (extendedTestAlgebra F L).obj ((restrictTestAlgebra F k).obj R) ⟶
      (restrictTestAlgebra F k).obj ((extendedTestAlgebra k K).obj R) := by
  refine (CommAlgCat.homEquivCommRingCat (R := F) _ _).symm ⟨CommRingCat.ofHom (coefficientTensorEquiv e h R).toRingHom, ?_⟩
  apply RingHom.ext
  intro x
  change coefficientTensorEquiv e h R (algebraMap F (L ⊗[F] (restrictTestAlgebra F k).obj R) x) =
    (algebraMap k K (algebraMap F k x)) ⊗ₜ[k] (1 : R)
  rw [← IsScalarTower.algebraMap_apply F k K x]
  exact (coefficientTensorEquiv e h R).commutes x

private theorem coefficientExtendedMap_integral
    (h : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) (R : TestAlgebra k) :
    (integralTestAlgebra F).map (coefficientExtendedMap h R) = (coefficientTestAlgebraIso e h).hom.app R := rfl

private theorem coefficientInvolution_comp (h : ExtendsDiagram F L k K σ β e) (R : TestAlgebra k) :
    coefficientInvolution σ ((restrictTestAlgebra F k).obj R) ≫ (coefficientTestAlgebraIso e h.1).hom.app R =
      (coefficientTestAlgebraIso e h.1).hom.app R ≫ coefficientInvolution β R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  exact coefficientTensorEquiv_diagram h R

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem coefficientInvolution_onPoints
    {D : BasedRootDatum.{u}} {M : Model D} (h : ExtendsDiagram F L k K σ β e)
    (R : TestAlgebra k) (x : IntegralPoints M.group
      ((quadraticIntegralAlgebra F L).obj ((restrictTestAlgebra F k).obj R))) :
    let m := changeRingHom M.group ((coefficientTestAlgebraIso e h.1).hom.app R)
    m (changeRingHom M.group (coefficientInvolution σ ((restrictTestAlgebra F k).obj R)) x) =
      changeRingHom M.group (coefficientInvolution β R) (m x) := by
  intro m
  let R₀ := (restrictTestAlgebra F k).obj R
  let c := (coefficientTestAlgebraIso e h.1).hom.app R
  let t := coefficientInvolution σ R₀
  let tk := coefficientInvolution β R
  calc
    m (changeRingHom M.group t x) = changeRingHom M.group (t ≫ c) x :=
      changeRingHom_comp_apply M.group t c x
    _ = changeRingHom M.group (c ≫ tk) x :=
      congrArg (fun f => changeRingHom M.group f x) (coefficientInvolution_comp h R)
    _ = changeRingHom M.group tk (m x) :=
      (changeRingHom_comp_apply M.group c tk x).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem markedCellAction_baseChange
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M F) (Ck : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Qk : AdjointQuotient Ck.realization.pinned.pair.G}
    (E : SplitSequence C.realization.pinned C.realization.attached l Q)
    (Ek : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk)
    {G : AffineAlgebraicGroup F} {B T : ClosedSubgroup G.val}
    {Gk : AffineAlgebraicGroup k} {Bk Tk : ClosedSubgroup Gk.val}
    (d : PinnedTwist L C.realization.attached l B T) (dk : PinnedTwist K Ck.realization.attached lk Bk Tk)
    (ha : (markedDiagramEquiv C.realization (d.outer σ)).asIso.hom =
      (markedDiagramEquiv Ck.realization (dk.outer β)).asIso.hom)
    (h : ExtendsDiagram F L k K σ β e)
    (R : TestAlgebra k) (x : IntegralPoints M.group
      ((quadraticIntegralAlgebra F L).obj ((restrictTestAlgebra F k).obj R))) :
    let c := changeRingHom M.group ((coefficientTestAlgebraIso e h.1).hom.app R)
    c (markedCellAction C d σ ((restrictTestAlgebra F k).obj R) x) =
      markedCellAction Ck dk β R (c x) := by
  intro c
  let b := restrictTestAlgebra F k
  let S := (extendedTestAlgebra k K).obj R
  let R₀ := b.obj R
  let S₀ := (extendedTestAlgebra F L).obj R₀
  let f := coefficientExtendedMap (e := e) h.1 R
  let y := changeRingHom M.group (coefficientInvolution σ R₀) x
  let yk := changeRingHom M.group (coefficientInvolution β R) (c x)
  let a := d.outer σ
  let ak := dk.outer β
  have hfirst : markedCellAction C d σ R₀ x = integralPinnedLift C (l a) S₀ y :=
    markedCellAction_eq_lift C d σ R₀ x
  have hsecond : markedCellAction Ck dk β R (c x) = integralPinnedLift Ck (lk ak) S yk :=
    markedCellAction_eq_lift Ck dk β R (c x)
  have hcoeff : c y = yk := coefficientInvolution_onPoints (M := M) h R x
  have hmap : (integralTestAlgebra F).map f = (coefficientTestAlgebraIso e h.1).hom.app R :=
    coefficientExtendedMap_integral (e := e) h.1 R
  have hn := integralPinnedLift_natural C (l a) f y
  rw [hmap] at hn
  have hlift := integralPinnedLift_baseChange C Ck E Ek a ak ha S
  calc
    _ = c (integralPinnedLift C (l a) S₀ y) := congrArg (fun z => c z) hfirst
    _ = integralPinnedLift C (l a) (b.obj S) (c y) := hn
    _ = integralPinnedLift C (l a) (b.obj S) yk :=
      congrArg (fun z => integralPinnedLift C (l a) (b.obj S) z) hcoeff
    _ = integralPinnedLift Ck (lk ak) S yk := DFunLike.congr_fun hlift yk
    _ = _ := hsecond.symm

set_option backward.isDefEq.respectTransparency false in
private theorem natIso_of_embeddings {C : Type*} [Category C] {P Q J : C ⥤ GrpCat.{u}}
    (a : P ⟶ J) (b : Q ⟶ J) (ha : ∀ R, Function.Injective (a.app R))
    (hb : ∀ R, Function.Injective (b.app R))
    (h : ∀ R, Set.range (a.app R) = Set.range (b.app R)) :
    ∃ q : P ≅ Q, q.hom ≫ b = a := by
  obtain ⟨f, hf⟩ := liftPointMorphism b a hb (fun R p => h R ▸ Set.mem_range_self p)
  obtain ⟨g, hg⟩ := liftPointMorphism a b ha (fun R p => (h R).symm ▸ Set.mem_range_self p)
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro p
    apply ha R
    have hfg : (f ≫ g) ≫ a = 𝟙 _ ≫ a := by rw [Category.assoc, hg, hf, Category.id_comp]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hfg R) p
  · apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro p
    apply hb R
    have hgf : (g ≫ f) ≫ b = 𝟙 _ ≫ b := by rw [Category.assoc, hf, hg, Category.id_comp]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hgf R) p

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem pinnedGroupComparisonAux [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M F) (Ck : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Qk : AdjointQuotient Ck.realization.pinned.pair.G}
    (E : SplitSequence C.realization.pinned C.realization.attached l Q)
    (Ek : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk)
    {G : AffineAlgebraicGroup F} {B T : ClosedSubgroup G.val}
    {Gk : AffineAlgebraicGroup k} {Bk Tk : ClosedSubgroup Gk.val}
    (d : PinnedTwist L C.realization.attached l B T) (dk : PinnedTwist K Ck.realization.attached lk Bk Tk)
    (ha : (markedDiagramEquiv C.realization (d.outer σ)).asIso.hom =
      (markedDiagramEquiv Ck.realization (dk.outer β)).asIso.hom)
    (hL : Module.finrank F L = 2) (hK : Module.finrank k K = 2) (hσ : σ ≠ 1) (hβ : β ≠ 1)
    (h : ExtendsDiagram F L k K σ β e) :
    ∃ (c : restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L ≅ quadraticIntegralAlgebra k K)
      (j : Gk.val ≅ (groupBaseChange F k).obj G.val),
      (∀ (R : TestAlgebra k) (z : L) (r : R),
        (c.hom.app R).hom (z ⊗ₜ[F] r) = e (z ⊗ₜ[F] (1 : k)) ⊗ₜ[k] r) ∧
      ∀ (R : TestAlgebra k) (p : GroupPoints Gk.val R),
        let R₀ := (restrictTestAlgebra F k).obj R
        pinnedMarkedPoint Ck dk R ((coordinatePointEquiv Gk R).symm p) =
          changeRingHom M.group (c.hom.app R)
            (pinnedMarkedPoint C d R₀ ((coordinatePointEquiv G R₀).symm
              (baseChangePoint F k G.val.X R (p ≫ j.hom.hom.hom)))) := by
  obtain ⟨i, hi, hInj⟩ := ExceptionalMarkedRootDescent.pinnedMarkedPointEmbedding C d
  obtain ⟨ik, hik, hInjk⟩ := ExceptionalMarkedRootDescent.pinnedMarkedPointEmbedding Ck dk
  let b := restrictTestAlgebra F k
  let J := integralPointFunctor M.group
  let E₀ := coefficientTestAlgebraIso e h.1
  let c := Functor.isoWhiskerRight E₀ J
  let a : b ⋙ (groupPointsFunctor F).obj G.val ⟶ quadraticIntegralAlgebra k K ⋙ J :=
    Functor.whiskerLeft b ((coordinatePointsIso G).inv ≫ i) ≫ c.hom
  let ak : (groupPointsFunctor k).obj Gk.val ⟶ quadraticIntegralAlgebra k K ⋙ J :=
    (coordinatePointsIso Gk).inv ≫ ik
  have h₀ (R : TestAlgebra k) (p : GroupPoints G.val (b.obj R)) :
      a.app R p = changeRingHom M.group (E₀.hom.app R)
        (pinnedMarkedPoint C d (b.obj R) ((coordinatePointEquiv G (b.obj R)).symm p)) :=
    congrArg (changeRingHom M.group (E₀.hom.app R)) (hi _ _)
  have h₁ (R : TestAlgebra k) (p : GroupPoints Gk.val R) :
      ak.app R p = pinnedMarkedPoint Ck dk R ((coordinatePointEquiv Gk R).symm p) := hik _ _
  have hai (R : TestAlgebra k) : Function.Injective (a.app R) :=
    (changeRingHom_injective M.group (E₀.app R)).comp
      ((hInj (b.obj R)).1.comp (coordinatePointEquiv G (b.obj R)).symm.injective)
  have haki (R : TestAlgebra k) : Function.Injective (ak.app R) :=
    (hInjk R).1.comp (coordinatePointEquiv Gk R).symm.injective
  have hrange (R : TestAlgebra k) : Set.range (ak.app R) = Set.range (a.app R) := by
    ext x
    obtain ⟨y, rfl⟩ := ((J.mapIso (E₀.app R)).groupIsoToMulEquiv).surjective x
    let m := changeRingHom M.group (E₀.hom.app R)
    change m y ∈ Set.range (ak.app R) ↔ m y ∈ Set.range (a.app R)
    have hkr : m y ∈ Set.range (ak.app R) ↔ m y ∈ Set.range (pinnedMarkedPoint Ck dk R) := by
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨(coordinatePointEquiv Gk R).symm p, (h₁ R p).symm.trans hp⟩
      · rintro ⟨p, hp⟩
        refine ⟨coordinatePointEquiv Gk R p, (h₁ R _).trans ?_⟩
        simpa only [MulEquiv.symm_apply_apply] using hp
    have hfr : m y ∈ Set.range (a.app R) ↔ y ∈ Set.range (pinnedMarkedPoint C d (b.obj R)) := by
      constructor
      · rintro ⟨p, hp⟩
        rw [h₀] at hp
        exact ⟨_, changeRingHom_injective M.group (E₀.app R) hp⟩
      · rintro ⟨p, hp⟩
        refine ⟨coordinatePointEquiv G (b.obj R) p, ?_⟩
        rw [h₀, MulEquiv.symm_apply_apply, hp]
    refine hkr.trans ((markedCellAction_fixed_iff Ck dk hK β hβ R (m y)).trans ?_)
    refine Iff.trans ?_ ((markedCellAction_fixed_iff C d hL σ hσ (b.obj R) y).symm.trans hfr.symm)
    have haction : m (markedCellAction C d σ (b.obj R) y) = markedCellAction Ck dk β R (m y) :=
      markedCellAction_baseChange C Ck E Ek d dk ha h R y
    exact haction ▸ (changeRingHom_injective M.group (E₀.app R)).eq_iff
  obtain ⟨v, hv⟩ := natIso_of_embeddings ak a haki hai hrange
  let q := groupBaseChangePointIso k G.val
  obtain ⟨j, hj⟩ := groupIsoOfPointIso Gk (Specs.Unipotent.baseChangedAlgebraicGroup k G) (v ≪≫ q.symm)
  refine ⟨E₀, j, ?_, fun R p => ?_⟩
  · intro R z r
    exact (coefficientTestAlgebraIso_apply e h.1 R _).trans (coefficientTensorEquiv_tmul e h.1 R z r)
  · have hpart := ConcreteCategory.congr_hom (NatTrans.congr_app hj R) p
    change p ≫ j.hom.hom.hom = q.inv.app R (v.hom.app R p) at hpart
    have hq (x : GroupPoints ((groupBaseChange F k).obj G.val) R) :
        baseChangePoint F k G.val.X R x = q.hom.app R x := rfl
    dsimp only
    rw [hq, hpart]
    have hcancel : q.hom.app R (q.inv.app R (v.hom.app R p)) = v.hom.app R p :=
      ConcreteCategory.congr_hom (q.app R).inv_hom_id (v.hom.app R p)
    have hvp : a.app R (v.hom.app R p) = ak.app R p :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hv R) p
    calc
      _ = ak.app R p := (h₁ R p).symm
      _ = a.app R (v.hom.app R p) := hvp.symm
      _ = _ := (h₀ R _).trans (congrArg
        (fun x => changeRingHom M.group (E₀.hom.app R)
          (pinnedMarkedPoint C d (b.obj R) ((coordinatePointEquiv G (b.obj R)).symm x)))
        hcancel.symm)

end FixedPoints

/-- The coefficient-field comparison intertwines the marked point
embeddings and is induced by an isomorphism of the descended groups. -/
theorem pinnedGroupComparison : Specs.ExceptionalPinnedGroupComparison.Statement.{u} := by
  intro F L k K _ _ _ _ _ _ _ _ _ _ _ _ _ D M C Ck l lk Q Qk E Ek G B T Gk Bk Tk d dk
    σ β e ha hL hK hσ hβ hcoeff hdiagram
  exact pinnedGroupComparisonAux C Ck E Ek d dk ha hL hK hσ hβ
    (e := e) ⟨hcoeff, hdiagram⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedGroupComparison
