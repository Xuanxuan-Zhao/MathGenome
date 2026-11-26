import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OrthogonalLeviFactorDisplacement
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MatrixGroups
open LinearAlgebraicGroups.Specs

universe u

namespace LinearAlgebraicGroups.Arithmetic.OrthogonalLeviFactorDisplacement

open Specs.Arithmetic.OrthogonalLeviFactorDisplacement
open Specs.StandardGroups (specialLinearPoints)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private groupBaseChange_map_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy

noncomputable section

set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private abbrev onPoints {G H : GroupScheme F} (f : G ⟶ H) (R : TestAlgebra F) :
    Points G.X R →* Points H.X R := ((groupPointsFunctor F).map f).app R |>.hom

private theorem onPoints_comp {G H J : GroupScheme F} (f : G ⟶ H) (g : H ⟶ J)
    (R : TestAlgebra F) (x : Points G.X R) :
    onPoints (f ≫ g) R x = onPoints g R (onPoints f R x) := rfl

private theorem onPoints_zero {G H : GroupScheme F} (R : TestAlgebra F) (x : Points G.X R) :
    onPoints (0 : G ⟶ H) R x = 1 := by
  change x ≫ (0 : G ⟶ H).hom.hom = 1
  rw [show (0 : G ⟶ H).hom.hom = (1 : G.X ⟶ H.X) by rfl, MonObj.comp_one]

private theorem point_ext {G H : GroupScheme F} (hG : IsAffine G.X.left)
    {f g : G ⟶ H} (h : ∀ (R : TestAlgebra F) x, onPoints f R x = onPoints g R x) : f = g := by
  apply Grp.hom_ext
  exact hom_ext_of_points hG h

private theorem point_baseChange {G H : GroupScheme F} (f : G ⟶ H)
    (R : TestAlgebra K) (x : Points ((groupBaseChange F K).obj G).X R) :
    baseChangePointGroupEquiv K H R (onPoints ((groupBaseChange F K).map f) R x) =
      onPoints f ((restrictTestAlgebra F K).obj R) (baseChangePointGroupEquiv K G R x) :=
  baseChangePointsSchemeNaturality F K f.hom.hom R x

section Product

variable {I : Type u} [Finite I] [DecidableEq I] {G S : GroupScheme F}
variable (π : I → (G ⟶ S)) (hπ : IsLimit (Fan.mk G π))

private def productSection (i : I) : S ⟶ G :=
  hπ.lift (Fan.mk S (fun j => if j = i then 𝟙 S else 0))

private theorem productSection_comp (i j : I) :
    productSection π hπ i ≫ π j = if j = i then 𝟙 S else 0 :=
  hπ.fac (Fan.mk S (fun j => if j = i then 𝟙 S else 0)) ⟨j⟩

private def pointProductHom (R : TestAlgebra F) :
    Points G.X R →* (I → Points S.X R) :=
  MonoidHom.pi fun i => onPoints (π i) R

include hπ in
private theorem pointProduct_bijective (R : TestAlgebra F) :
    Function.Bijective (pointProductHom π R) := by
  let U := (testSpec F).obj (op R)
  let C := Grp.forget (SchemeOver F)
  let h : IsLimit (Fan.mk G.X (fun i => (π i).hom.hom)) :=
    isLimitFanMkObjOfIsLimit C (fun _ => S) π hπ
  let coord (x : I → Points S.X R) : Fan (fun _ : I => S.X) := Fan.mk U x
  constructor
  · intro x y hxy
    apply h.hom_ext
    rintro ⟨j⟩
    exact congrFun hxy j
  · intro x
    exact ⟨h.lift (coord x), funext fun i => h.fac (coord x) ⟨i⟩⟩

private def pointProduct (R : TestAlgebra F) :
    Points G.X R ≃* (I → Points S.X R) :=
  MulEquiv.ofBijective (pointProductHom π R) (pointProduct_bijective π hπ R)

variable (K)

private def extendedProduct (R : TestAlgebra K) :
    Points ((groupBaseChange F K).obj G).X R ≃*
      (I → Points ((groupBaseChange F K).obj S).X R) :=
  (baseChangePointGroupEquiv K G R).trans <|
    (pointProduct π hπ ((restrictTestAlgebra F K).obj R)).trans <|
      MulEquiv.piCongrRight fun _ => (baseChangePointGroupEquiv K S R).symm

private theorem extendedProduct_apply (R : TestAlgebra K) (x) (i : I) :
    extendedProduct K π hπ R x i = onPoints ((groupBaseChange F K).map (π i)) R x := by
  apply (baseChangePointGroupEquiv K S R).injective
  simp only [extendedProduct, MulEquiv.trans_apply, MulEquiv.piCongrRight_apply,
    MulEquiv.apply_symm_apply]
  exact (point_baseChange (π i) R x).symm

private theorem extendedProduct_section (R : TestAlgebra K) (i : I)
    (x : Points ((groupBaseChange F K).obj S).X R) :
    extendedProduct K π hπ R
      (onPoints ((groupBaseChange F K).map (productSection π hπ i)) R x) =
      Pi.mulSingle i x := by
  funext j
  apply (baseChangePointGroupEquiv K S R).injective
  rw [extendedProduct_apply, point_baseChange, point_baseChange, ← onPoints_comp,
    productSection_comp]
  by_cases h : j = i
  · subst j
    simp only [ite_eq_left, Pi.mulSingle_eq_same]
    rfl
  · rw [ite_eq_right h, onPoints_zero, Pi.mulSingle_eq_of_ne h, map_one]


/-- An automorphism with vanishing off-diagonal components has invertible
diagonal components after reindexing the target projections. -/
private theorem projection_isomorphisms
    (hG : IsAffine ((groupBaseChange F K).obj G).X.left)
    (hS : IsAffine ((groupBaseChange F K).obj S).X.left)
    (δ : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj G)
    (τ : I ≃ I)
    (h : ∀ i j, j ≠ τ i →
      (groupBaseChange F K).map (productSection π hπ i) ≫ δ.hom ≫
        (groupBaseChange F K).map (π j) = 0) (i : I) :
    ∃ e : (groupBaseChange F K).obj S ≅ (groupBaseChange F K).obj S,
      δ.hom ≫ (groupBaseChange F K).map (π (τ i)) =
        (groupBaseChange F K).map (π i) ≫ e.hom := by
  let B := groupBaseChange F K
  let p := fun i => B.map (π i)
  let s := fun i => B.map (productSection π hπ i)
  have hproj (i : I) : s i ≫ p i = 𝟙 _ := by
    rw [← B.map_comp, productSection_comp, ite_eq_left rfl, B.map_id]
  let f := s i ≫ δ.hom ≫ p (τ i)
  have hfac : δ.hom ≫ p (τ i) = p i ≫ f := by
    apply point_ext hG
    intro R x
    let e := extendedProduct K π hπ R
    let a := (onPoints (δ.hom ≫ p (τ i)) R).comp e.symm.toMonoidHom
    let b := (onPoints (p i ≫ f) R).comp e.symm.toMonoidHom
    have he : a = b := by
      apply MonoidHom.pi_ext
      intro j y
      have hj : e.symm (Pi.mulSingle j y) = onPoints (s j) R y :=
        e.symm_apply_eq.mpr (extendedProduct_section K π hπ R j y).symm
      change onPoints (δ.hom ≫ p (τ i)) R (e.symm (Pi.mulSingle j y)) =
        onPoints (p i ≫ f) R (e.symm (Pi.mulSingle j y))
      rw [hj, ← onPoints_comp, ← onPoints_comp]
      by_cases hji : j = i
      · subst j
        rw [← Category.assoc (s i) (p i), hproj, Category.id_comp]
      · rw [h j (τ i) (fun e => hji (τ.injective e.symm)), onPoints_zero, onPoints_comp]
        have hy := congrFun (extendedProduct_section K π hπ R j y) i
        rw [extendedProduct_apply, Pi.mulSingle_eq_of_ne (Ne.symm hji), ← onPoints_comp] at hy
        change onPoints (s j ≫ p i) R y = 1 at hy
        rw [show onPoints (p i ≫ f) R (onPoints (s j) R y) =
          onPoints f R (onPoints (s j ≫ p i) R y) from rfl, hy, map_one]
    have hx := DFunLike.congr_fun he (e x)
    change onPoints (δ.hom ≫ p (τ i)) R (e.symm (e x)) =
      onPoints (p i ≫ f) R (e.symm (e x)) at hx
    rwa [e.symm_apply_apply] at hx
  have htransport : s i ≫ δ.hom = f ≫ s (τ i) := by
    apply point_ext hS
    intro R x
    apply (extendedProduct K π hπ R).injective
    funext j
    change extendedProduct K π hπ R (onPoints δ.hom R (onPoints (s i) R x)) j =
      extendedProduct K π hπ R (onPoints (s (τ i)) R (onPoints f R x)) j
    rw [extendedProduct_section]
    calc
      _ = onPoints (s i ≫ δ.hom ≫ p j) R x := extendedProduct_apply K π hπ R _ j
      _ = _ := by
        by_cases hj : j = τ i
        · subst j
          rw [Pi.mulSingle_eq_same]
        · rw [h i j hj, onPoints_zero, Pi.mulSingle_eq_of_ne hj]

  let g := s (τ i) ≫ δ.inv ≫ p i
  refine ⟨⟨f, g, ?_, ?_⟩, hfac⟩
  · calc
      f ≫ g = (f ≫ s (τ i)) ≫ δ.inv ≫ p i := by simp [g]
      _ = 𝟙 _ := by rw [← htransport]; simp [hproj]
  · calc
      g ≫ f = s (τ i) ≫ δ.inv ≫ (p i ≫ f) := by simp [g]
      _ = 𝟙 _ := by rw [← hfac]; simp [hproj]


end Product

section Matrices

open Matrix Matrix.SpecialLinearGroup

private abbrev firstIndex : Index.{u} 2 := ⟨0⟩
private abbrev lastIndex : Index.{u} 2 := ⟨1⟩
private theorem first_ne_last : firstIndex ≠ lastIndex := by decide

private def sl2_reindex (L : Type u) [Field L] : SL(2, L) ≃*
    SpecialLinearGroup (Index.{u} 2) L where
  toFun x := ⟨reindex Equiv.ulift.symm Equiv.ulift.symm x.val,
    (det_reindex_self _ _).trans x.property⟩
  invFun x := ⟨reindex Equiv.ulift Equiv.ulift x.val,
    (det_reindex_self _ _).trans x.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_mul' x y := by
    apply Subtype.ext
    exact (reindexRingEquiv L Equiv.ulift.symm).map_mul x.val y.val

private theorem sl2_reindex_upper {L : Type u} [Field L] (a : L) :
    sl2_reindex L (transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      transvection first_ne_last a := by
  apply Subtype.ext
  ext ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [sl2_reindex, transvection_coe, reindex_apply, Matrix.single]

private theorem upper_generates_normally {L : Type u} [Field L] {M : Type u} [Group M]
    (f : SpecialLinearGroup (Index.{u} 2) L →* M)
    (h : ∀ a, f (transvection first_ne_last a) = 1) : ∀ x, f x = 1 := by
  let f' := f.comp (sl2_reindex L).toMonoidHom
  have hupper (a : L) : f' (transvection (show (0 : Fin 2) ≠ 1 by decide) a) = 1 := by
    change f (sl2_reindex L (transvection _ a)) = 1
    rw [sl2_reindex_upper]
    exact h a
  let w : SL(2, L) := ⟨!![0, 1; -1, 0], by rw [det_fin_two_of]; ring⟩
  have hw (a : L) :
      w * transvection (show (0 : Fin 2) ≠ 1 by decide) (-a) =
        transvection (show (1 : Fin 2) ≠ 0 by decide) a * w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w, Matrix.mul_apply, Fin.sum_univ_two, transvection_coe, Matrix.single]
  have hlower (a : L) : f' (transvection (show (1 : Fin 2) ≠ 0 by decide) a) = 1 := by
    have h' := congrArg f' (hw a)
    rw [map_mul, map_mul, hupper, mul_one] at h'
    exact mul_right_cancel (show f' (transvection _ a) * f' w =
      1 * f' w by simpa only [one_mul] using h'.symm)
  intro x
  obtain ⟨y, rfl⟩ := (sl2_reindex L).surjective x
  change f' y = 1
  apply Matrix.SL2.transvection_induction (fun z => f' z = 1) _ _ y
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hupper a
    · exact hlower a
    · exact (hij rfl).elim
  · intro a b ha hb
    rw [map_mul, ha, hb, mul_one]

end Matrices
section PinnedAction

open Specs.AutomorphismSequence
open Specs.Pinning
open Specs.RelativeFormComparison (fieldTest IsInduced)
open Specs.QuasiSplitInnerForms (outerHom pinnedSection)
open Specs.AbstractPairing (Root)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.SimpleRoots (evaluate IsBaseFor)
open Specs.StandardParabolicLevi (HasFace)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsDerivedSubgroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private face_parabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private pinnedScalarAligned from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem face_contains_borel {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (c : Cocharacter P.pair.T.group)
    (M : LimitDecomposition (c ≫ P.pair.T.inclusion)) (J : Set (Root P.pair.T))
    (hc : letI := D.comm; HasFace D.base J c) :
    IsSubgroupOf P.pair.B M.parabolic := by
  letI := D.comm
  let E := D.datum
  obtain ⟨d, _, hdreg, _, hdpos⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal).1
      P.pair.B P.pair.borel P.pair.containsTorus
  letI := E.finiteRoots
  letI := E.freeCharacters
  letI := E.finiteCharacters
  letI := E.reduced
  have heval (i : Root P.pair.T) :
      evaluate E d (E.rootDatum.root i) = Specs.CharacterPairing.pairing P.pair.T.group i.val d := by
    change E.rootDatum.toLinearMap (E.rootDatum.root i) (Additive.ofMul d) = _
    rw [E.root_eq, E.pairing_eq]
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.RootData.SimpleRoots.baseFor E.rootDatum
    (evaluate E d) (fun i => heval i ▸ hdreg i)
  have hp : Specs.SimpleRoots.positive E.rootDatum (evaluate E d) = subgroupRoots P.pair.T P.pair.B := by
    rw [hdpos]
    ext i
    change 0 < evaluate E d (E.rootDatum.root i) ↔ _
    rw [heval]
    rfl
  have hbase : b = D.base := by
    have hs : b.support = D.base.support := by
      ext i
      rw [D.simple_iff, hb.simple_iff, hp]
      unfold IsSimple
      simp only [E.root_eq]
      rfl
    have hb_ext (b₁ b₂ : E.rootDatum.Base) (h : b₁.support = b₂.support) : b₁ = b₂ := by
      cases b₁
      cases b₂
      cases h
      rfl
    exact hb_ext _ _ hs
  exact (face_parabolic P.pair.reductive P.pair.split P.pair.maximal P.pair.borel
    P.pair.containsTorus hdpos.symm (hbase ▸ hb) hc M).2

variable {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
variable {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}

private theorem pinned_lift_character (seq : SplitSequence P D l Q) (d : Aut D.toBased)
    (χ : Character P.pair.T.group) :
    (l d).asIso.hom.torus.inv ≫ χ =
      (Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))) := by
  let T := 𝟙_ (SchemeOver F)
  let f := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) T
  let a := pinnedScalarAligned (l d) T
  let outerVal : (constantGroup (k := F) (Aut D.toBased)).obj (op T) :=
    ⟨LocallyConstant.const _ d⟩
  have hout : seq.outer.app (op T) f = outerVal := by
    dsimp only [f]
    rw [← seq.sectionOnConstants T d]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app seq.rightInverse (op T)) outerVal
  let U := Over.mk (toUnit P.pair.T.group.X)
  have h := (seq.latticeAction T f a d hout).1 χ U (𝟙 _)
  apply Grp.hom_ext
  change (𝟙 _ ≫ (l d).asIso.hom.torus.inv.hom.hom) ≫ χ.hom.hom = _ at h
  rw [Category.id_comp] at h
  change (l d).asIso.hom.torus.inv.hom.hom ≫ χ.hom.hom =
    (Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))).hom.hom
  exact h

private theorem pinned_lift_root (seq : SplitSequence P D l Q) (d : Aut D.toBased)
    (i j : Root P.pair.T) (hi : IsSimple P.pair i)
    (hidx : d.asIso.hom.val.indexEquiv i = j) :
    ∃ e : (P.roots i).val.group ≅ (P.roots j).val.group,
      (P.roots i).val.inclusion ≫ (l d).asIso.hom.group.hom =
        e.hom ≫ (P.roots j).val.inclusion := by
  letI := D.comm
  let a : SimpleRoot P.pair := ⟨i, hi⟩
  let f := (l d).asIso.hom
  have hchar : transportCharacter f.torus i.val = j.val := by
    rw [transportCharacter, pinned_lift_character seq d]
    apply Additive.ofMul.injective
    change d.asIso.hom.val.weightEquiv (Additive.ofMul i.val) = Additive.ofMul j.val
    have h := RootPairing.Hom.root_weightMap_apply D.toBased.datum D.toBased.datum i
      d.asIso.hom.val.toHom
    have hroot (x : D.toBased.I) : D.toBased.datum.root x = Additive.ofMul x.val :=
      D.datum.root_eq x
    rw [hidx, hroot, hroot] at h
    exact h
  have hmem : (transportCharacter f.torus i.val,
      ((P.pin a).val.hom ≫ (P.roots i).val.inclusion) ≫ f.group.hom) ∈ pinGraph P := by
    rw [← f.pin_comm]
    exact ⟨_, ⟨a, rfl⟩, rfl⟩
  obtain ⟨a', ha'⟩ := hmem
  have heq : a'.val = j := Subtype.ext ((congrArg Prod.fst ha').trans hchar)
  rw [← heq]
  let e := (P.pin a).val.symm ≪≫ (P.pin a').val
  refine ⟨e, (cancel_epi (P.pin a).val.hom).mp ?_⟩
  simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    using (congrArg Prod.snd ha').symm

end PinnedAction
section GeometricPoints

open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsReductive)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup)
open Specs.CentralDerived (firstProjection secondProjection)
open Specs.RelativeFormComparison (fieldTest IsInduced)
open Specs.AutomorphismSequence
open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.QuasiSplitInnerForms (outerHom pinnedSection)
open Specs.RootGroups (AdditiveLine)
open private rationalPointsEquiv fieldTestSpecIso smooth_baseChanged
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private hom_ext_rational
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private surjectiveOnSections productAlgebraicGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private pullback_map_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeBorelAlignment
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {E : Type u} [Field E]

private theorem rationalPoints_natural {G H : GroupScheme E} (f : G ⟶ H)
    (x : 𝟙_ (SchemeOver E) ⟶ G.X) :
    rationalPointsEquiv E H (x ≫ f.hom.hom) =
      onPoints f (CommAlgCat.of E E) (rationalPointsEquiv E G x) := by
  change (fieldTestSpecIso E).hom ≫ (x ≫ f.hom.hom) =
    ((fieldTestSpecIso E).hom ≫ x) ≫ f.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem morphism_eq_of_geometric_points [Algebra K E] [IsAlgClosed E]
    {G H : AffineAlgebraicGroup K} (hG : Smooth G.val.X.hom) {f g : G.val ⟶ H.val}
    (h : ∀ x : Points ((groupBaseChange K E).obj G.val).X (CommAlgCat.of E E),
      onPoints ((groupBaseChange K E).map f) (CommAlgCat.of E E) x =
        onPoints ((groupBaseChange K E).map g) (CommAlgCat.of E E) x) :
    f = g := by
  apply groupBaseChange_map_injective (K := E)
  apply Grp.hom_ext
  let A := baseChangedAlgebraicGroup E G
  let B := baseChangedAlgebraicGroup E H
  letI : IsReduced ((groupBaseChange K E).obj G.val).X.left := by
    letI : Smooth A.val.X.hom := smooth_baseChanged E hG
    exact isReduced_of_smooth_over_field A.val.X.hom
  letI : LocallyOfFiniteType ((groupBaseChange K E).obj G.val).X.hom := A.property.2.1
  letI : LocallyOfFiniteType ((groupBaseChange K E).obj H.val).X.hom := B.property.2.1
  letI := B.property.1
  letI : IsAffineHom B.val.X.hom := isAffineHom_of_isAffine _
  letI : IsSeparated ((groupBaseChange K E).obj H.val).X.hom :=
    inferInstanceAs (IsSeparated B.val.X.hom)
  change ((groupBaseChange K E).map f).hom.hom = ((groupBaseChange K E).map g).hom.hom
  apply hom_ext_rational
  intro x
  apply (rationalPointsEquiv E ((groupBaseChange K E).obj H.val)).injective
  rw [rationalPoints_natural, rationalPoints_natural]
  exact h _

/-- A surjective homomorphism of affine algebraic groups lifts sections over an
algebraically closed extension by taking a rational point of the fiber. -/
private theorem lifted_section [Algebra F E] [IsAlgClosed E]
    {G H : AffineAlgebraicGroup F} (f : G.val ⟶ H.val) (hf : Surjective f.hom.hom.left)
    (x : fieldTest F E ⟶ H.val.X) :
    ∃ y : fieldTest F E ⟶ G.val.X, y ≫ f.hom.hom = x := by
  let R := CommAlgCat.of E E
  let B := groupBaseChange F E
  let gx := (baseChangePointGroupEquiv E H.val R).symm x
  let q := (rationalPointsEquiv E (B.obj H.val)).symm gx
  have hsur : Surjective (B.map f).hom.hom.left :=
    MorphismProperty.of_isPullback
      (pullback_map_square (S := fieldTest F E) f.hom.hom).flip hf
  obtain ⟨p, hp⟩ := surjectiveOnSections
    (G := baseChangedAlgebraicGroup E G) (Q := baseChangedAlgebraicGroup E H) (B.map f) hsur q
  let y := rationalPointsEquiv E (B.obj G.val) p
  refine ⟨baseChangePointGroupEquiv E G.val R y, ?_⟩
  change onPoints f ((restrictTestAlgebra F E).obj R) (baseChangePointGroupEquiv E G.val R y) = x
  rw [← point_baseChange f, ← rationalPoints_natural, hp]
  exact (baseChangePointGroupEquiv E H.val R).apply_symm_apply x

set_option maxHeartbeats 3000000 in
private theorem central_product_conjugation [Algebra F E] [IsAlgClosed E]
    (L : AffineAlgebraicGroup F) (hL : IsReductive L)
    (H : ClosedSubgroup L.val) (hH : IsDerivedSubgroup H) (g : fieldTest F E ⟶ L.val.X) :
    ∃ v : fieldTest F E ⟶ H.group.X, ∀ x : fieldTest F E ⟶ L.val.X,
      g * x * g⁻¹ =
        (v ≫ H.inclusion.hom.hom) * x * (v ≫ H.inclusion.hom.hom)⁻¹ := by
  obtain ⟨Z, hZ, T, hT, _⟩ := Reductive.CentralDerived.centralTorusExists L hL
  obtain ⟨m, hm, _⟩ := Reductive.CentralDerived.centralProductKernel L hL Z hZ T hT H hH
  have hs := (Reductive.CentralDerived.centralProductFaithfullyFlat L hL Z hZ T hT H hH m hm).2
  let Z' := closedSubgroupAlgebraicGroup (G := L) Z
  let T' := closedSubgroupAlgebraicGroup (G := Z') T
  let H' := closedSubgroupAlgebraicGroup (G := L) H
  obtain ⟨w, hw⟩ := lifted_section (G := productAlgebraicGroup T' H') (H := L) m hs g
  let z := w ≫ (firstProjection T.group H.group ≫ T.inclusion).hom.hom
  let v := w ≫ (secondProjection T.group H.group).hom.hom
  refine ⟨v, fun x => ?_⟩
  let t := z ≫ Z.inclusion.hom.hom
  let d := v ≫ H.inclusion.hom.hom
  have hg : g = t * d := by
    change m.hom.hom = _ at hm
    rw [← hw, hm, MonObj.comp_mul]
    rfl
  have hcent (y : fieldTest F E ⟶ L.val.X) : Commute t y := by
    have he := (centralizes_iff (𝟙 L.val) t).mp
      ((hZ _ t).mpr ⟨z, rfl⟩) _ (𝟙 _) y
    simpa only [Grp.id_hom_hom, Category.id_comp, Category.comp_id] using he
  calc
    g * x * g⁻¹ = t * (d * x * d⁻¹) * t⁻¹ := by rw [hg]; group
    _ = d * x * d⁻¹ := by rw [(hcent _).eq, mul_inv_cancel_right]

end GeometricPoints
section GeometricParabolic

open Specs.SchemeDerivedGroup (IsSubgroupOf FactorsThrough)
open Specs.GeometricRadicals (IsReductive)
open Specs.GeometricBorelConjugacy (IsBorel subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private conjugate conjugation conjugation_apply borel_conjugate factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private restrictSubgroup compose_restrict normalizes_of_conjugates_self from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private borel_in_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
open private factors_of_range_subset from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

variable {E : Type u} [Field E] [IsAlgClosed E]

private theorem subgroupOf_of_rational_sections {G : AffineAlgebraicGroup E}
    (A B : ClosedSubgroup G.val) (hA : Smooth A.group.X.hom)
    (h : ∀ x : 𝟙_ (SchemeOver E) ⟶ A.group.X,
      FactorsThrough B (x ≫ A.inclusion.hom.hom)) : IsSubgroupOf A B := by
  let X := A.group.X
  let Y := B.group.X
  let f := A.inclusion.hom.hom
  let g := B.inclusion.hom.hom
  haveI : LocallyOfFiniteType X.hom := (closedSubgroupAlgebraicGroup A).property.2.1
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : Smooth X.hom := hA
  haveI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  have hclosed : IsClosed (Set.range g.left) := B.isClosedImmersion.isClosedEmbedding.isClosed_range
  have hrange : Set.range f.left ⊆ Set.range g.left := by
    suffices hall : Set.univ ⊆ f.left ⁻¹' Set.range g.left by
      rintro _ ⟨x, rfl⟩
      exact hall (Set.mem_univ x)
    have hpre : IsClosed (f.left ⁻¹' Set.range g.left) := hclosed.preimage f.left.continuous
    rw [← closure_closedPoints]
    apply closure_minimal _ hpre
    intro x hx
    let t := sectionOfClosedPoint X x hx
    obtain ⟨z, hz⟩ := h t
    refine ⟨z.left (IsLocalRing.closedPoint E), ?_⟩
    have hpt := congrArg (fun a : 𝟙_ (SchemeOver E) ⟶ G.val.X =>
      a.left (IsLocalRing.closedPoint E)) hz
    change g.left (z.left (IsLocalRing.closedPoint E)) =
      f.left (t.left (IsLocalRing.closedPoint E)) at hpt
    rwa [sectionOfClosedPoint_apply] at hpt
  obtain ⟨q, hq⟩ := factors_of_range_subset f g B.isClosedImmersion hrange
  exact factor_group_through_subgroup B A.inclusion q hq

/-- If a conjugate of a Borel lies in a connected smooth subgroup containing
the Borel, then the conjugating point lies in that subgroup. -/
private theorem borel_conjugator_mem
    (G : AffineAlgebraicGroup E) (hG : IsReductive G)
    (B P : ClosedSubgroup G.val) (hB : IsBorel B)
    (hP : Smooth P.group.X.hom) (hPc : ConnectedSpace P.group.X.left)
    (hBP : IsSubgroupOf B P) (g : 𝟙_ (SchemeOver E) ⟶ G.val.X)
    (hconj : IsSubgroupOf (conjugate g B) P) :
    FactorsThrough P g := by
  obtain ⟨i, hi⟩ := hBP
  obtain ⟨j, hj⟩ := hconj
  let B₁ := restrictSubgroup B P i hi
  let B₂ := restrictSubgroup (conjugate g B) P j hj
  have h₁ : IsBorel B₁ :=
    borel_in_subgroup B₁ ((compose_restrict B P i hi).symm ▸ hB)
  have h₂ : IsBorel B₂ :=
    borel_in_subgroup B₂ ((compose_restrict (conjugate g B) P j hj).symm ▸ borel_conjugate g hB)
  obtain ⟨p, e, he⟩ := GeometricBorelConjugacy.borelsConjugate
    (closedSubgroupAlgebraicGroup P) hP hPc B₁ B₂ h₁ h₂
  change 𝟙_ (SchemeOver E) ⟶ P.group.X at p
  change B.group ≅ B.group at e
  let q := p ≫ P.inclusion.hom.hom
  let X := B.group.X
  let Q := toUnit X ≫ q
  let G₀ := toUnit X ≫ g
  let a : X ⟶ G.val.X := (e.hom ≫ B.inclusion).hom.hom
  let b : X ⟶ G.val.X := B.inclusion.hom.hom
  have he' : G₀ * a * G₀⁻¹ = Q * b * Q⁻¹ := by
    have h := congrArg (· ≫ P.inclusion.hom.hom) he
    change ((e.hom ≫ j).hom.hom ≫ P.inclusion.hom.hom) =
      ((toUnit X ≫ p) * i.hom.hom * (toUnit X ≫ p)⁻¹) ≫ P.inclusion.hom.hom at h
    rw [← Grp.comp_hom_hom, Category.assoc, hj, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, ← Grp.comp_hom_hom i, hi, Category.assoc] at h
    change a ≫ (conjugation g).hom.hom = Q * b * Q⁻¹ at h
    rw [conjugation_apply] at h
    exact h
  let z := g⁻¹ * q
  have hz : Normalizes B.inclusion z := by
    apply normalizes_of_conjugates_self B
    refine ⟨e, ?_⟩
    change a = (toUnit X ≫ z) * b * (toUnit X ≫ z)⁻¹
    rw [show toUnit X ≫ z = G₀⁻¹ * Q by simp only [z, MonObj.comp_mul, GrpObj.comp_inv, G₀, Q]]
    calc
      a = G₀⁻¹ * (G₀ * a * G₀⁻¹) * G₀ := by group
      _ = _ := by rw [he']; group
  have hzB := (Flag.StandardParabolics.geometricParabolicNormalizer
    G hG B hB.1.1 ⟨B, hB, 𝟙 _, Category.id_comp _⟩ _ z).mp hz
  obtain ⟨v, hv⟩ := hzB
  have hqP : q ∈ SubgroupSections P (𝟙_ (SchemeOver E)) := ⟨p, rfl⟩
  have hzP : z ∈ SubgroupSections P (𝟙_ (SchemeOver E)) :=
    ⟨v ≫ i.hom.hom, by change (v ≫ i.hom.hom) ≫ P.inclusion.hom.hom = z
                       rw [Category.assoc, ← Grp.comp_hom_hom, hi]; exact hv⟩
  have hout := (SubgroupSections P _).mul_mem hqP ((SubgroupSections P _).inv_mem hzP)
  have he : q * z⁻¹ = g := by dsimp only [z]; group
  rw [he] at hout
  exact hout

end GeometricParabolic
section GeometricDisplacement

open Specs.AutomorphismSequence
open Specs.Pinning (PinnedGroup AttachedDatum PinnedIso)
open Specs.QuasiSplitInnerForms (outerHom pinnedSection)
open Specs.RootGroups (AdditiveLine)
open Specs.RelativeFormComparison (IsInduced fieldTest)
open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf IsDerivedSubgroup)
open Specs.GeometricRadicals (IsReductive)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter)
open Specs.StandardParabolicLevi (HasFace)
open Specs.AbstractPairing (Root)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private relativeSectionEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private extendSubgroup extend_subgroupOf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private extended_borel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeBorelAlignment
open private conjugate conjugation conjugation_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private rationalPointsEquiv smooth_baseChanged connected_baseChanged
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private connected_of_geometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

variable (E : Type u) [Field E] [Algebra K E]

private abbrev fieldTowerAlgebra : Algebra F E :=
  ((algebraMap K E).comp (algebraMap F K)).toAlgebra

private abbrev extendedFieldTest : SchemeOver F :=
  @fieldTest F E _ _ (fieldTowerAlgebra (F := F) (K := K) E)

private abbrev extensionArrow : extendedFieldTest (F := F) (K := K) E ⟶ fieldTest F K :=
  letI : Algebra F E := fieldTowerAlgebra (F := F) (K := K) E
  letI : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' rfl
  (testSpec F).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F K E)).op

private abbrev extensionObject : Over (fieldTest F K) := Over.mk (extensionArrow (F := F) (K := K) E)

private abbrev kTest : TestAlgebra K := CommAlgCat.of K E

private def extendPoints (G : GroupScheme F) :
    Points ((groupBaseChange F K).obj G).X (kTest E) ≃* ((extendedFieldTest (F := F) (K := K) E) ⟶ G.X) :=
  baseChangePointGroupEquiv K G (kTest E)

private theorem extendPoints_map {G H : GroupScheme F} (f : G ⟶ H) (x) :
    extendPoints E H (onPoints ((groupBaseChange F K).map f) (kTest E) x) =
      extendPoints E G x ≫ f.hom.hom := point_baseChange f _ x

private theorem induced_on_extension {G : GroupScheme F}
    (a : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj G)
    (α : RelativeAut G (fieldTest F K)) (ha : IsInduced F K a α.asIso)
    (x : Points ((groupBaseChange F K).obj G).X (kTest E)) :
    extendPoints E G (onPoints a.hom (kTest E) x) =
      (α.asIso.hom.app (op (extensionObject E))).hom (extendPoints E G x) := by
  let U : Over (fieldTest F K) := extensionObject E
  let y := extendPoints E G x
  apply Over.OverMorphism.ext
  have he := ha U y
  have hy : ((relativeSectionEquiv U G.X).symm y).left = x.left := by
    change (pullback.lift y.left U.hom.left _) = x.left
    apply pullback.hom_ext
    · exact pullback.lift_fst ..
    · rw [pullback.lift_snd]
      exact (Over.w x).symm
  change _ = (pullback.lift y.left U.hom.left _ ≫ _) ≫ _ at he
  rw [show pullback.lift y.left U.hom.left _ = x.left from hy] at he
  exact he.symm

variable [IsAlgClosed E]
variable {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
variable {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}

private theorem displacement_by_inner (seq : SplitSequence P D l Q)
    (α : RelativeAut P.pair.G.val (fieldTest F K)) :
    ∃ g : (extendedFieldTest (F := F) (K := K) E) ⟶ P.pair.G.val.X,
      ∀ x : (extendedFieldTest (F := F) (K := K) E) ⟶ P.pair.G.val.X,
        (α.asIso.hom.app (op (extensionObject E))).hom x =
          g * (x ≫ (l (outerHom seq α)).asIso.hom.group.hom.hom.hom) * g⁻¹ := by
  let d := outerHom seq α
  let v := pinnedSection (S := K) seq d
  let β := α * v⁻¹
  have hright := (Descent.QuasiSplitInnerForms.splitCoefficientMaps (S := K) seq).2.2 d
  have hβ : outerHom seq β = 1 := by
    change outerHom seq (α * v⁻¹) = 1
    rw [map_mul, map_inv, hright, mul_inv_cancel]
  obtain ⟨q, hq⟩ := (Descent.QuasiSplitInnerForms.splitKernel (S := K) seq β).mp hβ
  letI : Algebra F E := fieldTowerAlgebra (F := F) (K := K) E
  let t : (extendedFieldTest (F := F) (K := K) E) ⟶ fieldTest F K := extensionArrow E
  obtain ⟨g, hg⟩ := lifted_section Q.projection Q.fppf.2.1 (t ≫ q.down)
  let V := (extendedFieldTest (F := F) (K := K) E)
  have he : restrictAut t β = innerAut g := by
    rw [← hq]
    change (automorphisms P.pair.G.val).map t.op (seq.inner.app _ q) = _
    rw [← NatTrans.naturality_apply seq.inner]
    change seq.inner.app (op V) ⟨(t ≫ q.down)⟩ = innerAut g
    rw [← hg]
    exact seq.onLift V g
  let w : Aut P.pair.G.val := Functor.mapAut P (forgetPinning (A := A)) (l d)
  have hv : v = scalarAut w (fieldTest F K) := seq.sectionOnConstants _ d
  have hres : restrictAut t α = innerAut g * scalarAut w V := by
    calc
      restrictAut t α = restrictAut t (β * v) := by rw [show β * v = α by simp [β]]
      _ = _ := by
        rw [map_mul, he, hv]
        rfl
  refine ⟨g, fun x => ?_⟩
  have hh := congrArg (fun f : RelativeAut P.pair.G.val V =>
    (f.asIso.hom.app (op (Over.mk (𝟙 V)))).hom x) hres
  change (α.asIso.hom.app (op (extensionObject E))).hom x =
    (𝟙 V ≫ g) * (x ≫ (l d).asIso.hom.group.hom.hom.hom) * (𝟙 V ≫ g)⁻¹ at hh
  simpa only [Category.id_comp] using hh

/-- The inner part of a displacement preserving the parabolic is represented
by a point of the parabolic over the algebraically closed extension. -/
private theorem displacement_parabolic_point
    (seq : SplitSequence P D l Q) (c : Cocharacter P.pair.T.group)
    (M : LimitDecomposition (c ≫ P.pair.T.inclusion)) (J : Set (Root P.pair.T))
    (hface : letI := D.comm; HasFace D.base J c) (hP : IsParabolic P.pair.G M.parabolic)
    (a : (groupBaseChange F K).obj P.pair.G.val ≅ (groupBaseChange F K).obj P.pair.G.val)
    (α : RelativeAut P.pair.G.val (fieldTest F K)) (ha : IsInduced F K a α.asIso)
    (p : (groupBaseChange F K).obj M.parabolic.group ≅ (groupBaseChange F K).obj M.parabolic.group)
    (hp : (groupBaseChange F K).map M.parabolic.inclusion ≫ a.hom =
      p.hom ≫ (groupBaseChange F K).map M.parabolic.inclusion) :
    ∃ g : (extendedFieldTest (F := F) (K := K) E) ⟶ M.parabolic.group.X,
      ∀ x : (extendedFieldTest (F := F) (K := K) E) ⟶ P.pair.G.val.X,
        (α.asIso.hom.app (op (extensionObject E))).hom x =
          (g ≫ M.parabolic.inclusion.hom.hom) *
            (x ≫ (l (outerHom seq α)).asIso.hom.group.hom.hom.hom) *
            (g ≫ M.parabolic.inclusion.hom.hom)⁻¹ := by
  letI : Algebra F E := fieldTowerAlgebra (F := F) (K := K) E
  obtain ⟨h, hα⟩ := displacement_by_inner E seq α
  let G := baseChangedAlgebraicGroup E P.pair.G
  let B := extendSubgroup E P.pair.B
  let N := extendSubgroup E M.parabolic
  let ϕ (H : GroupScheme F) :=
    (rationalPointsEquiv E ((groupBaseChange F E).obj H)).trans
      (baseChangePointGroupEquiv E H (CommAlgCat.of E E))
  have natural {H J : GroupScheme F} (f : H ⟶ J) (x) :
      ϕ J (x ≫ ((groupBaseChange F E).map f).hom.hom) = ϕ H x ≫ f.hom.hom := by
    change baseChangePointGroupEquiv E J (CommAlgCat.of E E) (rationalPointsEquiv E _
      (x ≫ ((groupBaseChange F E).map f).hom.hom)) = _
    rw [rationalPoints_natural]
    exact point_baseChange f _ _
  let g := (ϕ P.pair.G.val).symm h
  obtain ⟨i, hi⟩ := face_contains_borel P D c M J hface
  let f := (l (outerHom seq α)).asIso.hom
  have hB := extended_borel P.pair E
  have hN := smooth_baseChanged E hP.2.1
  letI : Smooth P.pair.G.val.X.hom := P.pair.reductive.1
  letI : ConnectedSpace P.pair.G.val.X.left :=
    connected_of_geometricallyConnected P.pair.reductive.2.1
  have hNc := connected_baseChanged E
    (CocharacterDynamics.geometricallyConnectedLimitSubgroups P.pair.G _ M).1
  have hG : IsReductive G :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := E) P.pair.G
      P.pair.reductive.1 P.pair.reductive.2.1).2 P.pair.reductive
  have hgB : IsSubgroupOf (conjugate g B) N := by
    apply subgroupOf_of_rational_sections (G := G) (conjugate g B) N hB.1.1
    intro b
    let x : (extendedFieldTest (F := F) (K := K) E) ⟶ P.pair.B.group.X := ϕ P.pair.B.group b ≫ f.borel.inv.hom.hom
    let y : (extendedFieldTest (F := F) (K := K) E) ⟶ P.pair.G.val.X := x ≫ P.pair.B.inclusion.hom.hom
    let z := (extendPoints E M.parabolic.group).symm (x ≫ i.hom.hom)
    have hz : extendPoints E P.pair.G.val
        (onPoints ((groupBaseChange F K).map M.parabolic.inclusion) (kTest E) z) = y := by
      rw [extendPoints_map, MulEquiv.apply_symm_apply]
      change x ≫ i.hom.hom ≫ M.parabolic.inclusion.hom.hom = _
      rw [← Grp.comp_hom_hom, hi]
    let v := onPoints p.hom (kTest E) z
    let v' := (ϕ M.parabolic.group).symm (extendPoints (K := K) E M.parabolic.group v)
    refine ⟨v', (ϕ P.pair.G.val).injective ?_⟩
    change ϕ P.pair.G.val (v' ≫ ((groupBaseChange F E).map M.parabolic.inclusion).hom.hom) =
      ϕ P.pair.G.val ((b ≫ B.inclusion.hom.hom) ≫ (conjugation g).hom.hom)
    have hb := natural P.pair.B.inclusion b
    change ϕ P.pair.G.val (b ≫ B.inclusion.hom.hom) =
      ϕ P.pair.B.group b ≫ P.pair.B.inclusion.hom.hom at hb
    rw [natural M.parabolic.inclusion, conjugation_apply, map_mul, map_mul, map_inv, hb]
    have ht : toUnit (𝟙_ (SchemeOver E)) = 𝟙 _ :=
      (isTerminalTensorUnit (C := SchemeOver E)).hom_ext _ _
    rw [ht, Category.id_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hcancel : x ≫ f.borel.hom.hom.hom = ϕ P.pair.B.group b := by
      dsimp only [x]
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]
    have hy : y ≫ f.group.hom.hom.hom =
        ϕ P.pair.B.group b ≫ P.pair.B.inclusion.hom.hom := by
      change x ≫ P.pair.B.inclusion.hom.hom ≫ f.group.hom.hom.hom = _
      rw [← Grp.comp_hom_hom, f.borel_comm, Grp.comp_hom_hom, ← Category.assoc, hcancel]
    rw [← hy, ← hα y, ← hz, ← induced_on_extension E a α ha, ← onPoints_comp, hp,
      onPoints_comp, extendPoints_map]
  obtain ⟨gN, hgN⟩ := borel_conjugator_mem G hG B N hB hN hNc
    (extend_subgroupOf (K := E) ⟨i, hi⟩) g hgB
  refine ⟨ϕ M.parabolic.group gN, fun x => ?_⟩
  have hg : ϕ M.parabolic.group gN ≫ M.parabolic.inclusion.hom.hom = h := by
    rw [← natural]
    change gN ≫ ((groupBaseChange F E).map M.parabolic.inclusion).hom.hom = g at hgN
    rw [hgN]
    exact (ϕ P.pair.G.val).apply_symm_apply h
  rw [hg, hα]

end GeometricDisplacement
section FactorAction

open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AutomorphismSequence
open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.RootGroups (AdditiveLine)
open Specs.RelativeFormComparison (fieldTest IsInduced)
open Specs.QuasiSplitInnerForms (outerHom)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup)
open Specs.BorelProper (IsParabolic)
open Specs.GeometricRadicals (IsReductive)
open Specs.CharacterDescent (Cocharacter)
open Specs.StandardParabolicLevi (HasFace)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private smooth_baseChanged from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure

variable (E : Type u) [Field E] [Algebra K E] [IsAlgClosed E]

private def extendedAutomorphism {H : GroupScheme F}
    (δ : (groupBaseChange F K).obj H ≅ (groupBaseChange F K).obj H) :
    ((extendedFieldTest (F := F) (K := K) E) ⟶ H.X) →* ((extendedFieldTest (F := F) (K := K) E) ⟶ H.X) :=
  (extendPoints E H).toMonoidHom.comp <|
    (onPoints δ.hom (kTest E)).comp (extendPoints E H).symm.toMonoidHom

private theorem off_diagonal_zero {I : Type u} [Finite I] [DecidableEq I]
    {H : GroupScheme F} (S : AffineAlgebraicGroup F) (s : SpecialMatrixPoints S 2)
    (π : I → (H ⟶ S.val)) (hπ : IsLimit (Fan.mk H π))
    (δ : (groupBaseChange F K).obj H ≅ (groupBaseChange F K).obj H)
    (i j : I) {U : GroupScheme F} (uᵣ : U ⟶ H)
    (hu : ∀ j, j ≠ i → uᵣ ≫ π j = 0)
    (hs : IsUpperRootProjection s (uᵣ ≫ π i))
    (h : ∀ x : (extendedFieldTest (F := F) (K := K) E) ⟶ U.X,
      extendedAutomorphism E δ (x ≫ uᵣ.hom.hom) ≫ (π j).hom.hom = 1) :
    (groupBaseChange F K).map (productSection π hπ i) ≫ δ.hom ≫
      (groupBaseChange F K).map (π j) = 0 := by
  let B := groupBaseChange F K
  let S' := baseChangedAlgebraicGroup K S
  let f := B.map (productSection π hπ i) ≫ δ.hom ≫ B.map (π j)
  have hsmooth : Smooth S'.val.X.hom := smooth_baseChanged K
    (GeneralLinearStructure.specialLinearGeometry F 2 (by decide) S s)
  change f = (0 : S'.val ⟶ S'.val)
  apply morphism_eq_of_geometric_points (E := E) (G := S') (H := S') hsmooth
  intro x
  apply (baseChangePointGroupEquiv E S'.val (CommAlgCat.of E E)).injective
  rw [point_baseChange, point_baseChange, onPoints_zero]
  let R := kTest (K := K) E
  let RF := (restrictTestAlgebra F K).obj R
  let ES := extendPoints (K := K) E S.val
  let matrix := ES.trans ((s.app RF).groupIsoToMulEquiv)
  let m := (onPoints f R).comp matrix.symm.toMonoidHom
  have hrange := (hs RF).2
  change Set.range (fun x : Points U.X RF => s.hom.app RF (onPoints (uᵣ ≫ π i) RF x)) =
    Set.range (fun t : RF => Matrix.SpecialLinearGroup.transvection first_ne_last t) at hrange
  have hm (t : E) : m (Matrix.SpecialLinearGroup.transvection first_ne_last t) = 1 := by
    have ht : Matrix.SpecialLinearGroup.transvection first_ne_last (show RF from t) ∈
        Set.range (fun x : Points U.X RF => s.hom.app RF (onPoints (uᵣ ≫ π i) RF x)) := by
      rw [hrange]
      exact ⟨t, rfl⟩
    obtain ⟨y, hy⟩ := ht
    let a := Matrix.SpecialLinearGroup.transvection first_ne_last t
    let z := matrix.symm a
    have hz : extendPoints E S.val z = onPoints (uᵣ ≫ π i) RF y := by
      apply ((s.app RF).groupIsoToMulEquiv).injective
      change matrix z = s.hom.app RF (onPoints (uᵣ ≫ π i) RF y)
      exact (matrix.apply_symm_apply a).trans hy.symm
    have heq : extendPoints E H (onPoints (B.map (productSection π hπ i)) R z) =
        y ≫ uᵣ.hom.hom := by
      apply (pointProduct π hπ RF).injective
      funext k
      change (extendPoints E H (onPoints (B.map (productSection π hπ i)) R z)) ≫
        (π k).hom.hom = (y ≫ uᵣ.hom.hom) ≫ (π k).hom.hom
      rw [extendPoints_map, Category.assoc, ← Grp.comp_hom_hom, productSection_comp,
        Category.assoc, ← Grp.comp_hom_hom]
      by_cases hk : k = i
      · subst k
        rw [ite_eq_left rfl, Grp.id_hom_hom, Category.comp_id]
        exact hz
      · rw [ite_eq_right hk, hu k hk]
        change ES z ≫ (1 : S.val.X ⟶ S.val.X) = y ≫ (1 : U.X ⟶ S.val.X)
        simp only [MonObj.comp_one]
    apply ES.injective
    change ES (onPoints f R z) = ES 1
    rw [map_one]
    change ES (onPoints (B.map (π j)) R
      (onPoints δ.hom R (onPoints (B.map (productSection π hπ i)) R z))) = 1
    rw [extendPoints_map]
    have ho := h y
    change extendPoints E H
      (onPoints δ.hom R ((extendPoints E H).symm (y ≫ uᵣ.hom.hom))) ≫ (π j).hom.hom = 1 at ho
    rwa [← heq, MulEquiv.symm_apply_apply] at ho
  have hall := upper_generates_normally m hm
  let x' := baseChangePointGroupEquiv E S'.val (CommAlgCat.of E E) x
  have hx := hall (matrix x')
  change onPoints f R (matrix.symm (matrix x')) = 1 at hx
  rwa [MulEquiv.symm_apply_apply] at hx

set_option maxHeartbeats 3500000 in
theorem factorDisplacement : FactorDisplacement.{u} := by
  classical
  intro F K I _ _ _ _ _ A P D l Q seq r hr c M hface hP hL H hH
  dsimp only
  intro a α ha p b δ hp hb hδ τ hτ S s π ⟨hπ⟩ uᵣ hu ho hs
  let E := AlgebraicClosure K
  letI : Algebra F E := fieldTowerAlgebra (F := F) (K := K) E
  let C := groupBaseChange F K
  let L := closedSubgroupAlgebraicGroup (G := P.pair.G) M.centralizer
  let H' := closedSubgroupAlgebraicGroup (G := L) H
  let R := kTest (K := K) E
  obtain ⟨g, hg⟩ := displacement_parabolic_point E seq c M (Set.range r) hface hP a α ha p hp
  obtain ⟨v, hv⟩ := central_product_conjugation (E := E) L hL H (hH) (g ≫ M.limit.hom.hom)
  apply projection_isomorphisms (K := K) π hπ
    (baseChangedAlgebraicGroup K H').property.1 (baseChangedAlgebraicGroup K S).property.1 δ τ
  intro i j hij
  apply off_diagonal_zero E S s π hπ δ i j (uᵣ i) (ho i) (hs i)
  intro x
  let d := outerHom seq α
  have hi := (D.simple_iff (r i)).mp (hr ⟨i, rfl⟩)
  obtain ⟨e, he⟩ := pinned_lift_root seq d (r i) (r (τ i)) hi (hτ i)
  let f := (l d).asIso.hom.group.hom
  let y := (x ≫ e.hom.hom.hom) ≫ (uᵣ (τ i)).hom.hom
  let t := extendedAutomorphism E δ (x ≫ (uᵣ i).hom.hom)
  let m := H.inclusion ≫ M.centralizer.inclusion
  let n := H.inclusion ≫ M.sectionMap
  have hn : n ≫ M.parabolic.inclusion = m := by
    simp only [n, m, Category.assoc, M.section_in_G]
  have hboth : C.map m ≫ a.hom = δ.hom ≫ C.map m := by
    dsimp only [m]
    rw [C.map_comp, Category.assoc, hb, ← Category.assoc, hδ, Category.assoc]
  have hpinned : (x ≫ (uᵣ i).hom.hom) ≫ m.hom.hom ≫ f.hom.hom = y ≫ m.hom.hom := by
    have hroot (k : I) : uᵣ k ≫ m = (P.roots (r k)).val.inclusion := hu k
    have hcomp : (uᵣ i ≫ m) ≫ f = e.hom ≫ (uᵣ (τ i) ≫ m) := by
      rw [hroot i, hroot (τ i)]
      exact he
    calc
      _ = x ≫ ((uᵣ i ≫ m) ≫ f).hom.hom := by simp only [Grp.comp_hom_hom, Category.assoc]
      _ = _ := by rw [hcomp]; simp only [y, Grp.comp_hom_hom, Category.assoc]
  have hG : t ≫ m.hom.hom =
      (g ≫ M.parabolic.inclusion.hom.hom) * (y ≫ m.hom.hom) *
        (g ≫ M.parabolic.inclusion.hom.hom)⁻¹ := by
    let z := (extendPoints E H.group).symm (x ≫ (uᵣ i).hom.hom)
    have hpre : extendPoints E P.pair.G.val (onPoints (C.map m) R z) =
        (x ≫ (uᵣ i).hom.hom) ≫ m.hom.hom := by
      rw [extendPoints_map, MulEquiv.apply_symm_apply]
    have ha' := induced_on_extension E a α ha (onPoints (C.map m) R z)
    rw [hpre, hg] at ha'
    change extendPoints E P.pair.G.val (onPoints a.hom R (onPoints (C.map m) R z)) =
      (g ≫ M.parabolic.inclusion.hom.hom) *
        ((x ≫ (uᵣ i).hom.hom) ≫ m.hom.hom ≫ f.hom.hom) *
        (g ≫ M.parabolic.inclusion.hom.hom)⁻¹ at ha'
    rw [hpinned] at ha'
    rw [← onPoints_comp, hboth, onPoints_comp, extendPoints_map] at ha'
    exact ha'
  letI := mono_over M.parabolic.inclusion.hom.hom M.parabolic.isClosedImmersion
  have hN : t ≫ n.hom.hom = g * (y ≫ n.hom.hom) * g⁻¹ := by
    apply (cancel_mono M.parabolic.inclusion.hom.hom).mp
    simp only [Category.assoc, MonObj.mul_comp, GrpObj.inv_comp, ← Grp.comp_hom_hom, hn]
    exact hG
  have hlim : n ≫ M.limit = H.inclusion := by
    simp only [n, Category.assoc, M.section_limit, Category.comp_id]
  have hLevi : t ≫ H.inclusion.hom.hom =
      (g ≫ M.limit.hom.hom) * (y ≫ H.inclusion.hom.hom) * (g ≫ M.limit.hom.hom)⁻¹ := by
    have h := congrArg (· ≫ M.limit.hom.hom) hN
    simpa only [Category.assoc, MonObj.mul_comp, GrpObj.inv_comp, ← Grp.comp_hom_hom, hlim] using h
  letI := mono_over H.inclusion.hom.hom H.isClosedImmersion
  have hHpt : t = v * y * v⁻¹ := by
    apply (cancel_mono H.inclusion.hom.hom).mp
    rw [hLevi, hv]
    simp only [MonObj.mul_comp, GrpObj.inv_comp]
  change t ≫ (π j).hom.hom = 1
  have hzero : y ≫ (π j).hom.hom = 1 := by
    rw [Category.assoc, ← Grp.comp_hom_hom, ho _ _ hij]
    exact onPoints_zero _ _
  rw [hHpt, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hzero, mul_one, mul_inv_cancel]

end FactorAction

end

end LinearAlgebraicGroups.Arithmetic.OrthogonalLeviFactorDisplacement
