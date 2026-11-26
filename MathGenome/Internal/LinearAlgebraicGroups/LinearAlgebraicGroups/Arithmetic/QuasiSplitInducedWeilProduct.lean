import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.TensorProduct.Pi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Coalgebra HopfAlgebra
open scoped TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct

open Specs.QuasiSplitInducedWeilProduct
open _root_.LinearAlgebraicGroups.Specs
open Module
open WeilRestriction (restrictScalars extendScalars)

set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open _root_.LinearAlgebraicGroups.Descent

universe u

noncomputable section

theorem orbitFieldEmbeddings : OrbitFieldEmbeddings.{u} := by
  classical
  intro F K I _ _ _ _ _ _ i horbit
  let J := MulAction.stabilizer Gal(K/F) i
  let L := IntermediateField.fixedField J
  choose g hg using horbit
  let φ (s : Gal(K/F)) : L →ₐ[F] K := s.toAlgHom.comp L.val
  have hφ (s t : Gal(K/F)) : φ s = φ t ↔ s • i = t • i := by
    have hJ : L.fixingSubgroup = J := IntermediateField.fixingSubgroup_fixedField J
    rw [← show t⁻¹ * s ∈ J ↔ s • i = t • i from by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]]
    rw [← hJ, IntermediateField.mem_fixingSubgroup_iff]
    refine ⟨fun h x hx => ?_, fun h => AlgHom.ext fun x => ?_⟩
    · have he : s x = t x := DFunLike.congr_fun h ⟨x, hx⟩
      change t.symm (s x) = x
      rw [he, AlgEquiv.symm_apply_apply]
    · have he := h x.val x.property
      change t.symm (s x.val) = x.val at he
      exact (t.apply_symm_apply _).symm.trans (congrArg t he)
  let f (j : I) := φ (g j)
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      simpa only [hg] using (hφ (g j) (g k)).mp h
    · intro a
      obtain ⟨s₀, hs₀⟩ := IntermediateField.exists_algHom_of_splits
        (fun x : K => ⟨IsGalois.integral F x, IsGalois.splits F x⟩) a
      let s : Gal(K/F) := (algEquivEquivAlgHom F K).symm s₀
      have hs : φ s = a := (congrArg (fun b : K →ₐ[F] K => b.comp L.val)
        ((algEquivEquivAlgHom F K).apply_symm_apply s₀)).trans hs₀
      exact ⟨s • i, ((hφ (g (s • i)) s).2 (hg (s • i))).trans hs⟩
  refine ⟨Equiv.ofBijective f hf, ?_, ?_⟩
  · change φ (g i) = L.val
    exact ((hφ (g i) 1).2 ((hg i).trans (one_smul _ _).symm)).trans rfl
  · intro σ j
    change φ (g (σ • j)) = σ.toAlgHom.comp (φ (g j))
    exact ((hφ _ (σ * g j)).2 (by rw [hg, mul_smul, hg])).trans rfl

theorem orbitFieldTensorSplitting : OrbitFieldTensorSplitting.{u} := by
  classical
  intro F K _ _ _ _ _ L
  let f : K ⊗[F] L →ₐ[K] (L →ₐ[F] K) → K :=
    AlgHom.pi fun a => Algebra.TensorProduct.lift (AlgHom.id K K) a (fun _ _ => Commute.all _ _)
  have hf (r : K) (l : L) (a : L →ₐ[F] K) : f (r ⊗ₜ[F] l) a = r * a l := rfl
  have hsep (a b : L →ₐ[F] K) (h : a ≠ b) :
      ∃ z : K ⊗[F] L, f z a = 1 ∧ f z b = 0 := by
    obtain ⟨l, hl⟩ : ∃ l : L, a l ≠ b l := by
      by_contra! h'
      exact h (AlgHom.ext h')
    let c := (a l - b l)⁻¹
    refine ⟨c ⊗ₜ[F] l - (c * b l) ⊗ₜ[F] 1, ?_, ?_⟩
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one]
      rw [← mul_sub, inv_mul_cancel₀ (sub_ne_zero.mpr hl)]
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, sub_self]
  have hsingle (a : L →ₐ[F] K) : ∃ z : K ⊗[F] L, f z = Pi.single a 1 := by
    let s := Finset.univ.erase a
    have hne (b : s) : a ≠ b.val := (Finset.mem_erase.mp b.property).1.symm
    choose z haz hbz using fun b : s => hsep a b.val (hne b)
    refine ⟨∏ b, z b, ?_⟩
    funext b
    let ev := (Pi.evalAlgHom K (fun _ : L →ₐ[F] K => K) b).comp f
    change ev (∏ b, z b) = _
    rw [show ev (∏ b, z b) = ∏ i : s, ev (z i) from map_prod ev.toMonoidHom z Finset.univ]
    by_cases h : b = a
    · subst b
      simp only [ev, AlgHom.comp_apply, Pi.evalAlgHom_apply, haz, Finset.prod_const_one,
        Pi.single_eq_same]
    · have hb : b ∈ s := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ (⟨b, hb⟩ : s)) (hbz ⟨b, hb⟩)]
      simp [Ne.symm h]
  choose z hz using hsingle
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨∑ a, ((y a) ⊗ₜ[F] (1 : L)) * z a, ?_⟩
    funext b
    simp only [map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, hf, map_one, mul_one, hz]
    simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero] using Fintype.sum_ite_eq b y
  have hdim : finrank K (K ⊗[F] L) = finrank K ((L →ₐ[F] K) → K) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, AlgHom.card_of_splits F L K]
    intro l
    rw [← minpoly.algHom_eq L.val L.val.injective l]
    exact Normal.splits' (l : K)
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

theorem orbitTensorSplittingOnTestAlgebras : OrbitTensorSplittingOnTestAlgebras.{u} := by
  classical
  intro F K _ _ _ _ _ L U
  obtain ⟨s, hs⟩ := orbitFieldTensorSplitting L
  let e (R : TestAlgebra K) : (U.obj R) ⊗[F] L ≃ₐ[R] ((L →ₐ[F] K) → R) := by
    letI : Algebra F R := (U.obj R).algebra
    letI : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
    exact (Algebra.TensorProduct.cancelBaseChange F K R R L).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) s).trans
        (Algebra.TensorProduct.piScalarRight K R R _))
  have he (R : TestAlgebra K) (r : R) (l : L) (a : L →ₐ[F] K) :
      e R (r ⊗ₜ[F] l) a = r * algebraMap K R (a l) := by
    dsimp only [e, AlgEquiv.trans_apply]
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    change Algebra.TensorProduct.piScalarRight K R R _ (r ⊗ₜ[K] s (1 ⊗ₜ[F] l)) a = _
    rw [Algebra.TensorProduct.piScalarRight_tmul_apply, hs, one_mul, Algebra.smul_def, mul_comm]
  refine ⟨e, he, ?_⟩
  intro R S f x a
  induction x using TensorProduct.inductionOn with
  | tmul r l =>
    rw [Algebra.TensorProduct.map_tmul]
    change e S (f.hom r ⊗ₜ[F] l) a = f.hom (e R (r ⊗ₜ[F] l) a)
    rw [he, he, map_mul, f.hom.commutes]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

set_option backward.isDefEq.respectTransparency false in
theorem orbitTestAlgebraProduct : OrbitTestAlgebraProduct.{u} := by
  intro F K _ _ _ _ _ L R
  obtain ⟨split, pure, _⟩ := orbitTensorSplittingOnTestAlgebras L
  let A := (restrictTestAlgebra F K).obj R
  let T := (WeilRestriction.extendScalars F L).obj A
  let V (a : L →ₐ[F] K) := orbitTestAlgebra L a R
  let p (a : L →ₐ[F] K) := orbitTestProjection L a R
  let e := split R
  have hp (a : L →ₐ[F] K) (x : T) : (p a).hom x = e x a := by
    change _ = e x a
    induction x using TensorProduct.inductionOn with
    | tmul r l =>
      change r * algebraMap K R (a l) = e (r ⊗ₜ[F] l) a
      exact (pure R r l a).symm
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  let lift (s : Fan V) : s.pt ⟶ T := by
    let f : s.pt →+* ((L →ₐ[F] K) → R) := RingHom.pi fun a => (s.proj a).hom.toRingHom
    letI : Algebra L s.pt := s.pt.algebra
    letI : Algebra L T := T.algebra
    refine ConcreteCategory.ofHom (C := CommAlgCat L)
      ({ e.symm.toRingHom.comp f with commutes' := fun l => ?_ } : s.pt →ₐ[L] T)
    apply e.injective
    funext a
    change e (e.symm (f (algebraMap L s.pt l))) a = e (1 ⊗ₜ[F] l) a
    rw [AlgEquiv.apply_symm_apply, pure, one_mul]
    exact (s.proj a).hom.commutes l
  have hlift (s : Fan V) (x : s.pt) : e ((lift s).hom x) = fun a => (s.proj a).hom x :=
    e.apply_symm_apply _
  refine ⟨Fan.IsLimit.mk (Fan.mk T p) lift ?_ ?_⟩
  · intro s a
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (p a).hom ((lift s).hom x) = (s.proj a).hom x
    rw [hp]
    exact congrFun (hlift s x) a
  · intro s m hm
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply e.injective
    funext a
    exact (hp a (m.hom x)).symm.trans
      ((ConcreteCategory.congr_hom (hm a) x).trans (congrFun (hlift s x) a).symm)

section WeilProduct

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open WeilRestriction (extendScalars spectrumPoints)
private def productOptionIso {F I : Type u} [Field F] [Finite I] (X : Option I → SchemeOver F) :
    (∏ᶜ X) ≅ X none ⊗ (∏ᶜ fun i ↦ X (some i)) := by
  let Y := ∏ᶜ fun i ↦ X (some i)
  let p (i : Option I) : X none ⊗ Y ⟶ X i :=
    match i with
    | none => fst _ _
    | some j => snd _ _ ≫ Pi.π (fun i ↦ X (some i)) j
  refine ⟨lift (Pi.π X none) (Pi.lift fun i ↦ Pi.π X (some i)), Pi.lift p, ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    cases i <;> simp [p, Y, Category.assoc]
  · apply CartesianMonoidalCategory.hom_ext
    · simp [p, Y]
    · apply Pi.hom_ext
      intro i
      simp [p, Y]

private theorem affineTensor {F : Type u} [Field F] {A B : SchemeOver F}
    [IsAffine A.left] [IsAffine B.left] : IsAffine (A ⊗ B).left := by
  rw [Over.tensorObj_left]
  infer_instance

private theorem affineBaseChange {F K : Type u} [Field F] [Field K] [Algebra F K]
    (G : AffineAlgebraicGroup F) : IsAffine ((groupBaseChange F K).obj G.val).X.left := by
  let : IsAffine G.val.X.left := G.property.1
  change IsAffine (pullback G.val.X.hom (fieldSpecMap F K))
  infer_instance

private def productPointsEquiv {F I : Type u} [Field F] {G : I → Specs.GroupScheme F}
    [Finite I] (P : Fan G) (hP : IsLimit P) (R : TestAlgebra F) :
    ((groupPointsFunctor F).obj P.pt).obj R ≃*
      (∀ i, ((groupPointsFunctor F).obj (G i)).obj R) :=
  let Fg := Grp.forget (SchemeOver F)
  let h := (Fan.isLimitMapConeEquiv Fg G P) (isLimitOfPreserves Fg hP)
  { toFun := fun x i => ((groupPointsFunctor F).map (P.proj i)).app R x
    invFun := fun x => Fan.IsLimit.lift h x
    left_inv := fun _x => Fan.IsLimit.hom_ext h _ _ (fun i => Fan.IsLimit.fac h _ i)
    right_inv := fun _x => funext (fun i => Fan.IsLimit.fac h _ i)
    map_mul' := fun x y => funext fun i =>
      map_mul (((groupPointsFunctor F).map (P.proj i)).app R).hom x y }


private def groupBaseChangePointIso (F K : Type u) [Field F] [Field K] [Algebra F K]
    (G : Specs.GroupScheme F) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj G) ≅
      restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj G :=
  NatIso.ofComponents (fun R =>
    ({ toEquiv := Equiv.ofBijective (baseChangePoint F K G.X R) (baseChangePoints F K G.X R)
       map_mul' := baseChangePointsGroupLaw F K G R } :
      ((groupPointsFunctor K).obj ((groupBaseChange F K).obj G)).obj R ≃*
        ((groupPointsFunctor F).obj G).obj ((restrictTestAlgebra F K).obj R)).toGrpIso)
    (fun f => GrpCat.ext fun p => baseChangePointsNaturality F K G.X f p)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem pointsOnTestProduct {F I : Type u} [Field F] (X : SchemeOver F)
    (hX : IsAffine X.left)
    {T : I → TestAlgebra F} (P : Fan T) (hP : IsLimit P) :
    Function.Bijective (fun (x : Points X P.pt) i => mapPoints (P.proj i) x) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let C := A.unop
  let E := spectrumPoints C X e
  let t (R : TestAlgebra F) : (C ⟶ R) ≃ Points X R := (E.app R).toEquiv
  have ht {R S : TestAlgebra F} (f : R ⟶ S) (g : C ⟶ R) :
      t S (g ≫ f) = mapPoints f (t R g) := by
    have h := congrArg (fun (p : (C ⟶ R) ⟶ Points X S) => p.hom' g)
      (E.hom.naturality f)
    exact h
  constructor
  · intro x y h
    apply (t P.pt).symm.injective
    apply Fan.IsLimit.hom_ext hP
    intro i
    apply (t (T i)).injective
    rw [ht, ht, (t P.pt).apply_symm_apply, (t P.pt).apply_symm_apply]
    exact congrFun h i
  · intro x
    let y := Fan.IsLimit.lift hP (fun i => (t (T i)).symm (x i))
    refine ⟨t P.pt y, funext fun i => ?_⟩
    change mapPoints (P.proj i) (t P.pt y) = x i
    rw [← ht, show y ≫ P.proj i = (t (T i)).symm (x i) from Fan.IsLimit.fac hP _ i,
      Equiv.apply_symm_apply]

private theorem affineOfOverIso {F : Type u} [Field F] {X Y : SchemeOver F}
    (e : X ≅ Y) (h : IsAffine Y.left) :
    IsAffine X.left := by
  let := h
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact isAffine_of_isAffineHom e.hom.left

private theorem affineFiniteProduct {F I : Type u} [Field F] [Finite I]
    (X : I → SchemeOver F) (hX : ∀ i, IsAffine (X i).left) :
    IsAffine (∏ᶜ X).left := by
  classical
  cases nonempty_fintype I
  revert X
  refine Fintype.induction_empty_option
    (P := fun I [Fintype I] => ∀ (X : I → SchemeOver F),
      (∀ i, IsAffine (X i).left) → IsAffine (∏ᶜ X).left) ?_ ?_ ?_ I
  · intro α β _ e ih X hX
    have : Finite α := Finite.of_equiv β e.symm
    exact affineOfOverIso (Pi.reindex e X).symm (ih (X ∘ e) fun i => hX (e i))
  · intro X _
    let e : (∏ᶜ X) ≅ 𝟙_ (SchemeOver F) :=
      ⟨toUnit _, Pi.lift (fun i => PEmpty.elim i),
        Pi.hom_ext _ _ (fun i => PEmpty.elim i), toUnit_unique _ _⟩
    exact affineOfOverIso e (inferInstanceAs (IsAffine (Spec (CommRingCat.of F))))
  · intro α _ ih X hX
    let := hX none
    let := ih (fun i => X (some i)) fun i => hX (some i)
    exact affineOfOverIso (productOptionIso X) affineTensor

private theorem affineGroupFiniteProduct {F I : Type u} [Field F] [Finite I]
    (X : I → Specs.GroupScheme F) (h : ∀ i, IsAffine (X i).X.left) :
    IsAffine (∏ᶜ X).X.left := by
  let U := Grp.forget (SchemeOver F)
  let p : Fan (fun i => (X i).X) := Fan.mk (∏ᶜ X).X (fun i => U.map (Pi.π X i))
  let hp : IsLimit p := (Fan.isLimitMapConeEquiv U X (Fan.mk _ (Pi.π X)))
    (isLimitOfPreserves U (limit.isLimit _))
  exact affineOfOverIso (hp.conePointUniqueUpToIso (limit.isLimit _)) (affineFiniteProduct _ h)

set_option backward.isDefEq.respectTransparency false in
private def orbitScalarProjection {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K) :
    letI : Algebra L K := a.toRingHom.toAlgebra
    restrictTestAlgebra F K ⋙ extendScalars F L ⟶ restrictTestAlgebra L K := by
  letI : Algebra L K := a.toRingHom.toAlgebra
  refine { app := orbitTestProjection L a, naturality := ?_ }
  intro R S f
  apply CommAlgCat.hom_ext
  apply DFunLike.ext
  intro x
  change (orbitTestProjection L a S).hom
    (Algebra.TensorProduct.map ((restrictTestAlgebra F K).map f).hom (AlgHom.id F L) x) =
      f.hom ((orbitTestProjection L a R).hom x)
  induction x using TensorProduct.inductionOn with
  | tmul r l =>
    rw [Algebra.TensorProduct.map_tmul]
    change f.hom r * algebraMap K S (a l) = f.hom (r * algebraMap K R (a l))
    rw [map_mul, f.hom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private def orbitRestrictionProjection {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K)
    (W : Specs.GroupScheme F) (H : Specs.GroupScheme L)
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj W) ⟶
      (groupPointsFunctor K).obj (orbitBaseChangedGroup L a H) :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  let U := restrictTestAlgebra F K
  let V := (groupPointsFunctor L).obj H
  (groupBaseChangePointIso F K W).hom ≫ Functor.whiskerLeft U e.hom ≫
    (Functor.associator U (extendScalars F L) V).inv ≫
    Functor.whiskerRight (orbitScalarProjection L a) V ≫ (groupBaseChangePointIso L K H).inv

private theorem affineOrbitBaseChange {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K) (H : AffineAlgebraicGroup L) :
    IsAffine (orbitBaseChangedGroup L a H.val).X.left :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  affineBaseChange (K := K) H

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
theorem weilRestrictionBaseChangeProduct : WeilRestrictionBaseChangeProduct.{u} := by
  classical
  intro F K _ _ _ _ _ L W H e
  let I := L →ₐ[F] K
  let T (a : I) := orbitBaseChangedGroup L a H.val
  let G := (groupBaseChange F K).obj W.val
  let V := groupPointsFunctor K
  let n (a : I) := orbitRestrictionProjection L a W.val H.val e
  have hG : IsAffine G.X.left := affineBaseChange (K := K) W
  choose p hp using fun a : I => (groupHomComparison K G (T a) hG).surjective (n a)
  have hn (R : TestAlgebra K) :
      Function.Bijective (fun (x : (V.obj G).obj R) a => (n a).app R x) := by
    obtain ⟨hR⟩ := orbitTestAlgebraProduct L R
    let q := (groupBaseChangePointIso F K W.val).app R ≪≫ e.app ((restrictTestAlgebra F K).obj R)
    let z (a : I) : ((groupPointsFunctor L).obj H.val).obj (orbitTestAlgebra L a R) ≃*
        (V.obj (T a)).obj R :=
      letI : Algebra L K := a.toRingHom.toAlgebra
      ((groupBaseChangePointIso L K H.val).app R).symm.groupIsoToMulEquiv
    have h := (MulEquiv.piCongrRight z).bijective.comp
      ((pointsOnTestProduct H.val.X H.property.1 _ hR).comp q.groupIsoToMulEquiv.bijective)
    exact h
  let Y := ∏ᶜ T
  let f : G ⟶ Y := Pi.lift p
  have hY : IsAffine Y.X.left := affineGroupFiniteProduct T (fun a => affineOrbitBaseChange L a H)
  have hf (R : TestAlgebra K) : Function.Bijective ((V.map f).app R) := by
    let j := productPointsEquiv (Fan.mk Y (Pi.π T)) (limit.isLimit _) R
    have he : (fun (x : (V.obj G).obj R) a => (n a).app R x) = j ∘ ((V.map f).app R) := by
      funext x a
      change (n a).app R x = (V.map (Pi.π T a)).app R ((V.map f).app R x)
      rw [← hp a]
      have h := NatTrans.congr_app (congrArg V.map (Pi.lift_comp_π p a)) R
      rw [Functor.map_comp, NatTrans.comp_app] at h
      exact (ConcreteCategory.congr_hom h x).symm
    exact (Equiv.comp_bijective _ j.toEquiv).mp (he ▸ hn R)
  let (R : TestAlgebra K) : IsIso ((V.map f).app R) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hf R)
  let : IsIso (V.map f) := NatIso.isIso_of_isIso_app _
  obtain ⟨g, hg⟩ := (groupHomComparison K Y G hY).surjective (inv (V.map f))
  change V.map g = inv (V.map f) at hg
  have hfg : f ≫ g = 𝟙 G := (groupHomComparison K G G hG).injective (by
    change V.map (f ≫ g) = V.map (𝟙 G)
    rw [Functor.map_comp, hg, IsIso.hom_inv_id]
    exact (V.map_id G).symm)
  have hgf : g ≫ f = 𝟙 Y := (groupHomComparison K Y Y hY).injective (by
    change V.map (g ≫ f) = V.map (𝟙 Y)
    rw [Functor.map_comp, hg, IsIso.inv_hom_id]
    exact (V.map_id Y).symm)
  let j : G ≅ Y := ⟨f, g, hfg, hgf⟩
  let : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
  refine ⟨p, ⟨Fan.IsLimit.mk (Fan.mk G p) (fun s => Pi.lift s.proj ≫ j.inv) ?_ ?_⟩, ?_⟩
  · intro s a
    change (Pi.lift s.proj ≫ j.inv) ≫ p a = s.proj a
    rw [← Pi.lift_comp_π p a]
    change (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]
  · intro s m hm
    apply (cancel_mono j.hom).mp
    apply Pi.hom_ext
    intro a
    change m ≫ f ≫ Pi.π T a = (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a
    calc
      _ = s.proj a := by
        rw [show f ≫ Pi.π T a = p a from Pi.lift_comp_π p a]
        exact hm a
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]
  · intro a R x
    let : Algebra L K := a.toRingHom.toAlgebra
    let j := (groupBaseChangePointIso L K H.val).app R
    let x₀ : (V.obj G).obj R := x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hp a) R) x₀
    change j.hom (((V.map (p a)).app R) x₀) = _
    rw [h]
    change j.hom (j.inv _) = _
    exact ConcreteCategory.congr_hom j.inv_hom_id _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
theorem weilRestrictionProjectionNaturality : WeilRestrictionProjectionNaturality.{u} := by
  intro F K _ _ _ L a V W S H f g e d p q hp hq h
  let : Algebra L K := a.toRingHom.toAlgebra
  let V' := (groupBaseChange F K).obj V.val
  let H' := orbitBaseChangedGroup L a H.val
  let f' := (groupBaseChange F K).map f
  let g' := (groupBaseChange L K).map g
  have hV : IsAffine V'.X.left := affineBaseChange (K := K) V
  apply (groupHomComparison K V' H' hV).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  change (x ≫ (f' ≫ p).hom.hom) = (x ≫ (q ≫ g').hom.hom)
  apply (baseChangePoints L K H.val.X R).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  have hright := baseChangePointsSchemeNaturality L K g.hom.hom R (x ≫ q.hom.hom)
  change orbitBaseChangePoint L a H.val R ((x ≫ f'.hom.hom) ≫ p.hom.hom) =
    orbitBaseChangePoint L a H.val R ((x ≫ q.hom.hom) ≫ g'.hom.hom)
  rw [hp, show orbitBaseChangePoint L a H.val R ((x ≫ q.hom.hom) ≫ g'.hom.hom) =
    (orbitBaseChangePoint L a S.val R (x ≫ q.hom.hom)) ≫ g.hom.hom from hright, hq]
  rw [show baseChangePoint F K W.val.X R (x ≫ f'.hom.hom) =
    baseChangePoint F K V.val.X R x ≫ f.hom.hom from baseChangePointsSchemeNaturality F K f.hom.hom R x]
  let A := (restrictTestAlgebra F K).obj R
  let x₀ : ((groupPointsFunctor F).obj V.val).obj A := baseChangePoint F K V.val.X R x
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h A) x₀
  let b := orbitTestProjection L a R
  let Y := (groupPointsFunctor L).obj H.val
  let Z := (groupPointsFunctor L).obj S.val
  let v := (groupPointsFunctor L).map g
  change e.hom.app A (x₀ ≫ f.hom.hom) = v.app _ (d.hom.app A x₀) at he
  change Y.map b (e.hom.app A (x₀ ≫ f.hom.hom)) =
    v.app _ (Z.map b (d.hom.app A x₀))
  rw [he]
  exact (ConcreteCategory.congr_hom (v.naturality b) (d.hom.app A x₀)).symm

end WeilProduct

section Stabilizer

open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)
open private standard descend_standard_hom antipode_hom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private comparison_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

private theorem projection_injective (A : ProductDescent (F := F) (K := K) (I := I))
    (i : I) : Function.Injective (A.projection i).hom := by
  classical
  let R := CommAlgCat.of K (A.factor i)
  let family (j : I) : A.factor j →ₐ[K] R := by
    by_cases h : j = i
    · subst j
      exact AlgHom.id K _
    · exact (Algebra.ofId K R).comp (Bialgebra.counitAlgHom K (A.factor j))
  have hi : family i = AlgHom.id K _ := by simp [family]
  obtain ⟨f, hf⟩ := (A.product R).surjective family
  have hleft (x : A.factor i) : f ((A.projection i).hom x) = x := by
    have h := DFunLike.congr_fun (congrFun hf i) x
    rw [hi] at h
    exact h
  exact Function.LeftInverse.injective hleft

private def stabilizerDatum (A : ProductDescent (F := F) (K := K) (I := I)) (i : I) :
    HopfDescentDatum (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i))
      (A.factor i) := by
  let J := MulAction.stabilizer Gal(K/F) i
  let L := IntermediateField.fixedField J
  let s := restrictToFixedFieldSubgroup J
  let p := (A.projection i).hom
  let act (σ : Gal(K/L)) := A.transport (s σ).val i i
    (MulAction.mem_stabilizer_iff.mp (s σ).property)
  have hp : Function.Injective p := projection_injective A i
  have hc (σ : Gal(K/L)) (x : A.factor i) :
      p (act σ x) = A.datum.action.act (s σ).val (p x) :=
    A.transportProjection _ _ _ _ _
  let a : SemilinearAction L K (A.factor i) :=
    { act := fun σ => (act σ).toAddEquiv
      one_act := fun x => hp (by
        change p (act 1 x) = p x
        rw [hc, map_one]
        exact A.datum.action.one_act _)
      mul_act := fun σ τ x => hp (by
        change p (act (σ * τ) x) = p (act σ (act τ x))
        rw [hc, hc, hc, map_mul]
        exact A.datum.action.mul_act _ _ _)
      map_smul := fun σ r x => hp (by
        change p (act σ (r • x)) = p (σ r • act σ x)
        have hsmul (k : K) (v : A.factor i) : p (k • v) = k • p v :=
          p.toLinearMap.map_smul k v
        rw [hc, hsmul, A.datum.action.map_smul, hsmul, hc]
        rfl) }
  refine ⟨a, fun σ => map_one (act σ), fun σ => map_mul (act σ), ?_, ?_, ?_⟩
  · intro σ x
    let t := TensorProduct.map p.toLinearMap p.toLinearMap
    have ht (v : A.factor i ⊗[K] A.factor i) :
        t ((a.tensor a).act σ v) =
          (A.datum.action.tensor A.datum.action).act (s σ).val (t v) := by
      induction v using TensorProduct.inductionOn with
      | tmul x y =>
        change t ((a.tensor a).act σ (x ⊗ₜ[K] y)) = _
        simp only [t, SemilinearAction.tensor_act_tmul, TensorProduct.map_tmul]
        exact congrArg₂ (TensorProduct.tmul K) (hc σ x) (hc σ y)
      | add v w hv hw => simp only [map_add, hv, hw]
    apply (TensorProduct.map_injective_of_flat_flat _ _ hp hp : Function.Injective t)
    change t (comul (R := K) (a.act σ x)) = t ((a.tensor a).act σ (comul (R := K) x))
    rw [ht]
    change _ = (A.datum.action.tensor A.datum.action).act (s σ).val
      (TensorProduct.map p.toLinearMap p.toLinearMap (comul (R := K) x))
    have hpcomul (v : A.factor i) :
        t (comul (R := K) v) = comul (R := K) (p v) :=
      CoalgHomClass.map_comp_comul_apply p v
    rw [hpcomul, hpcomul]
    change comul (R := K) (p (act σ x)) = _
    rw [hc]
    exact A.datum.comul_equivariant _ _
  · intro σ x
    change counit (R := K) (act σ x) = σ (counit (R := K) x)
    rw [← CoalgHomClass.counit_comp_apply p, hc]
    exact (A.datum.counit_equivariant (s σ).val (p x)).trans
      (congrArg σ (CoalgHomClass.counit_comp_apply p x))
  · intro σ x
    apply hp
    change p (antipode K (act σ x)) = p (act σ (antipode K x))
    rw [hc]
    change (A.projection i).hom (antipode K (act σ x)) = _
    rw [antipode_hom]
    change antipode K (p (act σ x)) = A.datum.action.act (s σ).val (p (antipode K x))
    rw [hc]
    change _ = A.datum.action.act (s σ).val ((A.projection i).hom (antipode K x))
    rw [antipode_hom]
    exact A.datum.antipode_equivariant _ _

set_option backward.isDefEq.respectTransparency false in
theorem representativeDescent : RepresentativeDescent.{u} := by
  intro F K I _ _ _ _ _ _ A i L
  letI : IsGalois L K := IsGalois.tower_top_intermediateField L
  let D := stabilizerDatum A i
  let H := descendHopf D
  exact ⟨H.algebra, H.iso, (affineDescentProperties H).1 (A.finiteType i),
    comparison_equivariant H⟩

private theorem restrict_transport {A S : ProductDescent (F := F) (K := K) (I := I)}
    (j : ProductInclusion A S) (σ : Gal(K/F)) (i l : I) (h : σ • i = l)
    (x : A.factor i) :
    (j.factor l).hom (A.transport σ i l h x) =
      S.transport σ i l h ((j.factor i).hom x) := by
  apply projection_injective S l
  have hc (i : I) (x : A.factor i) :
      j.extended.hom ((A.projection i).hom x) =
        (S.projection i).hom ((j.factor i).hom x) :=
    ConcreteCategory.congr_hom (j.projected i) x
  have he (x : A.total) :
      j.extended.hom (A.datum.action.act σ x) = S.datum.action.act σ (j.extended.hom x) := by
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso A.descent.comparison.hom).surjective x
    have hcomp (z : extendedHopf K A.descent.coordinate) :
        j.extended.hom (A.descent.comparison.hom.hom z) =
          S.descent.comparison.hom.hom ((extendedHopfMap K j.ground).hom z) :=
      ConcreteCategory.congr_hom j.compared z
    change j.extended.hom (A.datum.action.act σ (A.descent.comparison.hom.hom y)) =
      S.datum.action.act σ (j.extended.hom (A.descent.comparison.hom.hom y))
    rw [← A.descent.equivariant, hcomp, hcomp, ← S.descent.equivariant]
    exact congrArg S.descent.comparison.hom.hom
      (SemilinearAction.scalarExtension_equivariant (K := K) j.ground.hom.toLinearMap σ y)
  rw [← hc, A.transportProjection, he, hc, S.transportProjection]

set_option backward.isDefEq.respectTransparency false in
theorem representativeInclusionDescent : RepresentativeInclusionDescent.{u} := by
  intro F K I _ _ _ _ _ _ A S j i L H D e d he hd
  letI : IsGalois L K := IsGalois.tower_top_intermediateField L
  let f := e.hom ≫ j.factor i ≫ d.inv
  have hf : (standard K H).Equivariant (standard K D) f := by
    intro σ x
    let s := restrictToFixedFieldSubgroup (MulAction.stabilizer Gal(K/F) i) σ
    let hs := MulAction.mem_stabilizer_iff.mp s.property
    have hc := restrict_transport j s.val i i hs (e.hom.hom x)
    apply (ConcreteCategory.bijective_of_isIso d.hom).injective
    change d.hom.hom (d.inv.hom ((j.factor i).hom
      (e.hom.hom ((SemilinearAction.scalarExtension H).act σ x)))) =
      d.hom.hom ((SemilinearAction.scalarExtension D).act σ
        (d.inv.hom ((j.factor i).hom (e.hom.hom x))))
    have hi (y : S.factor i) : d.hom.hom (d.inv.hom y) = y :=
      ConcreteCategory.congr_hom d.inv_hom_id y
    rw [hi, he σ x, hd σ, hi]
    exact hc
  obtain ⟨g, hg⟩ := descend_standard_hom f hf
  refine ⟨g, ?_, ?_⟩
  · apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective L K g.hom.toLinearMap).mp
    have hs : Function.Surjective f.hom :=
      (ConcreteCategory.bijective_of_isIso d.inv).surjective.comp
        ((j.closed i).comp (ConcreteCategory.bijective_of_isIso e.hom).surjective)
    rw [← hg] at hs
    exact hs
  · rw [hg]
    simp [f]

end Stabilizer

section RepresentativeProjection

open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)
open private standard descend_standard_hom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable (L : IntermediateField F K)

private theorem scalarTower_action (B : HopfAlgebraCategory F)
    (σ : Gal(K/L)) (x : extendedHopf K (extendedHopf L B)) :
    (scalarTowerIso B).hom.hom
      ((SemilinearAction.scalarExtension (k := L) (K := K) (extendedHopf L B)).act σ x) =
      (SemilinearAction.scalarExtension (k := F) (K := K) B).act (σ.restrictScalars F)
        ((scalarTowerIso B).hom.hom x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r y =>
    induction y using TensorProduct.inductionOn with
    | tmul l b =>
      change (l • σ r) ⊗ₜ[F] b = σ (l • r) ⊗ₜ[F] b
      rw [map_smul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
theorem representativeProjectionDescent : RepresentativeProjectionDescent.{u} := by
  intro F K I _ _ _ _ _ _ A i L H e he
  letI : IsGalois L K := IsGalois.tower_top_intermediateField L
  let B := A.descent.coordinate
  let t : extendedHopf K (extendedHopf L B) ≅ A.total :=
    scalarTowerIso B ≪≫ A.descent.comparison
  have ht (σ : Gal(K/L)) (x : extendedHopf K (extendedHopf L B)) :
      t.hom.hom ((SemilinearAction.scalarExtension (extendedHopf L B)).act σ x) =
        A.datum.action.act (σ.restrictScalars F) (t.hom.hom x) := by
    change A.descent.comparison.hom.hom ((scalarTowerIso B).hom.hom
      ((SemilinearAction.scalarExtension (extendedHopf L B)).act σ x)) = _
    rw [scalarTower_action, A.descent.equivariant]
    rfl
  let f := e.hom ≫ A.projection i ≫ t.inv
  have hf : (standard K H).Equivariant (standard K (extendedHopf L B)) f := by
    intro σ x
    let s := restrictToFixedFieldSubgroup (MulAction.stabilizer Gal(K/F) i) σ
    have hs : s.val = σ.restrictScalars F := rfl
    apply (ConcreteCategory.bijective_of_isIso t.hom).injective
    change t.hom.hom (t.inv.hom ((A.projection i).hom
      (e.hom.hom ((SemilinearAction.scalarExtension H).act σ x)))) =
      t.hom.hom ((SemilinearAction.scalarExtension (extendedHopf L B)).act σ
        (t.inv.hom ((A.projection i).hom (e.hom.hom x))))
    have hi (y : A.total) : t.hom.hom (t.inv.hom y) = y :=
      ConcreteCategory.congr_hom t.inv_hom_id y
    rw [hi, ht, hi, he σ x]
    exact (A.transportProjection _ _ _ _ _).trans (congrArg
      (fun τ => A.datum.action.act τ ((A.projection i).hom (e.hom.hom x))) hs)
  obtain ⟨g, hg⟩ := descend_standard_hom f hf
  refine ⟨g, ?_⟩
  rw [hg]
  change e.hom ≫ A.projection i = (e.hom ≫ A.projection i ≫ t.inv) ≫ t.hom
  simp [Category.assoc]

end RepresentativeProjection

section CoordinateProjections

open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

set_option backward.isDefEq.respectTransparency false in
theorem splitRepresentativeProjectionFormula : SplitRepresentativeProjectionFormula.{u} := by
  intro F K I _ _ _ _ _ _ A i L H e g hg σ j h R x
  let B := A.descent.coordinate
  let y := groundCoordinatePoint A x
  let a := σ.toAlgHom.comp L.val
  let T := (extendScalars F L).obj ((restrictTestAlgebra F K).obj R)
  let V := orbitTestAlgebra L a R
  letI : Algebra L T := T.algebra
  letI : Algebra L V := V.algebra
  let ev := (orbitTestProjection L a R).hom
  change ev.comp (representativeEvaluation L g y) =
    componentAtEmbedding A e σ h (x.comp (A.projection j).hom.toAlgHom)
  apply AlgHom.ext
  intro z
  change ev ((Algebra.TensorProduct.commRight F L ((restrictTestAlgebra F K).obj R))
      (Algebra.TensorProduct.map (AlgHom.id L L) y (g.hom z))) =
    x ((A.projection j).hom (A.transport σ i j h (e.hom.hom (1 ⊗ₜ[L] z))))
  have hp := ConcreteCategory.congr_hom hg (1 ⊗ₜ[L] z : K ⊗[L] H)
  change (A.projection i).hom (e.hom.hom (1 ⊗ₜ[L] z)) =
    A.descent.comparison.hom.hom ((scalarTowerIso B).hom.hom (1 ⊗ₜ[L] g.hom z)) at hp
  rw [A.transportProjection, hp, ← A.descent.equivariant]
  generalize g.hom z = v
  induction v using TensorProduct.inductionOn with
  | add b c hb hc => simp only [TensorProduct.tmul_add, map_add, hb, hc]
  | tmul l b =>
    change ev (y b ⊗ₜ[F] l) =
      x (A.descent.comparison.hom.hom
        ((SemilinearAction.scalarExtension (k := F) (K := K) B).act σ
          ((Algebra.TensorProduct.cancelBaseChange F L K K B) (1 ⊗ₜ[L] (l ⊗ₜ[F] b)))))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    have hl : l • (1 : K) = (l : K) := by rw [Algebra.smul_def, mul_one]; rfl
    rw [hl]
    change y b * algebraMap K R (σ (l : K)) =
      (x.comp A.descent.comparison.hom.hom.toAlgHom) (σ (l : K) ⊗ₜ[F] b)
    let w := x.comp A.descent.comparison.hom.hom.toAlgHom
    change y b * algebraMap K R (σ (l : K)) = w (σ (l : K) ⊗ₜ[F] b)
    rw [show (σ (l : K) ⊗ₜ[F] b : K ⊗[F] B) =
      (algebraMap K (K ⊗[F] B) (σ (l : K))) * (1 ⊗ₜ[F] b) by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul],
      map_mul, w.commutes, mul_comm]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem componentAtEmbeddingBijective : ComponentAtEmbeddingBijective.{u} := by
  intro F K I _ _ _ _ _ _ A i L H e σ j h R
  let a := σ.toAlgHom.comp L.val
  let V := orbitTestAlgebra L a R
  letI : Algebra L V := V.algebra
  let t := A.transport σ i j h
  let b : K →ₐ[L] V :=
    { (algebraMap K R).comp σ.toRingHom with commutes' := fun _ => rfl }
  let inv (y : H →ₐ[L] V) : A.factor j →ₐ[K] R := by
    let f := Algebra.TensorProduct.lift (R := L) (S := L) b y (fun _ _ => Commute.all _ _)
    refine { f.toRingHom.comp (e.inv.hom.toAlgHom.toRingHom.comp t.symm.toRingHom) with
      commutes' := fun k => ?_ }
    have hk : t.symm (algebraMap K (A.factor j) k) =
        algebraMap K (A.factor i) (σ.symm k) := by
      apply t.injective
      rw [t.apply_symm_apply, A.transportScalar, σ.apply_symm_apply]
    change f (e.inv.hom (t.symm (algebraMap K (A.factor j) k))) = algebraMap K R k
    have he := e.inv.hom.toAlgHom.commutes (σ.symm k)
    rw [hk, show e.inv.hom (algebraMap K (A.factor i) (σ.symm k)) = _ from he, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    change algebraMap K R (σ (σ.symm k)) = _
    rw [σ.apply_symm_apply]
  have hi (v : K ⊗[L] H) : e.inv.hom (e.hom.hom v) = v :=
    ConcreteCategory.congr_hom e.hom_inv_id v
  have hj (v : A.factor i) : e.hom.hom (e.inv.hom v) = v :=
    ConcreteCategory.congr_hom e.inv_hom_id v
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inv, ?_, ?_⟩
  · intro x
    apply AlgHom.ext
    intro v
    let f := Algebra.TensorProduct.lift (R := L) (S := L) b (componentAtEmbedding A e σ h x)
      (fun _ _ => Commute.all _ _)
    have heq (w : K ⊗[L] H) : f w = x (t (e.hom.hom w)) := by
      induction w using TensorProduct.inductionOn with
      | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul k z =>
        change (show R from b k) * x (t (e.hom.hom (1 ⊗ₜ[L] z))) = x (t (e.hom.hom (k ⊗ₜ[L] z)))
        have hk : (k ⊗ₜ[L] z : K ⊗[L] H) =
            algebraMap K (K ⊗[L] H) k * (1 ⊗ₜ[L] z) := by
          simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
        rw [hk, map_mul, map_mul, map_mul, show e.hom.hom (algebraMap K (K ⊗[L] H) k) = _ from e.hom.hom.toAlgHom.commutes k,
          A.transportScalar, x.commutes]
        rfl
    change f (e.inv.hom (t.symm v)) = x v
    rw [heq, hj, t.apply_symm_apply]
  · intro y
    apply AlgHom.ext
    intro z
    let f := Algebra.TensorProduct.lift (R := L) (S := L) b y (fun _ _ => Commute.all _ _)
    change f (e.inv.hom (t.symm (t (e.hom.hom (1 ⊗ₜ[L] z))))) = y z
    rw [t.symm_apply_apply, hi, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem inducedWeilSplitProjectionFormula : InducedWeilSplitProjectionFormula.{u} := by
  intro F K I _ _ _ _ _ _ A i W σ j h R x L a U T V y
  rw [W.projects U y]
  exact splitRepresentativeProjectionFormula A i W.descended.projection W.descended.projected
    σ j h R x

end CoordinateProjections

section OrbitAssembly

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open _root_.LinearAlgebraicGroups.WeilRestriction (Representation tensorMap)

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

private theorem representativeEvaluation_natural {L : IntermediateField F K}
    {R S : TestAlgebra F} {B : HopfAlgebraCategory F} {H : HopfAlgebraCategory L}
    (g : H ⟶ extendedHopf L B) (x : B →ₐ[F] R) (f : R ⟶ S) :
    (tensorMap F L f.hom).comp (representativeEvaluation L g x) =
      representativeEvaluation L g (f.hom.comp x) := by
  let t := (extendScalars F L).map f
  apply AlgHom.ext
  intro a
  change t.hom ((Algebra.TensorProduct.commRight F L R)
    (Algebra.TensorProduct.map (AlgHom.id L L) x (g.hom a))) =
    (Algebra.TensorProduct.commRight F L S)
      (Algebra.TensorProduct.map (AlgHom.id L L) (f.hom.comp x) (g.hom a))
  generalize g.hom a = y
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul l b => rfl

private theorem exists_weilCoordinateProjection
    (A : ProductDescent (F := F) (K := K) (I := I)) {i : I}
    (D : OrbitCoordinates A i)
    (W : Representation F (orbitField (F := F) (K := K) i)
      (CommAlgCat.of _ D.coordinate)) :
    ∃ p : W.coordinate ⟶ CommAlgCat.of F A.descent.coordinate,
      IsWeilCoordinateProjection A D W p := by
  let L := orbitField (F := F) (K := K) i
  let B := CommAlgCat.of F A.descent.coordinate
  let a : CommAlgCat.of L D.coordinate ⟶ (extendScalars F L).obj B :=
    ConcreteCategory.ofHom (representativeEvaluation L D.projection (AlgHom.id F B))
  let p : W.coordinate ⟶ B := W.points.inv.app B a
  refine ⟨p, ?_⟩
  intro R x
  have h := (W.points.hom.naturality_apply x p).symm
  change (W.points.hom.app B p) ≫ (extendScalars F L).map x =
    W.points.hom.app R (p ≫ x) at h
  have hp : W.points.hom.app B p = a := (W.points.app B).toEquiv.apply_symm_apply a
  rw [hp] at h
  rw [← h]
  exact representativeEvaluation_natural D.projection (AlgHom.id F B) x

private theorem algHomFromProduct {L : Type u} [Field L] {D : CommAlgCat.{u} L}
    {J : Type u} {S : J → CommAlgCat.{u} L} (T : Fan S) (ht : IsLimit T) :
    Function.Bijective (fun (x : D ⟶ T.pt) j => x ≫ T.proj j) := by
  constructor
  · intro x y h
    apply Fan.IsLimit.hom_ext ht
    exact congrFun h
  · intro z
    exact ⟨Fan.IsLimit.lift ht z, funext (Fan.IsLimit.fac ht z)⟩

/-- Extension of scalars detects the coproduct property of a given cocone. -/
private theorem cofan_of_testAlgebras_overExtension {O : Type u}
    {Q : O → TestAlgebra F} {P : TestAlgebra F} (p : ∀ o, Q o ⟶ P)
    (h : ∀ R : TestAlgebra K, Function.Bijective
      (fun (x : P ⟶ (restrictTestAlgebra F K).obj R) o => p o ≫ x)) :
    Nonempty (IsColimit (Cofan.mk P p)) := by
  let Y := ∐ Q
  let f : Y ⟶ P := Sigma.desc p
  have hcomp (R : TestAlgebra K) :
      Function.Bijective (fun x : P ⟶ (restrictTestAlgebra F K).obj R => f ≫ x) := by
    constructor
    · intro x y he
      apply (h R).injective
      funext o
      exact (by simpa [f, ← Category.assoc] using congrArg (fun a => Sigma.ι Q o ≫ a) he)
    · intro y
      obtain ⟨x, hx⟩ := (h R).surjective (fun o => Sigma.ι Q o ≫ y)
      refine ⟨x, ?_⟩
      apply Sigma.hom_ext
      intro o
      simpa [f, ← Category.assoc] using congrFun hx o
  let T (C : TestAlgebra F) := CommAlgCat.of K (K ⊗[F] C)
  let t := Algebra.TensorProduct.map (AlgHom.id K K) f.hom
  have hbase (R : TestAlgebra K) :
      Function.Bijective (fun x : (K ⊗[F] P) →ₐ[K] R => x.comp t) := by
    let U := (restrictTestAlgebra F K).obj R
    letI : Algebra F U := U.algebra
    letI : IsScalarTower F K U := IsScalarTower.of_algebraMap_eq' rfl
    let e (C : TestAlgebra F) : (C ⟶ U) ≃ ((K ⊗[F] C) →ₐ[K] R) :=
      ConcreteCategory.homEquiv.trans (Algebra.TensorProduct.liftEquivRight F K C U)
    have he (x : P ⟶ U) : (e P x).comp t = e Y (f ≫ x) := by
      apply Algebra.TensorProduct.ext_ring
      apply AlgHom.ext
      intro z
      change algebraMap K R 1 * x.hom (f.hom z) = algebraMap K R 1 * x.hom (f.hom z)
      rfl
    have hh := ((e Y).bijective.comp (hcomp R)).comp (e P).symm.bijective
    have heq : (fun x : (K ⊗[F] P) →ₐ[K] R => x.comp t) =
        (e Y) ∘ (fun x : P ⟶ U => f ≫ x) ∘ (e P).symm := by
      funext x
      change x.comp t = e Y (f ≫ (e P).symm x)
      simpa using he ((e P).symm x)
    exact heq ▸ hh
  obtain ⟨g, hg⟩ := (hbase (T Y)).surjective (AlgHom.id K (K ⊗[F] Y))
  change g.comp t = AlgHom.id K (K ⊗[F] Y) at hg
  have hg' : t.comp g = AlgHom.id K (K ⊗[F] P) := by
    apply (hbase (T P)).injective
    change (t.comp g).comp t = (AlgHom.id K (K ⊗[F] P)).comp t
    rw [AlgHom.comp_assoc, hg, AlgHom.comp_id, AlgHom.id_comp]
  have hb : Function.Bijective t := by
    refine ⟨Function.LeftInverse.injective (g := g) ?_, Function.RightInverse.surjective (g := g) ?_⟩
    · exact fun x => DFunLike.congr_fun hg x
    · exact fun x => DFunLike.congr_fun hg' x
  have hf : Function.Bijective f.hom :=
    ⟨(Module.FaithfullyFlat.lTensor_injective_iff_injective F K f.hom.toLinearMap).mp hb.1,
     (Module.FaithfullyFlat.lTensor_surjective_iff_surjective F K f.hom.toLinearMap).mp hb.2⟩
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  have hι (o : O) : Sigma.ι Q o ≫ f = p o := Sigma.ι_comp_desc p o
  refine ⟨Cofan.IsColimit.mk (Cofan.mk P p) (fun s => inv f ≫ Sigma.desc s.inj) ?_ ?_⟩
  · intro s o
    change p o ≫ inv f ≫ Sigma.desc s.inj = s.inj o
    rw [← hι, Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc]
  · intro s m hm
    apply (cancel_epi f).mp
    apply Sigma.hom_ext
    intro o
    rw [IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc, ← Category.assoc, hι]
    exact hm o

private theorem groundCoordinatePoint_bijective
    (A : ProductDescent (F := F) (K := K) (I := I)) (R : TestAlgebra K) :
    Function.Bijective (fun x : A.total →ₐ[K] R =>
      (ConcreteCategory.ofHom (groundCoordinatePoint A x) :
        CommAlgCat.of F A.descent.coordinate ⟶ (restrictTestAlgebra F K).obj R)) := by
  let B := A.descent.coordinate
  let U := (restrictTestAlgebra F K).obj R
  letI : Algebra F U := U.algebra
  letI : IsScalarTower F K U := IsScalarTower.of_algebraMap_eq' rfl
  let c := (CommHopfAlgCat.ofIso A.descent.comparison).toAlgEquiv
  let e : (A.total →ₐ[K] U) ≃ ((K ⊗[F] B) →ₐ[K] U) :=
    { toFun := fun x => x.comp c.toAlgHom
      invFun := fun x => x.comp c.symm.toAlgHom
      left_inv := fun x => AlgHom.ext fun y => congrArg x (c.apply_symm_apply y)
      right_inv := fun x => AlgHom.ext fun y => congrArg x (c.symm_apply_apply y) }
  let d := (Algebra.TensorProduct.liftEquivRight F K B U).symm.trans
    (ConcreteCategory.homEquiv (X := CommAlgCat.of F B) (Y := U)).symm
  exact (d.bijective.comp e.bijective)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem inducedCoordinateProduct : InducedCoordinateProduct.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ A O D W
  choose p hp using fun o : O => exists_weilCoordinateProjection A (D o) (W o)
  refine ⟨p, hp, cofan_of_testAlgebras_overExtension (K := K) p ?_⟩
  intro R
  let U := (restrictTestAlgebra F K).obj R
  let L (o : O) := orbitField (F := F) (K := K) o.out
  let J (o : O) := ↥(MulAction.orbit Gal(K/F) o.out)
  let V (o : O) (a : L o →ₐ[F] K) := orbitTestAlgebra (L o) a R
  let T (o : O) := CommAlgCat.of (L o) (D o).coordinate
  let B := CommAlgCat.of F A.descent.coordinate
  have htrans (o : O) (j : J o) : ∃ σ : Gal(K/F), σ • o.out = j.val :=
    MulAction.mem_orbit_iff.mp j.property
  choose σ hσ using htrans
  let a (o : O) (j : J o) := (σ o j).toAlgHom.comp (L o).val
  have ha (o : O) : Function.Bijective (a o) := by
    let J₀ := MulAction.stabilizer Gal(K/F) o.out
    let φ (s : Gal(K/F)) : L o →ₐ[F] K := s.toAlgHom.comp (L o).val
    have hφ (s t : Gal(K/F)) : φ s = φ t ↔ s • o.out = t • o.out := by
      have hJ : (L o).fixingSubgroup = J₀ := IntermediateField.fixingSubgroup_fixedField J₀
      rw [← show t⁻¹ * s ∈ J₀ ↔ s • o.out = t • o.out from by
        rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]]
      rw [← hJ, IntermediateField.mem_fixingSubgroup_iff]
      refine ⟨fun h x hx => ?_, fun h => AlgHom.ext fun x => ?_⟩
      · have hx' : s x = t x := DFunLike.congr_fun h ⟨x, hx⟩
        change t.symm (s x) = x
        rw [hx', t.symm_apply_apply]
      · have hx := h x.val x.property
        change t.symm (s x.val) = x.val at hx
        exact (t.apply_symm_apply _).symm.trans (congrArg t hx)
    constructor
    · intro j j' h
      apply Subtype.ext
      simpa only [hσ] using (hφ (σ o j) (σ o j')).mp h
    · intro e
      obtain ⟨s₀, hs₀⟩ := IntermediateField.exists_algHom_of_splits
        (fun x : K => ⟨IsGalois.integral F x, IsGalois.splits F x⟩) e
      let s : Gal(K/F) := (algEquivEquivAlgHom F K).symm s₀
      have hs : φ s = e := (congrArg (fun b : K →ₐ[F] K => b.comp (L o).val)
        ((algEquivEquivAlgHom F K).apply_symm_apply s₀)).trans hs₀
      let j : J o := ⟨s • o.out, MulAction.mem_orbit_iff.mpr ⟨s, rfl⟩⟩
      exact ⟨j, ((hφ (σ o j) s).2 (hσ o j)).trans hs⟩
  let pointMap (o : O) (j : J o) :
      (A.factor j.val →ₐ[K] R) → (T o ⟶ V o (a o j)) := fun x =>
    ConcreteCategory.ofHom (componentAtEmbedding A (D o).comparison (σ o j) (hσ o j) x)
  have pointMap_bijective (o : O) (j : J o) : Function.Bijective (pointMap o j) :=
    (ConcreteCategory.homEquiv (X := T o) (Y := V o (a o j))).symm.bijective.comp
      (componentAtEmbeddingBijective A o.out (D o).comparison (σ o j) _ (hσ o j) R)
  let comparison (o : O) (f : (W o).coordinate ⟶ U) (j : J o) : T o ⟶ V o (a o j) :=
    (W o).points.hom.app U f ≫ orbitTestProjection (L o) (a o j) R
  have comparison_bijective (o : O) : Function.Bijective (comparison o) := by
    obtain ⟨hlim⟩ := orbitTestAlgebraProduct (L o) R
    let hh := algHomFromProduct (D := T o) _ hlim
    let e := (Equiv.piCongrLeft (fun a => T o ⟶ V o a) (Equiv.ofBijective _ (ha o))).symm
    exact e.bijective.comp (hh.comp ((W o).points.app U).toEquiv.bijective)
  let reindex := (MulAction.selfEquivSigmaOrbits Gal(K/F) I).symm
  let t : (∀ i, A.factor i →ₐ[K] R) ≃ (∀ o (j : J o), A.factor j.val →ₐ[K] R) :=
    (Equiv.piCongrLeft (fun i => A.factor i →ₐ[K] R) reindex).symm.trans
      (Equiv.piCurry (fun (o : O) (j : J o) => A.factor j.val →ₐ[K] R))
  let b := Equiv.piCongrRight (fun o => Equiv.piCongrRight (fun j =>
    Equiv.ofBijective (pointMap o j) (pointMap_bijective o j)))
  let c := Equiv.piCongrRight (fun o => Equiv.ofBijective (comparison o) (comparison_bijective o))
  have hcomp : Function.Bijective (fun (x : A.total →ₐ[K] R) o =>
      comparison o (p o ≫ ConcreteCategory.ofHom (groundCoordinatePoint A x)) ) := by
    have heq : (fun (x : A.total →ₐ[K] R) o =>
          comparison o (p o ≫ ConcreteCategory.ofHom (groundCoordinatePoint A x))) =
        b ∘ t ∘ (fun (x : A.total →ₐ[K] R) i => x.comp (A.projection i).hom.toAlgHom) := by
      funext x o j
      change comparison o (p o ≫ ConcreteCategory.ofHom (groundCoordinatePoint A x)) j =
        pointMap o j (x.comp (A.projection j.val).hom.toAlgHom)
      dsimp only [comparison, pointMap]
      apply CommAlgCat.hom_ext
      let S := (extendScalars F (L o)).obj U
      letI : Algebra (L o) S := S.algebra
      letI : Algebra (L o) (V o (a o j)) := (V o (a o j)).algebra
      change (orbitTestProjection (L o) ((σ o j).toAlgHom.comp (L o).val) R).hom.comp
           ((show T o ⟶ _ from (W o).points.hom.app U
             (p o ≫ ConcreteCategory.ofHom (groundCoordinatePoint A x))).hom) = _
      rw [hp o U (ConcreteCategory.ofHom (groundCoordinatePoint A x))]
      exact splitRepresentativeProjectionFormula A o.out (D o).projection (D o).projected
        (σ o j) j.val (hσ o j) R x
    rw [heq]
    exact b.bijective.comp (t.bijective.comp (A.product R))
  have ht : Function.Bijective (fun (x : A.total →ₐ[K] R) o =>
      p o ≫ (ConcreteCategory.ofHom (groundCoordinatePoint A x) : B ⟶ U)) :=
    (Equiv.comp_bijective _ c).mp hcomp
  let e₀ := Equiv.ofBijective _ (groundCoordinatePoint_bijective A R)
  exact (Function.Bijective.of_comp_iff _ e₀.bijective).mp ht


end OrbitAssembly

section WeilGroup

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open WithConv
open WeilRestriction (Representation spectrumPoints affineSpectrum groupFromPoints groupFromPointsIso)
open private restrictConvolution restrictConvolution_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {F L : Type u} [Field F] [Field L] [Algebra F L]

private def representedWeilGroup {H : HopfAlgebraCategory L}
    (W : Representation F L (CommAlgCat.of L H)) : AffineAlgebraicGroup F :=
  let Y := affineSpectrum W.coordinate W.finiteType
  let Fh := (groupPointsFunctor L).obj (specGroup H)
  let eH := spectrumPoints (CommAlgCat.of L H) (specGroup H).X (Iso.refl _)
  let eW := spectrumPoints W.coordinate Y.val (Iso.refl _)
  let e := eW.symm ≪≫ W.points ≪≫
    Functor.isoWhiskerLeft (extendScalars F L) eH ≪≫
      Functor.associator (extendScalars F L) Fh (forget GrpCat)
  groupFromPoints Y (extendScalars F L ⋙ Fh) e

private def representedWeilIso {H : HopfAlgebraCategory L}
    (W : Representation F L (CommAlgCat.of L H)) :
    (groupPointsFunctor F).obj (representedWeilGroup W).val ≅
      extendScalars F L ⋙ (groupPointsFunctor L).obj (specGroup H) :=
  let Y := affineSpectrum W.coordinate W.finiteType
  let Fh := (groupPointsFunctor L).obj (specGroup H)
  let eH := spectrumPoints (CommAlgCat.of L H) (specGroup H).X (Iso.refl _)
  let eW := spectrumPoints W.coordinate Y.val (Iso.refl _)
  let e := eW.symm ≪≫ W.points ≪≫
    Functor.isoWhiskerLeft (extendScalars F L) eH ≪≫
      Functor.associator (extendScalars F L) Fh (forget GrpCat)
  groupFromPointsIso Y (extendScalars F L ⋙ Fh) e

private theorem spectrumPoints_apply {F : Type u} [Field F] (A R : TestAlgebra F)
    (x : A ⟶ R) :
    ((spectrumPoints A ((testSpec F).obj (op A)) (Iso.refl _)).hom.app R x).left =
      Spec.map (CommRingCat.ofHom x.hom.toRingHom) := by
  change ((testSpec F).map x.op).left ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

private theorem representedWeilIso_apply {H : HopfAlgebraCategory L}
    (W : Representation F L (CommAlgCat.of L H)) (R : TestAlgebra F)
    (x : W.coordinate ⟶ R) :
    ((representedWeilIso W).hom.app R
      ((spectrumPoints W.coordinate ((testSpec F).obj (op W.coordinate)) (Iso.refl _)).hom.app R x)).left =
      Spec.map (CommRingCat.ofHom
        (show CommAlgCat.of L H ⟶ (extendScalars F L).obj R from W.points.hom.app R x).hom.toRingHom) := by
  let Y := affineSpectrum W.coordinate W.finiteType
  let E := spectrumPoints W.coordinate Y.val (Iso.refl _)
  let D := spectrumPoints (CommAlgCat.of L H) (specGroup H).X (Iso.refl _)
  change ((D.hom.app ((extendScalars F L).obj R))
    (W.points.hom.app R (E.inv.app R (E.hom.app R x)))).left = _
  have he : E.inv.app R (E.hom.app R x) = x :=
    (E.app R).toEquiv.symm_apply_apply x
  rw [he]
  exact spectrumPoints_apply _ _ _

private theorem extensionPoint_mul {B : HopfAlgebraCategory F} (R : TestAlgebra F)
    (x y : (convolutionPoints B).obj R) :
    Algebra.TensorProduct.map (AlgHom.id L L) (x * y).ofConv =
      (toConv (Algebra.TensorProduct.map (AlgHom.id L L) x.ofConv) *
        toConv (Algebra.TensorProduct.map (AlgHom.id L L) y.ofConv)).ofConv := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro b
  let j : R →ₐ[F] L ⊗[F] R := Algebra.TensorProduct.includeRight
  let x' := toConv (Algebra.TensorProduct.map (AlgHom.id L L) x.ofConv)
  let y' := toConv (Algebra.TensorProduct.map (AlgHom.id L L) y.ofConv)
  have hm := restrictConvolution_mul x' y'
  exact DFunLike.congr_fun
    ((AlgHom.comp_convMul_distrib j x y).trans (congrArg ofConv hm).symm) b

private theorem adjointPointMap_mul {B : HopfAlgebraCategory F} {H : HopfAlgebraCategory L}
    (g : H ⟶ extendedHopf L B) (R : TestAlgebra F) (x y : (convolutionPoints B).obj R) :
    let f (z : (convolutionPoints B).obj R) :
        (convolutionPoints H).obj ((extendScalars F L).obj R) :=
      toConv (((Algebra.TensorProduct.commRight F L R).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) z.ofConv)).comp g.hom.toAlgHom)
    f (x * y) = f x * f y := by
  dsimp only
  apply ofConv_injective
  rw [extensionPoint_mul (L := L)]
  let t := (Algebra.TensorProduct.commRight F L R).toAlgHom
  let f := toConv (Algebra.TensorProduct.map (AlgHom.id L L) x.ofConv)
  let h := toConv (Algebra.TensorProduct.map (AlgHom.id L L) y.ofConv)
  change (t.comp (f * h).ofConv).comp g.hom.toAlgHom = _
  rw [AlgHom.comp_convMul_distrib]
  exact AlgHom.convMul_comp_bialgHom_distrib _ _ g.hom

end WeilGroup

section SchemeAssembly

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open WithConv
open WeilRestriction (Representation spectrumPoints)
open private isMonHom_of_affinePoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

set_option backward.isDefEq.respectTransparency false in
private theorem representedWeilProjection
    (A : ProductDescent (F := F) (K := K) (I := I)) {i : I}
    (D : OrbitCoordinates A i)
    (W : Representation F (orbitField (F := F) (K := K) i)
      (CommAlgCat.of _ D.coordinate))
    (p : W.coordinate ⟶ CommAlgCat.of F A.descent.coordinate)
    (hp : IsWeilCoordinateProjection A D W p) :
    ∃ f : specGroup A.descent.coordinate ⟶ (representedWeilGroup W).val,
      f.hom.hom = (testSpec F).map p.op := by
  let L := orbitField (F := F) (K := K) i
  let B := A.descent.coordinate
  let H := D.coordinate
  let G := (representedWeilGroup W).val
  let f : (specGroup B).X ⟶ G.X := (testSpec F).map p.op
  let b := hopfSpecPointIso B
  let h := hopfSpecPointIso H
  let w := representedWeilIso W
  have he (R : TestAlgebra F) (x : (convolutionPoints B).obj R) :
      w.hom.app R ((b.hom.app R x : Points (specGroup B).X R) ≫ f) =
        h.hom.app ((extendScalars F L).obj R)
          (toConv (representativeEvaluation L D.projection x.ofConv)) := by
    let x₀ : CommAlgCat.of F B ⟶ R := CommAlgCat.ofHom x.ofConv
    let x₁ := p ≫ x₀
    have h₁ : (b.hom.app R x : Points (specGroup B).X R) ≫ f =
        (spectrumPoints W.coordinate G.X (Iso.refl _)).hom.app R x₁ := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom x.ofConv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom p.hom.toRingHom) = _
      have hs := spectrumPoints_apply W.coordinate R x₁
      exact (Spec.map_comp _ _).symm.trans hs.symm
    rw [h₁]
    apply Over.OverMorphism.ext
    have hr := representedWeilIso_apply W R x₁
    change _ = Spec.map (CommRingCat.ofHom (representativeEvaluation L D.projection x.ofConv).toRingHom)
    refine hr.trans ?_
    have hh := hp R x₀
    change Spec.map (CommRingCat.ofHom
      (show CommAlgCat.of L H ⟶ _ from W.points.hom.app R x₁).hom.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (representativeEvaluation L D.projection x.ofConv).toRingHom)
    rw [hh]
    rfl
  have hm (R : TestAlgebra F) (x y : Points (specGroup B).X R) :
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    obtain ⟨x₀, rfl⟩ := (b.app R).groupIsoToMulEquiv.surjective x
    obtain ⟨y₀, rfl⟩ := (b.app R).groupIsoToMulEquiv.surjective y
    apply (w.app R).groupIsoToMulEquiv.injective
    change w.hom.app R ((b.hom.app R x₀ * b.hom.app R y₀ : Points (specGroup B).X R) ≫ f) =
        w.hom.app R ((b.hom.app R x₀ ≫ f) * (b.hom.app R y₀ ≫ f))
    rw [← map_mul (b.hom.app R).hom, map_mul (w.hom.app R).hom, he, he, he,
      ← map_mul (h.hom.app ((extendScalars F L).obj R)).hom]
    exact congrArg (h.hom.app ((extendScalars F L).obj R))
      (adjointPointMap_mul D.projection R x₀ y₀)
  letI : IsMonHom f := isMonHom_of_affinePoints (E := specGroup B) (G := G) f
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))) hm
  exact ⟨Grp.homMk f, rfl⟩

private theorem isLimit_of_pointwise {F O : Type u} [Field F] [Finite O]
    {G : Specs.GroupScheme F} {T : O → Specs.GroupScheme F} (p : ∀ o, G ⟶ T o)
    (hG : IsAffine G.X.left) (hT : ∀ o, IsAffine (T o).X.left)
    (hb : ∀ R : TestAlgebra F, Function.Bijective
      (fun (x : ((groupPointsFunctor F).obj G).obj R) o =>
        ((groupPointsFunctor F).map (p o)).app R x)) :
    Nonempty (IsLimit (Fan.mk G p)) := by
  let V := groupPointsFunctor F
  let Y := ∏ᶜ T
  let f : G ⟶ Y := Pi.lift p
  have hY : IsAffine Y.X.left := affineGroupFiniteProduct T hT
  have hf (R : TestAlgebra F) : Function.Bijective ((V.map f).app R) := by
    let j := productPointsEquiv (Fan.mk Y (Pi.π T)) (limit.isLimit _) R
    have he : (fun (x : (V.obj G).obj R) o => (V.map (p o)).app R x) =
        j ∘ ((V.map f).app R) := by
      funext x a
      change (V.map (p a)).app R x = (V.map (Pi.π T a)).app R ((V.map f).app R x)
      have h := NatTrans.congr_app (congrArg V.map (Pi.lift_comp_π p a)) R
      rw [Functor.map_comp, NatTrans.comp_app] at h
      exact (ConcreteCategory.congr_hom h x).symm
    exact (Equiv.comp_bijective _ j.toEquiv).mp (he ▸ hb R)
  let (R : TestAlgebra F) : IsIso ((V.map f).app R) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hf R)
  let : IsIso (V.map f) := NatIso.isIso_of_isIso_app _
  obtain ⟨g, hg⟩ := (groupHomComparison F Y G hY).surjective (inv (V.map f))
  change V.map g = inv (V.map f) at hg
  have hfg : f ≫ g = 𝟙 G := (groupHomComparison F G G hG).injective (by
    change V.map (f ≫ g) = V.map (𝟙 G)
    rw [Functor.map_comp, hg, IsIso.hom_inv_id]
    exact (V.map_id G).symm)
  have hgf : g ≫ f = 𝟙 Y := (groupHomComparison F Y Y hY).injective (by
    change V.map (g ≫ f) = V.map (𝟙 Y)
    rw [Functor.map_comp, hg, IsIso.inv_hom_id]
    exact (V.map_id Y).symm)
  let j : G ≅ Y := ⟨f, g, hfg, hgf⟩
  let : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
  refine ⟨Fan.IsLimit.mk (Fan.mk G p) (fun s => Pi.lift s.proj ≫ j.inv) ?_ ?_⟩
  · intro s a
    change (Pi.lift s.proj ≫ j.inv) ≫ p a = s.proj a
    rw [← Pi.lift_comp_π p a]
    change (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]
  · intro s m hm
    apply (cancel_mono j.hom).mp
    apply Pi.hom_ext
    intro a
    change m ≫ f ≫ Pi.π T a = (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a
    calc
      _ = s.proj a := by
        rw [show f ≫ Pi.π T a = p a from Pi.lift_comp_π p a]
        exact hm a
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]

end SchemeAssembly

section InducedProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open WeilRestriction (Representation spectrumPoints)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
theorem inducedWeilProduct : InducedWeilProduct.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ A O
  let L (o : O) := orbitField (F := F) (K := K) o.out
  choose H e hH he using fun o : O => representativeDescent A o.out
  choose g hg using fun o : O => representativeProjectionDescent A o.out (he o)
  let D (o : O) : OrbitCoordinates A o.out := ⟨H o, hH o, e o, he o, g o, hg o⟩
  let W (o : O) : Representation F (L o) (CommAlgCat.of _ (H o)) := by
    letI : Algebra.FiniteType (L o) (H o) := hH o
    exact WeilRestriction.ofBasis (Module.Free.chooseBasis F (L o)) (CommAlgCat.of _ (H o))
  obtain ⟨p, hp, ⟨hc⟩⟩ := inducedCoordinateProduct A D W
  choose f hf using fun o : O => representedWeilProjection A (D o) (W o) (p o) (hp o)
  let pieces (o : O) : OrbitWeilRestriction A o.out :=
    { descended := D o
      representation := W o
      restriction := representedWeilGroup (W o)
      coordinateIso := Iso.refl _
      weil := representedWeilIso (W o)
      represents := fun R x => by
        have h := representedWeilIso_apply (W o) R x
        have ht : (spectrumPoints (W o).coordinate ((testSpec F).obj (op (W o).coordinate))
            (Iso.refl _)).hom.app R x = (testSpec F).map x.op :=
          Over.OverMorphism.ext (spectrumPoints_apply (W o).coordinate R x)
        rw [ht] at h
        simpa only [Iso.refl_hom, Category.comp_id] using h
      coordinateProjection := p o
      projects := hp o
      projection := f o
      compares := (hf o).trans (Category.comp_id _).symm }
  have hlim₀ : Nonempty (IsLimit (Fan.mk (specGroup A.descent.coordinate) (fun o => (pieces o).projection))) := by
    have hAff : IsAffine (specGroup A.descent.coordinate).X.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of A.descent.coordinate)))
    apply isLimit_of_pointwise _ hAff (fun o => (pieces o).restriction.property.1)
    intro R
    let B := CommAlgCat.of F A.descent.coordinate
    let b := (spectrumPoints B (specGroup A.descent.coordinate).X (Iso.refl _)).app R
    let E (o : O) := (spectrumPoints (W o).coordinate (pieces o).restriction.val.X (Iso.refl _)).app R
    let eAll := Equiv.piCongrRight (fun o : O => (E o).toEquiv)
    have hbc : Function.Bijective (fun (x : B ⟶ R) o => p o ≫ x) := by
      constructor
      · intro x y h
        exact Cofan.IsColimit.hom_ext hc x y (congrFun h)
      · intro y
        exact ⟨Cofan.IsColimit.desc hc y, funext (Cofan.IsColimit.fac hc y)⟩
    have h := eAll.bijective.comp (hbc.comp b.toEquiv.symm.bijective)
    change Function.Bijective (fun (x : Points (specGroup A.descent.coordinate).X R) o =>
      x ≫ (f o).hom.hom)
    have hfun : (fun (x : Points (specGroup A.descent.coordinate).X R) o => x ≫ (f o).hom.hom) =
        eAll ∘ (fun (x : B ⟶ R) o => p o ≫ x) ∘ b.toEquiv.symm := by
      funext x o
      let y := b.inv x
      have hy : b.hom y = x := b.toEquiv.apply_symm_apply x
      change x ≫ (f o).hom.hom = (E o).hom (p o ≫ y)
      rw [← hy, hf]
      apply Over.OverMorphism.ext
      change ((spectrumPoints B (specGroup A.descent.coordinate).X (Iso.refl _)).hom.app R y).left ≫
        ((testSpec F).map (p o).op).left =
        ((spectrumPoints (W o).coordinate (pieces o).restriction.val.X (Iso.refl _)).hom.app R (p o ≫ y)).left
      have h₁ := spectrumPoints_apply B R y
      have h₂ := spectrumPoints_apply (W o).coordinate R (p o ≫ y)
      exact ((congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom (p o).hom.toRingHom)) h₁).trans
        (Spec.map_comp _ _).symm).trans h₂.symm
    exact hfun ▸ h
  obtain ⟨hlim⟩ := hlim₀
  let points := (productPointsEquiv _ hlim (CommAlgCat.of F F)).trans
    (MulEquiv.piCongrRight fun o => (weilFieldPointIso (pieces o).weil).groupIsoToMulEquiv)
  exact ⟨pieces, ⟨hlim⟩, points, fun _ _ => rfl⟩

end InducedProduct

set_option backward.isDefEq.respectTransparency false in
theorem productDescentFiniteType : ProductDescentFiniteType.{u} := by
  classical
  intro F K I _ _ _ _ _ A
  choose s hs using fun i : I => Subalgebra.fg_def.mp (A.finiteType i).out
  have (i : I) : Finite (s i) := (hs i).1
  let x (z : Σ i : I, s i) : A.total := (A.projection z.1).hom z.2
  let C := Algebra.adjoin K (Set.range x)
  let p (i : I) : A.factor i →ₐ[K] C := (A.projection i).hom.toAlgHom.codRestrict C (by
    have hi : Algebra.adjoin K (s i) ≤ C.comap (A.projection i).hom.toAlgHom :=
      Algebra.adjoin_le fun y hy => Algebra.subset_adjoin ⟨⟨i, y, hy⟩, rfl⟩
    rw [(hs i).2] at hi
    intro y
    exact hi (show y ∈ (⊤ : Subalgebra K (A.factor i)) from by simp))
  obtain ⟨f, hf⟩ := (A.product (CommAlgCat.of K C)).surjective p
  have hid : C.val.comp f = AlgHom.id K A.total := by
    apply (A.product (CommAlgCat.of K A.total)).injective
    funext i
    exact AlgHom.ext fun b => congrArg Subtype.val (DFunLike.congr_fun (congrFun hf i) b)
  have hC : C = ⊤ := by
    apply eq_top_iff.mpr
    intro b _
    have hb := DFunLike.congr_fun hid b
    change (f b : A.total) = b at hb
    rw [← hb]
    exact (f b).property
  have hA : Algebra.FiniteType K A.total :=
    ⟨Subalgebra.fg_def.mpr ⟨Set.range x, Set.finite_range x, hC⟩⟩
  have : Algebra.FiniteType K (K ⊗[F] A.descent.coordinate) :=
    hA.equiv (CommHopfAlgCat.ofIso A.descent.comparison.symm).toAlgEquiv
  exact ⟨hA, Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat K⟩

section ClosedProductDescent

open private standard descend_standard_hom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private comparison_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

private theorem productMapSurjective
    (A : ProductDescent (F := F) (K := K) (I := I))
    (S : SplitProduct (F := F) (K := K) (I := I)) (j : StableProductInclusion A S) :
    Function.Surjective j.extended.hom := by
  let C := j.extended.hom.toAlgHom.range
  let T := CommAlgCat.of K C
  let p (i : I) : S.factor i →ₐ[K] T := (S.projection i).hom.toAlgHom.codRestrict C (by
    intro x
    obtain ⟨y, hy⟩ := j.closed i x
    refine ⟨(A.projection i).hom y, ?_⟩
    exact (ConcreteCategory.congr_hom (j.projected i) y).trans
      (congrArg (S.projection i).hom hy))
  obtain ⟨g, hg⟩ := (S.product T).surjective p
  have hid : C.val.comp g = AlgHom.id K S.total := by
    apply (S.product (CommAlgCat.of K S.total)).injective
    funext i
    apply AlgHom.ext
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun (congrFun hg i) x)
  intro y
  obtain ⟨x, hx⟩ := (g y).property
  exact ⟨x, hx.trans (DFunLike.congr_fun hid y)⟩

set_option backward.isDefEq.respectTransparency false in
theorem stableProductDescent : StableProductDescent.{u} := by
  intro F K I _ _ _ _ _ _ A S j
  let D := descendHopf S.datum
  let d : KnownDescent S.datum := ⟨D.algebra, D.iso, comparison_equivariant D⟩
  let f := A.descent.comparison.hom ≫ j.extended ≫ d.comparison.inv
  have hf : (standard K A.descent.coordinate).Equivariant (standard K d.coordinate) f := by
    intro σ x
    apply (ConcreteCategory.bijective_of_isIso d.comparison.hom).injective
    let b := d.comparison
    change b.hom.hom (b.inv.hom (j.extended.hom (A.descent.comparison.hom.hom
      ((SemilinearAction.scalarExtension A.descent.coordinate).act σ x)))) =
      b.hom.hom ((SemilinearAction.scalarExtension d.coordinate).act σ
        (b.inv.hom (j.extended.hom (A.descent.comparison.hom.hom x))))
    have hb (y : S.total) : b.hom.hom (b.inv.hom y) = y :=
      ConcreteCategory.congr_hom b.inv_hom_id y
    rw [hb, d.equivariant, hb, A.descent.equivariant]
    exact j.equivariant σ _
  obtain ⟨g, hg⟩ := descend_standard_hom f hf
  refine ⟨d, g, ?_, ?_⟩
  · rw [hg]
    simp [f, Category.assoc]
  · have hbase : Function.Surjective (extendedHopfMap K g).hom := by
      rw [hg]
      exact (ConcreteCategory.bijective_of_isIso d.comparison.inv).surjective.comp
        ((productMapSurjective A S j).comp
          (ConcreteCategory.bijective_of_isIso A.descent.comparison.hom).surjective)
    have hs : Function.Surjective g.hom :=
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective F K g.hom.toLinearMap).mp hbase
    refine ⟨hs, ?_⟩
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom g.hom.toAlgHom.toRingHom))
    exact IsClosedImmersion.spec_of_surjective _ hs

end ClosedProductDescent

section WeilInclusion

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open WeilRestriction (Representation spectrumPoints)
open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)
open private extendedHom_injective extendedHom_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private isMonHom_of_affinePoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [MulAction Gal(K/F) I]

private theorem tower_naturality (L : IntermediateField F K) {B C : HopfAlgebraCategory F}
    (f : B ⟶ C) :
    (scalarTowerIso B).hom ≫ extendedHopfMap K f =
      extendedHopfMap K (extendedHopfMap L f) ≫ (scalarTowerIso C).hom := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  have hx (r : K) (l : L) (b : B) :
      ((scalarTowerIso B).hom ≫ extendedHopfMap K f).hom (r ⊗ₜ[L] (l ⊗ₜ[F] b)) =
        (extendedHopfMap K (extendedHopfMap L f) ≫ (scalarTowerIso C).hom).hom
          (r ⊗ₜ[L] (l ⊗ₜ[F] b)) := by
    change (l • r) ⊗ₜ[F] f.hom b = (l • r) ⊗ₜ[F] f.hom b
    rfl
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r x =>
    induction x using TensorProduct.inductionOn with
    | tmul l b => exact hx r l b
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
private theorem representative_projection_square
    {A S : ProductDescent (F := F) (K := K) (I := I)} (j : ProductInclusion A S)
    {i : I} (D : OrbitCoordinates A i) (E : OrbitCoordinates S i)
    (f : D.coordinate ⟶ E.coordinate)
    (hf : D.comparison.hom ≫ j.factor i = extendedHopfMap K f ≫ E.comparison.hom) :
    D.projection ≫ extendedHopfMap (orbitField (F := F) (K := K) i) j.ground =
      f ≫ E.projection := by
  let L := orbitField (F := F) (K := K) i
  apply extendedHom_injective (K := K)
  simp only [extendedHom_comp]
  let tA := (scalarTowerIso (L := L) (S := K) A.descent.coordinate).hom
  let tS := (scalarTowerIso (L := L) (S := K) S.descent.coordinate).hom
  let cA := A.descent.comparison.hom
  let cS := S.descent.comparison.hom
  haveI : IsIso tS := inferInstanceAs
    (IsIso (scalarTowerIso (L := L) (S := K) S.descent.coordinate).hom)
  haveI : IsIso cS := inferInstanceAs (IsIso S.descent.comparison.hom)
  apply (cancel_mono (tS ≫ cS)).mp
  have ht : extendedHopfMap K (extendedHopfMap L j.ground) ≫ tS =
      tA ≫ extendedHopfMap K j.ground := (tower_naturality L j.ground).symm
  have hE : E.comparison.hom ≫ S.projection i = extendedHopfMap K E.projection ≫ tS ≫ cS :=
    E.projected
  calc
    _ = extendedHopfMap K D.projection ≫
        (extendedHopfMap K (extendedHopfMap L j.ground) ≫ tS) ≫ cS := by
          simp only [L, Category.assoc]
    _ = (extendedHopfMap K D.projection ≫ tA ≫ cA) ≫ j.extended := by
      rw [ht]
      simp only [Category.assoc]
      rw [← j.compared]
    _ = (D.comparison.hom ≫ A.projection i) ≫ j.extended :=
      congrArg (fun x => x ≫ j.extended) D.projected.symm
    _ = (D.comparison.hom ≫ j.factor i) ≫ S.projection i := by
      simp only [Category.assoc, j.projected]
    _ = _ := by
      rw [hf]
      simp only [Category.assoc, hE]

variable {L : Type u} [Field L] [Algebra F L]
variable {H D : HopfAlgebraCategory L}

private theorem representedAlgebraMap
    (W : Representation F L (CommAlgCat.of L H))
    (V : Representation F L (CommAlgCat.of L D)) (g : H ⟶ D) :
    ∃ q : W.coordinate ⟶ V.coordinate,
      ∀ (R : TestAlgebra F) (x : V.coordinate ⟶ R),
      (show CommAlgCat.of L H ⟶ _ from W.points.hom.app R (q ≫ x)) =
        CommAlgCat.ofHom g.hom.toAlgHom ≫ V.points.hom.app R x := by
  let g₀ : CommAlgCat.of L H ⟶ CommAlgCat.of L D := CommAlgCat.ofHom g.hom.toAlgHom
  let v := V.points.hom.app V.coordinate (𝟙 V.coordinate)
  let q := W.points.inv.app V.coordinate (g₀ ≫ v)
  refine ⟨q, ?_⟩
  intro R x
  have hw := (W.points.hom.naturality_apply x q).symm
  have hv := (V.points.hom.naturality_apply x (𝟙 V.coordinate)).symm
  change W.points.hom.app V.coordinate q ≫ (extendScalars F L).map x =
    W.points.hom.app R (q ≫ x) at hw
  change v ≫ (extendScalars F L).map x = V.points.hom.app R (𝟙 _ ≫ x) at hv
  rw [Category.id_comp] at hv
  rw [← hw, show W.points.hom.app V.coordinate q = g₀ ≫ v from
    (W.points.app V.coordinate).toEquiv.apply_symm_apply _,
    Category.assoc, hv]

set_option backward.isDefEq.respectTransparency false in
private theorem representedAlgebraMap_surjective
    (W : Representation F L (CommAlgCat.of L H))
    (V : Representation F L (CommAlgCat.of L D))
    {g : H ⟶ D} (hg : Function.Surjective g.hom)
    {q : W.coordinate ⟶ V.coordinate}
    (hq : ∀ (R : TestAlgebra F) (x : V.coordinate ⟶ R),
      (show CommAlgCat.of L H ⟶ _ from W.points.hom.app R (q ≫ x)) =
        CommAlgCat.ofHom g.hom.toAlgHom ≫ V.points.hom.app R x) :
    Function.Surjective q.hom := by
  let C := q.hom.range
  let B := CommAlgCat.of F C
  let q₀ : W.coordinate ⟶ B := CommAlgCat.ofHom (q.hom.codRestrict C (fun x => ⟨x, rfl⟩))
  let j : B ⟶ V.coordinate := CommAlgCat.ofHom C.val
  let T := extendScalars F L
  let t := (T.map j).hom
  have ht : Function.Injective t :=
    TensorProduct.map_injective_of_flat_flat j.hom.toLinearMap
      (LinearMap.id : L →ₗ[F] L) Subtype.val_injective Function.injective_id
  let v : CommAlgCat.of L D ⟶ T.obj V.coordinate :=
    V.points.hom.app V.coordinate (𝟙 V.coordinate)
  let w : CommAlgCat.of L H ⟶ T.obj B := W.points.hom.app B q₀
  have he (x : H) : t (w.hom x) = v.hom (g.hom x) := by
    have h := (W.points.hom.naturality_apply j q₀).symm
    change w ≫ T.map j = W.points.hom.app V.coordinate (q₀ ≫ j) at h
    have hj : q₀ ≫ j = q := rfl
    rw [hj] at h
    have h₀ := hq V.coordinate (𝟙 _)
    change W.points.hom.app V.coordinate (q ≫ 𝟙 V.coordinate) =
      CommAlgCat.ofHom g.hom.toAlgHom ≫ v at h₀
    rw [Category.comp_id] at h₀
    exact ConcreteCategory.congr_hom (h.trans h₀) x
  have hr (x : D) : v.hom x ∈ t.range := by
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨w.hom y, he y⟩
  let U := T.obj B
  let E := T.obj V.coordinate
  letI : Algebra L U := U.algebra
  letI : Algebra L E := E.algebra
  let e := AlgEquiv.ofInjective t ht
  let v₀ : CommAlgCat.of L D ⟶ U :=
    ConcreteCategory.ofHom (e.symm.toAlgHom.comp (v.hom.codRestrict t.range hr))
  have hv : v₀ ≫ T.map j = v := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (v.hom.codRestrict t.range hr x))
  let f := V.points.inv.app B v₀
  have hf : f ≫ j = 𝟙 _ := by
    apply (V.points.app V.coordinate).toEquiv.injective
    change V.points.hom.app V.coordinate (f ≫ j) = v
    have h := V.points.hom.naturality_apply j f
    change V.points.hom.app V.coordinate (f ≫ j) = V.points.hom.app B f ≫ T.map j at h
    rw [h, show V.points.hom.app B f = v₀ from (V.points.app B).toEquiv.apply_symm_apply _, hv]
  intro z
  have hz : j.hom (f.hom z) = z := ConcreteCategory.congr_hom hf z
  exact hz ▸ (f.hom z).property

private theorem affinePoint_of_coordinates {k : Type u} [Field k]
    (A : TestAlgebra k) {X : SchemeOver k} (e : (testSpec k).obj (op A) ≅ X)
    (R : TestAlgebra k) (x : Points X R) :
    ∃ y : A ⟶ R, x = (testSpec k).map y.op ≫ e.hom := by
  obtain ⟨y, hy⟩ := (spectrumPoints A X e).app R |>.toEquiv.surjective x
  exact ⟨y, hy.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem representedInclusion
    {A S : ProductDescent (F := F) (K := K) (I := I)} {i : I}
    (W : OrbitWeilRestriction A i) (V : OrbitWeilRestriction S i)
    (g : W.descended.coordinate ⟶ V.descended.coordinate)
    (hg : Function.Surjective g.hom) :
    ∃ (q : W.representation.coordinate ⟶ V.representation.coordinate)
      (f : V.restriction.val ⟶ W.restriction.val),
      IsClosedImmersion f.hom.hom.left ∧
      f.hom.hom = V.coordinateIso.inv ≫ (testSpec F).map q.op ≫ W.coordinateIso.hom ∧
      ((groupPointsFunctor F).map f ≫ W.weil.hom =
        V.weil.hom ≫ Functor.whiskerLeft (extendScalars F (orbitField (F := F) (K := K) i))
          ((groupPointsFunctor _).map (specGroupMap g))) ∧
      ∀ (R : TestAlgebra F) (x : V.representation.coordinate ⟶ R),
        (show CommAlgCat.of _ W.descended.coordinate ⟶ _ from
          W.representation.points.hom.app R (q ≫ x)) =
          CommAlgCat.ofHom g.hom.toAlgHom ≫ V.representation.points.hom.app R x := by
  let L := orbitField (F := F) (K := K) i
  let X := V.restriction.val
  let Y := W.restriction.val
  let T := extendScalars F L
  obtain ⟨q, hq⟩ := representedAlgebraMap W.representation V.representation g
  have hsurj := representedAlgebraMap_surjective W.representation V.representation hg hq
  let f : X.X ⟶ Y.X := V.coordinateIso.inv ≫ (testSpec F).map q.op ≫ W.coordinateIso.hom
  have h (R : TestAlgebra F) (x : Points X.X R) :
      W.weil.hom.app R (x ≫ f) = (V.weil.hom.app R x : Points _ _) ≫ (specGroupMap g).hom.hom := by
    obtain ⟨y, hy⟩ := affinePoint_of_coordinates _ V.coordinateIso R x
    rw [hy]
    have hz : (((testSpec F).map y.op ≫ V.coordinateIso.hom) ≫ f) =
        (testSpec F).map (q ≫ y).op ≫ W.coordinateIso.hom := by
      simp only [f, Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Functor.map_comp_assoc, ← op_comp]
    rw [hz]
    apply Over.OverMorphism.ext
    have hW := W.represents R (q ≫ y)
    have hV := V.represents R y
    change _ = (V.weil.hom.app R ((testSpec F).map y.op ≫ V.coordinateIso.hom)).left ≫
      Spec.map (CommRingCat.ofHom g.hom.toAlgHom.toRingHom)
    rw [hW, hV, hq R y, ← Spec.map_comp]
    rfl
  have hm (R : TestAlgebra F) (p r : Points X.X R) :
      (p * r) ≫ f = (p ≫ f) * (r ≫ f) := by
    apply (W.weil.app R).groupIsoToMulEquiv.injective
    let v := ((groupPointsFunctor L).map (specGroupMap g)).app (T.obj R)
    change W.weil.hom.app R ((p * r) ≫ f) = W.weil.hom.app R ((p ≫ f) * (r ≫ f))
    rw [map_mul (W.weil.hom.app R).hom, h, h, h, map_mul (V.weil.hom.app R).hom]
    exact map_mul v.hom _ _
  letI : IsMonHom f := isMonHom_of_affinePoints (E := X) (G := Y) f V.restriction.property.1 hm
  refine ⟨q, Grp.homMk f, ?_, rfl, ?_, hq⟩
  · haveI hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom q.hom.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hsurj
    haveI : IsIso V.coordinateIso.inv.left := (Over.forget _).map_isIso _
    haveI : IsIso W.coordinateIso.hom.left := (Over.forget _).map_isIso _
    change IsClosedImmersion (V.coordinateIso.inv.left ≫
      Spec.map (CommRingCat.ofHom q.hom.toRingHom) ≫ W.coordinateIso.hom.left)
    infer_instance
  · apply NatTrans.ext
    funext R
    exact GrpCat.ext (h R)

set_option backward.isDefEq.respectTransparency false in
private theorem projection_inclusion_square
    {A S : ProductDescent (F := F) (K := K) (I := I)} (j : ProductInclusion A S) {i : I}
    (W : OrbitWeilRestriction A i) (V : OrbitWeilRestriction S i)
    (g : W.descended.coordinate ⟶ V.descended.coordinate)
    (hg : W.descended.comparison.hom ≫ j.factor i =
      extendedHopfMap K g ≫ V.descended.comparison.hom)
    (q : W.representation.coordinate ⟶ V.representation.coordinate)
    (f : V.restriction.val ⟶ W.restriction.val)
    (hf : f.hom.hom = V.coordinateIso.inv ≫ (testSpec F).map q.op ≫ W.coordinateIso.hom)
    (hq : ∀ (R : TestAlgebra F) (x : V.representation.coordinate ⟶ R),
        (show CommAlgCat.of _ W.descended.coordinate ⟶ _ from
          W.representation.points.hom.app R (q ≫ x)) =
          CommAlgCat.ofHom g.hom.toAlgHom ≫ V.representation.points.hom.app R x) :
    specGroupMap j.ground ≫ W.projection = V.projection ≫ f := by
  let L := orbitField (F := F) (K := K) i
  let B := CommAlgCat.of F S.descent.coordinate
  let a : CommAlgCat.of F A.descent.coordinate ⟶ B := CommAlgCat.ofHom j.ground.hom.toAlgHom
  have hc : W.coordinateProjection ≫ a = q ≫ V.coordinateProjection := by
    apply (W.representation.points.app B).toEquiv.injective
    apply CommAlgCat.hom_ext
    have hW := W.projects B a
    have hV := V.projects B (𝟙 B)
    rw [Category.comp_id] at hV
    change (show CommAlgCat.of L W.descended.coordinate ⟶ _ from
      W.representation.points.hom.app B (W.coordinateProjection ≫ a)).hom =
      (show CommAlgCat.of L W.descended.coordinate ⟶ _ from
      W.representation.points.hom.app B (q ≫ V.coordinateProjection)).hom
    rw [hW, hq]
    apply AlgHom.ext
    intro z
    have hh := ConcreteCategory.congr_hom
      (representative_projection_square j W.descended V.descended g hg) z
    change (extendedHopfMap L j.ground).hom (W.descended.projection.hom z) =
      V.descended.projection.hom (g.hom z) at hh
    have ht : (CommAlgCat.Hom.hom (V.representation.points.hom.app B V.coordinateProjection))
        (g.hom z) =
      representativeEvaluation L V.descended.projection (AlgHom.id F B) (g.hom z) :=
      DFunLike.congr_fun hV (g.hom z)
    change representativeEvaluation L W.descended.projection a.hom z =
      (CommAlgCat.Hom.hom (V.representation.points.hom.app B V.coordinateProjection)) (g.hom z)
    rw [ht]
    change (Algebra.TensorProduct.commRight F L B)
        (Algebra.TensorProduct.map (AlgHom.id L L) a.hom (W.descended.projection.hom z)) =
      (Algebra.TensorProduct.commRight F L B)
        (Algebra.TensorProduct.map (AlgHom.id L L) (AlgHom.id F B)
          (V.descended.projection.hom (g.hom z)))
    rw [← hh, Algebra.TensorProduct.map_id]
    rfl
  apply Grp.hom_ext
  change (testSpec F).map a.op ≫ W.projection.hom.hom =
    V.projection.hom.hom ≫ f.hom.hom
  rw [W.compares, V.compares, hf, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← op_comp, ← op_comp, hc]

private theorem weilFieldPoints_natural {E : Type u} [Field E] [Algebra F E]
    {V W : Specs.GroupScheme F} {D H : Specs.GroupScheme E} (f : V ⟶ W) (g : D ⟶ H)
    (d : (groupPointsFunctor F).obj V ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj D)
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj H)
    (h : (groupPointsFunctor F).map f ≫ e.hom =
      d.hom ≫ Functor.whiskerLeft (extendScalars F E) ((groupPointsFunctor E).map g)) :
    ((groupPointsFunctor F).map f).app (CommAlgCat.of F F) ≫ (weilFieldPointIso e).hom =
      (weilFieldPointIso d).hom ≫ ((groupPointsFunctor E).map g).app (CommAlgCat.of E E) := by
  have hn := NatTrans.congr_app h (CommAlgCat.of F F)
  let R := CommAlgCat.of F F
  let a := (scalarExtensionOfGroundField (F := F) E).hom
  change ((groupPointsFunctor F).map f).app R ≫ e.hom.app R =
    d.hom.app R ≫ ((groupPointsFunctor E).map g).app ((extendScalars F E).obj R) at hn
  change ((groupPointsFunctor F).map f).app R ≫ e.hom.app R ≫ ((groupPointsFunctor E).obj H).map a =
    (d.hom.app R ≫ ((groupPointsFunctor E).obj D).map a) ≫
      ((groupPointsFunctor E).map g).app (CommAlgCat.of E E)
  rw [← Category.assoc, hn, Category.assoc, Category.assoc, ((groupPointsFunctor E).map g).naturality]

private theorem range_under_product_equiv {O X Y : Type u} {P Q : O → Type u}
    (eX : X ≃ (∀ o, P o)) (eY : Y ≃ (∀ o, Q o))
    (f : X → Y) (g : ∀ o, P o → Q o)
    (h : ∀ x o, eY (f x) o = g o (eX x o)) (y : Y) :
    y ∈ Set.range f ↔ ∀ o, eY y o ∈ Set.range (g o) := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ o
    exact ⟨eX x o, (h x o).symm⟩
  · intro hmem
    choose x hx using hmem
    refine ⟨eX.symm x, eY.injective (funext fun o => ?_)⟩
    rw [h, eX.apply_symm_apply]
    exact hx o

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
theorem inducedWeilProductInclusions : InducedWeilProductInclusions.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ A S j O W V
  choose g hg hgK using fun o : O => representativeInclusionDescent j o.out
    (W o).descended.equivariant (V o).descended.equivariant
  choose q f hclosed hf hnat hq using fun o : O => representedInclusion (W o) (V o) (g o) (hg o)
  have hsq (o : O) : specGroupMap j.ground ≫ (W o).projection = (V o).projection ≫ f o :=
    projection_inclusion_square j (W o) (V o) (g o) (hgK o) (q o) (f o) (hf o) (hq o)
  let R := CommAlgCat.of F F
  let L (o : O) := orbitField (F := F) (K := K) o.out
  let i := ((groupPointsFunctor F).map (specGroupMap j.ground)).app R
  let j₀ (o : O) := ((groupPointsFunctor (L o)).map (specGroupMap (g o))).app
    (CommAlgCat.of (L o) (L o))
  have hpt (o : O) : i ≫ orbitFieldProjection (W o) = orbitFieldProjection (V o) ≫ j₀ o := by
    let fw := ((groupPointsFunctor F).map (W o).projection).app R
    let fv := ((groupPointsFunctor F).map (V o).projection).app R
    let fi := ((groupPointsFunctor F).map (f o)).app R
    have hh := congrArg (fun m => (groupPointsFunctor F).map m) (hsq o)
    rw [Functor.map_comp, Functor.map_comp] at hh
    have h₁ : i ≫ fw = fv ≫ fi := NatTrans.congr_app hh R
    have h₂ : fi ≫ (weilFieldPointIso (W o).weil).hom =
        (weilFieldPointIso (V o).weil).hom ≫ j₀ o :=
      weilFieldPoints_natural (f o) (specGroupMap (g o)) (V o).weil (W o).weil (hnat o)
    change i ≫ fw ≫ (weilFieldPointIso (W o).weil).hom =
      (fv ≫ (weilFieldPointIso (V o).weil).hom) ≫ j₀ o
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  refine ⟨g, f, fun o => ⟨hg o, hclosed o, hgK o, hsq o, hnat o⟩, hpt, ?_⟩
  intro hW hV x
  let pw := (productPointsEquiv _ hW R).trans
    (MulEquiv.piCongrRight fun o => (weilFieldPointIso (W o).weil).groupIsoToMulEquiv)
  let pv := (productPointsEquiv _ hV R).trans
    (MulEquiv.piCongrRight fun o => (weilFieldPointIso (V o).weil).groupIsoToMulEquiv)
  change x ∈ Set.range i ↔ ∀ o, pw x o ∈ Set.range (j₀ o)
  exact range_under_product_equiv pv.toEquiv pw.toEquiv i (fun o y => j₀ o y)
    (fun y o => ConcreteCategory.congr_hom (hpt o) y) x


end WeilInclusion

end
end LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
