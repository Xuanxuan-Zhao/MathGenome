import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedAffineBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.TensorResolutionComparison
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Adjunction.Limits

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace DerivedFormalization.Affine.DerivedAffineBaseChange

open NonpositiveCDGA (h0Functor h0Map ordinary ordinaryFunctor)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor)
open Specs.DerivedFormalization.Affine.TensorResolutionComparison (CoproductModel Resolution)
open Specs.DerivedFormalization.Affine.DerivedAffineBaseChange

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : NonpositiveCDGA.{u,v} k} {E : CommAlgCat.{v} k}

omit [CharZero k] in
private theorem chainMap_d_apply {X Y : ModuleCochain.{u,v} k} (q : X ⟶ Y)
    (i j : ℤ) (x : X.X i) :
    q.f j (X.d i j x) = Y.d i j (q.f i x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (q.comm i j).symm) x

private theorem ordinaryHom_ext {p q : A ⟶ ordinary E}
    (h : ∀ x, p.chainMap.f 0 x = q.chainMap.f 0 x) : p = q := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.to_single_hom_ext
  exact ModuleCat.hom_ext (LinearMap.ext h)

private def homToOrdinaryComplex (r : (h0Functor k).obj A ⟶ E) :
    A.complex ⟶ (ordinary E).complex :=
  HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom (r.hom.comp A.h0Class).toLinearMap) fun i hi => by
      change i + 1 = 0 at hi
      have h : i = -1 := by omega
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change r.hom (A.h0Class (A.complex.d (-1) 0 x)) = 0
      have hx : A.h0Class (A.complex.d (-1) 0 x) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ⟨x, rfl⟩
      exact (congrArg r.hom hx).trans r.hom.map_zero

private theorem homToOrdinaryComplex_zero (r : (h0Functor k).obj A ⟶ E)
    (x : A.complex.X 0) :
    (homToOrdinaryComplex r).f 0 x = r.hom (A.h0Class x) := by
  rw [homToOrdinaryComplex, HomologicalComplex.mkHomToSingle_f]
  rfl

private def homToOrdinary (r : (h0Functor k).obj A ⟶ E) : A ⟶ ordinary E where
  chainMap := homToOrdinaryComplex r
  map_one := by
    rw [homToOrdinaryComplex_zero]
    exact (r.hom.comp A.h0Class).map_one
  map_mul i j n hn x y := by
    by_cases h : n = 0
    · subst n
      by_cases hi : i = 0
      · subst i
        have hj : j = 0 := by omega
        subst j
        simp only [homToOrdinaryComplex_zero]
        exact (r.hom.comp A.h0Class).map_mul x y
      · by_cases ip : 0 < i
        · rw [(A.nonpositive i ip).elim x 0]
          simp only [map_zero, LinearMap.zero_apply]
        · have jp : 0 < j := by omega
          rw [(A.nonpositive j jp).elim y 0]
          simp only [map_zero]
    · exact (ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k E)
          n h)).elim _ _

private def liftOrdinaryHom (q : A ⟶ ordinary E) : (h0Functor k).obj A ⟶ E :=
  CommAlgCat.ofHom <|
    Ideal.Quotient.liftₐ A.boundaryIdeal
      { toFun := fun x => q.chainMap.f 0 x
        map_one' := q.map_one
        map_mul' := q.map_mul 0 0 0 rfl
        map_zero' := map_zero (q.chainMap.f 0).hom
        map_add' := map_add (q.chainMap.f 0).hom
        commutes' := fun c => by
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
          change (q.chainMap.f 0).hom (c • A.one) = c • (ordinary E).one
          rw [map_smul, q.map_one] } (by
      rintro _ ⟨y, rfl⟩
      change q.chainMap.f 0 (A.complex.d (-1) 0 y) = 0
      rw [chainMap_d_apply]
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (ModuleCat.of k E) (-1) 0)) _)

private theorem liftOrdinaryHom_class (q : A ⟶ ordinary E) (x : A.DegreeZero) :
    (liftOrdinaryHom q).hom (A.h0Class x) = q.chainMap.f 0 x := rfl

/-- Zeroth cohomology is left adjoint to placing an algebra in degree zero. -/
private def h0Adjunction (k : Type u) [Field k] [CharZero k] :
    h0Functor.{u,v} k ⊣ ordinaryFunctor k := by
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun A E =>
        { toFun := homToOrdinary
          invFun := liftOrdinaryHom
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro r
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k A.boundaryIdeal z
    rw [liftOrdinaryHom_class]
    exact homToOrdinaryComplex_zero r x
  · intro q
    apply ordinaryHom_ext
    intro x
    exact (homToOrdinaryComplex_zero (liftOrdinaryHom q) x).trans (liftOrdinaryHom_class q x)
  · intro A' A E f g
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k A'.boundaryIdeal z
    change (liftOrdinaryHom (f ≫ g)).hom (A'.h0Class x) =
      (liftOrdinaryHom g).hom (A.h0Class (f.chainMap.f 0 x))
    exact (liftOrdinaryHom_class (f ≫ g) x).trans
      (liftOrdinaryHom_class g (f.chainMap.f 0 x)).symm
  · intro A E E' f g
    apply ordinaryHom_ext
    intro x
    change (homToOrdinaryComplex (f ≫ g)).f 0 x =
      g.hom ((homToOrdinaryComplex f).f 0 x)
    rw [homToOrdinaryComplex_zero, homToOrdinaryComplex_zero]
    rfl

private theorem tensorIsPushout {T : ModuleTensor.{u,v} k} (S : CoproductModel T)
    (f : A ⟶ B) (g : A ⟶ C) : IsPushout f g (S.inl f g) (S.inr f g) := by
  let w : CommSq f g (S.inl f g) (S.inr f g) := ⟨(S.formulas f g).base⟩
  refine IsPushout.of_isColimit' w (PushoutCocone.isColimitAux' _ fun s => ?_)
  let D := s.pt
  have h : Nonempty {t : S.tensor f g ⟶ D //
      S.inl f g ≫ t = s.inl ∧ S.inr f g ≫ t = s.inr ∧
        ∀ m : S.tensor f g ⟶ D, S.inl f g ≫ m = s.inl → S.inr f g ≫ m = s.inr →
          m = t} := by
    obtain ⟨t, ht, hu⟩ := (S.formulas f g).coproduct (D := D.toCommDGAlgebra)
      s.inl s.inr s.condition
    exact ⟨⟨t, ht.1, ht.2, fun m hm₁ hm₂ => hu m ⟨hm₁, hm₂⟩⟩⟩
  exact ⟨h.some.val, h.some.property.1, h.some.property.2.1,
    fun hm₁ hm₂ => h.some.property.2.2 _ hm₁ hm₂⟩

private theorem h0TensorIsPushout {T : ModuleTensor.{u,v} k} (S : CoproductModel T)
    (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout ((h0Functor k).map f) ((h0Functor k).map g)
      ((h0Functor k).map (S.inl f g)) ((h0Functor k).map (S.inr f g)) := by
  let : PreservesColimitsOfSize.{0, 0} (h0Functor.{u,v} k) :=
    (h0Adjunction.{u,v} k).leftAdjoint_preservesColimits
  exact (tensorIsPushout S f g).map (h0Functor k)

/-- The ordinary tensor cocone is universal for maps of ordinary k-algebras. -/
private def ordinaryTensorIsColimit (f : A ⟶ B) (g : A ⟶ C) :
    IsColimit (h0Tensor f g) := by
  letI : Algebra A.H0 B.H0 := (h0Map f).toRingHom.toAlgebra
  letI : Algebra A.H0 C.H0 := (h0Map g).toRingHom.toAlgebra
  letI : IsScalarTower k A.H0 B.H0 := IsScalarTower.of_algHom (h0Map f)
  letI : IsScalarTower k A.H0 C.H0 := IsScalarTower.of_algHom (h0Map g)
  refine PushoutCocone.isColimitAux' _ fun s => ?_
  let l := CommRingCat.ofHom s.inl.hom.toRingHom
  let r := CommRingCat.ofHom s.inr.hom.toRingHom
  have h : CommRingCat.ofHom (algebraMap A.H0 B.H0) ≫ l =
      CommRingCat.ofHom (algebraMap A.H0 C.H0) ≫ r :=
    congrArg ((forget₂ (CommAlgCat k) CommRingCat).map) s.condition
  let R := CommRingCat.pushoutCocone A.H0 B.H0 C.H0
  let H : IsColimit R := CommRingCat.pushoutCoconeIsColimit A.H0 B.H0 C.H0
  let d := PushoutCocone.IsColimit.desc H l r h
  have h₁ : R.inl ≫ d = l := PushoutCocone.IsColimit.inl_desc H l r h
  have h₂ : R.inr ≫ d = r := PushoutCocone.IsColimit.inr_desc H l r h
  let m : (h0Tensor f g).pt ⟶ s.pt := CommAlgCat.ofHom
    { d.hom with
      commutes' := fun x => by
        change d.hom ((algebraMap k B.H0 x) ⊗ₜ[A.H0] (1 : C.H0)) = algebraMap k s.pt x
        exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h₁) _).trans
          (s.inl.hom.commutes x) }
  refine ⟨m, CommAlgCat.hom_ext ?_, CommAlgCat.hom_ext ?_, fun {n} hn₁ hn₂ => ?_⟩
  · exact AlgHom.ext fun x => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h₁) x
  · exact AlgHom.ext fun x => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h₂) x
  · let F := forget₂ (CommAlgCat k) CommRingCat
    apply F.map_injective
    change F.map n = d
    apply PushoutCocone.IsColimit.hom_ext H
    · exact (congrArg F.map hn₁).trans h₁.symm
    · exact (congrArg F.map hn₂).trans h₂.symm

private theorem h0AugmentationIsIso {f : A ⟶ B} (P : Resolution f) :
    IsIso ((h0Functor k).map P.augmentation) := by
  let q := P.augmentation
  have hs (i : ℤ) : Function.Surjective (q.chainMap.f i) := P.surjective i
  have hq : Function.Bijective (h0Map q) := by
    constructor
    · apply (injective_iff_map_eq_zero (h0Map q)).2
      intro z hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k P.obj.boundaryIdeal z
      change B.h0Class (q.chainMap.f 0 x) = 0 at hz
      obtain ⟨y, hy⟩ := Ideal.Quotient.eq_zero_iff_mem.mp hz
      obtain ⟨w, hw⟩ := hs (-1) y
      let x' : P.obj.complex.X 0 := x - P.obj.complex.d (-1) 0 w
      have hx' : q.chainMap.f 0 x' = 0 := by
        change q.chainMap.f 0 (x - P.obj.complex.d (-1) 0 w) = 0
        rw [map_sub, chainMap_d_apply q.chainMap (-1) 0 w, hw, hy, sub_self]
      have hker : ∀ z : P.obj.complex.X 0, P.obj.complex.d 0 1 z = 0 →
          q.chainMap.f 0 z = 0 →
          ∃ a : P.obj.complex.X (-1),
            P.obj.complex.d (-1) 0 a = z ∧ q.chainMap.f (-1) a = 0 := by
        simpa only using!
          NonpositiveCDGA.exists_kernel_primitive q P.surjective P.quasiIso (-1)
      obtain ⟨w', hw', _⟩ := hker x' (P.obj.d_zero_apply x') hx'
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      refine ⟨w' + w, ?_⟩
      rw [map_add, hw']
      exact sub_add_cancel _ _
    · intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k B.boundaryIdeal z
      obtain ⟨w, hw⟩ := hs 0 x
      exact ⟨P.obj.h0Class w, congrArg B.h0Class hw⟩
  exact (CommAlgCat.isoMk (AlgEquiv.ofBijective (h0Map q) hq)).isIso_hom

private theorem h0Comparisons {T : ModuleTensor.{u,v} k} (S : CoproductModel T) :
    H0Comparisons S := by
  intro A B C f P g
  let H := h0Functor.{u,v} k
  let := h0AugmentationIsIso P
  let e := asIso (H.map P.augmentation)
  let l := e.inv ≫ H.map (S.inl P.base g)
  have hs : IsPushout (H.map P.base) (H.map g)
      (H.map (S.inl P.base g)) (H.map (S.inr P.base g)) :=
    h0TensorIsPushout S P.base g
  have hs' : IsPushout (H.map f) (H.map g) l (H.map (S.inr P.base g)) := by
    apply hs.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · change H.map P.base ≫ H.map P.augmentation = 𝟙 _ ≫ H.map f
      rw [Category.id_comp, ← H.map_comp, P.commutes]
    · simp
    · simp [l]
    · simp
  have ht := IsPushout.of_isColimit (ordinaryTensorIsColimit f g)
  let i := hs'.isoIsPushout _ _ ht
  have hi : IsH0Comparison S P g i := by
    constructor
    · change H.map (S.inl P.base g) ≫ i.hom = H.map P.augmentation ≫ (h0Tensor f g).inl
      calc
        _ = e.hom ≫ (l ≫ i.hom) := by simp [l]
        _ = _ := by
          rw [hs'.inl_isoIsPushout_hom _ _ ht]
          rfl
    · exact hs'.inr_isoIsPushout_hom _ _ ht
  refine ⟨i, hi, fun j hj => ?_⟩
  apply Iso.ext
  exact hs.hom_ext (hj.1.trans hi.1.symm) (hj.2.trans hi.2.symm)

private theorem h0Naturality {T : ModuleTensor.{u,v} k} (S : CoproductModel T) :
    H0Naturality S := by
  intro A B C A' B' C' f g f' g' P P' p b c t ha hl hr e e' he he'
  let H := h0Functor.{u,v} k
  let := h0AugmentationIsIso P
  have ha' : H.map p ≫ H.map P'.augmentation = H.map P.augmentation ≫ H.map b := by
    simpa only [Functor.map_comp] using congrArg H.map ha
  have hl' : H.map (S.inl P.base g) ≫ H.map t = H.map p ≫ H.map (S.inl P'.base g') := by
    simpa only [Functor.map_comp] using congrArg H.map hl
  have hr' : H.map (S.inr P.base g) ≫ H.map t = H.map c ≫ H.map (S.inr P'.base g') := by
    simpa only [Functor.map_comp] using congrArg H.map hr
  let m := e.inv ≫ H.map t ≫ e'.hom
  refine ⟨m, ?_, ?_, by simp [m, H]⟩
  · apply (cancel_epi (H.map P.augmentation)).1
    calc
      _ = H.map (S.inl P.base g) ≫ H.map t ≫ e'.hom := by
        rw [← Category.assoc, ← he.1]
        simp [m, H]
      _ = H.map p ≫ H.map (S.inl P'.base g') ≫ e'.hom := by
        simp only [← Category.assoc, hl']
      _ = _ := by rw [he'.1, ← Category.assoc, ha', Category.assoc]
  · calc
      _ = H.map (S.inr P.base g) ≫ H.map t ≫ e'.hom := by
        rw [← he.2]
        simp [m, H]
      _ = H.map c ≫ H.map (S.inr P'.base g') ≫ e'.hom := by
        simp only [← Category.assoc, hr']
      _ = _ := by rw [he'.2]

/-- The semifree tensor model for derived affine base change, with its
canonical and natural zeroth cohomology algebra isomorphism. -/
theorem derivedAffineBaseChange : BaseChange.{u,v} :=
  ⟨TensorResolutionComparison.tensorModels, fun S => ⟨h0Comparisons S, h0Naturality S⟩⟩

end

end DerivedFormalization.Affine.DerivedAffineBaseChange
