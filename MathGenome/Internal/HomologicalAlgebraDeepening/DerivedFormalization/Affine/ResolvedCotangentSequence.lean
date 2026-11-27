import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.ResolvedCotangentSequence
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeFlatness
import Batteries.Tactic.OpenPrivate
import Mathlib.Order.Sum.Order

open CategoryTheory

universe u v

namespace DerivedFormalization.Affine.ResolvedCotangentSequence

open Specs.DerivedFormalization.Affine.ResolvedCotangentSequence
open Specs.DerivedFormalization.Affine.CotangentComplex (Model localizedModel oneObject moduleClass)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor term act regular restrict restrictFunctor)
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.Derived (quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
attribute [local reducible] Derived.derivedCategory

theorem localizedTerms : LocalizedTerms.{u,v} := by
  intro k _ _ T A B C b c R S U hs X hX D W I F hB hC E hp
  letI := Derived.homotopyCategory (oneObject B) hB
  letI := Derived.homotopyCategory (oneObject C) hC
  letI := derivedCategoryInstance (oneObject B) hB
  letI := derivedCategoryInstance (oneObject C) hC
  let QC := quotient (oneObject C) hC
  let L := E.onProjective (R.module _) hp
  let H : C.Module ⥤ HomComplex.homotopyCategory (oneObject C) :=
    RightDGModule.toHomotopyCategory (oneObject C)
  let J := H ⋙ QC
  let i := (extend T S.augmentation).map F.incl
  let p := (extend T S.augmentation).map F.proj
  refine ⟨L ≪≫ J.mapIso I.left.symm, Iso.refl _, J.mapIso I.right, rfl, rfl, rfl, ?_, ?_⟩
  · change (L.hom ≫ J.map I.left.inv) ≫ J.map i ≫ 𝟙 _ = L.hom ≫ J.map (I.left.inv ≫ i)
    rw [Category.comp_id, J.map_comp, Category.assoc]
  · change J.map p ≫ J.map I.right.hom = 𝟙 _ ≫ J.map (p ≫ I.right.hom)
    rw [Category.id_comp, J.map_comp]

variable {k : Type u} [Field k] [CharZero k]
variable {A B C P Q : NonpositiveCDGA.{u,v} k}

private theorem goodTermOfSemifree (T : ModuleTensor.{u,v} k) (hT : TensorFormulas T)
    {M : B.Module} (h : IndexedSemiFree.semiFree M) : GoodTerm T M := by
  obtain ⟨F⟩ := h
  have hP := RightDGModule.SemiFreePresentation.isKProjective F
  exact ⟨⟨F⟩, hP, DerivedTensor.projectiveIsFlat T (hT (𝟙 B.toCommDGAlgebra)) hP⟩

private theorem extendedSemifree (T : ModuleTensor.{u,v} k) (hT : TensorFormulas T)
    {f : A ⟶ P} (hf : Semifree.IsSemifree A f) (O : Differentials f)
    (g : P ⟶ B) : IndexedSemiFree.semiFree ((extend T g).obj O.module) := by
  obtain ⟨_, ⟨F⟩⟩ := hf
  obtain ⟨_, _, ⟨E, _⟩, _⟩ :=
    SemifreeDifferentials.semifreeAfterBaseChange T F O (underlying g) (hT _ _)
  exact ⟨E⟩

private theorem semifreeOfIso {M N : B.Module} (e : M ≅ N)
    (h : IndexedSemiFree.semiFree M) : IndexedSemiFree.semiFree N := by
  obtain ⟨F⟩ := h
  refine ⟨{
    stage := F.stage
    bottom := F.bottom
    index := F.index
    family := F.family
    extension := F.extension
    into := fun l => F.into l ≫ e.hom
    compatible := ?_
    injective := ?_
    exhaustive := ?_ }⟩
  · intro l
    rw [← Category.assoc, F.compatible l]
  · intro l a n x y hxy
    apply F.injective l a n
    change (e.hom.app a).f n ((F.into l).app a |>.f n x) =
      (e.hom.app a).f n ((F.into l).app a |>.f n y) at hxy
    have h := CategoryTheory.congr_fun
      (congrArg (fun h : M ⟶ M => (h.app a).f n) e.hom_inv_id)
    exact (h _).symm.trans ((congrArg ((e.inv.app a).f n) hxy).trans (h _))
  · intro a n x
    obtain ⟨l, y, hy⟩ := F.exhaustive a n ((e.inv.app a).f n x)
    refine ⟨l, y, ?_⟩
    change (e.hom.app a).f n ((F.into l).app a |>.f n y) = x
    rw [hy]
    exact CategoryTheory.congr_fun
      (congrArg (fun h : N ⟶ N => (h.app a).f n) e.inv_hom_id) x

private theorem successiveModels (concat : Concatenation.{u,v}) : ResolutionsExist.{u,v} := by
  intro k _ _ A B C b c
  obtain ⟨P, f, p, hf, hfp, hps, hpq⟩ := semifreeResolution b
  let R : Model b := ⟨⟨P, f, p, hf, hfp, hps, hpq⟩, Kahler.model (underlying f)⟩
  obtain ⟨Q, g, q, hg, hgq, hqs, hqq⟩ := semifreeResolution (R.augmentation ≫ c)
  let S : Model (R.augmentation ≫ c) :=
    ⟨⟨Q, g, q, hg, hgq, hqs, hqq⟩, Kahler.model (underlying g)⟩
  exact ⟨R, S, concat f g hfp hgq, ⟨Kahler.model (underlying (f ≫ g))⟩⟩

section Graded

open Semifree
attribute [local reducible] Semifree.polynomialGradedAlgebra

/-- A degree-preserving algebra map, used for the polynomial coordinates. -/
private structure GradedMap (A B : NonpositiveCDGA.{u,v} k) where
  app : ∀ i, A.complex.X i →ₗ[k] B.complex.X i
  one : app 0 A.one = B.one
  mul (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j) :
    app n (A.mul i j n h a b) = B.mul i j n h (app i a) (app j b)

private abbrev poly (A : NonpositiveCDGA.{u,v} k) (V : Variables.{v}) :=
  polynomialGradedAlgebra A V

private def GradedMap.strict (f : A ⟶ B) : GradedMap A B :=
  ⟨fun i => (f.chainMap.f i).hom, f.map_one, f.map_mul⟩

private def GradedMap.comp (L : GradedMap A B) (M : GradedMap B C) : GradedMap A C where
  app i := (M.app i).comp (L.app i)
  one := by rw [LinearMap.comp_apply, L.one, M.one]
  mul i j n h x y := by simp only [LinearMap.comp_apply, L.mul, M.mul]

private def GradedMap.coefficient (A : NonpositiveCDGA.{u,v} k) (V : Variables.{v}) :
    GradedMap A (poly A V) where
  app i := Semifree.coefficient A V i
  one := rfl
  mul i j n h a b := (polynomialMul_coefficient A V i j n h a b).symm

private def GradedMap.lift {V : Variables.{v}} (L : GradedMap A B)
    (x : ∀ a, B.complex.X (V.degree a)) : GradedLift A V B.toCommDGAlgebra L.app x :=
  (Classical.choice (gradedUniversalProperty A V B.toCommDGAlgebra L.app L.one L.mul x)).default

private def GradedMap.ofLift {V : Variables.{v}} {L : GradedMap A B}
    {x : ∀ a, B.complex.X (V.degree a)}
    (E : GradedLift A V B.toCommDGAlgebra L.app x) : GradedMap (poly A V) B where
  app := E.component
  one := (E.map_base 0 A.one).trans L.one
  mul := E.map_mul

private def GradedMap.ofPresentation {V : Variables.{v}} {f : A ⟶ B}
    (E : Semifree.Presentation A V f) : GradedMap (poly A V) B :=
  ⟨fun i => (E.component i).toLinearMap, E.map_one, E.map_mul⟩

private def GradedMap.inversePresentation {V : Variables.{v}} {f : A ⟶ B}
    (E : Semifree.Presentation A V f) : GradedMap B (poly A V) where
  app i := (E.component i).symm.toLinearMap
  one := by
    change _ = Semifree.coefficient A V 0 A.one
    exact (E.component 0).symm_apply_eq.mpr E.map_one.symm
  mul i j n h a b := by
    apply (E.component n).injective
    change (E.component n) ((E.component n).symm (B.mul i j n h a b)) =
      (E.component n) (polynomialMul A V i j n h
        ((E.component i).symm a) ((E.component j).symm b))
    rw [E.map_mul]
    simp

private theorem GradedMap.polyExt {V : Variables.{v}} {L M : GradedMap (poly A V) B}
    (hc : ∀ i a, L.app i (Semifree.coefficient A V i a) = M.app i (Semifree.coefficient A V i a))
    (hv : ∀ x, L.app (V.degree x) (variableTerm A V x) = M.app (V.degree x) (variableTerm A V x)) :
    ∀ i y, L.app i y = M.app i y := by
  apply polynomial_generated A V (fun i y => L.app i y = M.app i y)
  · intro i
    simp
  · intro i a b ha hb
    simp only [map_add, ha, hb]
  · intro i s a ha
    simp only [LinearMap.map_smul_of_tower, ha]
  · exact hc
  · exact hv
  · intro i j n h a b ha hb
    change L.app n ((poly A V).mul i j n h a b) = _
    rw [L.mul, ha, hb, ← M.mul]

private theorem GradedMap.lift_usesOnly {V W : Variables.{v}} {L : GradedMap A (poly B W)}
    {x : ∀ a, (poly B W).complex.X (V.degree a)} (E : GradedLift A V (poly B W).toCommDGAlgebra L.app x)
    {S : Set V.Index} {U : Set W.Index} (hc : ∀ i a, UsesOnly B W U (L.app i a))
    (hv : ∀ a ∈ S, UsesOnly B W U (x a)) (i : ℤ) (p : Polynomial A V i)
    (hp : UsesOnly A V S p) : UsesOnly B W U (E.component i p) := by
  apply polynomial_generated_on A V S (fun i p => UsesOnly B W U (E.component i p)) _ _ _ _ _ _ i p hp
  · intro i
    rw [map_zero]
    exact UsesOnly.zero i
  · intro i a b ha hb
    rw [map_add]
    exact ha.add hb
  · intro i s a ha
    rw [LinearMap.map_smul_of_tower]
    exact ha.sign s
  · intro i a
    rw [E.map_base]
    exact hc i a
  · intro a ha
    rw [E.map_var]
    exact hv a ha
  · intro r s n h a b ha hb
    rw [E.map_mul]
    exact ha.mul h hb

private abbrev sumVariables (V W : Variables.{v}) : Variables.{v} where
  Index := V.Index ⊕ W.Index
  degree := Sum.elim V.degree W.degree
  nonpositive := Sum.rec V.nonpositive W.nonpositive

private abbrev sumStages {V W : Variables.{v}} (S : Stages V) (U : Stages W) :
    Stages (sumVariables V W) where
  Stage := S.Stage ⊕ₗ U.Stage
  order := inferInstance
  wellFounded := Sum.lex_wf S.wellFounded U.wellFounded
  stage := Sum.elim (fun a => Sum.inlₗ (S.stage a)) (fun b => Sum.inrₗ (U.stage b))

private structure ConcatenatedPresentation {V W : Variables.{v}}
    {f : A ⟶ P} {g : P ⟶ Q} (E : StagedPresentation A V f) (H : StagedPresentation P W g) where
  presentation : StagedPresentation A (sumVariables V W) (f ≫ g)
  left (x : V.Index) :
    presentation.component (V.degree x) (variableTerm A (sumVariables V W) (Sum.inl x)) =
      g.chainMap.f (V.degree x) (E.component (V.degree x) (variableTerm A V x))
  right (x : W.Index) :
    presentation.component (W.degree x) (variableTerm A (sumVariables V W) (Sum.inr x)) =
      H.component (W.degree x) (variableTerm P W x)

private def concatenatePresentations {V W : Variables.{v}}
    {f : A ⟶ P} {g : P ⟶ Q} (E : StagedPresentation A V f) (H : StagedPresentation P W g) :
    ConcatenatedPresentation E H := by
  let Z := sumVariables V W
  let S := sumStages E.stages H.stages
  let I := (GradedMap.coefficient A Z).lift (V := V)
    (fun x => variableTerm A Z (Sum.inl x))
  let G := (GradedMap.inversePresentation E.toPresentation).comp (GradedMap.ofLift I)
  let J := G.lift (V := W) (fun x => variableTerm A Z (Sum.inr x))
  let x : ∀ z : Z.Index, Q.complex.X (Z.degree z)
    | .inl a => g.chainMap.f (V.degree a) (E.component (V.degree a) (variableTerm A V a))
    | .inr b => H.component (W.degree b) (variableTerm P W b)
  let F := (GradedMap.strict (f ≫ g)).lift (V := Z) x
  let K := (GradedMap.inversePresentation H.toPresentation).comp (GradedMap.ofLift J)
  have hFI : ∀ i y, F.component i (I.component i y) = g.chainMap.f i (E.component i y) := by
    apply GradedMap.polyExt (L := (GradedMap.ofLift I).comp (GradedMap.ofLift F))
      (M := (GradedMap.ofPresentation E.toPresentation).comp (GradedMap.strict g))
    · intro i a
      change F.component i (I.component i (Semifree.coefficient A V i a)) = _
      rw [I.map_base]
      change F.component i (Semifree.coefficient A Z i a) = g.chainMap.f i (E.component i _)
      rw [F.map_base, E.map_base]
      rfl
    · intro a
      change F.component _ (I.component _ (variableTerm A V a)) = _
      rw [I.map_var]
      exact F.map_var (Sum.inl a)
  have hFJ : ∀ i y, F.component i (J.component i y) = H.component i y := by
    apply GradedMap.polyExt (L := (GradedMap.ofLift J).comp (GradedMap.ofLift F))
      (M := GradedMap.ofPresentation H.toPresentation)
    · intro i a
      change F.component i (J.component i (Semifree.coefficient P W i a)) = _
      rw [J.map_base]
      change F.component i (I.component i ((E.component i).symm a)) =
        H.component i (Semifree.coefficient P W i a)
      rw [hFI, LinearEquiv.apply_symm_apply, H.map_base]
    · intro a
      change F.component _ (J.component _ (variableTerm P W a)) = _
      rw [J.map_var]
      exact F.map_var (Sum.inr a)
  have hKg : ∀ i a, K.app i (g.chainMap.f i a) = I.component i ((E.component i).symm a) := by
    intro i a
    change J.component i ((H.component i).symm (g.chainMap.f i a)) = _
    rw [← H.map_base, LinearEquiv.symm_apply_apply, J.map_base]
    rfl
  have hKx : ∀ a, K.app (Z.degree a) (x a) = variableTerm A Z a := by
    intro a
    cases a with
    | inl a =>
      change K.app (V.degree a) (g.chainMap.f _ (E.component _ (variableTerm A V a))) = _
      rw [hKg, LinearEquiv.symm_apply_apply, I.map_var]
    | inr a =>
      change J.component (W.degree a) ((H.component _).symm (H.component _ (variableTerm P W a))) = _
      rw [LinearEquiv.symm_apply_apply, J.map_var]
  have hKF : ∀ i y, K.app i (F.component i y) = y := by
    let id : GradedMap (poly A Z) (poly A Z) := ⟨fun _ => LinearMap.id, rfl, fun _ _ _ _ _ _ => rfl⟩
    apply GradedMap.polyExt (L := (GradedMap.ofLift F).comp K) (M := id)
    · intro i a
      change K.app i (F.component i (Semifree.coefficient A Z i a)) = Semifree.coefficient A Z i a
      rw [F.map_base]
      change K.app i (g.chainMap.f i (f.chainMap.f i a)) = _
      rw [hKg, ← E.map_base, LinearEquiv.symm_apply_apply, I.map_base]
      rfl
    · intro a
      change K.app _ (F.component _ (variableTerm A Z a)) = variableTerm A Z a
      rw [F.map_var, hKx]
  let L (i : ℤ) : Polynomial A Z i ≃ₗ[k] Q.complex.X i :=
    LinearEquiv.ofLinearMap (F.component i) (K.app i)
      (LinearMap.ext fun y => by
        change F.component i (J.component i ((H.component i).symm y)) = y
        rw [hFJ, LinearEquiv.apply_symm_apply])
      (LinearMap.ext (hKF i))
  let Lbase : Semifree.Presentation A Z (f ≫ g) :=
    ⟨L, (GradedMap.ofLift F).one, F.map_mul, F.map_base⟩
  refine ⟨⟨Lbase, S, ?_⟩, ?_, ?_⟩
  · intro a
    change UsesOnly A Z (S.before (S.stage a)) (K.app _ (Q.complex.d _ _ (F.component _ _)))
    rw [F.map_var]
    cases a with
    | inl a =>
      change UsesOnly A Z (S.before (S.stage (Sum.inl a)))
        (K.app (V.degree a + 1)
          (Q.complex.d (V.degree a) (V.degree a + 1)
            (g.chainMap.f _ (E.component _ (variableTerm A V a)))))
      have hd := CategoryTheory.congr_fun (g.chainMap.comm (V.degree a) (V.degree a+1))
        (E.component _ (variableTerm A V a))
      simp only [ModuleCat.comp_apply] at hd
      erw [hd, hKg]
      apply GradedMap.lift_usesOnly I _ _ _ _ (E.earlier a)
      · exact fun i y => coefficient_usesOnly i y
      · intro y hy
        apply variable_usesOnly
        exact Sum.Lex.inl_lt_inl_iff.mpr hy
    | inr a =>
      change UsesOnly A Z (S.before (S.stage (Sum.inr a)))
        (J.component (W.degree a + 1)
          ((H.component _).symm (Q.complex.d (W.degree a) (W.degree a + 1)
            (H.component _ (variableTerm P W a)))))
      apply GradedMap.lift_usesOnly J _ _ _ _ (H.earlier a)
      · intro i y
        apply GradedMap.lift_usesOnly I (S := Set.univ) _ _
        · intro _ _ _ _
          exact Set.mem_univ _
        · exact fun i z => coefficient_usesOnly i z
        · intro z _
          apply variable_usesOnly
          exact Sum.Lex.inl_lt_inr _ _
      · intro y hy
        apply variable_usesOnly
        exact Sum.Lex.inr_lt_inr_iff.mpr hy
  · intro a
    exact F.map_var (Sum.inl a)
  · intro a
    exact F.map_var (Sum.inr a)

theorem concatenation : Concatenation.{u,v} := by
  intro k _ _ A P Q f g hf hg
  obtain ⟨V, ⟨E⟩⟩ := hf
  obtain ⟨W, ⟨H⟩⟩ := hg
  exact ⟨sumVariables V W, ⟨(concatenatePresentations E H).presentation⟩⟩

theorem resolutionsExist : ResolutionsExist.{u,v} :=
  successiveModels concatenation

open private shuffle mul_assoc_at from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.Tensor
open private signedLeft_regular from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

section Pushout

variable {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
variable {X : T.AlgebraCoproduct (underlying g) (underlying p)} (hX : X.Formulas)

private def pushoutCoordinates (n : ℤ) :
    Specs.DerivedFormalization.Affine.Tensor.tensorDegree (underlying p)
      (restrict (underlying g) (regular Q.toCommDGAlgebra)) (regular B.toCommDGAlgebra) n ≃ₗ[k]
      (pushout X hX).complex.X n :=
  by
    let e : term (T.obj (underlying p)
        (restrict (underlying g) (regular Q.toCommDGAlgebra)) (regular B.toCommDGAlgebra)) n
        ≃ₗ[k] (pushout X hX).complex.X n :=
      LinearEquiv.ofLinearMap (X.comparison.hom.app () |>.f n).hom
        (X.comparison.inv.app () |>.f n).hom
        (LinearMap.ext fun y => CategoryTheory.congr_fun
          (congrArg (fun z => (z.app ()).f n) X.comparison.inv_hom_id) y)
        (LinearMap.ext fun y => CategoryTheory.congr_fun
          (congrArg (fun z => (z.app ()).f n) X.comparison.hom_inv_id) y)
    exact (T.degree (underlying p) (restrict (underlying g) (regular Q.toCommDGAlgebra))
      (regular B.toCommDGAlgebra) n).trans e

private theorem pushoutExt {n : ℤ} {N : Type*} [AddCommGroup N] [Module k N]
    {L M : (pushout X hX).complex.X n →ₗ[k] N}
    (eq : ∀ i j h x y, L (X.tmul i j n h x y) = M (X.tmul i j n h x y)) : L = M := by
  let e := pushoutCoordinates hX n
  have w : L.comp e.toLinearMap = M.comp e.toLinearMap := Tensor.pure_ext (f := underlying p)
    (M := restrict (underlying g) (regular Q.toCommDGAlgebra))
    (N := regular B.toCommDGAlgebra) eq
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := e.surjective z
  exact LinearMap.congr_fun w y

private theorem pushout_factor (i j n : ℤ) (h : i+j=n)
    (x : Q.complex.X i) (y : B.complex.X j) :
    (pushout X hX).mul i j n h
      (X.inl.chainMap.f i x) (X.inr.chainMap.f j y) = X.tmul i j n h x y := by
  change X.obj.mul i j n h _ _ = _
  rw [hX.inl, hX.inr, hX.mul i 0 0 j i j n (add_zero i) (zero_add j) h,
    Int.zero_mul, Int.negOnePow_zero, one_smul]
  have w (i' j' : ℤ) (hi : i+0=i') (hj : 0+j=j') :
      X.tmul i' j' n (by omega) (Q.mul i 0 i' hi x Q.one) (B.mul 0 j j' hj B.one y) =
        X.tmul i j n h x y := by
    obtain rfl : i' = i := by omega
    obtain rfl : j' = j := by omega
    rw [Q.toDGAlgebra.comp_id, B.toDGAlgebra.id_comp]
  exact w _ _ rfl rfl

/-- The balanced graded map on a coproduct is determined by its two restrictions. -/
private def pushoutGradedDesc (r : GradedMap Q C) (s : GradedMap B C)
    (e : ∀ i a, r.app i (g.chainMap.f i a) = s.app i (p.chainMap.f i a))
    (n : ℤ) : (pushout X hX).complex.X n →ₗ[k] C.complex.X n :=
  (Tensor.liftDegree (f := underlying p)
    (M := restrict (underlying g) (regular Q.toCommDGAlgebra)) (N := regular B.toCommDGAlgebra)
    (fun i j h => ((C.mul i j n h).comp (r.app i)).compl₂ (s.app j))
    (by
      intro i l j h x a y
      change C.mul (i+l) j n h (r.app (i+l) (Q.mul i l (i+l) rfl x (g.chainMap.f l a)))
          (s.app j y) =
        C.mul i (l+j) n (by omega) (r.app i x)
          (s.app (l+j) (Specs.DerivedFormalization.Affine.Tensor.signedLeft
            (regular B.toCommDGAlgebra) l j (l+j) rfl (p.chainMap.f l a) y))
      rw [r.mul, mul_assoc_at C.toCommDGAlgebra i l j (i+l) (l+j) n rfl rfl h,
        e, signedLeft_regular, s.mul])).comp (pushoutCoordinates hX n).symm.toLinearMap

private theorem pushoutGradedDesc_pure (r : GradedMap Q C) (s : GradedMap B C)
    (e : ∀ i a, r.app i (g.chainMap.f i a) = s.app i (p.chainMap.f i a))
    (i j n : ℤ) (h : i+j=n) (x : Q.complex.X i) (y : B.complex.X j) :
    pushoutGradedDesc hX r s e n (X.tmul i j n h x y) = C.mul i j n h (r.app i x) (s.app j y) := by
  unfold pushoutGradedDesc
  rw [LinearMap.comp_apply]
  rw [show X.tmul i j n h x y = (pushoutCoordinates hX n)
    (Specs.DerivedFormalization.Affine.Tensor.pure (underlying p)
      (M := restrict (underlying g) (regular Q.toCommDGAlgebra))
      (N := regular B.toCommDGAlgebra) i j n h x y) from rfl]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  erw [Tensor.liftDegree_pure]
  rfl

private def pushoutDesc (r : GradedMap Q C) (s : GradedMap B C)
    (e : ∀ i a, r.app i (g.chainMap.f i a) = s.app i (p.chainMap.f i a)) :
    GradedMap (pushout X hX) C where
  app := pushoutGradedDesc hX r s e
  one := by
    change pushoutGradedDesc hX r s e 0 X.obj.one = C.one
    rw [hX.unit, pushoutGradedDesc_pure, r.one, s.one]
    exact C.toDGAlgebra.id_comp 0 C.one
  mul i j n h x y := by
    let L := pushoutGradedDesc hX r s e
    suffices eq : ((pushout X hX).mul i j n h).compr₂ (L n) =
        ((C.mul i j n h).comp (L i)).compl₂ (L j) from
      LinearMap.congr_fun (LinearMap.congr_fun eq x) y
    apply pushoutExt hX
    intro a b hab x₁ y₁
    apply pushoutExt hX
    intro c d hcd x₂ y₂
    change L n (X.obj.mul i j n h (X.tmul a b i hab x₁ y₁)
        (X.tmul c d j hcd x₂ y₂)) =
      C.mul i j n h (L i (X.tmul a b i hab x₁ y₁)) (L j (X.tmul c d j hcd x₂ y₂))
    rw [hX.mul a b c d i j n hab hcd h]
    simp only [Units.smul_def, map_zsmul]
    dsimp only [L]
    rw [pushoutGradedDesc_pure, pushoutGradedDesc_pure, pushoutGradedDesc_pure, r.mul, s.mul]
    subst i j
    exact (shuffle (D := C.toCommDGAlgebra) a b c d n h (r.app a x₁)
      (s.app b y₁) (r.app c x₂) (s.app d y₂)).symm

private theorem pushoutDesc_inl (r : GradedMap Q C) (s : GradedMap B C)
    (e : ∀ i a, r.app i (g.chainMap.f i a) = s.app i (p.chainMap.f i a))
    (i : ℤ) (x : Q.complex.X i) :
    (pushoutDesc hX r s e).app i (X.inl.chainMap.f i x) = r.app i x := by
  change pushoutGradedDesc hX r s e i _ = _
  rw [hX.inl, pushoutGradedDesc_pure, s.one]
  exact C.toDGAlgebra.comp_id i _

private theorem pushoutDesc_inr (r : GradedMap Q C) (s : GradedMap B C)
    (e : ∀ i a, r.app i (g.chainMap.f i a) = s.app i (p.chainMap.f i a))
    (i : ℤ) (y : B.complex.X i) :
    (pushoutDesc hX r s e).app i (X.inr.chainMap.f i y) = s.app i y := by
  change pushoutGradedDesc hX r s e i _ = _
  rw [hX.inr, pushoutGradedDesc_pure, r.one]
  exact C.toDGAlgebra.id_comp i _

private structure BaseChangedPresentation {V : Variables.{v}} (E : StagedPresentation P V g) where
  presentation : StagedPresentation B V (pushoutInr X hX)
  variable_image (x : V.Index) :
    presentation.component (V.degree x) (variableTerm B V x) =
      X.inl.chainMap.f (V.degree x) (E.component (V.degree x) (variableTerm P V x))

private def baseChangePresentation {V : Variables.{v}} (E : StagedPresentation P V g) :
    BaseChangedPresentation hX E := by
  let b := GradedMap.coefficient B V
  let J := ((GradedMap.strict p).comp b).lift (V := V) (variableTerm B V)
  let r := (GradedMap.inversePresentation E.toPresentation).comp (GradedMap.ofLift J)
  have compat : ∀ i a, r.app i (g.chainMap.f i a) = b.app i (p.chainMap.f i a) := by
    intro i a
    change J.component i ((E.component i).symm (g.chainMap.f i a)) = _
    rw [← E.map_base, LinearEquiv.symm_apply_apply, J.map_base]
    rfl
  let K := pushoutDesc hX r b compat
  let L := (GradedMap.strict (pushoutInr X hX)).lift (V := V)
    (fun x => X.inl.chainMap.f (V.degree x) (E.component _ (variableTerm P V x)))
  have hLJ : ∀ i y, L.component i (J.component i y) = X.inl.chainMap.f i (E.component i y) := by
    apply GradedMap.polyExt (L := (GradedMap.ofLift J).comp (GradedMap.ofLift L))
      (M := (GradedMap.ofPresentation E.toPresentation).comp (GradedMap.strict (pushoutInl X hX)))
    · intro i a
      change L.component i (J.component i (Semifree.coefficient P V i a)) = _
      rw [J.map_base]
      change L.component i (Semifree.coefficient B V i (p.chainMap.f i a)) =
        X.inl.chainMap.f i (E.component i (Semifree.coefficient P V i a))
      rw [L.map_base, E.map_base]
      exact (congrArg (fun z : P.toCommDGAlgebra ⟶ X.obj => z.chainMap.f i a) hX.base).symm
    · intro a
      change L.component _ (J.component _ (variableTerm P V a)) = _
      rw [J.map_var]
      exact L.map_var a
  have hLK : ∀ i z, L.component i (K.app i z) = z := by
    intro i z
    suffices eq : (L.component i).comp (K.app i) = LinearMap.id from LinearMap.congr_fun eq z
    apply pushoutExt hX
    intro m n eq x y
    change L.component i (pushoutGradedDesc hX r b compat i (X.tmul m n i eq x y)) = _
    rw [pushoutGradedDesc_pure]
    change L.component i (polynomialMul B V m n i eq (r.app m x) (Semifree.coefficient B V n y)) = _
    rw [L.map_mul, L.map_base]
    change X.obj.mul m n i eq (L.component m (J.component m ((E.component m).symm x)))
      (X.inr.chainMap.f n y) = _
    rw [hLJ, LinearEquiv.apply_symm_apply]
    exact pushout_factor hX m n i eq x y
  have hKL : ∀ i z, K.app i (L.component i z) = z := by
    let id : GradedMap (poly B V) (poly B V) := ⟨fun _ => LinearMap.id, rfl, fun _ _ _ _ _ _ => rfl⟩
    apply GradedMap.polyExt (L := (GradedMap.ofLift L).comp K) (M := id)
    · intro i a
      change K.app i (L.component i (Semifree.coefficient B V i a)) = Semifree.coefficient B V i a
      rw [L.map_base]
      exact pushoutDesc_inr hX r b compat i a
    · intro x
      change K.app _ (L.component _ (variableTerm B V x)) = variableTerm B V x
      rw [L.map_var]
      change (pushoutDesc hX r b compat).app _
        (X.inl.chainMap.f _ (E.component _ (variableTerm P V x))) = _
      rw [pushoutDesc_inl]
      change J.component _ ((E.component _).symm (E.component _ (variableTerm P V x))) = _
      rw [LinearEquiv.symm_apply_apply, J.map_var]
  let D (i : ℤ) : Polynomial B V i ≃ₗ[k] (pushout X hX).complex.X i :=
    LinearEquiv.ofLinearMap (L.component i) (K.app i) (LinearMap.ext (hLK i)) (LinearMap.ext (hKL i))
  let E' : Semifree.Presentation B V (pushoutInr X hX) :=
    ⟨D, (GradedMap.ofLift L).one, L.map_mul, L.map_base⟩
  refine ⟨⟨E', E.stages, ?_⟩, L.map_var⟩
  intro x
  change UsesOnly B V (E.stages.before (E.stages.stage x))
    (K.app (V.degree x + 1) (X.obj.complex.d (V.degree x) (V.degree x+1)
      (L.component _ (variableTerm B V x))))
  rw [L.map_var]
  have hd := CategoryTheory.congr_fun (X.inl.chainMap.comm (V.degree x) (V.degree x+1))
    (E.component _ (variableTerm P V x))
  simp only [ModuleCat.comp_apply] at hd
  erw [hd, show K = pushoutDesc hX r b compat from rfl, pushoutDesc_inl]
  apply GradedMap.lift_usesOnly J _ _ _ _ (E.earlier x)
  · exact fun i y => coefficient_usesOnly i (p.chainMap.f i y)
  · exact fun a ha => variable_usesOnly a ha

private def regularComparison {A B C : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ B} {g : A ⟶ C} (p : B ⟶ C) (h : f ≫ p = g) :
    restrict (underlying f) (regular B.toCommDGAlgebra) ⟶
      restrict (underlying g) (regular C.toCommDGAlgebra) where
  app _ := p.chainMap
  comm_act := by
    rintro ⟨⟩ ⟨⟩ i j n e x a
    change p.chainMap.f n (B.mul i j n e x (f.chainMap.f j a)) =
      C.mul i j n e (p.chainMap.f i x) (g.chainMap.f j a)
    rw [p.map_mul]
    exact congrArg (C.mul i j n e (p.chainMap.f i x))
      (congrArg (fun t : A ⟶ C => t.chainMap.f j a) h)

private theorem pushoutInlQuasiIso (hT : TensorFormulas T) (comp : T.Comparisons)
    (hg : Semifree.IsSemifree P g) (hp : NonpositiveCDGA.IsQuasiIso p) :
    NonpositiveCDGA.IsQuasiIso (pushoutInl X hX) := by
  let A := P.toCommDGAlgebra
  let M := restrict (underlying g) (regular Q.toCommDGAlgebra)
  let a := regularComparison p (f := 𝟙 P) (g := p) (Category.id_comp p)
  have ha : Specs.DerivedFormalization.DG.Module.quasiIsomorphism a := by
    rintro ⟨⟩
    exact hp
  have hM : T.KFlat M := SemifreeFlatness.semifree_algebra_kFlat T g (hT _ _) hg
  obtain ⟨m, hm, hmFormula⟩ := comp.secondQuasiIso (M := M) a hM ha
  obtain ⟨e₁, he₁⟩ := comp.identity M
  obtain ⟨e₂, he₂⟩ := hX.underlying
  let F := RightDGModuleModel.eval (A := Specs.DerivedFormalization.Affine.Tensor.dgCat A) ()
  have chain_eq : (F.mapIso e₁).inv ≫ m.app () ≫ (F.mapIso e₂).hom = X.inl.chainMap := by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have eInv : (e₁.inv.app ()).f i x = T.tmul (𝟙 A) (M := M) (N := regular A)
        i 0 i (add_zero i) x A.one := by
      have he := he₁ i 0 i (add_zero i) x A.one
      change (e₁.hom.app ()).f i _ = act M i 0 i (add_zero i) x A.one at he
      rw [M.act_id] at he
      have h := CategoryTheory.congr_fun
        (congrArg (fun z => (z.app ()).f i) e₁.hom_inv_id)
      have hh := h (T.tmul (𝟙 A) (M := M) (N := regular A) i 0 i (add_zero i) x A.one)
      change (e₁.inv.app ()).f i ((e₁.hom.app ()).f i _) = _ at hh
      rw [he] at hh
      exact hh
    change (e₂.hom.app ()).f i ((m.app ()).f i ((e₁.inv.app ()).f i x)) =
      X.inl.chainMap.f i x
    rw [eInv, hmFormula, he₂, hX.inl]
    exact congrArg (X.tmul i 0 i (add_zero i) x) p.map_one
  have hi : QuasiIso ((F.mapIso e₁).inv ≫ m.app () ≫ (F.mapIso e₂).hom) :=
    quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' :=
      quasiIso_comp _ _ (hφ := hm ()) (hφ' := quasiIso_of_isIso _))
  change QuasiIso X.inl.chainMap
  exact chain_eq ▸ hi

theorem pushoutResolves : PushoutResolves.{u,v} := by
  intro k _ _ T hT hc P Q B C g p c q X hX hcomm hg hp hqs hqq
  have sq : underlying g ≫ underlying q = underlying p ≫ underlying c := hcomm
  obtain ⟨w, ⟨hw₁, hw₂⟩, _⟩ := hX.coproduct (underlying q) (underlying c) sq
  let w' : pushout X hX ⟶ C := w
  have h₁ : pushoutInl X hX ≫ w' = q := hw₁
  have h₂ : pushoutInr X hX ≫ w' = c := hw₂
  have hI := pushoutInlQuasiIso hX hT hc hg hp
  obtain ⟨V, ⟨G⟩⟩ := hg
  refine ⟨⟨w', h₁, h₂, ⟨V, ⟨(baseChangePresentation hX G).presentation⟩⟩, hI, ?_, ?_⟩⟩
  · intro n z
    obtain ⟨y, hy⟩ := hqs n z
    refine ⟨X.inl.chainMap.f n y, ?_⟩
    exact (congrArg (fun t : Q ⟶ C => t.chainMap.f n y) h₁).trans hy
  · change QuasiIso w.chainMap
    have hq : QuasiIso (X.inl.chainMap ≫ w.chainMap) := by
      change NonpositiveCDGA.IsQuasiIso (pushoutInl X hX ≫ w')
      rwa [h₁]
    exact (quasiIso_iff_comp_left X.inl.chainMap w.chainMap (hφ := hI)).mp hq

end Pushout

end Graded

section Differentials

open CochainComplex.HomComplex (Cochain)
open Kahler (IsDerivation value DifferentialModel)
open Specs.DerivedFormalization.Affine.Tensor (act_assoc_at)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component ofStrict)

open private representStrict scalarExtend scalarExtend_pure symbol_commutes
  tensor_ext unit_tensor_action from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open private unitTensor unitTensor_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex

private theorem differentialSquare {A P B Q : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ P} {f' : B ⟶ Q} (g : P ⟶ Q) (a : A ⟶ B) (eq : f ≫ g = a ≫ f')
    (O : Differentials f) (W : Differentials f') :
    ∃ L : O.module ⟶ restrict (underlying g) W.module,
      ∀ i x, (L.app ()).f i (symbol O i x) = symbol W i (g.chainMap.f i x) := by
  let D : P.complex ⟶ (restrict (underlying g) W.module).complex () :=
    Tensor.chainOfDegrees (fun i =>
      (value W.symbol i i (add_zero i)).hom.comp (g.chainMap.f i).hom) (by
      intro i x
      change ((W.module.complex ()).d i (i+1)) (symbol W i (g.chainMap.f i x)) =
        symbol W (i+1) (g.chainMap.f (i+1) (P.complex.d i (i+1) x))
      rw [symbol_commutes _ W.closed]
      exact congrArg (symbol W (i+1))
        (CategoryTheory.congr_fun (g.chainMap.comm i (i+1)) x))
  apply representStrict O _ D
  constructor
  · intro i p h x
    have e : i=p := by omega
    cases e
    change symbol W i (g.chainMap.f i (f.chainMap.f i x)) = 0
    rw [show g.chainMap.f i (f.chainMap.f i x) = f'.chainMap.f i (a.chainMap.f i x) from
      congrArg (fun t : A ⟶ Q => t.chainMap.f i x) eq]
    exact W.symbol.property.relative i i (add_zero i) _
  · intro i j n ir jr nr h hi hj hn x y
    cases (show i=ir by omega)
    cases (show j=jr by omega)
    cases (show n=nr by omega)
    change symbol W n (g.chainMap.f n (P.mul i j n h x y)) =
      act W.module i j n h (symbol W i (g.chainMap.f i x)) (g.chainMap.f j y) +
        (i*j).negOnePow • act W.module j i n (by omega)
          (symbol W j (g.chainMap.f j y)) (g.chainMap.f i x)
    rw [g.map_mul]
    exact W.symbol.property.leibniz i j n i j n h
      (add_zero i) (add_zero j) (add_zero n) (g.chainMap.f i x) (g.chainMap.f j y)

private theorem differentialSquareExtended {A P B Q C : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ P} {f' : B ⟶ Q} (T : ModuleTensor.{u,v} k) (hT : TensorFormulas T)
    (g : P ⟶ Q) (a : A ⟶ B) (eq : f ≫ g = a ≫ f')
    (O : Differentials f) (W : Differentials f')
    (p : P ⟶ C) (q : Q ⟶ C) (h : g ≫ q = p) :
    ∃ L : (extend T p).obj O.module ⟶ (extend T q).obj W.module,
      ∀ i j n h x y, (L.app ()).f n (extendedSymbol T O p i j n h x y) =
        extendedSymbol T W q i j n h (g.chainMap.f i x) y := by
  obtain ⟨d, hd⟩ := differentialSquare g a eq O W
  let f₁ := underlying g
  let f₂ := underlying q
  let L : O.module ⟶ restrict (underlying p) ((extend T q).obj W.module) :=
    (show O.module ⟶ restrict (f₁ ≫ f₂) ((extend T q).obj W.module) from
      d ≫ (restrictFunctor f₁).map (unitTensor f₂ W.module (hT _ _))) ≫
      eqToHom (congrArg (fun t : P ⟶ C => restrict (underlying t) ((extend T q).obj W.module)) h)
  refine ⟨scalarExtend T (hT _ _) L, ?_⟩
  intro i j n e x y
  change ((scalarExtend T (hT (underlying p) _) L).app ()).f n
      (extendedSymbol T O p i j n e x y) = _
  rw [show extendedSymbol T O p i j n e x y =
    T.tmul (underlying p) (N := regular C.toCommDGAlgebra) i j n e (symbol O i x) y from rfl,
    scalarExtend_pure]
  have hL : (L.app ()).f i (symbol O i x) =
      T.tmul f₂ (N := regular C.toCommDGAlgebra) i 0 i (add_zero i)
        (symbol W i (g.chainMap.f i x)) C.one := by
    subst p
    change ((unitTensor f₂ W.module (hT _ _)).app ()).f i
      ((d.app ()).f i (symbol O i x)) = _
    rw [hd, unitTensor_apply]
  rw [hL, unit_tensor_action T (hT f₂ _)]

end Differentials

section Bases

open SemifreeDifferentials
open Specs.DerivedFormalization.Affine.Tensor (act_assoc_at)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component ofStrict)

open private freeModule multiples_act freeGenerator multiples_freeGenerator
  degreeMap degreeMap_act gradedOfDegrees gradedOfDegrees_apply multiples_single single
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials

variable {D : CommDGAlgebra.{u,v} k} {V : Semifree.Variables.{v}} {M N : D.Module}

private def mapBasis {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)
    (y : ∀ x, term N (V.degree x)) : gradedHom M N 0 :=
  gradedOfDegrees
    (fun n => (multiples y n).comp (LinearEquiv.ofBijective _ (basis n)).symm.toLinearMap)
    (by
      intro i j n h z a
      let H (r : ℤ) := LinearEquiv.ofBijective _ (basis r)
      change multiples y n ((H n).symm (act M i j n h z a)) =
        act N i j n h (multiples y i ((H i).symm z)) a
      have he : (H n).symm (act M i j n h z a) =
          act (freeModule D V) i j n h ((H i).symm z) a := by
        apply (H n).injective
        rw [LinearEquiv.apply_symm_apply]
        change act M i j n h z a = multiples e n (act (freeModule D V) i j n h ((H i).symm z) a)
        rw [multiples_act]
        exact congrArg (fun x => act M i j n h x a) ((H i).apply_symm_apply z).symm
      rw [he, multiples_act])

private theorem mapBasis_apply {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)
    (y : ∀ x, term N (V.degree x)) (x : V.Index) :
    degreeMap (mapBasis basis y) (V.degree x) (e x) = y x := by
  let H := LinearEquiv.ofBijective _ (basis (V.degree x))
  unfold mapBasis
  rw [gradedOfDegrees_apply, LinearMap.comp_apply]
  change multiples y (V.degree x) (H.symm (e x)) = _
  rw [show H.symm (e x) = freeGenerator D V x by
    apply H.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (multiples_freeGenerator e x).symm, multiples_freeGenerator]

private theorem linearBasisExt {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)
    {L K : ∀ n, term M n →ₗ[k] term N n}
    (hL : ∀ i j n h x a, L n (act M i j n h x a) = act N i j n h (L i x) a)
    (hK : ∀ i j n h x a, K n (act M i j n h x a) = act N i j n h (K i x) a)
    (eq : ∀ x, L (V.degree x) (e x) = K (V.degree x) (e x)) (n : ℤ) :
    L n = K n := by
  classical
  have E : (L n).comp (multiples e n) = (K n).comp (multiples e n) := by
    apply DirectSum.linearMap_ext
    intro x
    apply LinearMap.ext
    intro a
    change L n (multiples e n (single D V n x a)) = K n (multiples e n (single D V n x a))
    rw [multiples_single, hL, hK, eq]
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (basis n).surjective x
  exact LinearMap.congr_fun E z

private theorem strictIsoOfBasis {e : ∀ x, term M (V.degree x)} {y : ∀ x, term N (V.degree x)}
    (he : IsGradedBasis e) (hy : IsGradedBasis y) (L : M ⟶ N)
    (hL : ∀ x, (L.app ()).f (V.degree x) (e x) = y x) : IsIso L := by
  let F (i : ℤ) := (L.app ()).f i |>.hom
  let inv := mapBasis hy e
  let G := degreeMap inv
  have GF (i : ℤ) : (G i).comp (F i) = LinearMap.id := by
    apply linearBasisExt he (L := fun i => (G i).comp (F i)) (K := fun _ => LinearMap.id)
    · intro p q n h x a
      change G n ((L.app ()).f n (act M p q n h x a)) = _
      rw [L.comm_act, degreeMap_act]
      rfl
    · intros
      rfl
    · intro x
      change G (V.degree x) ((L.app ()).f (V.degree x) (e x)) = e x
      rw [hL, mapBasis_apply hy e]
  have FG (i : ℤ) : (F i).comp (G i) = LinearMap.id := by
    apply linearBasisExt hy (L := fun i => (F i).comp (G i)) (K := fun _ => LinearMap.id)
    · intro p q n h x a
      change (L.app ()).f n (G n (act N p q n h x a)) = _
      rw [degreeMap_act, L.comm_act]
      rfl
    · intros
      rfl
    · intro x
      change (L.app ()).f (V.degree x) (G (V.degree x) (y x)) = y x
      rw [mapBasis_apply hy e, hL]
  let J : N ⟶ M := Tensor.homOfDegrees G (by
    intro i z
    have hLeft : Function.LeftInverse (G (i+1)) (F (i+1)) :=
      fun y => LinearMap.congr_fun (GF (i+1)) y
    apply hLeft.injective
    change (L.app ()).f (i+1) ((M.complex ()).d i (i+1) (G i z)) =
      F (i+1) (G (i+1) ((N.complex ()).d i (i+1) z))
    rw [show F (i+1) (G (i+1) ((N.complex ()).d i (i+1) z)) = (N.complex ()).d i (i+1) z
      from LinearMap.congr_fun (FG _) _]
    have h := CategoryTheory.congr_fun ((L.app ()).comm i (i+1)) (G i z)
    change (N.complex ()).d i (i+1) (F i (G i z)) = _ at h
    rw [show F i (G i z) = z from LinearMap.congr_fun (FG i) z] at h
    exact h.symm) (degreeMap_act inv)
  refine ⟨⟨J, ?_, ?_⟩⟩
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    ext n z
    exact LinearMap.congr_fun (GF n) z
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    ext n z
    exact LinearMap.congr_fun (FG n) z

end Bases

section GradedTensor

open Specs.DerivedFormalization.DG.HomComplex (gradedHom component)
open Specs.DerivedFormalization.Affine.Tensor (signedLeft)

open private degreeMap degreeMap_act gradedOfDegrees gradedOfDegrees_apply
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials
open private tensor_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {A B : CommDGAlgebra.{u,v} k} {M N : A.Module}
variable (T : ModuleTensor.{u,v} k) {g : A ⟶ B}

private def extendGradedDegree (L : gradedHom M N 0) (n : ℤ) :
    term ((T.baseChange g).obj M) n →ₗ[k] term ((T.baseChange g).obj N) n :=
  (T.degree g N (regular B) n).toLinearMap.comp
    ((Tensor.liftDegree (f := g) (M := M) (N := regular B)
      (fun i j h => (Tensor.pair g (M := N) (N := regular B) i j n h).comp (degreeMap L i))
      (by
        intro i l j h x a y
        simp only [LinearMap.comp_apply, degreeMap_act]
        exact Tensor.pure_balance g (M := N) (N := regular B) i l j (i+l) (l+j) n
          rfl rfl h (degreeMap L i x) a y)).comp
      (T.degree g M (regular B) n).symm.toLinearMap)

private theorem extendGradedDegree_pure (L : gradedHom M N 0) (i j n : ℤ)
    (h : i+j=n) (x : term M i) (y : B.complex.X j) :
    extendGradedDegree (g := g) T L n (T.tmul g (N := regular B) i j n h x y) =
      T.tmul g (N := regular B) i j n h (degreeMap L i x) y := by
  simp only [extendGradedDegree, ModuleTensor.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  erw [Tensor.liftDegree_pure]
  rfl

private def extendGraded (formulas : T.Formulas g (regular B)) (L : gradedHom M N 0) :
    gradedHom ((T.baseChange g).obj M) ((T.baseChange g).obj N) 0 :=
  gradedOfDegrees (extendGradedDegree T L) (by
    intro n l q h z a
    suffices e : (extendGradedDegree T L q).comp
        ((act ((T.baseChange g).obj M) n l q h).flip a) =
      ((act ((T.baseChange g).obj N) n l q h).flip a).comp (extendGradedDegree T L n) from
        LinearMap.congr_fun e z
    apply tensor_ext T
    intro i j e x y
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, formulas.action, extendGradedDegree_pure])

private theorem extendGraded_pure (formulas : T.Formulas g (regular B)) (L : gradedHom M N 0)
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : B.complex.X j) :
    degreeMap (extendGraded T formulas L) n (T.tmul g (N := regular B) i j n h x y) =
      T.tmul g (N := regular B) i j n h (degreeMap L i x) y := by
  rw [extendGraded, gradedOfDegrees_apply, extendGradedDegree_pure]

open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)

private theorem extendsGradedSplit {L M N : A.Module} {f : L ⟶ M} {p : M ⟶ N}
    (formulas : T.Formulas g (regular B)) (h : GradedSplit f p) :
    Nonempty (GradedSplit ((T.baseChange g).map f) ((T.baseChange g).map p)) := by
  let i := (T.baseChange g).map f
  let j := (T.baseChange g).map p
  let r := extendGraded T formulas h.retraction
  let s := extendGraded T formulas h.sectionMap
  have iz : i ≫ j = 0 := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply tensor_ext T
    intro a b e x y
    change (j.app ()).f n ((i.app ()).f n (T.tmul g (N := regular B) a b n e x y)) = 0
    rw [formulas.first, formulas.first]
    have z : (p.app ()).f a ((f.app ()).f a x) = 0 :=
      CategoryTheory.congr_fun (congrArg (fun q => (q.app ()).f a) h.zero) x
    rw [z]
    simp only [ModuleTensor.tmul, ← Tensor.pair_apply, map_zero, LinearMap.zero_apply]
  refine ⟨⟨iz, r, s, ?_, ?_, ?_⟩⟩
  · intro n z
    suffices e : (degreeMap r n).comp ((i.app ()).f n).hom = LinearMap.id from
      LinearMap.congr_fun e z
    apply tensor_ext T
    intro a b e x y
    change degreeMap r n ((i.app ()).f n (T.tmul g (N := regular B) a b n e x y)) =
      T.tmul g (N := regular B) a b n e x y
    rw [formulas.first, extendGraded_pure T formulas,
      show degreeMap h.retraction a ((f.app ()).f a x) = x from h.retract a x]
  · intro n z
    suffices e : ((j.app ()).f n).hom.comp (degreeMap s n) = LinearMap.id from
      LinearMap.congr_fun e z
    apply tensor_ext T
    intro a b e x y
    change (j.app ()).f n (degreeMap s n (T.tmul g (N := regular B) a b n e x y)) =
      T.tmul g (N := regular B) a b n e x y
    rw [extendGraded_pure T formulas, formulas.first,
      show (p.app ()).f a (degreeMap h.sectionMap a x) = x from h.section_id a x]
  · intro n z
    suffices e : ((i.app ()).f n).hom.comp (degreeMap r n) +
        (degreeMap s n).comp ((j.app ()).f n).hom = LinearMap.id from LinearMap.congr_fun e z
    apply tensor_ext T
    intro a b e x y
    change (i.app ()).f n (degreeMap r n (T.tmul g (N := regular B) a b n e x y)) +
      degreeMap s n ((j.app ()).f n (T.tmul g (N := regular B) a b n e x y)) =
        T.tmul g (N := regular B) a b n e x y
    rw [extendGraded_pure T formulas, formulas.first, formulas.first, extendGraded_pure T formulas]
    let L := (T.degree g M (regular B) n).toLinearMap.comp
      ((Tensor.pair g (M := M) (N := regular B) a b n e).flip y)
    change L ((f.app ()).f a (degreeMap h.retraction a x)) +
      L (degreeMap h.sectionMap a ((p.app ()).f a x)) = L x
    rw [← map_add]
    exact congrArg L (h.decompose a x)

end GradedTensor

section SplitSequence

open Semifree (Variables StagedPresentation variableTerm)
open SemifreeDifferentials (IsGradedBasis generator)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom)
open private degreeMap degreeMap_act from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials
open private scalarExtend scalarExtend_pure from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {D : CommDGAlgebra.{u,v} k} {L M N : D.Module} {V W : Variables.{v}}

private def splitOnBasis (f : L ⟶ M) (g : M ⟶ N)
    {l : ∀ x, term L (V.degree x)} {r : ∀ x, term N (W.degree x)}
    {m : ∀ x, term M ((sumVariables V W).degree x)}
    (hl : IsGradedBasis l) (hm : IsGradedBasis m) (hr : IsGradedBasis r)
    (hf : ∀ x, (f.app ()).f (V.degree x) (l x) = m (.inl x))
    (hg₁ : ∀ x, (g.app ()).f (V.degree x) (m (.inl x)) = 0)
    (hg₂ : ∀ x, (g.app ()).f (W.degree x) (m (.inr x)) = r x) :
    GradedSplit f g := by
  let re := mapBasis hm (N := L) (fun x => match x with | .inl a => l a | .inr _ => 0)
  let se := mapBasis hr (N := M) (fun x => m (.inr x))
  have hl' (x : V.Index) : degreeMap re (V.degree x) (m (.inl x)) = l x :=
    mapBasis_apply hm _ (.inl x)
  have hr' (x : W.Index) : degreeMap re (W.degree x) (m (.inr x)) = 0 :=
    mapBasis_apply hm _ (.inr x)
  have hse (x : W.Index) : degreeMap se (W.degree x) (r x) = m (.inr x) :=
    mapBasis_apply hr _ x
  let F (i : ℤ) := ((f.app ()).f i).hom
  let G (i : ℤ) := ((g.app ()).f i).hom
  let R := degreeMap re
  let S := degreeMap se
  have hzero (n : ℤ) : (G n).comp (F n) = 0 := by
    apply linearBasisExt hl (L := fun n => (G n).comp (F n)) (K := fun _ => 0)
    · intro i j n h x a
      change (g.app ()).f n ((f.app ()).f n (act L i j n h x a)) = _
      rw [f.comm_act, g.comm_act]
      rfl
    · intro i j n h x a
      simp only [LinearMap.zero_apply, map_zero]
    · intro x
      change (g.app ()).f _ ((f.app ()).f _ (l x)) = 0
      rw [hf, hg₁]
  refine ⟨?_, re, se, ?_, ?_, ?_⟩
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    ext n x
    exact LinearMap.congr_fun (hzero n) x
  · intro n x
    suffices e : (R n).comp (F n) = LinearMap.id from LinearMap.congr_fun e x
    apply linearBasisExt hl (L := fun n => (R n).comp (F n)) (K := fun _ => LinearMap.id)
    · intro i j n h z a
      change R n ((f.app ()).f n (act L i j n h z a)) = _
      rw [f.comm_act, degreeMap_act]
      rfl
    · intros
      rfl
    · intro a
      change R (V.degree a) ((f.app ()).f _ (l a)) = l a
      rw [hf, hl']
  · intro n x
    suffices e : (G n).comp (S n) = LinearMap.id from LinearMap.congr_fun e x
    apply linearBasisExt hr (L := fun n => (G n).comp (S n)) (K := fun _ => LinearMap.id)
    · intro i j n h z a
      change (g.app ()).f n (S n (act N i j n h z a)) = _
      rw [degreeMap_act, g.comm_act]
      rfl
    · intros
      rfl
    · intro a
      change (g.app ()).f _ (S (W.degree a) (r a)) = r a
      rw [hse, hg₂]
  · intro n x
    suffices e : (F n).comp (R n) + (S n).comp (G n) = LinearMap.id from LinearMap.congr_fun e x
    apply linearBasisExt hm (L := fun n => (F n).comp (R n) + (S n).comp (G n))
      (K := fun _ => LinearMap.id)
    · intro i j n h z a
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      change (f.app ()).f n (R n (act M i j n h z a)) +
        S n ((g.app ()).f n (act M i j n h z a)) = _
      rw [degreeMap_act, f.comm_act, g.comm_act, degreeMap_act]
      exact (map_add ((act M i j n h).flip a) _ _).symm
    · intros
      rfl
    · rintro (a | a)
      · change (f.app ()).f _ (R (V.degree a) (m (.inl a))) +
          S (V.degree a) ((g.app ()).f _ (m (.inl a))) = m (.inl a)
        rw [hl', hf, hg₁, map_zero, add_zero]
      · change (f.app ()).f _ (R (W.degree a) (m (.inr a))) +
          S (W.degree a) ((g.app ()).f _ (m (.inr a))) = m (.inr a)
        rw [hr', map_zero, hg₂, hse, zero_add]

theorem exactDifferentialSequence : ExactDifferentialSequence.{u,v} := by
  intro k _ _ T hT A P Q f g O U V hf hg
  obtain ⟨I, ⟨E⟩⟩ := hf
  obtain ⟨J, ⟨H⟩⟩ := hg
  let Z := concatenatePresentations E H
  obtain ⟨i, hi⟩ := differentialSquare g (𝟙 A) (Category.id_comp (f ≫ g)).symm O U
  obtain ⟨p, hp⟩ := differentialSquare (𝟙 Q) f (Category.comp_id (f ≫ g)) U V
  let i' := scalarExtend T (hT (underlying g) _) i
  let p' : U.module ⟶ V.module := p ≫ eqToHom
    (show restrict (underlying (𝟙 Q)) V.module = V.module from rfl)
  have hp' : ∀ n x, (p'.app ()).f n (symbol U n x) = symbol V n x := hp
  have hi' : ∀ n j z e x a, (i'.app ()).f z (extendedSymbol T O g n j z e x a) =
      act U.module n j z e (symbol U n (g.chainMap.f n x)) a := by
    intro n j z e x a
    change ((scalarExtend T (hT (underlying g) _) i).app ()).f z
      (T.tmul (underlying g) (N := regular Q.toCommDGAlgebra) n j z e (symbol O n x) a) = _
    rw [scalarExtend_pure, hi]
  obtain ⟨_, hl, _⟩ := SemifreeDifferentials.semifreeAfterBaseChange T E O
    (underlying g) (hT _ _)
  have hm := SemifreeDifferentials.graded_basis Z.presentation U
  have hr := SemifreeDifferentials.graded_basis H V
  have hleft x : (i'.app ()).f (I.degree x)
      (T.tmul (underlying g) (N := regular Q.toCommDGAlgebra) (I.degree x) 0 (I.degree x)
        (add_zero _) (generator E O x) Q.one) = generator Z.presentation U (.inl x) := by
    change (i'.app ()).f (I.degree x)
      (extendedSymbol T O g (I.degree x) 0 (I.degree x) (add_zero _)
        (E.component _ (variableTerm A I x)) Q.one) = _
    rw [hi', U.module.act_id]
    exact congrArg (symbol U (I.degree x)) (Z.left x).symm
  have hproj₁ x : (p'.app ()).f (I.degree x) (generator Z.presentation U (.inl x)) = 0 := by
    change (p'.app ()).f (I.degree x)
      (symbol U (I.degree x) (Z.presentation.component _ (variableTerm A (sumVariables I J) (.inl x)))) = 0
    rw [hp']
    have eq := Z.left x
    erw [eq]
    exact V.symbol.property.relative _ _ (add_zero _) _
  have hproj₂ x : (p'.app ()).f (J.degree x) (generator Z.presentation U (.inr x)) = generator H V x := by
    change (p'.app ()).f (J.degree x)
      (symbol U (J.degree x) (Z.presentation.component _ (variableTerm A (sumVariables I J) (.inr x)))) = _
    rw [hp']
    exact congrArg (symbol V (J.degree x)) (Z.right x)
  let split := splitOnBasis i' p' hl hm hr hleft hproj₁ hproj₂
  exact ⟨⟨i', p', hi', hp', split⟩, fun t => extendsGradedSplit T (hT t _) split⟩

end SplitSequence

section ResolvedTerms

open Semifree (Variables StagedPresentation variableTerm)
open SemifreeDifferentials (IsGradedBasis generator)

variable (T : ModuleTensor.{u,v} k)

private theorem composeUnit {f : P ⟶ Q} {g : Q ⟶ C} {M : P.Module}
    (hc : T.Comparisons) :
    ∃ e : (extend T g).obj ((extend T f).obj M) ≅ (extend T (f ≫ g)).obj M,
      ∀ i j n h x y, (e.hom.app ()).f n
        (T.tmul (underlying g) (N := regular C.toCommDGAlgebra) i j n h
          (T.tmul (underlying f) (N := regular Q.toCommDGAlgebra) i 0 i (add_zero i) x Q.one) y) =
        T.tmul (underlying (f ≫ g)) (N := regular C.toCommDGAlgebra) i j n h x y := by
  obtain ⟨e, h⟩ := hc.compose (underlying f) (underlying g) M
  refine ⟨e, ?_⟩
  intro i j n eq x y

  have eFormula := h i 0 j i n (add_zero i) eq x Q.one y
  erw [eFormula, g.map_one]
  have h₁ (l : ℤ) (hl : 0+j=l) :
      T.tmul (underlying (f ≫ g)) (N := regular C.toCommDGAlgebra) i l n (by omega) x
        (C.mul 0 j l hl C.one y) =
      T.tmul (underlying (f ≫ g)) (N := regular C.toCommDGAlgebra) i j n eq x y := by
    obtain rfl : l=j := by omega
    rw [C.toDGAlgebra.id_comp]
  exact h₁ _ rfl

private theorem transportPure {M : P.Module} {g g' : P ⟶ C} (eq : g = g')
    (i j n : ℤ) (h : i+j=n) (x : term M i) (a : C.complex.X j) :
    ((eqToHom (congrArg (fun t : P ⟶ C => (extend T t).obj M) eq)).app ()).f n
      (T.tmul (underlying g) (N := regular C.toCommDGAlgebra) i j n h x a) =
      T.tmul (underlying g') (N := regular C.toCommDGAlgebra) i j n h x a := by
  subst g'
  rfl

theorem resolvedTerms : ResolvedTerms.{u,v} := by
  intro k _ _ T hT hc A B C b c R S U F X hX D W
  have hp := CotangentModelProperties.cotangentModelProperties T b R.base R.augmentation
    R.differentials R.triangle R.semifree R.surjective R.quasiIso (hT _ _) (hT _)
  have hs := concatenation R.base S.base R.semifree S.semifree
  obtain ⟨e₁, he₁⟩ := composeUnit T (f := S.base) (g := S.augmentation)
    (M := R.differentials.module) hc
  obtain ⟨e₂, he₂⟩ := composeUnit T (f := R.augmentation) (g := c) (M := R.differentials.module) hc
  let e₀ := eqToIso (congrArg (fun t : R.algebra ⟶ C => (extend T t).obj R.differentials.module) S.triangle)
  let left := e₁ ≪≫ e₀ ≪≫ e₂.symm
  have lhs : ∀ i j n h x a, (left.hom.app ()).f n
      (T.tmul (underlying S.augmentation) (N := regular C.toCommDGAlgebra) i j n h
        (extendedSymbol T R.differentials S.base i 0 i (add_zero i) x S.algebra.one) a) =
      T.tmul (underlying c) (N := regular C.toCommDGAlgebra) i j n h
        (extendedSymbol T R.differentials R.augmentation i 0 i (add_zero i) x B.one) a := by
    intro i j n h x a
    let z := T.tmul (underlying c) (N := regular C.toCommDGAlgebra) i j n h
      (extendedSymbol T R.differentials R.augmentation i 0 i (add_zero i) x B.one) a
    change (e₂.inv.app ()).f n ((e₀.hom.app ()).f n ((e₁.hom.app ()).f n
      (T.tmul (underlying S.augmentation) (N := regular C.toCommDGAlgebra) i j n h
        (T.tmul (underlying S.base) (N := regular S.algebra.toCommDGAlgebra) i 0 i (add_zero i)
          (symbol R.differentials i x) S.algebra.one) a))) = z
    rw [he₁]
    have eq₀ := transportPure T S.triangle i j n h (symbol R.differentials i x) a
    change (e₀.hom.app ()).f n _ = _ at eq₀
    rw [eq₀, ← he₂]
    exact CategoryTheory.congr_fun (congrArg (fun t => (t.app ()).f n) e₂.hom_inv_id) z
  have sq : S.base ≫ pushoutInl X hX = R.augmentation ≫ pushoutInr X hX := hX.base
  obtain ⟨r, hr⟩ := differentialSquareExtended T hT (pushoutInl X hX)
    R.augmentation sq S.differentials W S.augmentation D.augmentation D.ofQ_comp
  have hi : IsIso r := by
    obtain ⟨V, ⟨E⟩⟩ := S.semifree
    let H := baseChangePresentation hX E
    obtain ⟨_, hE, _⟩ := SemifreeDifferentials.semifreeAfterBaseChange T E S.differentials
      (underlying S.augmentation) (hT _ _)
    obtain ⟨_, hH, _⟩ := SemifreeDifferentials.semifreeAfterBaseChange T H.presentation W
      (underlying D.augmentation) (hT _ _)
    apply strictIsoOfBasis hE hH r
    intro x
    change (r.app ()).f (V.degree x) (extendedSymbol T S.differentials S.augmentation
      (V.degree x) 0 (V.degree x) (add_zero _) (E.component _ (variableTerm _ _ x)) C.one) =
        extendedSymbol T W D.augmentation (V.degree x) 0 (V.degree x) (add_zero _)
          (H.presentation.component _ (variableTerm _ _ x)) C.one
    rw [hr, H.variable_image]
    rfl
  refine ⟨hp.1, hp.2, ⟨⟨left, asIso r, lhs, hr⟩⟩, extendsGradedSplit T (hT _ _) F.split, ?_, ?_, ?_⟩
  · exact goodTermOfSemifree T hT (semifreeOfIso e₁.symm
      (extendedSemifree T hT R.semifree R.differentials (S.base ≫ S.augmentation)))
  · exact goodTermOfSemifree T hT (extendedSemifree T hT hs U S.augmentation)
  · exact goodTermOfSemifree T hT
      (extendedSemifree T hT S.semifree S.differentials S.augmentation)

end ResolvedTerms

end
end DerivedFormalization.Affine.ResolvedCotangentSequence
