import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.Basic (cyclesZero boundariesZero classOf h0Hom)
open Specs.DerivedFormalization.DG.DerivedCoproducts
open Specs.DerivedFormalization.DG.IndexedSemiFree (StrictSum)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open private restrict restrict_d restrict_app gradedHom_coproduct_bijective
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure
open private term_hom_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
open private represented_naturality classMap_strict transitionSum
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

universe u v w j t s z z' v'

namespace DerivedFormalization.RightDGModule

noncomputable section

variable {k : Type u} [CommRing k]

private def quotientEquivOfSurjective {M L : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup L] [Module k L] (p : Submodule k M) (f : M →ₗ[k] L)
    (hker : ∀ x, f x = 0 ↔ x ∈ p) (hsurj : Function.Surjective f) :
    (M ⧸ p) ≃ₗ[k] L :=
  let g := p.liftQ f (fun x hx => LinearMap.mem_ker.mpr ((hker x).mpr hx))
  LinearEquiv.ofBijective g ⟨by
    apply (LinearMap.ker_eq_bot).mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun x hx => (hker x).mp (LinearMap.mem_ker.mp hx)), by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨p.mkQ x, rfl⟩⟩

private theorem mem_boundaries_iff {C : ModuleCochain.{u,z} k} (x : cyclesZero C) :
    x ∈ boundariesZero C ↔ ∃ y : C.X (-1), C.d (-1) 0 y = x.val := by
  change (∃ y : C.X (-1), (Basic.zeroShort C).moduleCatToCycles y = x) ↔ _
  exact exists_congr fun _ => Subtype.ext_iff

theorem productH0 : ProductH0.{u,j,z} := by
  intro k _ I C
  let f : cyclesZero (productComplex C) →ₗ[k] (∀ i, h0Hom (C i)) :=
    { toFun := fun x i => classOf (productCycle C x i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hker (x : cyclesZero (productComplex C)) : f x = 0 ↔ x ∈ boundariesZero (productComplex C) := by
    rw [mem_boundaries_iff]
    constructor
    · intro hx
      have hi (i : I) : ∃ y : (C i).X (-1), (C i).d (-1) 0 y = x.val i := by
        apply (mem_boundaries_iff (productCycle C x i)).mp
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hx i
      choose y hy using hi
      exact ⟨y, funext hy⟩
    · rintro ⟨y, hy⟩
      funext i
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (mem_boundaries_iff _).mpr ⟨y i, congrFun hy i⟩
  have hsurj : Function.Surjective f := by
    intro y
    choose x hx using fun i => (boundariesZero (C i)).mkQ_surjective (y i)
    let v : cyclesZero (productComplex C) := ⟨fun i => (x i).val,
      funext fun i => (x i).property⟩
    exact ⟨v, funext hx⟩
  exact ⟨quotientEquivOfSurjective _ f hker hsurj, fun _ _ => rfl⟩

/-- Degreewise coefficient equivalences commuting with the differential identify H⁰,
even when the terms of the complexes live in different universes. -/
private def h0EquivOfDegrees (C : ModuleCochain.{u,z} k) (L : ModuleCochain.{u,z'} k)
    (e : ∀ n, C.X n ≃ₗ[k] L.X n)
    (he : ∀ n m (x : C.X n), e m (C.d n m x) = L.d n m (e n x)) :
    h0Hom C ≃ₗ[k] h0Hom L := by
  let g : cyclesZero C →ₗ[k] cyclesZero L :=
    { toFun := fun x => ⟨e 0 x.val, by
        change L.d 0 1 (e 0 x.val) = 0
        rw [← he, show C.d 0 1 x.val = 0 from x.property, map_zero]⟩
      map_add' := fun x y => Subtype.ext (map_add (e 0) x.val y.val)
      map_smul' := fun r x => Subtype.ext (map_smul (e 0) r x.val) }
  refine quotientEquivOfSurjective _ ((boundariesZero L).mkQ.comp g) ?_ ?_
  · intro x
    change classOf (g x) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_boundaries_iff, mem_boundaries_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(e (-1)).symm y, (e 0).injective ?_⟩
      rw [he, LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨y, hy⟩
      exact ⟨e (-1) y, (he (-1) 0 y).symm.trans (congrArg (e 0) hy)⟩
  · intro x
    obtain ⟨x, rfl⟩ := (boundariesZero L).mkQ_surjective x
    have h : C.d 0 1 ((e 0).symm x.val) = 0 := by
      apply (e 1).injective
      rw [he, LinearEquiv.apply_symm_apply, map_zero]
      exact x.property
    refine ⟨⟨(e 0).symm x.val, h⟩, ?_⟩
    apply congrArg (boundariesZero L).mkQ
    exact Subtype.ext ((e 0).apply_symm_apply _)

section Strict

variable {A : DGCategory.{u,v,w} k} {I : Type j}
  {F : I → RightDGModule A} {S : RightDGModule A}

private def gradedRestriction (b : StrictSum F S) (N : RightDGModule A) (r : ℤ) :
    GradedHom S N r ≃ₗ[k] (∀ i, GradedHom (F i) N r) := by
  let f : GradedHom S N r →ₗ[k] (∀ i, GradedHom (F i) N r) :=
    LinearMap.pi fun i => (dgCategory A).comp r 0 r (add_zero r) |>.flip (strictCycle (b.inclusion i)).val
  exact LinearEquiv.ofBijective f (gradedHom_coproduct_bijective (DG.IndexedSums.isColimit b) r)

private theorem gradedRestriction_d (b : StrictSum F S) (N : RightDGModule A)
    (r q : ℤ) (g : (homComplex S N).X r) :
    gradedRestriction b N q ((homComplex S N).d r q g) =
      (productComplex (fun i => homComplex (F i) N)).d r q (gradedRestriction b N r g) := by
  funext i
  change restrict (b.inclusion i) ((homComplex S N).d r q g) =
    (homComplex (F i) N).d r q (restrict (b.inclusion i) g)
  by_cases h : r + 1 = q
  · subst q
    exact restrict_d _ _ _
  · have h' : ¬ (ComplexShape.up ℤ).Rel r q := h
    rw [(homComplex S N).shape r q h', (homComplex (F i) N).shape r q h']
    change gradedRestriction b N q 0 i = 0
    rw [map_zero]
    rfl

theorem homFromStrictSum : HomFromStrictSum.{u,v,w,j} := by
  intro k _ A I F S b N
  let e := gradedRestriction b N
  have he := gradedRestriction_d b N
  refine ⟨⟨e, he, fun r g i a n m hn x => restrict_app (b.inclusion i) g a n m hn x⟩, ?_⟩
  obtain ⟨E, hE⟩ := productH0.{u,j,max v w} (fun i => homComplex (F i) N)
  refine ⟨(h0EquivOfDegrees _ _ e he).trans E, ?_⟩
  intro g i
  obtain ⟨x, rfl⟩ := (boundariesZero (homComplex S N)).mkQ_surjective g
  let y : cyclesZero (productComplex (fun i => homComplex (F i) N)) :=
    ⟨e 0 x.val, by
      change (productComplex (fun i => homComplex (F i) N)).d 0 1 (e 0 x.val) = 0
      rw [← he, show (homComplex S N).d 0 1 x.val = 0 from x.property, map_zero]
      rfl⟩
  change E (classOf y) i = _
  rw [hE]
  change _ = Basic.h0Comp (dgCategory A) (classOf x) (classOf (strictCycle (b.inclusion i)))
  rw [DGCategory.h0Comp_mk]
  rfl

end Strict

section SumMap

open IndexedSemiFree (SumTerm summand)
open ShiftCone (coneDiff_succ)

variable {A : DGCategory.{u,v,w} k} {I : Type j}
  {F G : I → RightDGModule A} {S T : RightDGModule A}
  (b : StrictSum F S) (c : StrictSum G T) (p : ∀ i, F i ⟶ G i)
  {q : S ⟶ T} (hq : ∀ i, b.inclusion i ≫ q = p i ≫ c.inclusion i)

include hq in
private theorem sumMap_coordinate (a : A.Obj) (n : ℤ) (x : (S.complex a).X n) (i : I) :
    c.coordinates a n ((q.app a).f n x) i = ((p i).app a).f n (b.coordinates a n x i) := by
  classical
  let e : SumTerm F a n →ₗ[k] SumTerm G a n := DirectSum.lmap fun i => ((p i).app a |>.f n).hom
  have h : (c.coordinates a n).toLinearMap.comp ((q.app a).f n).hom =
      e.comp (b.coordinates a n).toLinearMap := by
    apply term_hom_ext b a n
    intro l y
    change c.coordinates a n (((b.inclusion l ≫ q).app a).f n y) =
      e (b.coordinates a n (((b.inclusion l).app a).f n y))
    rw [hq, b.coordinate_inclusion]
    change c.coordinates a n (((c.inclusion l).app a).f n (((p l).app a).f n y)) =
      DirectSum.lmap (fun i => ((p i).app a |>.f n).hom) (summand F a n l y)
    rw [c.coordinate_inclusion]
    exact (DirectSum.lmap_lof (fun i => ((p i).app a |>.f n).hom) l y).symm
  exact congrArg (fun z : SumTerm G a n => z i) (LinearMap.congr_fun h x)

private def coneEntry (a : A.Obj) (n : ℤ) (x : ShiftCone.coneTerm S T a n) (i : I) :
    ShiftCone.coneTerm (F i) (G i) a n :=
  (c.coordinates a n x.1 i, b.coordinates a (n + 1) x.2 i)

include hq in
private theorem coneEntry_d (a : A.Obj) (n : ℤ) (x : ((cone q).complex a).X n) (i : I) :
    coneEntry b c a (n + 1) (((cone q).complex a).d n (n + 1) x) i =
      ((cone (p i)).complex a).d n (n + 1) (coneEntry b c a n x i) := by
  change coneEntry b c a (n + 1) (ShiftCone.coneDiff q a n (n + 1) x) i =
    ShiftCone.coneDiff (p i) a n (n + 1) (coneEntry b c a n x i)
  rw [coneDiff_succ, coneDiff_succ]
  apply Prod.ext
  · change c.coordinates a (n+1)
      ((T.complex a).d n (n+1) x.1 + (q.app a).f (n+1) x.2) i =
      ((G i).complex a).d n (n+1) (c.coordinates a n x.1 i) +
        ((p i).app a).f (n+1) (b.coordinates a (n+1) x.2 i)
    rw [map_add, DFinsupp.add_apply, c.coordinate_d, sumMap_coordinate b c p hq]
  · change b.coordinates a (n+1+1) (-((S.complex a).d (n+1) (n+1+1) x.2)) i =
      -((F i).complex a).d (n+1) (n+1+1) (b.coordinates a (n+1) x.2 i)
    rw [map_neg, DFinsupp.neg_apply, b.coordinate_d]

theorem sumQuasiIsomorphism : SumQuasiIsomorphism.{u,v,w,j} := by
  classical
  intro k _ A I F G S T b c p hp
  let q : S ⟶ T := DG.IndexedSums.desc b fun i => p i ≫ c.inclusion i
  have hq (i : I) : b.inclusion i ≫ q = p i ≫ c.inclusion i := DG.IndexedSums.inclusion_desc b _ i
  refine ⟨q, (quasiIso_iff_cone_acyclic q).mpr ?_, hq⟩
  intro a n
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = n := ⟨n - 1, by omega⟩
  let L := (cone q).complex a
  change L.ExactAt (m + 1)
  rw [L.exactAt_iff' (i := m) (j := m + 1) (k := m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change L.d (m + 1) (m + 1 + 1) x = 0 at hx
  let support := (c.coordinates a (m+1) x.1).support ∪ (b.coordinates a (m+1+1) x.2).support
  have primitive (i : I) : ∃ y : ((cone (p i)).complex a).X m,
      ((cone (p i)).complex a).d m (m+1) y = coneEntry b c a (m+1) x i := by
    let C := (cone (p i)).complex a
    have h := (quasiIso_iff_cone_acyclic (p i)).mp (hp i) a (m+1)
    change C.ExactAt (m+1) at h
    rw [C.exactAt_iff' (i := m) (j := m + 1) (k := m + 1 + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at h
    refine h _ ?_
    change C.d (m + 1) (m + 1 + 1) (coneEntry b c a (m + 1) x i) = 0
    rw [← coneEntry_d b c p hq, hx]
    change (c.coordinates a (m+1+1) 0 i, b.coordinates a (m+1+1+1) 0 i) = (0, 0)
    simp
  choose y hy using primitive
  let y₁ : SumTerm G a m := DFinsupp.mk support (fun i => (y i).1)
  let y₂ : SumTerm F a (m+1) := DFinsupp.mk support (fun i => (y i).2)
  let v : L.X m := ((c.coordinates a m).symm y₁, (b.coordinates a (m+1)).symm y₂)
  have hv (i : I) :
      coneEntry b c a (m+1) (L.d m (m+1) v) i = coneEntry b c a (m+1) x i := by
    rw [coneEntry_d b c p hq]
    have ev : coneEntry b c a m v i = (y₁ i, y₂ i) := by
      change (c.coordinates a m ((c.coordinates a m).symm y₁) i,
        b.coordinates a (m+1) ((b.coordinates a (m+1)).symm y₂) i) = _
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [ev]
    by_cases hi : i ∈ support
    · rw [DFinsupp.mk_of_mem hi, DFinsupp.mk_of_mem hi]
      exact hy i
    · rw [DFinsupp.mk_of_notMem hi, DFinsupp.mk_of_notMem hi]
      have hs := Finset.notMem_union.mp hi
      change _ = (c.coordinates a (m+1) x.1 i, b.coordinates a (m+1+1) x.2 i)
      rw [DFinsupp.notMem_support_iff.mp hs.1, DFinsupp.notMem_support_iff.mp hs.2]
      exact map_zero _
  refine ⟨v, Prod.ext ?_ ?_⟩
  · apply (c.coordinates a (m+1)).injective
    exact DFinsupp.ext fun i => congrArg Prod.fst (hv i)
  · apply (b.coordinates a (m+1+1)).injective
    exact DFinsupp.ext fun i => congrArg Prod.snd (hv i)

end SumMap

section Localization

open Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.DerivedKProjective (homComparisonMap replacementIso)

private def cofanIsColimitOfBijective {C : Type*} [Category C] {I : Type*}
    {F : I → C} (c : Cofan F)
    (hc : ∀ X : C, Function.Bijective (fun g : c.pt ⟶ X => fun i => c.inj i ≫ g)) :
    IsColimit c :=
  Cofan.IsColimit.mk c
    (fun b => (Equiv.ofBijective _ (hc b.pt)).symm b.inj)
    (fun b i => congrFun ((Equiv.ofBijective _ (hc b.pt)).apply_symm_apply b.inj) i)
    (fun b _f hf => (hc b.pt).injective
      ((funext hf).trans ((Equiv.ofBijective _ (hc b.pt)).apply_symm_apply b.inj).symm))

variable {A : DGCategory.{u,v,w} k} {I : Type j}
  {F P : I → RightDGModule A} {S U : RightDGModule A}
  (h : HomotopyCategoryLaws A) (b : StrictSum F S) (a : StrictSum P U)

private theorem homComparison_inclusion (p : ∀ i, P i ⟶ F i) (q : U ⟶ S)
    (hp : ∀ i, IsQuasiIso (p i)) (hq : IsQuasiIso q)
    (hs : ∀ i, a.inclusion i ≫ q = p i ≫ b.inclusion i)
    (N : RightDGModule A) (g : h0Hom (homComplex U N)) (i : I) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    (derivedCofan h b).inj i ≫ homComparisonMap h q hq g =
      homComparisonMap h (p i) (hp i)
        (Basic.h0Comp (dgCategory A) g (homotopyClass (a.inclusion i))) := by
  let _ := Derived.homotopyCategory A h
  let _ := derivedCategoryInstance A h
  let L := Derived.quotient A h
  let e := replacementIso h q hq
  let eᵢ := replacementIso h (p i) (hp i)
  let Kfun := toHomotopyCategory A ⋙ L
  have hs' : eᵢ.hom ≫ L.map (homotopyClass (b.inclusion i)) =
      L.map (homotopyClass (a.inclusion i)) ≫ e.hom := by
    change Kfun.map (p i) ≫ Kfun.map (b.inclusion i) =
      Kfun.map (a.inclusion i) ≫ Kfun.map q
    rw [← Kfun.map_comp, ← Kfun.map_comp, hs]
  apply (cancel_epi eᵢ.hom).mp
  change eᵢ.hom ≫ L.map (homotopyClass (b.inclusion i)) ≫ e.inv ≫ L.map g =
    eᵢ.hom ≫ eᵢ.inv ≫ L.map (homotopyClass (a.inclusion i) ≫ g)
  rw [← Category.assoc eᵢ.hom, hs', Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc]
  exact (L.map_comp (homotopyClass (a.inclusion i)) g).symm

private def derivedCofanIsColimitOfResolutions (p : ∀ i, P i ⟶ F i) (q : U ⟶ S)
    (hp : ∀ i, IsQuasiIso (p i)) (hq : IsQuasiIso q)
    (hP : ∀ i, IsKProjective (P i)) (hU : IsKProjective U)
    (hs : ∀ i, a.inclusion i ≫ q = p i ≫ b.inclusion i) :
    letI := derivedCategoryInstance A h
    IsColimit (derivedCofan h b) := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  apply cofanIsColimitOfBijective
  intro X
  obtain ⟨N, rfl⟩ := (Localization.Construction.objEquiv
    (RightDGModule.quasiIsomorphisms A)).surjective X
  obtain ⟨e, he⟩ := (homFromStrictSum.{u,v,w,j} a N).2
  let l := homComparisonMap (N := N) h q hq
  let lᵢ (i : I) := homComparisonMap (N := N) h (p i) (hp i)
  have hl : Function.Bijective l := derivedHomComparison_bijective h q hq hU
  let E := Equiv.piCongrRight fun i => Equiv.ofBijective (lᵢ i)
    (derivedHomComparison_bijective h (p i) (hp i) (hP i))
  let restrictMap := fun g : (Derived.quotient A h).obj S ⟶ (Derived.quotient A h).obj N => fun i =>
    (derivedCofan h b).inj i ≫ g
  change Function.Bijective restrictMap
  apply (hl.of_comp_iff _).1
  have heq : restrictMap ∘ l = E ∘ e := by
    funext g i
    change (derivedCofan h b).inj i ≫ l g = lᵢ i (e g i)
    rw [he]
    exact homComparison_inclusion h b a p q hp hq hs N g i
  rw [heq]
  exact E.bijective.comp e.bijective

theorem nativeDerivedCoproduct : NativeDerivedCoproduct.{u,v,w,j} := by
  classical
  intro k _ A h I F S b
  choose P p hp using fun i =>
    unboundedSemiFreeResolutionInUniverse.{u,max v j,w} k A (F i)
  let H : Specs.DerivedFormalization.DG.IndexedSums.TermsSmall P :=
    fun _ _ => small_self _
  let U := DG.IndexedSums.sum P H
  let a := DG.IndexedSums.sumRealization P H
  obtain ⟨q, hq, hs⟩ := sumQuasiIsomorphism.{u,max v w j,w,j} a b p (fun i => (hp i).2.2)
  have hP (i : I) : IsKProjective (P i) := IsSemiFree.isKProjective (hp i).1
  have hU : IsKProjective U := IsKProjective.coproduct _ (DG.IndexedSums.isColimit a) hP
  exact ⟨⟨P, p, hp, U, a, q, hU, hq, hs⟩,
    ⟨derivedCofanIsColimitOfResolutions h b a p q (fun i => (hp i).2.2) hq hP hU hs⟩⟩

theorem originalDerivedCoproduct : OriginalDerivedCoproduct.{u,v,w,j,t} := by
  intro k _ A h I F
  let L := AmbientDerived.strictInput.{u,v,w,max j t} A
  let G := fun i => L.obj (F i)
  let H : Specs.DerivedFormalization.DG.IndexedSums.TermsSmall G := fun _ _ => small_self _
  exact ⟨DG.IndexedSums.sum G H, DG.IndexedSums.sumRealization G H,
    nativeDerivedCoproduct.{u,max v t,w,j} h (DG.IndexedSums.sumRealization G H)⟩

theorem g02SumComparison : G02SumComparison.{u,v,w} := by
  intro k _ A I F c hc S b
  let a := DG.IndexedSums.strictSumOfIsColimit hc
  obtain ⟨e, hi, he⟩ := DG.IndexedSums.strictComparison a b
  exact ⟨a, e, fun _ => rfl, hi, he⟩

end Localization

section Transition

open Derived (HomotopyCategoryLaws)
open DerivedCoefficientLift (Descent strictTransition)
open AmbientDerived (category strictInput)

variable {A : DGCategory.{u,v,w} k} {B : DGCategory.{u,v',w} k}
  {h : HomotopyCategoryLaws A} {h' : HomotopyCategoryLaws B}
  {T : RightDGModule A ⥤ RightDGModule B}
  {I : Type j} {F : I → RightDGModule A} {S : RightDGModule A}
  (d : Descent h h' T) (b : StrictSum F S)
  (c : StrictSum (fun i => T.obj (F i)) (T.obj S))

private theorem transition_inclusion (hc : ∀ i, c.inclusion i = T.map (b.inclusion i)) (i : I) :
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance B h'
    d.D.map ((derivedCofan h b).inj i) ≫ (d.representedIso S).hom =
      (d.representedIso (F i)).hom ≫ (derivedCofan h' c).inj i := by
  let _ := Derived.homotopyCategory A h
  let _ := Derived.homotopyCategory B h'
  let _ := derivedCategoryInstance A h
  let _ := derivedCategoryInstance B h'
  change d.D.map ((Derived.quotient A h).map (homotopyClass (b.inclusion i))) ≫
      (d.representedIso S).hom =
    (d.representedIso (F i)).hom ≫ (Derived.quotient B h').map (homotopyClass (c.inclusion i))
  have he := represented_naturality d (homotopyClass (b.inclusion i))
  erw [classMap_strict] at he
  rw [hc]
  exact he

section CofanTransport

variable {C E : Type*} [Category C] [Category E] {J : Type*} {G : J → C} {H : J → E}
  {l : Cofan G} {r : Cofan H} (L : C ⥤ E) (e : L.obj l.pt ≅ r.pt)
  (eᵢ : ∀ i, L.obj (G i) ≅ H i)
  (he : ∀ i, L.map (l.inj i) ≫ e.hom = (eᵢ i).hom ≫ r.inj i)
  (hr : IsColimit r)

include he in
/-- The injections determine the image of a coproduct descent map. -/
private theorem map_eq_desc_of_fac {X : C} (f : l.pt ⟶ X) (g : ∀ i, G i ⟶ X)
    (hg : ∀ i, l.inj i ≫ f = g i) :
    L.map f = e.hom ≫ Cofan.IsColimit.desc hr (fun i => (eᵢ i).inv ≫ L.map (g i)) := by
  apply (cancel_epi e.inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply Cofan.IsColimit.hom_ext hr
  intro i
  have hi := congrArg (fun m => (eᵢ i).inv ≫ m ≫ e.inv) (he i)
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] at hi
  rw [Cofan.IsColimit.fac, ← Category.assoc, ← hi, Category.assoc, ← L.map_comp, hg]

/-- Full faithfulness restricts the upper universal property to lower targets. -/
private def reflectCofan (ff : L.FullyFaithful) : IsColimit l := by
  let lift {X : C} (g : ∀ i, G i ⟶ X) :=
    Cofan.IsColimit.desc hr (fun i => (eᵢ i).inv ≫ L.map (g i))
  refine Cofan.IsColimit.mk _ (fun a => ff.preimage (e.hom ≫ lift a.inj)) ?_ ?_
  · intro a i
    apply ff.map_injective
    rw [L.map_comp, ff.map_preimage, ← Category.assoc, he, Category.assoc, Cofan.IsColimit.fac,
      Iso.hom_inv_id_assoc]
  · intro a f hf
    apply ff.map_injective
    rw [ff.map_preimage]
    exact map_eq_desc_of_fac L e eᵢ he hr f a.inj hf

end CofanTransport

private def reflectDerivedCofan (hc : ∀ i, c.inclusion i = T.map (b.inclusion i))
    (hd : d.FullyFaithful)
    (upper : letI := derivedCategoryInstance B h'; IsColimit (derivedCofan h' c)) :
    letI := derivedCategoryInstance A h
    IsColimit (derivedCofan h b) := by
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  exact reflectCofan (l := derivedCofan h b) (r := derivedCofan h' c)
    d.D (d.representedIso S) (fun i => d.representedIso (F i))
    (transition_inclusion d b c hc) upper (Classical.choice hd.2)

private theorem transitionMaps_of_inclusions (hc : ∀ i, c.inclusion i = T.map (b.inclusion i)) :
    TransitionMaps d b c := by
  let _ := derivedCategoryInstance A h
  let _ := derivedCategoryInstance B h'
  refine ⟨transition_inclusion d b c hc, ?_⟩
  intro lower upper X f
  exact map_eq_desc_of_fac (l := derivedCofan h b) (r := derivedCofan h' c)
    d.D (d.representedIso S) (fun i => d.representedIso (F i))
    (transition_inclusion d b c hc) upper _ f (fun i => Cofan.IsColimit.fac lower f i)

theorem nativeExistingDerivedCoproduct : NativeExistingDerivedCoproduct.{u,v,w,j} := by
  intro k _ A h I F S b
  let B := CoefficientLift.liftCategory.{u,max v w,w,j} A
  have h' : HomotopyCategoryLaws B := ⟨instCategoryK B, rfl⟩
  obtain ⟨⟨d, hd, _, _⟩, _⟩ := DG.DerivedCoefficientLift.nativeDerivedCoefficientTransition.{u,v,w,j}
    A h h'
  let c := DG.IndexedSums.liftStrictSum.{u,max v w,w,j,j} b
  obtain ⟨upper⟩ := (nativeDerivedCoproduct.{u,v,w,j} h' c).2
  exact ⟨reflectDerivedCofan d b c (fun _ => rfl) hd upper⟩

theorem ambientCoproductTransition : AmbientCoproductTransition.{u,v,w,j,t,s} := by
  intro k _ A h h' I F S b
  obtain ⟨d, hd, _, _⟩ := DG.DerivedCoefficientLift.derivedCoefficientTransition.{u,v,w,t,s} A h h'
  let c := transitionSum.{u,v,w,t,s,j} b
  have hi : ∀ i, c.inclusion i = (strictTransition.{u,v,w,t,s} A).map (b.inclusion i) := fun _ => rfl
  obtain ⟨upper⟩ := nativeExistingDerivedCoproduct.{u,max v t s,w,j} h' c
  exact ⟨d, c, hd, hi, fun _ _ _ _ => rfl,
    ⟨reflectDerivedCofan d b c hi hd upper⟩, ⟨upper⟩,
    transitionMaps_of_inclusions d b c hi⟩

theorem originalExistingDerivedCoproduct : OriginalExistingDerivedCoproduct.{u,v,w,j,t} := by
  intro k _ A h I F S b
  let c := DG.IndexedSums.liftStrictSum.{u,v,w,j,max w t} b
  exact ⟨c, fun _ => rfl, fun _ _ _ _ => rfl,
    nativeExistingDerivedCoproduct.{u,max v t,w,j} h c⟩

end Transition

end
end DerivedFormalization.RightDGModule
