import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectHomBaseChange

/-! Transport of the ordinary Amitsur diagram through changes of ring representatives. -/

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct BigOperators

namespace DerivedFormalization.Descent.AmitsurRingTransport

open Specs.DerivedFormalization.Cochains (compValue qValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.Descent.AmitsurRingTransport
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (scalarExtension extend extendCochain comparison)

noncomputable section

universe u v w t x y i j

attribute [local instance] HasDerivedCategory.standard

section Localization

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (e : R ≃+* R')

private theorem derivedIsEquivalence :
    (changeDerivedRepresentative.{u,v,t} e).IsEquivalence := by
  let E := moduleChange.{u,v,t} e
  let D := CategoryTheory.Equivalence.mk (changeDerivedRepresentative.{u,v,t} e)
    E.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso (ModuleCat.{t} R)).symm ≪≫
      (Specs.DerivedFormalization.CochainRingTransport.derivedComp E.unitIso.symm).symm)
    (Specs.DerivedFormalization.CochainRingTransport.derivedComp E.counitIso ≪≫
      Functor.mapDerivedCategoryIdIso (ModuleCat.{t} R'))
  exact D.isEquivalence_functor

private theorem originalModel (L' : compValue.{t} R') :
    ∃ (L : compValue.{t} R) (c : (changeRepresentative.{u,v,t} e).obj L ≅ L')
      (a : (changeDerivedRepresentative.{u,v,t} e).obj ((qValue R).obj L) ≅ (qValue R').obj L'),
      a.hom = ((quotientSquare e).app L).hom ≫ (qValue R').map c.hom := by
  let E := (moduleChange.{u,v,t} e).mapHomologicalComplex (.up ℤ)
  let L := E.inverse.obj L'
  let c : (changeRepresentative.{u,v,t} e).obj L ≅ L' := E.counitIso.app L'
  exact ⟨L, c, (quotientSquare e).app L ≪≫ (qValue R').mapIso c, rfl⟩

end Localization

section Extension

variable {R : Type u} {S : Type w} {R' S' : Type v}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable (e : R ≃+* R') (d : S ≃+* S')
variable (h : ∀ r : R, d (algebraMap R S r) = algebraMap R' S' (e r))

local instance {T U : Type*} [Ring T] [Ring U] (a : T ≃+* U) :
    RingHomInvPair a.toRingHom a.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv a

private def semilinearAlgebra : S ≃ₛₗ[e.toRingHom] S' where
  __ := d
  map_smul' r s := by
    change d (r • s) = e r • d s
    simp only [Algebra.smul_def, map_mul, h]

private def semilinearCarrier (M : ModuleCat.{t} R) :
    M ≃ₛₗ[e.toRingHom] (moduleChange.{u,v,t} e).functor.obj M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change r • m = e.symm (e r) • m
    rw [RingEquiv.symm_apply_apply]

include h

private def extensionTerm (M : ModuleCat.{max w v t} R) :
    (moduleChange.{w,v,max w v t} d).functor.obj
        ((scalarExtension.{u,w,max w v t} R S).obj M) ≃ₗ[S']
      (scalarExtension.{v,v,max w v t} R' S').obj
        ((moduleChange.{u,v,max w v t} e).functor.obj M) := by
  let E := TensorProduct.congr (semilinearAlgebra e d h) (semilinearCarrier e M)
  let F : (moduleChange.{w,v,max w v t} d).functor.obj
        ((scalarExtension.{u,w,max w v t} R S).obj M) →ₗ[S']
      (scalarExtension.{v,v,max w v t} R' S').obj
        ((moduleChange.{u,v,max w v t} e).functor.obj M) :=
    { toFun := fun z => E z
      map_add' := fun a b => E.map_add a b
      map_smul' := by
        intro r z
        change E (d.symm r • (show S ⊗[R] M from z)) = r • E z
        induction z using TensorProduct.inductionOn with
        | add a b ha hb => rw [smul_add, E.map_add, E.map_add, smul_add, ha, hb]
        | tmul s z =>
          change d (d.symm r * s) ⊗ₜ[R'] _ = (r * d s) ⊗ₜ[R'] _
          rw [map_mul, RingEquiv.apply_symm_apply] }
  exact LinearEquiv.ofBijective F E.bijective

private def extensionModuleIso :
    scalarExtension.{u,w,max w v t} R S ⋙ (moduleChange.{w,v,max w v t} d).functor ≅
    (moduleChange.{u,v,max w v t} e).functor ⋙ scalarExtension.{v,v,max w v t} R' S' :=
  NatIso.ofComponents (fun M => (extensionTerm.{u,v,w,t} e d h M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ _ _).symm)
    | tmul s m => rfl)

private def extensionIso :
    extend.{u,w,max w v t} R S ⋙ changeRepresentative.{w,v,max w v t} d ≅
    changeRepresentative.{u,v,max w v t} e ⋙ extend.{v,v,max w v t} R' S' :=
  NatIso.ofComponents
    (fun M => HomologicalComplex.Hom.isoOfComponents
      (fun n => (extensionModuleIso.{u,v,w,t} e d h).app (M.X n))
      (fun n m _ => ((extensionModuleIso.{u,v,w,t} e d h).hom.naturality (M.d n m)).symm))
    (fun f => HomologicalComplex.hom_ext _ _
      (fun n => (extensionModuleIso.{u,v,w,t} e d h).hom.naturality (f.f n)))

@[simp] private theorem extensionIso_tmul (M : compValue.{max w v t} R)
    (n : ℤ) (s : S) (z : M.X n) :
    ((extensionIso.{u,v,w,t} e d h).hom.app M).f n (s ⊗ₜ[R] z) =
      d s ⊗ₜ[R'] (show ((changeRepresentative.{u,v,max w v t} e).obj M).X n from z) :=
  rfl

end Extension

section Hom

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (e : R ≃+* R')

private def cochainEquiv (P X : compValue.{t} R) (n : ℤ) :
    ((changeRepresentative.{u,v,t} e).obj (internalHomValue P X)).X n ≃ₗ[R']
      Cochain ((changeRepresentative.{u,v,t} e).obj P)
        ((changeRepresentative.{u,v,t} e).obj X) n := by
  let F := (moduleChange.{u,v,t} e).functor
  let m : ((changeRepresentative.{u,v,t} e).obj (internalHomValue P X)).X n →ₗ[R']
      Cochain ((changeRepresentative.{u,v,t} e).obj P)
        ((changeRepresentative.{u,v,t} e).obj X) n :=
    { toFun := fun z => Cochain.map z F
      map_add' := fun a b => Cochain.map_add a b F
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro a b h
        apply ModuleCat.hom_ext
        ext p
        rfl }
  refine LinearEquiv.ofBijective m ⟨?_, ?_⟩
  · intro f g h
    apply Cochain.ext
    intro a b hab
    exact F.map_injective (congrArg (fun z => Cochain.v z a b hab) h)
  · intro z
    refine ⟨Cochain.mk (fun a b h => F.preimage (z.v a b h)), ?_⟩
    apply Cochain.ext
    intro a b h
    exact F.map_preimage _

private def homIso (P X : compValue.{t} R) :
    (changeRepresentative.{u,v,t} e).obj (internalHomValue P X) ≅
      internalHomValue ((changeRepresentative.{u,v,t} e).obj P)
        ((changeRepresentative.{u,v,t} e).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainEquiv e P X n).toModuleIso)
    (by
      intro a b _
      apply ModuleCat.hom_ext
      ext z : 1
      exact (δ_map a b z (moduleChange.{u,v,t} e).functor).symm)

private theorem homIso_eval (P X : compValue.{t} R) (n a b : ℤ) (h : a + n = b)
    (z : Cochain P X n) (p : P.X a) :
    (((homIso e P X).hom.f n z).v a b h) p = z.v a b h p :=
  rfl

private theorem homMap_eval {P P' X X' : compValue.{t} R} (a : P' ⟶ P) (b : X ⟶ X')
    {n l m : ℤ} (h : l + n = m) (z : Cochain P X n) (p : P'.X l) :
    ((internalHomMapValue a b).f n z).v l m h p = b.f m (z.v l m h (a.f l p)) :=
  DerivedFormalization.internalHomMap_apply a b h z p

private theorem homIso_natural {P P' X X' : compValue.{t} R}
    (a : P' ⟶ P) (b : X ⟶ X') :
    let F := changeRepresentative.{u,v,t} e
    F.map (internalHomMapValue a b) ≫ (homIso e P' X').hom =
      (homIso e P X).hom ≫ internalHomMapValue (F.map a) (F.map b) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext z : 1
  let F := (moduleChange.{u,v,t} e).functor
  change (((Cochain.ofHom a).comp (show Cochain P X n from z) (zero_add n)).comp
    (Cochain.ofHom b) (add_zero n)).map F =
      ((Cochain.ofHom ((changeRepresentative e).map a)).comp
        ((show Cochain P X n from z).map F) (zero_add n)).comp
          (Cochain.ofHom ((changeRepresentative e).map b)) (add_zero n)
  rw [Cochain.map_comp, Cochain.map_comp, Cochain.map_ofHom, Cochain.map_ofHom]

end Hom

section TensorRings

variable {A B C A' B' C' : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra A B] [Algebra A C] [Algebra A' B'] [Algebra A' C']

private theorem inverse_algebraMap (e : A ≃+* A') (d : C ≃+* C')
    (h : ∀ a, d (algebraMap A C a) = algebraMap A' C' (e a)) (a : A') :
    d.symm (algebraMap A' C' a) = algebraMap A C (e.symm a) := by
  apply d.injective
  rw [d.apply_symm_apply, h, e.apply_symm_apply]

variable (e : A ≃+* A') (b : B ≃+* B') (c : C ≃+* C')
variable (hb : ∀ a, b (algebraMap A B a) = algebraMap A' B' (e a))
variable (hc : ∀ a, c (algebraMap A C a) = algebraMap A' C' (e a))

private def tensorRingHom : B ⊗[A] C →+* B' ⊗[A'] C' :=
  Algebra.TensorProduct.mapRingHom e.toRingHom b.toRingHom c.toRingHom
    (RingHom.ext hb) (RingHom.ext hc)

@[simp] private theorem tensorRingHom_tmul (z : B) (s : C) :
    tensorRingHom e b c hb hc (z ⊗ₜ[A] s) = b z ⊗ₜ[A'] c s :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ _ _

private theorem tensorRingHom_leftInverse :
    Function.LeftInverse (tensorRingHom e.symm b.symm c.symm
      (inverse_algebraMap e b hb) (inverse_algebraMap e c hc)) (tensorRingHom e b c hb hc) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul z s => simp only [tensorRingHom_tmul, RingEquiv.symm_apply_apply]
  | add z s hz hs => rw [map_add, map_add, hz, hs]

private def tensorRingEquiv : B ⊗[A] C ≃+* B' ⊗[A'] C' :=
  { tensorRingHom e b c hb hc with
    invFun := tensorRingHom e.symm b.symm c.symm
      (inverse_algebraMap e b hb) (inverse_algebraMap e c hc)
    left_inv := tensorRingHom_leftInverse e b c hb hc
    right_inv := tensorRingHom_leftInverse e.symm b.symm c.symm
      (inverse_algebraMap e b hb) (inverse_algebraMap e c hc) }

@[simp] private theorem tensorRingEquiv_tmul (z : B) (s : C) :
    tensorRingEquiv e b c hb hc (z ⊗ₜ[A] s) = b z ⊗ₜ[A'] c s :=
  tensorRingHom_tmul e b c hb hc z s

include hc in
private theorem faithfullyFlat_of_algebra_equiv [Module.FaithfullyFlat A C] :
    Module.FaithfullyFlat A' C' := by
  let : Algebra A A' := e.toRingHom.toAlgebra
  let d := tensorRingEquiv e (RingEquiv.refl A') c (fun _ => rfl) hc
  let d' : A' ⊗[A] C ≃ₐ[A'] A' ⊗[A'] C' := AlgEquiv.ofRingEquiv (f := d) (by
    intro a
    change d (a ⊗ₜ[A] (1 : C)) = a ⊗ₜ[A'] (1 : C')
    have hd := tensorRingEquiv_tmul (B := A') (B' := A') e (RingEquiv.refl A') c
      (fun _ => rfl) hc a (1 : C)
    exact hd.trans (by rw [map_one]; rfl))
  exact Module.FaithfullyFlat.of_linearEquiv _ (A' ⊗[A] C)
    (d'.toLinearEquiv.trans (TensorProduct.lid A' C')).symm

end TensorRings

section Powers

open AmitsurAlgebrasSpec (tensorPower factor)
open DerivedFormalization.Descent.AmitsurAlgebras (liftFactors_factor liftFactors_tprod map_factor)

variable {A C A' C' : Type*}
  [CommRing A] [CommRing C] [CommRing A'] [CommRing C'] [Algebra A C] [Algebra A' C']

private def pulledFactor (e : A ≃+* A') (c : C ≃+* C')
    (hc : ∀ a, c (algebraMap A C a) = algebraMap A' C' (e a))
    {n : ℕ} (a : Fin n) :
    letI : Algebra A (tensorPower A' C' n) :=
      ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
    C →ₐ[A] tensorPower A' C' n := by
  let : Algebra A (tensorPower A' C' n) :=
    ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
  exact { (factor A' C' a).toRingHom.comp c.toRingHom with
    commutes' := fun r => by
      change factor A' C' a (c (algebraMap A C r)) = algebraMap A' _ (e r)
      rw [hc, AlgHom.commutes] }

variable (e : A ≃+* A') (c : C ≃+* C')
  (hc : ∀ a, c (algebraMap A C a) = algebraMap A' C' (e a))

private def powerRingHom (n : ℕ) : tensorPower A C n →+* tensorPower A' C' n :=
  letI : Algebra A (tensorPower A' C' n) :=
    ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
  (AmitsurAlgebrasSpec.liftFactors (pulledFactor e c hc)).toRingHom

@[simp] private theorem powerRingHom_factor {n : ℕ} (a : Fin n) (s : C) :
    powerRingHom e c hc n (factor A C a s) = factor A' C' a (c s) := by
  let : Algebra A (tensorPower A' C' n) :=
    ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
  exact liftFactors_factor (pulledFactor e c hc) a s

private theorem powerRingHom_algebraMap (n : ℕ) (a : A) :
    powerRingHom e c hc n (algebraMap A (tensorPower A C n) a) =
      algebraMap A' (tensorPower A' C' n) (e a) := by
  let : Algebra A (tensorPower A' C' n) :=
    ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
  exact (AmitsurAlgebrasSpec.liftFactors (pulledFactor e c hc)).commutes a

private theorem prod_factor_eq_tprod {n : ℕ} (z : Fin n → C) :
    ∏ a, factor A C a (z a) = PiTensorProduct.tprod A z := by
  have h : AmitsurAlgebrasSpec.liftFactors (factor A C (n := n)) =
      AlgHom.id A (tensorPower A C n) := by
    apply PiTensorProduct.algHom_ext
    intro a
    apply AlgHom.ext
    intro s
    exact liftFactors_factor (factor A C) a s
  rw [← liftFactors_tprod (factor A C)]
  exact DFunLike.congr_fun h _

@[simp] private theorem powerRingHom_tprod {n : ℕ} (z : Fin n → C) :
    powerRingHom e c hc n (PiTensorProduct.tprod A z) =
      PiTensorProduct.tprod A' (fun a => c (z a)) := by
  let : Algebra A (tensorPower A' C' n) :=
    ((algebraMap A' (tensorPower A' C' n)).comp e.toRingHom).toAlgebra
  exact (liftFactors_tprod (pulledFactor e c hc) z).trans (prod_factor_eq_tprod _)

private theorem powerRingHom_leftInverse (n : ℕ) :
    Function.LeftInverse (powerRingHom e.symm c.symm (inverse_algebraMap e c hc) n)
      (powerRingHom e c hc n) := by
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a z =>
    simp only [Algebra.smul_def, map_mul, powerRingHom_algebraMap, powerRingHom_tprod,
      RingEquiv.symm_apply_apply]
  | add z s hz hs => rw [map_add, map_add, hz, hs]

private def powerRingEquiv (n : ℕ) : tensorPower A C n ≃+* tensorPower A' C' n :=
  { powerRingHom e c hc n with
    invFun := powerRingHom e.symm c.symm (inverse_algebraMap e c hc) n
    left_inv := powerRingHom_leftInverse e c hc n
    right_inv := powerRingHom_leftInverse e.symm c.symm (inverse_algebraMap e c hc) n }

@[simp] private theorem powerRingEquiv_factor {n : ℕ} (a : Fin n) (s : C) :
    powerRingEquiv e c hc n (factor A C a s) = factor A' C' a (c s) :=
  powerRingHom_factor e c hc a s

@[simp] private theorem powerRingEquiv_tprod {n : ℕ} (z : Fin n → C) :
    powerRingEquiv e c hc n (PiTensorProduct.tprod A z) =
      PiTensorProduct.tprod A' (fun a => c (z a)) :=
  powerRingHom_tprod e c hc z

private theorem powerRingEquiv_algebraMap (n : ℕ) (a : A) :
    powerRingEquiv e c hc n (algebraMap A (tensorPower A C n) a) =
      algebraMap A' (tensorPower A' C' n) (e a) :=
  powerRingHom_algebraMap e c hc n a

private theorem powerRingEquiv_map {m n : ℕ} (f : Fin m → Fin n) (z : tensorPower A C m) :
    powerRingEquiv e c hc n (AmitsurAlgebrasSpec.map f z) =
      AmitsurAlgebrasSpec.map f (powerRingEquiv e c hc m z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a z =>
    simp only [Algebra.smul_def, map_mul, powerRingEquiv_algebraMap, AlgHom.commutes]
    congr 1
    rw [← prod_factor_eq_tprod z]
    simp only [map_prod, powerRingEquiv_factor]
    change (∏ a, powerRingEquiv e c hc n
      (DerivedFormalization.Descent.AmitsurAlgebras.map f
        (DerivedFormalization.Descent.AmitsurAlgebras.factor A C a (z a)))) =
      ∏ a, DerivedFormalization.Descent.AmitsurAlgebras.map f
        (DerivedFormalization.Descent.AmitsurAlgebras.factor A' C' a (c (z a)))
    apply Finset.prod_congr rfl
    intro a _
    exact (congrArg (powerRingEquiv e c hc n) (map_factor f a (z a))).trans
      ((powerRingEquiv_factor e c hc (f a) (z a)).trans (map_factor f a (c (z a))).symm)
  | add z s hz hs => rw [map_add, map_add, map_add, map_add, hz, hs]

end Powers

section Conjugation

variable {R : Type u} [CommRing R]
variable {P P' X X' : compValue.{t} R}

@[simp] private theorem iso_inv_hom_apply (a : P ≅ P') (n : ℤ) (z : P'.X n) :
    a.hom.f n (a.inv.f n z) = z := by
  have h := HomologicalComplex.congr_hom a.inv_hom_id n
  exact ConcreteCategory.congr_hom h z

@[simp] private theorem iso_hom_inv_apply (a : P ≅ P') (n : ℤ) (z : P.X n) :
    a.inv.f n (a.hom.f n z) = z :=
  iso_inv_hom_apply a.symm n z

private def homConjugation (a : P ≅ P') (b : X ≅ X') :
    internalHomValue P X ≅ internalHomValue P' X' where
  hom := internalHomMapValue a.inv b.hom
  inv := internalHomMapValue a.hom b.inv
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro l m h
    apply ModuleCat.hom_ext
    ext p
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homMap_eval,
      iso_hom_inv_apply, HomologicalComplex.id_f, ModuleCat.id_apply]
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro l m h
    apply ModuleCat.hom_ext
    ext p
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homMap_eval,
      iso_inv_hom_apply, HomologicalComplex.id_f, ModuleCat.id_apply]

end Conjugation

section Columns


variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {S : ℕ → Type w} {S' : ℕ → Type v}
variable [∀ p, CommRing (S p)] [∀ p, CommRing (S' p)]
variable [∀ p, Algebra R (S p)] [∀ p, Algebra R' (S' p)]
variable (e : R ≃+* R') (d : ∀ p, S p ≃+* S' p)
variable (h : ∀ p (r : R), d p (algebraMap R (S p) r) = algebraMap R' (S' p) (e r))

private def homColumnIso (p : ℕ) (P X : compValue.{max u v w t} R) :
    let E := extend.{u,w,max u v w t} R (S p)
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let F := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (d p)).obj (internalHomValue (E.obj P) (E.obj X)) ≅
      internalHomValue (E'.obj (F.obj P)) (E'.obj (F.obj X)) :=
  let E := extend.{u,w,max u v w t} R (S p)
  let a := extensionIso.{u,v,w,max u t} e (d p) (h p)
  homIso (d p) (E.obj P) (E.obj X) ≪≫ homConjugation (a.app P) (a.app X)

set_option backward.isDefEq.respectTransparency false in
private theorem homColumnIso_eval (p : ℕ) (P X : compValue.{max u v w t} R)
    (n l m : ℤ) (hlm : l + n = m)
    (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P)
      ((extend.{u,w,max u v w t} R (S p)).obj X) n)
    (x : ((extend.{u,w,max u v w t} R (S p)).obj P).X l) :
    (((homColumnIso.{u,v,w,t} e d h p P X).hom.f n z).v l m hlm)
      (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app P).f l x) =
      ((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app X).f m (z.v l m hlm x) := by
  let E := extend.{u,w,max u v w t} R (S p)
  let a := extensionIso.{u,v,w,max u t} e (d p) (h p)
  change ((internalHomMapValue (a.inv.app P) (a.hom.app X)).f n
      ((homIso (d p) (E.obj P) (E.obj X)).hom.f n z)).v l m hlm
        ((a.hom.app P).f l x) = _
  rw [homMap_eval]
  have hx := iso_hom_inv_apply ((extensionIso.{u,v,w,max u t} e (d p) (h p)).app P) l
    (show ((changeRepresentative.{w,v,max u v w t} (d p)).obj
      ((extend.{u,w,max u v w t} R (S p)).obj P)).X l from x)
  change ((extensionIso.{u,v,w,max u t} e (d p) (h p)).inv.app P).f l
    (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app P).f l x) = x at hx
  rw [hx]
  rfl

variable
    (f : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S p →ₐ[R] S q)
    (g : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S' p →ₐ[R'] S' q)
    (hfg : ∀ {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (s : S p),
      d q (f a s) = g a (d p s))

include hfg in
set_option backward.isDefEq.respectTransparency false in
private theorem extensionIso_column {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (X : compValue.{max u v w t} R) (n : ℤ) (z : ((extend.{u,w,max u v w t} R (S p)).obj X).X n) :
    ((extensionIso.{u,v,w,max u t} e (d q) (h q)).hom.app X).f n ((scalarColumnMap (f a) X).f n z) =
      (scalarColumnMap (g a) ((changeRepresentative.{u,v,max u v w t} e).obj X)).f n
        (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app X).f n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    rw [changeCoefficients_apply R (S p) (S q) (f a), extensionIso_tmul, extensionIso_tmul,
      changeCoefficients_apply R' (S' p) (S' q) (g a), hfg a s]
  | add z s hz hs =>
    simp only [map_add, hz, hs]

private theorem apply_extensionIso_natural (p : ℕ) {X Y : compValue.{max u v w t} R}
    (a : X ⟶ Y) (n : ℤ) (x : ((extend.{u,w,max u v w t} R (S p)).obj X).X n) :
    ((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app Y).f n (((extend.{u,w,max u v w t} R (S p)).map a).f n x) =
      ((extend.{v,v,max u v w t} R' (S' p)).map ((changeRepresentative.{u,v,max u v w t} e).map a)).f n
        (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app X).f n x) := by
  have en := HomologicalComplex.congr_hom ((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.naturality a) n
  exact ConcreteCategory.congr_hom en x

set_option backward.isDefEq.respectTransparency false in
private theorem homColumnIso_natural (p : ℕ) {P P' X X' : compValue.{max u v w t} R}
    (a : P' ⟶ P) (b : X ⟶ X') :
    let E := extend.{u,w,max u v w t} R (S p)
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let F := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (d p)).map
        (internalHomMapValue (E.map a) (E.map b)) ≫ (homColumnIso.{u,v,w,t} e d h p P' X').hom =
      (homColumnIso.{u,v,w,t} e d h p P X).hom ≫ internalHomMapValue (E'.map (F.map a)) (E'.map (F.map b)) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext z : 1
  apply Cochain.ext
  intro l m hlm
  apply ModuleCat.hom_ext
  ext p'
  let E := extend.{u,w,max u v w t} R (S p)
  let E' := extend.{v,v,max u v w t} R' (S' p)
  let F := changeRepresentative.{u,v,max u v w t} e
  let c := extensionIso.{u,v,w,max u t} e (d p) (h p)
  let z₀ : Cochain (E.obj P) (E.obj X) n := z
  let x : (E.obj P').X l := (c.inv.app P').f l p'
  have hx : (c.hom.app P').f l x = p' := iso_inv_hom_apply (c.app P') l p'
  change ((homColumnIso.{u,v,w,t} e d h p P' X').hom.f n
      ((internalHomMapValue (E.map a) (E.map b)).f n z₀)).v l m hlm p' =
    ((internalHomMapValue (E'.map (F.map a)) (E'.map (F.map b))).f n
      ((homColumnIso.{u,v,w,t} e d h p P X).hom.f n z₀)).v l m hlm p'
  rw [← hx, homColumnIso_eval, homMap_eval, homMap_eval,
    ← apply_extensionIso_natural, homColumnIso_eval, apply_extensionIso_natural]

set_option backward.isDefEq.respectTransparency false in
private theorem extendedCochain_ext {K : Type*} {T : Type*} [CommRing K] [CommRing T] [Algebra K T]
    {P X : compValue.{t} K} {n : ℤ}
    {a b : Cochain ((extend K T).obj P) ((extend K T).obj X) n}
    (heval : ∀ l m (hlm : l + n = m) (z : P.X l),
      a.v l m hlm ((1 : T) ⊗ₜ[K] z) = b.v l m hlm ((1 : T) ⊗ₜ[K] z)) :
    a = b := by
  apply Cochain.ext
  intro l m hlm
  apply ModuleCat.hom_ext
  change (a.v l m hlm).hom = (b.v l m hlm).hom
  exact TensorProduct.AlgebraTensorModule.ext (A := T) (P := T ⊗[K] X.X m) (by
    intro s z
    rw [show s ⊗ₜ[K] z = s • ((1 : T) ⊗ₜ[K] z) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    let a₀ : T ⊗[K] P.X l →ₗ[T] T ⊗[K] X.X m := (a.v l m hlm).hom
    let b₀ : T ⊗[K] P.X l →ₗ[T] T ⊗[K] X.X m := (b.v l m hlm).hom
    change a₀ (s • ((1 : T) ⊗ₜ[K] z)) = b₀ (s • ((1 : T) ⊗ₜ[K] z))
    exact (a₀.map_smul s _).trans
      ((congrArg (s • ·) (heval l m hlm z)).trans (b₀.map_smul s _).symm))

private theorem extendCochain_eval {K T : Type*} [CommRing K] [CommRing T] [Algebra K T]
    {P X : compValue.{t} K} {n l m : ℤ} (hlm : l + n = m) (z : Cochain P X n) (s : T)
    (a : P.X l) :
    (extendCochain T n z).v l m hlm (s ⊗ₜ[K] a) = s ⊗ₜ[K] z.v l m hlm a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem homColumnIso_augmentation (p : ℕ) (P X : compValue.{max u v w t} R)
    (n : ℤ) (z : Cochain P X n) :
    (homColumnIso.{u,v,w,t} e d h p P X).hom.f n (extendCochain (S p) n z) =
      extendCochain (S' p) n ((homIso e P X).hom.f n z) := by
  apply extendedCochain_ext
  intro l m hlm a
  let a₀ : P.X l := a
  have ha : ((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app P).f l ((1 : S p) ⊗ₜ[R] a₀) =
      (1 : S' p) ⊗ₜ[R'] a := by
    rw [extensionIso_tmul, map_one]
  rw [← ha, homColumnIso_eval, extendCochain_eval, extensionIso_tmul, map_one, ha,
    extendCochain_eval, homIso_eval]

set_option backward.isDefEq.respectTransparency false in
private theorem homColumnIso_baseChange (p : ℕ) (P X : compValue.{max u v w t} R) :
    (changeRepresentative.{w,v,max u v w t} (d p)).map (comparison (S p) P X) ≫ (homColumnIso.{u,v,w,t} e d h p P X).hom =
      (extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app (internalHomValue P X) ≫ (extend.{v,v,max u v w t} R' (S' p)).map (homIso e P X).hom ≫
        comparison (S' p) ((changeRepresentative.{u,v,max u v w t} e).obj P) ((changeRepresentative.{u,v,max u v w t} e).obj X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext v : 1
  let v₀ : S p ⊗[R] Cochain P X n := v
  change (homColumnIso.{u,v,w,t} e d h p P X).hom.f n ((comparison (S p) P X).f n v₀) =
    (comparison (S' p) ((changeRepresentative.{u,v,max u v w t} e).obj P) ((changeRepresentative.{u,v,max u v w t} e).obj X)).f n
      (((extend.{v,v,max u v w t} R' (S' p)).map (homIso e P X).hom).f n (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app (internalHomValue P X)).f n v₀))
  induction v₀ using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s z =>
    rw [extensionIso_tmul, Specs.DerivedFormalization.Descent.PerfectHomBaseChange.extend_map_tmul]
    apply extendedCochain_ext
    intro l m hlm a
    let a₀ : P.X l := a
    have ha : ((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app P).f l ((1 : S p) ⊗ₜ[R] a₀) =
        (1 : S' p) ⊗ₜ[R'] a := by
      rw [extensionIso_tmul, map_one]
    rw [← ha, homColumnIso_eval, homBaseChange_apply, extensionIso_tmul, map_mul, map_one, ha,
      homBaseChange_apply, homIso_eval]

include hfg in
set_option backward.isDefEq.respectTransparency false in
private theorem homColumnIso_cofaces {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (P X : compValue.{max u v w t} R) (n : ℤ)
    (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P) ((extend.{u,w,max u v w t} R (S p)).obj X) n) :
    (homColumnIso.{u,v,w,t} e d h q P X).hom.f n ((homColumnMap (f a) P X).f n z) =
      (homColumnMap (g a) ((changeRepresentative.{u,v,max u v w t} e).obj P)
        ((changeRepresentative.{u,v,max u v w t} e).obj X)).f n
          ((homColumnIso.{u,v,w,t} e d h p P X).hom.f n z) := by
  apply extendedCochain_ext
  intro l m hlm x
  let x₀ : P.X l := x
  let y : ((extend.{u,w,max u v w t} R (S p)).obj P).X l := (1 : S p) ⊗ₜ[R] x₀
  have hy : ((extensionIso.{u,v,w,max u t} e (d q) (h q)).hom.app P).f l ((scalarColumnMap (f a) P).f l y) =
      (1 : S' q) ⊗ₜ[R'] x := by
    change ((extensionIso.{u,v,w,max u t} e (d q) (h q)).hom.app P).f l
      ((scalarColumnMap (f a) P).f l ((1 : S p) ⊗ₜ[R] x₀)) = _
    rw [changeCoefficients_apply R (S p) (S q) (f a), map_one, extensionIso_tmul, map_one]
  rw [← hy, homColumnIso_eval]
  rw [show ((homColumnMap (f a) P X).f n z).v l m hlm ((scalarColumnMap (f a) P).f l y) =
    (scalarColumnMap (f a) X).f m (z.v l m hlm y) from
      changeHomCoefficients_apply R (S p) (S q) (f a) P X n l m hlm z y]
  rw [extensionIso_column e d h f g hfg a X, ← homColumnIso_eval,
    extensionIso_column e d h f g hfg a P]
  exact (changeHomCoefficients_apply R' (S' p) (S' q) (g a)
    ((changeRepresentative.{u,v,max u v w t} e).obj P) ((changeRepresentative.{u,v,max u v w t} e).obj X)
    n l m hlm ((homColumnIso.{u,v,w,t} e d h p P X).hom.f n z)
    (((extensionIso.{u,v,w,max u t} e (d p) (h p)).hom.app P).f l y)).symm

end Columns

section Comparison

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {S : ℕ → Type w} {S' : ℕ → Type v}
variable [∀ p, CommRing (S p)] [∀ p, CommRing (S' p)]
variable [∀ p, Algebra R (S p)] [∀ p, Algebra R' (S' p)]

private def compareRingDiagram (e : R ≃+* R') (d : ∀ p, S p ≃+* S' p)
    (f : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S p →ₐ[R] S q)
    (g : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S' p →ₐ[R'] S' q)
    (h : ∀ p r, d p (algebraMap R (S p) r) = algebraMap R' (S' p) (e r))
    (hfg : ∀ {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (s : S p),
      d q (f a s) = g a (d p s)) :
    OriginalRingDiagramComparison.{u,v,w,t} e d f g where
  localizationEquivalence := derivedIsEquivalence.{u,v,max u v w t} e
  originalModel := originalModel.{u,v,max u v w t} e
  extendIso p := extensionIso.{u,v,w,max u t} e (d p) (h p)
  extend_tmul p := extensionIso_tmul.{u,v,w,max u t} e (d p) (h p)
  extend_map := extensionIso_column.{u,v,w,t} e d h f g hfg
  homIso := homIso.{u,v,max u v w t} e
  hom_evaluation := homIso_eval.{u,v,max u v w t} e
  hom_natural := homIso_natural.{u,v,max u v w t} e
  homColumnIso := homColumnIso.{u,v,w,t} e d h
  homColumn_evaluation := homColumnIso_eval.{u,v,w,t} e d h
  homColumn_natural := homColumnIso_natural.{u,v,w,t} e d h
  baseChangeComparison := homColumnIso_baseChange.{u,v,w,t} e d h
  augmentation := homColumnIso_augmentation.{u,v,w,t} e d h
  cofaces := homColumnIso_cofaces.{u,v,w,t} e d h f g hfg

end Comparison

section Representatives

variable {k A B C A' B' C' : Type*}
  [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k A'] [Algebra k B'] [Algebra k C']
  [Algebra A B] [Algebra A C] [Algebra A' B'] [Algebra A' C']
  [IsScalarTower k A B] [IsScalarTower k A C] [IsScalarTower k A' B'] [IsScalarTower k A' C']
variable (e : A ≃ₐ[k] A') (b : B ≃ₐ[k] B') (c : C ≃ₐ[k] C')
variable (hb : ∀ a, b (algebraMap A B a) = algebraMap A' B' (e a))
variable (hc : ∀ a, c (algebraMap A C a) = algebraMap A' C' (e a))

private def cpEquiv (p : ℕ) : CP A C p ≃ₐ[k] CP A' C' p :=
  AlgEquiv.ofRingEquiv (f := powerRingEquiv e.toRingEquiv c.toRingEquiv hc (p + 1)) (by
    intro r
    rw [IsScalarTower.algebraMap_apply k A (CP A C p), powerRingEquiv_algebraMap]
    change algebraMap A' (CP A' C' p) (e (algebraMap k A r)) = _
    rw [e.commutes, ← IsScalarTower.algebraMap_apply])

private def bpEquiv (p : ℕ) : BP A B C p ≃ₐ[k] BP A' B' C' p :=
  AlgEquiv.ofRingEquiv
    (f := tensorRingEquiv e.toRingEquiv b.toRingEquiv
      (powerRingEquiv e.toRingEquiv c.toRingEquiv hc (p + 1)) hb
      (powerRingEquiv_algebraMap e.toRingEquiv c.toRingEquiv hc (p + 1))) (by
    intro r
    rw [IsScalarTower.algebraMap_apply k B (BP A B C p)]
    change tensorRingEquiv e.toRingEquiv b.toRingEquiv
      (powerRingEquiv e.toRingEquiv c.toRingEquiv hc (p + 1)) hb
      (powerRingEquiv_algebraMap e.toRingEquiv c.toRingEquiv hc (p + 1))
      ((algebraMap k B r) ⊗ₜ[A] (1 : CP A C p)) = _
    rw [tensorRingEquiv_tmul, map_one]
    change b (algebraMap k B r) ⊗ₜ[A'] (1 : CP A' C' p) = _
    rw [b.commutes]
    exact (IsScalarTower.algebraMap_apply k B' (BP A' B' C' p) r).symm)

omit [IsScalarTower k A C] [IsScalarTower k A' C'] in
@[simp] private theorem bpEquiv_tmul (p : ℕ) (z : B) (s : CP A C p) :
    bpEquiv e b c hb hc p (z ⊗ₜ[A] s) = b z ⊗ₜ[A'] cpEquiv e c hc p s :=
  tensorRingEquiv_tmul e.toRingEquiv b.toRingEquiv
    (powerRingEquiv e.toRingEquiv c.toRingEquiv hc (p + 1)) hb
    (powerRingEquiv_algebraMap e.toRingEquiv c.toRingEquiv hc (p + 1)) z s

omit [IsScalarTower k A C] [IsScalarTower k A' C'] in
private theorem bpEquiv_baseMap (p : ℕ) (z : B) :
    bpEquiv e b c hb hc p (baseMap (A := A) (C := C) p z) =
      baseMap (A := A') (C := C') p (b z) := by
  change bpEquiv e b c hb hc p (z ⊗ₜ[A] (1 : CP A C p)) =
    b z ⊗ₜ[A'] (1 : CP A' C' p)
  rw [bpEquiv_tmul, map_one]

omit [IsScalarTower k A C] [IsScalarTower k A' C'] in
private theorem bpEquiv_includeRight (p : ℕ) (s : CP A C p) :
    bpEquiv e b c hb hc p ((Algebra.TensorProduct.includeRight : CP A C p →ₐ[A] BP A B C p) s) =
      (Algebra.TensorProduct.includeRight : CP A' C' p →ₐ[A'] BP A' B' C' p) (cpEquiv e c hc p s) := by
  change bpEquiv e b c hb hc p ((1 : B) ⊗ₜ[A] s) = (1 : B') ⊗ₜ[A'] cpEquiv e c hc p s
  rw [bpEquiv_tmul, map_one]

omit [IsScalarTower k A C] [IsScalarTower k A' C'] in
private theorem cpEquiv_map {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (s : CP A C p) :
    cpEquiv e c hc q (AmitsurAlgebrasSpec.map a s) =
      AmitsurAlgebrasSpec.map a (cpEquiv e c hc p s) :=
  powerRingEquiv_map e.toRingEquiv c.toRingEquiv hc a s

private theorem columnMap_tmul {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (z : B) (s : CP A C p) :
    columnMap (A := A) (C := C) a (z ⊗ₜ[A] s) = z ⊗ₜ[A] AmitsurAlgebrasSpec.map a s :=
  Algebra.TensorProduct.map_tmul (AlgHom.id B B) (AmitsurAlgebrasSpec.map a) z s

omit [IsScalarTower k A C] [IsScalarTower k A' C'] in
private theorem bpEquiv_map {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (s : BP A B C p) :
    bpEquiv e b c hb hc q (columnMap (A := A) (C := C) a s) =
      columnMap (A := A') (C := C') a (bpEquiv e b c hb hc p s) := by
  induction s using TensorProduct.inductionOn with
  | tmul z s => rw [columnMap_tmul, bpEquiv_tmul, bpEquiv_tmul, columnMap_tmul, cpEquiv_map]
  | add x y hx hy => simp only [map_add, hx, hy]

end Representatives

set_option maxHeartbeats 1000000 in
/-- Ring representatives and ordinary Hom models at the common Amitsur bound. -/
theorem ringDiagramTransport : RingDiagramTransport.{u,v,t,x,y,i,j} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ _ _ _
  let A' := CommAlgCat.of k (ULift.{max u x y} A)
  let B' := CommAlgCat.of k (ULift.{max u v y} B)
  let C' := CommAlgCat.of k (ULift.{max u v x} C)
  let e : A ≃ₐ[k] A' := ULift.algEquiv.symm
  let b : B ≃ₐ[k] B' := ULift.algEquiv.symm
  let c : C ≃ₐ[k] C' := ULift.algEquiv.symm
  let f := b.toAlgHom.comp ((IsScalarTower.toAlgHom k A B).comp e.symm.toAlgHom)
  let g := c.toAlgHom.comp ((IsScalarTower.toAlgHom k A C).comp e.symm.toAlgHom)
  have hf (a : A) : f (e a) = b (algebraMap A B a) := by simp [f]
  have hg (a : A) : g (e a) = c (algebraMap A C a) := by simp [g]
  refine ⟨A', B', C', e, b, c, f, g, hf, hg, ?_⟩
  let : Algebra A' B' := f.toRingHom.toAlgebra
  let : Algebra A' C' := g.toRingHom.toAlgebra
  let : @IsScalarTower k A' B' (inferInstance : Algebra k A').toSMul
      f.toRingHom.toAlgebra.toSMul (inferInstance : Algebra k B').toSMul :=
    IsScalarTower.of_algHom f
  let : @IsScalarTower k A' C' (inferInstance : Algebra k A').toSMul
      g.toRingHom.toAlgebra.toSMul (inferInstance : Algebra k C').toSMul :=
    IsScalarTower.of_algHom g
  have hb (a : A) : b (algebraMap A B a) = algebraMap A' B' (e a) := (hf a).symm
  have hc (a : A) : c (algebraMap A C a) = algebraMap A' C' (e a) := (hg a).symm
  refine ⟨faithfullyFlat_of_algebra_equiv e.toRingEquiv c.toRingEquiv hc,
    cpEquiv e c hc, bpEquiv e b c hb hc, ?_, ?_, ?_, bpEquiv_tmul e b c hb hc,
    bpEquiv_baseMap e b c hb hc, bpEquiv_includeRight e b c hb hc, ?_, ?_⟩
  · intro p a s
    exact powerRingEquiv_factor e.toRingEquiv c.toRingEquiv hc a s
  · intro p z
    exact powerRingEquiv_tprod e.toRingEquiv c.toRingEquiv hc z
  · intro p a
    exact powerRingEquiv_algebraMap e.toRingEquiv c.toRingEquiv hc (p + 1) a
  · intro p q a s z
    exact ⟨cpEquiv_map e c hc a s, bpEquiv_map e b c hb hc a z⟩
  · exact ⟨compareRingDiagram.{x,max u v x y,max v x y,max i j t} b.toRingEquiv
      (fun p => (bpEquiv e b c hb hc p).toRingEquiv)
      (fun a => columnMap (A := A) (B := B) (C := C) a)
      (fun a => columnMap (A := A') (B := B') (C := C') a)
      (bpEquiv_baseMap e b c hb hc) (bpEquiv_map e b c hb hc)⟩

end
end DerivedFormalization.Descent.AmitsurRingTransport
