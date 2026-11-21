import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! Carrier transport for HA-R14 (lines 2181–2203), with HA-R07's
augmentation comparison and HA-D04's positive connecting homomorphism. -/

noncomputable section
set_option linter.checkUnivs false

open CategoryTheory CategoryTheory.Limits
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AdvancedHomologicalAlgebra.TorBalance (AugmentedResolution LinearChainMap OriginalAugmentations)
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison

namespace Specs.AdvancedHomologicalAlgebra.DerivedTorOriginalModules

universe u v v' v'' a b l k w w' x y
variable {S : Type u} [Ring S]

/-- The ambient category contains the ring and the original carrier. -/
abbrev carrierLift (S : Type u) [Ring S] :=
  ModuleCat.uliftFunctor.{max u k,v} S

abbrev up (A : ModuleCat.{v} S) :
    A ≃ₗ[S] (carrierLift.{u,v,k} S).obj A :=
  ULift.moduleEquiv.symm

def liftMap {A : ModuleCat.{v} S} {B : ModuleCat.{v'} S} (f : A →ₗ[S] B) :
    (carrierLift.{u,v,max k v'} S).obj A ⟶ (carrierLift.{u,v',max k v} S).obj B :=
  ModuleCat.ofHom ((up.{u,v',max k v} B).toLinearMap.comp (f.comp (up.{u,v,max k v'} A).symm.toLinearMap))

/-- A specified identification of the original resolution with an ambient
resolution of the lifted module, including the augmentation. -/
structure ResolutionModel {A : ModuleCat.{v} S}
    (P : AugmentedResolution.{u,v,a} S A) where
  resolution : LeftResolution S ((carrierLift.{u,v,max a k} S).obj A)
  term : ∀ n, P.complex.X n ≃ₗ[S] resolution.complex.X n
  differential : ∀ i j, (resolution.complex.d i j).hom.comp (term i).toLinearMap =
    (term j).toLinearMap.comp (P.complex.d i j).hom
  augmentation : resolution.ε.comp (term 0).toLinearMap =
    (up.{u,v,max a k} A).toLinearMap.comp P.ε

def ResolutionModel.projective {A : ModuleCat.{v} S}
    {P : AugmentedResolution.{u,v,a} S A} (L : ResolutionModel.{u,v,a,k} P) :
    ProjectiveChoice S ((carrierLift.{u,v,max a k} S).obj A) :=
  ⟨L.resolution, fun n => letI := P.projective n; Module.Projective.of_equiv' (L.term n)⟩

/-- At the size of the original resolution only the augmentation changes. -/
def smallModel {A : ModuleCat.{v} S} (P : AugmentedResolution.{u,v,max u v} S A) :
    ResolutionModel.{u,v,max u v,v} P where
  resolution :=
    { complex := P.complex
      ε := (up A).toLinearMap.comp P.ε
      surjective := (up A).surjective.comp P.surjective
      exact_zero := (LinearMap.exact_iff.mp (LinearEquiv.postcomp_exact_iff_exact.mpr
        (LinearMap.exact_iff.mpr P.exact_zero.symm))).symm
      exact_succ := P.exact_succ }
  term n := LinearEquiv.refl _ _
  differential _ _ := by simp
  augmentation := by simp

/-- In a larger category the resolution is the termwise carrier lift. -/
def largeModel {A : ModuleCat.{v} S} (P : AugmentedResolution.{u,v,a} S A) :
    ResolutionModel.{u,v,a,k} P where
  resolution :=
    { complex := ((ModuleCat.uliftFunctor.{max u v k,a} S).mapHomologicalComplex
          (.down ℕ)).obj P.complex
      ε := (up A).toLinearMap.comp (P.ε.comp ULift.moduleEquiv.toLinearMap)
      surjective := (up A).surjective.comp (P.surjective.comp ULift.moduleEquiv.surjective)
      exact_zero := by
        symm
        apply LinearMap.exact_iff.mp
        change Function.Exact
          (ULift.moduleEquiv.symm.toLinearMap.comp ((P.complex.d 1 0).hom.comp
            ULift.moduleEquiv.toLinearMap))
          ((up A).toLinearMap.comp (P.ε.comp ULift.moduleEquiv.toLinearMap))
        rw [LinearEquiv.postcomp_exact_iff_exact, ← LinearMap.comp_assoc,
          LinearEquiv.precomp_exact_iff_exact,
          LinearEquiv.conj_symm_exact_iff_exact]
        exact LinearMap.exact_iff.mpr P.exact_zero.symm
      exact_succ := by
        intro n
        symm
        apply LinearMap.exact_iff.mp
        change Function.Exact
          (ULift.moduleEquiv.symm.toLinearMap.comp ((P.complex.d (n + 2) (n + 1)).hom.comp
            ULift.moduleEquiv.toLinearMap))
          (ULift.moduleEquiv.symm.toLinearMap.comp ((P.complex.d (n + 1) n).hom.comp
            ULift.moduleEquiv.toLinearMap))
        rw [LinearEquiv.postcomp_exact_iff_exact, ← LinearMap.comp_assoc,
          LinearEquiv.precomp_exact_iff_exact,
          LinearEquiv.conj_symm_exact_iff_exact]
        exact LinearMap.exact_iff.mpr (P.exact_succ n).symm }
  term _ := ULift.moduleEquiv.symm
  differential i j := by ext a; rfl
  augmentation := by ext a; rfl

variable {R : Type u} [Ring R]

/-- The original balanced tensor homology on a resolution of any term size. -/
abbrev resolutionTor {A : ModuleCat.{v} Rᵐᵒᵖ}
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (M : ModuleCat.{w} R) (n : ℕ) :=
  Homology (tensorComplex P.complex M) n

/-- The canonical map between tensor complexes, allowing independent sizes. -/
def tensorChainMap
    {K : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {L : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    (l : LinearChainMap K L) (g : M →ₗ[R] N) :
    LinearChainMap (tensorComplex K M) (tensorComplex L N) where
  app n := tensorMap (l.app n) g
  comm i j := by
    apply tensor_hom_ext
    intro a b
    change tmul R ((L.d i j).hom (l.app i a)) (g b) =
      tmul R (l.app j ((K.d i j).hom a)) (g b)
    rw [show (L.d i j).hom (l.app i a) = l.app j ((K.d i j).hom a)
      from LinearMap.congr_fun (l.comm i j) a]

def ResolutionModel.termMap {A : ModuleCat.{v} Rᵐᵒᵖ} {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
    (L : ResolutionModel.{u,v,a,k} P) :
    LinearChainMap P.complex L.resolution.complex :=
  ⟨fun n => (L.term n).toLinearMap, L.differential⟩

def ResolutionModel.termMapInv {A : ModuleCat.{v} Rᵐᵒᵖ} {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
    (L : ResolutionModel.{u,v,a,k} P) :
    LinearChainMap L.resolution.complex P.complex where
  app n := (L.term n).symm.toLinearMap
  comm i j := by
    ext z
    apply (L.term j).injective
    have h := LinearMap.congr_fun (L.differential i j) ((L.term i).symm z)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      using h.symm

/-- Tensor transport by a linear equivalence in the right factor. -/
def tensorEquiv {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
    (e : A ≃ₗ[Rᵐᵒᵖ] B) (M : ModuleCat.{w} R) :
    Tensor R A M ≃ₗ[ℤ] Tensor R B M :=
  LinearEquiv.ofLinearMap (tensorMap e.toLinearMap LinearMap.id)
    (tensorMap e.symm.toLinearMap LinearMap.id)
    (by
      apply tensor_hom_ext
      intro a m
      change tmul R (e (e.symm a)) m = tmul R a m
      rw [e.apply_symm_apply])
    (by
      apply tensor_hom_ext
      intro a m
      change tmul R (e.symm (e a)) m = tmul R a m
      rw [e.symm_apply_apply])

section Comparison
variable {A : ModuleCat.{v} Rᵐᵒᵖ} {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
variable [HasDerivedCategory.{x} (RightModules.{u,max v a k} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v a k,w})]
  [(minus (RightModules.{u,max v a k} R)).IsTriangulated]
  [(minus (Groups.{u,max v a k,w})).IsTriangulated]

/-- One normalized comparison on the original quotient and on every original
cycle. The degree-zero map is the actual derived counit transported back by
the inverse of the tensor equivalence of the stalk modules. -/
structure CarrierComparison
    {T : CanonicalTheory.{u,max u v a k,w} R}
    {D : DerivedFamily.{u,max v a k,w,x,y} R}
    (c : Comparison.{u,max v a k,w,x,y} R T D) (M : ModuleCat.{w} R)
    (L : ResolutionModel.{u,v,a,k} P) where
  classes : ∀ n, resolutionTor P M n ≃ₗ[ℤ] TorWith L.resolution M n
  classes_up : (tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)).InducesHomology
    (fun n z => classes n z)
  classes_down : (tensorChainMap L.termMapInv (LinearMap.id : M →ₗ[R] M)).InducesHomology
    (fun n z => (classes n).symm z)
  iso : ∀ n, (leftValue (tensor.{u,max v a k,w} R M) (D M) n).obj ((carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A) ≃ₗ[ℤ]
    resolutionTor P M n
  normalized : ∀ n z, iso n z = (classes n).symm
    ((c.iso M ((carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A) (L.projective) n).hom z)
  zero : (leftValue (tensor.{u,max v a k,w} R M) (D M) 0).obj ((carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A) ≃ₗ[ℤ]
    Tensor R A M
  zero_counit : ∀ z, zero z =
    (tensorEquiv (up.{u,v,max a k} A) M).symm (counitOnTensorStalk.{u,max v a k,w,x,y} R M (D M) _ z)
  zero_formula : ∀ z : cycles (tensorComplex P.complex M) 0,
    zero ((iso 0).symm (homologyClass _ 0 z)) = tensorMap P.ε LinearMap.id z.val
  balance : ∀ (Q : AugmentedResolution.{u,w,b} R M),
    ∃ (α : OriginalAugmentations P Q)
      (hL : α.left.IsQuasiIso) (hR : α.right.IsQuasiIso),
      ∀ n,
        ∃ e : (leftValue (tensor.{u,max v a k,w} R M) (D M) n).obj ((carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A) ≃ₗ[ℤ]
            Homology (leftOrdinaryTensorComplex A Q.complex) n,
          ∀ z, e z = α.balanceEquiv hL hR n (iso n z)

def ComparisonType : Prop :=
  ∀ (T : CanonicalTheory.{u,max u v a k,w} R) (D : DerivedFamily.{u,max v a k,w,x,y} R),
    ∃ c : Comparison.{u,max v a k,w,x,y} R T D,
      ∀ (A : ModuleCat.{v} Rᵐᵒᵖ) (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A)
        (L : ResolutionModel.{u,v,a,k} P) (M : ModuleCat.{w} R),
        Nonempty (CarrierComparison.{u,v,a,b,k,w,x,y} c M L)

end Comparison

/-- The augmented lift between ambient resolutions is conjugated by the
specified term identifications. -/
def liftChainMap {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v',b} Rᵐᵒᵖ B}
    (L : ResolutionModel.{u,v,a,max k v' b} P) (K : ResolutionModel.{u,v',b,max k v a} Q)
    (l : LinearChainMap P.complex Q.complex) : L.resolution.complex ⟶ K.resolution.complex where
  f n := ModuleCat.ofHom ((K.term n).toLinearMap.comp ((l.app n).comp (L.term n).symm.toLinearMap))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext z
    have hl := LinearMap.congr_fun (l.comm i j) ((L.term i).symm z)
    have hk := LinearMap.congr_fun (K.differential i j) (l.app i ((L.term i).symm z))
    have hL := LinearMap.congr_fun (L.termMapInv.comm i j) z
    change (K.resolution.complex.d i j).hom (K.term i (l.app i ((L.term i).symm z))) =
      K.term j (l.app j ((L.term j).symm ((L.resolution.complex.d i j).hom z)))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hl hk hL
    rw [hk, hl]
    exact congrArg (fun t => K.term j (l.app j t)) hL

/-- The map of original tensor complexes in the coefficient variable. -/
def identityChainMap {S : Type u} [Ring S] (K : ChainComplex (ModuleCat.{v} S) ℕ) :
    LinearChainMap K K :=
  ⟨fun _ => LinearMap.id, fun _ _ => by simp⟩

section RightNaturality
variable [HasDerivedCategory.{x} (RightModules.{u,max v v' a b k} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v v' a b k,w})]
  [(minus (RightModules.{u,max v v' a b k} R)).IsTriangulated]
  [(minus (Groups.{u,max v v' a b k,w})).IsTriangulated]

/-- Naturality for every original right-module map, between independent
carrier sizes, and every augmented lift on the original resolutions. -/
def RightNaturalityType : Prop :=
  ∀ {T : CanonicalTheory.{u,max u v v' a b k,w} R} {D : DerivedFamily.{u,max v v' a b k,w,x,y} R}
    {c : Comparison.{u,max v v' a b k,w,x,y} R T D}
    {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ} {M : ModuleCat.{w} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v',b} Rᵐᵒᵖ B}
    {L : ResolutionModel.{u,v,a,max k v' b} P} {K : ResolutionModel.{u,v',b,max k v a} Q}
    (a : CarrierComparison.{u,v,a,b,max k v' b,w,x,y} c M L)
    (b : CarrierComparison.{u,v',b,a,max k v a,w,x,y} c M K)
    (f : A →ₗ[Rᵐᵒᵖ] B),
    (∃ l : LinearChainMap P.complex Q.complex, Q.ε.comp (l.app 0) = f.comp P.ε) ∧
    ∀ (l : LinearChainMap P.complex Q.complex),
      Q.ε.comp (l.app 0) = f.comp P.ε →
      ∃ h : ∀ n, resolutionTor P M n →ₗ[ℤ] resolutionTor Q M n,
        (tensorChainMap l (LinearMap.id : M →ₗ[R] M)).InducesHomology
          (fun n z => h n z) ∧
        ∀ n z, b.iso n ((leftValue (tensor.{u,max v v' a b k,w} R M) (D M) n).map
          (liftMap.{u,v,v',max a b k} f) z) = h n (a.iso n z)

end RightNaturality

section CoefficientNaturality
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

variable [HasDerivedCategory.{x} (RightModules.{u,max v a k} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v a k,w})]
  [(minus (RightModules.{u,max v a k} R)).IsTriangulated]
  [(minus (Groups.{u,max v a k,w})).IsTriangulated]

/-- Naturality for original maps in the coefficient category, using the
HA-R07 transformation corresponding to the given coefficient map. -/
def CoefficientNaturalityType : Prop :=
  ∀ {T : CanonicalTheory.{u,max u v a k,w} R} {D : DerivedFamily.{u,max v a k,w,x,y} R}
    {c : Comparison.{u,max v a k,w,x,y} R T D}
    {A : ModuleCat.{v} Rᵐᵒᵖ} {M N : ModuleCat.{w} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
    {L : ResolutionModel.{u,v,a,k} P}
    (a : CarrierComparison.{u,v,a,b,k,w,x,y} c M L)
    (b : CarrierComparison.{u,v,a,b,k,w,x,y} c N L)
    (g : M ⟶ N) (α : (D M).functor ⟶ (D N).functor),
    Functor.whiskerLeft (QMinus (RightModules.{u,max v a k} R)) α ≫ (D N).counit =
      (D M).counit ≫ minusUMapValue (tensor.{u,max v a k,w} R M) (tensor.{u,max v a k,w} R N)
        (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom) →
    ∃ h : ∀ n, resolutionTor P M n →ₗ[ℤ] resolutionTor P N n,
      (tensorChainMap (identityChainMap P.complex) g.hom).InducesHomology
        (fun n z => h n z) ∧
      ∀ n z, b.iso n ((DerivedCategory.homologyFunctor (Groups.{u,max v a k,w}) (-(n : ℤ))).map
        (DerivedCategory.Minus.ι.map (α.app ((minusSingle (RightModules.{u,max v a k} R)).obj
          ((carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A)))) z) = h n (a.iso n z)

end CoefficientNaturality

section Horseshoes
open P103.Specs.Ch10.Horseshoe

variable {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
  {C : ModuleCat.{v''} Rᵐᵒᵖ}
  {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v'',b} Rᵐᵒᵖ C}

/-- The P103 horseshoe data with independent carrier sizes for the three
modules and for the terms of the middle resolution. The terms of both endpoint
resolutions also have independent sizes. The maps and term identifications act
on the given resolutions with their original augmentations. -/
structure OriginalHorseshoe (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (Q : AugmentedResolution.{u,v'',b} Rᵐᵒᵖ C) where
  middle : AugmentedResolution.{u,v',l} Rᵐᵒᵖ B
  term : ∀ n, middle.complex.X n ≃ₗ[Rᵐᵒᵖ] (P.complex.X n × Q.complex.X n)
  inclusion : LinearChainMap P.complex middle.complex
  projection : LinearChainMap middle.complex Q.complex
  inclusion_apply : ∀ n a, term n (inclusion.app n a) = (a, 0)
  projection_apply : ∀ n b, projection.app n b = (term n b).2
  augmentation_inclusion : middle.ε.comp (inclusion.app 0) = f.comp P.ε
  augmentation_projection : Q.ε.comp (projection.app 0) = g.comp middle.ε

def OriginalHorseshoe.ofP103 {B C : ModuleCat.{v} Rᵐᵒᵖ}
    {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution Rᵐᵒᵖ C}
    {f : A →ₗ[Rᵐᵒᵖ] B} {g : B →ₗ[Rᵐᵒᵖ] C}
    (hP : P.IsProjective) (hQ : Q.IsProjective) (H : ProjectiveData f g P Q) :
    OriginalHorseshoe f g (AugmentedResolution.ofP103 P hP)
      (AugmentedResolution.ofP103 Q hQ) where
  middle := ⟨H.middle.complex, H.middle.ε, H.middle.surjective,
    H.middle.exact_zero, H.middle.exact_succ, H.projective⟩
  term := H.term
  inclusion := ⟨fun n => (H.inclusion.f n).hom,
    fun i j => congrArg ModuleCat.Hom.hom (H.inclusion.comm i j)⟩
  projection := ⟨fun n => (H.projection.f n).hom,
    fun i j => congrArg ModuleCat.Hom.hom (H.projection.comm i j)⟩
  inclusion_apply := H.inclusion_apply
  projection_apply := H.projection_apply
  augmentation_inclusion := H.augmentation_inclusion
  augmentation_projection := H.augmentation_projection

def liftSequence (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (h : Function.Exact f g) : ShortComplex (RightModules.{u,max v v' v'' k} R) :=
  ShortComplex.mk (liftMap.{u,v,v',max k v''} f) (liftMap.{u,v',v'',max k v} g) (by
    apply ModuleCat.hom_ext
    ext z
    change up.{u,v'',max k v v'} C
      (g ((up.{u,v',max k v v''} B).symm
        (up.{u,v',max k v v''} B (f ((up.{u,v,max k v' v''} A).symm z))))) = 0
    rw [LinearEquiv.symm_apply_apply]
    have hz := congrFun h.comp_eq_zero ((up.{u,v,max k v' v''} A).symm z)
    exact (congrArg (up.{u,v'',max k v v'} C) hz).trans (map_zero _))

theorem liftSequence_exact (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    (liftSequence.{u,v,v',v'',k} f g h).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((up.{u,v',max k v v''} B).toLinearMap.comp
      (f.comp (up.{u,v,max k v' v''} A).symm.toLinearMap))
      ((up.{u,v'',max k v v'} C).toLinearMap.comp
        (g.comp (up.{u,v',max k v v''} B).symm.toLinearMap))
    rw [LinearEquiv.postcomp_exact_iff_exact, ← LinearMap.comp_assoc,
      LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact]
    exact h
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact (up.{u,v',max k v v''} B).injective.comp
      (hf.comp (up.{u,v,max k v' v''} A).symm.injective)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact (up.{u,v'',max k v v'} C).surjective.comp
      (hg.comp (up.{u,v',max k v v''} B).symm.surjective)

variable [HasDerivedCategory.{x} (RightModules.{u,max v v' v'' a b l k} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v v' v'' a b l k,w})]
  [(minus (RightModules.{u,max v v' v'' a b l k} R)).IsTriangulated]
  [(minus (Groups.{u,max v v' v'' a b l k,w})).IsTriangulated]

/-- The positive classical connector on every original horseshoe
representative. The derived boundary goes from degree −(n+1) to −n. -/
def ConnectingType : Prop :=
  ∀ {T : CanonicalTheory.{u,max u v v' v'' a b l k,w} R}
    {D : DerivedFamily.{u,max v v' v'' a b l k,w,x,y} R}
    {c : Comparison.{u,max v v' v'' a b l k,w,x,y} R T D}
    (M : ModuleCat.{w} R) (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g),
    Nonempty (OriginalHorseshoe.{u,v,v',v'',a,b,max u v v' v'' a b l k} f g P Q) ∧
    ∀ (H : OriginalHorseshoe.{u,v,v',v'',a,b,l} f g P Q)
      (L : ResolutionModel.{u,v,a,max k b l v' v''} P)
      (K : ResolutionModel.{u,v'',b,max k a l v v'} Q)
      (a : CarrierComparison.{u,v,a,b,max k b l v' v'',w,x,y} c M L)
      (b : CarrierComparison.{u,v'',b,a,max k a l v v',w,x,y} c M K)
      (n : ℕ)
      (z : cycles (tensorComplex Q.complex M) (n + 1))
      (m : (tensorComplex H.middle.complex M).X (n + 1))
      (s : cycles (tensorComplex P.complex M) n),
      tensorMap (H.projection.app (n + 1)) LinearMap.id m = z.val →
      tensorMap (H.inclusion.app n) LinearMap.id s.val =
        ((tensorComplex H.middle.complex M).d (n + 1) n).hom m →
      a.iso n (leftBoundary (tensor.{u,max v v' v'' a b l k,w} R M) (D M)
        (liftSequence_exact.{u,v,v',v'',max a b l k} f g he hf hg) n
          ((b.iso (n + 1)).symm (homologyClass _ (n + 1) z))) = homologyClass _ n s

end Horseshoes


def ComparisonExpected : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,max v a k} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v a k,w})]
    [(minus (RightModules.{u,max v a k} R)).IsTriangulated]
    [(minus (Groups.{u,max v a k,w})).IsTriangulated],
    ComparisonType.{u,v,a,b,k,w,x,y} (R := R)

def RightNaturalityExpected : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,max v v' a b k} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v v' a b k,w})]
    [(minus (RightModules.{u,max v v' a b k} R)).IsTriangulated]
    [(minus (Groups.{u,max v v' a b k,w})).IsTriangulated],
    RightNaturalityType.{u,v,v',a,b,k,w,x,y} (R := R)

def CoefficientNaturalityExpected : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,max v a k} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v a k,w})]
    [(minus (RightModules.{u,max v a k} R)).IsTriangulated]
    [(minus (Groups.{u,max v a k,w})).IsTriangulated],
    CoefficientNaturalityType.{u,v,a,b,k,w,x,y} (R := R)

def ConnectingExpected : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,max v v' v'' a b l k} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v v' v'' a b l k,w})]
    [(minus (RightModules.{u,max v v' v'' a b l k} R)).IsTriangulated]
    [(minus (Groups.{u,max v v' v'' a b l k,w})).IsTriangulated]
    (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v'} Rᵐᵒᵖ) (C : ModuleCat.{v''} Rᵐᵒᵖ)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (Q : AugmentedResolution.{u,v'',b} Rᵐᵒᵖ C),
    ConnectingType.{u,v,v',v'',a,b,l,k,w,x,y} (R := R) (A := A) (B := B) (C := C) (P := P) (Q := Q)

section HeterogeneousCoefficients
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

/-- With a common target group category, an original coefficient map acts
directly by the balanced tensor map even if its endpoints have different sizes. -/
def coefficientMap {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R} (g : M →ₗ[R] N) :
    tensor.{u,max v a k w w',w} R M ⟶ tensor.{u,max v a k w w',w'} R N where
  app A := ModuleCat.ofHom (tensorMap LinearMap.id g)
  naturality := by
    intro A B f
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a m
    rfl

variable [HasDerivedCategory.{x} (RightModules.{u,max v a k w w'} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v a k w w',0})]
  [(minus (RightModules.{u,max v a k w w'} R)).IsTriangulated]
  [(minus (Groups.{u,max v a k w w',0})).IsTriangulated]

def coefficientValueMap
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    {D : DerivedFamily.{u,max v a k w w',w,x,y} R}
    {E : DerivedFamily.{u,max v a k w w',w',x,y} R}
    (α : (D M).functor ⟶ (E N).functor)
    (A : RightModules.{u,max v a k w w'} R) (n : ℕ) :
    (leftValue (tensor.{u,max v a k w w',w} R M) (D M) n).obj A ⟶
    (leftValue (tensor.{u,max v a k w w',w'} R N) (E N) n).obj A :=
  (DerivedCategory.homologyFunctor (Groups.{u,max v a k w w',0}) (-(n : ℤ))).map
    (DerivedCategory.Minus.ι.map (α.app ((minusSingle (RightModules.{u,max v a k w w'} R)).obj A)))

set_option maxHeartbeats 1000000 in
def HeterogeneousCoefficientType : Prop :=
  ∀ {T : CanonicalTheory.{u,max u v a k w w',w} R}
    {U : CanonicalTheory.{u,max u v a k w w',w'} R}
    {D : DerivedFamily.{u,max v a k w w',w,x,y} R}
    {E : DerivedFamily.{u,max v a k w w',w',x,y} R}
    {c : Comparison.{u,max v a k w w',w,x,y} R T D}
    {c' : Comparison.{u,max v a k w w',w',x,y} R U E}
    {A : ModuleCat.{v} Rᵐᵒᵖ} {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
    {L : ResolutionModel.{u,v,a,max k w w'} P}
    (a : CarrierComparison.{u,v,a,b,max k w w',w,x,y} c M L)
    (b : CarrierComparison.{u,v,a,b,max k w w',w',x,y} c' N L)
    (g : M →ₗ[R] N) (α : (D M).functor ⟶ (E N).functor),
    Functor.whiskerLeft (QMinus (RightModules.{u,max v a k w w'} R)) α ≫ (E N).counit =
      (D M).counit ≫ minusUMapValue (tensor.{u,max v a k w w',w} R M)
        (tensor.{u,max v a k w w',w'} R N) (coefficientMap.{u,v,a,k,w,w'} g) →
    ∃ h : ∀ n, resolutionTor P M n →ₗ[ℤ] resolutionTor P N n,
      (tensorChainMap (identityChainMap P.complex) g).InducesHomology
        (fun n z => h n z) ∧
      ∀ (n : ℕ)
        (z : (leftValue (tensor.{u,max v a k w w',w} R M) (D M) n).obj
          ((carrierLift.{u,v,max a k w w'} Rᵐᵒᵖ).obj A)),
        (@CarrierComparison.iso.{u,v,a,b,max k w w',w',x,y} R _ A P _ _ _ _ U E c' N L b n)
          ((coefficientValueMap.{u,v,a,k,w,w',x,y} (D := D) (E := E)
          α ((carrierLift.{u,v,max a k w w'} Rᵐᵒᵖ).obj A) n).hom z) =
        h n ((@CarrierComparison.iso.{u,v,a,b,max k w w',w,x,y} R _ A P _ _ _ _ T D c M L a n) z)

end HeterogeneousCoefficients


def HeterogeneousCoefficientExpected : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,max v a k w w'} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v a k w w',0})]
    [(minus (RightModules.{u,max v a k w w'} R)).IsTriangulated]
    [(minus (Groups.{u,max v a k w w',0})).IsTriangulated],
    HeterogeneousCoefficientType.{u,v,a,b,k,w,w',x,y} (R := R)

end Specs.AdvancedHomologicalAlgebra.DerivedTorOriginalModules
