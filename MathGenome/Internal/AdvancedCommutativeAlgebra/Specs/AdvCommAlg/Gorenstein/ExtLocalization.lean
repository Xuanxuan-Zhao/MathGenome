import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtScalarActions
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Support

/-!
Canonical objects for localization of categorical Ext. `localizedModule` is
Mathlib's universe-preserving model of module localization. In particular it
is a localization of the original module, not a replacement Ext theory.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace AdvCommAlg.Gorenstein.ExtLocalization

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
instance localizationFunctor_linear (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{u} S).Linear R where
  map_smul := by
    intro M N f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.localizedModule S at x
    change (IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) (Localization S)) (r • f.hom) x =
        algebraMap R (Localization S) r •
          (IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
            (N.localizedModuleMkLinearMap S) (Localization S)) f.hom x
    rw [map_smul]
    change r • ((IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) (Localization S)) f.hom x) = _
    exact (algebraMap_smul (Localization S) r _).symm

/-- Restriction of the coefficient-ring action agrees with the categorical
scalar action on Ext. -/
instance extScalarTower {A : Type u} [CommRing A] [Algebra R A]
    (M N : ModuleCat.{u} A) (n : ℕ) : IsScalarTower R A (Ext M N n) where
  smul_assoc r a x := by
    have h (y : Ext M N n) : r • y = algebraMap R A r • y := by
      rw [Ext.smul_eq_comp_mk₀ (R := R), Ext.smul_eq_comp_mk₀ (R := A)]
      rfl
    rw [h, Algebra.smul_def]
    exact mul_smul (algebraMap R A r) a x

/-- The localization functor's canonical R-linear map on Ext. -/
def localizeExt (S : Submonoid R) (M N : ModuleCat.{u} R) (n : ℕ) :
    Ext M N n →ₗ[R] Ext (M.localizedModule S) (N.localizedModule S) n :=
  (ModuleCat.localizedModuleFunctor S).mapExtLinearMap R M N n

/-- Simultaneous contravariant and covariant functoriality of Ext. -/
def mapExt {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ) :
    Ext M N n →ₗ[R] Ext M' N' n :=
  (Ext.precompOfLinear (Ext.mk₀ f) R N' (zero_add n)).comp
    (Ext.postcompOfLinear (Ext.mk₀ g) R M (add_zero n))

set_option backward.isDefEq.respectTransparency false in
/-- The localization of the rank-one coefficient module is the localized ring. -/
def localizedRingIso (S : Submonoid R) :
    (ModuleCat.of R R).localizedModule S ≅ ModuleCat.of (Localization S) (Localization S) := by
  letI := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R R) S
  exact ((IsLocalizedModule.linearEquiv S ((ModuleCat.of R R).localizedModuleMkLinearMap S)
    (Algebra.linearMap R (Localization S))).extendScalarsOfIsLocalization S _).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- Localization of R/I is the quotient of the localized ring by the
extended ideal. This identification uses the actual ideal extension. -/
def localizedQuotientIso (S : Submonoid R) (I : Ideal R) :
    (ModuleCat.of R (R ⧸ I)).localizedModule S ≅
      ModuleCat.of (Localization S) ((Localization S) ⧸ I.map (algebraMap R (Localization S))) := by
  letI := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (R ⧸ I)) S
  let e := IsLocalizedModule.linearEquiv S
    ((ModuleCat.of R (R ⧸ I)).localizedModuleMkLinearMap S)
    (I.toLocalizedQuotient' (Localization S) S (Algebra.linearMap R (Localization S)))
  exact ((e.extendScalarsOfIsLocalization S _).trans
    (Submodule.quotEquivOfEq _ _ (Ideal.localized'_eq_map (Localization S) S I))).toModuleIso

end AdvCommAlg.Gorenstein.ExtLocalization

namespace Specs.AdvCommAlg.Gorenstein.ExtLocalization
open _root_.AdvCommAlg.Gorenstein.ExtLocalization

/-- Universal localization property of the canonical map, in every degree.
The coefficient module is arbitrary; only the first module is finite. -/
def isLocalizedExt : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (S : Submonoid R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (N : ModuleCat.{u} R) (n : ℕ),
    IsLocalizedModule S (localizeExt S M N n)

/-- The comparison is an isomorphism over the localized ring, with its
canonical value on the image of each Ext class specified. -/
def comparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (S : Submonoid R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (N : ModuleCat.{u} R) (n : ℕ),
    ∃ e : LocalizedModule S (Ext M N n) ≃ₗ[Localization S]
        Ext (M.localizedModule S) (N.localizedModule S) n,
      ∀ x, e (LocalizedModule.mk x 1) = localizeExt S M N n x

/-- One family of comparisons, natural in both module variables. -/
def naturalComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (S : Submonoid R) (n : ℕ),
    ∃ e : ∀ (M : ModuleCat.{u} R) [Module.Finite R M] (N : ModuleCat.{u} R),
        LocalizedModule S (Ext M N n) ≃ₗ[Localization S]
          Ext (M.localizedModule S) (N.localizedModule S) n,
      (∀ (M : ModuleCat.{u} R) [Module.Finite R M] (N : ModuleCat.{u} R) x,
        e M N (LocalizedModule.mk x 1) = localizeExt S M N n x) ∧
      (∀ (M M' : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R M']
          (N N' : ModuleCat.{u} R) (f : M' ⟶ M) (g : N ⟶ N') z,
        e M' N' (LocalizedModule.map S (mapExt f g n) z) =
          mapExt ((ModuleCat.localizedModuleFunctor S).map f)
            ((ModuleCat.localizedModuleFunctor S).map g) n (e M N z))

/-- The coefficient R comparison over the prime localization, including
its canonical image formula. -/
def primeComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ),
    ∃ e : LocalizedModule p.primeCompl (Ext M (ModuleCat.of R R) n) ≃ₗ[Localization.AtPrime p]
        Ext (M.localizedModule p.primeCompl)
          (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) n,
      ∀ x, e (LocalizedModule.mk x 1) =
        (localizeExt p.primeCompl M (ModuleCat.of R R) n x).comp
          (Ext.mk₀ (localizedRingIso p.primeCompl).hom) (add_zero n)

/-- Naturality of the comparison with coefficient the actual local ring. -/
def primeNaturalComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (n : ℕ),
    ∃ e : ∀ (M : ModuleCat.{u} R) [Module.Finite R M],
        LocalizedModule p.primeCompl (Ext M (ModuleCat.of R R) n) ≃ₗ[Localization.AtPrime p]
          Ext (M.localizedModule p.primeCompl)
            (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) n,
      (∀ (M : ModuleCat.{u} R) [Module.Finite R M] x,
        e M (LocalizedModule.mk x 1) =
          (localizeExt p.primeCompl M (ModuleCat.of R R) n x).comp
            (Ext.mk₀ (localizedRingIso p.primeCompl).hom) (add_zero n)) ∧
      (∀ (M M' : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R M']
          (f : M' ⟶ M) z,
        e M' (LocalizedModule.map p.primeCompl (mapExt f (𝟙 (ModuleCat.of R R)) n) z) =
          mapExt ((ModuleCat.localizedModuleFunctor p.primeCompl).map f)
            (𝟙 (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) n (e M z))

/-- The exact ideal-quotient comparison used in GC-07. -/
def idealQuotientComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (I : Ideal R) (n : ℕ),
    ∃ e : LocalizedModule p.primeCompl
        (Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n) ≃ₗ[Localization.AtPrime p]
        Ext (ModuleCat.of (Localization.AtPrime p)
          ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))))
          (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) n,
      ∀ x, e (LocalizedModule.mk x 1) =
        mapExt (localizedQuotientIso p.primeCompl I).inv
          (localizedRingIso p.primeCompl).hom n
          (localizeExt p.primeCompl (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n x)

/-- The support containment used in GC-09, over arbitrary Noetherian rings. -/
def support_subset : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] (N : ModuleCat.{u} R) (n : ℕ),
    Module.support R (Ext M N n) ⊆ Module.support R M

end Specs.AdvCommAlg.Gorenstein.ExtLocalization
