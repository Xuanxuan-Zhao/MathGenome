import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtScalarActions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
Shared objects and independent statement of the general assertion of GC-03
(paper.tex, 4453–4491). Rings and modules are arbitrary; the structural map
need not be surjective. The final regular-quotient assertion is allocated to
`gc_03_regular_quotient`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false


universe u

open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

variable {S R : Type u} [CommRing S] [CommRing R]

/-- Ext over S, retaining the R-module in its first argument. This type synonym
allows its R-action to be distinguished from the ordinary S-action on Ext. -/
def FirstExt (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (n : ℕ) : Type u :=
  Ext ((ModuleCat.restrictScalars φ).obj M) N n

instance (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (n : ℕ) :
    AddCommGroup (FirstExt φ M N n) :=
  inferInstanceAs (AddCommGroup (Ext ((ModuleCat.restrictScalars φ).obj M) N n))

/-- The R-action induced by multiplication on the first argument. -/
instance firstExtModule (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (n : ℕ) :
    Module R (FirstExt φ M N n) where
  smul r x := (Ext.mk₀ ((ModuleCat.restrictScalars φ).map (r • 𝟙 M))).comp x (zero_add n)
  one_smul x := by unfold FirstExt at *; change (Ext.mk₀ _).comp _ _ = _; simp
  mul_smul r s x := by
    unfold FirstExt at *
    change (Ext.mk₀ _).comp _ _ = (Ext.mk₀ _).comp ((Ext.mk₀ _).comp _ _) _
    rw [Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp]
    congr 2
    congr 1
    ext m
    change (r * s) • m = s • (r • m)
    rw [mul_smul, smul_comm]
  smul_zero r := by unfold FirstExt at *; change (Ext.mk₀ _).comp 0 _ = 0; simp
  smul_add r x y := by
    unfold FirstExt at *
    change (Ext.mk₀ _).comp (x + y) (zero_add n) =
      (Ext.mk₀ _).comp x (zero_add n) + (Ext.mk₀ _).comp y (zero_add n)
    simp
  add_smul r s x := by
    unfold FirstExt at *
    change (Ext.mk₀ ((ModuleCat.restrictScalars φ).map ((r + s) • 𝟙 M))).comp x _ =
      (Ext.mk₀ ((ModuleCat.restrictScalars φ).map (r • 𝟙 M))).comp x (zero_add n) +
      (Ext.mk₀ ((ModuleCat.restrictScalars φ).map (s • 𝟙 M))).comp x (zero_add n)
    simp [add_smul, Ext.mk₀_add]
  zero_smul x := by
    unfold FirstExt at *
    change (Ext.mk₀ ((ModuleCat.restrictScalars φ).map (0 • 𝟙 M))).comp x _ = _
    simp

/-- Forget the type synonym; the underlying additive group is exactly Mathlib Ext. -/
def firstExtAddEquiv (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (n : ℕ) :
    FirstExt φ M N n ≃+ Ext ((ModuleCat.restrictScalars φ).obj M) N n :=
  AddEquiv.refl _

/-- W = Ext_S^c(R,N), with R acting through multiplication on R. -/
def coefficient (φ : S →+* R) (N : ModuleCat.{u} S) (c : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (FirstExt φ (ModuleCat.of R R) N c)

/-- Concentration is imposed on actual Ext groups of the restricted module R. -/
def Concentrated (φ : S →+* R) (N : ModuleCat.{u} S) (c : ℕ) : Prop :=
  ∀ j : ℕ, j ≠ c → Subsingleton (Ext
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of R R)) N j)

/-- Pullback along an R-linear morphism, acting on Ext over S. -/
def firstExtPullback (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (N : ModuleCat.{u} S) (n : ℕ) :
    FirstExt φ M' N n →ₗ[R] FirstExt φ M N n where
  toFun x := (Ext.mk₀ ((ModuleCat.restrictScalars φ).map f)).comp x (zero_add n)
  map_add' x y := by unfold FirstExt at *; change (Ext.mk₀ _).comp (x + y) _ = _; simp
  map_smul' r x := by
    unfold FirstExt at *
    change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp x _) _ =
      (Ext.mk₀ _).comp ((Ext.mk₀ _).comp x _) _
    rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 2
    congr 1
    ext m
    exact (f.hom.map_smul r m).symm

/-- The shifted Ext functor over S with its actual first-argument R-action. -/
def shiftedExtFunctor (φ : S →+* R) (N : ModuleCat.{u} S) (c i : ℕ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (FirstExt φ M.unop N (i + c))
  map f := ModuleCat.ofHom (firstExtPullback φ f.unop N (i + c))
  map_id M := by ext x; change (Ext.mk₀ _).comp x (zero_add (i + c)) = x; simp
  map_comp f g := by
    ext x
    change (Ext.mk₀ _).comp x (zero_add (i + c)) =
      (Ext.mk₀ _).comp ((Ext.mk₀ _).comp x (zero_add (i + c))) (zero_add (i + c))
    simp [Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp]

/-- The ordinary Ext_R functor with coefficient W. -/
def coefficientExtFunctor (φ : S →+* R) (N : ModuleCat.{u} S) (c i : ℕ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Ext M.unop (coefficient φ N c) i)
  map f := ModuleCat.ofHom (Ext.precompOfLinear (Ext.mk₀ f.unop) R _ (zero_add i))

end AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

namespace Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

open _root_.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

/-- A natural R-linear isomorphism in every degree. A natural isomorphism of
ModuleCat-valued functors includes both the isomorphisms and naturality for
every R-linear map M → M'. -/
def comparison : Prop :=
  ∀ (S R : Type u) [CommRing S] [CommRing R] (φ : S →+* R)
    (N : ModuleCat.{u} S) (c : ℕ), Concentrated φ N c →
    ∀ i : ℕ, Nonempty (coefficientExtFunctor φ N c i ≅ shiftedExtFunctor φ N c i)

/-- All Ext groups below the concentration degree vanish for every R-module. -/
def vanishing : Prop :=
  ∀ (S R : Type u) [CommRing S] [CommRing R] (φ : S →+* R)
    (N : ModuleCat.{u} S) (c : ℕ), Concentrated φ N c →
    ∀ (M : ModuleCat.{u} R) (j : ℕ), j < c →
      Subsingleton (Ext ((ModuleCat.restrictScalars φ).obj M) N j)

end Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
