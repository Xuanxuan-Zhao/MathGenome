import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.Module

noncomputable section

open scoped TensorProduct Pointwise
open IsLocalRing
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs (Tor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs (intersectionEuler)

namespace CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion.Specs

universe u v w

abbrev CompletedRing (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

abbrev CompletedModule (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type v) [AddCommGroup L] [Module R L] :=
  AdicCompletion (maximalIdeal R) L

abbrev completedModuleCat {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) : ModuleCat.{v} (CompletedRing R) :=
  ModuleCat.of (CompletedRing R) (CompletedModule R M)

def completionRingDimension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ringKrullDim (CompletedRing R) = ringKrullDim R

def completionRegularLocal : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    IsRegularLocalRing (CompletedRing R)

def completionModuleDimension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L],
    Module.supportDim (CompletedRing R) (CompletedModule R L) = Module.supportDim R L

def completionModuleFinite : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L],
    Module.Finite (CompletedRing R) (CompletedModule R L)

def completionTensorComparison : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L] [Module.Finite R L],
    ∃ e : CompletedRing R ⊗[R] L ≃ₗ[CompletedRing R] CompletedModule R L,
      ∀ (a : CompletedRing R) (l : L), e (a ⊗ₜ[R] l) = a • AdicCompletion.of (maximalIdeal R) L l

def completionPowerQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L] (n : ℕ),
    Nonempty
      ((CompletedModule R L ⧸ ((maximalIdeal (CompletedRing R)) ^ n •
        (⊤ : Submodule (CompletedRing R) (CompletedModule R L)))) ≃ₗ[R]
        (L ⧸ ((maximalIdeal R) ^ n • (⊤ : Submodule R L))))

def completionBaseChangeLength : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (L : Type v) [AddCommGroup L] [Module R L],
    IsFiniteLength R L →
      Module.length (CompletedRing R) (CompletedRing R ⊗[R] L) = Module.length R L

def completionTor : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ),
    Nonempty (CompletedRing R ⊗[R] Tor M N i ≃ₗ[CompletedRing R]
      Tor (completedModuleCat M) (completedModuleCat N) i)

def completionTensorFiniteLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) →
      IsFiniteLength (CompletedRing R) (CompletedModule R M ⊗[CompletedRing R] CompletedModule R N)

def completionEuler : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) →
      ∃ h : IsRegularLocalRing (CompletedRing R),
        letI := h
        intersectionEuler (completedModuleCat M) (completedModuleCat N) = intersectionEuler M N

end CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion.Specs
