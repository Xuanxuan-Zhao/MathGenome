import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FinitePrimeFiltration
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Additivity and reduction to prime quotients

The Grothendieck group of a fixed support is presented by finite modules with
support contained in it, subject to the short exact sequence relations.
-/

noncomputable section

open scoped BigOperators
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs (intersectionEuler)

namespace CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction

universe u v w

variable {R : Type u} [CommRing R]

/-- The category's objects for the short exact sequence presentation of the
Grothendieck group with support in `X`. -/
structure SupportedModule (X : Set (PrimeSpectrum R)) where
  obj : ModuleCat.{v} R
  finite : Module.Finite R obj
  support_subset : Module.support R obj ⊆ X

instance {X : Set (PrimeSpectrum R)} (M : SupportedModule.{u,v} X) :
    Module.Finite R M.obj := M.finite

/-- The relations `[M] - ([A] + [C])` for short exact sequences
`0 → A → M → C → 0` of finite modules supported in `X`. -/
def exactRelations (X : Set (PrimeSpectrum R)) : Submodule ℤ (SupportedModule.{u,v} X →₀ ℤ) :=
  Submodule.span ℤ {r | ∃ (A M C : SupportedModule.{u,v} X)
    (f : A.obj →ₗ[R] M.obj) (g : M.obj →ₗ[R] C.obj),
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
      r = Finsupp.single M 1 - (Finsupp.single A 1 + Finsupp.single C 1)}

/-- The Grothendieck group of finite modules with support contained in `X`. -/
abbrev GrothendieckGroup (X : Set (PrimeSpectrum R)) :=
  (SupportedModule.{u,v} X →₀ ℤ) ⧸ exactRelations X

/-- The generator class of a supported finite module. -/
def classOf {X : Set (PrimeSpectrum R)} (M : SupportedModule.{u,v} X) :
    GrothendieckGroup.{u,v} X :=
  (exactRelations X).mkQ (Finsupp.single M 1)

namespace Specs

def additivity : Prop :=
  IntersectionEulerAdditivity.Specs.addLeft.{u,v,w} ∧
    IntersectionEulerAdditivity.Specs.addRight.{u,v,w}

/-- In every prime filtration of a nonzero finite module, the module's
dimension is the maximum dimension of its prime quotient factors. -/
def dimensionMaximum : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (F : PrimeFiltration R M),
    Nontrivial M →
      ∃ i : Fin F.length, ringKrullDim (R ⧸ (F.prime i).asIdeal) = Module.supportDim R M ∧
        ∀ j : Fin F.length, ringKrullDim (R ⧸ (F.prime j).asIdeal) ≤ Module.supportDim R M

/-- Reduction to prime quotients for any two prime filtrations, also when a
filtration is empty. All the summands are defined at isolated intersections. -/
def primeFiltrationReduction : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N]
    (F : PrimeFiltration R M) (G : PrimeFiltration R N),
    Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} →
      (∀ (i : Fin F.length) (j : Fin G.length),
        Module.support R (R ⧸ (F.prime i).asIdeal) ∩
          Module.support R (R ⧸ (G.prime j).asIdeal) ⊆ {IsLocalRing.closedPoint R}) ∧
      intersectionEuler M N =
        ∑ i : Fin F.length, ∑ j : Fin G.length,
          intersectionEuler (ModuleCat.of R (R ⧸ (F.prime i).asIdeal))
            (ModuleCat.of R (R ⧸ (G.prime j).asIdeal))

def classShortExact : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Set (PrimeSpectrum R)}
    (A M C : SupportedModule.{u,v} X) (f : A.obj →ₗ[R] M.obj) (g : M.obj →ₗ[R] C.obj),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    classOf M = classOf A + classOf C

/-- The presentation on module objects identifies isomorphic modules. -/
def classEqOfLinearEquiv : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Set (PrimeSpectrum R)}
    (M N : SupportedModule.{u,v} X), (M.obj ≃ₗ[R] N.obj) → classOf M = classOf N

/-- The Euler characteristic descends to the unique integer bilinear pairing
on the Grothendieck groups for the two fixed closed supports. -/
def grothendieckPairing : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (X Y : Set (PrimeSpectrum R)), IsClosed X → IsClosed Y →
    X ∩ Y ⊆ {IsLocalRing.closedPoint R} →
      ∃! pairing : GrothendieckGroup.{u,v} X →ₗ[ℤ] GrothendieckGroup.{u,w} Y →ₗ[ℤ] ℤ,
        ∀ (M : SupportedModule.{u,v} X) (N : SupportedModule.{u,w} Y),
          pairing (classOf M) (classOf N) = intersectionEuler M.obj N.obj

end Specs

end CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction
