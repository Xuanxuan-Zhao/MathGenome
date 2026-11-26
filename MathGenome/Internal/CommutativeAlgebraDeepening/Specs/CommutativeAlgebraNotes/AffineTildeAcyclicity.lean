import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Topology.Sheaves.Abelian
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

noncomputable section

open AlgebraicGeometry CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory hiding evaluation
open AdvancedHomologicalAlgebra.SheafTheory

namespace Specs.CommutativeAlgebraNotes.AffineTildeAcyclicity

universe u

instance moduleSpecΓFunctor_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

def TildeExact : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact →
      (S.map (tilde.functor R)).ShortExact

def TildeSectionsSurjective : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (Q : ModuleCat.{u} R) [Injective Q]
    (U : (Spec R).Opens), Function.Surjective (tilde.toOpen Q U)

def TildeFlasque : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (Q : ModuleCat.{u} R) [Injective Q],
    IsFlasque (Spec R).ringCatSheaf (tilde Q)

def TildeBasicOpenAcyclic : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (f : R) (n : ℕ), 0 < n →
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
    IsZero ((sectionCohomology (Spec R).ringCatSheaf U n).obj (tilde M)) ∧
    IsZero ((openCohomology (Spec R).ringCatSheaf U n).obj (tilde M))

def TildeAffineAcyclic : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (n : ℕ), 0 < n →
    IsZero ((sectionCohomology (Spec R).ringCatSheaf ⊤ n).obj (tilde M))

/-- This includes the empty intersection, which is the whole spectrum. -/
def TildeBasicOpenIntersectionAcyclic : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (s : Finset R) (n : ℕ), 0 < n →
    let U : (Spec R).Opens := s.inf PrimeSpectrum.basicOpen
    IsZero ((sectionCohomology (Spec R).ringCatSheaf U n).obj (tilde M)) ∧
    IsZero ((openCohomology (Spec R).ringCatSheaf U n).obj (tilde M))

open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients in
/-- The same vanishing for the coefficient functor of the original-coefficient
Čech comparison, on distinguished opens including the whole spectrum. -/
def TildeBasicOpenCoefficientAcyclic : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (f : R) (n : ℕ), 0 < n →
    IsZero ((coefficientCohomologyValue.{u,u,u} (Spec R) (Spec R).ringCatSheaf
      (PrimeSpectrum.basicOpen f) n).obj (tilde M))

/-- The tilde image of every injective module resolution is an augmented flasque
resolution, and its global sections over the base ring recover the original complex. -/
def TildeFlasqueResolution : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (I : InjectiveResolution M),
    let F := (tilde.functor R).mapHomologicalComplex (.up ℕ)
    QuasiIso (F.map I.ι) ∧
    (∀ n : ℕ, IsFlasque (Spec R).ringCatSheaf ((F.obj I.cocomplex).X n)) ∧
    Nonempty (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (F.obj I.cocomplex) ≅ I.cocomplex)

end Specs.CommutativeAlgebraNotes.AffineTildeAcyclicity
