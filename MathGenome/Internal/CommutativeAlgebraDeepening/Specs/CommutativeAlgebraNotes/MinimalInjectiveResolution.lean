import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MinimalInjectiveResolutionSocles
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Specs.CommutativeAlgebraNotes.MinimalInjectiveResolution

open CategoryTheory IsLocalRing AdvCommAlg.Depth
open _root_.CommutativeAlgebraNotes.MinimalInjectiveResolutionSoclesSpecs

universe u

/-- Every module has a resolution by the injective hulls of its cosyzygies with
zero differentials after applying `Hom_R(k, -)`. -/
def resolutionWithZeroResidueHomDifferentialType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : ModuleCat.{u} R),
    ∃ J : Resolution X,
      ∀ (i j : ℕ) (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X i),
        f ≫ J.toInjectiveResolution.cocomplex.d i j = 0

/-- The maximal-ideal power torsion of an injective with finite-dimensional socle
is a power of the chosen residue-field hull with one copy per basis vector. -/
def injectiveTorsionEquivHullPowerType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue R)
    {J : Type u} [AddCommGroup J] [Module R J],
    Module.Injective R J → FiniteDimensional (ResidueField R) (Socle R J) →
      Nonempty (IdealTorsion.idealTorsion (maximalIdeal R) J ≃ₗ[R]
        (Fin (Module.finrank (ResidueField R) (Socle R J)) → E.carrier))

end Specs.CommutativeAlgebraNotes.MinimalInjectiveResolution
