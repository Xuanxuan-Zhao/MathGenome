import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Noetherian.Defs
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion

namespace Specs.CommutativeAlgebraNotes.LocalizationOfInjectives

universe u v w

/-- Lemma 1.4 for any model of localization away from `f`. Baer's criterion expresses
injectivity independently of the relative sizes of the ring and module universes. -/
def localizationAwaySurjectiveKerOfBaerType : Prop :=
  ∀ {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]
    {Qf : Type w} [AddCommGroup Qf] [Module R Qf] [IsNoetherianRing R] (f : R) (loc : Q →ₗ[R] Qf)
    [IsLocalizedModule.Away f loc], Module.Baer R Q →
      Function.Surjective loc ∧ LinearMap.ker loc = IdealTorsion.idealTorsion (Ideal.span {f}) Q

/-- The injective-module formulation in a module universe containing the ring. -/
def localizationAwaySurjectiveKerType : Prop :=
  ∀ {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]
    {Qf : Type w} [AddCommGroup Qf] [Module R Qf] [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R Q]
    (f : R) (loc : Q →ₗ[R] Qf) [IsLocalizedModule.Away f loc],
      Function.Surjective loc ∧ LinearMap.ker loc = IdealTorsion.idealTorsion (Ideal.span {f}) Q

end Specs.CommutativeAlgebraNotes.LocalizationOfInjectives
