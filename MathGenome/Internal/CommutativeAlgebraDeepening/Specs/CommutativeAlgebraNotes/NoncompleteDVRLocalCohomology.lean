import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.PowerSeries.Inverse

open CategoryTheory IsLocalRing
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (Completion IsPowerTorsion completionModule completionScalarTower)

namespace Specs.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology

universe u

variable (k : Type u) [Field k]

/-- The origin of the polynomial affine line. -/
noncomputable abbrev origin : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance : (origin k).IsMaximal :=
  ((Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X).isMaximal
    (by simp)

/-- The local ring of the affine line at the origin. -/
abbrev LocalLine := Localization.AtPrime (origin k)

/-- The image of the polynomial variable in the local ring. -/
noncomputable abbrev parameter : LocalLine k := algebraMap (Polynomial k) _ Polynomial.X

/-- The rational function field, independent of its model by localization of the local ring. -/
abbrev RationalFunctions := FractionRing (Polynomial k)

/-- The natural map from the local ring to the power series ring. -/
noncomputable def seriesMap : LocalLine k →+* PowerSeries k :=
  IsLocalization.lift (M := (origin k).primeCompl)
    (g := Polynomial.coeToPowerSeries.ringHom) fun s => by
      rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.constantCoeff_coe, isUnit_iff_ne_zero]
      intro hs
      exact s.property (by simpa [origin, Ideal.mem_span_singleton, Polynomial.X_dvd_iff] using hs)

noncomputable instance : Algebra (LocalLine k) (PowerSeries k) := (seriesMap k).toAlgebra

/-- The quotient by the image of the local ring in the rational function field. -/
abbrev FractionQuotient :=
  RationalFunctions k ⧸ LinearMap.range (Algebra.linearMap (LocalLine k) (RationalFunctions k))

/-- First local cohomology of the local ring with support in its parameter. -/
noncomputable abbrev TopCohomology : ModuleCat.{u} (LocalLine k) :=
  (IdealTorsion.localCohomology (Ideal.span {parameter k}) 1).obj
    (ModuleCat.of (LocalLine k) (LocalLine k))

def DVRProfile : Prop :=
  ∀ (k : Type u) [Field k], IsDiscreteValuationRing (LocalLine k) ∧
    maximalIdeal (LocalLine k) = Ideal.span {parameter k} ∧
    ringKrullDim (LocalLine k) = 1 ∧
    AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue (LocalLine k) ∧
    Nonempty (ResidueField (LocalLine k) ≃+* k)

/-- The local ring at the origin is incomplete for the topology of its maximal ideal. -/
def Noncomplete : Prop :=
  ∀ (k : Type u) [Field k], ¬ IsAdicComplete (maximalIdeal (LocalLine k)) (LocalLine k)

def FractionQuotientComparison : Prop :=
  ∀ (k : Type u) [Field k], Nonempty (TopCohomology k ≃ₗ[LocalLine k] FractionQuotient k)

def ResidueHullComparison : Prop :=
  ∀ (k : Type u) [Field k] (E : residueFieldEnvelopeValue (LocalLine k)),
    Nonempty (TopCohomology k ≃ₗ[LocalLine k] E.carrier)

def CompletionComparison : Prop :=
  ∀ (k : Type u) [Field k], Nonempty (Completion (LocalLine k) ≃ₐ[LocalLine k] PowerSeries k)

/-- Completion acts on the Matlis dual through its action on the target hull. Power series
carry the regular module structure restricted along the indicated completion isomorphism. -/
def MatlisDualComparison : Prop :=
  ∀ (k : Type u) [Field k] (E : residueFieldEnvelopeValue (LocalLine k)),
    ∃ (h : IsPowerTorsion (LocalLine k) E.carrier)
      (e : Completion (LocalLine k) ≃ₐ[LocalLine k] PowerSeries k),
      letI := completionModule h
      letI := completionScalarTower h
      letI : Module (Completion (LocalLine k)) (PowerSeries k) := Module.compHom _ e.toRingHom
      Nonempty ((TopCohomology k →ₗ[LocalLine k] E.carrier) ≃ₗ[Completion (LocalLine k)] PowerSeries k)

end Specs.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology
