import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-! Independent statements for KD-16 (paper.tex, Localization of derivations
and differentials). All localization submonoids are allowed, including those
containing zero. The tensor product represents localization of a module over
any chosen model T of the localized ring. -/
namespace Specs.AdvCommAlg.Differentials.Localization

universe u v w z
noncomputable section
open scoped TensorProduct

def restrictionBijective : Prop :=
  ∀ (A : Type u) (B : Type v) (T : Type w) (N : Type z)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    [AddCommGroup N] [Module T N] [Module B N] [Module A N]
    [IsScalarTower B T N] [IsScalarTower A T N] [IsScalarTower A B N]
    (S : Submonoid B) [IsLocalization S T],
    Function.Bijective (fun E : Derivation A T N => E.compAlgebraMap B)

/-- The inverse s⁻¹ is written as mk' T 1 s; no field inverse or regularity
assumption on the denominator in B is used. -/
def uniqueExtensionFormula : Prop :=
  ∀ (A : Type u) (B : Type v) (T : Type w) (N : Type z)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    [AddCommGroup N] [Module T N] [Module B N] [Module A N]
    [IsScalarTower B T N] [IsScalarTower A T N] [IsScalarTower A B N]
    (S : Submonoid B) [IsLocalization S T] (D : Derivation A B N),
    ∃! E : Derivation A T N,
      (∀ b : B, E (algebraMap B T b) = D b) ∧
      ∀ (b : B) (s : S), E (IsLocalization.mk' T b s) =
        IsLocalization.mk' T 1 s • D b -
          (algebraMap B T b * IsLocalization.mk' T 1 s ^ 2) • D (s : B)

def differentialLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (T : Type w)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    (S : Submonoid B) [IsLocalization S T],
    ∃ e : T ⊗[B] KaehlerDifferential A B ≃ₗ[T] KaehlerDifferential A T,
      ∀ (t : T) (b : B), e (t ⊗ₜ[B] KaehlerDifferential.D A B b) =
        t • KaehlerDifferential.D A T (algebraMap B T b)

/-- The same conclusion for the fraction model S⁻¹Ω itself, with its induced
T-module structure, including the required value on db/1. -/
def localizedDifferential : Prop :=
  ∀ (A : Type u) (B : Type v) (T : Type w)
    [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    (S : Submonoid B) [IsLocalization S T],
    letI : Module T (LocalizedModule S (KaehlerDifferential A B)) :=
      LocalizedModule.moduleOfIsLocalization (S := S) (T := T)
    ∃ e : LocalizedModule S (KaehlerDifferential A B) ≃ₗ[T] KaehlerDifferential A T,
      ∀ b : B, e (LocalizedModule.mk (KaehlerDifferential.D A B b) 1) =
        KaehlerDifferential.D A T (algebraMap B T b)

/-- The hypothesis that the images of U are units supplies the extended base
structure on B by the ring-localization universal property. Thus the assertion
applies without assuming an additional algebra structure on B. -/
def baseLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    (U : Submonoid A) [IsLocalization U A']
    (hU : ∀ s : U, IsUnit (algebraMap A B s)),
    letI : Algebra A' B := (IsLocalization.lift (S := A') hU).toAlgebra
    letI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
      (fun a => (IsLocalization.lift_eq hU a).symm)
    ∃ e : KaehlerDifferential A B ≃ₗ[B] KaehlerDifferential A' B,
      ∀ x, e x = KaehlerDifferential.map A A' B B x

end
end Specs.AdvCommAlg.Differentials.Localization
