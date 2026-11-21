import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Polynomial.Coeff

/-! The actual subalgebra and origin localization in SN-12. No characteristic
restriction is placed on the coefficient field. -/
namespace AdvCommAlg.Normality.Cusp
open Polynomial
universe u
variable (k : Type u) [Field k]

noncomputable def algebra : Subalgebra k k[X] :=
  Algebra.adjoin k {X ^ 2, X ^ 3}

noncomputable def square : algebra k :=
  ⟨X ^ 2, Algebra.subset_adjoin (Set.mem_insert _ _)⟩

noncomputable def cube : algebra k :=
  ⟨X ^ 3, Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

noncomputable def residue : algebra k →+* k :=
  Polynomial.constantCoeff.comp (algebra k).val

noncomputable def origin : Ideal (algebra k) := RingHom.ker (residue k)

theorem residue_surjective : Function.Surjective (residue k) := by
  intro a
  exact ⟨algebraMap k (algebra k) a, by simp [residue, Polynomial.constantCoeff]⟩

instance origin_isMaximal : (origin k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (residue k) (residue_surjective k)

abbrev Local := Localization.AtPrime (origin k)

noncomputable def parameter : FractionRing (algebra k) :=
  algebraMap (algebra k) (FractionRing (algebra k)) (cube k) /
    algebraMap (algebra k) (FractionRing (algebra k)) (square k)

/-- The canonical injection of the displayed localization into the cusp fraction field. -/
noncomputable def localToFraction : Local k →+* FractionRing (algebra k) :=
  algebraMap (Local k) (FractionRing (algebra k))

/-- The map induced by the original inclusion into the polynomial ring. -/
noncomputable def fractionEmbedding :
    FractionRing (algebra k) →+* FractionRing k[X] :=
  IsFractionRing.lift (A := algebra k) (K := FractionRing (algebra k))
    (g := (algebraMap k[X] (FractionRing k[X])).comp (algebra k).val.toRingHom)
    (by
      intro a b h
      apply Subtype.ext
      exact IsFractionRing.injective k[X] (FractionRing k[X]) h)

end AdvCommAlg.Normality.Cusp

namespace AdvCommAlg.Normality.Specs
open Polynomial Cusp
universe u

/-- SN-12, first example, including the concrete origin, finite integral
extension, and the fractional parameter that obstructs normality. The Serre
predicates here are the independent shared predicates of SN-01 and CM-11a. -/
def cuspExampleType : Prop :=
  ∀ (k : Type u) [Field k],
    origin k = Ideal.span {square k, cube k} ∧
    (origin k).IsMaximal ∧
    IsNoetherianRing (algebra k) ∧
    Module.Finite (algebra k) k[X] ∧
    Algebra.IsIntegral (algebra k) k[X] ∧
    IsIntegral (algebra k) (X : k[X]) ∧
    fractionEmbedding k (parameter k) = algebraMap k[X] (FractionRing k[X]) X ∧
    IsIntegral (algebra k) (parameter k) ∧
    IsIntegral (Local k) (parameter k) ∧
    parameter k ∉ Set.range (localToFraction k) ∧
    algebraMap k[X] (FractionRing k[X]) X ∉
      Set.range ((fractionEmbedding k).comp (localToFraction k)) ∧
    IsDomain (Local k) ∧
    IsLocalRing (Local k) ∧
    ringKrullDim (algebra k) = 1 ∧
    ringKrullDim k[X] = 1 ∧
    ringKrullDim (Local k) = 1 ∧
    ∃ hN : IsNoetherianRing (Local k),
      @CohenMacaulay.Specs.RingSerreConditionValue (Local k) _ hN 2 ∧
      ¬ @RegularInCodimensionValue (Local k) _ hN 1

end AdvCommAlg.Normality.Specs
