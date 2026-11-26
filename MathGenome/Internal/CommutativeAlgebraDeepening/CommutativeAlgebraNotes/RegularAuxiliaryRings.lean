import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatLocalRegularity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalLocalization
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalRing

/-! Polynomial rings, finite separable scalar extensions and completions
in Lemma 5.2. -/

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence

theorem regularRing_polynomial (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : RegularRing R) : RegularRing (Polynomial R) := by
  let : IsRegularRing R := (regularRing_iff R).mp h
  exact (regularRing_iff _).mpr (Polynomial.isRegularRing_of_isRegularRing R)

theorem regularRing_mvPolynomial (R : Type u) (ι : Type v) [CommRing R]
    [IsNoetherianRing R] [Finite ι] (h : RegularRing R) :
    RegularRing (MvPolynomial ι R) := by
  let : IsRegularRing R := (regularRing_iff R).mp h
  exact (regularRing_iff _).mpr (MvPolynomial.isRegularRing_of_isRegularRing R)

/-- Regularity ascends along an étale map because its local closed fibres are fields. -/
private theorem regularRing_of_etale (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.Etale A B]
    (h : RegularRing A) : IsRegularRing B := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  apply (regularRing_iff B).mp
  intro q hq
  let p := q.under A
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap Ap Bq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have : Algebra.EssFiniteType Ap Bq := .of_comp A _ _
  have hfield : IsField (Bq ⧸ (maximalIdeal Ap).map (algebraMap Ap Bq)) :=
    Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
  let := hfield.toField
  exact isRegularLocalRing_of_flatLocal_of_regularClosedFiber Ap Bq (h p) inferInstance

theorem regularRing_separableScalarExtension
    (k : Type u) (L : Type v) (R : Type w) [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R] [Module.Finite k L] [Algebra.IsSeparable k L]
    [IsNoetherianRing R] (h : RegularRing R) : RegularRing (L ⊗[k] R) := by
  let : Algebra.Etale k L := ⟨Algebra.FormallyEtale.of_isSeparable k L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  -- Use a representative in the universe of R for the flat local ascent theorem.
  have := Algebra.FiniteType.small (R := R) (S := R ⊗[k] L)
  let B := Shrink.{w} (R ⊗[k] L)
  let e : B ≃ₐ[R] R ⊗[k] L := Shrink.algEquiv R _
  let : Algebra.Etale R B := Algebra.Etale.of_equiv e.symm
  let : IsRegularRing B := regularRing_of_etale R B h
  let extensionEquiv := e.toRingEquiv.trans (Algebra.TensorProduct.comm k R L).toRingEquiv
  let : IsRegularRing (L ⊗[k] R) := IsRegularRing.of_ringEquiv extensionEquiv
  exact (regularRing_iff _).mpr inferInstance

theorem regularLocalRing_completion (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (h : IsRegularLocalRing R) :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  let B := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing B :=
    P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)
  apply isRegularLocalRing_of_flatLocal_of_regularClosedFiber R B h
  rw [← AdicCompletion.maximalIdeal_eq_map]
  exact (inferInstance : IsRegularLocalRing (ResidueField B))

theorem regularRing_completion (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (h : IsRegularLocalRing R) :
    RegularRing (AdicCompletion (maximalIdeal R) R) := by
  let := regularLocalRing_completion R h
  exact AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime _

end CommutativeAlgebraNotes.Excellence
