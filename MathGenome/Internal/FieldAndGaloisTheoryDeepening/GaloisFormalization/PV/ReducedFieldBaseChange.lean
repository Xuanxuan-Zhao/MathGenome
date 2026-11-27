import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ReducedFieldBaseChange
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Unramified.Field

open scoped TensorProduct
open Algebra

namespace GaloisFormalization.PV

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The tensor product with a purely transcendental field is a domain. -/
private theorem isDomain_tensor_rationalFunctions (F L ι : Type*)
    [Field F] [Field L] [Algebra F L] :
    IsDomain (L ⊗[F] FractionRing (MvPolynomial ι F)) := by
  let P := MvPolynomial ι F
  let Q := MvPolynomial ι L
  let D := FractionRing P
  have : IsLocalization (algebraMapSubmonoid Q (nonZeroDivisors P)) (Q ⊗[P] D) :=
    IsLocalization.tensor D (nonZeroDivisors P)
  have hsub : algebraMapSubmonoid Q (nonZeroDivisors P) ≤ nonZeroDivisors Q := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h ↦ nonZeroDivisors.ne_zero hp
        (MvPolynomial.map_injective (σ := ι) (algebraMap F L) (algebraMap F L).injective
          (h.trans (map_zero (algebraMap P Q)).symm)))
  let : IsDomain (Q ⊗[P] D) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hsub
  let e : Q ⊗[P] D ≃ₐ[L] L ⊗[F] D := IsPushout.cancelBaseChangeAlg F L P Q D
  exact Function.Injective.isDomain e.symm e.symm.injective

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Passing to the fraction field detects nilpotents in a separable base change. -/
private theorem reducedTensor_of_domain (T U M : Type*)
    [Field T] [CommRing U] [IsDomain U] [Field M] [Algebra T U] [Algebra T M]
    [EssFiniteType T M] [Algebra.IsSeparable T M] : IsReduced (U ⊗[T] M) := by
  let K := FractionRing U
  have : FormallyUnramified T M := FormallyUnramified.of_isSeparable T M
  have : IsReduced (FractionRing U ⊗[T] M) :=
    FormallyUnramified.isReduced_of_field (FractionRing U) _
  let j : U →ₐ[T] K := IsScalarTower.toAlgHom T U (FractionRing U)
  let f := Algebra.TensorProduct.map j (AlgHom.id T M)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap
      (IsFractionRing.injective U K)
  exact isReduced_of_injective f hf

/-- The field step, with essential finite type allowing fraction fields of finite-type domains. -/
private theorem reducedTensor_fields (F L M : Type*)
    [Field F] [CharZero F] [Field L] [Field M] [Algebra F L] [Algebra F M]
    [EssFiniteType F M] : IsReduced (L ⊗[F] M) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F M
  let T := IntermediateField.adjoin F (Set.range ((↑) : s → M))
  have : CharZero T := charZero_of_injective_algebraMap (algebraMap F T).injective
  have : Algebra.IsAlgebraic T M := hs.isAlgebraic_field
  have : Algebra.IsSeparable T M := inferInstance
  have : EssFiniteType T M := EssFiniteType.of_comp F T M
  have : IsDomain (L ⊗[F] FractionRing (MvPolynomial s F)) :=
    isDomain_tensor_rationalFunctions F L s
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl (R := F) (A₁ := L)) hs.1.aevalEquivField
  have : IsDomain (L ⊗[F] T) := Function.Injective.isDomain e.symm e.symm.injective
  let : Algebra (↥T) (L ⊗[F] (↥T)) := Algebra.TensorProduct.rightAlgebra
  have := reducedTensor_of_domain (↥T) (L ⊗[F] (↥T)) M
  let cancel := IsPushout.cancelBaseChangeAlg F L T (L ⊗[F] T) M
  exact isReduced_of_injective cancel.symm cancel.symm.injective

private theorem reducedTensor_finiteType_domain (F L B : Type*)
    [Field F] [CharZero F] [Field L] [CommRing B] [IsDomain B]
    [Algebra F L] [Algebra F B] [FiniteType F B] : IsReduced (L ⊗[F] B) := by
  have : EssFiniteType B (FractionRing B) := EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  have : EssFiniteType F (FractionRing B) := EssFiniteType.comp F B (FractionRing B)
  have : IsReduced (L ⊗[F] FractionRing B) := reducedTensor_fields F L (FractionRing B)
  let j := IsScalarTower.toAlgHom F B (FractionRing B)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F L) j)
    (Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap
      (IsFractionRing.injective B (FractionRing B)))

/-- Reducedness is preserved by arbitrary field base change in characteristic zero
for finitely generated commutative algebras. -/
theorem reducedFieldBaseChange (F L A : Type*) [Field F] [CharZero F] [Field L] [CommRing A]
    [Algebra F L] [Algebra F A] [Algebra.FiniteType F A] [IsReduced A] :
    IsReduced (L ⊗[F] A) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  let I := minimalPrimes A
  let : Fintype I := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  let B (p : I) := A ⧸ (p : Ideal A)
  let f : A →ₐ[F] ∀ p : I, B p := AlgHom.pi fun p ↦ Ideal.Quotient.mkₐ F (p : Ideal A)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    have hmem : x ∈ sInf (minimalPrimes A) := by
      rw [Ideal.mem_sInf]
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx (⟨p, hp⟩ : I))
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    change x ∈ nilradical A at hmem
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] using hmem
  have (p : I) : IsReduced (L ⊗[F] B p) := by
    have : (p : Ideal A).IsPrime := p.property.1.1
    exact reducedTensor_finiteType_domain F L (B p)
  let g := Algebra.TensorProduct.map (AlgHom.id F L) f
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  let e := Algebra.TensorProduct.piRight F F L B
  exact isReduced_of_injective (e.toAlgHom.comp g) (e.injective.comp hg)

end GaloisFormalization.PV
