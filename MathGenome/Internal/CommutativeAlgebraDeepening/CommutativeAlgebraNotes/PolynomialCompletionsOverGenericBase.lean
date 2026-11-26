import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Pi

namespace CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase

open scoped Polynomial TensorProduct
open IsLocalRing
open Excellence (GeometricallyRegular regularRing_iff)
open _root_.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion (Factor PrimesOver)
open _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
  (CompletedPolynomialStalk GenericConstantsFibre)

universe u

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] Polynomial.algebra FractionRing.liftAlgebra

private theorem regularFactor {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    [IsRegularRing (∀ i, R i)] (i : ι) : IsRegularRing (R i) := by
  classical
  letI : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  let e : ∀ j, R j := Pi.single i 1
  have he : IsIdempotentElem e := by
    change e * e = e
    ext j
    by_cases h : j = i
    · subst j
      simp [e]
    · simp [e, Pi.single_eq_of_ne h]
  letI : IsLocalization.Away e (R i) := IsLocalization.away_of_isIdempotentElem_of_mul he
    (fun x y => by
      change x i = y i ↔ e * x = e * y
      constructor
      · intro h
        ext j
        by_cases hj : j = i
        · subst j
          simpa [e] using h
        · simp [e, Pi.single_eq_of_ne hj]
      · intro h
        simpa [e] using congrFun h i)
    (fun x => ⟨Pi.single i x, Pi.single_eq_same i x⟩)
  letI : IsNoetherianRing (R i) :=
    IsLocalization.isNoetherianRing (Submonoid.powers e) (R i) inferInstance
  refine (isRegularRing_iff (R := R i)).2 fun q hq => ?_
  let p := q.comap (algebraMap (∀ j, R j) (R i))
  letI : p.IsPrime := hq.comap _
  letI : IsLocalization p.primeCompl (Localization.AtPrime q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers e) _ q
  exact IsRegularLocalRing.of_ringEquiv
    (Localization.algEquiv p.primeCompl (Localization.AtPrime q)).toRingEquiv

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem ofFiniteNormalization (S A : Type u) [CommRing S] [CommRing A]
    [IsDomain S] [IsDomain A] [IsNoetherianRing S] [IsNoetherianRing A]
    [Algebra S A] [Module.Finite S A] (hinj : Function.Injective (algebraMap S A))
    (P : Ideal A[X]) [P.IsPrime]
    (hreg : ∀ (p : Ideal S[X]) [p.IsPrime],
      GeometricallyRegular (FractionRing S) (GenericConstantsFibre p)) :
    GeometricallyRegular (FractionRing A) (GenericConstantsFibre P) := by
  classical
  let p := P.comap (algebraMap S[X] A[X])
  letI : p.IsPrime := Ideal.IsPrime.comap _
  let q : PrimesOver p A[X] := ⟨⟨P, inferInstance⟩, rfl⟩
  let C := CompletedPolynomialStalk p
  letI : Algebra S[X] C := inferInstanceAs (Algebra S[X] (CompletedPolynomialStalk p))
  let U := C ⊗[S[X]] A[X]
  let B := (j : PrimesOver p A[X]) → Factor p j
  letI : Module.Finite S[X] A[X] :=
    Module.Finite.of_surjective (Algebra.IsPushout.equiv S S[X] A A[X]).toLinearMap
      (Algebra.IsPushout.equiv S S[X] A A[X]).surjective
  haveI : Finite (PrimesOver p A[X]) :=
    FiniteAlgebraCompletion.finitePrimes S[X] A[X] p
  letI : Fintype (PrimesOver p A[X]) := Fintype.ofFinite _
  -- The product decomposition is compatible with the constant algebra A.
  letI : Algebra A[X] U := Algebra.TensorProduct.rightAlgebra
  letI : Algebra A U := ((algebraMap A[X] U).comp (algebraMap A A[X])).toAlgebra
  letI : IsScalarTower A A[X] U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S A[X] U := IsScalarTower.to₁₃₄ S S[X] A[X] U
  letI : IsScalarTower S A U := IsScalarTower.to₁₂₄ S A A[X] U
  letI : IsScalarTower S C U := IsScalarTower.to₁₃₄ S S[X] C U
  letI : Algebra.IsPushout S C A U :=
    (Algebra.IsPushout.comp_iff S S[X] A (S' := A[X]) (T := C)).2 inferInstance
  letI : Algebra.IsPushout S A C U :=
    (show Algebra.IsPushout S C A U from inferInstance).symm
  let eBase : (A ⊗[S] C) ≃ₐ[A] U := Algebra.IsPushout.equiv S A C U
  let eDecomp : U ≃ₐ[A] B :=
    { __ := (FiniteAlgebraCompletion.decomposition p).toRingEquiv
      commutes' a := by
        funext j
        change FiniteAlgebraCompletion.decomposition p
          ((1 : C) ⊗ₜ[S[X]] Polynomial.C a) j = algebraMap A (Factor p j) a
        rw [FiniteAlgebraCompletion.decomposition_one_tmul]
        exact (IsScalarTower.algebraMap_apply A A[X] (Factor p j) a).symm }
  let e := eBase.trans eDecomp
  -- Every finite test field over Frac(A) is finite over Frac(S).
  let K := FractionRing A
  let K₀ := FractionRing S
  letI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).2 hinj
  letI : Algebra K₀ K := FractionRing.liftAlgebra S K
  letI : IsScalarTower S K₀ K := FractionRing.isScalarTower_liftAlgebra S K
  letI : Module.Finite K₀ K := inferInstanceAs (FiniteDimensional (FractionRing S) (FractionRing A))
  intro L _ _ _
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K₀ L := ((algebraMap K L).comp (algebraMap K₀ K)).toAlgebra
  letI : IsScalarTower K₀ K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S L := ((algebraMap K L).comp (algebraMap S K)).toAlgebra
  letI : IsScalarTower S K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S A L := IsScalarTower.to₁₂₄ S A K L
  letI : IsScalarTower S K₀ L := IsScalarTower.to₁₂₄ S K₀ K L
  letI : Module.Finite K₀ L := Module.Finite.trans K L
  obtain ⟨hNoeth, hRegular⟩ := (hreg p).regular_tensorProduct L
  letI : IsRegularRing (L ⊗[K₀] (K₀ ⊗[S] C)) := (regularRing_iff _).mp hRegular
  let eL : (L ⊗[K₀] (K₀ ⊗[S] C)) ≃ₐ[L]
      ((j : PrimesOver p A[X]) → L ⊗[A] Factor p j) :=
    (Algebra.TensorProduct.cancelBaseChange S K₀ L L C).trans
      ((Algebra.TensorProduct.cancelBaseChange S A L L C).symm.trans
        ((Algebra.TensorProduct.congr (.refl : L ≃ₐ[L] L) e).trans
          (Algebra.TensorProduct.piRight A L L (Factor p))))
  letI : IsRegularRing ((j : PrimesOver p A[X]) → L ⊗[A] Factor p j) :=
    IsRegularRing.of_ringEquiv (R := L ⊗[K₀] (K₀ ⊗[S] C)) eL.toRingEquiv
  letI : IsRegularRing (L ⊗[A] CompletedPolynomialStalk P) :=
    regularFactor (R := fun j : PrimesOver p A[X] => L ⊗[A] Factor p j) q
  let eP := Algebra.TensorProduct.cancelBaseChange A K L L (CompletedPolynomialStalk P)
  letI : IsRegularRing (L ⊗[K] (GenericConstantsFibre P)) :=
    IsRegularRing.of_ringEquiv (R := L ⊗[A] CompletedPolynomialStalk P) eP.symm.toRingEquiv
  exact ⟨inferInstance, (regularRing_iff _).mpr inferInstance⟩

/-- The generic fibre over the constant ring of a completed polynomial stalk
is geometrically regular. -/
theorem overCompleteLocalDomain :
    _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase.OverCompleteLocalDomain.{u} := by
  intro A _ _ _ _ _ P _
  obtain ⟨d, _, h⟩ := CoefficientRings.finitePowerSeriesNormalization A
  rcases h with ⟨_, σ, x, F, _, _, _, _, _, _, hF⟩ | ⟨p, hp, _, _, h⟩
  · obtain ⟨_, _, hRegular, _, _, hinj, _, hFinite, _⟩ := hF
    let S := MvPowerSeries (Fin d) (ResidueField A)
    letI : IsDomain S := NoZeroDivisors.to_isDomain _
    letI : IsRegularLocalRing S := hRegular
    letI : Algebra S A := F.toAlgebra
    letI : Module.Finite S A := hFinite
    exact ofFiniteNormalization S A hinj P
      (PolynomialCompletionsOverRegularConstants.overField (ResidueField A) d)
  · obtain ⟨_, _, _, _, D, _, _, _, _, _, hUniformizer, _, _, _, F, _, _, _, _, _, _, _, hF⟩ := h
    obtain ⟨_, _, hRegular, _, _, hinj, _, hFinite, _⟩ := hF
    letI : Fact p.Prime := ⟨hp⟩
    have hirr : Irreducible (p : D) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : D)).2 hUniformizer
    let S := MvPowerSeries (Fin (d - 1)) D
    letI : IsDomain S := NoZeroDivisors.to_isDomain _
    letI : IsRegularLocalRing S := hRegular
    letI : Algebra S A := F.toAlgebra
    letI : Module.Finite S A := hFinite
    exact ofFiniteNormalization S A hinj P
      (PolynomialCompletionsOverRegularConstants.overCompleteDVR D p hirr (d - 1))

end

end CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase
