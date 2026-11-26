import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExtendDerivations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularAuxiliaryRings
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivationHypersurface
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.GeometricClosedPointRegularity
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.Ideal

/-! Derivations and regular hypersurfaces. -/

namespace CommutativeAlgebraNotes

/-- Differentiate the coefficients of a polynomial, keeping the variable fixed. -/
noncomputable def polynomialDerivation {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) : Derivation ℤ (Polynomial R) (Polynomial R) :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem polynomialDerivation_C {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (a : R) :
    polynomialDerivation D (Polynomial.C a) = Polynomial.C (D a) := by
  simp [polynomialDerivation, PolynomialModule.equivPolynomialSelf_apply_eq, Polynomial.monomial_zero_left]

@[simp]
theorem polynomialDerivation_X {R : Type*} [CommRing R] (D : Derivation ℤ R R) :
    polynomialDerivation D Polynomial.X = 0 := by
  simp [polynomialDerivation]

namespace Excellence

private theorem regularLocalRing_quotient_span_singleton {A : Type*}
    [CommRing A] [IsRegularLocalRing A] {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) (ha₂ : a ∉ IsLocalRing.maximalIdeal A ^ 2) :
    IsRegularLocalRing (A ⧸ Ideal.span {a}) := by
  let m := IsLocalRing.maximalIdeal A
  let x : Fin 1 → m := fun _ => ⟨a, ha⟩
  have hx : LinearIndependent (IsLocalRing.ResidueField A) (fun i => m.toCotangent (x i)) := by
    rw [linearIndependent_unique_iff]
    exact fun h => ha₂ ((m.toCotangent_eq_zero (x default)).mp h)
  have hd : ringKrullDim A = (m.spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have h := (AdvCommAlg.Smooth.regular_quotient_of_cotangent_independent hd x hx).1
  change IsRegularLocalRing (A ⧸ Ideal.span (Set.range (fun _ : Fin 1 => a))) at h
  rwa [Set.range_const] at h

/-- A defining equation whose derivative is a unit gives a regular quotient. -/
theorem regularRing_quotient_span_singleton_of_isUnit_derivation
    {R : Type*} [CommRing R] [IsNoetherianRing R] (hR : RegularRing R)
    (D : Derivation ℤ R R) (g : R) (hg : IsUnit (D g)) :
    RegularRing (R ⧸ Ideal.span {g}) := by
  intro q hq
  let I : Ideal R := Ideal.span {g}
  let p := q.comap (Ideal.Quotient.mk I)
  let : p.IsPrime := Ideal.comap_isPrime _ q
  let A := Localization.AtPrime p
  let : IsRegularLocalRing A := hR p
  let a := algebraMap R A g
  have hp : g ∈ p := by
    change Ideal.Quotient.mk I g ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton g))]
    exact q.zero_mem
  have ha : a ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A p g).mpr hp
  let E := localizationDerivation (L := A) p.primeCompl D
  have hE : IsUnit (E a) := by
    dsimp only [E, a]
    rw [localizationDerivation_algebraMap]
    exact hg.map (algebraMap R A)
  have ha₂ : a ∉ IsLocalRing.maximalIdeal A ^ 2 := by
    intro h
    have hm : E a ∈ IsLocalRing.maximalIdeal A := by
      simpa only [pow_one] using derivation_mem_ideal_pow E (IsLocalRing.maximalIdeal A) 1 h
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((IsLocalRing.maximalIdeal A).eq_top_of_isUnit_mem hm hE)
  let J := I.map (algebraMap R A)
  have hJ : J = Ideal.span {a} := by
    simp [J, I, a, Ideal.map_span]
  let : IsRegularLocalRing (A ⧸ J) := by
    rw [hJ]
    exact regularLocalRing_quotient_span_singleton ha ha₂
  have hS : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl :=
    q.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalization q.primeCompl (A ⧸ J) :=
    hS ▸ (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) (A ⧸ J))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (A ⧸ J) (Localization.AtPrime q)).toRingEquiv

/-- Regularity of the binomial hypersurface (T^n-f) from Lemma 5.3. -/
theorem regularRing_quotient_X_pow_sub_C_of_isUnit_derivation
    {R : Type*} [CommRing R] [IsNoetherianRing R] (hR : RegularRing R)
    (D : Derivation ℤ R R) (f : R) (hf : IsUnit (D f)) (n : ℕ) (_hn : 1 ≤ n) :
    RegularRing (Polynomial R ⧸ Ideal.span {Polynomial.X ^ n - Polynomial.C f}) := by
  apply regularRing_quotient_span_singleton_of_isUnit_derivation
    (regularRing_polynomial R hR) (polynomialDerivation D)
  change IsUnit (polynomialDerivation D (Polynomial.X ^ n - Polynomial.C f))
  rw [map_sub, Derivation.leibniz_pow, polynomialDerivation_X, smul_zero, smul_zero,
    zero_sub, polynomialDerivation_C]
  exact (hf.map (Polynomial.C : R →+* Polynomial R)).neg

/-- The localization, completion, and hypersurface assertions of Lemma 5.3. -/
theorem derivations_and_regular_hypersurface :
    Specs.derivations_and_regular_hypersurfaceType :=
  ⟨exists_localization_derivation, exists_adicCompletion_derivation,
    regularRing_quotient_X_pow_sub_C_of_isUnit_derivation⟩

end Excellence
end CommutativeAlgebraNotes
