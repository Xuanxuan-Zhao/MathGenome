import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.SimpleOperatorComponents
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.SpecializationNonunits
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.FiniteTypeConstants
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Derivation.MapCoeffs

namespace GaloisFormalization.PV.Operator

open Polynomial

universe u v w

section Algebraicity

variable {kind : OperatorKind} {k : Type u} {S : Type v}
  [Field k] [CharZero k] [CommRing S] [Algebra k S]
  {D : OperatorField kind k} {E : Operator kind S}

private theorem not_transcendental_of_unit_translates
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (D : OperatorField kind k) {x : S} (f : S →ₐ[k] B)
    (hu : ∀ a : D.constantSubfield, IsUnit (x - algebraMap k S (a : k))) :
    ¬ Transcendental k (f x) := by
  intro ht
  have hfinite := finite_unit_specializations (f x) ht
  have hinfinite : (Set.range D.constantSubfield.subtype).Infinite :=
    Set.infinite_range_of_injective Subtype.val_injective
  apply hinfinite.not_finite
  apply hfinite.subset
  rintro _ ⟨a, rfl⟩
  change IsUnit (f x - algebraMap k B (a : k))
  simpa only [map_sub, AlgHom.commutes] using (hu a).map f

variable [Algebra.FiniteType k S]

private theorem constant_isIntegral (hS : E.IsSimple) (h : D.IsAlgebra E)
    (c : E.constantSubring) : IsIntegral k (c : S) := by
  classical
  let : Nontrivial S := hS.1
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let : Field E.constantSubring := (E.isField_constantSubring_of_isSimple hS).toField
  by_contra hnot
  have ht : Transcendental k (c : S) := fun ha => hnot ha.isIntegral
  have hu (a : D.constantSubfield) : IsUnit ((c : S) - algebraMap k S (a : k)) := by
    let f := RingHom.mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩
    have hne : c - f a ≠ 0 := by
      intro hz
      have heq : (c : S) = algebraMap k S (a : k) :=
        congrArg Subtype.val (sub_eq_zero.mp hz)
      exact ht ⟨X - C (a : k), (monic_X_sub_C _).ne_zero, by
        simp only [map_sub, aeval_X, aeval_C, heq, sub_self]⟩
    exact (isUnit_iff_ne_zero.mpr hne).map E.constantSubring.subtype
  cases kind with
  | differential =>
    let : Algebra ℚ S := Algebra.compHom S (algebraMap ℚ k)
    let : IsDomain S := E.isDomain_of_isSimple hS
    exact not_transcendental_of_unit_translates D (AlgHom.id k S) hu ht
  | difference =>
    obtain ⟨hfinite, _, hdomain, e, _, _, _, _, he, _⟩ :=
      simpleDifferenceComponents E.toRingEquiv hS
    let : Fintype (minimalPrimes S) := Fintype.ofFinite _
    let (i : minimalPrimes S) : IsDomain (S ⧸ i.val) := hdomain i
    let q (i : minimalPrimes S) : S →ₐ[k] S ⧸ i.val := _root_.Ideal.Quotient.mkₐ k i.val
    have hq (i : minimalPrimes S) : IsIntegral k (q i (c : S)) :=
      isAlgebraic_iff_isIntegral.mp (not_not.mp (not_transcendental_of_unit_translates D (q i) hu))
    -- A product of monic relations for the components kills the element in S.
    choose p hmonic hroot using hq
    refine hnot ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hmonic i), ?_⟩
    apply e.injective
    funext i
    rw [he, _root_.map_zero]
    change q i (aeval (c : S) (∏ j, p j)) = 0
    rw [← aeval_algHom_apply, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hroot i)

end Algebraicity

section Descent

variable {kind : OperatorKind} {k : Type u} {S : Type v}
  [Field k] [CommRing S] [Algebra k S]
  {D : OperatorField kind k} {E : Operator kind S}

private theorem isConstant_minpoly_coeff (h : D.IsAlgebra E)
    {c : S} (hc : E.IsConstant c) (hi : IsIntegral k c) (n : ℕ) :
    D.IsConstant ((minpoly k c).coeff n) := by
  let p := minpoly k c
  have hp : p.Monic := minpoly.monic hi
  have hroot : aeval c p = 0 := minpoly.aeval k c
  cases kind with
  | differential =>
    let : Differential k := ⟨D.toDerivation⟩
    let : Differential S := ⟨E.toDerivation⟩
    let : DifferentialAlgebra k S := ⟨fun a => (h a).symm⟩
    let q := Differential.mapCoeffs p
    have hcoeff (i : ℕ) : q.coeff i = D.toDerivation (p.coeff i) := rfl
    have hq : aeval c q = 0 := by
      have heval := Differential.deriv_aeval_eq c p
      change E.toDerivation (aeval c p) =
        aeval c q + aeval c p.derivative * E.toDerivation c at heval
      change E.toDerivation c = 0 at hc
      simpa only [hroot, _root_.map_zero, hc, mul_zero, add_zero] using heval.symm
    have hdeg : q.degree < p.degree := by
      rw [degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
      intro i hle
      rw [hcoeff]
      rcases hle.eq_or_lt with rfl | hlt
      · rw [hp.coeff_natDegree, Derivation.map_one_eq_zero]
      · rw [coeff_eq_zero_of_natDegree_lt hlt, _root_.map_zero]
    have hzero : q = 0 := by
      by_contra hne
      exact (minpoly.degree_le_of_ne_zero k c hne hq).not_gt hdeg
    change D.toDerivation (p.coeff n) = 0
    rw [← hcoeff, hzero, coeff_zero]
  | difference =>
    let σ := D.toRingEquiv.toRingHom
    let τ := E.toRingEquiv.toRingHom
    have hcompat : (algebraMap k S).comp σ = τ.comp (algebraMap k S) :=
      _root_.RingHom.ext h
    have hfix : τ c = c := hc
    have hmap : aeval c (p.map σ) = 0 := by
      simpa only [hfix, hroot, _root_.map_zero] using
        (map_aeval_eq_aeval_map hcompat p c).symm
    -- Applying the automorphism preserves monicity and cannot raise the degree.
    have heq : p.map σ = p :=
      minpoly.unique_of_degree_le_degree_minpoly k c (hp.map σ) hmap degree_map_le
    change σ (p.coeff n) = p.coeff n
    rw [← coeff_map, heq]

end Descent

/-- A simple finite-type operator algebra over a Picard–Vessiot base field has
exactly the constants of that field, via the given inclusion. -/
theorem constants_finiteType {kind : OperatorKind} {k : Type u} {S : Type v}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (D : OperatorField kind k) (E : Operator kind S)
    (hk : D.IsBaseField) (hS : E.IsSimple) (h : D.IsAlgebra E) :
    Function.Bijective (RingHom.mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩) := by
  let : CharZero k := hk.1
  let : IsAlgClosed D.constantSubfield := hk.2
  let : Field E.constantSubring := (E.isField_constantSubring_of_isSimple hS).toField
  let f : D.constantSubfield →+* E.constantSubring :=
    RingHom.mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩
  apply IsAlgClosed.ringHom_bijective_of_isIntegral f
  let : Algebra D.constantSubfield E.constantSubring := f.toAlgebra
  intro c
  have hi := constant_isIntegral hS h c
  let p := minpoly k (c : S)
  have hp : p.Monic := minpoly.monic hi
  let ι := D.constantSubfield.subtype
  have hlift : p ∈ lifts ι := (lifts_iff_coeff_lifts p).mpr fun n =>
    ⟨⟨p.coeff n, (mem_constantSubfield D _).mpr
      (isConstant_minpoly_coeff h ((mem_constantSubring E _).mp c.property) hi n)⟩, rfl⟩
  obtain ⟨q, hq, _, hmonic⟩ := lifts_and_degree_eq_and_monic hlift hp
  refine ⟨q, hmonic, ?_⟩
  change aeval c q = 0
  apply (show Function.Injective E.constantSubring.subtype from Subtype.val_injective)
  have hcompat : (algebraMap k S).comp ι =
      E.constantSubring.subtype.comp (algebraMap D.constantSubfield E.constantSubring) := rfl
  rw [_root_.map_zero, map_aeval_eq_aeval_map hcompat, hq]
  exact minpoly.aeval k (c : S)

/-- The same inclusion identifies the base constants with those in the total
ring of fractions, for its compatible operator. -/
theorem constants_finiteType_fractionRing
    {kind : OperatorKind} {k : Type u} {S : Type v} {Q : Type w}
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [CommRing Q] [Algebra S Q] [IsFractionRing S Q]
    (D : OperatorField kind k) (E : Operator kind S) (F : Operator kind Q)
    (hk : D.IsBaseField) (hS : E.IsSimple)
    (h : D.IsAlgebra E) (hQ : E.Commutes F (algebraMap S Q)) :
    Function.Bijective
      ((RingHom.mapConstants (D := E) (E := F) ⟨algebraMap S Q, hQ⟩).comp
        (RingHom.mapConstants (D := D) (E := E) ⟨algebraMap k S, h⟩)) :=
  (constants_fractionRing E F hS hQ).1.comp (constants_finiteType D E hk hS h)

end GaloisFormalization.PV.Operator
