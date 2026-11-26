import Specs.LinearAlgebraicGroups.Affine.GenericFreeness
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.Basic

open Module MvPolynomial
open scoped TensorProduct

namespace LinearAlgebraicGroups

private theorem finite_degree_generators {σ ι : Type*} [Finite σ]
    (K : Type*) [Field K] (d : ι → σ →₀ ℕ) :
    ∃ t : Finset ι, ∀ i, ∃ j ∈ t, d j ≤ d i := by
  classical
  let v : ι → MvPolynomial σ K := fun i => monomial (d i) 1
  let I := Ideal.span (Set.range v)
  have hfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨T, hT, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hpre (p : T) : ∃ i, v i = p.1 := hT p.2
  choose pick hpick using hpre
  let t := Finset.univ.image pick
  have himage : (↑T : Set (MvPolynomial σ K)) = (fun a => monomial a 1) '' (d '' ↑t) := by
    ext p
    constructor
    · intro hp
      exact ⟨d (pick ⟨p, hp⟩), ⟨pick ⟨p, hp⟩, by simp [t], rfl⟩, hpick ⟨p, hp⟩⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
      change v (pick q) ∈ T
      rw [hpick]
      exact q.2
  refine ⟨t, fun i => ?_⟩
  have hmem : v i ∈ Ideal.span ((fun a => monomial a 1) '' (d '' ↑t)) := by
    rw [← himage]
    change v i ∈ Submodule.span (MvPolynomial σ K) ↑T
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨_, ⟨j, hj, rfl⟩, hle⟩ :=
    mem_ideal_span_monomial_image.mp hmem (d i) (by simp [v, support_monomial])
  exact ⟨j, hj, hle⟩

/-- Division supplies spanning, and the leading degree detects any nonzero
relation among the monomials in the remainder. -/
private theorem basis_of_standard_monomials {σ : Type} {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Nontrivial S]
    (m : MonomialOrder σ) (e : MvPolynomial σ R →ₐ[R] S) (he : Function.Surjective e)
    (g : ι → MvPolynomial σ R) (hg : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hzero : ∀ i, e (g i) = 0)
    (hdiv : ∀ p, p ≠ 0 → e p = 0 → ∃ i, m.degree (g i) ≤ m.degree p) :
    ∃ J : Type, Nonempty J ∧ Nonempty (Basis J R S) := by
  classical
  let J := {a : σ →₀ ℕ // ∀ i, ¬ m.degree (g i) ≤ a}
  let v : J → MvPolynomial σ R := fun a => monomial a.1 1
  let P := Submodule.span R (Set.range v)
  have hsupport (p : MvPolynomial σ R) (hp : p ∈ P) :
      ∀ a ∈ p.support, ∀ i, ¬ m.degree (g i) ≤ a := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a, rfl⟩ b hb
      have hab : b = a.1 := Finset.mem_singleton.mp (support_monomial_subset hb)
      exact hab ▸ a.2
    · simp
    · intro p q _ _ hp hq a ha
      rcases Finset.mem_union.mp (support_add ha) with h | h
      · exact hp _ h
      · exact hq _ h
    · intro c p _ hp a ha
      exact hp _ (support_smul ha)
  have hinj : Set.InjOn e.toLinearMap P := by
    intro p hp q hq hpq
    apply sub_eq_zero.mp
    by_contra hne
    have hz : e (p - q) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hpq
    obtain ⟨i, hi⟩ := hdiv (p - q) hne hz
    exact hsupport _ (P.sub_mem hp hq) _ (m.degree_mem_support hne) i hi
  have hli : LinearIndependent R (e ∘ v) :=
    (e.toLinearMap.linearIndependent_iff_of_injOn hinj).mpr
      (by simpa only [v, coe_basisMonomials, Function.comp_def] using
        ((basisMonomials σ R).linearIndependent.comp (Subtype.val : J → σ →₀ ℕ)
          Subtype.val_injective))
  have hspan : ⊤ ≤ Submodule.span R (Set.range (e ∘ v)) := by
    intro b _
    obtain ⟨p, rfl⟩ := he b
    obtain ⟨q, r, hqr, -, hr⟩ := m.div hg p
    have hz : e (Finsupp.linearCombination (MvPolynomial σ R) g q) = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      simp [smul_eq_mul, hzero]
    rw [hqr, map_add, hz, zero_add]
    have hr' : r = ∑ a ∈ r.support, r.coeff a • monomial a (1 : R) := by
      simpa only [smul_monomial, smul_eq_mul, mul_one] using (support_sum_monomial_coeff r).symm
    rw [hr', map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    change e.toLinearMap (r.coeff a • monomial a 1) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, hr a ha⟩, rfl⟩)
  let b := Basis.mk hli hspan
  exact ⟨J, b.index_nonempty, ⟨b⟩⟩

/-- A finite-type algebra containing its base domain has a principal localization
that is free with a nonempty basis. -/
theorem genericFreeness_of_injective {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) : Specs.hasFreeLocalization A B := by
  classical
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType A B)
  let m : MonomialOrder (Fin n) := MonomialOrder.lex
  let I := {p : MvPolynomial (Fin n) A // p ≠ 0 ∧ f p = 0}
  obtain ⟨t, ht⟩ := finite_degree_generators (FractionRing A) (fun p : I => m.degree p.1)
  -- Invert all the selected leading coefficients at once.
  let s := ∏ p ∈ t, m.leadingCoeff p.1
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => m.leadingCoeff_ne_zero_iff.mpr p.2.1)
  refine ⟨s, hs, ?_⟩
  let A' := Localization.Away s
  let B' := Localization.Away (algebraMap A B s)
  let : Algebra A' B' := localizationAlgebra (Submonoid.powers s) B
  let : IsScalarTower A A' B' := isScalarTower_localizationAlgebra (Submonoid.powers s) B
  let : IsDomain A' := Localization.Away.isDomain hs
  have hA : Function.Injective (algebraMap A A') :=
    IsLocalization.injective A' (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hinj' : Function.Injective (algebraMap A' B') :=
    localizationAlgebra_injective (M := Submonoid.powers s) A' B' hinj
  let : Nontrivial B' := hinj'.nontrivial
  let l : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) A' :=
    MvPolynomial.map (algebraMap A A')
  let e : MvPolynomial (Fin n) A' →ₐ[A'] B' :=
    aeval (fun i => algebraMap B B' (f (X i)))
  have hC (a : A) : f (C a) = algebraMap A B a := f.commutes a
  have hl (p : MvPolynomial (Fin n) A) : e (l p) = algebraMap B B' (f p) := by
    have h : e.toRingHom.comp l = (algebraMap B B').comp f.toRingHom := by
      ext a
      · simp [l, e, ← IsScalarTower.algebraMap_apply]
      · simp [l, e]
    exact DFunLike.congr_fun h p
  let : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A') :=
    MvPolynomial.algebraMvPolynomial
  let : IsLocalization.Away (C (σ := Fin n) s) (MvPolynomial (Fin n) A') := by
    show IsLocalization (Submonoid.powers (C (σ := Fin n) s)) _
    rw [← Submonoid.map_powers]
    exact MvPolynomial.isLocalization (Submonoid.powers s) A'
  have he : Function.Surjective e := by
    intro y
    obtain ⟨k, b, hb⟩ := IsLocalization.Away.surj (algebraMap A B s) y
    obtain ⟨p, rfl⟩ := hf b
    let hu : IsUnit (l (C s) ^ k) :=
      (IsLocalization.Away.algebraMap_isUnit (S := MvPolynomial (Fin n) A') (C s)).pow k
    refine ⟨l p * ↑hu.unit⁻¹, ?_⟩
    have hy : e (l p) = y * e (hu.unit : MvPolynomial (Fin n) A') := by
      rw [hu.unit_spec, map_pow, hl, hl, hC]
      exact hb.symm
    rw [map_mul, hy, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hd (p : MvPolynomial (Fin n) A) : m.degree (l p) = m.degree p := by
    simp only [l, MonomialOrder.degree, support_map_of_injective _ hA]
  -- A localized relation has the degree of an original relation after clearing
  -- its polynomial denominator and killing the resulting torsion in B.
  have hclear (r : MvPolynomial (Fin n) A') (hr : r ≠ 0) (hz : e r = 0) :
      ∃ p : I, m.degree p.1 = m.degree r := by
    obtain ⟨k, p, hp⟩ := IsLocalization.Away.surj (C (σ := Fin n) s) r
    change r * l (C s) ^ k = l p at hp
    have hz' : algebraMap B B' (f p) = algebraMap B B' 0 := by
      rw [← hl, ← hp, map_mul, hz, zero_mul, map_zero]
    obtain ⟨j, hj⟩ := IsLocalization.Away.exists_of_eq (algebraMap A B s) hz'
    have hp' : p ≠ 0 := by
      intro hp0
      apply hr
      have hu : IsUnit (l (C s) ^ k) :=
        (IsLocalization.Away.algebraMap_isUnit (S := MvPolynomial (Fin n) A') (C s)).pow k
      exact hu.mul_left_inj.mp (by simpa [hp0] using hp)
    have hpdeg : m.degree p = m.degree r := by
      rw [← hd, ← hp, show l (C s) = C (algebraMap A A' s) by simp [l],
        ← map_pow, mul_comm r, ← smul_eq_C_mul]
      exact m.degree_smul_of_isRegular ((IsLocalization.Away.algebraMap_isUnit
        (S := A') s).pow k).isRegular
    refine ⟨⟨s ^ j • p, ?_, ?_⟩, ?_⟩
    · rw [smul_eq_C_mul]
      exact mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ hs)) hp'
    · simpa only [smul_eq_C_mul, map_mul, hC, map_pow, mul_zero] using hj
    · rw [m.degree_smul_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero j hs)), hpdeg]
  refine basis_of_standard_monomials m e he (fun p : t => l p.1.1) ?_ ?_ ?_
  · intro p
    have hcoeff : m.leadingCoeff (l p.1.1) = algebraMap A A' (m.leadingCoeff p.1.1) := by
      simp [MonomialOrder.leadingCoeff, hd, l, coeff_map]
    rw [hcoeff]
    exact IsLocalization.Away.isUnit_of_dvd s (Finset.dvd_prod_of_mem _ p.2)
  · intro p
    simp [hl, p.1.2.2]
  · intro r hr hz
    obtain ⟨p, hp⟩ := hclear r hr hz
    obtain ⟨q, hq, hle⟩ := ht p
    exact ⟨⟨q, hq⟩, by simpa only [hd, ← hp] using hle⟩

/-- Over a domain, a finite-type algebra with nonzero generic fiber has a free
localization with a nonempty basis. -/
theorem genericFreeness (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (h : Nontrivial (FractionRing A ⊗[A] B)) :
    Specs.hasFreeLocalization A B := by
  have hK : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hT : Function.Injective (algebraMap (FractionRing A) (FractionRing A ⊗[A] B)) :=
    (algebraMap (FractionRing A) (FractionRing A ⊗[A] B)).injective
  apply genericFreeness_of_injective
  intro a b hab
  apply hK
  apply hT
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let ι : B →ₐ[A] FractionRing A ⊗[A] B := Algebra.TensorProduct.includeRight
  exact ((ι.commutes a).symm.trans (congrArg ι hab)).trans (ι.commutes b)

end LinearAlgebraicGroups
