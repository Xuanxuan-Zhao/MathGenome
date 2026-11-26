import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MaximalSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped WithZero
open ValuativeRel
open RM03.CSA (degree IsCentralSimple IsCentralDivision)

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation

noncomputable section

variable {F B L : Type*} [Field F] [DivisionRing B] [Field L] [Algebra F B] [Algebra F L]

private def Implements (i : L →ₐ[F] B) (u : Bˣ) (σ : Gal(L/F)) : Prop :=
  ∀ a : L, (u : B) * i a = i (σ a) * (u : B)

private theorem Implements.mul {i : L →ₐ[F] B} {u v : Bˣ} {σ τ : Gal(L/F)}
    (hu : Implements i u σ) (hv : Implements i v τ) : Implements i (u * v) (σ * τ) := by
  intro a
  change ((u : B) * (v : B)) * i a = i (σ (τ a)) * ((u : B) * (v : B))
  rw [mul_assoc, hv a, ← mul_assoc, hu (τ a), mul_assoc]

private theorem Implements.inv {i : L →ₐ[F] B} {u : Bˣ} {σ : Gal(L/F)}
    (hu : Implements i u σ) : Implements i u⁻¹ σ⁻¹ := by
  intro a
  have h := hu (σ.symm a)
  rw [σ.apply_symm_apply] at h
  change (↑u⁻¹ : B) * i a = i (σ.symm a) * (↑u⁻¹ : B)
  calc
    (↑u⁻¹ : B) * i a = (↑u⁻¹ : B) * (i a * (u : B)) * (↑u⁻¹ : B) := by
      rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = i (σ.symm a) * (↑u⁻¹ : B) := by rw [← h, ← mul_assoc, Units.inv_mul, one_mul]

private theorem Implements.pow {i : L →ₐ[F] B} {u : Bˣ} {σ : Gal(L/F)}
    (hu : Implements i u σ) (m : ℕ) : Implements i (u ^ m) (σ ^ m) := by
  induction m with
  | zero => simp [Implements]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hu

private theorem scalar_implements (i : L →ₐ[F] B) (c : Fˣ) :
    Implements i (Units.map (algebraMap F B) c) 1 := by
  intro a
  change algebraMap F B (c : F) * i a = i a * algebraMap F B (c : F)
  exact Algebra.commutes _ _

private theorem Implements.preserves_value {n : ℕ} (hn : n ≠ 0)
    {i : L →ₐ[F] B} {vB : Valuation B ℤᵐ⁰} {vL : Valuation L ℤᵐ⁰}
    (hval : ∀ a : L, vB (i a) = vL a ^ n)
    {u : Bˣ} {σ : Gal(L/F)} (hu : Implements i u σ) (a : L) :
    vL (σ a) = vL a := by
  have h := congrArg vB (hu a)
  rw [map_mul, map_mul, mul_comm (vB (i (σ a))), hval, hval] at h
  exact (pow_left_inj₀ zero_le zero_le hn).mp
    (mul_left_cancel₀ ((map_ne_zero vB).mpr u.ne_zero) h).symm

private theorem unit_reduction_trivial {n : ℕ} (hn : n ≠ 0)
    {i : L →ₐ[F] B} {vB : Valuation B ℤᵐ⁰} {vL : Valuation L ℤᵐ⁰}
    (hval : ∀ a : L, vB (i a) = vL a ^ n)
    {k ell : Type*} [Field k] [Field ell] [Algebra k ell]
    (red : vB.integer →+* ell) (hker : ∀ x : vB.integer, red x = 0 ↔ vB (x : B) < 1)
    (res : IsLocalRing.ResidueField vL.valuationSubring ≃+* ell)
    (hres : ∀ (a : vL.valuationSubring) (x : vB.integer), (x : B) = i (a : L) →
      res (IsLocalRing.residue _ a) = red x)
    (reduce : Gal(L/F) ≃* Gal(ell/k))
    (hreduce : ∀ (σ : Gal(L/F)) (a b : vL.valuationSubring), (b : L) = σ (a : L) →
        res (IsLocalRing.residue _ b) = reduce σ (res (IsLocalRing.residue _ a)))
    {u : Bˣ} {σ : Gal(L/F)} (hu : Implements i u σ) (huval : vB (u : B) = 1) :
    σ = 1 := by
  apply reduce.injective
  rw [map_one]
  ext y
  obtain ⟨a, ha⟩ := (res.surjective.comp (IsLocalRing.residue_surjective (R := vL.valuationSubring))) y
  change res (IsLocalRing.residue _ a) = y at ha
  have aval : vL (a : L) ≤ 1 := a.property
  let b : vL.valuationSubring := ⟨σ (a : L), by
    change vL (σ (a : L)) ≤ 1
    rwa [hu.preserves_value hn hval]⟩
  have bval : vL (b : L) ≤ 1 := b.property
  let A : vB.integer := ⟨i (a : L), by
    change vB (i (a : L)) ≤ 1
    rw [hval]
    exact pow_le_one₀ zero_le aval⟩
  let C : vB.integer := ⟨i (b : L), by
    change vB (i (b : L)) ≤ 1
    rw [hval]
    exact pow_le_one₀ zero_le bval⟩
  let U : vB.integer := ⟨(u : B), huval.le⟩
  have hU : red U ≠ 0 := by
    intro h
    exact (lt_irrefl (1 : ℤᵐ⁰)) (huval ▸ (hker U).mp h)
  have hprod : U * A = C * U := Subtype.ext (hu (a : L))
  have he := congrArg red hprod
  rw [map_mul, map_mul, mul_comm (red U)] at he
  change reduce σ y = y
  rw [← ha, ← hreduce σ a b rfl, hres b C rfl, hres a A rfl]
  exact (mul_right_cancel₀ hU he).symm

section Exponents

variable (vB : Valuation B ℤᵐ⁰)

/-- The integer exponent of a nonzero multiplicative value. -/
private def exponent (u : Bˣ) : ℤ := WithZero.log (vB (u : B))

private theorem exp_exponent (u : Bˣ) : WithZero.exp (exponent vB u) = vB (u : B) :=
  WithZero.exp_log ((map_ne_zero vB).mpr u.ne_zero)

private theorem exponent_mul (u v : Bˣ) :
    exponent vB (u * v) = exponent vB u + exponent vB v := by
  simp only [exponent, Units.val_mul, map_mul]
  exact WithZero.log_mul ((map_ne_zero vB).mpr u.ne_zero) ((map_ne_zero vB).mpr v.ne_zero)

end Exponents

section ValuationClasses

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem scale_exponent {n : ℕ} (vB : Valuation B ℤᵐ⁰)
    (hscalar : ∀ a : F, vB (algebraMap F B a) = normalizedValue F a ^ n)
    (u : Bˣ) (m : ℤ) :
    ∃ c : Fˣ, exponent vB (Units.map (algebraMap F B) c * u) = (n : ℤ) * m + exponent vB u := by
  have hs : Function.Surjective (normalizedValue F) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (ValuativeRel.valuation_surjective (K := F))
  obtain ⟨a, ha⟩ := hs (WithZero.exp m)
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    exact WithZero.exp_ne_zero (a := m) (by simpa only [normalizedValue, map_zero] using ha.symm)
  refine ⟨Units.mk0 a ha0, ?_⟩
  rw [exponent_mul]
  change WithZero.log (vB (algebraMap F B a)) + _ = _
  rw [hscalar, ha, WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul]

private theorem exists_normalizing_uniformizer {n : ℕ} (hn : 0 < n)
    [FiniteDimensional F L] [IsGalois F L] (hdeg : Module.finrank F L = n)
    (hB : IsCentralSimple F B) (i : L →ₐ[F] B) (vB : Valuation B ℤᵐ⁰)
    (hscalar : ∀ a : F, vB (algebraMap F B a) = normalizedValue F a ^ n)
    (htriv : ∀ {u σ}, Implements i u σ → vB (u : B) = 1 → σ = 1) :
    ∃ (u : Bˣ) (σ : Gal(L/F)), vB (u : B) = WithZero.exp (-1) ∧ Implements i u σ := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  have hrep (σ : Gal(L/F)) : ∃ u, Implements i u σ := by
    obtain ⟨u, hu⟩ := RM03.CSA.skolem_noether hB inferInstance
      (i.comp σ.toAlgHom) i (i.comp σ.toAlgHom).injective i.injective
    exact ⟨u, fun a => (hu a).symm⟩
  choose rep hrep using hrep
  let residueClass (σ : Gal(L/F)) : ZMod n := (exponent vB (rep σ) : ZMod n)
  -- A central rescaling makes representatives in the same class have equal values.
  -- Their quotient then has trivial conjugation on the residue field.
  have hinj : Function.Injective residueClass := by
    intro σ τ h
    obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp h
    obtain ⟨c, hc⟩ := scale_exponent vB hscalar (rep σ) m
    let u := Units.map (algebraMap F B) c * rep σ
    have hu : Implements i u σ := by
      simpa only [one_mul] using (scalar_implements i c).mul (hrep σ)
    have he : exponent vB u = exponent vB (rep τ) := by
      rw [hc]
      omega
    have hv : vB (u : B) = vB (rep τ : B) := by
      simpa only [exp_exponent] using congrArg WithZero.exp he
    have hone := htriv (hu.mul (hrep τ).inv) (by
      rw [Units.val_mul, map_mul, hv, Units.val_inv_eq_inv_val, vB.map_inv]
      exact mul_inv_cancel₀ ((map_ne_zero vB).mpr (rep τ).ne_zero))
    exact mul_inv_eq_one.mp hone
  have hsurj : Function.Surjective residueClass :=
    (hinj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card (α := ZMod n), ZMod.card, IsGalois.card_aut_eq_finrank, hdeg])).2
  obtain ⟨σ, hσ⟩ := hsurj ((-1 : ℤ) : ZMod n)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp hσ
  obtain ⟨c, hc⟩ := scale_exponent vB hscalar (rep σ) m
  let u := Units.map (algebraMap F B) c * rep σ
  have he : exponent vB u = -1 := by
    rw [hc]
    omega
  refine ⟨u, σ, ?_, ?_⟩
  · simpa only [exp_exponent] using congrArg WithZero.exp he
  · simpa only [one_mul] using (scalar_implements i c).mul (hrep σ)

end ValuationClasses

private theorem centralizer_eq_range (hB : IsCentralDivision F B) (i : L →ₐ[F] B)
    (hdeg : Module.finrank F L = degree F B) :
    Subalgebra.centralizer F (Set.range i) = i.range := by
  let e : L ≃ₐ[F] i.range := AlgEquiv.ofInjective i i.injective
  have hfield : IsField i.range := e.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField L)
  have hdim : Module.finrank F i.range = degree F B := e.toLinearEquiv.finrank_eq.symm.trans hdeg
  exact (RM03.CSA.maximal_subfield_iff_centralizer_eq hB i.range hfield).mp
    ((RM03.CSA.maximal_subfield_iff_degree hB i.range hfield).mpr hdim)

private theorem Implements.power_mem_range {i : L →ₐ[F] B}
    (hcent : Subalgebra.centralizer F (Set.range i) = i.range)
    {u : Bˣ} {σ : Gal(L/F)} (hu : Implements i u σ) {m : ℕ} (hm : σ ^ m = 1) :
    ∃ a : L, i a = (u : B) ^ m := by
  have h := hu.pow m
  rw [hm] at h
  suffices (u : B) ^ m ∈ Subalgebra.centralizer F (Set.range i) by
    rwa [hcent] at this
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact ((Units.val_pow_eq_pow_val u m) ▸ (h a)).symm

private theorem uniformizer_generates {n : ℕ}
    [FiniteDimensional F L] [IsGalois F L] (hdeg : Module.finrank F L = n)
    {i : L →ₐ[F] B} (hcent : Subalgebra.centralizer F (Set.range i) = i.range)
    {vB : Valuation B ℤᵐ⁰} {vL : Valuation L ℤᵐ⁰}
    (hval : ∀ a : L, vB (i a) = vL a ^ n)
    {u : Bˣ} {σ : Gal(L/F)} (hu : Implements i u σ) (huval : vB (u : B) = WithZero.exp (-1)) :
    orderOf σ = n ∧ Subgroup.zpowers σ = ⊤ := by
  have hcard : Nat.card Gal(L/F) = n := (IsGalois.card_aut_eq_finrank F L).trans hdeg
  have hdvd : orderOf σ ∣ n := hcard ▸ orderOf_dvd_natCard σ
  obtain ⟨a, ha⟩ := hu.power_mem_range hcent (pow_orderOf_eq_one σ)
  have heq := congrArg (fun x : B => WithZero.log (vB x)) ha
  change WithZero.log (vB (i a)) = WithZero.log (vB ((u : B) ^ orderOf σ)) at heq
  rw [hval, map_pow, huval, WithZero.log_pow, WithZero.log_pow, WithZero.log_exp,
    nsmul_eq_mul, nsmul_eq_mul, mul_neg_one] at heq
  have hn' : (n : ℤ) ∣ (orderOf σ : ℤ) := ⟨-WithZero.log (vL a), by
    rw [mul_neg, heq, neg_neg]⟩
  have ho : orderOf σ = n := Nat.dvd_antisymm hdvd (Int.natCast_dvd_natCast.mp hn')
  exact ⟨ho, (Subgroup.zpowers σ).eq_top_of_card_eq (by rw [Nat.card_zpowers, ho, hcard])⟩

private theorem central_power {n : ℕ} (hn : n ≠ 0)
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F L] [IsGalois F L]
    {i : L →ₐ[F] B} (hcent : Subalgebra.centralizer F (Set.range i) = i.range)
    {vB : Valuation B ℤᵐ⁰}
    (hscalar : ∀ a : F, vB (algebraMap F B a) = normalizedValue F a ^ n)
    {u : Bˣ} {σ : Gal(L/F)} (hu : Implements i u σ) (huval : vB (u : B) = WithZero.exp (-1))
    (ho : orderOf σ = n) (hgen : Subgroup.zpowers σ = ⊤) :
    ∃ t : F, normalizedValue F t = WithZero.exp (-1) ∧ (u : B) ^ n = algebraMap F B t := by
  obtain ⟨a, ha⟩ := hu.power_mem_range hcent (ho ▸ pow_orderOf_eq_one σ)
  have hfixed : σ a = a := by
    apply i.injective
    apply mul_right_cancel₀ u.ne_zero
    change i (σ a) * (u : B) = i a * (u : B)
    rw [← hu a, ha, ← pow_succ, ← pow_succ']
  have hfixed_pow (m : ℕ) : (σ ^ m) a = a := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ']; exact (congrArg σ ih).trans hfixed
  have hfixed_all (τ : Gal(L/F)) : τ a = a := by
    have hm : τ ∈ Subgroup.zpowers σ := by rw [hgen]; trivial
    obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite σ).mem_powers_iff_mem_zpowers.mpr hm
    exact (congrArg (fun f : Gal(L/F) => f a) hm).symm.trans (hfixed_pow m)
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed a).mpr hfixed_all
  have hpow : (u : B) ^ n = algebraMap F B t := by
    rw [← ha, ← ht, i.commutes]
  refine ⟨t, (pow_left_inj₀ zero_le zero_le hn).mp ?_, hpow⟩
  rw [← hscalar, ← hpow, map_pow, huval]

private theorem generating_residue_frobenius {k ell : Type*} [Field k] [Field ell] [Finite ell]
    [Algebra k ell] {n : ℕ} {σ : Gal(L/F)} (horder : orderOf σ = n)
    (hgen : Subgroup.zpowers σ = ⊤) (reduce : Gal(L/F) ≃* Gal(ell/k)) :
    ∃ m : ℕ, Nat.Coprime m n ∧ ∀ y : ell, reduce σ y = y ^ (Nat.card k ^ m) := by
  classical
  let : Finite k := Finite.of_injective _ (algebraMap k ell).injective
  let : Fintype k := Fintype.ofFinite k
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k ell
  have hφcard : orderOf φ = Nat.card Gal(ell/k) := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Nat.card_fin _).symm.trans
      (Nat.card_congr (Equiv.ofBijective _ (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k ell)))
  have hφorder : orderOf φ = n :=
    hφcard.trans ((Nat.card_congr reduce.toEquiv).symm.trans
      ((orderOf_eq_card_of_zpowers_eq_top hgen).symm.trans horder))
  obtain ⟨m, hm⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k ell).surjective (reduce σ)
  change φ ^ (m : ℕ) = reduce σ at hm
  have hmem : φ ∈ Subgroup.zpowers (φ ^ (m : ℕ)) := by
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp
      (hgen.ge (Subgroup.mem_top (reduce.symm φ)))
    exact Subgroup.mem_zpowers_iff.mpr ⟨r, by rw [hm, ← map_zpow, hr, reduce.apply_symm_apply]⟩
  refine ⟨m, by simpa [hφorder, Nat.coprime_iff_gcd_eq_one] using mem_zpowers_pow_iff.mp hmem, ?_⟩
  intro y
  rw [← hm]
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    Nat.card_eq_fintype_card]

section OrderedBasis

variable {n : ℕ} {i : L →ₐ[F] B}
    {vB : Valuation B ℤᵐ⁰} {vL : Valuation L ℤᵐ⁰}

private theorem term_exponent {u : Bˣ} (hu : vB (u : B) = WithZero.exp (-1))
    (hval : ∀ a : L, vB (i a) = vL a ^ n) (j : Fin n) {a : L} (ha : a ≠ 0) :
    WithZero.log (vB ((u : B) ^ j.val * i a)) = -(j.val : ℤ) + (n : ℤ) * WithZero.log (vL a) := by
  rw [map_mul, map_pow, hu, hval, WithZero.log_mul (pow_ne_zero _ WithZero.exp_ne_zero)
    (pow_ne_zero _ ((map_ne_zero vL).mpr ha)), WithZero.log_pow, WithZero.log_pow, WithZero.log_exp,
    nsmul_eq_mul, nsmul_eq_mul, mul_neg_one]

private theorem term_val_le_one_iff {u : Bˣ} (hu : vB (u : B) = WithZero.exp (-1))
    (hval : ∀ a : L, vB (i a) = vL a ^ n) (j : Fin n) (a : L) :
    vB ((u : B) ^ j.val * i a) ≤ 1 ↔ vL a ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hterm : (u : B) ^ j.val * i a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ u.ne_zero) ((map_ne_zero i).mpr ha)
  rw [← WithZero.exp_log ((map_ne_zero vB).mpr hterm), ← WithZero.exp_log ((map_ne_zero vL).mpr ha),
    WithZero.exp_le_one_iff, WithZero.exp_le_one_iff, term_exponent hu hval j ha]
  constructor
  · intro h
    by_contra! hpos
    have hge := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ WithZero.log (vL a) by omega)
      (show 0 ≤ (n : ℤ) by exact_mod_cast Nat.zero_le n)
    rw [mul_one] at hge
    have hj := j.isLt
    omega
  · intro h
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (n : ℤ) by exact_mod_cast Nat.zero_le n) h
    omega

private theorem term_le_sum {u : Bˣ} (hu : vB (u : B) = WithZero.exp (-1))
    (hval : ∀ a : L, vB (i a) = vL a ^ n) (a : Fin n → L) (j : Fin n) :
    vB ((u : B) ^ j.val * i (a j)) ≤ vB (∑ k : Fin n, (u : B) ^ k.val * i (a k)) := by
  classical
  let f (k : Fin n) := (u : B) ^ k.val * i (a k)
  change vB (f j) ≤ vB (∑ k, f k)
  by_cases hj : vB (f j) = 0
  · simp [hj]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => vB (f k))
    ⟨j, Finset.mem_univ j⟩
  have hkj := hmax j (Finset.mem_univ j)
  have hk0 : vB (f k) ≠ 0 := (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hj) hkj).ne'
  have hc (l : Fin n) (hl : vB (f l) ≠ 0) : a l ≠ 0 := by
    intro h
    exact hl (by simp [f, h])
  -- Equal nonzero term values would give equal indices modulo the degree.
  have hstrict : ∀ l ∈ Finset.univ \ {k}, vB (f l) < vB (f k) := by
    intro l hl
    have hlk : l ≠ k := by simpa using hl
    refine lt_of_le_of_ne (hmax l (Finset.mem_univ l)) fun he => hlk ?_
    have he' := congrArg WithZero.log he
    change WithZero.log (vB ((u : B) ^ l.val * i (a l))) =
      WithZero.log (vB ((u : B) ^ k.val * i (a k))) at he'
    rw [term_exponent hu hval l (hc l (he ▸ hk0)), term_exponent hu hval k (hc k hk0)] at he'
    have hmod : (-(l.val : ℤ)) ≡ -(k.val : ℤ) [ZMOD (n : ℤ)] := by
      simpa only [Int.ModEq, Int.add_mul_emod_self_left] using
        congrArg (fun m : ℤ => m % (n : ℤ)) he'
    have hnat : l.val ≡ k.val [MOD n] :=
      Int.natCast_modEq_iff.mp (by simpa only [neg_neg] using hmod.neg)
    exact Fin.ext (by simpa only [Nat.ModEq, Nat.mod_eq_of_lt l.isLt, Nat.mod_eq_of_lt k.isLt]
      using hnat)
  rw [vB.map_sum_eq_of_lt hk hstrict]
  exact hkj

private theorem ordered_basis (hB : IsCentralDivision F B)
    (hdeg : Module.finrank F L = degree F B) {u : Bˣ} (hu : vB (u : B) = WithZero.exp (-1))
    (hval : ∀ a : L, vB (i a) = vL a ^ degree F B) :
    letI := _root_.Specs.RM03.CSA.rightSubfieldModule i
    ∃ b : Module.Basis (Fin (degree F B)) L B,
      (∀ j, b j = (u : B) ^ j.val) ∧
      (∀ x : B, x ∈ vB.integer ↔ ∀ j, b.equivFun x j ∈ vL.valuationSubring) := by
  let := _root_.Specs.RM03.CSA.rightSubfieldModule i
  obtain ⟨hfinite, hdim⟩ := RM03.CSA.rightSubfield_dimension i hB hdeg
  let f (j : Fin (degree F B)) := (u : B) ^ j.val
  have hind : LinearIndependent L f := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha j
    change ∑ k, (u : B) ^ k.val * i (a k) = 0 at ha
    have h := term_le_sum hu hval a j
    rw [ha, map_zero, le_zero_iff, map_eq_zero, mul_eq_zero] at h
    exact (map_eq_zero i).mp (h.resolve_left (pow_ne_zero _ u.ne_zero))
  let b := basisOfLinearIndependentOfCardEqFinrank' f hind (by rw [Fintype.card_fin, hdim])
  have hb (j : Fin (degree F B)) : b j = (u : B) ^ j.val :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' f hind _) j
  refine ⟨b, hb, fun x => ?_⟩
  let a (j : Fin (degree F B)) := b.equivFun x j
  have hx : ∑ j, (u : B) ^ j.val * i (a j) = x := by
    have h := b.sum_repr x
    change ∑ j, b j * i (a j) = x at h
    simpa only [hb] using h
  change vB x ≤ 1 ↔ ∀ j, vL (a j) ≤ 1
  rw [← hx] at ⊢
  constructor
  · intro h j
    exact (term_val_le_one_iff hu hval j (a j)).mp ((term_le_sum hu hval a j).trans h)
  · intro h
    exact vB.map_sum_le fun j _ => (term_val_le_one_iff hu hval j (a j)).mpr (h j)

end OrderedBasis

/-- A normalizing uniformizer yields the integral ordered cyclic presentation. -/
theorem cyclicPresentation : CyclicPresentation := by
  intro F _ _ _ _ B _ _ hB n vB hscalar _ L _ _ _ i hdeg vL _ hval
    ell _ _ _ red _ hker _ res hres reduce hreduce
  have hn : 0 < n := RM03.CSA.degree_pos hB
  let : FiniteDimensional F L := FiniteDimensional.of_finrank_pos (hdeg.symm ▸ hn)
  have hD : IsCentralDivision F B := hB.2
  have hcent := centralizer_eq_range hD i hdeg
  obtain ⟨pi, τ, hpi, hτ⟩ := exists_normalizing_uniformizer hn hdeg hB i vB hscalar
    (fun h => unit_reduction_trivial hn.ne' hval red hker res hres reduce hreduce h)
  obtain ⟨ho, hg⟩ := uniformizer_generates hdeg hcent hval hτ hpi
  obtain ⟨t, ht, hpow⟩ := central_power hn.ne' hcent hscalar hτ hpi ho hg
  obtain ⟨b, hb, hint⟩ := ordered_basis hD hdeg hpi hval
  exact ⟨hcent, pi, τ, t, b, hpi, hτ, hτ.preserves_value hn.ne' hval, hg,
    generating_residue_frobenius ho hg reduce, ht, hpow, hb, hint⟩

end

end LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation
