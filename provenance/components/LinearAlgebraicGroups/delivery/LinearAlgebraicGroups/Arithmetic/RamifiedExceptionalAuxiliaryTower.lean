import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower

open Specs.RamifiedExceptionalAuxiliaryTower
open Specs.ExceptionalAffineBruhat (DiagramCompositum IsUnramifiedLocalExtension)
open Specs.ExceptionalLocalRootCoordinates
  (normalizedValuation normalizedValueGroupMap residueMap ramificationIndex)
open ValuativeRel WithZero IsLocalRing Polynomial
open scoped WithZero ValuativeRel TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 1200000

attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension

open private valuativeEmbedding diagramCompositum_ramification
  from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

section Valuations

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]


theorem normalizedValuation_surjective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (normalizedValuation K) := by
  change Function.Surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) ∘ valuation K)
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    (valuation_surjective (K := K))

theorem normalizedValuation_le_one {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (a : K) :
    normalizedValuation K a ≤ 1 ↔ valuation K a ≤ 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K a) ≤ 1 ↔ _
  have ho : e 1 = 1 := e.map_one
  rw [← ho, e.strictMono.le_iff_le]

theorem normalizedValuation_lt_one {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (a : K) :
    normalizedValuation K a < 1 ↔ valuation K a < 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K a) < 1 ↔ _
  have ho : e 1 = 1 := e.map_one
  rw [← ho, e.strictMono.lt_iff_lt]

theorem normalizedValueGroupMap_apply (a : K) :
    normalizedValueGroupMap K E (normalizedValuation K a) =
      normalizedValuation E (algebraMap K E a) := by
  unfold normalizedValueGroupMap normalizedValuation
  simp [MonoidWithZeroHom.comp_apply, Valuation.map_apply]

theorem normalizedValuation_of_uniformizerRoot
    (π : K) (hπ : normalizedValuation K π = exp (-1)) (ξ : E) (d : ℕ)
    (hξ : ξ ^ d = algebraMap K E π) (a : K) (ha : a ≠ 0) :
    normalizedValuation E (algebraMap K E a) =
      (normalizedValuation E ξ) ^ ((d : ℤ) * (-log (normalizedValuation K a))) := by
  let b := -log (normalizedValuation K a)
  have hb : normalizedValuation K a = exp (-1 : ℤ) ^ b := by
    rw [← exp_zsmul]
    simpa [b] using (exp_log ((map_ne_zero (normalizedValuation K)).2 ha)).symm
  change _ = _ ^ ((d : ℤ) * b)
  rw [← normalizedValueGroupMap_apply, hb, map_zpow₀, ← hπ, normalizedValueGroupMap_apply,
    ← hξ, map_pow, ← zpow_natCast, ← zpow_mul]

private theorem equal_indices_of_weighted_values {d : ℕ} (i j : Fin d) (m n : ℤ)
    (h : (d : ℤ) * m + i.val = (d : ℤ) * n + j.val) : i = j := by
  apply Fin.ext
  have hi : ((i.val : ℕ) : ℤ) % (d : ℤ) = i.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast i.isLt)
  have hj : ((j.val : ℕ) : ℤ) % (d : ℤ) = j.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)
  have he : ((i.val : ℕ) : ℤ) % (d : ℤ) = ((j.val : ℕ) : ℤ) % (d : ℤ) := by
    simpa only [Int.mul_add_emod_self_left, add_comm ((d : ℤ) * m),
      add_comm ((d : ℤ) * n), Int.add_mul_emod_self_left] using
        congrArg (fun a : ℤ => a % (d : ℤ)) h
  exact_mod_cast (hi.symm.trans (he.trans hj))


private theorem uniformizerRoot_valuation_lt_one (π : K)
    (hπ : normalizedValuation K π = exp (-1)) (ξ : E) (d : ℕ)
    (hξ : ξ ^ d = algebraMap K E π) : normalizedValuation E ξ < 1 := by
  have hK : valuation K π < 1 :=
    (normalizedValuation_lt_one π).1 (by rw [hπ]; simp)
  have hE : valuation E (algebraMap K E π) < 1 := by
    rw [← map_one (valuation E), ← map_one (algebraMap K E), ← (valuation E).vlt_iff_lt,
      ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt, map_one]
    exact hK
  have hpow : normalizedValuation E ξ ^ d < 1 := by
    rw [← map_pow, hξ]
    exact (normalizedValuation_lt_one _).2 hE
  by_contra! hn
  exact hpow.not_ge (one_le_pow₀ hn)

theorem uniformizerRootBasis_integral
    (B : PowerBasis K E) (π : K) (hπ : normalizedValuation K π = exp (-1))
    (hξ : B.gen ^ B.dim = algebraMap K E π) (x : E) :
    normalizedValuation E x ≤ 1 ↔ ∀ i, normalizedValuation K (B.basis.repr x i) ≤ 1 := by
  classical
  let v := normalizedValuation E
  let a := B.basis.repr x
  let z := fun i : Fin B.dim => algebraMap K E (a i) * B.gen ^ (i : ℕ)
  let c := log (v B.gen)
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact (exp_ne_zero hπ.symm)
  have hξ0 : B.gen ≠ 0 := by
    intro h
    apply (algebraMap K E).injective.ne hπ0
    rw [← hξ, h, zero_pow (PowerBasis.dim_ne_zero B), map_zero]
  have hc : c < 0 := by
    rw [← exp_lt_one_iff, exp_log ((map_ne_zero v).2 hξ0)]
    exact uniformizerRoot_valuation_lt_one π hπ B.gen B.dim hξ
  have hval (i : Fin B.dim) (hi : a i ≠ 0) :
      v (z i) = exp (c * ((B.dim : ℤ) * (-log (normalizedValuation K (a i))) + i.val)) := by
    dsimp [z]
    rw [map_mul, map_pow, normalizedValuation_of_uniformizerRoot π hπ B.gen B.dim hξ _ hi]
    change v B.gen ^ _ * v B.gen ^ _ = _
    rw [← zpow_natCast, ← zpow_add₀ ((map_ne_zero v).2 hξ0)]
    have hvc : v B.gen = exp c := (exp_log ((map_ne_zero v).2 hξ0)).symm
    rw [hvc, ← exp_zsmul]
    congr 1
    ring
  have hsum : ∑ i, z i = x := by
    simpa only [z, a, ← Algebra.smul_def, ← B.basis_eq_pow] using B.basis.sum_repr x
  have hdistinct (i j : Fin B.dim) (hi : a i ≠ 0) (hj : a j ≠ 0)
      (he : v (z i) = v (z j)) : i = j := by
    rw [hval i hi, hval j hj, exp_inj] at he
    exact equal_indices_of_weighted_values i j _ _
      (mul_left_cancel₀ (ne_of_lt hc) he)
  have hcomponent (hx : v x ≤ 1) (i : Fin B.dim) : v (z i) ≤ 1 := by
    have : Nonempty (Fin B.dim) := ⟨i⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => v (z j)) Finset.univ_nonempty
    apply (hj i (Finset.mem_univ i)).trans
    by_cases hj₀ : a j = 0
    · simp [z, hj₀]
    have hsumval : v x = v (z j) := by
      rw [← hsum]
      apply v.map_sum_eq_of_lt (Finset.mem_univ j)
      intro k hk
      have hne : k ≠ j := by simpa using hk
      by_cases hk₀ : a k = 0
      · rw [show z k = 0 by simp [z, hk₀], map_zero]
        rw [hval j hj₀]
        simp
      · exact lt_of_le_of_ne (hj k (Finset.mem_univ k))
          (fun he => hne (hdistinct k j hk₀ hj₀ he))
    rwa [← hsumval]
  constructor
  · intro hx i
    by_cases hi : a i = 0
    · simp [a] at hi
      simp [hi]
    have hv := hcomponent hx i
    change normalizedValuation K (a i) ≤ 1
    rw [hval i hi, exp_le_one_iff] at hv
    let m := -log (normalizedValuation K (a i))
    have hmn : 0 ≤ (B.dim : ℤ) * m + i.val := by
      by_contra! hn
      exact (not_lt_of_ge hv) (mul_pos_of_neg_of_neg hc hn)
    by_contra! hneg
    have hm : m ≤ -1 := by
      have he := exp_log ((map_ne_zero (normalizedValuation K)).2 hi)
      have hlog : 0 < log (normalizedValuation K (a i)) := by
        rw [← one_lt_exp_iff, he]
        exact hneg
      omega
    have hmul := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg B.dim)
    have hilt : (i.val : ℤ) < (B.dim : ℤ) := by exact_mod_cast i.isLt
    linarith
  · intro hx
    rw [← hsum]
    apply v.map_sum_le
    intro i _
    by_cases hi : a i = 0
    · simp [z, hi]
    have hm : 0 ≤ -log (normalizedValuation K (a i)) := by
      have hlog : log (normalizedValuation K (a i)) ≤ 0 := by
        rw [← exp_le_one_iff, exp_log ((map_ne_zero (normalizedValuation K)).2 hi)]
        exact hx i
      omega
    rw [hval i hi, exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hc.le
      (add_nonneg (mul_nonneg (Int.natCast_nonneg _) hm) (Int.natCast_nonneg _))


/-- In the uniformizer power basis the residue of an integral element is
the residue of its constant coefficient. In particular the residue field
does not grow, including for inseparable uniformizer-root extensions. -/
theorem uniformizerRootBasis_residue_surjective
    (B : PowerBasis K E) (π : K) (hπ : normalizedValuation K π = exp (-1))
    (hξ : B.gen ^ B.dim = algebraMap K E π) :
    Function.Surjective (residueMap K E) := by
  classical
  let v := normalizedValuation E
  let O := (valuation K).valuationSubring
  let O' := (valuation E).valuationSubring
  let red : O' →+* IsLocalRing.ResidueField O' := IsLocalRing.residue O'
  intro y
  obtain ⟨x, rfl⟩ : ∃ x : O', red x = y := Ideal.Quotient.mk_surjective y
  let f : O →+* O' := algebraMap O O'
  let a := B.basis.repr (x : E)
  let : NeZero B.dim := ⟨PowerBasis.dim_ne_zero B⟩
  let j : Fin B.dim := 0
  have ht : ∀ i, normalizedValuation K (a i) ≤ 1 := by
    apply (uniformizerRootBasis_integral B π hπ hξ _).1
    exact (normalizedValuation_le_one _).2 x.property
  let u : O := ⟨a j, (normalizedValuation_le_one _).1 (ht j)⟩
  refine ⟨IsLocalRing.residue O u, ?_⟩
  change (IsLocalRing.ResidueField.map f) (IsLocalRing.residue O u) = red x
  rw [IsLocalRing.ResidueField.map_residue]
  apply Ideal.Quotient.eq.mpr
  rw [(valuation E).mem_maximalIdeal_iff, ← normalizedValuation_lt_one]
  change v (algebraMap K E (a j) - (x : E)) < 1
  have hξlt : v B.gen < 1 := uniformizerRoot_valuation_lt_one π hπ B.gen B.dim hξ
  let z := fun i : Fin B.dim => algebraMap K E (a i) * B.gen ^ (i : ℕ)
  have hsum : ∑ i, z i = (x : E) := by
    simpa only [z, a, ← Algebra.smul_def, ← B.basis_eq_pow] using B.basis.sum_repr (x : E)
  have hzero : z j = algebraMap K E (a j) := by simp [z, j]
  rw [← Valuation.map_neg, neg_sub, ← hsum, ← hzero,
    Finset.sum_erase_add _ _ (Finset.mem_univ j) |>.symm]
  rw [add_sub_cancel_right]
  apply Valuation.map_sum_lt' _ zero_lt_one
  intro i hi
  have hne : i ≠ j := (Finset.mem_erase.mp hi).1
  have hi0 : 0 < i.val := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hne (Fin.ext h)
  have ha : v (algebraMap K E (a i)) ≤ 1 := by
    apply (normalizedValuation_le_one _).2
    rw [← map_one (valuation E), ← map_one (algebraMap K E), ← (valuation E).vle_iff_le,
      ValuativeExtension.vle_iff_vle, (valuation K).vle_iff_le, map_one]
    exact (normalizedValuation_le_one _).1 (ht i)
  have hpow : v (B.gen ^ (i : ℕ)) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hξlt hi0.ne'
  show v (z i) < 1
  dsimp [z]
  rw [map_mul]
  exact (mul_le_mul_of_nonneg_right ha zero_le).trans_lt (by simpa using hpow)

end Valuations


section UniformizerExtension

open Polynomial IsLocalRing

private theorem normalizedUniformizer_generates {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (π : (valuation K).valuationSubring)
    (hπ : normalizedValuation K (π : K) = exp (-1)) :
    maximalIdeal (valuation K).valuationSubring = Ideal.span {π} := by
  let O := (valuation K).valuationSubring
  let v := normalizedValuation K
  have hπ₀ : (π : K) ≠ 0 := (map_ne_zero v).1 (by simp [v, hπ])
  have hπm : π ∈ maximalIdeal O := by
    rw [(valuation K).mem_maximalIdeal_iff, ← normalizedValuation_lt_one, hπ]
    simp
  apply le_antisymm _ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπm))
  intro x hx
  have hlt : v (x : K) < 1 := (normalizedValuation_lt_one _).2
    ((valuation K).mem_maximalIdeal_iff.mp hx)
  have hle : v (x : K) ≤ exp (-1) := by
    by_cases h : v (x : K) = 0
    · simp [h]
    rw [← exp_log h] at hlt ⊢
    simp only [exp_lt_one_iff] at hlt
    exact exp_le_exp.mpr (by omega)
  let b : O := ⟨(x : K) / (π : K), (normalizedValuation_le_one _).1 (by
    change v ((x : K) / (π : K)) ≤ 1
    rw [map_div₀, div_le_iff₀, one_mul]
    · exact hπ.symm ▸ hle
    · simp [v, hπ])⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨b, Subtype.ext ?_⟩
  change (x : K) = (π : K) * ((x : K) / (π : K))
  field_simp

theorem uniformizerPolynomialIrreducible {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (π : (valuation K).valuationSubring)
    (hπ : normalizedValuation K (π : K) = exp (-1)) :
    Irreducible (X ^ d - C (π : K)) := by
  let R := (valuation K).valuationSubring
  let f : R[X] := X ^ d - C π
  have hmon : f.Monic := monic_X_pow_sub_C _ hd.ne'
  have hdeg : f.natDegree = d := natDegree_X_pow_sub_C
  have hgen := normalizedUniformizer_generates π hπ
  have hπmem : π ∈ maximalIdeal R := hgen.symm ▸ Ideal.subset_span (Set.mem_singleton _)
  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hgen
  have heis : f.IsEisensteinAt (maximalIdeal R) := by
    apply hmon.isEisensteinAt_of_mem_of_notMem ((maximalIdeal.isMaximal R).ne_top)
    · intro n hn
      have hnd : n ≠ d := ne_of_lt (by simpa only [hdeg] using hn)
      simp only [f, coeff_sub, coeff_X_pow, ite_eq_right hnd, zero_sub, Ideal.neg_mem_iff]
      by_cases h : n = 0
      · subst n
        simp [hπmem]
      · simp [coeff_C, h]
    · simp only [f, coeff_sub, coeff_X_pow, ite_eq_right (Ne.symm hd.ne'), coeff_C_zero, zero_sub, Ideal.neg_mem_iff]
      rw [hgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      obtain ⟨b, hb⟩ := h
      apply hπirr.not_isUnit
      have he : 1 = π * b := by
        apply mul_left_cancel₀ hπirr.ne_zero
        simpa only [pow_two, mul_assoc, mul_one] using hb
      exact isUnit_iff_dvd_one.mpr ⟨b, he⟩
  have hirr := heis.irreducible (maximalIdeal.isMaximal R).isPrime hmon.isPrimitive (hdeg ▸ hd)
  have hmapped := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K) hmon).mp hirr
  simpa [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C] using hmapped


theorem uniformizerRoot_pow {K : Type*} [Field K] (d : ℕ) (π : K) :
    AdjoinRoot.root (X ^ d - C π) ^ d =
      algebraMap K (AdjoinRoot (X ^ d - C π)) π := by
  apply sub_eq_zero.mp
  have hr := AdjoinRoot.eval₂_root (X ^ d - C π)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at hr
  exact hr

/-- A coefficient automorphism fixing the original uniformizer also fixes
the distinguished root in its scalar extension. -/
noncomputable def uniformizerRootAut {K : Type*} [Field K] (f : K ≃+* K)
    (d : ℕ) (π : K) (hf : f π = π) :
    AdjoinRoot (X ^ d - C π) ≃+* AdjoinRoot (X ^ d - C π) :=
  AdjoinRoot.mapRingEquiv f _ _ (by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    change Associated (X ^ d - C (f π)) (X ^ d - C π)
    rw [hf])

@[simp]
theorem uniformizerRootAut_root {K : Type*} [Field K] (f : K ≃+* K)
    (d : ℕ) (π : K) (hf : f π = π) :
    uniformizerRootAut f d π hf (AdjoinRoot.root (X ^ d - C π)) =
      AdjoinRoot.root (X ^ d - C π) := by
  simp [uniformizerRootAut]

@[simp]
theorem uniformizerRootAut_algebraMap {K : Type*} [Field K] (f : K ≃+* K)
    (d : ℕ) (π : K) (hf : f π = π) (x : K) :
    uniformizerRootAut f d π hf (algebraMap K (AdjoinRoot (X ^ d - C π)) x) =
      algebraMap K (AdjoinRoot (X ^ d - C π)) (f x) := by
  simp [uniformizerRootAut, AdjoinRoot.algebraMap_eq]

/-- The chosen extension is the quotient by the Eisenstein polynomial. -/
def uniformizerRootExtension {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (d : ℕ) (hd : 0 < d)
    (π : K) (hπ : normalizedValuation K π = exp (-1)) :
    UniformizerRootExtension K d π := by
  let π₀ : 𝒪[K] := ⟨π, (normalizedValuation_le_one π).mp (by simp [hπ])⟩
  let f : K[X] := X ^ d - C π
  have hirr : Irreducible f := uniformizerPolynomialIrreducible d hd π₀ hπ
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let E := AdjoinRoot f
  let B : PowerBasis K E := AdjoinRoot.powerBasis hirr.ne_zero
  have hdim : B.dim = d := natDegree_X_pow_sub_C
  letI : FiniteDimensional K E := (monic_X_pow_sub_C π hd.ne').finite_adjoinRoot
  let data := finiteExtension_localField (K := K) (L := E)
  let v := data.choose
  let t := data.choose_spec.choose
  letI : ValuativeRel E := v
  letI : TopologicalSpace E := t
  haveI : ValuativeExtension K E := data.choose_spec.choose_spec.1
  haveI : IsNonarchimedeanLocalField E := data.choose_spec.choose_spec.2.1
  have hpow : B.gen ^ d = algebraMap K E π := uniformizerRoot_pow d π
  have hpow' : B.gen ^ B.dim = algebraMap K E π := hdim ▸ hpow
  have hx : B.gen ≠ 0 := by
    intro h
    have hπ₀ : π ≠ 0 := (map_ne_zero (normalizedValuation K)).1 (by simp [hπ])
    exact ((algebraMap K E).injective.ne hπ₀) (by simpa [h, hd.ne'] using hpow.symm)
  exact {
    field := E
    root := Units.mk0 B.gen hx
    degree := B.finrank.trans hdim
    power := hpow
    generated := B.adjoin_gen_eq_top
    residue_bijective := ⟨RingHom.injective _,
      uniformizerRootBasis_residue_surjective B π hπ hpow'⟩ }

end UniformizerExtension

section ValuedMaps

variable {F K E N : Type u} [Field F] [Field K] [Field E] [Field N]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel N]

/-- A valuation-preserving comparison restricts to a local homomorphism. -/
def restrictValued (f : K →+* E)
    (hf : ∀ x y, valuation E (f x) ≤ valuation E (f y) ↔ valuation K x ≤ valuation K y) :
    ValuedFieldMap f where
  integers := f.restrict (valuation K).valuationSubring (valuation E).valuationSubring
    (fun x hx => by
      change valuation E (f x) ≤ 1
      rw [← (valuation E).map_one, ← f.map_one, hf, map_one]
      exact hx)
  field_eq _ := rfl
  isLocal := ⟨fun z hz => by
    apply (Valuation.integer.integers (v := valuation K)).isUnit_of_one'
    have h := (Valuation.integer.integers (v := valuation E)).one_of_isUnit hz
    change valuation E (f (z : K)) = 1 at h
    change valuation K (z : K) = 1
    apply le_antisymm z.property
    rw [← (valuation K).map_one]
    apply (hf 1 z).mp
    rw [f.map_one, h, map_one]⟩

def valuedAlgebraMap [Algebra K E] [ValuativeExtension K E] :
    ValuedFieldMap (algebraMap K E) where
  integers := algebraMap _ _
  field_eq _ := rfl

@[simp] theorem valuedAlgebraMap_residue [Algebra K E] [ValuativeExtension K E] :
    (valuedAlgebraMap (K := K) (E := E)).residue = residueMap K E := rfl

def finiteValuedEmbedding [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra F K] [Algebra F E]
    [FiniteDimensional F K] [ValuativeExtension F K] [ValuativeExtension F E]
    (f : K →ₐ[F] E) : ValuedFieldMap f.toRingHom :=
  restrictValued f.toRingHom (valuativeEmbedding f)

/-- Equality of field-map composites descends to the actual residue maps. -/
theorem residue_square {A : Type u} [Field A] [ValuativeRel A]
    {f : A →+* K} {g : K →+* N} {f' : A →+* E} {g' : E →+* N}
    (vf : ValuedFieldMap f) (vg : ValuedFieldMap g)
    (vf' : ValuedFieldMap f') (vg' : ValuedFieldMap g')
    (h : g.comp f = g'.comp f') :
    vg.residue.comp vf.residue = vg'.residue.comp vf'.residue := by
  have he : vg.integers.comp vf.integers = vg'.integers.comp vf'.integers := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    exact (vg.field_eq _).trans ((congrArg g (vf.field_eq x)).trans
      ((DFunLike.congr_fun h (x : A)).trans
        ((congrArg g' (vf'.field_eq x)).symm.trans (vg'.field_eq _).symm)))
  ext z
  obtain ⟨z, rfl⟩ := residue_surjective z
  simp only [RingHom.comp_apply, ResidueField.map_residue]
  exact congrArg (residue 𝒪[N]) (DFunLike.congr_fun he z)

/-- The residue action of a field embedding over a local base is linear
over the residue field of that base. -/
private def residueAlgHomOfEmbedding [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra F K] [Algebra F E]
    [FiniteDimensional F K] [ValuativeExtension F K] [ValuativeExtension F E]
    (f : K →ₐ[F] E) : 𝓀[K] →ₐ[𝓀[F]] 𝓀[E] where
  __ := (finiteValuedEmbedding f).residue
  commutes' := fun z => by
    obtain ⟨z, rfl⟩ := residue_surjective z
    change residue 𝒪[E] ((finiteValuedEmbedding f).integers (algebraMap 𝒪[F] 𝒪[K] z)) =
      residue 𝒪[E] (algebraMap 𝒪[F] 𝒪[E] z)
    congr 1
    exact Subtype.ext (f.commutes (z : F))

end ValuedMaps

section CompositumMaps

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {σ : Gal(L/F)}

variable (T : ∀ k : UnramifiedLevel F S, DiagramCompositum F L k.field σ)

variable {k k' k'' : UnramifiedLevel F S}

/-- A compositum map is determined by the two original factors. -/
private theorem compositum_hom_ext {N : Type u} [Field N] [Algebra F N]
    {f g : (T k).field →ₐ[F] N}
    (hL : ∀ z, f (algebraMap L (T k).field z) = g (algebraMap L (T k).field z))
    (hk : ∀ z, f (algebraMap k.field (T k).field z) = g (algebraMap k.field (T k).field z)) :
    f = g := by
  apply AlgHom.ext
  intro z
  obtain ⟨z, rfl⟩ := (T k).tensor.surjective z
  change (f.comp (T k).tensor.toAlgHom) z = (g.comp (T k).tensor.toAlgHom) z
  have h : f.comp (T k).tensor.toAlgHom = g.comp (T k).tensor.toAlgHom := by
    ext x
    · change f ((T k).tensor (x ⊗ₜ[F] (1 : k.field))) =
        g ((T k).tensor (x ⊗ₜ[F] (1 : k.field)))
      simpa only [(T k).left_eq] using hL x
    · change f ((T k).tensor ((1 : L) ⊗ₜ[F] x)) = g ((T k).tensor ((1 : L) ⊗ₜ[F] x))
      simpa only [(T k).right_eq] using hk x
  rw [h]

/-- Scalar change on the given tensor composita. -/
def compositumMap (f : k.field →ₐ[F] k'.field) : (T k).field →ₐ[F] (T k').field :=
  (T k').tensor.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id F L) f).comp (T k).tensor.symm.toAlgHom)

@[simp] theorem compositumMap_left (f : k.field →ₐ[F] k'.field) (z : L) :
    compositumMap T f (algebraMap L (T k).field z) = algebraMap L (T k').field z := by
  rw [← (T k).left_eq]
  simp [compositumMap, (T k').left_eq]

@[simp] theorem compositumMap_right (f : k.field →ₐ[F] k'.field) (z : k.field) :
    compositumMap T f (algebraMap k.field (T k).field z) = algebraMap k'.field (T k').field (f z) := by
  rw [← (T k).right_eq]
  simp [compositumMap, (T k').right_eq]

theorem compositumMap_id :
    compositumMap T (AlgHom.id F k.field) = AlgHom.id F (T k).field := by
  apply compositum_hom_ext T <;> simp

theorem compositumMap_comp (f : k.field →ₐ[F] k'.field) (g : k'.field →ₐ[F] k''.field) :
    compositumMap T (g.comp f) = (compositumMap T g).comp (compositumMap T f) := by
  apply compositum_hom_ext T <;> simp

theorem compositumMap_coefficients (f : k.field →ₐ[F] k'.field)
    (s : Gal(k.field/F)) (s' : Gal(k'.field/F))
    (hs : ∀ z, s' (f z) = f (s z)) (z : (T k).field) :
    (T k').coefficient s' (compositumMap T f z) = compositumMap T f ((T k).coefficient s z) := by
  change (((T k').coefficient s').restrictScalars F).toAlgHom.comp (compositumMap T f) z =
    ((compositumMap T f).comp (((T k).coefficient s).restrictScalars F).toAlgHom) z
  congr 1
  apply compositum_hom_ext T
  · intro a
    simp [(T k).coefficient s |>.commutes,
      (T k').coefficient s' |>.commutes]
  · intro a
    simp [(T k).coefficient_extends, (T k').coefficient_extends, hs]

private theorem towerExtension {A B C : Type*} [Field A] [Field B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
    [ValuativeExtension A B] [ValuativeExtension B C] : ValuativeExtension A C :=
  ⟨fun a b => by
    rw [IsScalarTower.algebraMap_apply A B C a, IsScalarTower.algebraMap_apply A B C b,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩

/-- The residue degree of the diagram compositum over the coefficient field is one. -/
theorem coefficientResidue_bijective [FiniteDimensional F L] [IsGalois F L]
    (hd : Module.finrank F L = 2) (hr : 1 < ramificationIndex F L) (k : UnramifiedLevel F S) :
    Function.Bijective (coefficientResidue T k) :=
  (ExceptionalLocalRootCoordinates.ramifiedQuadratic k.field (T k).field (T k).degree
    (diagramCompositum_ramification (T k) hd hr k.unramified)).2.2

variable (d : ℕ) (hd : 0 < d) (π : L) (hπ : normalizedValuation L π = exp (-1))

def stageExtension (k : UnramifiedLevel F S) :
    UniformizerRootExtension (T k).field d (algebraMap L (T k).field π) :=
  uniformizerRootExtension d hd _ ((T k).unramified π |>.trans hπ)

local notation "E[" k "]" => stageExtension T d hd π hπ k

/-- The root-preserving map is the map on quotients of the same polynomial. -/
private def stageMap (f : k.field →ₐ[F] k'.field) : E[k].field →+* E[k'].field :=
  AdjoinRoot.lift ((algebraMap (T k').field E[k'].field).comp (compositumMap T f).toRingHom)
    (E[k'].root : E[k'].field) (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        RingHom.comp_apply]
      rw [E[k'].power]
      exact sub_eq_zero.mpr (congrArg _ (compositumMap_left T f π).symm))

@[simp] private theorem stageMap_root (f : k.field →ₐ[F] k'.field) :
    stageMap T d hd π hπ f (E[k].root : E[k].field) = E[k'].root :=
  AdjoinRoot.lift_root ..

@[simp] private theorem stageMap_diagram (f : k.field →ₐ[F] k'.field) (z : (T k).field) :
    stageMap T d hd π hπ f (algebraMap (T k).field E[k].field z) =
      algebraMap (T k').field E[k'].field (compositumMap T f z) :=
  AdjoinRoot.lift_of ..

private theorem stage_hom_ext {N : Type u} [Field N] {f g : E[k].field →+* N}
    (h₁ : ∀ z, f (algebraMap (T k).field E[k].field z) =
      g (algebraMap (T k).field E[k].field z))
    (h₂ : f (E[k].root : E[k].field) = g (E[k].root : E[k].field)) :
    f = g :=
  AdjoinRoot.ringHom_ext (RingHom.ext h₁) h₂

private theorem stageMap_id :
    stageMap T d hd π hπ (AlgHom.id F k.field) = RingHom.id E[k].field := by
  apply stage_hom_ext T d hd π hπ
  · simp [compositumMap_id]
  · simp

private theorem stageMap_comp (f : k.field →ₐ[F] k'.field) (g : k'.field →ₐ[F] k''.field) :
    stageMap T d hd π hπ (g.comp f) =
      (stageMap T d hd π hπ g).comp (stageMap T d hd π hπ f) := by
  apply stage_hom_ext T d hd π hπ
  · simp [compositumMap_comp]
  · simp

private def stageAuto (k : UnramifiedLevel F S) (s : Gal(k.field/F)) :
    E[k].field ≃+* E[k].field :=
  uniformizerRootAut ((T k).coefficient s).toRingEquiv d _ (((T k).coefficient s).commutes π)

@[simp] private theorem stageAuto_root (k : UnramifiedLevel F S) (s : Gal(k.field/F)) :
    stageAuto T d hd π hπ k s (E[k].root : E[k].field) = E[k].root :=
  uniformizerRootAut_root ..

@[simp] private theorem stageAuto_diagram (k : UnramifiedLevel F S) (s : Gal(k.field/F))
    (z : (T k).field) :
    stageAuto T d hd π hπ k s (algebraMap (T k).field E[k].field z) =
      algebraMap (T k).field E[k].field ((T k).coefficient s z) :=
  uniformizerRootAut_algebraMap ..

private def stageAction (k : UnramifiedLevel F S) : Gal(k.field/F) →* (E[k].field ≃+* E[k].field) where
  toFun := stageAuto T d hd π hπ k
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply stage_hom_ext T d hd π hπ
    · intro z
      simp [stageAuto_diagram]
    · simp
  map_mul' s s' := by
    apply RingEquiv.toRingHom_injective
    apply stage_hom_ext T d hd π hπ
    · intro z
      simp [stageAuto_diagram, AlgEquiv.mul_apply]
    · simp

private theorem stageAuto_natural (f : k.field →ₐ[F] k'.field) (s : Gal(k.field/F)) (s' : Gal(k'.field/F))
    (hs : ∀ z, s' (f z) = f (s z)) (z : E[k].field) :
    stageAuto T d hd π hπ k' s' (stageMap T d hd π hπ f z) =
      stageMap T d hd π hπ f (stageAuto T d hd π hπ k s z) := by
  change ((stageAuto T d hd π hπ k' s').toRingHom.comp (stageMap T d hd π hπ f)) z =
    ((stageMap T d hd π hπ f).comp (stageAuto T d hd π hπ k s).toRingHom) z
  congr 1
  apply stage_hom_ext T d hd π hπ
  · intro x
    simp [compositumMap_coefficients T f s s' hs]
  · simp

local instance stageBase (k : UnramifiedLevel F S) : Algebra F E[k].field :=
  ((algebraMap (T k).field E[k].field).comp (algebraMap F (T k).field)).toAlgebra

local instance stageScalarTower (k : UnramifiedLevel F S) :
    IsScalarTower F (T k).field E[k].field :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance compositumExtendsBase (k : UnramifiedLevel F S) : ValuativeExtension F (T k).field :=
  towerExtension (B := k.field)

local instance stageExtendsBase (k : UnramifiedLevel F S) : ValuativeExtension F E[k].field :=
  towerExtension (B := (T k).field)

local instance compositumFinite (k : UnramifiedLevel F S) : FiniteDimensional F (T k).field :=
  FiniteDimensional.trans F k.field (T k).field

local instance stageFinite (k : UnramifiedLevel F S) : FiniteDimensional F E[k].field :=
  FiniteDimensional.trans F (T k).field E[k].field

private def stageAlgHom (f : k.field →ₐ[F] k'.field) : E[k].field →ₐ[F] E[k'].field :=
  { stageMap T d hd π hπ f with
    commutes' := fun z => by
      rw [IsScalarTower.algebraMap_apply F (T k).field E[k].field,
        IsScalarTower.algebraMap_apply F (T k').field E[k'].field]
      change stageMap T d hd π hπ f _ = _
      rw [stageMap_diagram, AlgHom.commutes] }

private def stageAutoAlgHom (k : UnramifiedLevel F S) (s : Gal(k.field/F)) :
    E[k].field →ₐ[F] E[k].field :=
  { (stageAuto T d hd π hπ k s).toRingHom with
    commutes' := fun z => by
      rw [IsScalarTower.algebraMap_apply F (T k).field E[k].field]
      change stageAuto T d hd π hπ k s _ = _
      rw [stageAuto_diagram, IsScalarTower.algebraMap_apply F L (T k).field,
        AlgEquiv.commutes] }

private def stageActionValued (k : UnramifiedLevel F S) (s : Gal(k.field/F)) :
    ValuedFieldMap (stageAction T d hd π hπ k s).toRingHom :=
  finiteValuedEmbedding (stageAutoAlgHom T d hd π hπ k s)

private def stageTransition (h : k ≤ k') :
    AuxiliaryTransition T h E[k] E[k'] where
  coefficient := finiteValuedEmbedding (UnramifiedLevel.inclusion h)
  diagram := compositumMap T (UnramifiedLevel.inclusion h)
  diagram_left := compositumMap_left T _
  diagram_right := compositumMap_right T _
  diagramValued := finiteValuedEmbedding (compositumMap T (UnramifiedLevel.inclusion h))
  auxiliary := stageMap T d hd π hπ (UnramifiedLevel.inclusion h)
  auxiliary_diagram := stageMap_diagram T d hd π hπ _
  auxiliary_root := stageMap_root T d hd π hπ _
  valued := finiteValuedEmbedding (stageAlgHom T d hd π hπ (UnramifiedLevel.inclusion h))
  diagram_residue := residue_square (valuedAlgebraMap) _ _ (valuedAlgebraMap)
    (RingHom.ext (compositumMap_right T _))
  auxiliary_residue := residue_square (valuedAlgebraMap) _ _ (valuedAlgebraMap)
    (RingHom.ext (stageMap_diagram T d hd π hπ _))

end CompositumMaps


section LocalUnramifiedFields

variable {F K S : Type u} [Field F] [Field K] [Field S] [Algebra F K] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A valuation of the base extends to the chosen separable closure. -/
private theorem exists_ambient_valuation :
    ∃ r : ValuativeRel S, @ValuativeExtension F S _ _ _ r _ := by
  let v := valuation F
  let f := (algebraMap F S).comp (v.valuationSubring.subtype)
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  letI : ValuativeRel S := .ofValuation V.valuation
  let w := V.valuation
  haveI : w.Compatible := Valuation.Compatible.ofValuation _
  have hle (x : F) : w (algebraMap F S x) ≤ 1 ↔ v x ≤ 1 := by
    rw [V.valuation_le_one_iff]
    refine ⟨?_, fun hx => hV ⟨x, hx⟩⟩
    intro hx
    by_contra! h
    have hx0 : x ≠ 0 := by
      intro h'; simp [h'] at h
    let z : v.valuationSubring := ⟨x⁻¹, by
      change v x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h.le⟩
    have hz : IsUnit (f.codRestrict V.toSubring hV z) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨algebraMap F S x, hx⟩, Subtype.ext ?_⟩
      change algebraMap F S x⁻¹ * algebraMap F S x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hu : IsUnit z := IsLocalHom.map_nonunit _ hz
    have hu' := (Valuation.integer.integers (v := v)).one_of_isUnit hu
    change v x⁻¹ = 1 at hu'
    rw [map_inv₀, inv_eq_one] at hu'
    exact h.ne' hu'
  have he : v.IsEquiv (w.comap (algebraMap F S)) :=
    Valuation.isEquiv_iff_val_le_one.mpr (fun {x} => (hle x).symm)
  refine ⟨inferInstance, ⟨fun x y => ?_⟩⟩
  rw [w.vle_iff_le, v.vle_iff_le]
  exact (he x y).symm

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K]

/-- The familiar Hensel lifting property for the actual valuation ring. -/
private theorem local_henselian (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : HenselianLocalRing 𝒪[K] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  exact ((HenselianLocalRing.TFAE 𝒪[K]).out 3 1).mp
    (by
      intro J _ φ hφ f hf b hb hb'
      obtain ⟨b, rfl⟩ := hφ b
      have hI : RingHom.ker φ = maximalIdeal 𝒪[K] := ker_eq_maximalIdeal φ hφ
      have heval : f.eval b ∈ maximalIdeal 𝒪[K] := by
        rw [← hI, RingHom.mem_ker, ← eval₂_at_apply]
        exact hb
      have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal 𝒪[K]) (f.derivative.eval b)) := by
        apply IsUnit.map (Ideal.Quotient.mk (maximalIdeal 𝒪[K]))
        rw [← notMem_maximalIdeal, ← hI, RingHom.mem_ker, ← eval₂_at_apply]
        exact hb'
      obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian f hf b heval hderiv
      rw [← hI, RingHom.mem_ker, map_sub, sub_eq_zero] at hab
      exact ⟨a, ha, hab⟩)

private theorem lift_monic_residue (g : 𝓀[F][X]) (hg : g.Monic) :
    ∃ f : 𝒪[F][X], f.map (residue 𝒪[F]) = g ∧ f.natDegree = g.natDegree ∧ f.Monic :=
  lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).mpr (Polynomial.map_surjective _ residue_surjective g)) hg

private theorem lift_residue_root (f : 𝒪[F][X]) (hf : f.Monic) (b : 𝓀[K])
    (hr : aeval b (f.map (residue 𝒪[F])) = 0)
    (hs : aeval b (f.map (residue 𝒪[F])).derivative ≠ 0) :
    ∃ a : 𝒪[K], (f.map (algebraMap 𝒪[F] 𝒪[K])).IsRoot a ∧ residue 𝒪[K] a = b := by
  have hH : HenselianLocalRing 𝒪[K] := local_henselian K
  have hh :
      ∀ (g : 𝒪[K][X]), g.Monic → ∀ c : 𝓀[K], aeval c g = 0 →
        aeval c g.derivative ≠ 0 → ∃ a : 𝒪[K], g.IsRoot a ∧ residue 𝒪[K] a = c :=
    ((HenselianLocalRing.TFAE 𝒪[K]).out 1 2).mp hH
  have hbase : algebraMap 𝒪[K] 𝓀[K] = residue 𝒪[K] := rfl
  have hmap : algebraMap 𝓀[F] 𝓀[K] = ResidueField.map (algebraMap 𝒪[F] 𝒪[K]) := rfl
  apply hh _ (hf.map _) b
  · simpa only [aeval_def, eval₂_map, hbase, hmap, ResidueField.map_comp_residue]
      using hr
  · simpa only [derivative_map, aeval_def, eval₂_map, hbase, hmap,
      ResidueField.map_comp_residue] using hs

end LocalUnramifiedFields


section ResidueBasis

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K]

/-- Surjectivity on values forces the ramification index to be one. -/
private theorem unramified_of_same_values
    (h : ∀ z : K, ∃ a : F, valuation K z = valuation K (algebraMap F K a)) :
    IsUnramifiedLocalExtension F K := by
  obtain ⟨e, he, heq⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization F).2.2 K
  obtain ⟨z, hz⟩ := normalizedValuation_surjective K (exp (-1))
  obtain ⟨a, ha⟩ := h z
  have hval : normalizedValuation K (algebraMap F K a) = exp (-1) :=
    (congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) ha).symm.trans hz
  have hpow : normalizedValuation F a ^ e = exp (-1) := (heq a).symm.trans hval
  have hlog := congrArg (WithZero.log : ℤᵐ⁰ → ℤ) hpow
  rw [← zpow_natCast, log_zpow, log_exp, zsmul_eq_mul] at hlog
  have hed : (e : ℤ) ∣ (-1 : ℤ) := ⟨_, hlog.symm⟩
  have h₁ : e = 1 := by
    have := Int.le_of_dvd (by decide : 0 < (1 : ℤ)) (dvd_neg.mp hed)
    omega
  intro a
  change normalizedValuation K (algebraMap F K a) = normalizedValuation F a
  have hh := heq a
  change normalizedValuation K (algebraMap F K a) = normalizedValuation F a ^ e at hh
  rw [hh, h₁, pow_one]

/-- A basis whose reductions are independent is orthogonal for the
valuation, with the valuation of a sum given by a largest coefficient. -/
private theorem valuation_basis_max {m : ℕ} (B : Module.Basis (Fin m) F K)
    (b : Fin m → 𝒪[K]) (hb : ∀ i, (b i : K) = B i)
    (hred : LinearIndependent 𝓀[F] (fun i => residue 𝒪[K] (b i))) (hm : 0 < m)
    (z : K) :
    ∃ j : Fin m, valuation K z = valuation K (algebraMap F K (B.repr z j)) ∧
      ∀ i, valuation F (B.repr z i) ≤ valuation F (B.repr z j) := by
  classical
  let a := B.repr z
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun i => valuation F (a i)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  refine ⟨j, ?_, fun i => hj i (Finset.mem_univ i)⟩
  by_cases h0 : a j = 0
  · have ha : a = 0 := by
      ext i
      have h := hj i (Finset.mem_univ i)
      rw [h0, map_zero, le_zero_iff, (valuation F).zero_iff] at h
      exact h
    have hz : z = 0 := B.repr.injective (ha.trans B.repr.map_zero.symm)
    simp [hz]
  let c (i : Fin m) : 𝒪[F] := ⟨a i / a j, by
    change valuation F (a i / a j) ≤ 1
    rw [map_div₀, div_le_iff₀ ((valuation F).pos_iff.mpr h0), one_mul]
    exact hj i (Finset.mem_univ i)⟩
  let w : 𝒪[K] := ∑ i, (algebraMap 𝒪[F] 𝒪[K] (c i)) * b i
  have hunit : IsUnit w := by
    apply (residue_ne_zero_iff_isUnit w).mp
    intro h
    have he : ∑ i ∈ (Finset.univ : Finset (Fin m)), (residue 𝒪[F] (c i)) •
        (residue 𝒪[K] (b i)) = 0 := by
      have hmap : algebraMap 𝓀[F] 𝓀[K] = ResidueField.map (algebraMap 𝒪[F] 𝒪[K]) := rfl
      simpa only [w, map_sum, map_mul, Algebra.smul_def, hmap, ← ResidueField.map_residue] using h
    have hf := (linearIndependent_iff'.mp hred) _ _ he j (Finset.mem_univ _)
    have hc : c j = 1 := Subtype.ext (div_self h0)
    rw [hc, map_one] at hf
    exact one_ne_zero hf
  have hv := (Valuation.integer.integers (v := valuation K)).one_of_isUnit hunit
  change valuation K (w : K) = 1 at hv
  have hsum : algebraMap F K (a j) * (w : K) = z := by
    change algebraMap F K (a j) *
        ((valuation K).valuationSubring.subtype (∑ i, algebraMap 𝒪[F] 𝒪[K] (c i) * b i)) = z
    rw [map_sum, Finset.mul_sum]
    convert B.sum_repr z using 1
    apply Finset.sum_congr rfl
    intro i _
    change algebraMap F K (a j) * (algebraMap F K (a i / a j) * (b i : K)) = a i • B i
    rw [hb, ← mul_assoc, ← map_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ h0, Algebra.smul_def]
  conv_lhs => rw [← hsum, map_mul, hv, mul_one]

private theorem minpoly_lift_irreducible (f : 𝒪[F][X]) (hf : f.Monic)
    (hred : Irreducible (f.map (residue 𝒪[F]))) :
    Irreducible (f.map (algebraMap 𝒪[F] F)) :=
  (hf.irreducible_iff_irreducible_map_fraction_map (K := F)).mp
    (Polynomial.Monic.irreducible_of_irreducible_map _ f hf hred)

/-- Adjoining an integral root of a monic lift of its residue minimal
polynomial gives an unramified extension with the expected residue generator. -/
private theorem powerBasis_unramified (B : PowerBasis F K) (b : 𝒪[K])
    (hb : (b : K) = B.gen)
    (hdeg : (minpoly 𝓀[F] (residue 𝒪[K] b)).natDegree = B.dim) :
    IsUnramifiedLocalExtension F K ∧
      IntermediateField.adjoin 𝓀[F] {residue 𝒪[K] b} = ⊤ := by
  have hlin : LinearIndependent 𝓀[F] (fun i : Fin B.dim => residue 𝒪[K] (b ^ (i : ℕ))) := by
    simp only [map_pow]
    let e : Fin B.dim ≃ Fin (minpoly 𝓀[F] (residue 𝒪[K] b)).natDegree := finCongr hdeg.symm
    exact (linearIndependent_pow (K := 𝓀[F]) (residue 𝒪[K] b)).comp e e.injective
  have hmax (z : K) := valuation_basis_max B.basis (fun i => b ^ (i : ℕ))
    (fun i => by rw [B.basis_eq_pow]; exact congrArg (· ^ (i : ℕ)) hb)
    hlin B.dim_pos z
  refine ⟨unramified_of_same_values (fun z => ?_), ?_⟩
  · obtain ⟨j, hj, _⟩ := hmax z
    exact ⟨B.basis.repr z j, hj⟩
  · apply eq_top_iff.mpr
    intro x _
    obtain ⟨z, rfl⟩ := residue_surjective x
    obtain ⟨j, hj, hji⟩ := hmax (z : K)
    have hj₀ : valuation F (B.basis.repr (z : K) j) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (valuation F) (valuation K) _).mp
        (hj ▸ z.property)
    let a (i : Fin B.dim) : 𝒪[F] := ⟨B.basis.repr (z : K) i, (hji i).trans hj₀⟩
    have hs : z = ∑ i, algebraMap 𝒪[F] 𝒪[K] (a i) * b ^ (i : ℕ) := by
      apply Subtype.ext
      change (z : K) = (valuation K).valuationSubring.subtype
        (∑ i, algebraMap 𝒪[F] 𝒪[K] (a i) * b ^ (i : ℕ))
      rw [map_sum]
      refine (B.basis.sum_repr (z : K)).symm.trans (Finset.sum_congr rfl ?_)
      intro i _
      change (B.basis.repr (z : K) i) • B.basis i =
        algebraMap F K (B.basis.repr (z : K) i) * (b : K) ^ (i : ℕ)
      rw [hb, B.basis_eq_pow, Algebra.smul_def]
    rw [hs, map_sum]
    apply IntermediateField.sum_mem
    intro i _
    rw [map_mul, map_pow, ← ResidueField.map_residue]
    apply IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
    exact pow_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) _

end ResidueBasis


section UnramifiedBridges

variable {F J K : Type u} [Field F] [Field J] [Field K] [Algebra F J] [Algebra F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel J] [TopologicalSpace J] [IsNonarchimedeanLocalField J] [ValuativeExtension F J]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  [FiniteDimensional F J]

/-- An embedding into an unramified extension whose actual residue map
is onto is itself onto. Adic completeness lifts the residue surjection. -/
private theorem surjective_of_unramified_residue
    (f : J →ₐ[F] K) (hu : IsUnramifiedLocalExtension F K)
    (hs : Function.Surjective (finiteValuedEmbedding f).residue) :
    Function.Surjective f := by
  classical
  let v := finiteValuedEmbedding f
  have huJ : IsUnramifiedLocalExtension F J := by
    apply unramified_of_same_values
    intro z
    obtain ⟨a, ha⟩ := normalizedValuation_surjective F (normalizedValuation K (f z))
    have hv : normalizedValuation K (f z) = normalizedValuation K (f (algebraMap F J a)) := by
      rw [f.commutes, hu a, ha]
    have heq := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective hv
    exact ⟨a, le_antisymm ((valuativeEmbedding f _ _).mp heq.le)
      ((valuativeEmbedding f _ _).mp heq.ge)⟩
  obtain ⟨π, hπ⟩ := normalizedValuation_surjective F (exp (-1))
  let πJ : 𝒪[J] := ⟨algebraMap F J π, (normalizedValuation_le_one _).mp (by rw [huJ π, hπ]; simp)⟩
  have hπK : normalizedValuation K (v.integers πJ : K) = exp (-1) := by
    rw [v.field_eq]
    change normalizedValuation K (f (algebraMap F J π)) = exp (-1)
    rw [f.commutes, hu π, hπ]
  have hI : (maximalIdeal 𝒪[J]).map v.integers = maximalIdeal 𝒪[K] := by
    have hJ : maximalIdeal 𝒪[J] = Ideal.span {πJ} :=
      normalizedUniformizer_generates πJ ((huJ π).trans hπ)
    have hK : maximalIdeal 𝒪[K] = Ideal.span {v.integers πJ} :=
      normalizedUniformizer_generates (v.integers πJ) hπK
    rw [hJ, hK, Ideal.map_span, Set.image_singleton]
  letI : UniformSpace J := IsTopologicalAddGroup.rightUniformSpace J
  letI : IsUniformAddGroup J := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hH : IsHausdorff ((maximalIdeal 𝒪[J]).map v.integers) 𝒪[K] :=
    hI.symm ▸ (inferInstance : IsHausdorff (maximalIdeal 𝒪[K]) 𝒪[K])
  have hO : Function.Surjective v.integers := by
    apply surjective_of_mk_map_comp_surjective (I := maximalIdeal 𝒪[J])
    rw [hI]
    exact hs.comp residue_surjective
  intro z
  by_cases hz : valuation K z ≤ 1
  · obtain ⟨a, ha⟩ := hO (⟨z, hz⟩ : 𝒪[K])
    exact ⟨a, (v.field_eq a).symm.trans (congrArg Subtype.val ha)⟩
  · have hzi : valuation K z⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hz))
    obtain ⟨a, ha⟩ := hO (⟨z⁻¹, hzi⟩ : 𝒪[K])
    refine ⟨(a : J)⁻¹, ?_⟩
    rw [map_inv₀]
    change (f.toRingHom (a : J))⁻¹ = z
    rw [← v.field_eq, ha]
    exact inv_inv z

end UnramifiedBridges

section LocalStructure

variable (F K : Type u) [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private structure LocalStructure where
  r : ValuativeRel K
  top : TopologicalSpace K
  extension : @ValuativeExtension F K _ _ _ r _
  localField : @IsNonarchimedeanLocalField K _ r top

private def selectLocalStructure [FiniteDimensional F K] : LocalStructure F K :=
  let h := finiteExtension_localField (K := F) (L := K)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2.1⟩

end LocalStructure


section GaloisLift

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]

private theorem lift_root_aeval {f : 𝒪[F][X]} {a : 𝒪[K]}
    (ha : (f.map (algebraMap 𝒪[F] 𝒪[K])).IsRoot a) :
    aeval (a : K) (f.map (algebraMap 𝒪[F] F)) = 0 := by
  have he : ((algebraMap F K).comp (algebraMap 𝒪[F] F)) =
      ((algebraMap 𝒪[K] K).comp (algebraMap 𝒪[F] 𝒪[K])) := rfl
  have h := congrArg (algebraMap 𝒪[K] K) ha
  rw [← eval₂_at_apply, eval₂_map, map_zero] at h
  rw [aeval_def, eval₂_map, he]
  exact h

private theorem isGalois_of_residue_generator (B : PowerBasis F K)
    (b : 𝒪[K]) (hb : (b : K) = B.gen)
    (f : 𝒪[F][X]) (hf : f.Monic)
    (hfF : f.map (algebraMap 𝒪[F] F) = minpoly F B.gen)
    (hfb : f.map (residue 𝒪[F]) = minpoly 𝓀[F] (residue 𝒪[K] b))
    (htop : IntermediateField.adjoin 𝓀[F] {residue 𝒪[K] b} = ⊤) : IsGalois F K := by
  let b₀ := residue 𝒪[K] b
  letI : FiniteDimensional F K := B.finite
  have hdeg : Module.finrank 𝓀[F] 𝓀[K] = Module.finrank F K := by
    let pb := PowerBasis.ofAdjoinSimpleEqTop
      (Algebra.IsIntegral.isIntegral (R := 𝓀[F]) b₀) htop
    have hpb : pb.dim = (minpoly 𝓀[F] b₀).natDegree :=
      PowerBasis.ofAdjoinSimpleEqTop_dim _ _
    calc
      Module.finrank 𝓀[F] 𝓀[K] = pb.dim := pb.finrank
      _ = Module.finrank F K := by
        rw [hpb, B.finrank, ← B.natDegree_minpoly, ← hfF, ← hfb,
          hf.natDegree_map, hf.natDegree_map]
  have hsep : (minpoly 𝓀[F] b₀).Separable := Algebra.IsSeparable.isSeparable _ _
  have h (s : Gal(𝓀[K]/𝓀[F])) :
      ∃ a : 𝒪[K], (f.map (algebraMap 𝒪[F] 𝒪[K])).IsRoot a ∧ residue 𝒪[K] a = s b₀ := by
    have hroot : aeval (s b₀) (minpoly 𝓀[F] b₀) = 0 := minpoly.aeval_algHom _ s.toAlgHom _
    apply lift_residue_root f hf
    · rw [hfb]; exact hroot
    · rw [hfb]; exact hsep.aeval_derivative_ne_zero hroot
  choose r hr using h
  let φ (s : Gal(𝓀[K]/𝓀[F])) : K →ₐ[F] K :=
    B.lift (r s : K) (hfF ▸ lift_root_aeval (hr s).1)
  let θ (s : Gal(𝓀[K]/𝓀[F])) : Gal(K/F) :=
    AlgEquiv.ofBijective (φ s) ⟨(φ s).injective,
      LinearMap.injective_iff_surjective.mp (φ s).injective⟩
  have hθ : Function.Injective θ := by
    intro s t hst
    have he : (r s : K) = r t := by
      have he := DFunLike.congr_fun hst B.gen
      change φ s B.gen = φ t B.gen at he
      simpa only [φ, PowerBasis.lift_gen] using he
    have hr' : s b₀ = t b₀ := by
      rw [← (hr s).2, ← (hr t).2, Subtype.ext he]
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top (s := {b₀})
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (R := 𝓀[F]) b₀), htop, IntermediateField.top_toSubalgebra]
    · rintro x (rfl : x = b₀)
      exact hr'
  have hle := Nat.card_le_card_of_injective θ hθ
  rw [IsGalois.card_aut_eq_finrank, hdeg] at hle
  apply IsGalois.of_card_aut_eq_finrank
  exact le_antisymm (by rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le) hle

end GaloisLift


section UnramifiedSubfields

variable {F S : Type u} [Field F] [Field S] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem exists_residue_generator_lift (K : Type u) [Field K] [Algebra F K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K] :
    ∃ (f : 𝒪[F][X]) (a : 𝒪[K]), f.Monic ∧ (f.map (algebraMap 𝒪[F] 𝒪[K])).IsRoot a ∧
      f.map (residue 𝒪[F]) = minpoly 𝓀[F] (residue 𝒪[K] a) ∧
      IntermediateField.adjoin 𝓀[F] {residue 𝒪[K] a} = ⊤ := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element 𝓀[F] 𝓀[K]
  have hmon : (minpoly 𝓀[F] b).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral b)
  obtain ⟨f, hfb, _, hf⟩ := lift_monic_residue (minpoly 𝓀[F] b) hmon
  have hsep : (minpoly 𝓀[F] b).Separable := Algebra.IsSeparable.isSeparable _ _
  obtain ⟨a, ha, hab⟩ := lift_residue_root f hf b
    (hfb.symm ▸ minpoly.aeval _ _) (hfb.symm ▸ hsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  exact ⟨f, a, hf, ha, hab ▸ hfb, hab ▸ hb⟩

/-- Inside a finite local extension, adjoining a simple lift of a
primitive residue element realizes its entire residue field. -/
private theorem unramifiedSubfield_generated (K : IntermediateField F S)
    [FiniteDimensional F K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (f : 𝒪[F][X]) (a : 𝒪[K]) (hf : f.Monic)
    (ha : (f.map (algebraMap 𝒪[F] 𝒪[K])).IsRoot a)
    (hred : f.map (residue 𝒪[F]) = minpoly 𝓀[F] (residue 𝒪[K] a))
    (htop : IntermediateField.adjoin 𝓀[F] {residue 𝒪[K] a} = ⊤) :
    ∃ (J : UnramifiedLevel F S) (h : J.field ≤ K),
      J.field = IntermediateField.adjoin F ({((a : K) : S)} : Set S) ∧
      Function.Surjective (finiteValuedEmbedding (IntermediateField.inclusion h)).residue := by
  let x : S := (a : K)
  let E := IntermediateField.adjoin F ({x} : Set S)
  have hE : E ≤ K := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (a : K).property)
  have hx : IsIntegral F x := (Algebra.IsIntegral.isIntegral (R := F) (a : K)).map K.val
  let B := IntermediateField.adjoin.powerBasis hx
  letI : FiniteDimensional F E := B.finite
  let s := selectLocalStructure F E
  letI : ValuativeRel E := s.r
  letI : TopologicalSpace E := s.top
  letI : ValuativeExtension F E := s.extension
  letI : IsNonarchimedeanLocalField E := s.localField
  let ι := IntermediateField.inclusion hE
  let v := finiteValuedEmbedding ι
  have hgen : ι B.gen = (a : K) := rfl
  have hgen_int : valuation E B.gen ≤ 1 := by
    rw [← (valuation E).map_one, ← valuativeEmbedding ι, hgen, map_one, map_one]
    exact a.property
  let b : 𝒪[E] := ⟨B.gen, hgen_int⟩
  have hba : v.integers b = a := Subtype.ext ((v.field_eq b).trans hgen)
  let ρ := residueAlgHomOfEmbedding ι
  have hρ : ρ (residue 𝒪[E] b) = residue 𝒪[K] a := by
    change residue 𝒪[K] (v.integers b) = _
    rw [hba]
  have hredE : f.map (residue 𝒪[F]) = minpoly 𝓀[F] (residue 𝒪[E] b) := by
    rw [hred, ← hρ, minpoly.algHom_eq ρ ρ.injective]
  have hfE : f.map (algebraMap 𝒪[F] F) = minpoly F B.gen := by
    apply minpoly.eq_of_irreducible_of_monic (minpoly_lift_irreducible f hf ?_) _ (hf.map _)
    · rw [hred]
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
    · apply ι.injective
      change ι (aeval B.gen _) = ι 0
      rw [map_zero, ← aeval_algHom_apply ι, hgen]
      exact lift_root_aeval ha
  have hdegree : (minpoly 𝓀[F] (residue 𝒪[E] b)).natDegree = B.dim := by
    rw [← B.natDegree_minpoly, ← hfE, ← hredE, hf.natDegree_map, hf.natDegree_map]
  obtain ⟨hu, htopE⟩ := powerBasis_unramified B b rfl hdegree
  letI : IsGalois F E := isGalois_of_residue_generator B b rfl f hf hfE hredE htopE
  let J : UnramifiedLevel F S := { field := E, unramified := hu }
  refine ⟨J, hE, rfl, ?_⟩
  change Function.Surjective ρ
  apply AlgHom.fieldRange_eq_top.mp
  apply top_unique
  rw [← htop]
  apply IntermediateField.adjoin_le_iff.mpr
  exact Set.singleton_subset_iff.mpr ⟨residue 𝒪[E] b, hρ⟩

/-- A finite unramified subfield is generated by a simple lift of a
primitive residue element, hence is Galois. -/
theorem finiteUnramifiedSubfieldsAreGalois : FiniteUnramifiedSubfieldsAreGalois.{u} := by
  intro F S _ _ _ _ _ _ K _ _ _ _ _ hUnramified
  obtain ⟨f, a, hf, ha, hred, htop⟩ := exists_residue_generator_lift (F := F) K
  obtain ⟨J, hJ, _, hres⟩ := unramifiedSubfield_generated K f a hf ha hred htop
  let ι := IntermediateField.inclusion hJ
  have hι : Function.Surjective ι :=
    surjective_of_unramified_residue ι hUnramified hres
  exact IsGalois.of_algEquiv (AlgEquiv.ofBijective ι ⟨ι.injective, hι⟩)

private theorem exists_base_level : ∃ k : UnramifiedLevel F S, k.field = ⊥ := by
  let K : IntermediateField F S := ⊥
  let e := IntermediateField.botEquiv F S
  letI : FiniteDimensional F K := e.symm.toLinearEquiv.finiteDimensional
  letI : IsGalois F K := IsGalois.of_algEquiv e.symm
  let s := selectLocalStructure F K
  letI : ValuativeRel K := s.r
  letI : TopologicalSpace K := s.top
  letI : ValuativeExtension F K := s.extension
  letI : IsNonarchimedeanLocalField K := s.localField
  have hr : IsUnramifiedLocalExtension F K := by
    apply unramified_of_same_values
    intro z
    have h : algebraMap F K (e z) = z := by
      have he : e.symm (e z) = algebraMap F K (e z) := by simpa using e.symm.commutes (e z)
      rw [← he, e.symm_apply_apply]
    exact ⟨e z, (congrArg (valuation K) h).symm⟩
  exact ⟨{ field := K, unramified := hr }, rfl⟩

end UnramifiedSubfields


section DirectedResidues

variable {F S : Type u} [Field F] [Field S] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel S] [ValuativeExtension F S]

private abbrev levelResidue (k : UnramifiedLevel F S) : 𝓀[k.field] →+* 𝓀[S] :=
  (finiteValuedEmbedding k.field.val).residue

private theorem residue_comp_finite {J K : Type u} [Field J] [Field K] [Algebra F J] [Algebra F K]
    [ValuativeRel J] [ValuativeRel K] [ValuativeExtension F J] [ValuativeExtension F K]
    [FiniteDimensional F J] [FiniteDimensional F K] (f : J →ₐ[F] K) (g : K →ₐ[F] S) :
    (finiteValuedEmbedding g).residue.comp (finiteValuedEmbedding f).residue =
      (finiteValuedEmbedding (g.comp f)).residue := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  simp only [RingHom.comp_apply, ResidueField.map_residue]
  congr 1

private theorem levelResidue_compatible {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    (levelResidue k').comp (finiteValuedEmbedding (UnramifiedLevel.inclusion h)).residue =
      levelResidue k :=
  residue_comp_finite (UnramifiedLevel.inclusion h) k'.field.val

private theorem levelResidue_base (k : UnramifiedLevel F S) :
    (levelResidue k).comp (residueMap F k.field) = residueMap F S := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  change residue 𝒪[S] ((finiteValuedEmbedding k.field.val).integers (algebraMap 𝒪[F] 𝒪[k.field] a)) =
    residue 𝒪[S] (algebraMap 𝒪[F] 𝒪[S] a)
  congr 1

/-- An actual unramified subfield is determined, with its order, by its
image in the residue field of the common separable closure. -/
private theorem level_le_of_residue_le (k k' : UnramifiedLevel F S)
    (h : Set.range (levelResidue k) ⊆ Set.range (levelResidue k')) : k ≤ k' := by
  obtain ⟨f, a, hf, ha, hred, htop⟩ := exists_residue_generator_lift (F := F) k.field
  obtain ⟨J, hJ, hgen, hsurj⟩ := unramifiedSubfield_generated k.field f a hf ha hred htop
  have hK : k.field = IntermediateField.adjoin F ({((a : k.field) : S)} : Set S) := by
    have hs := surjective_of_unramified_residue (IntermediateField.inclusion hJ) k.unramified hsurj
    have he : J.field = k.field := by
      apply le_antisymm hJ
      intro x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
      have he : (y : S) = x := congrArg Subtype.val hy
      rw [← he]
      exact y.property
    exact he.symm.trans hgen
  obtain ⟨c, hc⟩ := h (Set.mem_range_self (residue 𝒪[k.field] a))
  have hm : ∀ p : 𝓀[F][X], aeval c p = 0 ↔ aeval (residue 𝒪[k.field] a) p = 0 := by
    intro p
    let r := residueAlgHomOfEmbedding k.field.val
    let r' := residueAlgHomOfEmbedding k'.field.val
    change r' c = r (residue 𝒪[k.field] a) at hc
    calc
      aeval c p = 0 ↔ r' (aeval c p) = 0 := (map_eq_zero_iff r' r'.injective).symm
      _ ↔ r (aeval (residue 𝒪[k.field] a) p) = 0 := by
        rw [← aeval_algHom_apply r', ← aeval_algHom_apply r, hc]
      _ ↔ _ := map_eq_zero_iff r r.injective
  have hr : aeval c (f.map (residue 𝒪[F])) = 0 := (hm _).mpr (hred.symm ▸ minpoly.aeval _ _)
  have hs : aeval c (f.map (residue 𝒪[F])).derivative ≠ 0 := by
    rw [ne_eq, hm, hred]
    exact (Algebra.IsSeparable.isSeparable 𝓀[F] (residue 𝒪[k.field] a)).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  obtain ⟨a', ha', ha'c⟩ := lift_residue_root f hf c hr hs
  let e := finiteValuedEmbedding k.field.val
  let e' := finiteValuedEmbedding k'.field.val
  have hmapped (j : UnramifiedLevel F S) (x : 𝒪[j.field])
      (hx : (f.map (algebraMap 𝒪[F] 𝒪[j.field])).IsRoot x) :
      (f.map (algebraMap 𝒪[F] 𝒪[S])).IsRoot ((finiteValuedEmbedding j.field.val).integers x) := by
    let e := finiteValuedEmbedding j.field.val
    have he : e.integers.comp (algebraMap 𝒪[F] 𝒪[j.field]) = algebraMap 𝒪[F] 𝒪[S] :=
      RingHom.ext fun z => Subtype.ext (j.field.val.commutes (z : F))
    change (f.map (algebraMap 𝒪[F] 𝒪[S])).eval (e.integers x) = 0
    rw [eval_map, ← he, ← eval₂_map, eval₂_at_apply]
    exact (congrArg e.integers hx).trans (map_zero _)
  have hsame : residue 𝒪[S] (e.integers a) = residue 𝒪[S] (e'.integers a') := by
    change levelResidue k (residue 𝒪[k.field] a) = levelResidue k' (residue 𝒪[k'.field] a')
    rw [ha'c, hc]
  have heq : e.integers a = e'.integers a' := by
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (hmapped k a ha) (hmapped k' a' ha')
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hsame, sub_self]
    · apply (residue_ne_zero_iff_isUnit _).mp
      intro hz
      apply hs
      let ρ := residueAlgHomOfEmbedding k'.field.val
      apply ρ.injective
      change ρ (aeval c (f.map (residue 𝒪[F])).derivative) = ρ 0
      rw [map_zero, ← aeval_algHom_apply ρ]
      have hρ : ρ c = residue 𝒪[S] (e'.integers a') := by
        rw [← ha'c]
        rfl
      rw [hρ, ← hsame]
      have hmap : algebraMap 𝓀[F] 𝓀[S] = ResidueField.map (algebraMap 𝒪[F] 𝒪[S]) := rfl
      rw [derivative_map, aeval_def, eval₂_map, hmap, ResidueField.map_comp_residue,
        ← eval₂_map, eval₂_at_apply, ← derivative_map]
      exact hz
  change k.field ≤ k'.field
  rw [hK]
  apply IntermediateField.adjoin_le_iff.mpr
  apply Set.singleton_subset_iff.mpr
  have hx : ((a : k.field) : S) = ((a' : k'.field) : S) := congrArg Subtype.val heq
  rw [hx]
  exact (a' : k'.field).property

private theorem finite_level_residue_cover (K : IntermediateField F S) [FiniteDimensional F K] :
    ∃ k : UnramifiedLevel F S,
      let s := selectLocalStructure F K
      letI : ValuativeRel K := s.r
      letI : ValuativeExtension F K := s.extension
      Set.range (finiteValuedEmbedding K.val).residue ⊆ Set.range (levelResidue k) := by
  let s := selectLocalStructure F K
  letI : ValuativeRel K := s.r
  letI : TopologicalSpace K := s.top
  letI : ValuativeExtension F K := s.extension
  letI : IsNonarchimedeanLocalField K := s.localField
  obtain ⟨f, a, hf, ha, hred, htop⟩ := exists_residue_generator_lift (F := F) K
  obtain ⟨k, hk, _, hs⟩ := unramifiedSubfield_generated K f a hf ha hred htop
  refine ⟨k, ?_⟩
  change Set.range (finiteValuedEmbedding K.val).residue ⊆ Set.range (levelResidue k)
  rintro y ⟨x, rfl⟩
  obtain ⟨b, hb⟩ := hs x
  refine ⟨b, ?_⟩
  have he : K.val.comp (IntermediateField.inclusion hk) = k.field.val :=
    AlgHom.ext fun _ => rfl
  have h' := residue_comp_finite (IntermediateField.inclusion hk) K.val
  rw [he] at h'
  simpa only [RingHom.comp_apply, hb] using (DFunLike.congr_fun h' b).symm

private theorem directed_unramifiedLevels (k k' : UnramifiedLevel F S) :
    ∃ l, k ≤ l ∧ k' ≤ l := by
  let K := k.field ⊔ k'.field
  letI : FiniteDimensional F K := IntermediateField.finiteDimensional_sup k.field k'.field
  obtain ⟨l, hl⟩ := finite_level_residue_cover K
  let s := selectLocalStructure F K
  letI : ValuativeRel K := s.r
  letI : ValuativeExtension F K := s.extension
  refine ⟨l, level_le_of_residue_le k l ?_, level_le_of_residue_le k' l ?_⟩
  · intro x hx
    apply hl
    obtain ⟨b, rfl⟩ := hx
    let f := IntermediateField.inclusion (show k.field ≤ K from le_sup_left)
    exact ⟨(finiteValuedEmbedding f).residue b, DFunLike.congr_fun (residue_comp_finite f K.val) b⟩
  · intro x hx
    apply hl
    obtain ⟨b, rfl⟩ := hx
    let f := IntermediateField.inclusion (show k'.field ≤ K from le_sup_right)
    exact ⟨(finiteValuedEmbedding f).residue b, DFunLike.congr_fun (residue_comp_finite f K.val) b⟩

end DirectedResidues


section GeometricResidues

variable {F S : Type u} [Field F] [Field S] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel S] [ValuativeExtension F S] [Algebra.IsSeparable F S]

/-- Residue classes in the chosen separable closure have simultaneous
integral lifts in one finite intermediate field. -/
private theorem ambient_residue_finite_level {I : Type u} [Finite I] (x : I → 𝓀[S]) :
    ∃ k : UnramifiedLevel F S, ∀ i, x i ∈ Set.range (levelResidue k) := by
  classical
  choose a ha using fun i => residue_surjective (x i)
  let K := IntermediateField.adjoin F (Set.range fun i => (a i : S))
  letI : FiniteDimensional F K := IntermediateField.finiteDimensional_adjoin
    (fun b _ => Algebra.IsSeparable.isIntegral F b)
  let s := selectLocalStructure F K
  letI : ValuativeRel K := s.r
  letI : ValuativeExtension F K := s.extension
  obtain ⟨k, hk⟩ := finite_level_residue_cover K
  refine ⟨k, fun i => hk ?_⟩
  let ain : K := ⟨a i, IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  have hai : valuation K ain ≤ 1 := by
    rw [← (valuation K).map_one, ← valuativeEmbedding K.val, map_one, map_one]
    exact (a i).property
  let aint : 𝒪[K] := ⟨ain, hai⟩
  refine ⟨residue 𝒪[K] aint, ?_⟩
  change residue 𝒪[S] ((finiteValuedEmbedding K.val).integers aint) = x i
  exact (congrArg (residue 𝒪[S]) (Subtype.ext rfl)).trans (ha i)

private theorem ambient_residue_algebraic : Algebra.IsAlgebraic 𝓀[F] 𝓀[S] where
  isAlgebraic x := by
    obtain ⟨k, hk⟩ := ambient_residue_finite_level (F := F) (I := PUnit.{u + 1}) (fun _ => x)
    obtain ⟨y, hy⟩ := hk PUnit.unit
    exact hy ▸ IsAlgebraic.algHom (residueAlgHomOfEmbedding k.field.val)
      (Algebra.IsAlgebraic.isAlgebraic (R := 𝓀[F]) y)

private theorem valuationInteger_integrallyClosed (K : Type u) [Field K] [ValuativeRel K] :
    IsIntegrallyClosed 𝒪[K] :=
  (Subring.isIntegrallyClosed_iff (S := (valuation K).valuationSubring)).mpr
    (fun {_} hx => LocalSubring.mem_of_isMax_of_isIntegral
      (valuation K).valuationSubring.isMax_toLocalSubring hx)

private theorem ambient_residue_algClosed [IsSepClosed S]
    (hAlg : Algebra.IsAlgebraic 𝓀[F] 𝓀[S]) : IsAlgClosed 𝓀[S] := by
  letI := hAlg
  haveI : PerfectField 𝓀[S] := Algebra.IsAlgebraic.perfectField 𝓀[F]
  haveI : IsIntegrallyClosed 𝒪[S] := valuationInteger_integrallyClosed S
  apply IsAlgClosed.of_exists_root
  intro g hg hgi
  obtain ⟨f, hfg, _, hf⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts g).mpr (Polynomial.map_surjective _ residue_surjective g)) hg
  let fS := f.map (algebraMap 𝒪[S] S)
  have hi : Irreducible fS := (hf.irreducible_iff_irreducible_map_fraction_map (K := S)).mp
    (Polynomial.Monic.irreducible_of_irreducible_map (residue 𝒪[S]) f hf (hfg.symm ▸ hgi))
  have hsep : fS.Separable := (separable_iff_derivative_ne_zero hi).mpr (by
    intro h
    have hzero : f.derivative = 0 := (Polynomial.map_injective (algebraMap 𝒪[S] S)
      (IsFractionRing.injective 𝒪[S] S)) (by
        rw [← derivative_map, Polynomial.map_zero]
        exact h)
    have hd : g.derivative = 0 := by rw [← hfg, derivative_map, hzero, Polynomial.map_zero]
    exact (separable_iff_derivative_ne_zero hgi).mp (PerfectField.separable_of_irreducible hgi) hd)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root fS (degree_pos_of_irreducible hi).ne' hsep
  have hx' : aeval x f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hx
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff S).mp (inferInstance : IsIntegrallyClosed 𝒪[S])
    (show IsIntegral 𝒪[S] x from ⟨f, hf, hx'⟩)
  have hef : f.IsRoot a := by
    apply (IsFractionRing.injective 𝒪[S] S)
    rw [map_zero, ← eval₂_at_apply, ← aeval_def, ha]
    exact hx'
  refine ⟨residue 𝒪[S] a, ?_⟩
  rw [← hfg, eval_map, eval₂_at_apply, show f.eval a = 0 from hef, map_zero]

end GeometricResidues


section Assembly

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [FiniteDimensional F L] [IsGalois F L]

set_option maxHeartbeats 3500000 in
/-- The auxiliary fields, including possible inseparable root extensions,
and their actual coefficient and residue comparisons. -/
theorem ramifiedAuxiliaryTower : RamifiedAuxiliaryTower.{u} := by
  intro F L S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hdeg _ hram T d hd π hπ
  obtain ⟨rS, hvS⟩ := exists_ambient_valuation (F := F) (S := S)
  letI : ValuativeRel S := rS
  letI : ValuativeExtension F S := hvS
  have hAlg : Algebra.IsAlgebraic 𝓀[F] 𝓀[S] := ambient_residue_algebraic
  haveI : IsAlgClosure 𝓀[F] 𝓀[S] := ⟨ambient_residue_algClosed hAlg, hAlg⟩
  let e := IsAlgClosure.equiv 𝓀[F] 𝓀[S] (AlgebraicClosure 𝓀[F])
  obtain ⟨b, hb⟩ := exists_base_level (F := F) (S := S)
  let E := stageExtension T d hd π hπ
  let trans {k k' : UnramifiedLevel F S} (h : k ≤ k') := stageTransition T d hd π hπ h
  let r (k : UnramifiedLevel F S) : 𝓀[k.field] ≃+* 𝓀[(E k).field] :=
    RingEquiv.ofBijective ((residueMap (T k).field (E k).field).comp (coefficientResidue T k))
      ((E k).residue_bijective.comp (coefficientResidue_bijective T hdeg hram k))
  let emb (k : UnramifiedLevel F S) : 𝓀[(E k).field] →+* AlgebraicClosure 𝓀[F] :=
    (e.toRingHom.comp (levelResidue k)).comp (r k).symm.toRingHom
  refine ⟨{
    ramifiedResidue := (ExceptionalLocalRootCoordinates.ramifiedQuadratic F L hdeg hram).2.2
    base := b
    base_eq := hb
    directed := directed_unramifiedLevels
    extension := E
    transition := trans
    transition_diagram_id := ?_
    transition_diagram_comp := ?_
    transition_id := ?_
    transition_comp := ?_
    coefficientResidue_bijective := coefficientResidue_bijective T hdeg hram
    action := stageAction T d hd π hπ
    action_extends := stageAuto_diagram T d hd π hπ
    action_fixes_root := stageAuto_root T d hd π hπ
    actionValued := stageActionValued T d hd π hπ
    action_natural := fun h s s' => stageAuto_natural T d hd π hπ (UnramifiedLevel.inclusion h) s s'
    residueEmbedding := emb
    residue_base := ?_
    residue_compatible := ?_
    residue_exhaustive := ?_ }⟩
  · intro k
    exact compositumMap_id T
  · intro k k' k'' h h'
    exact compositumMap_comp T (UnramifiedLevel.inclusion h) (UnramifiedLevel.inclusion h')
  · intro k
    exact stageMap_id T d hd π hπ
  · intro k k' k'' h h'
    exact stageMap_comp T d hd π hπ (UnramifiedLevel.inclusion h) (UnramifiedLevel.inclusion h')
  · intro k
    apply RingHom.ext
    intro x
    change e (levelResidue k ((r k).symm ((r k) (residueMap F k.field x)))) = _
    rw [(r k).symm_apply_apply, show levelResidue k (residueMap F k.field x) = residueMap F S x
      from DFunLike.congr_fun (levelResidue_base k) x]
    exact e.commutes x
  · intro k k' h
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := (r k).surjective z
    have hdg := DFunLike.congr_fun (trans h).diagram_residue x
    have haux := DFunLike.congr_fun (trans h).auxiliary_residue (coefficientResidue T k x)
    have hv : (trans h).valued.residue (r k x) = r k' ((trans h).coefficient.residue x) := by
      change (trans h).valued.residue ((residueMap (T k).field (E k).field) (coefficientResidue T k x)) =
        (residueMap (T k').field (E k').field) (coefficientResidue T k' ((trans h).coefficient.residue x))
      change (trans h).valued.residue
        (residueMap (T k).field (E k).field (coefficientResidue T k x)) =
        residueMap (T k').field (E k').field ((trans h).diagramValued.residue (coefficientResidue T k x))
        at haux
      change (trans h).diagramValued.residue (coefficientResidue T k x) =
        coefficientResidue T k' ((trans h).coefficient.residue x) at hdg
      rw [haux, hdg]
    change e (levelResidue k' ((r k').symm ((trans h).valued.residue (r k x)))) =
      e (levelResidue k ((r k).symm (r k x)))
    rw [hv, (r k').symm_apply_apply, (r k).symm_apply_apply]
    exact congrArg e (DFunLike.congr_fun (levelResidue_compatible h) x)
  · intro I _ z
    obtain ⟨k, hk⟩ := ambient_residue_finite_level (F := F) (fun i => e.symm (z i))
    choose c hc using hk
    refine ⟨k, fun i => r k (c i), fun i => ?_⟩
    change e (levelResidue k ((r k).symm (r k (c i)))) = z i
    rw [(r k).symm_apply_apply, hc i, e.apply_symm_apply]

end Assembly


section ValuedFunctoriality

variable {K E N : Type u} [Field K] [Field E] [Field N]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel N]

private def idValued (K : Type u) [Field K] [ValuativeRel K] :
    ValuedFieldMap (RingHom.id K) where
  integers := RingHom.id _
  field_eq _ := rfl

private def compValued {f : K →+* E} {g : E →+* N}
    (w : ValuedFieldMap g) (v : ValuedFieldMap f) : ValuedFieldMap (g.comp f) where
  integers := w.integers.comp v.integers
  field_eq z := (w.field_eq (v.integers z)).trans (congrArg g (v.field_eq z))

private theorem integers_eq_of_field_eq {f g : K →+* E}
    (v : ValuedFieldMap f) (w : ValuedFieldMap g) (h : f = g) :
    v.integers = w.integers :=
  RingHom.ext fun x => Subtype.ext ((v.field_eq x).trans
    ((DFunLike.congr_fun h (x : K)).trans (w.field_eq x).symm))

private theorem residue_eq_of_field_eq {f g : K →+* E}
    (v : ValuedFieldMap f) (w : ValuedFieldMap g) (h : f = g) :
    v.residue = w.residue := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  exact congrArg (residue 𝒪[E]) (DFunLike.congr_fun (integers_eq_of_field_eq v w h) x)

end ValuedFunctoriality

set_option maxHeartbeats 2500000 in
/-- The selected field comparisons descend to compatible integral and
residue maps, with the induced coefficient actions. -/
theorem ramifiedAuxiliaryValuedCompatibility : RamifiedAuxiliaryValuedCompatibility.{u} := by
  intro F L S _ _ _ _ _ _ _ _ _ _ _ _ σ T d π P
  have hOne (k : UnramifiedLevel F S) : (P.action k 1).toRingHom = RingHom.id _ := by
    rw [map_one]
    rfl
  have hMul (k : UnramifiedLevel F S) (s t : Gal(k.field/F)) :
      (P.action k (s * t)).toRingHom = (P.action k s).toRingHom.comp (P.action k t).toRingHom :=
    congrArg RingEquiv.toRingHom ((P.action k).map_mul s t)
  have hDiagram {k k' : UnramifiedLevel F S} (h : k ≤ k') :
      (P.diagramResidueEmbedding k').comp (P.transition h).diagramValued.residue =
        P.diagramResidueEmbedding k := by
    unfold AuxiliaryTower.diagramResidueEmbedding
    rw [RingHom.comp_assoc, ← (P.transition h).auxiliary_residue,
      ← RingHom.comp_assoc, P.residue_compatible h]
  refine {
    integers_id := fun k => integers_eq_of_field_eq _ (idValued _) (P.transition_id k)
    integers_comp := fun h h' => integers_eq_of_field_eq _ (compValued _ _) (P.transition_comp h h')
    residue_id := fun k => (residue_eq_of_field_eq _ (idValued _) (P.transition_id k)).trans
      ResidueField.map_id
    residue_comp := fun h h' => (residue_eq_of_field_eq _ (compValued _ _) (P.transition_comp h h')).trans
      (ResidueField.map_comp _ _)
    integers_action_one := fun k => integers_eq_of_field_eq _ (idValued _) (hOne k)
    integers_action_mul := fun k s t => integers_eq_of_field_eq _ (compValued _ _) (hMul k s t)
    residue_action_one := fun k => (residue_eq_of_field_eq _ (idValued _) (hOne k)).trans ResidueField.map_id
    residue_action_mul := fun k s t => (residue_eq_of_field_eq _ (compValued _ _) (hMul k s t)).trans
      (ResidueField.map_comp _ _)
    integers_action_natural := fun h s s' hs => integers_eq_of_field_eq (compValued _ _) (compValued _ _)
      (RingHom.ext (P.action_natural h s s' hs))
    residue_action_natural := fun h s s' hs => residue_square _ _ _ _
      (RingHom.ext (P.action_natural h s s' hs))
    diagram_embedding_compatible := hDiagram
    coefficient_embedding_compatible := ?_ }
  intro k k' h
  unfold AuxiliaryTower.coefficientResidueEmbedding
  rw [RingHom.comp_assoc, ← (P.transition h).diagram_residue,
    ← RingHom.comp_assoc, hDiagram h]


end

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
