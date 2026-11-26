import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceCoefficientDepths

import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
namespace LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceCoefficientDepths

open LinearAlgebraicGroups.Specs
open Specs.RamifiedCongruenceCoefficientDepths
open ExceptionalLocalRootCoordinates (normalizedValuation normalizedValueGroupMap residueMap)
open ValuativeRel WithZero IsLocalRing
open scoped WithZero

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

noncomputable section

local notation "O(" K ")" => Valuation.valuationSubring (valuation K)
local notation "κ(" K ")" => IsLocalRing.ResidueField (O(K))

section NormalizedDepth

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
private theorem normalizedValuation_le_iff (a b : K) :
    normalizedValuation K a ≤ normalizedValuation K b ↔ valuation K a ≤ valuation K b :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

private theorem normalizedValuation_integer (a : (valuation K).valuationSubring) :
    normalizedValuation K (a : K) ≤ 1 := by
  rw [← (normalizedValuation K).map_one]
  exact (normalizedValuation_le_iff _ _).mpr (by
    rw [map_one]
    exact (Valuation.mem_valuationSubring_iff _ _).mp a.2)

private theorem normalizedValuation_uniformizer (π : (valuation K).valuationSubring)
    (hπ : (valuation K).IsUniformizer (π : K)) :
    normalizedValuation K (π : K) = exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hπlt : normalizedValuation K (π : K) < 1 := by
    change e (valuation K (π : K)) < 1
    simpa only [map_one] using e.strictMono hπ.val_lt_one
  obtain ⟨z, hz⟩ := valuation_surjective (e.symm (exp (-1 : ℤ)))
  have hz' : normalizedValuation K z = exp (-1 : ℤ) := by
    change e (valuation K z) = _
    rw [hz, e.apply_symm_apply]
  have hzlt : valuation K z < 1 := by
    have h : e (valuation K z) < e 1 := by
      change normalizedValuation K z < e 1
      rw [hz', map_one]
      simp
    exact e.toOrderIso.lt_iff_lt.mp h
  let a : (valuation K).valuationSubring := ⟨z, hzlt.le⟩
  have hamax : a ∈ maximalIdeal ((valuation K).valuationSubring) :=
    (Valuation.mem_maximalIdeal_iff (v := valuation K)).mpr hzlt
  obtain ⟨b, hb⟩ := (Ideal.mem_span_singleton.mp (hπ.is_generator ▸
    (show a ∈ maximalIdeal ((valuation K).valuationSubring) from hamax)) : π ∣ a)
  have hzb : z = (π : K) * (b : K) :=
    congrArg (fun x : (valuation K).valuationSubring => (x : K)) hb
  have hl : exp (-1 : ℤ) ≤ normalizedValuation K (π : K) := by
    rw [← hz', hzb, map_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedValuation_integer b)
      (zero_le : 0 ≤ normalizedValuation K (π : K))
  have hne : normalizedValuation K (π : K) ≠ 0 := (map_ne_zero _).mpr hπ.ne_zero
  have h₁ : (-1 : ℤ) ≤ log (normalizedValuation K (π : K)) :=
    (le_log_iff_exp_le hne).mpr hl
  have h₂ : log (normalizedValuation K (π : K)) < 0 :=
    (log_lt_iff_lt_exp hne).mpr (by simpa only [exp_zero] using hπlt)
  exact (exp_log hne).symm.trans (congrArg exp (by omega))

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra K E] [ValuativeExtension K E]

private theorem normalizedValuation_map (a : K) :
    normalizedValuation E (algebraMap K E a) =
      normalizedValueGroupMap K E (normalizedValuation K a) := by
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eE := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  change eE (valuation E (algebraMap K E a)) =
    eE (ValuativeExtension.mapValueGroupWithZero K E (eK.symm (eK (valuation K a))))
  rw [eK.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]

/-- Computing one uniformizer value determines restriction of normalized
valuations on the whole coefficient field. -/
private theorem normalizedValuation_extension_power (π : K) (hπ : normalizedValuation K π = exp (-1 : ℤ))
    (d : ℕ) (hd : 0 < d)
    (he : normalizedValuation E (algebraMap K E π) = exp (-(d : ℤ))) (a : K) :
    normalizedValuation E (algebraMap K E a) = normalizedValuation K a ^ d := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [zero_pow hd.ne']
  have ha' : normalizedValuation K a ≠ 0 := (map_ne_zero _).mpr ha
  let m := -log (normalizedValuation K a)
  have hpow : normalizedValuation K a = exp (-1 : ℤ) ^ m := by
    have hm : m • (-1 : ℤ) = log (normalizedValuation K a) := by
      simp [m]
    rw [← exp_zsmul, hm, exp_log ha']
  have hf := (normalizedValuation_map (E := E) π).symm.trans he
  rw [hπ] at hf
  rw [normalizedValuation_map, hpow, map_zpow₀, hf, ← exp_zsmul, ← exp_zsmul, ← exp_nsmul]
  congr 1
  simp only [zsmul_eq_mul, nsmul_eq_mul]
  ring

/-- An automorphism preserving the valuation ring and fixing the
uniformizer preserves all normalized depths. -/
private theorem normalizedValuation_fixed_uniformizer
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (σ : K ≃+* K) (hfix : σ (π : K) = π)
    (e : (valuation K).valuationSubring ≃+* (valuation K).valuationSubring)
    (he : ∀ b, (e b : K) = σ (b : K)) (z : K) :
    normalizedValuation K (σ z) = normalizedValuation K z := by
  let v := normalizedValuation K
  have hO (x : K) : σ x ∈ (valuation K).valuationSubring ↔ x ∈ (valuation K).valuationSubring := by
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := e.surjective ⟨σ x, hx⟩
      have hh : σ (b : K) = σ x :=
        (he b).symm.trans (congrArg (fun z : (valuation K).valuationSubring => (z : K)) hb)
      exact ((σ.injective hh) ▸ b.2)
    · intro hx
      exact (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).2
  have hv (x : K) (m : ℤ) : v x ≤ exp m ↔ x / (π : K) ^ (-m) ∈ (valuation K).valuationSubring := by
    have hp : v ((π : K) ^ (-m)) = exp m := by
      rw [map_zpow₀, normalizedValuation_uniformizer π hπ, ← exp_zsmul]
      congr 1
      simp
    have hnn : 0 < v ((π : K) ^ (-m)) := by rw [hp]; exact exp_pos
    calc
      v x ≤ exp m ↔ v (x / (π : K) ^ (-m)) ≤ 1 := by rw [map_div₀, div_le_one₀ hnn, hp]
      _ ↔ x / (π : K) ^ (-m) ∈ (valuation K).valuationSubring := by
        rw [Valuation.mem_valuationSubring_iff, ← (valuation K).map_one,
          ← normalizedValuation_le_iff, map_one]
  have hbound (m : ℤ) : v (σ z) ≤ exp m ↔ v z ≤ exp m := by
    rw [hv, hv]
    simpa only [map_div₀, map_zpow₀, hfix] using hO (z / (π : K) ^ (-m))
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz₁ : v z ≠ 0 := (map_ne_zero _).mpr hz
  have hz₂ : v (σ z) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr hz)
  have hl := hbound (log (v z))
  have hr := hbound (log (v (σ z)))
  rw [exp_log hz₁] at hl
  rw [exp_log hz₂] at hr
  exact le_antisymm (hl.mpr le_rfl) (hr.mp le_rfl)

private theorem integer_iff (x : K) :
    valuation K x ≤ 1 ↔ normalizedValuation K x ≤ 1 := by
  rw [← (normalizedValuation K).map_one, normalizedValuation_le_iff, map_one]

private theorem normalizedValuation_lt_one_iff (x : K) :
    normalizedValuation K x < 1 ↔ valuation K x < 1 := by
  rw [lt_iff_not_ge, lt_iff_not_ge, ← (normalizedValuation K).map_one,
    normalizedValuation_le_iff, map_one]

private theorem normalizedUnit (a : O(K)ˣ) :
    normalizedValuation K ((a : O(K)) : K) = 1 := by
  have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.valuationSubring.integers (valuation K))).mp a.isUnit
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K _) = 1
  change valuation K ((a : O(K)) : K) = 1 at h
  rw [h, map_one]

private theorem isUnit_ofValueOne (a : K) (ha : normalizedValuation K a = 1) :
    IsUnit (⟨a, (integer_iff a).mpr ha.le⟩ : O(K)) := by
  apply (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.valuationSubring.integers (valuation K))).mpr
  change valuation K a = 1
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply iso.injective
  rw [map_one]
  exact ha

private def unitOfValueOne (a : K) (ha : normalizedValuation K a = 1) : O(K)ˣ :=
  (isUnit_ofValueOne a ha).unit

private theorem coe_unitOfValueOne (a : K) (ha : normalizedValuation K a = 1) :
    ((unitOfValueOne a ha : O(K)) : K) = a :=
  congrArg (fun z : O(K) => (z : K)) (isUnit_ofValueOne a ha).unit_spec

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem coe_zpow (w : O(K)ˣ) (m : ℤ) :
    (((w ^ m : O(K)ˣ) : O(K)) : K) = (((w : O(K)) : K) ^ m) := by
  let i := (valuation K).valuationSubring.subtype.toMonoidHom
  change ((Units.map i (w ^ m) : Kˣ) : K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem exp_depth (x : K) (hx : x ≠ 0) :
    ∃ m : ℤ, normalizedValuation K x = exp (-m) := by
  refine ⟨-log (normalizedValuation K x), ?_⟩
  rw [neg_neg, exp_log ((map_ne_zero _).mpr hx)]

private theorem uniformizer_zpow (ξ : K)
    (hξ : normalizedValuation K ξ = exp (-1 : ℤ)) (m : ℤ) :
    normalizedValuation K (ξ ^ m) = exp (-m) := by
  rw [map_zpow₀, hξ, ← exp_zsmul]
  simp

private theorem uniformizer_pow (ξ : K)
    (hξ : normalizedValuation K ξ = exp (-1 : ℤ)) (n : ℕ) :
    normalizedValuation K (ξ ^ n) = exp (-(n : ℤ)) := by
  simpa only [zpow_natCast] using uniformizer_zpow ξ hξ (n : ℤ)

private theorem factor_at_depth (ξ : O(K)) (hξ : (valuation K).IsUniformizer (ξ : K))
    (n : ℕ) (z : K) :
    AtDepth n z ↔ ∃ w : O(K), z = (ξ : K) ^ n * (w : K) := by
  have hspan : maximalIdeal O(K) ^ n = Ideal.span {ξ ^ n} := by
    rw [hξ.is_generator, Ideal.span_singleton_pow]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hspan, Ideal.mem_span_singleton] at ha
    obtain ⟨w, hw⟩ := ha
    exact ⟨w, congrArg (fun a : O(K) => (a : K)) hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨ξ ^ n * w, by rw [hspan, Ideal.mem_span_singleton]; exact dvd_mul_right _ _, rfl⟩

private theorem leading_iff_at_depth (ξ : O(K)) (hξ : (valuation K).IsUniformizer (ξ : K))
    (n : ℕ) (z : K) :
    AtDepth n z ↔ ∃ r, IsLeading ξ n z r := by
  rw [factor_at_depth ξ hξ]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨residue _ w, w, hw, rfl⟩
  · rintro ⟨_, w, hw, _⟩
    exact ⟨w, hw⟩

private theorem at_depth_iff (ξ : O(K)) (hξ : (valuation K).IsUniformizer (ξ : K))
    (n : ℕ) (z : K) :
    AtDepth n z ↔ normalizedValuation K z ≤ exp (-(n : ℤ)) := by
  rw [factor_at_depth ξ hξ, ← uniformizer_pow _ (normalizedValuation_uniformizer ξ hξ)]
  have hp : (ξ : K) ^ n ≠ 0 := pow_ne_zero n hξ.ne_zero
  constructor
  · rintro ⟨w, rfl⟩
    rw [map_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedValuation_integer w)
      (zero_le : 0 ≤ normalizedValuation K ((ξ : K) ^ n))
  · intro hz
    have hw : valuation K (z / (ξ : K) ^ n) ≤ 1 := by
      apply (integer_iff _).mpr
      rwa [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hp))]
    exact ⟨⟨_, hw⟩, (mul_div_cancel₀ z hp).symm⟩

private theorem leading_unique (ξ : O(K)) (hξ : (valuation K).IsUniformizer (ξ : K))
    {n : ℕ} {z : K} {r t : κ(K)} (hr : IsLeading ξ n z r) (ht : IsLeading ξ n z t) : r = t := by
  obtain ⟨b, hb, rfl⟩ := hr
  obtain ⟨c, hc, rfl⟩ := ht
  have h : b = c := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n hξ.ne_zero) (hb.symm.trans hc))
  rw [h]

private theorem leading_zero (ξ : O(K)) (hξ : (valuation K).IsUniformizer (ξ : K))
    {n : ℕ} {z : K} (h : normalizedValuation K z < exp (-(n : ℤ))) :
    IsLeading ξ n z 0 := by
  obtain ⟨b, hb⟩ := (factor_at_depth ξ hξ n z).mp ((at_depth_iff ξ hξ n z).mpr h.le)
  refine ⟨b, hb, (residue_eq_zero_iff _).mpr ((Valuation.mem_maximalIdeal_iff (v := valuation K)).mpr ?_)⟩
  apply (normalizedValuation_lt_one_iff _).mp
  rw [hb, map_mul, uniformizer_pow _ (normalizedValuation_uniformizer ξ hξ)] at h
  apply (mul_lt_mul_iff_right₀ (a := exp (-(n : ℤ))) exp_pos).mp
  simpa only [mul_one] using h

private theorem near_one {a : K} (ha : normalizedValuation K a < 1) :
    ∃ t : O(K)ˣ, ((t : O(K)) : K) - 1 = a := by
  let v := normalizedValuation K
  have h : v (1 + a) = 1 := v.map_one_add_of_lt ha
  exact ⟨unitOfValueOne (1 + a) h, by rw [coe_unitOfValueOne]; ring⟩

end NormalizedDepth

section Quadratic

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  [ValuativeRel k] [ValuativeRel K] [TopologicalSpace k] [TopologicalSpace K]
  [IsNonarchimedeanLocalField k] [IsNonarchimedeanLocalField K]
  [finite : FiniteDimensional k K] [galois : IsGalois k K]

include finite galois in
private theorem quadratic_valuation (degree : Module.finrank k K = 2)
    (τ : Gal(K/k)) (hτ : τ ≠ 1)
    (hbase : ∀ a : k, normalizedValuation K (algebraMap k K a) = normalizedValuation k a ^ 2)
    (π : K) (hπ : normalizedValuation K π = exp (-1 : ℤ)) (a : K) :
    normalizedValuation K (τ a) = normalizedValuation K a := by
  classical
  let v := normalizedValuation K
  have hc : Nat.card Gal(K/k) = 2 := (IsGalois.card_aut_eq_finrank k K).trans degree
  have hτ₂ : Function.Involutive τ := by
    have h : τ ^ 2 = 1 := hc ▸ pow_card_eq_one' (x := τ)
    intro x
    simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using
      congrArg (fun g : Gal(K/k) => g x) h
  have range_of_fixed (x : K) (hx : τ x = x) : x ∈ Set.range (algebraMap k K) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (E := K) x).mpr
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · obtain ⟨t, _, ht⟩ := (Nat.card_eq_two_iff' (1 : Gal(K/k))).mp hc
      rw [(ht g hg).trans (ht τ hτ).symm]
      exact hx
  have even_exponent {x : K} {m : ℤ} (hx : x ∈ Set.range (algebraMap k K))
      (h : v x = exp m) : ∃ j : ℤ, m = 2 * j := by
    obtain ⟨b, rfl⟩ := hx
    have hb : b ≠ 0 := by
      rintro rfl
      simp only [map_zero] at h
      exact exp_ne_zero h.symm
    obtain ⟨j, hj⟩ := exp_depth b hb
    refine ⟨-j, exp_injective ?_⟩
    rw [← h, hbase, hj, ← exp_nsmul]
    congr 1
  have hπ₀ : π ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hπ_not_base : π ∉ Set.range (algebraMap k K) := by
    intro h
    obtain ⟨j, hj⟩ := even_exponent h hπ
    omega
  have hτπ : v (τ π) = v π := by
    obtain ⟨m, hm⟩ := exp_depth (τ π) ((map_ne_zero τ).mpr hπ₀)
    have hprod : π * τ π ∈ Set.range (algebraMap k K) :=
      range_of_fixed _ (by rw [map_mul, hτ₂, mul_comm])
    have hp : v (π * τ π) = exp (-1 + -m : ℤ) := by
      rw [map_mul, hπ, hm, exp_add]
    obtain ⟨j, hj⟩ := even_exponent hprod hp
    have hs : π + τ π ∈ Set.range (algebraMap k K) :=
      range_of_fixed _ (by rw [map_add, hτ₂, add_comm])
    rcases lt_trichotomy (v (τ π)) (v π) with h | h | h
    · have hsum := (v.map_add_eq_of_lt_left h).trans hπ
      obtain ⟨i, hi⟩ := even_exponent hs hsum
      omega
    · exact h
    · have hsum := (v.map_add_eq_of_lt_right h).trans hm
      obtain ⟨i, hi⟩ := even_exponent hs hsum
      omega
  let f : Fin 2 → K := ![π, 1]
  have hf : LinearIndependent k f := by
    refine linearIndependent_fin2.mpr ⟨one_ne_zero, ?_⟩
    intro b hb
    exact hπ_not_base ⟨b, by simpa [f, Algebra.smul_def] using hb⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hf (by simpa using degree.symm)
  have hB : (B : Fin 2 → K) = f := coe_basisOfLinearIndependentOfCardEqFinrank hf _
  let b := B.repr a 1
  let c := B.repr a 0
  have ha : a = algebraMap k K b + algebraMap k K c * π := by
    have h := B.sum_repr a
    rw [Fin.sum_univ_two] at h
    have h0 : B 0 = π := congrFun hB 0
    have h1 : B 1 = 1 := congrFun hB 1
    rw [h0, h1] at h
    rw [← h]
    change c • π + b • (1 : K) = algebraMap k K b + algebraMap k K c * π
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, add_comm]
  have hb : v (algebraMap k K b) ≠ v (algebraMap k K c * π) ∨ (b = 0 ∧ c = 0) := by
    by_cases hb : b = 0
    · by_cases hcz : c = 0
      · exact Or.inr ⟨hb, hcz⟩
      · left
        rw [hb, map_zero, map_zero]
        exact ((map_ne_zero v).mpr (mul_ne_zero ((map_ne_zero _).mpr hcz) hπ₀)).symm
    · left
      intro h
      by_cases hcz : c = 0
      · rw [hcz, map_zero, zero_mul, map_zero] at h
        exact ((map_ne_zero v).mpr ((map_ne_zero _).mpr hb)) h
      · obtain ⟨j, hj⟩ := exp_depth c hcz
        have hv : v (algebraMap k K b) = exp ((2 : ℤ) * -j - 1) := by
          rw [h, map_mul, hbase, hj, hπ, ← exp_nsmul, ← exp_add]
          congr 1
        obtain ⟨i, hi⟩ := even_exponent ⟨b, rfl⟩ hv
        omega
  have hmul : v (algebraMap k K c * τ π) = v (algebraMap k K c * π) := by
    rw [map_mul, map_mul, hτπ]
  rw [ha, map_add τ, map_mul τ, AlgEquiv.commutes, AlgEquiv.commutes]
  rcases hb with hb | ⟨hb, hc⟩
  · rcases lt_or_gt_of_ne hb with h | h
    · rw [v.map_add_eq_of_lt_right (hmul.symm ▸ h), v.map_add_eq_of_lt_right h, hmul]
    · rw [v.map_add_eq_of_lt_left (hmul.symm ▸ h), v.map_add_eq_of_lt_left h]
  · simp [hb, hc]

end Quadratic

section Residues

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]

private def residueEquiv (h : Nat.card κ(K) = Nat.card κ(E)) : κ(K) ≃+* κ(E) := by
  letI : Finite κ(E) := inferInstanceAs (Finite (IsLocalRing.ResidueField ((valuation E).integer)))
  exact RingEquiv.ofBijective (residueMap K E)
    ((Nat.bijective_iff_injective_and_card (residueMap K E)).mpr ⟨(residueMap K E).injective, h⟩)

private def restrictIntegers (τ : K ≃+* K)
    (hτ : ∀ a, normalizedValuation K (τ a) = normalizedValuation K a) : O(K) ≃+* O(K) where
  toFun a := ⟨τ a, (integer_iff _).mpr ((hτ _).trans_le (normalizedValuation_integer a))⟩
  invFun a := ⟨τ.symm a, (integer_iff _).mpr (by
    rw [← hτ (τ.symm a), τ.apply_symm_apply]
    exact normalizedValuation_integer a)⟩
  left_inv a := Subtype.ext (τ.symm_apply_apply a)
  right_inv a := Subtype.ext (τ.apply_symm_apply a)
  map_mul' a b := Subtype.ext (map_mul τ (a : K) (b : K))
  map_add' a b := Subtype.ext (map_add τ (a : K) (b : K))

omit [TopologicalSpace K] [TopologicalSpace E] [IsNonarchimedeanLocalField K]
  [IsNonarchimedeanLocalField E] in
private theorem restriction_residue_fixed (τ : O(E) ≃+* O(E))
    (hτ : ∀ a : O(K), τ (algebraMap O(K) O(E) a) = algebraMap O(K) O(E) a)
    (hsurj : Function.Surjective (residueMap K E)) (b : O(E)) :
    IsLocalRing.residue _ (τ b) = IsLocalRing.residue _ b := by
  obtain ⟨r, hr⟩ := hsurj (IsLocalRing.residue _ b)
  obtain ⟨a, rfl⟩ := residue_surjective r
  change IsLocalRing.residue _ (algebraMap O(K) O(E) a) = IsLocalRing.residue _ b at hr
  have hh := congrArg (reduceAutomorphism τ) hr
  change IsLocalRing.residue _ (τ (algebraMap O(K) O(E) a)) = IsLocalRing.residue _ (τ b) at hh
  rw [hτ, hr] at hh
  exact hh.symm

end Residues

section Coefficients

variable {P E : Type*} [Field P] [Field E]
  [ValuativeRel P] [ValuativeRel E] [TopologicalSpace P] [TopologicalSpace E]
  [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField E]

private theorem scaled_value
    (f : P →+* E) (e : ℕ)
    (hval : ∀ a, normalizedValuation E (f a) = normalizedValuation P a ^ e)
    (ξ : O(E)) (hξ : (valuation E).IsUniformizer (ξ : E))
    (s : ℤ) (c : O(E)ˣ) (a : P) (m : ℤ) (ha : normalizedValuation P a = exp (-m)) :
    normalizedValuation E (scaledEntry f ξ s c a) = exp (-(s + (e : ℤ) * m)) := by
  rw [scaledEntry, map_mul, map_mul, uniformizer_zpow _ (normalizedValuation_uniformizer ξ hξ),
    normalizedUnit, mul_one, hval, ha, ← exp_nsmul, ← exp_add]
  congr 1
  ring

omit [TopologicalSpace P] [TopologicalSpace E] [IsNonarchimedeanLocalField P]
  [IsNonarchimedeanLocalField E] in
private theorem scale_product
    (f : P →+* E) (f₀ : O(P) →+* O(E))
    (hf₀ : ∀ b, (f₀ b : E) = f (b : P))
    (ξ : O(E)) (hξ : (ξ : E) ≠ 0) {e n : ℕ} {s m : ℤ}
    (hn : (n : ℤ) = s + (e : ℤ) * m)
    (c δ : O(E)ˣ) (π : P) (hπ : f π = (ξ : E) ^ e * ((δ : O(E)) : E))
    (b : O(P)) :
    scaledEntry f ξ s c (π ^ m * (b : P)) =
      (ξ : E) ^ n * ((((c * δ ^ m : O(E)ˣ) : O(E)) * f₀ b : O(E)) : E) := by
  have hs : (ξ : E) ^ n = (ξ : E) ^ s * (((ξ : E) ^ e) ^ m) := by
    rw [← zpow_natCast, hn, zpow_add₀ hξ, zpow_mul, zpow_natCast]
  rw [scaledEntry, map_mul f, map_zpow₀ f, hπ, mul_zpow, hs]
  change _ = _ * (((c : O(E)) : E) * (((δ ^ m : O(E)ˣ) : O(E)) : E) * (f₀ b : E))
  rw [coe_zpow, hf₀]
  ring

private theorem single_slot
    (f : P →+* E) (f₀ : O(P) →+* O(E))
    (hf₀ : ∀ b, (f₀ b : E) = f (b : P))
    (ρ : κ(P) →+* κ(E)) (hres : Function.Surjective ρ)
    (hρ : ∀ b, ρ (residue _ b) = residue _ (f₀ b))
    {e n : ℕ} (he : 0 < e) (hn : 0 < n)
    (hval : ∀ a, normalizedValuation E (f a) = normalizedValuation P a ^ e)
    (ξ : O(E)) (hξ : (valuation E).IsUniformizer (ξ : E)) (s : ℤ) (c : O(E)ˣ) :
    SingleSlot f ξ e n s c := by
  have hdepth := scaled_value f e hval ξ hξ s c
  refine ⟨hdepth, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨r, hr⟩ := (leading_iff_at_depth ξ hξ _ _).mp ha
    exact ⟨r, hr, fun t ht => leading_unique ξ hξ ht hr⟩
  · intro hnot a ha
    apply leading_zero ξ hξ
    rcases eq_or_ne a 0 with rfl | ha₀
    · simp [scaledEntry]
    · obtain ⟨m, hm⟩ := exp_depth a ha₀
      have hle := (at_depth_iff ξ hξ n _).mp ha
      rw [hdepth a m hm, exp_le_exp] at hle
      rw [hdepth a m hm, exp_lt_exp]
      have hne : (n : ℤ) ≠ s + (e : ℤ) * m := fun h => hnot ⟨m, h⟩
      omega
  · intro m hm r
    by_cases hr : r = 0
    · subst r
      refine ⟨0, ⟨0, by simp [scaledEntry], map_zero _⟩, fun _ => rfl,
        fun h => (h rfl).elim, fun _ => near_one (by simp)⟩
    let v := normalizedValuation P
    let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt P
    obtain ⟨π, hπ⟩ := valuation_surjective (iso.symm (exp (-1 : ℤ)))
    have hπv : v π = exp (-1 : ℤ) := by
      change iso (valuation P π) = _
      rw [hπ, iso.apply_symm_apply]
    have hratio : normalizedValuation E (f π / (ξ : E) ^ e) = 1 := by
      rw [map_div₀, hval, hπv, uniformizer_pow _ (normalizedValuation_uniformizer ξ hξ),
        ← exp_nsmul]
      simp [exp_ne_zero]
    let δ := unitOfValueOne _ hratio
    have hπf : f π = (ξ : E) ^ e * ((δ : O(E)) : E) := by
      rw [coe_unitOfValueOne, mul_div_cancel₀ _ (pow_ne_zero _ hξ.ne_zero)]
    let C := Units.map (residue O(E)).toMonoidHom (c * δ ^ m)
    obtain ⟨t, ht⟩ := hres ((↑C : κ(E))⁻¹ * r)
    obtain ⟨b, rfl⟩ := residue_surjective t
    have hred : residue O(E) (((c * δ ^ m : O(E)ˣ) : O(E)) * f₀ b) = r := by
      rw [map_mul]
      change (↑C : κ(E)) * residue _ (f₀ b) = r
      rw [← hρ, ht, ← mul_assoc, mul_inv_cancel₀ C.ne_zero, one_mul]
    have hb_unit : IsUnit b := by
      apply (residue_ne_zero_iff_isUnit _).mp
      intro hb0
      have hz : residue O(E) (f₀ b) = 0 := by rw [← hρ, hb0, map_zero]
      exact hr (by simpa [map_mul, hz] using hred.symm)
    have hb_val : v (b : P) = 1 := by
      obtain ⟨w, rfl⟩ := hb_unit
      exact normalizedUnit w
    let a := π ^ m * (b : P)
    have hav : v a = exp (-m) := by
      change v (π ^ m * (b : P)) = _
      rw [map_mul, uniformizer_zpow π hπv, hb_val, mul_one]
    refine ⟨a, ⟨_, scale_product f f₀ hf₀ ξ hξ.ne_zero hm c δ π hπf b, hred⟩,
      fun h => (hr h).elim, fun _ => hav, ?_⟩
    intro hs
    have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
    have he' : 0 < (e : ℤ) := by exact_mod_cast he
    have hm' : 0 < m := by
      rw [hs, zero_add] at hm
      by_contra h
      have hle : (e : ℤ) * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he'.le (le_of_not_gt h)
      omega
    exact near_one (hav ▸ exp_lt_one_iff.mpr (by omega))

end Coefficients

section Pair

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]

private theorem paired_slots (τ : K ≃+* K) (τ₀ : O(K) ≃+* O(K))
    (hτ : ∀ a, normalizedValuation K (τ a) = normalizedValuation K a)
    (hτ₀ : ∀ b, (τ₀ b : K) = τ (b : K))
    (hτκ : ∀ b, residue _ (τ₀ b) = residue _ b)
    (π : K) (hπ : normalizedValuation K π = exp (-1 : ℤ))
    (ε : O(K)ˣ) (hε : τ π = ((ε : O(K)) : K) * π)
    {d n : ℕ} (hd : 0 < d)
    (hval : ∀ a, normalizedValuation E (algebraMap K E a) = normalizedValuation K a ^ d)
    (ξ : O(E)) (hξ : (valuation E).IsUniformizer (ξ : E))
    (hpower : (ξ : E) ^ d = algebraMap K E π)
    (s : ℤ) (c₁ c₂ : O(E)ˣ) (h₁ : SingleSlot (algebraMap K E) ξ d n s c₁)
    (h₂ : SingleSlot (algebraMap K E) ξ d n s c₂) :
    PairedSlots τ ξ ε d n s c₁ c₂ := by
  let f := algebraMap K E
  let f₀ := algebraMap O(K) O(E)
  let v := normalizedValuation K
  let z₁ := scaledEntry f ξ s c₁
  let z₂ := scaledEntry f ξ s c₂
  have hv₂ (a : K) : normalizedValuation E (z₂ (τ a)) = normalizedValuation E (z₁ a) := by
    change normalizedValuation E (scaledEntry f ξ s c₂ (τ a)) =
      normalizedValuation E (scaledEntry f ξ s c₁ a)
    simp only [scaledEntry, map_mul, normalizedUnit, mul_one, f, hval, hτ]
  have hπ₀ : π ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  change (∀ a m, v a = exp (-m) → _) ∧ _ ∧ _
  refine ⟨fun a m ha => ⟨h₁.1 a m ha, (hv₂ a).trans (h₁.1 a m ha)⟩, ?_, ?_⟩
  · intro hinactive a ha
    have hb : AtDepth n (z₂ (τ a)) := by
      apply (at_depth_iff ξ hξ _ _).mpr
      rw [hv₂]
      exact (at_depth_iff ξ hξ _ _).mp ha
    exact ⟨h₁.2.2.1 hinactive a ha, h₂.2.2.1 hinactive (τ a) hb⟩
  · intro m hm
    have compare (a : K) (r : κ(E)) (hr : IsLeading ξ n (z₁ a) r) :
        IsLeading ξ n (z₂ (τ a)) ((pairedFactor c₁ c₂ ε m : κ(E)) * r) := by
      have hle : v a ≤ exp (-m) := by
        rcases eq_or_ne a 0 with rfl | ha
        · simp only [v, map_zero, zero_le]
        obtain ⟨j, hj⟩ := exp_depth a ha
        have h := (at_depth_iff ξ hξ _ _).mp
          ((leading_iff_at_depth ξ hξ _ _).mpr ⟨r, hr⟩)
        change normalizedValuation E (scaledEntry (algebraMap K E) ξ s c₁ a) ≤ _ at h
        rw [h₁.1 a j hj, exp_le_exp, hm] at h
        have hd' : 0 < (d : ℤ) := by exact_mod_cast hd
        have hmul : (d : ℤ) * m ≤ (d : ℤ) * j := by linarith
        have hjm := (mul_le_mul_iff_of_pos_left hd').mp hmul
        rw [hj, exp_le_exp]
        omega
      have hb : valuation K (a / π ^ m) ≤ 1 := by
        apply (integer_iff _).mpr
        rw [map_div₀, uniformizer_zpow π hπ, div_le_one₀ exp_pos]
        exact hle
      let b : O(K) := ⟨a / π ^ m, hb⟩
      have ha : a = π ^ m * (b : K) := (mul_div_cancel₀ a (zpow_ne_zero m hπ₀)).symm
      let δ := Units.map f₀.toMonoidHom ε
      have h₁π : f π = (ξ : E) ^ d * (((1 : O(E)ˣ) : O(E)) : E) := by
        simpa using hpower.symm
      have h₂π : (f.comp τ.toRingHom) π = (ξ : E) ^ d * ((δ : O(E)) : E) := by
        change f (τ π) = _ * f ((ε : O(K)) : K)
        rw [hε, map_mul, hpower]
        exact mul_comm _ _
      let b₁ : O(E) := (c₁ : O(E)) * f₀ b
      let b₂ : O(E) := ((c₂ * δ ^ m : O(E)ˣ) : O(E)) * f₀ (τ₀ b)
      have hb₁ : z₁ a = (ξ : E) ^ n * (b₁ : E) := by
        rw [ha]
        simpa only [one_zpow, mul_one, z₁, b₁] using
          scale_product f f₀ (fun _ => rfl) ξ hξ.ne_zero hm c₁ 1 π h₁π b
      have hb₂ : z₂ (τ a) = (ξ : E) ^ n * (b₂ : E) := by
        rw [ha]
        exact scale_product (f.comp τ.toRingHom) (f₀.comp τ₀.toRingHom)
          (fun w => congrArg f (hτ₀ w)) ξ hξ.ne_zero hm c₂ δ π h₂π b
      have hr₁ := leading_unique ξ hξ hr (show IsLeading ξ n (z₁ a) (residue _ b₁) from
        ⟨b₁, hb₁, rfl⟩)
      have hred : residue _ (f₀ (τ₀ b)) = residue _ (f₀ b) := by
        simpa only [f₀, ResidueField.algebraMap_residue] using
          congrArg (residueMap K E) (hτκ b)
      refine ⟨b₂, hb₂, ?_⟩
      rw [hr₁]
      let r₁ := Units.map (residue O(E)).toMonoidHom c₁
      let r₂ := Units.map (residue O(E)).toMonoidHom c₂
      let rδ := Units.map (residue O(E)).toMonoidHom δ
      have hfactor : pairedFactor c₁ c₂ ε m = r₂ * r₁⁻¹ * rδ ^ m := rfl
      rw [hfactor]
      have hred₂ : residue O(E) b₂ =
          (↑(r₂ * rδ ^ m) : κ(E)) * residue O(E) (f₀ b) := by
        simp only [b₂, map_mul, ← hred]
        rw [hred]
        change (↑(Units.map (residue O(E)).toMonoidHom (c₂ * δ ^ m)) : κ(E)) * _ = _
        rw [map_mul, map_zpow]
      rw [hred₂]
      change (↑(r₂ * rδ ^ m) : κ(E)) * _ = ↑(r₂ * r₁⁻¹ * rδ ^ m) * residue O(E) b₁
      rw [show residue O(E) b₁ = ↑r₁ * residue O(E) (f₀ b) from map_mul _ _ _]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp [r₁.ne_zero]
    refine ⟨compare, ?_⟩
    intro r
    obtain ⟨a, ha, _⟩ := h₁.2.2.2 m hm r
    exact ⟨a, ha, compare a r ha⟩

end Pair

open ExceptionalAffineBruhat

theorem ramifiedCoefficientDepths_conditional.{u}
    (_coxeter : CoxeterDoubleCosets.{u, u, u})
    (_coweight : E6CoweightClass)
    (_projected : E6ProjectedLattices)
    (_index : LeftCosetIndex.{u})
    (_ramified : RamifiedAffineBruhatComparison.{u})
    (_product : RankOneDoubleCosetProduct.{u})
    (_conjugation : RankOneWallConjugation.{u})
    (_multiplication : RankOneWallMultiplication.{u})
    (_layers : ResidueLayerCounts.{u})
    (_powers : ResiduePowerCounts.{u})
    (_split : SplitAffineBruhatComparison.{u}) :
    RamifiedCoefficientDepths.{u} := by
  unfold RamifiedCoefficientDepths
  intro F L k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ σ _ _ _ D M R T A X S galResidue hgal
  dsimp only
  let π := algebraMap L T.field (S.uniformizer : L)
  have hπ : normalizedValuation T.field π = exp (-1 : ℤ) :=
    (T.unramified _).trans S.uniformizer_value
  have hE (a : T.field) :
      normalizedValuation S.E (algebraMap T.field S.E a) = normalizedValuation T.field a ^ S.d := by
    apply normalizedValuation_extension_power π hπ S.d S.d_pos _ a
    change normalizedValuation S.E
      (algebraMap T.field S.E (algebraMap L T.field (S.uniformizer : L))) = _
    rw [← S.xi_power, uniformizer_pow _ (normalizedValuation_uniformizer S.xi S.xi_uniformizer)]
  have hk (a : k) :
      normalizedValuation S.E (algebraMap T.field S.E (algebraMap k T.field a)) =
        normalizedValuation k a ^ (2 * S.d) := by
    rw [hE, X.ramification, pow_mul]
  have hτ := quadratic_valuation T.degree T.diagram T.diagram_ne X.ramification π hπ
  let τ₀ := restrictIntegers T.diagram.toRingEquiv hτ
  have hτ₀ (a : O(T.field)) : (τ₀ a : T.field) = T.diagram (a : T.field) := rfl
  let i := residueEquiv (K := k) (E := T.field) X.same_residue.symm
  let j := residueEquiv (K := T.field) (E := S.E) S.unchanged_residue.symm
  have hτκ (a : O(T.field)) : residue _ (τ₀ a) = residue _ a := by
    apply restriction_residue_fixed (K := k) τ₀ _ i.surjective a
    intro b
    apply Subtype.ext
    change T.diagram (algebraMap k T.field (b : k)) = algebraMap k T.field (b : k)
    exact T.diagram.commutes (b : k)
  refine ⟨hE, hk, hτ, ⟨τ₀, hτ₀, hτκ⟩, ⟨i, j, rfl, rfl, ?_⟩, ?_⟩
  · intro g r
    obtain ⟨z, rfl⟩ := residue_surjective r
    let f := algebraMap T.field S.E
    let e := algebraMap k T.field
    have hcoeff (a : k) : S.coefficient g (f (e a)) = f (e (g a)) := by
      rw [S.coefficient_extends, T.coefficient_extends]
    have hgE := normalizedValuation_fixed_uniformizer S.xi S.xi_uniformizer
      (S.coefficient g) (S.coefficient_fixes_xi g) (S.integralCoefficient g) (S.integralCoefficient_eq g)
    have hzk : normalizedValuation k (g (z : k)) = normalizedValuation k (z : k) := by
      have h := hgE (f (e (z : k)))
      rw [hcoeff, hk, hk] at h
      exact (pow_left_inj₀ zero_le zero_le (Nat.mul_ne_zero two_ne_zero S.d_pos.ne')).mp h
    let w : O(k) := ⟨g (z : k), (integer_iff _).mpr (hzk.trans_le (normalizedValuation_integer z))⟩
    have hw := hgal g z w rfl
    rw [hw]
    let e₀ := algebraMap O(k) O(T.field)
    let f₀ := algebraMap O(T.field) O(S.E)
    change residue _ (S.integralCoefficient g (f₀ (e₀ z))) = residue _ (f₀ (e₀ w))
    congr 1
    apply Subtype.ext
    rw [S.integralCoefficient_eq]
    change S.coefficient g (f (e (z : k))) = f (e (w : k))
    exact hcoeff (z : k)
  · have hπ₀ : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact exp_ne_zero hπ.symm
    have hquot : normalizedValuation T.field (T.diagram π / π) = 1 := by
      rw [map_div₀, hτ, hπ, div_self exp_ne_zero]
    let ε := unitOfValueOne _ hquot
    have hε : ((ε : O(T.field)) : T.field) = T.diagram π / π := coe_unitOfValueOne _ hquot
    have hεmul : T.diagram π = ((ε : O(T.field)) : T.field) * π := by
      rw [hε, div_mul_cancel₀ _ hπ₀]
    refine ⟨ε, hε.symm, ?_⟩
    intro n hn s c₁ c₂
    let f₀ := algebraMap O(T.field) O(S.E)
    let e₀ := algebraMap O(k) O(T.field)
    have hsingle (c : O(S.E)ˣ) : SingleSlot (algebraMap T.field S.E) S.xi S.d n s c :=
      single_slot _ f₀ (fun _ => rfl) (residueMap T.field S.E) j.surjective (fun _ => rfl)
        S.d_pos hn hE S.xi S.xi_uniformizer s c
    refine ⟨?_, hsingle c₁, paired_slots T.diagram.toRingEquiv τ₀ hτ hτ₀ hτκ π hπ ε hεmul
      S.d_pos hE S.xi S.xi_uniformizer S.xi_power s c₁ c₂ (hsingle c₁) (hsingle c₂)⟩
    exact single_slot _ (f₀.comp e₀) (fun _ => rfl) (j.toRingHom.comp i.toRingHom)
      (j.surjective.comp i.surjective) (fun _ => rfl)
      (Nat.mul_pos (by decide) S.d_pos) hn hk S.xi S.xi_uniformizer s c₁

end
end LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceCoefficientDepths

universe v8_closure_e4ffbbfc09797f1c_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedCongruenceCoefficientDepths».«ramifiedCoefficientDepths» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedCongruenceCoefficientDepths».«RamifiedCoefficientDepths».{v8_closure_e4ffbbfc09797f1c_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedCongruenceCoefficientDepths».«ramifiedCoefficientDepths_conditional».{v8_closure_e4ffbbfc09797f1c_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_e4ffbbfc09797f1c_u0, v8_closure_e4ffbbfc09797f1c_u0, v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_e4ffbbfc09797f1c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_e4ffbbfc09797f1c_u0})
