import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricPointReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricReduction

open Specs.ExceptionalSplitParahoricReduction

noncomputable section

section ScalingField

universe u

open ValuativeRel WithZero Polynomial
open Specs.ExceptionalLocalRootCoordinates
  (canonicalExtension normalizedValuation normalizedValueGroupMap ramificationIndex residueMap)
open scoped WithZero

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

set_option quotPrecheck false in
local notation "O(" K ")" => (valuation K).valuationSubring

private theorem normalized_le (x y : K) :
    normalizedValuation K x ≤ normalizedValuation K y ↔ valuation K x ≤ valuation K y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

private theorem normalized_lt (x y : K) :
    normalizedValuation K x < normalizedValuation K y ↔ valuation K x < valuation K y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.lt_iff_lt

private theorem normalized_le_one (x : K) :
    normalizedValuation K x ≤ 1 ↔ valuation K x ≤ 1 := by
  simpa only [map_one] using normalized_le x 1

private theorem normalized_lt_one (x : K) :
    normalizedValuation K x < 1 ↔ valuation K x < 1 := by
  simpa only [map_one] using normalized_lt x 1

private theorem uniformizer_span {π : K} (hπ : normalizedValuation K π = exp (-1 : ℤ)) :
    ∃ π₀ : O(K), (π₀ : K) = π ∧ IsLocalRing.maximalIdeal O(K) = Ideal.span {π₀} := by
  have hπlt : normalizedValuation K π < 1 := by
    rw [hπ, ← exp_zero]
    exact exp_lt_exp.mpr (by decide)
  have hπint := normalized_lt_one π |>.mp hπlt
  let π₀ : O(K) := ⟨π, hπint.le⟩
  refine ⟨π₀, rfl, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr
    ((Valuation.mem_maximalIdeal_iff K _).mpr hπint))⟩
  intro z hz
  have hlt := (normalized_lt_one (z : K)).mpr
    ((Valuation.mem_maximalIdeal_iff K _).mp hz)
  rw [Ideal.mem_span_singleton]
  apply (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr
  apply (normalized_le _ _).mp
  change normalizedValuation K (z : K) ≤ normalizedValuation K π
  rw [hπ]
  by_cases h0 : normalizedValuation K (z : K) = 0
  · simp [h0]
  · rw [← exp_log h0, exp_le_exp]
    have hlog : log (normalizedValuation K (z : K)) < 0 := by
      apply exp_lt_exp.mp
      simpa only [exp_log h0, exp_zero] using hlt
    omega

private theorem uniformizer_polynomial_irreducible
    {d : ℕ} (hd : d ≠ 0) {π : K} (hπ : normalizedValuation K π = exp (-1 : ℤ)) :
    Irreducible (X ^ d - C π : K[X]) := by
  obtain ⟨π₀, hcoe, hspan⟩ := uniformizer_span hπ
  let p : O(K)[X] := X ^ d - C π₀
  have hm : p.Monic := monic_X_pow_sub_C π₀ hd
  have hdeg : p.natDegree = d := natDegree_X_pow_sub_C
  let P := IsLocalRing.maximalIdeal O(K)
  have hmax : P.IsMaximal := inferInstanceAs ((IsLocalRing.maximalIdeal O(K)).IsMaximal)
  have hp : p.IsEisensteinAt P := by
    refine hm.isEisensteinAt_of_mem_of_notMem hmax.ne_top ?_ ?_
    · intro n hn
      rw [hdeg] at hn
      simp only [p, coeff_sub, coeff_X_pow, ite_eq_right hn.ne, zero_sub]
      apply P.neg_mem
      by_cases h : n = 0
      · subst n
        change (C π₀).coeff 0 ∈ IsLocalRing.maximalIdeal O(K)
        rw [coeff_C_zero, hspan]
        exact Ideal.subset_span (by simp)
      · rw [coeff_C_of_ne_zero h]
        exact P.zero_mem
    · simp only [p, coeff_sub, coeff_X_pow, ite_eq_right (Ne.symm hd), coeff_C_zero, zero_sub]
      intro h
      have hdiv : π₀ ^ 2 ∣ π₀ := by
        apply Ideal.mem_span_singleton.mp
        have h' := (P ^ 2).neg_mem h
        -- Convert the squared ideal to the principal ideal on the squared uniformizer.
        simpa only [neg_neg, P, hspan, Ideal.span_singleton_pow] using h'
      have hle := (Valuation.integer.integers (valuation K)).dvd_iff_le.mp hdiv
      have hval := (normalized_le _ _).mpr hle
      change normalizedValuation K (π₀ : K) ≤ normalizedValuation K (↑(π₀ ^ 2) : K) at hval
      have hpow : (↑(π₀ ^ 2) : K) = (π₀ : K) ^ 2 := map_pow (valuation K).valuationSubring.subtype _ _
      rw [hpow, map_pow, hcoe, hπ] at hval
      rw [pow_two, ← exp_add, exp_le_exp] at hval
      omega
  have hir := hp.irreducible hmax.isPrime hm.isPrimitive
    (hdeg.symm ▸ Nat.pos_of_ne_zero hd)
  have hir' := (hm.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hir
  have hcoeMap : algebraMap O(K) K π₀ = π := hcoe
  simpa only [p, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hcoeMap]
    using hir'

variable {L : Type u} [Field L] [Algebra K L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

private theorem normalized_value_map (x : K) :
    normalizedValueGroupMap K L (normalizedValuation K x) =
      normalizedValuation L (algebraMap K L x) := by
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eL := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change eL (ValuativeExtension.mapValueGroupWithZero K L (eK.symm (eK (valuation K x)))) =
    eL (valuation L (algebraMap K L x))
  rw [eK.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]

private theorem scaled_uniformizer_values {d : ℕ} (hd : 0 < d) {π : K} {ξ : L}
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) (hξ : ξ ^ d = algebraMap K L π) :
    ∃ c : ℤ, 0 < c ∧ normalizedValuation L ξ = exp (-c) ∧
      ∀ x : K, x ≠ 0 → normalizedValuation L (algebraMap K L x) =
        exp ((d : ℤ) * c * log (normalizedValuation K x)) := by
  have hπ₀ : π ≠ 0 := fun hz => exp_ne_zero (a := (-1 : ℤ)) (hπ.symm.trans (by simp [hz]))
  have hξ₀ : ξ ≠ 0 := fun hz => ((_root_.map_ne_zero (algebraMap K L)).mpr hπ₀)
    (by simpa [hz, Nat.ne_of_gt hd] using hξ.symm)
  let c := -(log (normalizedValuation L ξ))
  have hξv : normalizedValuation L ξ = exp (-c) := by
    simpa only [c, neg_neg] using (exp_log ((_root_.map_ne_zero (normalizedValuation L)).mpr hξ₀)).symm
  have hall : normalizedValuation L (algebraMap K L π) = exp (-c) ^ d := by rw [← hξ, map_pow, hξv]
  have hπlt : normalizedValuation L (algebraMap K L π) < 1 := by
    let := canonicalExtension K L
    refine (normalized_lt_one _).mpr
      ((Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) π).mpr ?_)
    apply (normalized_lt_one π).mp
    rw [hπ, ← exp_zero]
    exact exp_lt_exp.mpr (by decide)
  have hc : 0 < c := by
    have hp : exp (-c) ^ d < 1 := hall ▸ hπlt
    have hv : exp (-c) < 1 := by
      by_contra! h
      exact (not_le_of_gt hp) (one_le_pow₀ h)
    have : -c < 0 := exp_lt_exp.mp (by simpa only [exp_zero] using hv)
    omega
  refine ⟨c, hc, hξv, ?_⟩
  intro x hx
  let n := log (normalizedValuation K x)
  let f := normalizedValueGroupMap K L
  have hexp (z : ℤ) (e : ℤ) : (exp z : ℤᵐ⁰) ^ e = exp (e * z) := by
    change (((↑(Multiplicative.ofAdd z)) : ℤᵐ⁰) ^ e) =
      ↑(Multiplicative.ofAdd (e * z))
    rw [← WithZero.coe_zpow]
    rfl
  have hπ' : f (exp (-1 : ℤ)) = exp (-((d : ℤ) * c)) := by
    rw [← hπ, normalized_value_map, hall, ← zpow_natCast, hexp]
    congr 1
    simp
  have hz (z : ℤ) : exp z = (exp (-1 : ℤ) : ℤᵐ⁰) ^ (-z) := by rw [hexp]; simp
  calc
    normalizedValuation L (algebraMap K L x) = f (exp n) := by
      rw [exp_log ((_root_.map_ne_zero (normalizedValuation K)).mpr hx), normalized_value_map]
    _ = exp ((d : ℤ) * c * n) := by
      rw [hz n, map_zpow₀, hπ', hexp]
      congr 1
      simp [mul_comm]


private theorem scaled_residue_field {d : ℕ} (hd : 0 < d) {π : K} {ξ : L}
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) (hξ : ξ ^ d = algebraMap K L π)
    (b : Module.Basis (Fin d) K L) (hb : ∀ i, b i = ξ ^ i.val) :
    Function.Bijective (residueMap K L) ∧ normalizedValuation L ξ = exp (-1 : ℤ) := by
  classical
  let := canonicalExtension K L
  obtain ⟨c, hc, hξv, hv⟩ := scaled_uniformizer_values hd hπ hξ
  have hξ₀ : ξ ≠ 0 := fun h => exp_ne_zero (hξv.symm.trans (by simp [h]))
  let zeroIndex : Fin d := ⟨0, hd⟩
  let coeff (z : L) (i : Fin d) : K := b.repr z i
  let term (z : L) (i : Fin d) : L := algebraMap K L (coeff z i) * ξ ^ i.val
  let v := normalizedValuation L
  have hsum (z : L) : ∑ i, term z i = z := by
    simpa only [term, coeff, ← hb, ← Algebra.smul_def] using b.sum_repr z
  have hterm (z : L) (i : Fin d) (hi : coeff z i ≠ 0) :
      v (term z i) =
        exp (c * ((d : ℤ) * log (normalizedValuation K (coeff z i)) - (i.val : ℤ))) := by
    dsimp only [term, v]
    rw [map_mul, hv _ hi, map_pow, hξv, ← exp_nsmul, ← exp_add, exp_inj, nsmul_eq_mul]
    ring
  have hterm_zero_iff (z : L) (i : Fin d) : v (term z i) = 0 ↔ coeff z i = 0 := by
    change v (algebraMap K L (coeff z i) * ξ ^ i.val) = 0 ↔ coeff z i = 0
    simp [hξ₀]
  have hdistinct (z : L) (i j : Fin d) (hij : v (term z i) = v (term z j))
      (hi : v (term z i) ≠ 0) : i = j := by
    have hni : coeff z i ≠ 0 := fun h => hi ((hterm_zero_iff z i).mpr h)
    have hnj : coeff z j ≠ 0 := fun h => hi (hij.trans ((hterm_zero_iff z j).mpr h))
    rw [hterm z i hni, hterm z j hnj, exp_inj, mul_right_inj' (ne_of_gt hc)] at hij
    have hmod (x : ℤ) (i : Fin d) :
        (-((d : ℤ) * x - (i.val : ℤ))) % d = i.val := by
      rw [neg_sub, Int.sub_mul_emod_self_left, Int.emod_eq_of_lt]
      · omega
      · exact_mod_cast i.isLt
    apply Fin.ext
    exact_mod_cast (hmod _ i |>.symm.trans
      ((congrArg (fun s : ℤ => (-s) % d) hij).trans (hmod _ j)))
  -- Distinct nonzero summands have distinct values, so the highest value
  -- survives in their sum.
  have hmax (z : L) : ∃ j : Fin d, (∀ i, v (term z i) ≤ v (term z j)) ∧
      v z = v (term z j) := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      ⟨zeroIndex, Finset.mem_univ _⟩ (fun i => v (term z i))
    have hle (i : Fin d) : v (term z i) ≤ v (term z j) :=
      hj ▸ Finset.le_sup (f := fun i => v (term z i)) (Finset.mem_univ i)
    refine ⟨j, hle, (congrArg v (hsum z)).symm.trans ?_⟩
    by_cases h0 : v (term z j) = 0
    · rw [h0]
      exact le_antisymm (v.map_sum_le (g := 0) (fun i _ => (hle i).trans_eq h0)) zero_le
    · apply v.map_sum_eq_of_lt (Finset.mem_univ j)
      intro i hi
      apply lt_of_le_of_ne (hle i)
      intro he
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_singleton.mpr (hdistinct z i j he (he.symm ▸ h0)))
  have hξuniformizer : normalizedValuation L ξ = exp (-1 : ℤ) := by
    let valueIso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
    obtain ⟨w, hw⟩ := valuation_surjective (valueIso.symm (exp (-1 : ℤ)))
    have hw' : v w = exp (-1 : ℤ) := by
      change valueIso (valuation L w) = _
      rw [hw, valueIso.apply_symm_apply]
    obtain ⟨j, _, hj⟩ := hmax w
    have hCoeff : coeff w j ≠ 0 := by
      intro hz
      exact exp_ne_zero (hw'.symm.trans (hj.trans ((hterm_zero_iff w j).mpr hz)))
    rw [hw', hterm w j hCoeff, exp_inj] at hj
    have hdiv : c ∣ (1 : ℤ) := dvd_neg.mp ⟨_, hj⟩
    have hle := Int.le_of_dvd (by decide : 0 < (1 : ℤ)) hdiv
    have hc' : c = 1 := by omega
    simpa only [hc'] using hξv
  refine ⟨⟨(residueMap K L).injective, ?_⟩, hξuniformizer⟩
  intro r
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective r
  let a := coeff (z : L)
  let t := term (z : L)
  obtain ⟨j, hjmax, hj⟩ := hmax (z : L)
  have hzz : v (z : L) ≤ 1 := (normalized_le_one _).mpr z.property
  have hmaxle : v (t j) ≤ 1 := hj ▸ hzz
  have hlog_le (i : Fin d) (hi : a i ≠ 0) :
      log (normalizedValuation K (a i)) ≤ 0 := by
    have hi' : (i.val : ℤ) < (d : ℤ) := by exact_mod_cast i.isLt
    have hval := (hjmax i).trans hmaxle
    rw [hterm (z : L) i hi, ← exp_zero, exp_le_exp] at hval
    change c * ((d : ℤ) * log (normalizedValuation K (a i)) - (i.val : ℤ)) ≤ 0 at hval
    by_contra! hpos
    have hmul : (d : ℤ) ≤ (d : ℤ) * log (normalizedValuation K (a i)) :=
      le_mul_of_one_le_right (by omega) (by omega)
    exact (not_le_of_gt (mul_pos hc (by omega))) hval
  have hconst : (a zeroIndex) ∈ O(K) := by
    change valuation K (a zeroIndex) ≤ 1
    apply (normalized_le_one _).mp
    by_cases h : a zeroIndex = 0
    · simp [h]
    rw [← exp_log ((_root_.map_ne_zero (normalizedValuation K)).mpr h), ← exp_zero, exp_le_exp]
    exact hlog_le _ h
  let liftConst : O(K) := ⟨a zeroIndex, hconst⟩
  have htail (i : Fin d) (hi : i ≠ zeroIndex) : v (t i) < 1 := by
    by_cases he : a i = 0
    · rw [(hterm_zero_iff (z : L) i).mpr he]
      exact zero_lt_one
    have hi' : 0 < (i.val : ℤ) := by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    have hmul : (d : ℤ) * log (normalizedValuation K (a i)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) (hlog_le _ he)
    rw [hterm (z : L) i he, ← exp_zero, exp_lt_exp]
    change c * ((d : ℤ) * log (normalizedValuation K (a i)) - (i.val : ℤ)) < 0
    exact mul_neg_of_pos_of_neg hc (by omega)
  have hdiff : v ((z : L) - algebraMap K L (a zeroIndex)) < 1 := by
    have hsplit := Finset.sum_erase_add Finset.univ t (Finset.mem_univ zeroIndex)
    have hterm0 : t zeroIndex = algebraMap K L (a zeroIndex) := by simp [t, term, a, zeroIndex]
    rw [show ∑ i, t i = (z : L) from hsum _, hterm0, ← eq_sub_iff_add_eq] at hsplit
    rw [← hsplit]
    apply lt_of_le_of_lt (v.map_sum_le (g := exp (-1 : ℤ)) ?_)
    · rw [← exp_zero]
      exact exp_lt_exp.mpr (by decide)
    · intro i hi
      have hvlt := htail i (Finset.mem_erase.mp hi).1
      by_cases h0 : v (t i) = 0
      · simp [h0]
      · rw [← exp_log h0, exp_le_exp]
        have hlog : log (v (t i)) < 0 := exp_lt_exp.mp (by simpa only [exp_log h0, exp_zero] using hvlt)
        omega
  refine ⟨IsLocalRing.residue _ liftConst, ?_⟩
  rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap (valuation K) (valuation L)]
  apply (sub_eq_zero.mp ?_).symm
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact (normalized_lt_one _).mp hdiff

/-- Adjoining a root of the uniformizer leaves the residue field unchanged. -/
theorem exists_uniformizer_root_same_residue (d : ℕ) (hd : 0 < d) (π : Kˣ)
    (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : ValuativeExtension K L) (ξ : Lˣ),
      (ξ : L) ^ d = algebraMap K L (π : K) ∧ Function.Bijective (residueMap K L) ∧
      Algebra.adjoin K ({(ξ : L)} : Set L) = ⊤ ∧ Module.finrank K L = d ∧
      ramificationIndex K L = (d : ℤ) ∧ normalizedValuation L (ξ : L) = exp (-1 : ℤ) := by
  let p : K[X] := X ^ d - C (π : K)
  have hp : p.Monic := monic_X_pow_sub_C _ hd.ne'
  let : Fact (Irreducible p) := ⟨uniformizer_polynomial_irreducible hd.ne' hπ⟩
  let L := AdjoinRoot p
  let : FiniteDimensional K L := hp.finite_adjoinRoot
  let ξ := AdjoinRoot.root p
  have hξ : ξ ^ d = algebraMap K L (π : K) := by
    have h := AdjoinRoot.aeval_eq (f := p) p
    rw [AdjoinRoot.mk_self] at h
    simpa [p, ξ, L, sub_eq_zero] using h
  have hξ₀ : ξ ≠ 0 := by
    intro hz
    have := algebraMap K L |>.injective
    apply π.ne_zero
    apply this
    simpa [hz, hd.ne'] using hξ.symm
  obtain ⟨r, T, ext, loc, _, _, _⟩ := finiteExtension_localField (K := K) (L := L)
  let := r
  let := T
  let := ext
  let := loc
  let b := AdjoinRoot.powerBasis hp.ne_zero
  have hdeg : b.dim = d := natDegree_X_pow_sub_C
  have hb (i : Fin d) : b.basis.reindex (finCongr hdeg) i = ξ ^ i.val := by
    rw [Module.Basis.reindex_apply, b.basis_eq_pow]
    rfl
  obtain ⟨hresidue, hξv⟩ := scaled_residue_field hd hπ hξ _ hb
  have hmap : normalizedValueGroupMap K L (exp (-1 : ℤ)) = exp (-(d : ℤ)) := by
    rw [← hπ, normalized_value_map, ← hξ, map_pow, hξv, ← exp_nsmul, nsmul_eq_mul]
    simp
  have hmapInv : normalizedValueGroupMap K L (exp (1 : ℤ)) =
      (normalizedValueGroupMap K L (exp (-1 : ℤ)))⁻¹ := by
    rw [← map_inv₀, ← exp_neg, neg_neg]
  have hRamification : ramificationIndex K L = (d : ℤ) := by
    rw [ramificationIndex, hmapInv, hmap, ← exp_neg, neg_neg, log_exp]
  exact ⟨L, inferInstance, inferInstance, inferInstance, r, T, loc, ext, Units.mk0 ξ hξ₀,
    hξ, hresidue, AdjoinRoot.adjoinRoot_eq_top, b.finrank.trans hdeg, hRamification, hξv⟩


end ScalingField

section ComparisonLemmas

universe u

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights SplitBuildingLevel cotype parahoric)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

/-- A root evaluates on the integral multiple of a rational point by the
same integer pairing used in the marked torus conjugation formula. -/
theorem root_at_scaled_point {E : BasedRootDatum.{u}}
    (a : E.I) (x : ℚ ⊗[ℤ] E.Y) (d : ℕ) (y : E.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) :
    (d : ℚ) * (ApartmentRoots.split E.datum ℚ).root a x =
      (E.datum.toLinearMap (E.datum.root a) y : ℚ) := by
  let f := (ApartmentRoots.split E.datum ℚ).root a
  calc
    (d : ℚ) * f x = f ((d : ℚ) • x) := by rw [map_smul, smul_eq_mul]
    _ = f ((1 : ℚ) ⊗ₜ[ℤ] y) := congrArg f hy
    _ = _ := RootData.extendFunctional_one_tmul ℚ (E.datum.root' a) y

/-- The integer pairing vanishes modulo the denominator precisely for roots
that take integral values at the apartment point. -/
theorem integral_root_iff_dvd {E : BasedRootDatum.{u}}
    (a : E.I) (x : ℚ ⊗[ℤ] E.Y) {d : ℕ} (hd : 0 < d) (y : E.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) :
    (∃ n : ℤ, (ApartmentRoots.split E.datum ℚ).root a x = n) ↔
      (d : ℤ) ∣ E.datum.toLinearMap (E.datum.root a) y := by
  have hs := root_at_scaled_point a x d y hy
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn] at hs
    exact_mod_cast hs.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : (E.datum.toLinearMap (E.datum.root a) y : ℚ) = (d : ℚ) * (n : ℚ) := by
      exact_mod_cast hn
    rw [hn'] at hs
    exact mul_left_cancel₀ (by exact_mod_cast hd.ne') hs

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
  (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))

/-- Incidence with the marked standard face is equivalent to having a
representative in its actual parahoric subgroup. -/
theorem mem_incident_iff
    (q : FieldPoints M' K ⧸ Y.ad.I) :
    q ∈ IncidentChambers B (B.ad.realization.place 1 t) ↔
      ∃ g : parahoric Y.ad (cotype t), q = QuotientGroup.mk (g : FieldPoints M' K) := by
  constructor
  · rintro ⟨g, s, hq, hs⟩
    obtain ⟨_, hg⟩ := (B.ad.realization.place_eq 1 g t s).mp hs.symm
    exact ⟨⟨g, by simpa using hg⟩, hq⟩
  · rintro ⟨g, rfl⟩
    let g₀ : Y.ad.G₀ := ⟨g, B.ad.realization.face_mem _ g.property⟩
    refine ⟨g₀, t, rfl, ?_⟩
    exact ((B.ad.realization.place_eq 1 g₀ t t).mpr
      ⟨rfl, by simp [g₀, g.property]⟩).symm

/-- Incident chambers form the quotient by the restriction of the Iwahori
to the parahoric. -/
def incidentCosetEquiv :
    (parahoric Y.ad (cotype t) ⧸ Y.ad.I.subgroupOf (parahoric Y.ad (cotype t))) ≃
      IncidentChambers B (B.ad.realization.place 1 t) :=
  Equiv.ofBijective
    (Quotient.lift (fun g : parahoric Y.ad (cotype t) =>
      ⟨QuotientGroup.mk (g : FieldPoints M' K), (mem_incident_iff B t _).mpr ⟨g, rfl⟩⟩)
      (fun g h hrel => by
        apply Subtype.ext
        apply QuotientGroup.eq.mpr
        exact (QuotientGroup.leftRel_apply
          (s := Y.ad.I.subgroupOf (parahoric Y.ad (cotype t)))).mp hrel))
    ⟨fun q r => Quotient.inductionOn₂ q r fun g h hab => by
        apply QuotientGroup.eq.mpr
        have he := congrArg Subtype.val hab
        change (QuotientGroup.mk (g : FieldPoints M' K) : FieldPoints M' K ⧸ Y.ad.I) =
          QuotientGroup.mk (h : FieldPoints M' K) at he
        exact (QuotientGroup.eq (s := Y.ad.I)).mp he,
      fun q => by
        obtain ⟨g, hg⟩ := (mem_incident_iff B t q.val).mp q.property
        exact ⟨QuotientGroup.mk g, Subtype.ext hg.symm⟩⟩

@[simp] theorem incidentCosetEquiv_mk (g : parahoric Y.ad (cotype t)) :
    (incidentCosetEquiv B t (QuotientGroup.mk g)).val =
      QuotientGroup.mk (g : FieldPoints M' K) := rfl

/-- A surjective reduction with the stated Borel preimage and flag fibres
induces a bijection on the incident chambers. -/
def incidentEquivOfReduction {H F : Type u} [Group H]
    (q : parahoric Y.ad (cotype t) →* H) (hq : Function.Surjective q)
    (S : Subgroup H)
    (hS : S.comap q = Y.ad.I.subgroupOf (parahoric Y.ad (cotype t)))
    (pr : H → F) (hpr : Function.Surjective pr)
    (hpr_eq : ∀ a b, pr a = pr b ↔ a⁻¹ * b ∈ S) :
    IncidentChambers B (B.ad.realization.place 1 t) ≃ F := by
  let P := parahoric Y.ad (cotype t)
  let I := Y.ad.I.subgroupOf P
  have h (g k : P) : pr (q g) = pr (q k) ↔ g⁻¹ * k ∈ I := by
    rw [hpr_eq, ← map_inv, ← map_mul]
    change g⁻¹ * k ∈ S.comap q ↔ g⁻¹ * k ∈ I
    rw [hS]
  let f : P ⧸ I → F :=
    Quotient.lift (fun g => pr (q g))
      (fun g k hg => (h g k).mpr ((QuotientGroup.leftRel_apply (s := I)).mp hg))
  have hb : Function.Bijective f :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun g k hg =>
        (QuotientGroup.eq (s := I)).mpr ((h g k).mp hg),
      fun a => by
        obtain ⟨b, rfl⟩ := hpr a
        obtain ⟨g, rfl⟩ := hq b
        exact ⟨QuotientGroup.mk g, rfl⟩⟩
  exact (incidentCosetEquiv B t).symm.trans (Equiv.ofBijective f hb)

@[simp] theorem incidentEquivOfReduction_mk {H F : Type u} [Group H]
    (q : parahoric Y.ad (cotype t) →* H) (hq : Function.Surjective q)
    (S : Subgroup H)
    (hS : S.comap q = Y.ad.I.subgroupOf (parahoric Y.ad (cotype t)))
    (pr : H → F) (hpr : Function.Surjective pr)
    (hpr_eq : ∀ a b, pr a = pr b ↔ a⁻¹ * b ∈ S)
    (g : parahoric Y.ad (cotype t)) (b : IncidentChambers B (B.ad.realization.place 1 t))
    (hb : b.val = QuotientGroup.mk (g : FieldPoints M' K)) :
    incidentEquivOfReduction B t q hq S hS pr hpr hpr_eq b = pr (q g) := by
  have he : b = incidentCosetEquiv B t (QuotientGroup.mk g) := Subtype.ext hb
  rw [he]
  simp only [incidentEquivOfReduction, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end ComparisonLemmas

section Assembly

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct WithZero
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights SplitBuildingLevel cotype parahoric)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalLocalRootCoordinates (residueMap)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalResidueCentralizer (cyclicGroup rootValue survivingRoots)
open Specs.IntegralSemisimpleModel (Model integerAlgebra fibre splitTorus)
open Specs.Pinning (BasedRootDatum)
open Specs.AdjointRepresentation (GroupPoints)

attribute [local instance] integerAlgebra

local notation "A(" E ")" => ApartmentRoots.split (BasedRootDatum.datum E) ℚ

private theorem root_direction_eq_wall {E : BasedRootDatum.{u}}
    (p x : ℚ ⊗[ℤ] E.Y) (a : E.I) (j : ℤ) (hj : A(E).root a x = j) :
    rootValue E a (p - x) = A(E).wallValue (a, -j) p := by
  change A(E).root a (p - x) = A(E).root a p + ((-j : ℤ) : ℚ)
  rw [map_sub, hj, Int.cast_neg, sub_eq_add_neg]

private theorem surviving_roots_eq {E : BasedRootDatum.{u}}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} (hd : 0 < d) (y : E.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) :
    survivingRoots E d y = {a | ∃ j : ℤ, A(E).root a x = j} := by
  ext a
  exact (integral_root_iff_dvd a x hd y hy).symm

private theorem regular_direction_on_surviving_roots {E : BasedRootDatum.{u}}
    {p x : ℚ ⊗[ℤ] E.Y} (hp : A(E).IsRegular p)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) :
    ∀ a ∈ survivingRoots E d y, rootValue E a (p - x) ≠ 0 := by
  intro a ha hz
  rw [surviving_roots_eq hd y hy] at ha
  obtain ⟨j, hj⟩ := ha
  rw [root_direction_eq_wall p x a j hj] at hz
  change A(E).root a p + ((-j : ℤ) : ℚ) = 0 at hz
  rw [Int.cast_neg] at hz
  exact hp a ⟨j, by linarith⟩

private theorem positive_surviving_root_iff {E : BasedRootDatum.{u}}
    (p x : ℚ ⊗[ℤ] E.Y) {d : ℕ} (hd : 0 < d) (y : E.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) (a : E.I) :
    (a ∈ survivingRoots E d y ∧ 0 < rootValue E a (p - x)) ↔
      ∃ j : ℤ, A(E).root a x = j ∧ A(E).positive p (a, -j) := by
  rw [surviving_roots_eq hd y hy]
  constructor
  · rintro ⟨⟨j, hj⟩, hpos⟩
    refine ⟨j, hj, ?_⟩
    change 0 < A(E).wallValue (a, -j) p
    exact (root_direction_eq_wall p x a j hj) ▸ hpos
  · rintro ⟨j, hj, hpos⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [root_direction_eq_wall p x a j hj]
    exact hpos

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- At a prescribed uniformizer root, the actual incident chambers are the
rational flags of the marked connected residue centralizer. -/
theorem splitFaceResidueAtRoot : SplitFaceResidueAtRoot.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y B t x hx d y hd hy π hπ L _ _ _ _ _ _ _ ξ hξ hres
  let k := residue L
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨line, F, eG, eT, coords, hT, hSimple, hEval, hRootEval⟩ := M'.fieldFibre k
  let marking : MarkedFibre M' k :=
    ⟨line, F, eG, eT, coords, hT, fun a => congrArg Subtype.val (hSimple a), hEval, hRootEval⟩
  have hreg := regular_direction_on_surviving_roots (x := x) Y.ad.geometry.regular hd y hy
  obtain ⟨unitPoints, μImage, C, H, hμImage, hCentralizes, hSmooth, hOpen, hComponent,
    hAff, hLft, hQc, hRed, T, τ, hMarked, hSplit, hMax, hChars, hRoots,
    Bψ, hBorel, hBT, hBorelRoots⟩ :=
    ExceptionalResidueCentralizer.residueCentralizer M' d y (p' - x) hd hreg
      line F eG eT coords hT hSimple hEval hRootEval
  have hCharacters : Specs.CharacterPairing.absoluteRoots T =
      (fun a : E.I => Specs.Pinning.transportCharacter (marking.torusIso.symm ≪≫ τ)
        (marking.realization.datumIso.val.indexEquiv a).val) ''
          {a | ∃ j : ℤ, A(E).root a x = j} := by
    rw [← surviving_roots_eq hd y hy]
    exact hChars
  have hRoot (a : E.I) :
      (∃ r : (fibre k).obj M'.line.group ⟶ H.group,
        r ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
        ∃ j : ℤ, A(E).root a x = j :=
    (hRoots a).trans (integral_root_iff_dvd a x hd y hy).symm
  have hBorelRoot (a : E.I) :
      (∃ r : (fibre k).obj M'.line.group ⟶ Bψ.group,
        r ≫ Bψ.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
        ∃ j : ℤ, A(E).root a x = j ∧ A(E).positive p' (a, -j) :=
    (hBorelRoots a).trans (positive_surviving_root_iff p' x hd y hy a)
  obtain ⟨R⟩ := ExceptionalParahoricPointReduction.splitParahoricPointReduction K B t x hx
    d y hd hy π hπ L ξ hξ hres C H hAff hLft hQc hRed T τ hMarked hSplit hMax
    marking hCharacters hRoot Bψ hBorel hBT hBorelRoot
  let bPoint := IsMonHom.monoidHom Bψ.inclusion.hom.hom
    ((testSpec k).obj (Opposite.op (CommAlgCat.of k k)))
  let bRange := bPoint.range
  have hbRange :
      bRange.comap R.reduction = Y.ad.I.subgroupOf (parahoric Y.ad (cotype t)) := by
    ext g
    exact R.preimage_borel g
  let flag (a : GroupPoints H.group (CommAlgCat.of k k)) := a ≫ R.flags.projection
  have hFlagFibres (a b : GroupPoints H.group (CommAlgCat.of k k)) :
      flag a = flag b ↔ a⁻¹ * b ∈ bRange :=
    R.flag_fibres a b
  let incident := incidentEquivOfReduction B t R.reduction R.reduction_surjective
    bRange hbRange flag R.flag_surjective hFlagFibres
  exact ⟨{
    parameter := hξ
    same_residue := hres
    integral := R.integral
    scale := R.scale
    muGroup := cyclicGroup k d
    unitPoints := unitPoints
    μImage := μImage
    μImage_cocharacter := hμImage
    centralizer := C
    centralizes := hCentralizes
    centralizer_smooth := hSmooth
    identityComponent := H
    component_open := hOpen
    component_eq := hComponent
    group_is_affine := hAff
    group_lft := hLft
    group_qc := hQc
    reductive := hRed
    torus := T
    torusComparison := τ
    torus_marked := hMarked
    torus_split := hSplit
    torus_maximal := hMax
    ambientMarking := marking
    root_characters := hCharacters
    roots := hRoot
    borel := Bψ
    borel_is_borel := hBorel
    borel_torus := hBT
    borel_roots := hBorelRoot
    reduction := R.reduction
    reduction_eq := R.reduction_eq
    reduction_surjective := R.reduction_surjective
    preimage_borel := R.preimage_borel
    iwahori_image := R.iwahori_image
    flags := R.flags
    flag_surjective := R.flag_surjective
    flag_fibres := R.flag_fibres
    incident := incident
    incident_eq := incidentEquivOfReduction_mk B t R.reduction R.reduction_surjective
      bRange hbRange flag R.flag_surjective hFlagFibres
  }⟩

/-- The prescribed-root reduction yields the version with a newly adjoined
uniformizer root. -/
theorem splitFaceResidue_of_atRoot (reduceAtRoot : SplitFaceResidueAtRoot.{u}) :
    SplitFaceResidue.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y B t x hx d y hd hy π hπ
  obtain ⟨L, f, a, fin, v, T, loc, ext, ξ, hξ, hres, hGen, hDegree, hRamification, hξv⟩ :=
    exists_uniformizer_root_same_residue d hd π hπ
  exact ⟨L, f, a, fin, v, T, loc, ext, ξ, hGen, hDegree, hRamification, hξv,
    reduceAtRoot K B t x hx d y hd hy π hπ L ξ hξ hres⟩

/-- Split face reduction after adjoining a root of the uniformizer. -/
theorem splitFaceResidue : SplitFaceResidue.{u} :=
  splitFaceResidue_of_atRoot splitFaceResidueAtRoot

end Assembly

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricReduction
