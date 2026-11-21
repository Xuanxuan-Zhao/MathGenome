import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.DimensionOneDVR
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Lean.Elab.Tactic.Omega

namespace AdvCommAlg.Normality

open IsLocalRing

/-- Dimension one excludes a field and leaves exactly one nonzero prime. -/
theorem dimension_one_prime_data
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) :
    ¬ IsField A ∧ ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime := by
  have hfield : ¬ IsField A := by
    intro h
    have := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at this
    exact one_ne_zero this
  have hle : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  refine ⟨hfield, maximalIdeal A,
    ⟨isField_iff_maximalIdeal_eq.not.mp hfield, inferInstance⟩, ?_⟩
  intro P hP
  exact eq_maximalIdeal
    (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hle P hP.1 hP.2)

/-- The three conditions of SN-06, with their original dimension-one hypotheses. -/
theorem dimension_one_dvr_equivalences
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) :
    (IsIntegrallyClosed A ↔ IsRegularLocalRing A) ∧
    (IsRegularLocalRing A ↔ IsDiscreteValuationRing A) := by
  obtain ⟨hfield, hprime⟩ := dimension_one_prime_data A hdim
  have hic : IsIntegrallyClosed A ↔ IsDiscreteValuationRing A := by
    exact ⟨fun h ↦ ((IsDiscreteValuationRing.TFAE A hfield).out 4 1 rfl rfl).mp ⟨h, hprime⟩,
      fun h ↦ (((IsDiscreteValuationRing.TFAE A hfield).out 1 4 rfl rfl).mp h).1⟩
  have hreg : IsRegularLocalRing A ↔ IsDiscreteValuationRing A := by
    rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hdim]
    simpa using (IsLocalRing.finrank_CotangentSpace_eq_one_iff (R := A))
  exact ⟨hic.trans hreg.symm, hreg⟩

/-- Clear a common negative power, then use uniqueness of natural exponents. -/
theorem unit_mul_zpow_exponent_unique
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {π : A} (hπ : Irreducible π) (u v : Aˣ) (m n : ℤ)
    (h : algebraMap A K (u : A) * algebraMap A K π ^ m =
      algebraMap A K (v : A) * algebraMap A K π ^ n) : m = n := by
  let k := min m n
  have hm : 0 ≤ m - k := sub_nonneg.mpr (min_le_left _ _)
  have hn : 0 ≤ n - k := sub_nonneg.mpr (min_le_right _ _)
  have hπ0 : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  have hs := congrArg (fun x : K ↦ x * algebraMap A K π ^ (-k)) h
  have hmcast : ((m - k).toNat : ℤ) = m - k := Int.toNat_of_nonneg hm
  have hncast : ((n - k).toNat : ℤ) = n - k := Int.toNat_of_nonneg hn
  have hs' : algebraMap A K ((u : A) * π ^ (m - k).toNat) =
      algebraMap A K ((v : A) * π ^ (n - k).toNat) := by
    simp only [map_mul, map_pow, ← zpow_natCast]
    rw [hmcast, hncast]
    simpa only [mul_assoc, ← zpow_add₀ hπ0, sub_eq_add_neg] using hs
  have he := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ u v
    (m - k).toNat (n - k).toNat ((IsFractionRing.injective A K) hs')
  omega

/-- Fractional factorization for every chosen generator, with unique integer exponent. -/
theorem dimension_one_fractional_factorization
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1)
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : maximalIdeal A = Ideal.span {π})
    (z : K) (hz : z ≠ 0) :
    ∃! n : ℤ, ∃ u : Aˣ,
      z = algebraMap A K (u : A) * (algebraMap A K π) ^ n := by
  have hequiv := dimension_one_dvr_equivalences A hdim
  let : IsDiscreteValuationRing A := hequiv.2.mp (hequiv.1.mp inferInstance)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hirr hz
  have hu' : z = algebraMap A K (u : A) * algebraMap A K π ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def] using hu
  refine ⟨n, ⟨u, hu'⟩, ?_⟩
  rintro m ⟨v, hv⟩
  exact unit_mul_zpow_exponent_unique hirr v u m n (hv.symm.trans hu')

/-- Ring elements have a unique nonnegative exponent. -/
theorem dimension_one_integral_factorization
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1)
    (π : A) (hπ : maximalIdeal A = Ideal.span {π})
    (a : A) (ha : a ≠ 0) :
    ∃! n : ℕ, ∃ u : Aˣ, a = (u : A) * π ^ n := by
  have hequiv := dimension_one_dvr_equivalences A hdim
  let : IsDiscreteValuationRing A := hequiv.2.mp (hequiv.1.mp inferInstance)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
  refine ⟨n, ⟨u, hu⟩, ?_⟩
  rintro m ⟨v, hv⟩
  exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr v u m n (hv.symm.trans hu)

/-- The fractional and integral factorizations assign the same exponent to a ring element. -/
theorem dimension_one_fractional_exponent_nonnegative
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1)
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : maximalIdeal A = Ideal.span {π})
    (a : A) (ha : a ≠ 0) (n : ℤ) (u : Aˣ)
    (h : algebraMap A K a = algebraMap A K (u : A) * algebraMap A K π ^ n) :
    0 ≤ n := by
  have hequiv := dimension_one_dvr_equivalences A hdim
  let : IsDiscreteValuationRing A := hequiv.2.mp (hequiv.1.mp inferInstance)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  obtain ⟨m, ⟨v, hv⟩, _⟩ := dimension_one_integral_factorization A hdim π hπ a ha
  have hv' : algebraMap A K a = algebraMap A K (v : A) * algebraMap A K π ^ (m : ℤ) := by
    simpa only [map_mul, map_pow, zpow_natCast] using congrArg (algebraMap A K) hv
  have heq := unit_mul_zpow_exponent_unique hirr u v n (m : ℤ) (h.symm.trans hv')
  rw [heq]
  exact Int.natCast_nonneg m

end AdvCommAlg.Normality
