import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorLocalization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.SimpleDifferentialDomain
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

namespace GaloisFormalization.PV.Operator

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]

private theorem derivation_preserves_nilpotence (d : Derivation ℤ R R) {x : R}
    (hx : IsNilpotent x) : IsNilpotent (d x) := by
  -- Differentiating a vanishing product and multiplying by its second factor
  -- lowers the exponent of x by one, at the cost of more factors of d x.
  have step (n k : ℕ) (h : x ^ n * d x ^ k = 0) : IsNilpotent (d x) := by
    induction n generalizing k with
    | zero => exact ⟨k, by simpa only [pow_zero, one_mul] using h⟩
    | succ n ih =>
      let y := d x ^ k
      change x ^ (n + 1) * y = 0 at h
      have hd : d (x ^ (n + 1) * y) = 0 := by rw [h, d.map_zero]
      rw [d.leibniz, d.leibniz_pow x (n + 1)] at hd
      simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul] at hd
      have hy : (x ^ (n + 1) * d y) * y = 0 := calc
        (x ^ (n + 1) * d y) * y = (x ^ (n + 1) * y) * d y := by ac_rfl
        _ = 0 := by rw [h, zero_mul]
      have hunitQ : IsUnit ((n + 1 : ℕ) : ℚ) :=
        isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      have hunit : IsUnit ((n + 1 : ℕ) : R) := by
        simpa only [map_natCast] using hunitQ.map (algebraMap ℚ R)
      have hstep : x ^ n * (d x * (y * y)) = 0 := by
        apply hunit.mul_left_cancel
        rw [mul_zero]
        calc
          ((n + 1 : ℕ) : R) * (x ^ n * (d x * (y * y))) =
              (x ^ (n + 1) * d y + y * (((n + 1 : ℕ) : R) * (x ^ n * d x))) * y := by
            rw [add_mul, hy, zero_add]
            ac_rfl
          _ = 0 := by rw [hd, zero_mul]
      apply ih (1 + (k + k))
      simpa only [pow_add, pow_one, y] using hstep
  obtain ⟨n, hn⟩ := hx
  exact step n 0 (by simpa only [pow_zero, mul_one] using hn)

private theorem minimalPrime_isStable (D : Operator .differential R) {p : _root_.Ideal R}
    (hp : p ∈ minimalPrimes R) : D.IsStable (p : Set R) := by
  let : p.IsPrime := hp.isPrime
  let L := Localization.AtPrime p
  let : Algebra ℚ L := ((algebraMap R L).comp (algebraMap ℚ R)).toAlgebra
  let q := p.map (algebraMap R L)
  have hq : q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime p (S := L) le_rfl
  have : Subsingleton (PrimeSpectrum L) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp L
  have hcontract : q.comap (algebraMap R L) = p :=
    Ideal.under_map_of_isLocalizationAtPrime p (S := L) le_rfl
  intro x hx
  change x ∈ p at hx
  change D.toDerivation x ∈ p
  have hxq : algebraMap R L x ∈ q := Ideal.mem_map_of_mem (algebraMap R L) hx
  have hnil : IsNilpotent (algebraMap R L x) := by
    apply nilpotent_iff_mem_prime.mpr
    intro J hJ
    have h : (⟨q, hq⟩ : PrimeSpectrum L) = ⟨J, hJ⟩ := Subsingleton.elim _ _
    have hqJ : q = J := congrArg PrimeSpectrum.asIdeal h
    exact hqJ ▸ hxq
  have hdn := derivation_preserves_nilpotence (localizeDerivation p.primeCompl D.toDerivation) hnil
  rw [localizeDerivation_algebraMap] at hdn
  rw [← hcontract]
  exact nilpotent_iff_mem_prime.mp hdn q hq

/-- A simple Noetherian differential ring containing the rationals is a domain. -/
theorem isDomain_of_isSimple [IsNoetherianRing R] (D : Operator .differential R)
    (hD : D.IsSimple) : IsDomain R := by
  let : Nontrivial R := hD.1
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : _root_.Ideal R)) bot_ne_top
  have hp0 : p = ⊥ := (hD.2 p (minimalPrime_isStable D hp)).resolve_right hp.isPrime.ne_top
  apply (isDomain_iff_noZeroDivisors_and_nontrivial R).mpr
  refine ⟨⟨fun {a b} hab => ?_⟩, hD.1⟩
  simpa only [hp0, Submodule.mem_bot] using hp.isPrime.mem_or_mem_of_mul_eq_zero hab

end GaloisFormalization.PV.Operator
