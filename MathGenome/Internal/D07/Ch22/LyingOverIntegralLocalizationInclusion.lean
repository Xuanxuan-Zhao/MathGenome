import MathGenome.Internal.Specs.D07.Ch22.LyingOverIntegralLocalizationInclusion
import MathGenome.Internal.D07.Ch22.LocalRings
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Localization.Integral

/-!
The localization step of lying over (paper.tex:7309–7316). The maps use
the canonical quotient localization, with the image denominator submonoid.
Injectivity and integrality are valid even for zero divisors. The last
proof verifies the particular monic equation displayed in the source.
-/

universe u v

namespace D07.Ch22.LyingOverIntegralLocalizationInclusion

open Polynomial
open scoped BigOperators
open Specs.D07.Ch22.LyingOverIntegralLocalizationInclusion

theorem mapOnFractions : MapOnFractions.{u, v} := by
  intro R B _ _ f S r s
  simp only [localizationMap, Localization.mk_eq_mk'_apply, IsLocalization.map_mk']
  rfl

theorem mapInjective : MapInjective.{u, v} := by
  intro R B _ _ f S hf
  exact IsLocalization.map_injective_of_injective _ _ _ hf

theorem mapIntegral : MapIntegral.{u, v} := by
  intro R B _ _ f S hf
  exact isIntegral_localization' hf S

theorem nonzeroAtPrime : NonzeroAtPrime.{u, v} := by
  intro R B _ _ f P _ hf
  have hR := D07.Ch22.LocalRings.localizationNontrivial R P
  let := hR
  exact ⟨hR, Function.Injective.nontrivial (mapInjective R B f P.primeCompl hf)⟩

/-- Scaling a positive monic equation uses only commutative ring laws;
neither cancellation nor a nonzero denominator is needed. -/
theorem scaled_monic_equation {T : Type*} [CommRing T]
    (x d : T) (n : ℕ) (a : ℕ → T)
    (h : x ^ n + ∑ i ∈ Finset.range n, a i * x ^ i = 0) :
    (x * d) ^ n + ∑ i ∈ Finset.range n,
      (a i * d ^ (n - i)) * (x * d) ^ i = 0 := by
  calc
    _ = (x ^ n + ∑ i ∈ Finset.range n, a i * x ^ i) * d ^ n := by
      rw [add_mul, Finset.sum_mul, mul_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
      calc
        (a i * d ^ (n - i)) * (x * d) ^ i =
            (a i * x ^ i) * (d ^ (n - i) * d ^ i) := by
          rw [mul_pow]
          ac_rfl
        _ = (a i * x ^ i) * d ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hin]
    _ = 0 := by rw [h, zero_mul]

theorem fractionMonicEquation : FractionMonicEquation.{u, v} := by
  intro R B _ _ f S b s n hn a h
  let T := Localization (S.map f)
  let g : B →+* T := algebraMap B T
  let d : T := Localization.mk 1 (mappedDenominator f S s)
  have frac (r : R) (k : ℕ) :
      localizationMap f S (Localization.mk r (s ^ k)) = g (f r) * d ^ k := by
    rw [mapOnFractions R B f S]
    have hden : mappedDenominator f S (s ^ k) = (mappedDenominator f S s) ^ k := by
      apply Subtype.ext
      exact map_pow f (s : R) k
    rw [hden]
    change Localization.mk (f r) (mappedDenominator f S s ^ k) =
      algebraMap B (Localization (S.map f)) (f r) *
        Localization.mk 1 (mappedDenominator f S s) ^ k
    simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_pow,
      one_pow, Localization.mk_mul, mul_one, one_mul]
  have hx : Localization.mk b (mappedDenominator f S s) = g b * d := by
    change Localization.mk b (mappedDenominator f S s) =
      algebraMap B (Localization (S.map f)) b * Localization.mk 1 (mappedDenominator f S s)
    simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      mul_one, one_mul]
  have hmap : (g b) ^ n + ∑ i ∈ Finset.range n, g (f (a i)) * (g b) ^ i = 0 := by
    simpa only [map_add, map_sum, map_mul, map_pow, map_zero] using congrArg g h
  have heq : (Localization.mk b (mappedDenominator f S s)) ^ n +
      ∑ i ∈ Finset.range n,
        localizationMap f S (Localization.mk (a i) (s ^ (n - i))) *
          (Localization.mk b (mappedDenominator f S s)) ^ i = 0 := by
    simp only [hx, frac]
    exact scaled_monic_equation (g b) d n (fun i => g (f (a i))) hmap
  refine ⟨?_, ?_, heq⟩
  · apply monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    exact degree_sum_fin_lt (fun i : Fin n => Localization.mk (a i) (s ^ (n - i)))
  · simpa only [fractionPolynomial, eval₂_add, eval₂_finsetSum, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C] using heq

end D07.Ch22.LyingOverIntegralLocalizationInclusion
