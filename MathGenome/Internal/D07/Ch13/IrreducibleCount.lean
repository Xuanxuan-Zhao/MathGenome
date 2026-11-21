import MathGenome.Internal.Specs.D07.Ch13.IrreducibleCount
import MathGenome.Internal.D07.Ch13.UniversalFactorization
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp

/-! Counting monic irreducibles over a fixed finite field. The first identity
follows from the degrees in the upstream universal factorization. Its degree
fibers are counted intrinsically in K[X]. Möbius inversion then takes place
in ℚ; positivity of n justifies the final division. -/

universe u
namespace D07.Ch13.IrreducibleCount

open Polynomial
open Specs.D07.Ch13.IrreducibleCount

theorem finite_monic_irreducibles : FiniteCounts.{u} := by
  intro K _ _ n hn
  obtain ⟨s, hs, _⟩ :=
    UniversalFactorization.universal_factorization K (Nat.card K) n rfl hn
  apply Set.Finite.to_subtype
  apply s.finite_toSet.subset
  intro f hf
  exact (hs f).mpr ⟨hf.1, hf.2.1, hf.2.2 ▸ dvd_refl n⟩

/-- Each degree fiber of the universal factor set has the intrinsic count. -/
lemma fiber_card (K : Type u) [Field K] [Finite K] (n d : ℕ)
    (hd : d ∈ n.divisors) (s : Finset K[X])
    (hs : ∀ f : K[X], f ∈ s ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ∣ n) :
    (s.filter (fun f => f.natDegree = d)).card = count K d := by
  classical
  have heq : {f : K[X] | f ∈ s.filter (fun f => f.natDegree = d)} =
      {f : K[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = d} := by
    ext f
    simp only [Set.mem_ofPred_eq, Finset.mem_filter, hs]
    constructor
    · rintro ⟨⟨hm, hi, _⟩, he⟩
      exact ⟨hm, hi, he⟩
    · rintro ⟨hm, hi, he⟩
      exact ⟨⟨hm, hi, he ▸ (Nat.mem_divisors.mp hd).1⟩, he⟩
  rw [← Nat.card_eq_finsetCard, count]
  exact congrArg (fun t : Set K[X] => Nat.card t) heq

/-- Comparing degrees and grouping the monic factors by degree. -/
theorem degree_sum : DegreeSum.{u} := by
  intro K _ _ q n hq hn
  classical
  obtain ⟨s, hs, hprod⟩ :=
    UniversalFactorization.universal_factorization K q n hq hn
  have hqn : 1 < q ^ n :=
    Nat.one_lt_pow (Nat.ne_zero_of_lt hn) (hq ▸ Finite.one_lt_card)
  have hdeg : (X ^ (q ^ n) - X : K[X]).natDegree = q ^ n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hqn
  have hmap : ∀ f ∈ s, f.natDegree ∈ n.divisors := by
    intro f hf
    exact Nat.mem_divisors.mpr ⟨(hs f).mp hf |>.2.2, Nat.ne_zero_of_lt hn⟩
  calc
    q ^ n = ∑ f ∈ s, f.natDegree := by
      rw [← hdeg, hprod]
      exact natDegree_prod_of_monic s (fun f => f) (fun f hf => ((hs f).mp hf).1)
    _ = ∑ d ∈ n.divisors, ∑ f ∈ s with f.natDegree = d, f.natDegree :=
      (Finset.sum_fiberwise_of_maps_to hmap natDegree).symm
    _ = ∑ d ∈ n.divisors, d * count K d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ f ∈ s with f.natDegree = d, f.natDegree) =
            ∑ _f ∈ s with _f.natDegree = d, d := by
          apply Finset.sum_congr rfl
          intro f hf
          exact (Finset.mem_filter.mp hf).2
        _ = d * count K d := by
          rw [Finset.sum_const, smul_eq_mul, fiber_card K n d hd s hs, mul_comm]

/-- Möbius inversion is performed in ℚ before division by positive n. -/
theorem mobius_formula : MobiusFormula.{u} := by
  intro K _ _ q n hq hn
  have hsum : ∀ m > 0,
      (∑ d ∈ m.divisors, ((d : ℕ) : ℚ) * (count K d : ℚ)) = (q : ℚ) ^ m := by
    intro m hm
    exact_mod_cast (degree_sum K q m hq hm).symm
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℚ) * (q : ℚ) ^ b)] at hinv
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  change (count K n : ℚ) = _
  rw [hinv]
  field_simp [hnq]

end D07.Ch13.IrreducibleCount
