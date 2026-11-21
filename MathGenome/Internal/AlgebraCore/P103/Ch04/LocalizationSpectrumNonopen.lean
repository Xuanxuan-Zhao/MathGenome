import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.LocalizationSpectrumNonopen
import Mathlib.Algebra.Group.Int.Units

open scoped nonZeroDivisors

namespace P103.Ch04.LocalizationSpectrumNonopen

theorem integerFractionRingImageNotOpen :
    Specs.P103.Ch04.LocalizationSpectrumNonopen.integerFractionRingImageNotOpen := by
  change ¬ IsOpen (Set.range
    (PrimeSpectrum.comap (algebraMap ℤ (FractionRing ℤ))))
  rw [PrimeSpectrum.localization_comap_range (FractionRing ℤ) (nonZeroDivisors ℤ)]
  intro hOpen
  have hGeneric : (⊥ : PrimeSpectrum ℤ) ∈
      {p : PrimeSpectrum ℤ | Disjoint (nonZeroDivisors ℤ : Set ℤ) p.asIdeal} := by
    change Disjoint (nonZeroDivisors ℤ : Set ℤ) (⊥ : PrimeSpectrum ℤ).asIdeal
    rw [PrimeSpectrum.asIdeal_bot]
    exact Set.disjoint_left.mpr fun _ hd hz =>
      (mem_nonZeroDivisors_iff_ne_zero.mp hd) (Ideal.mem_bot.mp hz)
  obtain ⟨_, ⟨n, rfl⟩, hn, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hOpen) _ hGeneric
  have hn0 : n ≠ 0 := by
    change n ∉ (⊥ : PrimeSpectrum ℤ).asIdeal at hn
    simpa only [PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hn
  -- A maximal ideal containing n² + 1 contains a nonzero denominator but avoids n.
  let d : ℤ := n ^ 2 + 1
  have hd : 1 < d := by
    dsimp [d]
    have hsq : 0 < n ^ 2 := sq_pos_of_ne_zero hn0
    omega
  have hNotUnit : ¬ IsUnit d := by
    rw [Int.isUnit_iff]
    omega
  obtain ⟨I, hMax, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hNotUnit)
  have hdI : d ∈ I := hle (Ideal.mem_span_singleton_self d)
  have hnI : n ∉ I := by
    intro hnI
    have hsqI : n ^ 2 ∈ I := by
      simpa only [pow_two] using I.mul_mem_left n hnI
    have hOne : (1 : ℤ) ∈ I := by
      have hSub := I.sub_mem hdI hsqI
      rwa [show d - n ^ 2 = 1 by dsimp [d]; omega] at hSub
    exact hMax.ne_top (I.eq_top_iff_one.mpr hOne)
  let q : PrimeSpectrum ℤ := ⟨I, hMax.isPrime⟩
  have hq : q ∈ PrimeSpectrum.basicOpen n := hnI
  have hDisjoint : Disjoint (nonZeroDivisors ℤ : Set ℤ) (I : Set ℤ) := hsub hq
  exact Set.disjoint_left.mp hDisjoint
    (mem_nonZeroDivisors_of_ne_zero (show d ≠ 0 by omega)) hdI

end P103.Ch04.LocalizationSpectrumNonopen
