import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanNoEuclideanStructure
import MathGenome.Internal.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
import Mathlib.Order.WellFounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! No Euclidean structure on the fixed complex ring ℤ[(1+√(-19))/2].
The obstruction uses division at 2 and omega, and integer norms of their
differences with 0 and ±1. No special Euclidean function is assumed. -/

noncomputable section
namespace D07.Ch10.PidNotEuclideanNoEuclideanStructure

open PidNotEuclideanQuadraticIntegerNorm

theorem euclideanHasUniversalSideDivisor : Specs.EuclideanHasUniversalSideDivisor := by
  intro A _ _ hE hnonfield
  classical
  obtain ⟨smaller, hwf, hdiv⟩ := hE
  obtain ⟨u, hu, hmin⟩ := hwf.has_min {a : A | a ≠ 0 ∧ ¬ IsUnit a} hnonfield
  refine ⟨u, hu.1, hu.2, ?_⟩
  intro x
  obtain ⟨q, r, hqr, hr⟩ := hdiv x u hu.1
  refine ⟨r, ?_, q, ?_⟩
  · rcases hr with hr | hr
    · exact Or.inl hr
    · by_cases hzero : r = 0
      · exact Or.inl hzero
      · right
        by_contra hnunit
        exact hmin r ⟨hzero, hnunit⟩ hr
  · rw [hqr]
    ring

private def omegaElement : R :=
  ⟨omega, Subring.subset_closure (Set.mem_singleton omega)⟩

private lemma norm_integer (a : ℤ) : norm (a : R) = a ^ 2 := by
  have h := normFormula (a : R) a 0 (by simp [expression])
  simpa using h

private lemma norm_omega_sub_integer (a : ℤ) :
    norm (omegaElement - (a : R)) = a ^ 2 - a + 5 := by
  have h : ((omegaElement - (a : R) : R) : ℂ) = expression (-a) 1 := by
    simp [omegaElement, expression]
    ring
  rw [normFormula _ (-a) 1 h]
  ring

private lemma norm_dvd {u x : R} (h : u ∣ x) : norm u ∣ norm x := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨norm v, multiplicativeNorm.2.2 u v⟩

/-- The two test elements give relatively prime pairs of possible norms. -/
private lemma common_norm_divisor {n : ℤ}
    (h : n ∣ 1 ∨ n ∣ 4 ∨ n ∣ 9) (k : n ∣ 5 ∨ n ∣ 7) : n ∣ 1 := by
  rcases h with h | h | h
  · exact h
  · rcases k with k | k
    · exact dvd_sub k h
    · exact dvd_sub (dvd_mul_of_dvd_right h 2) k
  · rcases k with k | k
    · exact dvd_sub (dvd_mul_of_dvd_right k 2) h
    · exact dvd_sub (dvd_mul_of_dvd_right k 4)
        (dvd_mul_of_dvd_right h 3)

theorem noUniversalSideDivisor : Specs.NoUniversalSideDivisor := by
  rintro ⟨u, _, hunit, hall⟩
  have hn2 : norm (2 : R) = 4 := by simpa using norm_integer 2
  have hn3 : norm (3 : R) = 9 := by simpa using norm_integer 3
  have hnω : norm omegaElement = 5 := by simpa using norm_omega_sub_integer 0
  have hnωm : norm (omegaElement - 1) = 5 := by simpa using norm_omega_sub_integer 1
  have hnωp : norm (omegaElement + 1) = 7 := by
    simpa using norm_omega_sub_integer (-1)
  have htwo : norm u ∣ 1 ∨ norm u ∣ 4 ∨ norm u ∣ 9 := by
    obtain ⟨ε, hε, hd⟩ := hall 2
    rcases hε with rfl | hε
    · right; left
      simpa [hn2] using (norm_dvd hd : norm u ∣ norm (2 - 0))
    · rcases (units ε).mp hε with rfl | rfl
      · left
        have he : (2 : R) - 1 = 1 := by ring
        simpa only [he, multiplicativeNorm.2.1] using norm_dvd hd
      · right; right
        have he : (2 : R) - -1 = 3 := by ring
        simpa only [he, hn3] using norm_dvd hd
  have homega : norm u ∣ 5 ∨ norm u ∣ 7 := by
    obtain ⟨ε, hε, hd⟩ := hall omegaElement
    rcases hε with rfl | hε
    · left
      simpa only [sub_zero, hnω] using norm_dvd hd
    · rcases (units ε).mp hε with rfl | rfl
      · left
        simpa only [hnωm] using norm_dvd hd
      · right
        simpa only [sub_neg_eq_add, hnωp] using norm_dvd hd
  have hn : norm u = 1 :=
    Int.eq_one_of_dvd_one (positiveNorm.1 u) (common_norm_divisor htwo homega)
  exact hunit ((units u).mpr ((normOne u).mp hn))

theorem notEuclidean : Specs.NotEuclidean := by
  intro hE
  apply noUniversalSideDivisor
  apply euclideanHasUniversalSideDivisor R hE
  refine ⟨2, ?_, ?_⟩
  · norm_num
  · intro hu
    rcases (units (2 : R)).mp hu with h | h <;> norm_num at h

end D07.Ch10.PidNotEuclideanNoEuclideanStructure
