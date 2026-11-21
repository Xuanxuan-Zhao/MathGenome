import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.CompatibleCRT
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.LinearDiophantine

namespace P203.Ch01
open P203Specs.Ch01

universe u

/-- Two compatible congruences, without any coprimality restriction. -/
theorem compatibleCRT_pair (m n a b : ℤ)
    (h : (Int.gcd m n : ℤ) ∣ a - b) :
    ∃ x : ℤ, m ∣ x - a ∧ n ∣ x - b := by
  obtain ⟨t, v, htv⟩ := (linearSolvability m n (b-a)).mpr (by
    simpa only [neg_sub] using dvd_neg.mpr h)
  refine ⟨a + m*t, ?_, ?_⟩
  · exact ⟨t, by ring⟩
  · refine ⟨-v, ?_⟩
    linear_combination htv

/-- The gcd with a finite lcm divides a number if the gcd with every
individual modulus does. Prime valuations give the distributive step. -/
theorem gcd_lcm_dvd (a b n c : ℤ)
    (ha : (Int.gcd a n : ℤ) ∣ c) (hb : (Int.gcd b n : ℤ) ∣ c) :
    (Int.gcd (Int.lcm a b : ℤ) n : ℤ) ∣ c := by
  apply (valuationDivisibility.1 _ _).mpr
  intro p hp
  have ha' := (valuationDivisibility.1 _ _).mp ha p hp
  have hb' := (valuationDivisibility.1 _ _).mp hb p hp
  rw [(valuationGcdLcm p hp a n).1] at ha'
  rw [(valuationGcdLcm p hp b n).1] at hb'
  rw [(valuationGcdLcm p hp (Int.lcm a b : ℤ) n).1,
    (valuationGcdLcm p hp a b).2, min_max_distrib_right]
  exact max_le ha' hb'

theorem gcd_finite_lcm_dvd {ι : Type u} (s : Finset ι) (m : ι → ℤ)
    (n c : ℤ) (h : ∀ i ∈ s, (Int.gcd (m i) n : ℤ) ∣ c) :
    (Int.gcd (s.lcm m) n : ℤ) ∣ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.lcm_insert]
    exact gcd_lcm_dvd (m i) (s.lcm m) n c (h i (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- The induction works even for signed or zero moduli. -/
theorem compatibleCRT_exists {ι : Type u} (s : Finset ι) (m a : ι → ℤ)
    (h : ∀ i ∈ s, ∀ j ∈ s, (Int.gcd (m i) (m j) : ℤ) ∣ a i - a j) :
    ∃ x : ℤ, CRTSolution s m a x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [CRTSolution]⟩
  | @insert k s hk ih =>
    obtain ⟨y, hy⟩ := ih (fun i hi j hj => h i (by simp [hi]) j (by simp [hj]))
    have hc : (Int.gcd (s.lcm m) (m k) : ℤ) ∣ y - a k := by
      apply gcd_finite_lcm_dvd
      intro i hi
      have h₁ : (Int.gcd (m i) (m k) : ℤ) ∣ y - a i :=
        (Int.gcd_dvd_left _ _).trans (hy i hi)
      have h₂ := h i (by simp [hi]) k (by simp)
      convert dvd_add h₁ h₂ using 1; ring
    obtain ⟨x, hxy, hxk⟩ := compatibleCRT_pair (s.lcm m) (m k) y (a k) hc
    refine ⟨x, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hxk
    · have hx : m i ∣ x-y := (Finset.dvd_lcm hi).trans hxy
      convert dvd_add hx (hy i hi) using 1; ring

theorem compatibleCRTExistence : CompatibleCRTExistence.{u} := by
  intro ι s m a _
  constructor
  · rintro ⟨x, hx⟩ i hi j hj
    have h₁ : (Int.gcd (m i) (m j) : ℤ) ∣ x-a i :=
      (Int.gcd_dvd_left _ _).trans (hx i hi)
    have h₂ : (Int.gcd (m i) (m j) : ℤ) ∣ x-a j :=
      (Int.gcd_dvd_right _ _).trans (hx j hj)
    convert dvd_sub h₂ h₁ using 1; ring
  · exact compatibleCRT_exists s m a

theorem compatibleCRTSolutions : CompatibleCRTSolutions.{u} := by
  intro ι s m a _ x₀ h₀ x
  constructor
  · intro hx
    have hd : s.lcm m ∣ x-x₀ := Finset.lcm_dvd fun i hi => by
      convert dvd_sub (hx i hi) (h₀ i hi) using 1; ring
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by dsimp [finiteCRTLcm]; linear_combination ht⟩
  · rintro ⟨t, rfl⟩ i hi
    have hd : m i ∣ finiteCRTLcm s m * t :=
      dvd_mul_of_dvd_left (Finset.dvd_lcm hi) t
    convert dvd_add (h₀ i hi) hd using 1; ring

theorem compatibleCRTLcm : CompatibleCRTLcm.{u} := by
  constructor
  · intro ι s m hm
    have hnonneg : 0 ≤ s.lcm m :=
      Int.nonneg_of_normalize_eq_self (Finset.normalize_lcm (s := s) (f := m))
    have hne : s.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun i hi => (hm i hi).ne'
    exact ⟨lt_of_le_of_ne hnonneg (Ne.symm hne), fun z => Finset.lcm_dvd_iff⟩
  · intro ι m
    rfl

end P203.Ch01
