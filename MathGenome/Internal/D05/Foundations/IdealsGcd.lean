import MathGenome.Internal.Specs.D05.Foundations.IdealsGcd
import MathGenome.Internal.D05.Foundations.Division
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push

/-! Principal ideals and the terminating Euclidean algorithm of paper.tex:368.
The finite-run relation is independent of all correctness claims. -/

noncomputable section

namespace D05.Foundations.IdealsGcd

open D05.Foundations

variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- Normalization leaves the principal ideal unchanged. -/
theorem span_normalize (p : Polynomial K) :
    Ideal.span {normalize p} = Ideal.span {p} :=
  Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated p)

/-- The chosen monic gcd generates exactly the two-generated ideal, even at zero. -/
theorem span_monicGcd (a b : Polynomial K) :
    Ideal.span {monicGcd a b} = Ideal.span {a, b} := by
  classical
  exact (span_normalize _).trans (EuclideanDomain.span_gcd a b)

theorem monicGcd_dvd_left (a b : Polynomial K) : monicGcd a b ∣ a := by
  classical
  exact normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left a b)

theorem monicGcd_dvd_right (a b : Polynomial K) : monicGcd a b ∣ b := by
  classical
  exact normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right a b)

theorem dvd_monicGcd {a b c : Polynomial K} (ha : c ∣ a) (hb : c ∣ b) :
    c ∣ monicGcd a b := by
  classical
  exact dvd_normalize_iff.mpr (EuclideanDomain.dvd_gcd ha hb)

theorem monicGcd_monic {a b : Polynomial K} (h : a ≠ 0 ∨ b ≠ 0) :
    (monicGcd a b).Monic := by
  classical
  apply Polynomial.monic_normalize
  intro hz
  obtain ⟨ha, hb⟩ := EuclideanDomain.gcd_eq_zero_iff.mp hz
  rcases h with h | h
  · exact h ha
  · exact h hb

/-- Monic generators of the same ideal agree. -/
theorem monic_generators_eq {d e : Polynomial K} (hd : d.Monic) (he : e.Monic)
    (h : Ideal.span {d} = Ideal.span {e}) : d = e :=
  Polynomial.eq_of_monic_of_associated hd he
    (Ideal.span_singleton_eq_span_singleton.mp h)

/-- Unique monic least-degree generator for every nonzero ideal. -/
theorem idealMonicGenerator : D05.Specs.IdealsGcd.idealMonicGenerator := by
  intro K _ I hI
  classical
  let p := Submodule.IsPrincipal.generator I
  have hp : p ≠ 0 := by
    intro hp
    exact hI ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hp)
  have hd : (normalize p).Monic := Polynomial.monic_normalize hp
  have hs : Ideal.span {normalize p} = I :=
    (span_normalize p).trans (Ideal.span_singleton_generator I)
  refine ⟨normalize p, ⟨hd, ?_, hs, ?_⟩, ?_⟩
  · rw [← hs]
    exact Ideal.subset_span (by simp)
  · intro f hf hf0
    have hdf : normalize p ∣ f := Ideal.mem_span_singleton.mp (hs.symm ▸ hf)
    exact Polynomial.natDegree_le_of_dvd hdf hf0
  · intro e he
    exact monic_generators_eq he.1 hd (he.2.2.1.trans hs.symm)

/-- All gcd properties, including Bézout and the full common-divisor direction. -/
theorem gcdProperties : D05.Specs.IdealsGcd.gcdProperties := by
  intro K _ a b h
  refine ⟨monicGcd_monic h, span_monicGcd a b,
    monicGcd_dvd_left a b, monicGcd_dvd_right a b,
    fun _ ha hb => dvd_monicGcd ha hb, ?_⟩
  have hm : monicGcd a b ∈ Ideal.span {a, b} := by
    rw [← span_monicGcd]
    exact Ideal.subset_span (by simp)
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hm
  exact ⟨u, v, huv.symm⟩

theorem gcdUnique : D05.Specs.IdealsGcd.gcdUnique := by
  intro K _ a b d hd hda hdb hgreat
  classical
  have h : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    have hd0 := hgreat 0 (by simp [h.1]) (by simp [h.2])
    exact hd.ne_zero (zero_dvd_iff.mp hd0)
  exact dvd_antisymm_of_normalize_eq hd.normalize_eq_self
    (monicGcd_monic h).normalize_eq_self
    (dvd_monicGcd hda hdb)
    (hgreat _ (monicGcd_dvd_left a b) (monicGcd_dvd_right a b))

theorem zeroGcd : D05.Specs.IdealsGcd.zeroGcd := by
  intro K _
  classical
  simp [monicGcd]

/-- The ideal is invariant under a Euclidean division step. -/
theorem span_remainder (a b : Polynomial K) :
    Ideal.span {b, a % b} = Ideal.span {a, b} := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, Ideal.span_pair_comm,
    Ideal.span_pair_sub_right_mul]

theorem remainderSize_decreases (a : Polynomial K) {b : Polynomial K} (hb : b ≠ 0) :
    remainderSize (a % b) < remainderSize b := by
  classical
  by_cases hr : a % b = 0
  · simp [remainderSize, hr, hb]
  · have hdeg := Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_mod_lt a hb)
    simp only [remainderSize, ite_eq_right hr, ite_eq_right hb]
    omega

theorem euclideanStep : D05.Specs.IdealsGcd.euclideanStep := by
  intro K _ a b hb
  refine ⟨remainderSize_decreases a hb, ?_, ?_, span_remainder a b⟩
  · by_cases hr : a % b = 0
    · exact Or.inl hr
    · exact Or.inr (Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_mod_lt a hb))
  · rw [EuclideanDomain.mod_eq_sub_mul_div, mul_comm b]

/-- Strong induction on the second polynomial's size gives an actual finite
run, with a bound on the number of divisions. -/
theorem euclideanTermination : D05.Specs.IdealsGcd.euclideanTermination := by
  intro K _ a b
  classical
  have termination : ∀ m (a b : Polynomial K), remainderSize b = m →
      ∃ d n, EuclideanRun a b d n ∧ n ≤ remainderSize b := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b hm
      by_cases hb : b = 0
      · subst b
        exact ⟨a, 0, EuclideanRun.stop a, Nat.zero_le _⟩
      · have hlt := remainderSize_decreases a hb
        obtain ⟨d, n, hrun, hn⟩ := ih (remainderSize (a % b)) (by omega) b (a % b) rfl
        exact ⟨d, n + 1, EuclideanRun.divide a b d n hb hrun, by omega⟩
  exact termination _ a b rfl

/-- Backward substitution keeps actual Bézout coefficients for the final value. -/
theorem run_span_bezout {a b d : Polynomial K} {n : ℕ} (h : EuclideanRun a b d n) :
    Ideal.span {d} = Ideal.span {a, b} ∧
    ∃ u v : Polynomial K, d = u * a + v * b := by
  induction h with
  | stop a =>
    exact ⟨(Ideal.span_pair_zero a).symm, 1, 0, by simp⟩
  | divide a b d n hb tail ih =>
    refine ⟨ih.1.trans (span_remainder a b), ?_⟩
    obtain ⟨u, v, huv⟩ := ih.2
    refine ⟨v, u - v * (a / b), ?_⟩
    rw [huv, EuclideanDomain.mod_eq_sub_mul_div]
    ring

/-- Normalization here is precisely multiplication by the inverse leading
coefficient, rather than an unspecified associated polynomial. -/
theorem normalize_eq_mul_inv_leadingCoeff {d : Polynomial K} (hd : d ≠ 0) :
    normalize d = d * Polynomial.C d.leadingCoeff⁻¹ := by
  classical
  rw [normalize_apply, Polynomial.coe_normUnit,
    CommGroupWithZero.coe_normUnit K (Polynomial.leadingCoeff_ne_zero.mpr hd)]

theorem euclideanRunCorrect : D05.Specs.IdealsGcd.euclideanRunCorrect := by
  intro K _ a b d n hrun
  classical
  obtain ⟨hs, hbez⟩ := run_span_bezout hrun
  have hzero : d = 0 ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro hd
      have ha : d ∣ a := Ideal.mem_span_singleton.mp (hs.symm ▸
        (Ideal.subset_span (by simp) : a ∈ Ideal.span {a, b}))
      have hb : d ∣ b := Ideal.mem_span_singleton.mp (hs.symm ▸
        (Ideal.subset_span (by simp) : b ∈ Ideal.span {a, b}))
      simpa [hd] using And.intro ha hb
    · rintro ⟨rfl, rfl⟩
      obtain ⟨u, v, huv⟩ := hbez
      simpa using huv
  refine ⟨hs, hbez, hzero, ?_⟩
  intro h
  have hd : d ≠ 0 := by
    intro hd
    obtain ⟨ha, hb⟩ := hzero.mp hd
    rcases h with h | h
    · exact h ha
    · exact h hb
  refine ⟨hd, Polynomial.monic_mul_leadingCoeff_inv hd, ?_⟩
  rw [← normalize_eq_mul_inv_leadingCoeff hd]
  exact monic_generators_eq (Polynomial.monic_normalize hd) (monicGcd_monic h)
    ((span_normalize d).trans (hs.trans (span_monicGcd a b).symm))

end D05.Foundations.IdealsGcd
