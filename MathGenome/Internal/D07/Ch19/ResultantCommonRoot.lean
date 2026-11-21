import MathGenome.Internal.Specs.D07.Ch19.ResultantCommonRoot
import MathGenome.Internal.D07.Ch19.ResultantDefinition
import Mathlib.Tactic.Linarith

universe u v
namespace D07.Ch19.ResultantCommonRoot
open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantCommonRoot

/-- The actual-degree determinant vanishes precisely for a non-coprime pair. -/
lemma ordinaryResultant_eq_zero_iff {F : Type u} [Field F] (f g : F[X]) (hf : f ≠ 0) :
    ordinaryResultant f g = 0 ↔ ¬ IsCoprime f g := by
  rw [ordinaryResultant, D07.Ch19.ResultantDefinition.resultantBridge
    F f g f.natDegree g.natDegree le_rfl le_rfl, Polynomial.resultant_eq_zero_iff]
  simp [hf]

lemma not_isCoprime_iff_common_divisor {F : Type u} [Field F]
    (f g : F[X]) (hf : f ≠ 0) :
    ¬ IsCoprime f g ↔ ∃ h : F[X], 0 < h.degree ∧ h ∣ f ∧ h ∣ g := by
  classical
  let := EuclideanDomain.gcdMonoid F[X]
  constructor
  · intro hc
    refine ⟨gcd f g, ?_, gcd_dvd_left f g, gcd_dvd_right f g⟩
    exact degree_pos_of_ne_zero_of_nonunit
      (fun hz => hf (zero_dvd_iff.mp (hz ▸ gcd_dvd_left f g)))
      (fun hu => hc ((gcd_isUnit_iff f g).mp hu))
  · rintro ⟨h, hh, hhf, hhg⟩ hc
    have hu := hc.isUnit_of_dvd' hhf hhg
    rw [isUnit_iff_degree_eq_zero] at hu
    simp [hu] at hh

theorem commonDivisorCriterion : CommonDivisorCriterion.{u} := by
  intro F _ f g hf hg hn hm
  exact (ordinaryResultant_eq_zero_iff f g hf).trans
    (not_isCoprime_iff_common_divisor f g hf)

theorem commonRootCriterion : CommonRootCriterion.{u,v} := by
  intro F Ω _ _ _ _ _ f g hf hg hn hm
  rw [ordinaryResultant_eq_zero_iff f g hf,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F Ω f g]
  push Not
  rfl

theorem boundedRelationCriterion : BoundedRelationCriterion.{u} := by
  intro F _ f g hf hg hn hm
  constructor
  · intro hr
    obtain ⟨h, hh, hhf, hhg⟩ :=
      (commonDivisorCriterion F f g hf hg hn hm).mp hr
    have hh0 : h ≠ 0 := by
      intro hz
      simp [hz] at hh
    have hfq : h * (f / h) = f := EuclideanDomain.mul_div_cancel' hh0 hhf
    have hgq : h * (g / h) = g := EuclideanDomain.mul_div_cancel' hh0 hhg
    refine ⟨g / h, -(f / h), ?_, ?_, Or.inl ?_, ?_⟩
    · simpa [degree_eq_natDegree hg] using degree_div_lt hg hh
    · simpa [degree_eq_natDegree hf] using degree_div_lt hf hh
    · intro hz
      rw [hz, mul_zero] at hgq
      exact hg hgq.symm
    · calc
        (g / h) * f + -(f / h) * g =
            (g / h) * (h * (f / h)) + -(f / h) * (h * (g / h)) := by rw [hfq, hgq]
        _ = 0 := by ring
  · rintro ⟨A, B, hA, hB, hne, hrel⟩
    apply (ordinaryResultant_eq_zero_iff f g hf).mpr
    intro hc
    have hdiv : f ∣ B * g := by
      refine ⟨-A, ?_⟩
      calc
        B * g = -(A * f) := eq_neg_of_add_eq_zero_right hrel
        _ = f * -A := by ring
    have hB0 : B = 0 := by
      by_contra hb
      have hd := degree_le_of_dvd (hc.dvd_of_dvd_mul_right hdiv) hb
      rw [degree_eq_natDegree hf] at hd
      exact (not_lt_of_ge hd) hB
    have hA0 : A = 0 := by
      rw [hB0, zero_mul, add_zero] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right hf
    exact hne.elim (fun h => h hA0) (fun h => h hB0)

theorem rationalCounterexample : RationalCounterexample := by
  constructor
  · rw [ordinaryResultant, D07.Ch19.ResultantDefinition.resultantBridge
      ℚ (X ^ 2 + 1) (X ^ 2 + 1) _ _ le_rfl le_rfl]
    apply Polynomial.resultant_self_eq_zero
    simp
  · intro x hx
    simp only [eval_add, eval_pow, eval_X, eval_one] at hx
    nlinarith [sq_nonneg x]

end D07.Ch19.ResultantCommonRoot
