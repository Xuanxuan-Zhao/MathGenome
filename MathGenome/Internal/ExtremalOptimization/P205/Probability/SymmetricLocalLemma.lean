import MathGenome.Internal.ExtremalOptimization.P205.Probability.AsymmetricLocalLemma
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.SymmetricLocalLemma
import Mathlib.Tactic.FieldSimp

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace P205.Probability

/-- An exponential choice of the common local-lemma parameter, valid also
when the degree bound is zero. -/
private theorem symmetric_coefficient (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (hn : ((n : ℝ) + 1) * t ≤ 1) :
    t * Real.exp (-1) ≤ (1 - Real.exp (-t)) * Real.exp (-t) ^ n := by
  have hfirst : t ≤ Real.exp t - 1 := by
    linarith [Real.add_one_le_exp t]
  have hsecond : Real.exp (-1) ≤ Real.exp (-((n : ℝ) + 1) * t) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    t * Real.exp (-1) ≤
        (Real.exp t - 1) * Real.exp (-((n : ℝ) + 1) * t) :=
      mul_le_mul hfirst hsecond (Real.exp_pos _).le (by linarith)
    _ = (1 - Real.exp (-t)) * Real.exp (-t) ^ n := by
      rw [← Real.exp_nat_mul]
      simp only [sub_mul, one_mul, ← Real.exp_add]
      congr 1 <;> congr 1 <;> ring

/-- Finite symmetric Lovász local lemma, with no positive-degree or nonempty
family assumption (Corollary 6.3, p205:W29). -/
theorem symmetricLocalLemma : Specs.P205.Probability.SymmetricLocalLemmaType.{u, v} := by
  intro I _ Ω _ μ _ A D d p hD hdegree hp hprob hsmall
  let t : ℝ := 1 / ((d : ℝ) + 1)
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hdt : ((d : ℝ) + 1) * t = 1 := by
    dsimp [t]
    field_simp
  have hcancel : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpbound : p ≤ t * Real.exp (-1) := by
    have h := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (-1)).le
    have hpd : p * ((d : ℝ) + 1) ≤ Real.exp (-1) := by
      calc
        p * ((d : ℝ) + 1) =
            (Real.exp 1 * Real.exp (-1)) * (p * ((d : ℝ) + 1)) := by
          rw [hcancel, one_mul]
        _ = Real.exp 1 * p * ((d : ℝ) + 1) * Real.exp (-1) := by ring
        _ ≤ 1 * Real.exp (-1) := h
        _ = Real.exp (-1) := one_mul _
    calc
      p = (p * ((d : ℝ) + 1)) * t := by rw [mul_assoc, hdt, mul_one]
      _ ≤ Real.exp (-1) * t := mul_le_mul_of_nonneg_right hpd ht.le
      _ = t * Real.exp (-1) := mul_comm _ _
  let x : ℝ := 1 - Real.exp (-t)
  have hx : 0 ≤ x ∧ x < 1 := by
    dsimp [x]
    constructor
    · have he : Real.exp (-t) ≤ 1 := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        linarith
      linarith
    · linarith [Real.exp_pos (-t)]
  have hlocal : ∀ i, μ.real (A i) ≤ x *
      ∏ j ∈ Finset.univ.filter (D.Adj i), (1 - x) := by
    intro i
    have hn : (((Finset.univ.filter (D.Adj i)).card : ℝ) + 1) * t ≤ 1 := by
      have hc : ((Finset.univ.filter (D.Adj i)).card : ℝ) ≤ (d : ℝ) :=
        Nat.cast_le.mpr (hdegree i)
      nlinarith [mul_le_mul_of_nonneg_right (add_le_add_right hc 1) ht.le]
    have hb := symmetric_coefficient t ht.le (Finset.univ.filter (D.Adj i)).card hn
    calc
      μ.real (A i) ≤ p := hprob i
      _ ≤ t * Real.exp (-1) := hpbound
      _ ≤ x * ∏ j ∈ Finset.univ.filter (D.Adj i), (1 - x) := by
        simpa [x] using hb
  have h := asymmetricLocalLemma μ A D (fun _ => x) hD (fun _ => hx) hlocal
  exact lt_of_lt_of_le h.2 h.1

end P205.Probability
