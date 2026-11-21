import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Leibniz
import Mathlib.Data.Nat.Choose.Sum

/-!
# The higher product rule without continuity of the highest derivative

K03.04.leibniz, paper.tex:724–735. Induction differentiates the finite
binomial sum using first derivatives only. Local equality on the open domain
identifies its derivative with the next product derivative. Pascal's identity
is used in the finite-sum form `Finset.sum_choose_succ_mul`.
-/

namespace SingleVariableAnalysis

open Set
open scoped BigOperators
universe u

theorem leibniz_on_open
    {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
    (k : ℕ) (f g : ℝ → K) (I : Set ℝ) (hI : IsOpen I)
    (hf : KTimesDifferentiableOn k f I) (hg : KTimesDifferentiableOn k g I) :
    KTimesDifferentiableOn k (fun x => f x * g x) I ∧
      EqOn (RealIteratedDerivative k (fun x => f x * g x))
        (fun x => ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : K) * RealIteratedDerivative j f x *
            RealIteratedDerivative (k - j) g x) I := by
  induction k with
  | zero =>
    exact ⟨kTimesDifferentiableOn_zero _ _, by intro x hx; simp⟩
  | succ k ih =>
    obtain ⟨hprod, heq⟩ := ih
      (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    have hderiv (x : ℝ) (hx : x ∈ I) :
        HasDerivAt
          (fun y => ∑ j ∈ Finset.range (k + 1),
            (Nat.choose k j : K) * RealIteratedDerivative j f y *
              RealIteratedDerivative (k - j) g y)
          (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : K) *
            (RealIteratedDerivative (j + 1) f x * RealIteratedDerivative (k - j) g x +
              RealIteratedDerivative j f x * RealIteratedDerivative (k - j + 1) g x)) x := by
      apply HasDerivAt.fun_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hfj := (hf j (by omega) x hx).hasDerivAt
      have hgj := (hg (k - j) (by omega) x hx).hasDerivAt
      simpa only [← realIteratedDerivative_succ, Pi.mul_apply, mul_add, mul_assoc] using
        (hfj.mul hgj).const_mul (Nat.choose k j : K)
    have hnext (x : ℝ) (hx : x ∈ I) :=
      (hderiv x hx).congr_of_eventuallyEq
        (heq.eventuallyEq_of_mem (hI.mem_nhds hx))
    refine ⟨(kTimesDifferentiableOn_succ_iff k _ I).mpr
      ⟨hprod, fun x hx => (hnext x hx).differentiableAt⟩, ?_⟩
    intro x hx
    rw [realIteratedDerivative_succ, (hnext x hx).deriv]
    dsimp only
    simp_rw [mul_assoc]
    rw [Finset.sum_choose_succ_mul
      (fun i j => RealIteratedDerivative i f x * RealIteratedDerivative j g x) k]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [Nat.sub_add_comm hjk]

end SingleVariableAnalysis
