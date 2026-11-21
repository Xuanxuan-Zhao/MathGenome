import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.GoingUp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Data.Fin.Tuple.Basic

/-! Going up and iteration along finite chains, Theorem 4.8.
The library one-step theorem uses lying over for the induced integral map
R / comap g q → A / q, then contracts the resulting prime to A.
It requires neither injectivity of g nor strict inclusion of the base primes.
-/

namespace P103.Ch04.GoingUp

theorem going_up : Specs.going_up := by
  intro R A _ _ g hg p p' q hp hp' hq hle hcon
  let : Algebra R A := g.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hg⟩
  let : p'.IsPrime := hp'
  let : q.IsPrime := hq
  exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p' q
    (by change Ideal.comap g q ≤ p'; rw [hcon]; exact hle)

/-- Repeatedly lift the first step, and apply induction to the remaining chain. -/
theorem finite_chain_lift : Specs.finite_chain_lift := by
  intro R A _ _ g hg n
  induction n with
  | zero =>
      intro p hp hm q₀ hq₀ hcon
      refine ⟨fun _ => q₀, rfl, fun _ => hq₀, fun _ _ _ => le_rfl, ?_⟩
      intro i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using hcon
  | succ n ih =>
      intro p hp hm q₀ hq₀ hcon
      obtain ⟨q₁, hle, hq₁, hcon₁⟩ := going_up R A g hg (p 0) (p (0 : Fin (n + 1)).succ) q₀
        (hp 0) (hp (0 : Fin (n + 1)).succ) hq₀ (hm (Fin.zero_le _)) hcon
      obtain ⟨q, hzero, hprime, hmono, hcontract⟩ :=
        ih (fun i => p i.succ) (fun i => hp i.succ)
          (fun _ _ hij => hm (Fin.succ_le_succ_iff.mpr hij)) q₁ hq₁ hcon₁
      refine ⟨Fin.cons q₀ q, Fin.cons_zero _ _, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using hq₀
        · simpa only [Fin.cons_succ] using hprime j
      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun a => ?_) i
        · intro _
          refine Fin.cases ?_ (fun b => ?_) j
          · exact le_rfl
          · simpa only [Fin.cons_zero, Fin.cons_succ] using
              hle.trans (hzero ▸ hmono (Fin.zero_le b))
        · refine Fin.cases ?_ (fun b => ?_) j
          · intro h
            exact False.elim (Nat.not_succ_le_zero a.val h)
          · intro h
            simpa only [Fin.cons_succ] using hmono (Fin.succ_le_succ_iff.mp h)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using hcon
        · simpa only [Fin.cons_succ] using hcontract j

end P103.Ch04.GoingUp
