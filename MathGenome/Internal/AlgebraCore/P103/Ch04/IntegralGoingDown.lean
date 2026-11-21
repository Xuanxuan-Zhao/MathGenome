import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.IntegralGoingDown
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
Integral going down and finite descending-chain lifting (Theorem 4.8).
Mathlib's integral going-down instance uses minimal polynomials over an
integrally closed domain. It applies to arbitrary integral domain extensions,
without a finiteness, separability, characteristic, or normality condition.
-/

namespace P103.Ch04.IntegralGoingDown

theorem going_down : Specs.going_down := by
  intro R A _ _ _ _ _ g hinj hg p p' q' hp hp' hq' hle hcon
  let : Algebra R A := g.toAlgebra
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  let : Algebra.IsIntegral R A := ⟨hg⟩
  let : p.IsPrime := hp
  let : p'.IsPrime := hp'
  let : q'.IsPrime := hq'
  let : q'.LiesOver p' := ⟨hcon.symm⟩
  obtain ⟨q, hle, hq, hlo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := p') q' hle
  exact ⟨q, hle, hq, hlo.over.symm⟩

/-- Iterate going down, keeping the designated initial prime fixed. -/
theorem finite_chain_lift : Specs.finite_chain_lift := by
  intro R A _ _ _ _ _ g hinj hg n
  induction n with
  | zero =>
      intro p hp hm q₀ hq₀ hcon
      refine ⟨fun _ => q₀, rfl, fun _ => hq₀, fun _ _ _ => le_rfl, ?_⟩
      intro i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using hcon
  | succ n ih =>
      intro p hp hm q₀ hq₀ hcon
      obtain ⟨q₁, hle, hq₁, hcon₁⟩ :=
        going_down R A g hinj hg (p (0 : Fin (n + 1)).succ) (p 0) q₀
          (hp (0 : Fin (n + 1)).succ) (hp 0) hq₀ (hm (Fin.zero_le _)) hcon
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
              (hzero ▸ hmono (Fin.zero_le b)).trans hle
        · refine Fin.cases ?_ (fun b => ?_) j
          · intro h
            exact False.elim (Nat.not_succ_le_zero a.val h)
          · intro h
            simpa only [Fin.cons_succ] using hmono (Fin.succ_le_succ_iff.mp h)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using hcon
        · simpa only [Fin.cons_succ] using hcontract j

end P103.Ch04.IntegralGoingDown
