import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.KrullIntersection
import MathGenome.Internal.AlgebraCore.P103.Ch07.ArtinRees
import MathGenome.Internal.AlgebraCore.P103.Ch07.Nakayama
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness
import Mathlib.Tactic.NormNum

namespace P103.Ch07.KrullIntersection

open P103.Specs.Ch07.KrullIntersection

/-- Apply Artin–Rees to the intersection at c+1. Both intersections in
that equality are N itself, since N lies in every filtration term. -/
theorem stable : stableType := by
  intro R _ _ I M _ _ _
  let N : Submodule R M := ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)
  have hN (n : ℕ) : (I ^ n • (⊤ : Submodule R M)) ⊓ N = N :=
    inf_eq_right.mpr (iInf_le _ n)
  obtain ⟨c, hc⟩ := P103.Ch07.ArtinRees.artin_rees R I M N
  have h := hc (c + 1) (Nat.le_succ c)
  simpa only [hN, Nat.add_sub_cancel_left, pow_one] using h.symm

/-- Finite generation of the intersection gives one annihilator for all
its elements; no Jacobson or torsion condition is used. -/
theorem annihilator : annihilatorType := by
  intro R _ _ I M _ _ _
  let N : Submodule R M := ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)
  have hfg : N.FG := (P103.Ch05.NoetherianFiniteness.submodule_finiteness R M N).1
  obtain ⟨r, hr, hkill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hfg
      (stable R I M).ge
  refine ⟨1 - r, ?_, ?_⟩
  · simpa only [neg_sub] using I.neg_mem hr
  · intro x hx
    simpa only [sub_sub_cancel] using hkill x hx

theorem jacobson_vanishing : jacobson_vanishingType := by
  intro R _ _ I M _ _ _ hI
  obtain ⟨a, ha, hkill⟩ := annihilator R I M
  have hu := P103.Ch07.Nakayama.one_sub_isUnit R a (hI ha)
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  exact hu.smul_left_cancel.mp (by simpa only [smul_zero] using hkill x hx)

/-- Here M=R: the library domain theorem has no Jacobson hypothesis. -/
theorem domain_vanishing : domain_vanishingType := by
  intro R _ _ _ I hI
  exact I.iInf_pow_eq_bot_of_isDomain hI

theorem integer_counterexample : integer_counterexampleType := by
  let I : Ideal ℤ := Ideal.span {(2 : ℤ)}
  change I ≠ ⊤ ∧ Module.Finite ℤ (ZMod 3) ∧ _
  have htwo : I • (⊤ : Submodule ℤ (ZMod 3)) = ⊤ := by
    apply top_unique
    intro x _
    have hx : (2 : ℤ) • ((2 : ℤ) • x) = x := by
      rw [smul_smul, zsmul_eq_mul]
      change (4 : ZMod 3) * x = x
      change (1 : ZMod 3) * x = x
      exact one_mul x
    rw [← hx]
    exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top
  have hp (n : ℕ) : I ^ n • (⊤ : Submodule ℤ (ZMod 3)) = ⊤ := by
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ n ih => rw [pow_succ, mul_smul, htwo, ih]
  have hi : (⨅ n : ℕ, I ^ n • (⊤ : Submodule ℤ (ZMod 3))) = ⊤ := by
    simp only [hp, iInf_const]
  refine ⟨?_, ?_, hp, hi, ?_⟩
  · change Ideal.span {(2 : ℤ)} ≠ ⊤
    intro h
    have hu := Ideal.span_singleton_eq_top.mp h
    norm_num [Int.isUnit_iff] at hu
  · infer_instance
  · rw [hi]
    exact top_ne_bot

end P103.Ch07.KrullIntersection
