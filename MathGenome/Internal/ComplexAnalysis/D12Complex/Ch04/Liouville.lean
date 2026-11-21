import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.Liouville
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion

/-! Liouville's theorem from the local disk estimate and the previously
proved zero-derivative theorem. No global cycle Cauchy theorem is used. -/

namespace D12Complex.Liouville

/-- Cauchy's estimate on arbitrarily large disks forces the derivative to vanish. -/
theorem deriv_eq_zero_of_bounded_entire (f : ℂ → ℂ) (M : ℝ)
    (hf : HolomorphicOn Set.univ f) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ M) (a : ℂ) : deriv f a = 0 := by
  apply norm_eq_zero.mp
  by_contra hn
  have hd : 0 < ‖deriv f a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let r : ℝ := (M + 1) / ‖deriv f a‖
  have hr : 0 < r := div_pos (by linarith) hd
  have hest := DiskCauchyDerivatives.disk_cauchy_estimate a r Set.univ f M hr hf
    (Set.subset_univ _) (fun w _ => hbound w) 1
  have hest' : ‖deriv f a‖ ≤ M / r := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one,
      one_mul, pow_one] using hest
  have hmul := (le_div_iff₀ hr).mp hest'
  have hcancel : r * ‖deriv f a‖ = M + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  nlinarith

/-- The preliminary Liouville theorem, also reused in Chapter 6. -/
theorem bounded_entire_constant :
    Specs.D12Complex.Ch04.Liouville.bounded_entire_constant_type := by
  intro f M hf hM hbound
  have hdomain : IsDomain (Set.univ : Set ℂ) :=
    ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  obtain ⟨c, hc⟩ := Primitives.zero_derivative_constant Set.univ f hdomain hf
    (fun z _ => deriv_eq_zero_of_bounded_entire f M hf hM hbound z)
  exact ⟨c, fun z => hc z (Set.mem_univ z)⟩

end D12Complex.Liouville
