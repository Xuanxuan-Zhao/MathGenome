import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.UniformBound
import Mathlib.Analysis.Normed.Operator.Mul

/-!
Uniform Taylor error, K03.06.uniform_bound. We apply the real Lagrange
theorem to a fixed real projection of the remainder. All differentiations
are over ℝ. We retain the continuous endpoint derivative family rather
than differentiating an arbitrary exterior extension at the endpoints.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology BigOperators
universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict a compact derivative family to a closed subinterval. -/
theorem closedDerivativeFamily_mono {n : ℕ} {f : ℝ → F} {u v a b : ℝ}
    {D : ℕ → ℝ → F} (hD : ClosedDerivativeFamily n f u v D)
    (hI : Icc a b ⊆ Icc u v) : ClosedDerivativeFamily n f a b D := by
  exact ⟨hD.1.mono hI, fun j hj => (hD.2.1 j hj).mono hI,
    fun j hj t ht => (hD.2.2 j hj t (hI ht)).mono hI⟩

/-- A fixed real linear projection preserves all continuous endpoint jets. -/
theorem closedDerivativeFamily_comp_linear {n : ℕ} {f : ℝ → F} {u v : ℝ}
    {D : ℕ → ℝ → F} (hD : ClosedDerivativeFamily n f u v D)
    (L : F →L[ℝ] ℝ) :
    ClosedDerivativeFamily n (fun t => L (f t)) u v (fun j t => L (D j t)) := by
  refine ⟨fun t ht => congrArg L (hD.1 ht),
    fun j hj => L.continuous.comp_continuousOn (hD.2.1 j hj), ?_⟩
  intro j hj t ht
  exact L.hasFDerivAt.comp_hasDerivWithinAt t (hD.2.2 j hj t ht)

/-- The next interior derivative also commutes with a fixed real projection.
Existence, rather than continuity, of that derivative suffices. -/
theorem projected_next_derivative {n : ℕ} {f : ℝ → F} {u v : ℝ}
    {D : ℕ → ℝ → F} (hD : ClosedDerivativeFamily n f u v D)
    (hd : ∀ t ∈ Ioo u v, DifferentiableAt ℝ (RealIteratedDerivative n f) t)
    (L : F →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Ioo u v) :
    HasDerivAt (RealIteratedDerivative n (fun s => L (f s)))
      (L (RealIteratedDerivative (n+1) f t)) t := by
  have hP := closedDerivativeFamily_comp_linear hD L
  have hEq : EqOn (RealIteratedDerivative n (fun s => L (f s)))
      (fun s => L (RealIteratedDerivative n f s)) (Ioo u v) := by
    intro s hs
    calc
      _ = L (D n s) :=
        (closedDerivativeFamily_eq_interior n _ u v _ hP n le_rfl hs).symm
      _ = _ := congrArg L (closedDerivativeFamily_eq_interior n f u v D hD n le_rfl hs)
  have hder := L.hasFDerivAt.comp_hasDerivAt t (hd t ht).hasDerivAt
  rw [← realIteratedDerivative_succ] at hder
  exact hder.congr_of_eventuallyEq
    (hEq.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2))

/-- The real part after rotation by the phase of z norms z and is contractive.
For complex scalars this is Re(conj(z / |z|) * ·); the zero case uses zero. -/
theorem exists_scalar_norming_projection {K : Type u} [RCLike K] (z : K) :
    ∃ L : K →L[ℝ] ℝ, (∀ y, |L y| ≤ ‖y‖) ∧ L z = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  let c : K := star z / (‖z‖ : K)
  let L : K →L[ℝ] ℝ := (RCLike.reCLM : K →L[ℝ] ℝ).comp
    (ContinuousLinearMap.mul ℝ K c)
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : ‖c‖ = 1 := by simp [c, norm_div, hn]
  refine ⟨L, ?_, ?_⟩
  · intro y
    change |RCLike.re (c * y)| ≤ ‖y‖
    exact (RCLike.abs_re_le_norm _).trans_eq (by rw [norm_mul, hc, one_mul])
  · have hcz : c * z = (‖z‖ : K) := by
      dsimp [c]
      rw [div_mul_eq_mul_div, RCLike.conj_mul]
      rw [sq, mul_div_cancel_right₀ _ (RCLike.ofReal_ne_zero.mpr hn)]
    change RCLike.re (c * z) = ‖z‖
    rw [hcz, RCLike.ofReal_re]

/-- Uniform on the entire compact interval, for real and complex values.
The order n may be zero, and M is allowed to depend on n. -/
theorem uniform_taylor_bound {K : Type u} [RCLike K]
    (f : ℝ → K) (n : ℕ) (u v M : ℝ) (D : ℕ → ℝ → K)
    (hD : ClosedDerivativeFamily n f u v D)
    (hd : ∀ t ∈ Ioo u v, DifferentiableAt ℝ (RealIteratedDerivative n f) t)
    (hM : ∀ t ∈ Ioo u v, ‖RealIteratedDerivative (n+1) f t‖ ≤ M)
    (a : ℝ) (ha : a ∈ Icc u v) (x : ℝ) (hx : x ∈ Icc u v) :
    ‖f x - ∑ k ∈ Finset.range (n+1),
      D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k‖ ≤
      M / ((n+1).factorial : ℝ) * |x-a|^(n+1) := by
  have hterm (k : ℕ) :
      D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k =
        ((x-a)^k / (k.factorial : ℝ)) • D k a := by
    simp only [Algebra.smul_def, map_div₀, map_pow, map_natCast]
    ring
  by_cases hax : a = x
  · subst x
    have hsum : (∑ k ∈ Finset.range (n+1),
        D k a / (k.factorial : K) * (algebraMap ℝ K (a-a))^k) = f a := by
      rw [Finset.sum_eq_single 0]
      · simpa using hD.1 ha
      · intro k hk hne
        simp [hne]
      · simp
    rw [hsum]
    simp
  have hI : Icc (min a x) (max a x) ⊆ Icc u v :=
    Icc_subset_Icc (le_min ha.1 hx.1) (max_le ha.2 hx.2)
  have hJ : uIoo a x ⊆ Ioo u v :=
    Ioo_subset_Ioo (le_min ha.1 hx.1) (max_le ha.2 hx.2)
  let z := f x - ∑ k ∈ Finset.range (n+1),
    D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k
  obtain ⟨L, hL, hz⟩ := exists_scalar_norming_projection z
  have hP := closedDerivativeFamily_comp_linear hD L
  obtain ⟨ξ, hξ, heq⟩ := lagrange_remainder (fun t => L (f t)) n a x
    (fun k t => L (D k t)) hax (closedDerivativeFamily_mono hP hI)
    (fun t ht => (projected_next_derivative hD hd L t (hJ ht)).differentiableAt)
  have hnext : RealIteratedDerivative (n+1) (fun t => L (f t)) ξ =
      L (RealIteratedDerivative (n+1) f ξ) := by
    rw [realIteratedDerivative_succ]
    exact (projected_next_derivative hD hd L ξ (hJ hξ)).deriv
  have hpoly : (∑ k ∈ Finset.range (n+1),
      L (D k a) / (k.factorial : ℝ) * (x-a)^k) =
      L (∑ k ∈ Finset.range (n+1),
        D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm, map_smul]
    simp only [smul_eq_mul]
    ring
  have hrem : ‖z‖ = L (RealIteratedDerivative (n+1) f ξ) * (x-a)^(n+1) /
      ((n+1).factorial : ℝ) := by
    rw [hnext, hpoly, ← map_sub] at heq
    exact hz.symm.trans heq
  have hdBound : |L (RealIteratedDerivative (n+1) f ξ)| ≤ M :=
    (hL _).trans (hM ξ (hJ hξ))
  have hfac : (0 : ℝ) ≤ ((n+1).factorial : ℝ) := by positivity
  calc
    ‖z‖ = |‖z‖| := (abs_of_nonneg (norm_nonneg z)).symm
    _ = |L (RealIteratedDerivative (n+1) f ξ)| * |x-a|^(n+1) /
        ((n+1).factorial : ℝ) := by
      rw [hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg hfac]
    _ ≤ M * |x-a|^(n+1) / ((n+1).factorial : ℝ) := by
      gcongr
    _ = M / ((n+1).factorial : ℝ) * |x-a|^(n+1) := by ring

/-- The estimate expressed with canonical within Taylor coefficients, without
choosing a derivative family in the statement. -/
theorem uniform_taylor_bound_within {K : Type u} [RCLike K]
    (f : ℝ → K) (n : ℕ) (u v M : ℝ) (hf : CkOnClosed n f u v)
    (hd : ∀ t ∈ Ioo u v, DifferentiableAt ℝ (RealIteratedDerivative n f) t)
    (hM : ∀ t ∈ Ioo u v, ‖RealIteratedDerivative (n+1) f t‖ ≤ M)
    (a : ℝ) (ha : a ∈ Icc u v) (x : ℝ) (hx : x ∈ Icc u v) :
    ‖f x - taylorWithinEval f n (Icc u v) a x‖ ≤
      M / ((n+1).factorial : ℝ) * |x-a|^(n+1) := by
  by_cases hax : a = x
  · subst x
    simp
  have huv : u < v := by
    by_contra h
    have hvu : v ≤ u := le_of_not_gt h
    have hau : a = u := le_antisymm (ha.2.trans hvu) ha.1
    have hxu : x = u := le_antisymm (hx.2.trans hvu) hx.1
    exact hax (hau.trans hxu.symm)
  obtain ⟨D, hD⟩ := hf
  have hpoly : taylorWithinEval f n (Icc u v) a x =
      ∑ k ∈ Finset.range (n+1),
        D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← closedDerivativeFamily_eq_iteratedDerivWithin n f u v huv D hD k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) ha]
    simp only [Algebra.smul_def, map_mul, map_inv₀, map_pow, map_natCast]
    ring
  rw [hpoly]
  exact uniform_taylor_bound f n u v M D hD hd hM a ha x hx

end SingleVariableAnalysis
