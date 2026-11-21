import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import MathGenome.Internal.MultivariableAnalysis.D04.C02.SegmentMeanValue
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.TaylorBounds
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Lagrange
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set
open scoped BigOperators
namespace D04
open SingleVariableAnalysis.Riemann
open private riemann_weighted_constant from MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorIntegral

/-- A scalar line jet, including its endpoint values, gives the scalar remainder. -/
theorem scalar_taylor_lagrange : Specs.D04.C03.TaylorBounds.scalar_taylor_lagrangeType := by
  intro n k U f a h hU hf hseg _
  let F : ℝ → ℝ := fun t => f (a+t•h)
  let D : ℕ → ℝ → ℝ := fun j t => differentialDiagonal (higherDifferential j f (a+t•h)) h
  have htimes (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    crOn_timesDifferentiableAt (k+1) U f hU hf (a+t•h) (hseg t ht)
  have hfamily : SingleVariableAnalysis.ClosedDerivativeFamily k F 0 1 D := by
    refine ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro j hj t ht
      have hc := (crOn_iff_contDiffOn (k+1) U f hU).mp hf
      have hd := (hc.contDiffAt (hU.mem_nhds (hseg t ht))).iteratedFDeriv_right
        (i := j) (m := 0) (by simp only [zero_add]; exact_mod_cast (hj.trans (Nat.le_succ k)))
      exact (((hd.continuousAt.comp (x := t) (by fun_prop)).eval_const
        (fun _ => h))).continuousWithinAt
    · intro j hj t ht
      exact (differentialDiagonal_line_hasDerivAt j U f a h t
        (timesDifferentiableAt_of_le (Nat.succ_le_succ (Nat.le_of_lt hj)) U f _
          (htimes t ht))).hasDerivWithinAt
  have hd (t : ℝ) (ht : t ∈ uIoo (0 : ℝ) 1) :
      DifferentiableAt ℝ (SingleVariableAnalysis.RealIteratedDerivative k F) t := by
    have ht : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact (lineRestriction_hasDerivAt k U f a h t (htimes t ⟨ht.1.le, ht.2.le⟩)).differentiableAt
  obtain ⟨t, ht, he⟩ := SingleVariableAnalysis.lagrange_remainder F k 0 1 D
    (by norm_num) (by simpa using hfamily) hd
  have ht : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
  refine ⟨t, ht, ?_⟩
  have hj := lineRestriction_iteratedDeriv (k+1) U f a h t (htimes t ⟨ht.1.le, ht.2.le⟩)
  change iteratedDeriv (k+1) F t = D (k+1) t at hj
  change F 1 - _ = _ at he
  change F 1 - _ = iteratedDeriv (k+1) F t * _ / _ at he
  rw [hj] at he
  simpa [F, D, taylorRemainder, taylorPolynomial,
    Specs.D04.C03.HigherInterfaces.Model.taylorRemainder,
    Specs.D04.C03.HigherInterfaces.Model.taylorPolynomial, div_eq_mul_inv, mul_comm] using he

/-- The integral estimate first bounds the top diagonal, so it also applies
when a sharper coordinate estimate is available. -/
theorem taylor_remainder_diagonal_bound {n m : ℕ} (k : ℕ)
    (U : Set (E n)) (f : E n → E m) (a h : E n) (B : ℝ)
    (hU : IsOpen U) (hf : CrOn (k+1) U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a+t•h ∈ U)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖differentialDiagonal (higherDifferential (k+1) f (a+t•h)) h‖ ≤ B) :
    ‖taylorRemainder k f a h‖ ≤ B / ((k+1).factorial : ℝ) := by
  let v : ℝ → E m := fun t =>
    (1-t)^k • differentialDiagonal (higherDifferential (k+1) f (a+t•h)) h
  have hc : ContinuousOn v (Icc 0 1) :=
    ((continuous_const.sub continuous_id).pow k).continuousOn.smul
      (higherDifferential_line_continuous (k+1) (k+1) U f a h hU hf hseg le_rfl)
  obtain ⟨hv, he⟩ := taylor_remainder_integral k U f a h hU hf hseg
  obtain ⟨hn, hnorm⟩ := norm_vectorRiemannIntegral_le v (by norm_num) hc hv
  have hw : RealIntegrable (fun t : ℝ => (1-t)^k * B) 0 1 := by
    apply real_continuous_integrable _ (by norm_num)
    intro t ht
    apply (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
    exact (show Continuous (fun t : ℝ => (1-t)^k * B) by fun_prop).continuousWithinAt
  have hm := realIntegral_mono _ _ hn hw (fun t ht => by
    have ht0 : 0 ≤ (1-t)^k := pow_nonneg (sub_nonneg.mpr ht.2) k
    simpa only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] using
      mul_le_mul_of_nonneg_left (hB t ht) ht0)
  have hwval := riemann_weighted_constant k B hw
  change realIntegral _ hn ≤ realIntegral _ hw at hm
  rw [hwval] at hm
  change taylorRemainder k f a h = (k.factorial : ℝ)⁻¹ • vectorRiemannIntegral v hv at he
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  calc
    (k.factorial : ℝ)⁻¹ * ‖vectorRiemannIntegral v hv‖ ≤
        (k.factorial : ℝ)⁻¹ * (B / (k+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hm) (by positivity)
    _ = B / ((k+1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, Nat.cast_add, Nat.cast_one]
      ring

theorem taylor_remainder_bound : Specs.D04.C03.TaylorBounds.taylor_remainder_boundType := by
  intro n m k U f a h M hU hf hseg hM
  apply taylor_remainder_diagonal_bound k U f a h (M * ‖h‖^(k+1)) hU hf hseg
  intro t ht
  calc
    ‖differentialDiagonal (higherDifferential (k+1) f (a+t•h)) h‖ ≤
        ‖higherDifferential (k+1) f (a+t•h)‖ * ∏ _ : Fin (k+1), ‖h‖ :=
      (higherDifferential (k+1) f (a+t•h)).le_opNorm _
    _ ≤ M * ‖h‖^(k+1) := by
      simpa using mul_le_mul_of_nonneg_right (hM t ht) (pow_nonneg (norm_nonneg h) (k+1))

theorem taylor_bounds_dimension_zero : Specs.D04.C03.TaylorBounds.taylor_bounds_dimension_zeroType := by
  intro m k f a h
  exact ⟨Subsingleton.elim h 0, taylorRemainder_dimension_zero k f a h⟩

theorem vector_taylor_lagrange_failure : Specs.D04.C03.TaylorBounds.vector_taylor_lagrange_failureType := by
  constructor
  · apply (crOn_iff_contDiffOn 1 Set.univ _ isOpen_univ).mpr
    apply ContDiff.contDiffOn
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i <;>
      change ContDiff ℝ 1 (fun t : ℝ => t ^ _) <;> fun_prop
  rintro ⟨t, ht, he⟩
  apply vector_mean_value_no_common_point
  refine ⟨t, ht, ?_⟩
  change taylorRemainder 0 meanValueCounterexample 0 1 =
    iteratedFDeriv ℝ 1 meanValueCounterexample t (fun _ => (1 : ℝ)) at he
  erw [iteratedFDeriv_one_apply] at he
  change meanValueCounterexample (0+1) - taylorPolynomial 0 meanValueCounterexample 0 1 = _ at he
  erw [taylorPolynomial_zero] at he
  change meanValueCounterexample 1 - meanValueCounterexample 0 =
    (fderiv ℝ meanValueCounterexample t) (1-0)
  simpa only [zero_add, sub_zero] using he

/-- Basis expansion turns coefficient bounds into the sharp coordinate ℓ¹ bound. -/
theorem differentialDiagonal_coordinate_bound {n q : ℕ}
    (T : Differential (E n) ℝ q) (h : E n) (C : ℝ)
    (hT : ∀ j : Fin q → Fin n, |differentialCoefficients q T j| ≤ C) :
    |differentialDiagonal T h| ≤ C * (∑ i : Fin n, |h i|)^q := by
  classical
  change |T (fun _ => h)| ≤ _
  rw [differential_expansion]
  calc
    |∑ j : Fin q → Fin n, (∏ r, h (j r)) • differentialCoefficients q T j| ≤
        ∑ j : Fin q → Fin n, |(∏ r, h (j r)) • differentialCoefficients q T j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin q → Fin n, (∏ r, |h (j r)|) * C := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [smul_eq_mul, abs_mul, Finset.abs_prod] using
        mul_le_mul_of_nonneg_left (hT j) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = C * (∑ i : Fin n, |h i|)^q := by
      rw [← Finset.sum_mul]
      have he := Fintype.prod_sum (fun (_ : Fin q) (i : Fin n) => |h i|)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm] using
        congrArg (fun x : ℝ => x * C) he.symm

/-- Cauchy--Schwarz in the canonical Euclidean coordinates, including n=0. -/
theorem sum_abs_coordinates_le {n : ℕ} (h : E n) :
    (∑ i : Fin n, |h i|) ≤ Real.sqrt (n : ℝ) * ‖h‖ := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => |h i|)
    (fun _ => (1 : ℝ))
  simpa [sq_abs, norm_coordinates, mul_comm] using hh

theorem scalar_taylor_coordinate_bounds :
    Specs.D04.C03.TaylorBounds.scalar_taylor_coordinate_boundsType := by
  intro n k U f a h C hU hf hseg hC
  by_cases hn : n = 0
  · subst n
    have hh : h = 0 := Subsingleton.elim _ _
    rw [hh]
    change |taylorRemainder k f a 0| ≤ _ ∧ _
    rw [taylorRemainder_zero_increment]
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let i : Fin n := ⟨0, hnpos⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans
    (hC 0 (by constructor <;> norm_num) (fun _ => i))
  have hfirst : |taylorRemainder k f a h| ≤
      C * (∑ i : Fin n, |h i|)^(k+1) / ((k+1).factorial : ℝ) := by
    by_cases hh : h = 0
    · subst h
      simp [taylorRemainder_zero_increment]
    obtain ⟨t, ht, he⟩ := scalar_taylor_lagrange k U f a h hU hf hseg hh
    change taylorRemainder k f a h = differentialDiagonal
      (higherDifferential (k+1) f (a+t•h)) h / ((k+1).factorial : ℝ) at he
    rw [he, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply differentialDiagonal_coordinate_bound
    intro j
    rw [differentialCoefficients_apply, higherDifferential_basis (k+1) U f _
      (crOn_timesDifferentiableAt (k+1) U f hU hf _ (hseg t ⟨ht.1.le, ht.2.le⟩))]
    exact hC t ⟨ht.1.le, ht.2.le⟩ j
  refine ⟨hfirst, ?_⟩
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (sum_abs_coordinates_le h) (k+1)
  have hs : (Real.sqrt (n : ℝ))^(k+1) = (n : ℝ)^((k+1 : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  have hb := mul_le_mul_of_nonneg_left hp hC0
  rw [mul_pow, hs] at hb
  exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hb) (by positivity)

end D04
