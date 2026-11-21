import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExistenceFermat
import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorPeano
import MathGenome.Internal.MultivariableAnalysis.D04.C01.OperatorEstimates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.SecondOrderTests
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
namespace SecondOrder
open private hessian_basis from MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry

theorem diagonal_smul {n : ℕ} (T : Differential (E n) ℝ 2) (t : ℝ) (v : E n) :
    differentialDiagonal T (t • v) = t^2 * differentialDiagonal T v := by
  change T (fun _ => t • v) = t^2 * T (fun _ => v)
  rw [T.map_smul_univ (fun _ => t) (fun _ => v)]
  simp [pow_two]

theorem diagonal_zero {n : ℕ} (T : Differential (E n) ℝ 2) :
    differentialDiagonal T 0 = 0 := by
  simpa using diagonal_smul T 0 (0 : E n)

theorem taylor_two {n : ℕ} (f : E n → ℝ) (a h : E n) :
    taylorPolynomial 2 f a h = f a + totalDerivative f a h +
      (1/2 : ℝ) * differentialDiagonal (higherDifferential 2 f a) h := by
  change (∑ j ∈ Finset.range 3, _) = _
  rw [Finset.sum_range_succ]
  change taylorPolynomial 1 f a h + _ = _
  rw [taylorPolynomial_one]
  norm_num
  rfl

theorem remainder_bound {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TimesDifferentiableAt 2 U f a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : E n), |taylorRemainder 2 f a h| ≤ ε * ‖h‖^2 := by
  simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_norm] using
    (taylorPeano_succ 1 U f a hf).bound hε

theorem positive_lower_bound {n : ℕ} (T : Differential (E n) ℝ 2)
    (hT : ∀ v, v ≠ 0 → 0 < differentialDiagonal T v) :
    ∃ η > 0, ∀ h, η * ‖h‖^2 ≤ differentialDiagonal T h := by
  have hc : Continuous (fun v : E n => differentialDiagonal T v) :=
    T.cont.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨η, hη, hlow⟩ := (isCompact_sphere (0 : E n) 1).exists_forall_le'
    hc.continuousOn (fun v hv => hT v (by
      intro he
      simp [he] at hv))
  refine ⟨η, hη, fun h => ?_⟩
  by_cases hh : h = 0
  · simp [hh, diagonal_zero]
  · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hu : ‖h‖⁻¹ • h ∈ Metric.sphere (0 : E n) 1 := by
      simp [norm_smul, ne_of_gt hp]
    have hb := mul_le_mul_of_nonneg_right (hlow _ hu) (sq_nonneg ‖h‖)
    rw [diagonal_smul] at hb
    have hi : ‖h‖⁻¹ ^ 2 * ‖h‖^2 = 1 := by field_simp
    calc η * ‖h‖^2 ≤ ‖h‖⁻¹^2 * differentialDiagonal T h * ‖h‖^2 := hb
         _ = (‖h‖⁻¹^2 * ‖h‖^2) * differentialDiagonal T h := by ring
         _ = differentialDiagonal T h := by rw [hi, one_mul]

theorem timesDifferentiableAt_neg {n : ℕ} (k : ℕ) (U : Set (E n))
    (f : E n → ℝ) (a : E n) (hf : TimesDifferentiableAt k U f a) :
    TimesDifferentiableAt k U (-f) a := by
  induction k generalizing a with
  | zero => exact hf
  | succ k ih =>
    obtain ⟨V, hV, ha, hVU, hlow, hd⟩ := hf
    refine ⟨V, hV, ha, hVU, fun x hx => ih x (hlow x hx), ?_⟩
    apply (totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mpr
    have h := ((totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mp hd).neg
    simpa only [higherDifferential, Specs.D04.C03.HigherInterfaces.Model.higherDifferential,
      iteratedFDeriv_neg] using h

theorem diagonal_neg {n : ℕ} (f : E n → ℝ) (a v : E n) :
    differentialDiagonal (higherDifferential 2 (-f) a) v =
      -differentialDiagonal (higherDifferential 2 f a) v := by
  change iteratedFDeriv ℝ 2 (-f) a (fun _ => v) = _
  rw [iteratedFDeriv_neg_apply]
  rfl

theorem twice_of_contDiff {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f) (a : E n) :
    TimesDifferentiableAt 2 univ f a := by
  exact crOn_timesDifferentiableAt 2 univ f isOpen_univ
    ((crOn_iff_contDiffOn 2 univ f isOpen_univ).mpr hf.contDiffOn) a (mem_univ a)

theorem coordinatePower_contDiff {n : ℕ} (i : Fin n) (k : ℕ) :
    ContDiff ℝ 2 (fun x : E n => (x i)^k) := by
  let L : E n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i
  exact L.contDiff.pow k

theorem coordinatePower_fderiv {n : ℕ} (i : Fin n) (k : ℕ) :
    fderiv ℝ (fun x : E n => (x i)^k) =
      fun x => ((k : ℝ) * (x i)^(k-1)) • PiLp.proj 2 (fun _ : Fin n => ℝ) i := by
  funext x
  let L : E n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i
  simpa [L, nsmul_eq_mul] using
    ((L.hasFDerivAt (x := x)).pow k).fderiv

theorem coordinatePower_second {n : ℕ} (i : Fin n) (k : ℕ) (m : Fin 2 → E n) :
    higherDifferential 2 (fun x : E n => (x i)^k) 0 m =
      ((k : ℝ) * (k-1 : ℕ) * (0 : ℝ)^((k-1)-1)) * (m 0 i) * (m 1 i) := by
  let L : E n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i
  have hc := ((L.hasFDerivAt (x := (0 : E n))).pow (k-1)).const_mul (k : ℝ)
  have hd := (hc.smul_const L).fderiv
  change iteratedFDeriv ℝ 2 (fun x : E n => (x i)^k) 0 m = _
  rw [iteratedFDeriv_two_apply, coordinatePower_fderiv]
  convert congrArg (fun A : E n →L[ℝ] (E n →L[ℝ] ℝ) => A (m 0) (m 1)) hd using 1 <;>
    simp [L, nsmul_eq_mul, mul_assoc]

theorem coordinatePower_hessian {n : ℕ} (i : Fin n) (k : ℕ) (r s : Fin n) :
    hessian (fun x : E n => (x i)^k) 0 r s =
      ((k : ℝ) * (k-1 : ℕ) * (0 : ℝ)^((k-1)-1)) *
        (standardBasis n r i) * (standardBasis n s i) := by
  rw [← hessian_basis univ _ 0
    (twice_of_contDiff _ (coordinatePower_contDiff i k) 0) r s,
    coordinatePower_second]
  rfl

theorem hessian_add {n : ℕ} (f g : E n → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (a : E n) : hessian (f+g) a = hessian f a + hessian g a := by
  ext i j
  change hessian (fun x => f x + g x) a i j = hessian f a i j + hessian g a i j
  rw [← hessian_basis univ _ a (twice_of_contDiff _ (hf.add hg) a) i j,
    ← hessian_basis univ f a (twice_of_contDiff _ hf a) i j,
    ← hessian_basis univ g a (twice_of_contDiff _ hg a) i j]
  exact congrArg (fun T : Differential (E n) ℝ 2 => T ![standardBasis n i, standardBasis n j])
    (iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt)

theorem hessian_neg {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 2 f) (a : E n) :
    hessian (-f) a = -hessian f a := by
  ext i j
  change hessian (fun x => -f x) a i j = -hessian f a i j
  rw [← hessian_basis univ _ a (twice_of_contDiff _ hf.neg a) i j,
    ← hessian_basis univ f a (twice_of_contDiff _ hf a) i j]
  exact congrArg (fun T : Differential (E n) ℝ 2 => T ![standardBasis n i, standardBasis n j])
    iteratedFDeriv_neg_apply

theorem norm_axis {n : ℕ} (i : Fin n) (t : ℝ) :
    ‖t • standardBasis n i‖ = |t| := by
  rw [norm_smul, Real.norm_eq_abs]
  have h : ‖standardBasis n i‖ = 1 := by
    exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i
  rw [h, mul_one]

theorem axis_ne_zero {n : ℕ} (i : Fin n) {t : ℝ} (ht : t ≠ 0) :
    t • standardBasis n i ≠ 0 := by
  intro h
  have hi := congrArg (fun x : E n => x i) h
  simp [PiLp.smul_apply, standardBasis_apply] at hi
  exact ht hi

theorem quartic_strict_minimum :
    StrictLocalMinimumOn univ (fun x : E 1 => (x 0)^4) 0 := by
  refine ⟨mem_univ _, 1, zero_lt_one, fun x _ _ hne => ?_⟩
  have hx : x 0 ≠ 0 := by
    intro h
    apply hne
    ext i
    fin_cases i
    exact h
  simpa using (show Even 4 by decide).pow_pos hx

theorem cubic_saddle : SaddlePoint univ (fun x : E 1 => (x 0)^3) 0 := by
  refine ⟨mem_univ _, fun r hr => ?_⟩
  let t := r/2
  have ht : 0 < t := half_pos hr
  have hb : |t| < r := by rw [abs_of_pos ht]; exact half_lt_self hr
  constructor
  · refine ⟨t • standardBasis 1 0, mem_univ _, ?_, ?_⟩
    · simpa only [sub_zero, norm_axis] using hb
    · simpa [PiLp.smul_apply, standardBasis_apply] using pow_pos ht 3
  · refine ⟨(-t) • standardBasis 1 0, mem_univ _, ?_, ?_⟩
    · simpa only [sub_zero, norm_axis, abs_neg] using hb
    · simp only [PiLp.smul_apply, smul_eq_mul, standardBasis_apply]
      norm_num
      nlinarith [pow_pos ht 3]

theorem square_quartic_strict_minimum :
    StrictLocalMinimumOn univ (fun x : E 2 => (x 0)^2 + (x 1)^4) 0 := by
  refine ⟨mem_univ _, 1, zero_lt_one, fun x _ _ hne => ?_⟩
  simp only [PiLp.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), zero_add]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro he
      apply hne
      ext i
      fin_cases i
      · exact h0
      · exact he
    have hp := (show Even 4 by decide).pow_pos h1
    simpa [h0] using hp
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (by positivity)

theorem square_minus_quartic_saddle :
    SaddlePoint univ (fun x : E 2 => (x 0)^2 - (x 1)^4) 0 := by
  refine ⟨mem_univ _, fun r hr => ?_⟩
  let t := r/2
  have ht : 0 < t := half_pos hr
  have hb : |t| < r := by rw [abs_of_pos ht]; exact half_lt_self hr
  constructor
  · refine ⟨t • standardBasis 2 0, mem_univ _, ?_, ?_⟩
    · simpa only [sub_zero, norm_axis] using hb
    · simpa [PiLp.smul_apply, standardBasis_apply] using sq_pos_of_pos ht
  · refine ⟨t • standardBasis 2 1, mem_univ _, ?_, ?_⟩
    · simpa only [sub_zero, norm_axis] using hb
    · simpa [PiLp.smul_apply, standardBasis_apply] using neg_lt_zero.mpr (pow_pos ht 4)

theorem square_nonstrict_minimum :
    LocalMinimumOn univ (fun x : E 2 => (x 0)^2) 0 ∧
      ¬ StrictLocalMinimumOn univ (fun x : E 2 => (x 0)^2) 0 := by
  constructor
  · exact ⟨mem_univ _, 1, zero_lt_one, fun x _ _ => by simpa using sq_nonneg (x 0)⟩
  · rintro ⟨_, r, hr, h⟩
    have ht : 0 < r/2 := half_pos hr
    have hb : ‖(r/2) • standardBasis 2 1 - 0‖ < r := by
      rw [sub_zero, norm_axis, abs_of_pos ht]
      exact half_lt_self hr
    have hh := h ((r/2) • standardBasis 2 1) (mem_univ _) hb
      (axis_ne_zero 1 (ne_of_gt ht))
    simp [PiLp.smul_apply, standardBasis_apply] at hh

end SecondOrder

theorem secondOrder_minimum : Specs.D04.C05.SecondOrderTests.secondOrder_minimumType := by
  intro n U f a hf hm
  have hd := (timesDifferentiableAt_one U f a).mp
    (timesDifferentiableAt_lower 1 U f a hf)
  have hz := fermat_minimum U f a hd hm
  refine ⟨hz, fun v => ?_⟩
  by_contra hv
  have hv : differentialDiagonal (higherDifferential 2 f a) v < 0 := lt_of_not_ge hv
  have hv0 : v ≠ 0 := by
    intro he
    simp [he, SecondOrder.diagonal_zero] at hv
  let q := differentialDiagonal (higherDifferential 2 f a) v
  let ε := -q / (4 * ‖v‖^2)
  have hε : 0 < ε := div_pos (neg_pos.mpr hv) (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hv0)))
  have hrem := SecondOrder.remainder_bound U f a hf hε
  have hmin : ∀ᶠ h in 𝓝 (0 : E n), f a ≤ f (a+h) := by
    have hdom := timesDifferentiableAt_domain 2 U f a hf
    have hlocal := ((localMinimumOn_iff U f a).mp hm).2.isLocalMin (hdom.1.mem_nhds hdom.2)
    have ht : Tendsto (fun h : E n => a+h) (𝓝 0) (𝓝 a) := by
      convert (continuous_const_add a).tendsto (0 : E n) using 1
      simp only [add_zero]
    exact ht.eventually hlocal
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E n)) := by
    simpa using (tendsto_id.smul (tendsto_const_nhds (x := v)) :
      Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (hrem.and hmin))
  let t := δ / 2
  have htp : 0 < t := half_pos hδ
  have htb : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htp]
    exact half_lt_self hδ
  obtain ⟨hr, hm'⟩ := hb htb
  have hx := taylorRemainder_expansion 2 f a (t • v)
  rw [SecondOrder.taylor_two, hz, zero_apply, add_zero,
    SecondOrder.diagonal_smul] at hx
  have hn : ‖t • v‖^2 = t^2 * ‖v‖^2 := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htp, mul_pow]
  rw [hn] at hr
  have he : ε * ‖v‖^2 = -q/4 := by dsimp [ε]; field_simp
  have hb' : taylorRemainder 2 f a (t • v) ≤ ε * (t^2 * ‖v‖^2) := le_trans (le_abs_self _) hr
  have hmul : ε * (t^2 * ‖v‖^2) = t^2 * (-q/4) := by nlinarith [he]
  rw [hmul] at hb'
  have hq : t^2 * q < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos htp) hv
  dsimp [q] at *
  nlinarith

theorem secondOrder_positive : Specs.D04.C05.SecondOrderTests.secondOrder_positiveType := by
  intro n U f a hf hz hpos
  change totalDerivative f a = 0 at hz
  obtain ⟨η, hη, hlow⟩ := SecondOrder.positive_lower_bound _ hpos
  have he := SecondOrder.remainder_bound U f a hf (show 0 < η/4 by positivity)
  have hdom := timesDifferentiableAt_domain 2 U f a hf
  have hu : ∀ᶠ h in 𝓝 (0 : E n), a+h ∈ U := by
    exact (by fun_prop : ContinuousAt (fun h : E n => a+h) 0).preimage_mem_nhds
      (by simpa using hdom.1.mem_nhds hdom.2)
  obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff.mp (he.and hu)
  have hg : ∀ h, ‖h‖ < ρ → a+h ∈ U ∧ f a + (η/4) * ‖h‖^2 ≤ f (a+h) := by
    intro h hh
    obtain ⟨hr, hu⟩ := hb (by simpa [dist_zero_right] using hh)
    refine ⟨hu, ?_⟩
    have hx := taylorRemainder_expansion 2 f a h
    rw [SecondOrder.taylor_two, hz, zero_apply, add_zero] at hx
    have hl := hlow h
    have hab := neg_abs_le (taylorRemainder 2 f a h)
    nlinarith
  refine ⟨?_, η/4, by positivity, ρ, hρ, hg⟩
  refine ⟨hdom.2, ρ, hρ, fun x _ hx hne => ?_⟩
  have h := (hg (x-a) hx).2
  have hp : 0 < ‖x-a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  simp only [add_sub_cancel] at h
  nlinarith

theorem secondOrder_maximum : Specs.D04.C05.SecondOrderTests.secondOrder_maximumType := by
  intro n U f a hf hm
  have hn : LocalMinimumOn U (-f) a := by
    obtain ⟨ha, r, hr, h⟩ := hm
    exact ⟨ha, r, hr, fun x hx hb => neg_le_neg (h x hx hb)⟩
  have hh := secondOrder_minimum U (-f) a (SecondOrder.timesDifferentiableAt_neg 2 U f a hf) hn
  refine ⟨?_, fun v => ?_⟩
  · have hz : fderiv ℝ (-f) a = 0 := hh.1
    rw [fderiv_neg, neg_eq_zero] at hz
    exact hz
  · have h := hh.2 v
    change 0 ≤ differentialDiagonal (higherDifferential 2 (-f) a) v at h
    rw [SecondOrder.diagonal_neg] at h
    linarith

theorem secondOrder_negative : Specs.D04.C05.SecondOrderTests.secondOrder_negativeType := by
  intro n U f a hf hz hneg
  have hz' : totalDerivative (-f) a = 0 := by
    change fderiv ℝ (-f) a = 0
    rw [fderiv_neg]
    change fderiv ℝ f a = 0 at hz
    rw [hz, neg_zero]
  have hpos : ∀ v, v ≠ 0 → 0 < differentialDiagonal (higherDifferential 2 (-f) a) v := by
    intro v hv
    rw [SecondOrder.diagonal_neg]
    exact neg_pos.mpr (hneg v hv)
  obtain ⟨hm, c, hc, ρ, hρ, hg⟩ := secondOrder_positive U (-f) a
    (SecondOrder.timesDifferentiableAt_neg 2 U f a hf) hz' hpos
  refine ⟨?_, c, hc, ρ, hρ, fun h hh => ?_⟩
  · obtain ⟨ha, r, hr, h⟩ := hm
    exact ⟨ha, r, hr, fun x hx hb hne => neg_lt_neg_iff.mp (h x hx hb hne)⟩
  · obtain ⟨hu, hb⟩ := hg h hh
    refine ⟨hu, ?_⟩
    change -f a + c * ‖h‖^2 ≤ -f (a+h) at hb
    linarith

theorem secondOrder_indefinite : Specs.D04.C05.SecondOrderTests.secondOrder_indefiniteType := by
  intro n U f a hf hp hn
  have hdom := timesDifferentiableAt_domain 2 U f a hf
  apply (saddlePoint_iff_not_extrema U f a).mpr
  refine ⟨hdom.2, ?_, ?_⟩
  · intro hm
    obtain ⟨v, hv⟩ := hn
    have h := (secondOrder_minimum U f a hf ((localMinimumOn_iff U f a).mpr ⟨hdom.2, hm⟩)).2 v
    exact not_lt_of_ge h hv
  · intro hm
    obtain ⟨v, hv⟩ := hp
    have h := (secondOrder_maximum U f a hf ((localMaximumOn_iff U f a).mpr ⟨hdom.2, hm⟩)).2 v
    exact not_lt_of_ge h hv

theorem secondOrder_dimension_zero : Specs.D04.C05.SecondOrderTests.secondOrder_dimension_zeroType := by
  intro U f a ha
  obtain ⟨hmin, hmax⟩ := extrema_dimension_zero U f a ha
  refine ⟨hmin, hmax, fun c h => ?_⟩
  have hh : h = 0 := Subsingleton.elim _ _
  simp [hh]

theorem zeroHessian_examples : Specs.D04.C05.SecondOrderTests.zeroHessian_examplesType := by
  have hc4 := SecondOrder.coordinatePower_contDiff (n := 1) 0 4
  have hc3 := SecondOrder.coordinatePower_contDiff (n := 1) 0 3
  have h4 : hessian (fun x : E 1 => (x 0)^4) 0 = 0 := by
    ext i j
    rw [SecondOrder.coordinatePower_hessian]
    norm_num
  have h3 : hessian (fun x : E 1 => (x 0)^3) 0 = 0 := by
    ext i j
    rw [SecondOrder.coordinatePower_hessian]
    norm_num
  have hn : hessian (fun x : E 1 => -(x 0)^4) 0 = 0 := by
    change hessian (-(fun x : E 1 => (x 0)^4)) 0 = 0
    rw [SecondOrder.hessian_neg _ hc4, h4, neg_zero]
  refine ⟨SecondOrder.twice_of_contDiff _ hc4 0,
    SecondOrder.twice_of_contDiff _ hc4.neg 0,
    SecondOrder.twice_of_contDiff _ hc3 0, h4, hn, h3,
    SecondOrder.quartic_strict_minimum, ?_, SecondOrder.cubic_saddle⟩
  obtain ⟨ha, r, hr, h⟩ := SecondOrder.quartic_strict_minimum
  exact ⟨ha, r, hr, fun x hx hb hne => neg_lt_neg (h x hx hb hne)⟩

theorem semidefiniteHessian_examples : Specs.D04.C05.SecondOrderTests.semidefiniteHessian_examplesType := by
  have hc2 := SecondOrder.coordinatePower_contDiff (n := 2) 0 2
  have hc4 := SecondOrder.coordinatePower_contDiff (n := 2) 1 4
  have h2 : hessian (fun x : E 2 => (x 0)^2) 0 = !![2, 0; 0, 0] := by
    ext i j
    rw [SecondOrder.coordinatePower_hessian]
    fin_cases i <;> fin_cases j <;> norm_num [standardBasis_apply]
  have h4 : hessian (fun x : E 2 => (x 1)^4) 0 = 0 := by
    ext i j
    rw [SecondOrder.coordinatePower_hessian]
    norm_num
  have hadd : hessian (fun x : E 2 => (x 0)^2 + (x 1)^4) 0 = !![2, 0; 0, 0] := by
    change hessian ((fun x : E 2 => (x 0)^2) + (fun x => (x 1)^4)) 0 = _
    rw [SecondOrder.hessian_add _ _ hc2 hc4, h2, h4, add_zero]
  have hsub : hessian (fun x : E 2 => (x 0)^2 - (x 1)^4) 0 = !![2, 0; 0, 0] := by
    have he := SecondOrder.hessian_add (fun x : E 2 => (x 0)^2)
      (fun x : E 2 => -(x 1)^4) hc2 hc4.neg (0 : E 2)
    calc
      _ = hessian (fun x : E 2 => (x 0)^2) 0 + hessian (fun x : E 2 => -(x 1)^4) 0 := he
      _ = hessian (fun x : E 2 => (x 0)^2) 0 - hessian (fun x : E 2 => (x 1)^4) 0 := by
        rw [show hessian (fun x : E 2 => -(x 1)^4) 0 =
          -hessian (fun x : E 2 => (x 1)^4) 0 from SecondOrder.hessian_neg _ hc4 0]
        rfl
      _ = _ := by rw [h2, h4, sub_zero]
  have hnonzero : hessian (fun x : E 2 => (x 0)^2) 0 ≠ 0 := by
    intro he
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) he
    rw [h2] at hh
    norm_num at hh
  have hpsd := (secondOrder_minimum univ (fun x : E 2 => (x 0)^2) 0
    (SecondOrder.twice_of_contDiff _ hc2 0) SecondOrder.square_nonstrict_minimum.1).2
  have hkernel : ∃ v : E 2, v ≠ 0 ∧
      differentialDiagonal (higherDifferential 2 (fun x : E 2 => (x 0)^2) 0) v = 0 := by
    refine ⟨standardBasis 2 1, ?_, ?_⟩
    · simpa only [one_smul] using SecondOrder.axis_ne_zero (n := 2) 1 (one_ne_zero : (1 : ℝ) ≠ 0)
    · change higherDifferential 2 (fun x : E 2 => (x 0)^2) 0 (fun _ => standardBasis 2 1) = 0
      rw [SecondOrder.coordinatePower_second]
      norm_num [standardBasis_apply]
  exact ⟨SecondOrder.twice_of_contDiff _ (hc2.add hc4) 0,
    SecondOrder.twice_of_contDiff _ (hc2.sub hc4) 0,
    SecondOrder.twice_of_contDiff _ hc2 0, hadd, hsub, h2,
    hnonzero, hpsd, hkernel,
    SecondOrder.square_quartic_strict_minimum, SecondOrder.square_minus_quartic_saddle,
    SecondOrder.square_nonstrict_minimum⟩

end D04
