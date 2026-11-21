import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.IterationRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.SpectralRadius
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Proof of `fa2:p5:iteration-radius`. The accepted real spectral radius
and its root formula are applied to the endomorphism Banach algebra only
in the nonzero case. The zero space is handled directly. The inverse is
the norm-summable series of powers; no contraction hypothesis on ‖T‖ is used.
The counterexample uses the literal left shift on native complex ℓ². -/
noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace ExpandedFA.PartV.IterationRadius
open Specs.ExpandedFA.PartV.IterationRadius
open ExpandedFA.BanachAlgebra
universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma radius_zero_space [Subsingleton X] (T : X →L[ℂ] X) : Radius T = 0 := by
  change sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ T) = 0
  simp

lemma radius_geometric (T : X →L[ℂ] X) (h : Radius T < 1) : Geometric T := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine ⟨0, 1/2, le_rfl, by norm_num, by norm_num, ?_⟩
    intro n
    have hz : T ^ n = 0 := Subsingleton.elim _ _
    simp [hz]
  · have hA : IsUnitalBanachAlgebra (X →L[ℂ] X) := ⟨inferInstance, inferInstance, inferInstance⟩
    have hr0 := (algebraSpectralRadius_maximum _ hA T).2.2.1
    obtain ⟨q, hrq, hq1⟩ := exists_between h
    have hq0 : 0 < q := lt_of_le_of_lt hr0 hrq
    have ht := algebraSpectralRadius_root_limit _ hA T
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hrq)
    let C : ℝ := 1 + ∑ i ∈ Finset.range (N + 1), ‖T ^ i‖ / q ^ i
    have hsum : 0 ≤ ∑ i ∈ Finset.range (N + 1), ‖T ^ i‖ / q ^ i :=
      Finset.sum_nonneg (fun i _ => div_nonneg (norm_nonneg _) (pow_nonneg hq0.le _))
    have hC : 1 ≤ C := by dsimp [C]; linarith
    refine ⟨C, q, zero_le_one.trans hC, hq0.le, hq1, fun n => ?_⟩
    by_cases hn : n < N + 1
    · have hb : ‖T ^ n‖ / q ^ n ≤ ∑ i ∈ Finset.range (N + 1), ‖T ^ i‖ / q ^ i :=
        Finset.single_le_sum (f := fun i => ‖T ^ i‖ / q ^ i)
          (fun i _ => div_nonneg (norm_nonneg _) (pow_nonneg hq0.le _))
          (Finset.mem_range.mpr hn)
      apply (div_le_iff₀ (pow_pos hq0 n)).mp
      dsimp [C]
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hm : N ≤ m := by omega
      have hb := (hN m hm).le
      have hp : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hb' : ‖T ^ (m+1)‖ ≤ q ^ (m+1) := by
        rw [one_div] at hb
        have := (Real.rpow_inv_le_iff_of_pos (norm_nonneg _) hq0.le hp).mp hb
        simpa only [Real.rpow_natCast] using this
      exact hb'.trans (le_mul_of_one_le_left (pow_nonneg hq0.le _) hC)

omit [CompleteSpace X] in
lemma geometric_norm_tendsto (T : X →L[ℂ] X) (h : Geometric T) :
    Tendsto (fun n : ℕ => ‖T ^ n‖) atTop (𝓝 0) := by
  obtain ⟨C, q, hC, hq, hq1, hb⟩ := h
  apply squeeze_zero (fun n => norm_nonneg _) hb
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul C

lemma radius_lt_of_norm_tendsto (T : X →L[ℂ] X)
    (h : Tendsto (fun n : ℕ => ‖T ^ n‖) atTop (𝓝 0)) : Radius T < 1 := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · rw [radius_zero_space]; norm_num
  · have hA : IsUnitalBanachAlgebra (X →L[ℂ] X) := ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_lt_const zero_lt_one)
    have hb := algebraSpectralRadius_le_root _ hA T N
    exact hb.trans_lt (Real.rpow_lt_one (norm_nonneg _) (hN (N+1) (by omega)) (by positivity))

theorem iteration_radius_criterion : Criterion.{u} := by
  intro X _ _ _ T
  exact ⟨⟨fun h => geometric_norm_tendsto T (radius_geometric T h), radius_lt_of_norm_tendsto T⟩,
    ⟨radius_geometric T, fun h => radius_lt_of_norm_tendsto T (geometric_norm_tendsto T h)⟩⟩

omit [CompleteSpace X] in
lemma affine_error (T : X →L[ℂ] X) (b y : X) (hy : T y + b = y)
    (x : ℕ → X) (hx : ∀ n, x (n+1) = T (x n) + b) :
    ∀ n, x n - y = (T ^ n) (x 0 - y) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hx, pow_succ', mul_apply_eq_comp, ← ih, map_sub]
    conv_lhs => rw [← hy]
    abel

omit [CompleteSpace X] in
lemma powers_apply_tendsto (T : X →L[ℂ] X)
    (h : Tendsto (fun n : ℕ => ‖T ^ n‖) atTop (𝓝 0)) (v : X) :
    Tendsto (fun n : ℕ => (T ^ n) v) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => (T ^ n).le_opNorm v)
  simpa using h.mul_const ‖v‖

theorem norm_criterion_implies_strong : StrongConsequence.{u} := by
  intro X _ _ _ T h x
  exact powers_apply_tendsto T ((iteration_radius_criterion X T).1.mp h) x

theorem affine_iteration : AffineIteration.{u} := by
  intro X _ _ _ T h
  obtain ⟨C, q, hC, hq, hq1, hb⟩ := radius_geometric T h
  have hs : Summable (fun n : ℕ => T ^ n) := by
    apply Summable.of_norm
    exact ((summable_geometric_of_lt_one hq hq1).mul_left C).of_nonneg_of_le
      (fun n => norm_nonneg _) hb
  let S : X →L[ℂ] X := ∑' n : ℕ, T ^ n
  have hright : (1 - T) * S = 1 := hs.one_sub_mul_tsum_pow
  have hleft : S * (1 - T) = 1 := hs.tsum_pow_mul_one_sub
  refine ⟨S, C, q, hright, hleft, hC, hq, hq1, fun b => ?_⟩
  have hSb : S b - T (S b) = b := by
    simpa using congrArg (fun U : X →L[ℂ] X => U b) hright
  have hfix : T (S b) + b = S b := calc
    T (S b) + b = T (S b) + (S b - T (S b)) := congrArg (T (S b) + ·) hSb.symm
    _ = S b := by abel
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have he : y - T y = b := calc
        y - T y = (T y + b) - T y := congrArg (· - T y) hy.symm
        _ = b := by abel
      have hi := congrArg (fun U : X →L[ℂ] X => U y) hleft
      change S (y - T y) = y at hi
      rw [he] at hi
      exact hi.symm
    · rintro rfl
      exact hfix
  · intro x hx
    have herr := affine_error T b (S b) hfix x hx
    refine ⟨herr, ?_⟩
    have ht := powers_apply_tendsto T (geometric_norm_tendsto T ⟨C,q,hC,hq,hq1,hb⟩) (x 0 - S b)
    have hh : Tendsto (fun n => x n - S b) atTop (𝓝 0) := ht.congr' (Eventually.of_forall fun n => (herr n).symm)
    simpa using hh.add_const (S b)
  · intro x₀ R hR n
    let x : ℕ → X := fun k => (fun x => T x + b)^[k] x₀
    have hx : ∀ k, x (k+1) = T (x k) + b := fun k => Function.iterate_succ_apply' _ _ _
    have he := affine_error T b (S b) hfix x hx n
    change ‖x n - S b‖ ≤ _
    rw [he]
    exact ((T ^ n).le_opNorm _).trans <| (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hR (mul_nonneg hC (pow_nonneg hq n)))

theorem left_shift_coordinates : ShiftCoordinates := by
  intro x k
  rfl

lemma left_shift_power_coordinates (n : ℕ) (x : ShiftSpace) (k : ℕ) :
    (leftShift ^ n) x k = x (k + n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, left_shift_coordinates, ih]
    exact congrArg x (by omega : k + 1 + n = k + (n + 1))

instance shiftSpaceNontrivial : Nontrivial ShiftSpace := by
  refine ⟨⟨lp.single 2 0 (1 : ℂ), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun x : ShiftSpace => x 0) h
  simp at hh

lemma left_shift_power_norm (n : ℕ) : ‖leftShift ^ n‖ = 1 := by
  have hn : ‖leftShift‖ ≤ 1 := by
    unfold leftShift
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hu : ‖leftShift ^ n‖ ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (leftShift ^ n)])
  apply le_antisymm hu
  have he : (leftShift ^ n) (lp.single 2 n (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
    apply lp.ext
    funext k
    rw [left_shift_power_coordinates]
    simp [lp.single_apply, Pi.single_apply]
  have h := (leftShift ^ n).le_opNorm (lp.single 2 n (1 : ℂ))
  rw [he] at h
  simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one] using h

lemma left_shift_strong (x : ShiftSpace) :
    Tendsto (fun n : ℕ => (leftShift ^ n) x) atTop (𝓝 0) := by
  have hn (v : ShiftSpace) : ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  have ht : Tendsto (fun n => ‖(leftShift ^ n) x‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hn, left_shift_power_coordinates]
    exact tendsto_sum_nat_add (fun k => ‖x k‖ ^ 2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

lemma geometric_sequence_mem (z : ℂ) (hz : ‖z‖ < 1) :
    Memℓp (fun n : ℕ => z ^ n) 2 := by
  apply memℓp_gen
  have hs := summable_geometric_of_lt_one (sq_nonneg ‖z‖)
    (by nlinarith [norm_nonneg z] : ‖z‖ ^ 2 < 1)
  simpa only [ENNReal.toReal_ofNat, norm_pow, Real.rpow_two, ← pow_mul, mul_comm] using hs

lemma left_shift_spectrum : spectrum ℂ leftShift = Metric.closedBall 0 1 := by
  have hinterior : Metric.ball (0 : ℂ) 1 ⊆ spectrum ℂ leftShift := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    let v : ShiftSpace := ⟨fun n => z ^ n, geometric_sequence_mem z hz'⟩
    have hv : v ≠ 0 := by
      intro h
      have hh := congrArg (fun x : ShiftSpace => x 0) h
      change z ^ 0 = 0 at hh
      simp at hh
    have he : leftShift v = z • v := by
      apply lp.ext
      funext k
      change z ^ (k + 1) = z * z ^ k
      exact pow_succ' _ _
    change ¬ IsUnit (algebraMap ℂ (ShiftSpace →L[ℂ] ShiftSpace) z - leftShift)
    intro hu
    obtain ⟨S, _, hS⟩ := isUnit_iff_exists.mp hu
    have hh := congrArg (fun U : ShiftSpace →L[ℂ] ShiftSpace => U v) hS
    have hk : (algebraMap ℂ (ShiftSpace →L[ℂ] ShiftSpace) z - leftShift) v = 0 := by
      simp [he]
    change S ((algebraMap ℂ (ShiftSpace →L[ℂ] ShiftSpace) z - leftShift) v) = v at hh
    rw [hk, map_zero] at hh
    exact hv hh.symm
  apply Set.Subset.antisymm
  · intro z hz
    have hn := spectrum.norm_le_norm_of_mem hz
    have he : ‖leftShift‖ = 1 := by simpa using left_shift_power_norm 1
    simpa only [Metric.mem_closedBall, dist_zero_right, he] using hn
  · have hcl := closure_minimal hinterior (spectrum.isClosed leftShift)
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hcl
    exact hcl

lemma left_shift_radius : Radius leftShift = 1 := by
  change sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ leftShift) = 1
  rw [left_shift_spectrum]
  have hb : BddAbove ((fun z : ℂ => ‖z‖) '' Metric.closedBall 0 1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa using hz
  apply le_antisymm
  · apply csSup_le (by exact ⟨0, 0, by simp, by simp⟩)
    rintro _ ⟨z, hz, rfl⟩
    simpa using hz
  · exact le_csSup hb ⟨1, by simp, by simp⟩

theorem left_shift_counterexample : ShiftCounterexample := by
  refine ⟨left_shift_strong, left_shift_power_norm, left_shift_spectrum, left_shift_radius, ?_⟩
  intro h
  have hh := (iteration_radius_criterion ShiftSpace leftShift).2.mpr h
  rw [left_shift_radius] at hh
  exact lt_irrefl _ hh

end ExpandedFA.PartV.IterationRadius
