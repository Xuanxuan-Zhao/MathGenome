import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology ENNReal NNReal
universe u
namespace ExpandedFA.FunctionSpaces.SequenceDuals
open ExpandedFA.P1.C01SequenceSpaces

theorem discrete_holder : ∀ (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    p⁻¹ + q⁻¹ = 1 → ∀ (x : SequenceLp 𝕜 p) (y : SequenceLp 𝕜 q),
      Summable (fun n => ‖x n * y n‖) ∧ Summable (fun n => x n * y n) ∧
      (∑' n, ‖x n * y n‖) ≤ ‖x‖ * ‖y‖ := by
  intro 𝕜 _ p q _ _ hpq x y
  have : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr hpq
  let B : ℕ → 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜 := fun _ => ContinuousLinearMap.mul 𝕜 𝕜
  have hB : ∀ n, ‖B n‖ ≤ (1 : ℝ≥0) :=
    fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let z : SequenceLp 𝕜 1 := lp.holder 1 B hB x y
  have hz : Summable (fun n => ‖x n * y n‖) := by
    simpa [z, B] using (lp.memℓp z).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  refine ⟨hz, hz.of_norm, ?_⟩
  have hznorm : ‖z‖ = ∑' n, ‖x n * y n‖ := by
    simpa [z, B] using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) z
  rw [← hznorm]
  exact (lp.holderL (p := p) (q := q) 1 B hB).le_of_opNorm₂_le_of_le
    (lp.norm_holderL_le 1 B hB) le_rfl le_rfl |>.trans (by simp)

/-- The bilinear scalar series, without conjugation. -/
def lpSequencePairing (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p] :
    SequenceLp 𝕜 q →L[𝕜] (SequenceLp 𝕜 p →L[𝕜] 𝕜) :=
  lp.dualPairing q p (fun _ : ℕ => ContinuousLinearMap.mul 𝕜 𝕜)
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)

theorem lpSequencePairing_apply (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (a : SequenceLp 𝕜 q) (x : SequenceLp 𝕜 p) :
    lpSequencePairing 𝕜 p q a x = ∑' n, a n * x n := rfl

theorem lpSequencePairing_single (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (a : SequenceLp 𝕜 q) (n : ℕ) :
    lpSequencePairing 𝕜 p q a (lp.single p n 1) = a n := by
  classical
  rw [lpSequencePairing_apply, tsum_eq_single n]
  · simp
  · intro j hj
    simp [hj]

theorem lpSequencePairing_norm_le (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (a : SequenceLp 𝕜 q) : ‖lpSequencePairing 𝕜 p q a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [lpSequencePairing_apply]
  have h := discrete_holder 𝕜 q p
    (ENNReal.HolderConjugate.inv_add_inv_eq_one q p) a x
  exact (norm_tsum_le_tsum_norm h.1).trans h.2.2

/-- The scalar finite-test coefficient; its product with z is the qth power
of the modulus, for either real or complex scalars. -/
def lpDualTestScalar {𝕜 : Type u} [RCLike 𝕜] (r : ℝ) (z : 𝕜) : 𝕜 :=
  star z * RCLike.ofReal (‖z‖ ^ (r - 2))

theorem lpDualTestScalar_mul {𝕜 : Type u} [RCLike 𝕜] (r : ℝ)
    (hr : 1 < r) (z : 𝕜) :
    z * lpDualTestScalar r z = RCLike.ofReal (‖z‖ ^ r) := by
  by_cases hz : z = 0
  · simp [hz, lpDualTestScalar, Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hr))]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [lpDualTestScalar, ← mul_assoc, RCLike.star_def, RCLike.mul_conj]
    rw [← RCLike.ofReal_pow]
    rw [← RCLike.ofReal_mul]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_add hn]
    congr 1
    ring

theorem lpDualTestScalar_norm {𝕜 : Type u} [RCLike 𝕜] (r : ℝ)
    (hr : 1 < r) (z : 𝕜) :
    ‖lpDualTestScalar r z‖ = ‖z‖ ^ (r - 1) := by
  by_cases hz : z = 0
  · simp [hz, lpDualTestScalar, Real.zero_rpow (sub_pos.mpr hr).ne']
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp only [lpDualTestScalar, norm_mul, norm_star, RCLike.norm_ofReal,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    conv_lhs => lhs; rw [← Real.rpow_one ‖z‖]
    rw [← Real.rpow_add hn]
    congr 1
    ring

/-- A nonnegative power-sum estimate extracted from boundedness of a finite test. -/
theorem lpDual_power_bound {P Q C S : ℝ} (h : P.HolderConjugate Q)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hbound : S ≤ C * S ^ (1 / P)) :
    S ≤ C ^ Q := by
  by_cases hz : S = 0
  · subst S; positivity
  have hs : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have heq : S ^ (1 / Q) * S ^ (1 / P) = S := by
    rw [← Real.rpow_add hs, h.symm.one_div_add_one_div]
    simp
  have hroot : S ^ (1 / Q) ≤ C := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hs (1 / P))).mp
    calc
      S ^ (1 / Q) * S ^ (1 / P) = S := heq
      _ ≤ C * S ^ (1 / P) := hbound
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hS _) hroot h.symm.nonneg
  simpa [← Real.rpow_mul hS, h.symm.ne_zero] using hh

/-- Uniform q-power bounds for the coefficients of an arbitrary functional. -/
theorem lpDual_coefficients_sum_le (𝕜 : Type u) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp0 : 0 < p.toReal) (_hq0 : 0 < q.toReal)
    (h : p.toReal.HolderConjugate q.toReal)
    (f : SequenceLp 𝕜 p →L[𝕜] 𝕜) (s : Finset ℕ) :
    ∑ n ∈ s, ‖f (lp.single p n 1)‖ ^ q.toReal ≤ ‖f‖ ^ q.toReal := by
  classical
  let a : ℕ → 𝕜 := fun n => f (lp.single p n 1)
  let b : ℕ → 𝕜 := fun n => lpDualTestScalar q.toReal (a n)
  let x : SequenceLp 𝕜 p := ∑ n ∈ s, lp.single p n (b n)
  let S : ℝ := ∑ n ∈ s, ‖a n‖ ^ q.toReal
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by positivity)
  have hf (n : ℕ) : f (lp.single p n (b n)) = a n * b n := by
    have heq : lp.single p n (b n) = b n • lp.single (E := fun _ : ℕ => 𝕜) p n (1 : 𝕜) := by
      rw [← lp.single_smul]; simp
    rw [heq, map_smul]
    exact mul_comm _ _
  have hfx : f x = RCLike.ofReal S := by
    simp only [x, map_sum, hf]
    change (∑ n ∈ s, a n * lpDualTestScalar q.toReal (a n)) = _
    simp_rw [lpDualTestScalar_mul _ h.symm.lt]
    simp [S]
  have hnx : ‖x‖ ^ p.toReal = S := by
    rw [lp.norm_sum_single hp0]
    apply Finset.sum_congr rfl
    intro n _
    rw [lpDualTestScalar_norm _ h.symm.lt, ← Real.rpow_mul (norm_nonneg _),
      h.symm.sub_one_mul_conj]
  have hn : ‖x‖ = S ^ (1 / p.toReal) := by
    rw [← hnx, one_div, Real.rpow_rpow_inv (norm_nonneg _) h.ne_zero]
  apply lpDual_power_bound h (norm_nonneg f) hS
  have hb := f.le_opNorm x
  rwa [hfx, RCLike.norm_ofReal, abs_of_nonneg hS, hn] at hb

/-- The coordinate sequence belongs to ℓᑫ, with the reverse norm bound. -/
theorem lpDual_coefficients (𝕜 : Type u) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp0 : 0 < p.toReal) (hq0 : 0 < q.toReal)
    (h : p.toReal.HolderConjugate q.toReal)
    (f : SequenceLp 𝕜 p →L[𝕜] 𝕜) :
    ∃ a : SequenceLp 𝕜 q,
      (∀ n, a n = f (lp.single p n 1)) ∧ ‖a‖ ≤ ‖f‖ := by
  let a : SequenceLp 𝕜 q := ⟨fun n => f (lp.single p n 1),
    memℓp_gen' (lpDual_coefficients_sum_le 𝕜 p q hp0 hq0 h f)⟩
  refine ⟨a, fun _ => rfl, ?_⟩
  apply lp.norm_le_of_forall_sum_le hq0 (norm_nonneg f)
  exact lpDual_coefficients_sum_le 𝕜 p q hp0 hq0 h f

/-- Functionals on finite-exponent ℓᵖ are determined by their coordinates. -/
theorem lpDual_ext (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f g : SequenceLp 𝕜 p →L[𝕜] 𝕜)
    (h : ∀ n, f (lp.single p n 1) = g (lp.single p n 1)) : f = g := by
  apply ContinuousLinearMap.ext
  intro x
  have hs (n : ℕ) : f (lp.single p n (x n)) = g (lp.single p n (x n)) := by
    have heq : lp.single p n (x n) = x n •
        lp.single (E := fun _ : ℕ => 𝕜) p n (1 : 𝕜) := by
      rw [← lp.single_smul]; simp
    simp only [heq, map_smul, h]
  have hf := (f.continuous.tendsto x).comp (lp.hasSum_single hp x).tendsto_sum_nat
  have hg := (g.continuous.tendsto x).comp (lp.hasSum_single hp x).tendsto_sum_nat
  have heq : (fun N => f (∑ n ∈ Finset.range N, lp.single p n (x n))) =
      (fun N => g (∑ n ∈ Finset.range N, lp.single p n (x n))) := by
    funext N
    simp only [map_sum, hs]
  simp only [Function.comp_def] at hf hg
  rw [heq] at hf
  exact tendsto_nhds_unique hf hg

/-- Surjectivity comes from the actual coordinate sequence, with no assumed
representation or completeness certificate. -/
theorem lpSequencePairing_surjective (𝕜 : Type u) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : 1 < p) (hpfin : p ≠ ∞) :
    Function.Surjective (lpSequencePairing 𝕜 p q) := by
  have hqfin : q ≠ ∞ :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp |>.ne
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp)) hpfin
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ q))) hqfin
  have h : p.toReal.HolderConjugate q.toReal :=
    (ENNReal.HolderConjugate.toReal_of_ne_top hqfin hpfin).symm
  intro f
  obtain ⟨a, ha, _⟩ := lpDual_coefficients 𝕜 p q hp0 hq0 h f
  refine ⟨a, lpDual_ext 𝕜 p hpfin _ f (fun n => ?_)⟩
  rw [lpSequencePairing_single, ha]

/-- Exact equality of norms, proved using the same finite-test bound. -/
theorem lpSequencePairing_norm (𝕜 : Type u) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : 1 < p) (hpfin : p ≠ ∞) (a : SequenceLp 𝕜 q) :
    ‖lpSequencePairing 𝕜 p q a‖ = ‖a‖ := by
  apply le_antisymm (lpSequencePairing_norm_le 𝕜 p q a)
  have hqfin : q ≠ ∞ :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp |>.ne
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp)) hpfin
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ q))) hqfin
  have h : p.toReal.HolderConjugate q.toReal :=
    (ENNReal.HolderConjugate.toReal_of_ne_top hqfin hpfin).symm
  obtain ⟨b, hb, hbn⟩ := lpDual_coefficients 𝕜 p q hp0 hq0 h (lpSequencePairing 𝕜 p q a)
  have heq : b = a := by
    apply lp.ext
    funext n
    rw [hb, lpSequencePairing_single]
  rwa [heq] at hbn

/-- The full source theorem, including the bilinear complex convention,
absolute convergence, inverse coordinate formula, and uniqueness. -/
theorem lp_sequence_duality : Spec.LpDuality.{u} := by
  intro 𝕜 _ p q _ _ hp hpfin hpq
  have : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr hpq
  let I : SequenceLp 𝕜 q →ₗᵢ[𝕜] (SequenceLp 𝕜 p →L[𝕜] 𝕜) :=
    { (lpSequencePairing 𝕜 p q).toLinearMap with
      norm_map' := lpSequencePairing_norm 𝕜 p q hp hpfin }
  let U := LinearIsometryEquiv.ofSurjective I
    (lpSequencePairing_surjective 𝕜 p q hp hpfin)
  have hU (a : SequenceLp 𝕜 q) : U a = lpSequencePairing 𝕜 p q a := rfl
  have hformula (a : SequenceLp 𝕜 q) (x : SequenceLp 𝕜 p) :
      U a x = ∑' n, a n * x n := rfl
  refine ⟨U, ?_, U.norm_map, ?_, ?_⟩
  · intro a x
    exact ⟨(discrete_holder 𝕜 q p (by simpa [add_comm] using hpq) a x).1,
      hformula a x⟩
  · intro f n
    have hv := lpSequencePairing_single 𝕜 p q (U.symm f) n
    rw [← hU, U.apply_symm_apply] at hv
    exact hv.symm
  · intro f
    refine ⟨U.symm f, ?_, ?_⟩
    · intro x
      rw [← hformula, U.apply_symm_apply]
    · intro a ha
      apply U.injective
      apply ContinuousLinearMap.ext
      intro x
      rw [U.apply_symm_apply, hformula, ← ha x]

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The continuous bilinear series pairing. -/
def l1Pairing : SequenceLInfinity 𝕜 →L[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜) :=
  lp.dualPairing ∞ 1 (K := 1) (fun _ : ℕ => ContinuousLinearMap.mul 𝕜 𝕜)
    (fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)

@[simp] theorem l1Pairing_apply (a : SequenceLInfinity 𝕜) (x : SequenceLp 𝕜 1) :
    l1Pairing a x = ∑' n, a n * x n := rfl

@[simp] theorem l1Pairing_single (a : SequenceLInfinity 𝕜) (j : ℕ) :
    l1Pairing a (lp.single 1 j (1 : 𝕜)) = a j := by
  classical
  rw [l1Pairing_apply, tsum_eq_single j]
  · simp
  · intro n hn
    rw [lp.single_apply_ne _ _ _ hn, mul_zero]

theorem norm_l1Pairing (a : SequenceLInfinity 𝕜) : ‖l1Pairing a‖ = ‖a‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
    intro x
    rw [l1Pairing_apply]
    have h := discrete_holder 𝕜 ∞ 1 (by simp) a x
    exact (norm_tsum_le_tsum_norm h.1).trans h.2.2
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro j
    have h := (l1Pairing a).le_opNorm (lp.single 1 j (1 : 𝕜))
    rw [l1Pairing_single, lp.norm_single (by simp : 0 < (1 : ℝ≥0∞)),
      norm_one, mul_one] at h
    exact h

/-- The bounded sequence extracted from a continuous functional. -/
def l1Coefficients (f : SequenceLp 𝕜 1 →L[𝕜] 𝕜) : SequenceLInfinity 𝕜 :=
  ⟨fun n => f (lp.single 1 n (1 : 𝕜)), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨n, rfl⟩
    simpa [lp.norm_single (by simp : 0 < (1 : ℝ≥0∞))] using
      f.le_opNorm (lp.single 1 n (1 : 𝕜))⟩⟩

@[simp] theorem l1Coefficients_apply (f : SequenceLp 𝕜 1 →L[𝕜] 𝕜) (n : ℕ) :
    l1Coefficients f n = f (lp.single 1 n (1 : 𝕜)) := rfl

@[simp] theorem l1Coefficients_pairing (a : SequenceLInfinity 𝕜) :
    l1Coefficients (l1Pairing a) = a := by
  apply lp.ext
  funext n
  change l1Pairing a (lp.single 1 n (1 : 𝕜)) = a n
  exact l1Pairing_single a n

@[simp] theorem l1Pairing_coefficients (f : SequenceLp 𝕜 1 →L[𝕜] 𝕜) :
    l1Pairing (l1Coefficients f) = f := by
  ext x
  have h := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x).mapL f
  have heq (n : ℕ) : f (lp.single 1 n (x n)) = l1Coefficients f n * x n := by
    have hs : lp.single 1 n (x n) = x n • (lp.single 1 n (1 : 𝕜) : SequenceLp 𝕜 1) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : ℕ => 𝕜) 1 n (x n) (1 : 𝕜))
    calc
      _ = f (x n • (lp.single 1 n (1 : 𝕜) : SequenceLp 𝕜 1)) := congrArg f hs
      _ = l1Coefficients f n * x n := by simp only [map_smul, smul_eq_mul,
        l1Coefficients_apply, mul_comm]
  simp_rw [heq] at h
  exact h.tsum_eq

/-- The explicit linear isometric equivalence; its inverse evaluates unit vectors. -/
def l1Duality : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜) where
  toLinearEquiv :=
    { toLinearMap := l1Pairing.toLinearMap
      invFun := l1Coefficients
      left_inv := l1Coefficients_pairing
      right_inv := l1Pairing_coefficients }
  norm_map' := norm_l1Pairing

theorem l1_duality : Spec.L1Duality.{u} := by
  intro 𝕜 _
  exact ⟨l1Duality, (fun a x => ⟨(discrete_holder 𝕜 ∞ 1 (by simp) a x).1, rfl⟩),
    norm_l1Pairing, fun _ _ => rfl⟩

/-- Endpoint Hölder for the literal inclusion c₀ ⊆ ℓ∞. -/
theorem c0_pairing_holder (a : SequenceLp 𝕜 1) (x : SequenceC0 𝕜) :
    Summable (fun j => ‖a j * x.val j‖) ∧
    Summable (fun j => a j * x.val j) ∧
    (∑' j, ‖a j * x.val j‖) ≤ ‖a‖ * ‖x‖ := by
  exact discrete_holder 𝕜 1 ∞ (by simp) a x.val

/-- The series defines a continuous scalar-linear functional. -/
def c0SeriesFunctional (a : SequenceLp 𝕜 1) : SequenceC0 𝕜 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' j, a j * x.val j
      map_add' := by
        intro x y
        simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]
        exact (c0_pairing_holder a x).2.1.tsum_add (c0_pairing_holder a y).2.1
      map_smul' := by
        intro c x
        change (∑' j, a j * (c * x.val j)) = c * ∑' j, a j * x.val j
        simp_rw [← mul_assoc, mul_comm (a _) c, mul_assoc]
        exact tsum_mul_left }
    ‖a‖ (fun x => (norm_tsum_le_tsum_norm (c0_pairing_holder a x).1).trans
      (c0_pairing_holder a x).2.2)

@[simp] theorem c0SeriesFunctional_apply (a : SequenceLp 𝕜 1) (x : SequenceC0 𝕜) :
    c0SeriesFunctional a x = ∑' j, a j * x.val j := rfl

theorem c0SeriesFunctional_norm_le (a : SequenceLp 𝕜 1) :
    ‖c0SeriesFunctional a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (norm_tsum_le_tsum_norm (c0_pairing_holder a x).1).trans
    (c0_pairing_holder a x).2.2

@[simp] theorem c0Coordinate_apply (j n : ℕ) :
    (c0Coordinate 𝕜 j).val n = if n = j then 1 else 0 := by
  classical
  change lp.single (E := fun _ : ℕ => 𝕜) ∞ j (1 : 𝕜) n = _
  by_cases h : n = j
  · subst n; simp
  · simp [h]

@[simp] theorem c0SeriesFunctional_coordinate (a : SequenceLp 𝕜 1) (j : ℕ) :
    c0SeriesFunctional a (c0Coordinate 𝕜 j) = a j := by
  classical
  simp [c0SeriesFunctional_apply, c0Coordinate_apply, mul_ite, tsum_ite_eq', eq_comm]

/-- Scalar phase for the bilinear pairing; it cancels, rather than adds,
the phase of a coefficient. -/
def c0DualPhase (z : 𝕜) : 𝕜 := starRingEnd 𝕜 z / (‖z‖ : 𝕜)

theorem c0DualPhase_norm_le (z : 𝕜) : ‖c0DualPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [c0DualPhase, hz]
  · simp [c0DualPhase, norm_div, div_self (norm_ne_zero_iff.mpr hz)]

theorem mul_c0DualPhase (z : 𝕜) : z * c0DualPhase z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz, c0DualPhase]
  · have hn : (‖z‖ : 𝕜) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [c0DualPhase, ← mul_div_assoc, RCLike.mul_conj]
    field_simp

/-- A finite phase test controls every finite sum of coefficient norms. -/
theorem c0_dual_finite_coefficient_bound (f : SequenceC0 𝕜 →L[𝕜] 𝕜)
    (s : Finset ℕ) : ∑ j ∈ s, ‖f (c0Coordinate 𝕜 j)‖ ≤ ‖f‖ := by
  classical
  let x : SequenceC0 𝕜 := ∑ j ∈ s,
    c0DualPhase (f (c0Coordinate 𝕜 j)) • c0Coordinate 𝕜 j
  have hx : ‖x‖ ≤ 1 := by
    change ‖x.val‖ ≤ 1
    apply lp.norm_le_of_forall_le zero_le_one
    intro n
    change ‖(∑ j ∈ s, c0DualPhase (f (c0Coordinate 𝕜 j)) •
      c0Coordinate 𝕜 j : SequenceC0 𝕜).val n‖ ≤ 1
    simp only [Submodule.coe_sum, Submodule.coe_smul, lp.coeFn_sum,
      Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, c0Coordinate_apply]
    simp only [mul_ite, mul_one, mul_zero]
    simp_rw [eq_comm (a := n)]
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact c0DualPhase_norm_le _
    · simp
  have hfx : f x = ((∑ j ∈ s, ‖f (c0Coordinate 𝕜 j)‖ : ℝ) : 𝕜) := by
    change f.toLinearMap (∑ j ∈ s, c0DualPhase (f (c0Coordinate 𝕜 j)) • c0Coordinate 𝕜 j) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, ContinuousLinearMap.coe_coe]
    simp_rw [mul_comm (c0DualPhase _) _, mul_c0DualPhase]
    simp
  have h := (f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg f) hx)
  rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg
    (fun j _ => norm_nonneg _))] at h
  exact h

/-- Every functional's coordinate values form an ℓ¹ sequence. -/
def c0DualCoefficients (f : SequenceC0 𝕜 →L[𝕜] 𝕜) : SequenceLp 𝕜 1 :=
  ⟨fun j => f (c0Coordinate 𝕜 j), by
    apply memℓp_gen
    simpa using summable_of_sum_le (fun j => norm_nonneg (f (c0Coordinate 𝕜 j)))
      (c0_dual_finite_coefficient_bound f)⟩

theorem c0DualCoefficients_norm_le (f : SequenceC0 𝕜 →L[𝕜] 𝕜) :
    ‖c0DualCoefficients f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (p := 1) (f := c0DualCoefficients f) (by simp) (norm_nonneg f)
  simpa [c0DualCoefficients] using c0_dual_finite_coefficient_bound f

/-- Uniform convergence of the finite coordinate sums in the canonical c₀. -/
theorem c0_truncation_convergence (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC0 𝕜) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, x.val j • c0Coordinate 𝕜 j)
      atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.property (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  change ‖(∑ j ∈ Finset.range n, x.val j • c0Coordinate 𝕜 j : SequenceC0 𝕜).val - x.val‖ < ε
  apply lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity : 0 ≤ ε / 2) ?_)
    (half_lt_self hε)
  intro j
  simp only [lp.coeFn_sub, Pi.sub_apply, Submodule.coe_sum, Submodule.coe_smul,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, c0Coordinate_apply, mul_ite, mul_one, mul_zero]
  simp_rw [eq_comm (a := j)]
  rw [Finset.sum_ite_eq']
  by_cases hj : j < n
  · simp [Finset.mem_range, hj]; positivity
  · simpa [Finset.mem_range, hj, dist_eq_norm] using
      (hN j (hn.trans (Nat.le_of_not_gt hj))).le

theorem c0_functional_ext (f g : SequenceC0 𝕜 →L[𝕜] 𝕜)
    (h : ∀ j, f (c0Coordinate 𝕜 j) = g (c0Coordinate 𝕜 j)) : f = g := by
  ext x
  have heq (N : ℕ) :
      f (∑ j ∈ Finset.range N, x.val j • c0Coordinate 𝕜 j) =
      g (∑ j ∈ Finset.range N, x.val j • c0Coordinate 𝕜 j) := by
    change f.toLinearMap (∑ j ∈ Finset.range N, x.val j • c0Coordinate 𝕜 j) =
      g.toLinearMap (∑ j ∈ Finset.range N, x.val j • c0Coordinate 𝕜 j)
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_coe, h]
  have hf := f.continuous.tendsto x |>.comp (c0_truncation_convergence 𝕜 x)
  have hg := g.continuous.tendsto x |>.comp (c0_truncation_convergence 𝕜 x)
  exact tendsto_nhds_unique hf (hg.congr' (Eventually.of_forall fun N => (heq N).symm))

theorem c0SeriesFunctional_coefficients (f : SequenceC0 𝕜 →L[𝕜] 𝕜) :
    c0SeriesFunctional (c0DualCoefficients f) = f := by
  apply c0_functional_ext
  intro j
  simp [c0DualCoefficients]

@[simp] theorem c0DualCoefficients_series (a : SequenceLp 𝕜 1) :
    c0DualCoefficients (c0SeriesFunctional a) = a := by
  apply lp.ext
  funext j
  exact c0SeriesFunctional_coordinate a j

/-- Both norm inequalities, with no norm-attainment assumption. -/
theorem c0SeriesFunctional_norm (a : SequenceLp 𝕜 1) :
    ‖c0SeriesFunctional a‖ = ‖a‖ := by
  apply le_antisymm (c0SeriesFunctional_norm_le a)
  simpa using c0DualCoefficients_norm_le (c0SeriesFunctional a)

/-- The bilinear series map as a linear isometry. -/
def c0DualityIsometry : SequenceLp 𝕜 1 →ₗᵢ[𝕜] (SequenceC0 𝕜 →L[𝕜] 𝕜) where
  toFun := c0SeriesFunctional
  map_add' a b := by
    ext x
    change (∑' j, (a j + b j) * x.val j) =
      (∑' j, a j * x.val j) + ∑' j, b j * x.val j
    simp_rw [add_mul]
    exact (c0_pairing_holder a x).2.1.tsum_add (c0_pairing_holder b x).2.1
  map_smul' c a := by
    ext x
    change (∑' j, (c * a j) * x.val j) = c * ∑' j, a j * x.val j
    simp_rw [mul_assoc]
    exact tsum_mul_left
  norm_map' := c0SeriesFunctional_norm

/-- Surjectivity is supplied by the actual coefficient sequence f(eⱼ). -/
def c0DualityEquiv : SequenceLp 𝕜 1 ≃ₗᵢ[𝕜] (SequenceC0 𝕜 →L[𝕜] 𝕜) :=
  LinearIsometryEquiv.ofSurjective c0DualityIsometry
    (fun f => ⟨c0DualCoefficients f, c0SeriesFunctional_coefficients f⟩)

theorem c0_duality : Spec.C0Duality.{u} := by
  intro 𝕜 _
  refine ⟨c0DualityEquiv, ?_, ?_, ?_, ?_⟩
  · intro a x
    exact ⟨(c0_pairing_holder a x).1, rfl⟩
  · exact c0SeriesFunctional_norm
  · intro f j
    have h := congrArg (fun g : SequenceC0 𝕜 →L[𝕜] 𝕜 => g (c0Coordinate 𝕜 j))
      (c0DualityEquiv.apply_symm_apply f)
    change c0SeriesFunctional ((c0DualityEquiv (𝕜 := 𝕜)).symm f) (c0Coordinate 𝕜 j) =
      f (c0Coordinate 𝕜 j) at h
    simpa using h
  · intro f
    refine ⟨c0DualCoefficients f, ?_, ?_⟩
    · intro x
      exact (congrArg (fun g : SequenceC0 𝕜 →L[𝕜] 𝕜 => g x)
        (c0SeriesFunctional_coefficients f)).symm
    · intro a ha
      have heq : c0SeriesFunctional a = f := ContinuousLinearMap.ext (fun x => (ha x).symm)
      have h := congrArg c0DualCoefficients heq
      simpa using h


/-- The chosen limit really is the limit of the coordinates. -/
theorem tendsto_sequenceLimit (x : SequenceConvergent 𝕜) :
    Tendsto (fun n => x.val n) atTop (𝓝 (sequenceLimit x)) :=
  Classical.choose_spec x.property

theorem sequenceLimit_eq (x : SequenceConvergent 𝕜) {l : 𝕜}
    (h : Tendsto (fun n => x.val n) atTop (𝓝 l)) : sequenceLimit x = l :=
  tendsto_nhds_unique (tendsto_sequenceLimit x) h

/-- The constant sequence one, in c with its inherited norm. -/
def cOne (𝕜 : Type u) [RCLike 𝕜] : SequenceConvergent 𝕜 :=
  ⟨1, 1, by simp⟩

@[simp] theorem cOne_apply (n : ℕ) : (cOne 𝕜).val n = 1 := by
  simp [cOne]

@[simp] theorem sequenceLimit_cOne : sequenceLimit (cOne 𝕜) = 1 :=
  sequenceLimit_eq _ (by simp)

theorem norm_sequenceLimit_le (x : SequenceConvergent 𝕜) : ‖sequenceLimit x‖ ≤ ‖x‖ := by
  apply le_of_tendsto (tendsto_sequenceLimit x).norm
  exact Eventually.of_forall (fun n => lp.norm_apply_le_norm (by simp) x.val n)

/-- The scalar-linear limit functional, with its bound proved from convergence. -/
def limitFunctional : SequenceConvergent 𝕜 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := sequenceLimit
      map_add' := fun x y => sequenceLimit_eq _
        ((tendsto_sequenceLimit x).add (tendsto_sequenceLimit y))
      map_smul' := fun a x => sequenceLimit_eq _
        ((tendsto_sequenceLimit x).const_smul a) }
    1 (fun x => by simpa using norm_sequenceLimit_le x)

/-- The literal inclusion c₀ ⊆ c preserves coordinates and norm. -/
def c0Inclusion : SequenceC0 𝕜 →L[𝕜] SequenceConvergent 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨x.val, 0, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun _ => by simp)

@[simp] theorem c0Inclusion_apply (x : SequenceC0 𝕜) : (c0Inclusion x).val = x.val := rfl

@[simp] theorem sequenceLimit_c0Inclusion (x : SequenceC0 𝕜) :
    sequenceLimit (c0Inclusion x) = 0 := sequenceLimit_eq _ x.property

/-- Removing the limiting constant gives an element of the original c₀. -/
def cZeroPart (x : SequenceConvergent 𝕜) : SequenceC0 𝕜 :=
  ⟨(x - sequenceLimit x • cOne 𝕜).val, by
    have h := (tendsto_sequenceLimit x).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => sequenceLimit x) atTop (𝓝 (sequenceLimit x)))
    change Tendsto (fun n => x.val n - sequenceLimit x * (cOne 𝕜).val n) atTop (𝓝 0)
    simpa only [cOne_apply, mul_one, sub_self] using h⟩

@[simp] theorem cZeroPart_apply (x : SequenceConvergent 𝕜) (n : ℕ) :
    (cZeroPart x).val n = x.val n - sequenceLimit x := by
  change x.val n - sequenceLimit x * (cOne 𝕜).val n = _
  rw [cOne_apply, mul_one]

theorem cZeroPart_decomposition (x : SequenceConvergent 𝕜) :
    c0Inclusion (cZeroPart x) = x - sequenceLimit x • cOne 𝕜 := rfl

/-- Restriction to c₀ supplies the ℓ¹ coefficients; evaluation on one supplies
exactly the remaining coefficient. -/
theorem convergent_representation (L : SequenceConvergent 𝕜 →L[𝕜] 𝕜) :
    ∃ a : SequenceLp 𝕜 1, ∃ b : 𝕜,
      (∀ n, a n = L (c0Inclusion (c0Coordinate 𝕜 n))) ∧
      (∀ x, L x = (∑' n, a n * x.val n) + b * sequenceLimit x) := by
  let f := L.comp c0Inclusion
  let a := c0DualCoefficients f
  let b := L (cOne 𝕜) - ∑' n, a n
  have ha : Summable (fun n => a n) := by
    apply Summable.of_norm
    simpa using (lp.memℓp a).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  refine ⟨a, b, fun _ => rfl, ?_⟩
  intro x
  have hz := congrArg (fun g : SequenceC0 𝕜 →L[𝕜] 𝕜 => g (cZeroPart x))
    (c0SeriesFunctional_coefficients f)
  change (∑' n, a n * (cZeroPart x).val n) =
    L (c0Inclusion (cZeroPart x)) at hz
  simp only [cZeroPart_apply] at hz
  rw [cZeroPart_decomposition] at hz
  change (∑' n, a n * (x.val n - sequenceLimit x)) =
    L.toLinearMap (x - sequenceLimit x • cOne 𝕜) at hz
  rw [map_sub, map_smul] at hz
  simp only [ContinuousLinearMap.coe_coe] at hz
  have hs : (∑' n, a n * (x.val n - sequenceLimit x)) =
      (∑' n, a n * x.val n) - (∑' n, a n) * sequenceLimit x := by
    simp_rw [mul_sub]
    rw [((discrete_holder 𝕜 1 ∞ (by simp) a x.val).2.1).tsum_sub
      (ha.mul_right (sequenceLimit x)), ha.tsum_mul_right]
  rw [hs] at hz
  dsimp [b]
  simp only [smul_eq_mul] at hz
  linear_combination -hz

/-- The opposite norm bound uses absolute convergence and the limit bound. -/
theorem convergent_norm_le (L : SequenceConvergent 𝕜 →L[𝕜] 𝕜)
    (a : SequenceLp 𝕜 1) (b : 𝕜)
    (h : ∀ x, L x = (∑' n, a n * x.val n) + b * sequenceLimit x) :
    ‖L‖ ≤ ‖a‖ + ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [h x, add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_tsum_le_tsum_norm (discrete_holder 𝕜 1 ∞ (by simp) a x.val).1).trans
      (discrete_holder 𝕜 1 ∞ (by simp) a x.val).2.2
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sequenceLimit_le x) (norm_nonneg b)

/-- Finite phase tests with a constant tail give the sharp reverse bound on c. -/
theorem convergent_norm_ge (L : SequenceConvergent 𝕜 →L[𝕜] 𝕜)
    (a : SequenceLp 𝕜 1) (b : 𝕜)
    (h : ∀ x, L x = (∑' n, a n * x.val n) + b * sequenceLimit x) :
    ‖a‖ + ‖b‖ ≤ ‖L‖ := by
  classical
  have hanorm : Summable (fun n => ‖a n‖) := by
    simpa using (lp.memℓp a).summable (by simp)
  have ha : Summable (fun n => a n) := hanorm.of_norm
  have hcoord (n : ℕ) : L (c0Inclusion (c0Coordinate 𝕜 n)) = a n := by
    rw [h, sequenceLimit_c0Inclusion]
    simp only [c0Inclusion_apply, mul_zero, add_zero]
    exact c0SeriesFunctional_coordinate a n
  have hone : L (cOne 𝕜) = (∑' n, a n) + b := by
    simpa using h (cOne 𝕜)
  let t := c0DualPhase b
  let x (N : ℕ) : SequenceConvergent 𝕜 :=
    t • cOne 𝕜 + ∑ n ∈ Finset.range N,
      (c0DualPhase (a n) - t) • c0Inclusion (c0Coordinate 𝕜 n)
  have hx (N : ℕ) : ‖x N‖ ≤ 1 := by
    change ‖(x N).val‖ ≤ 1
    apply lp.norm_le_of_forall_le zero_le_one
    intro n
    change ‖(t • cOne 𝕜 + ∑ j ∈ Finset.range N,
      (c0DualPhase (a j) - t) • c0Inclusion (c0Coordinate 𝕜 j)).val n‖ ≤ 1
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
      lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sum, Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, c0Inclusion_apply, c0Coordinate_apply, cOne_apply,
      smul_eq_mul, mul_one, mul_ite, mul_zero]
    simp_rw [eq_comm (a := n)]
    rw [Finset.sum_ite_eq']
    split_ifs
    · simpa using c0DualPhase_norm_le (a n)
    · simpa [t] using c0DualPhase_norm_le b
  have hval (N : ℕ) : L (x N) =
      ((∑ n ∈ Finset.range N, ‖a n‖ : ℝ) : 𝕜) +
        t * (L (cOne 𝕜) - ∑ n ∈ Finset.range N, a n) := by
    change L.toLinearMap (t • cOne 𝕜 + ∑ n ∈ Finset.range N,
      (c0DualPhase (a n) - t) • c0Inclusion (c0Coordinate 𝕜 n)) = _
    simp only [map_add, map_sum, map_smul, ContinuousLinearMap.coe_coe,
      hcoord, smul_eq_mul]
    simp_rw [sub_mul, mul_comm (c0DualPhase _) _, mul_c0DualPhase]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [← RCLike.ofReal_sum]
    ring
  have ht : Tendsto (fun N => L (x N)) atTop (𝓝 ((‖a‖ + ‖b‖ : ℝ) : 𝕜)) := by
    have h1 := (RCLike.continuous_ofReal (K := 𝕜)).continuousAt.tendsto.comp hanorm.hasSum.tendsto_sum_nat
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => L (cOne 𝕜))
      atTop (𝓝 (L (cOne 𝕜)))).sub ha.hasSum.tendsto_sum_nat
    have h3 := h1.add (h2.const_mul t)
    have hnorm : (∑' n, ‖a n‖) = ‖a‖ := by
      simpa using (lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) a).symm
    simp only [Function.comp_def] at h3
    rw [hnorm, hone, add_sub_cancel_left] at h3
    have htb : t * b = (‖b‖ : 𝕜) := by
      dsimp [t]
      rw [mul_comm, mul_c0DualPhase]
    rw [htb, ← RCLike.ofReal_add] at h3
    apply h3.congr'
    apply Eventually.of_forall
    intro N
    have hv := hval N
    rw [hone] at hv
    exact hv.symm
  have hb := le_of_tendsto ht.norm
    (Eventually.of_forall fun N =>
      (L.le_opNorm (x N)).trans (mul_le_of_le_one_right (norm_nonneg L) (hx N)))
  rw [RCLike.norm_ofReal, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))] at hb
  exact hb

/-- Each pair of coefficients gives a continuous functional on c. -/
def convergentSeriesFunctional (a : SequenceLp 𝕜 1) (b : 𝕜) :
    SequenceConvergent 𝕜 →L[𝕜] 𝕜 :=
  ((lpSequencePairing 𝕜 ∞ 1 a).comp (convergentSubmodule 𝕜).subtypeL) +
    b • limitFunctional

@[simp] theorem convergentSeriesFunctional_apply (a : SequenceLp 𝕜 1) (b : 𝕜)
    (x : SequenceConvergent 𝕜) :
    convergentSeriesFunctional a b x = (∑' n, a n * x.val n) + b * sequenceLimit x := rfl

theorem convergentSeriesFunctional_norm (a : SequenceLp 𝕜 1) (b : 𝕜) :
    ‖convergentSeriesFunctional a b‖ = ‖a‖ + ‖b‖ :=
  le_antisymm (convergent_norm_le _ a b (fun _ => rfl))
    (convergent_norm_ge _ a b (fun _ => rfl))

theorem convergent_dual : Spec.ConvergentDual.{u} := by
  intro 𝕜 _ L
  obtain ⟨a, b, hcoord, h⟩ := convergent_representation L
  refine ⟨(a, b), (fun x => ⟨(discrete_holder 𝕜 1 ∞ (by simp) a x.val).1, h x⟩), ?_, ?_⟩
  · have hn : ‖a‖ = ∑' n, ‖a n‖ := by
      simpa using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) a
    rw [← hn]
    exact le_antisymm (convergent_norm_le L a b h) (convergent_norm_ge L a b h)
  · rintro ⟨c, d⟩ hd
    have hc : c = a := by
      apply lp.ext
      funext n
      have hv := hd (c0Inclusion (c0Coordinate 𝕜 n))
      rw [sequenceLimit_c0Inclusion, mul_zero, add_zero] at hv
      change L (c0Inclusion (c0Coordinate 𝕜 n)) = c0SeriesFunctional c (c0Coordinate 𝕜 n) at hv
      rw [c0SeriesFunctional_coordinate, ← hcoord n] at hv
      exact hv.symm
    subst c
    have hb := hd (cOne 𝕜)
    have hb' := h (cOne 𝕜)
    simp only [cOne_apply, mul_one, sequenceLimit_cOne] at hb hb'
    exact Prod.ext rfl (add_left_cancel (hb.symm.trans hb'))


/-- The definition of c is precisely all convergent scalar sequences. -/
theorem convergent_identification : Spec.ConvergentIdentification.{u} := by
  intro 𝕜 _
  refine ⟨?_, fun y => lp.norm_eq_ciSup y.val, tendsto_sequenceLimit⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · rintro ⟨l, hl⟩
    exact ⟨⟨⟨x, memℓp_infty hl.norm.bddAbove_range⟩, l, hl⟩, rfl⟩

theorem convergent_pairing : Spec.ConvergentPairing.{u} := by
  intro 𝕜 _ a b
  refine ⟨convergentSeriesFunctional a b,
    (fun x => ⟨(discrete_holder 𝕜 1 ∞ (by simp) a x.val).1, rfl⟩), ?_⟩
  rw [convergentSeriesFunctional_norm]
  congr 1
  simpa using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) a

end ExpandedFA.FunctionSpaces.SequenceDuals
