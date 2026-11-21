import MathGenome.Internal.FourierSobolev.Specs.P102.U4.NegativeLpPairingNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.U4

section Scalar
variable {𝕜 : Type} [RCLike 𝕜]

/-- A polar-power test written without division. At zero this is zero, also
when the real exponent in the prefactor is negative. -/
private def polarPower (r : ℝ) (z : 𝕜) : 𝕜 :=
  (‖z‖ ^ (r - 2)) • star z

private lemma norm_polarPower {r : ℝ} (hr : 1 < r) (z : 𝕜) :
    ‖polarPower r z‖ = ‖z‖ ^ (r - 1) := by
  by_cases hz : z = 0
  · simp [polarPower, hz, Real.zero_rpow (sub_pos.mpr hr).ne']
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [polarPower, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn.le _), norm_star]
    calc
      _ = ‖z‖ ^ ((r - 2) + 1) := (Real.rpow_add_one hn.ne' _).symm
      _ = _ := by congr 1; ring

private lemma polarPower_mul {r : ℝ} (hr : 1 < r) (z : 𝕜) :
    polarPower r z * z = (‖z‖ ^ r : ℝ) := by
  by_cases hz : z = 0
  · simp [polarPower, hz, Real.zero_rpow (by linarith : r ≠ 0)]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [polarPower, Algebra.smul_def, mul_assoc, RCLike.star_def, RCLike.conj_mul,
      ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_add hn]
    congr 1
    ring
end Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {𝕜 : Type} [RCLike 𝕜]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

private lemma polarPower_aestronglyMeasurable {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    AEStronglyMeasurable (fun x => polarPower r (f x)) μ :=
  (hf.norm.aemeasurable.pow_const (r - 2)).aestronglyMeasurable.smul hf.star

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
private lemma conjugate_power_exponent (hp : p ≠ ∞) (hq : q ≠ ∞) :
    p * ENNReal.ofReal (q.toReal - 1) = q := by
  have h := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    mul_comm, h.symm.sub_one_mul_conj, ENNReal.ofReal_toReal hq]

private lemma polarPower_eLpNorm (hp : p ≠ ∞) (hq : q ≠ ∞)
    (a : Lp 𝕜 q μ) :
    eLpNorm (fun x => polarPower q.toReal (a x)) p μ =
      eLpNorm a q μ ^ (q.toReal - 1) := by
  have h := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hm := polarPower_aestronglyMeasurable (Lp.aestronglyMeasurable a) q.toReal
  calc
    _ = eLpNorm (fun x => ‖a x‖ ^ (q.toReal - 1)) p μ := by
      apply eLpNorm_congr_norm_ae hm
        (Lp.aestronglyMeasurable a |>.norm.aemeasurable.pow_const _).aestronglyMeasurable
      filter_upwards with x
      rw [norm_polarPower h.symm.lt, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    _ = _ := by
      rw [eLpNorm_norm_rpow _ (Lp.aestronglyMeasurable a) h.symm.sub_one_pos,
        conjugate_power_exponent hp hq]

private lemma polarPower_memLp (hp : p ≠ ∞) (hq : q ≠ ∞) (a : Lp 𝕜 q μ) :
    MemLp (fun x => polarPower q.toReal (a x)) p μ := by
  change eLpNorm _ _ _ < ∞
  rw [polarPower_eLpNorm hp hq]
  exact ENNReal.rpow_lt_top_of_nonneg
    (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.sub_one_pos.le (Lp.eLpNorm_ne_top a)

omit [Fact (1 ≤ q)] in
private lemma integral_norm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : Lp 𝕜 q μ) :
    (∫ x, ‖a x‖ ^ q.toReal ∂μ) = ‖a‖ ^ q.toReal := by
  have hi : 0 ≤ ∫ x, ‖a x‖ ^ q.toReal ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hn : ‖a‖ = (∫ x, ‖a x‖ ^ q.toReal ∂μ) ^ q.toReal⁻¹ := by
    rw [Lp.norm_def, (Lp.memLp a).eLpNorm_eq_integral_rpow_norm hq0 hq,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hi _)]
  rw [hn, Real.rpow_inv_rpow hi (ENNReal.toReal_ne_zero.mpr ⟨hq0, hq⟩)]

/-- Hölder gives the upper bound for the bilinear scalar pairing. -/
lemma scalar_lpPairing_bound (a : Lp 𝕜 q μ) (v : Lp 𝕜 p μ) :
    ‖(ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q v a‖ ≤ ‖a‖ * ‖v‖ := by
  rw [ContinuousLinearMap.lpPairing]
  change ‖L1.integralCLM' 𝕜 ((ContinuousLinearMap.mul 𝕜 𝕜).holder 1 v a)‖ ≤ _
  rw [← L1.integral_eq']
  calc
    _ ≤ ‖(ContinuousLinearMap.mul 𝕜 𝕜).holder 1 v a‖ := L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖v‖ * ‖a‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖v‖ * ‖a‖ := by gcongr; exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
    _ = _ := by ring

/-- The sharp norm is measure-independent; no dual representation is used. -/
theorem scalar_lpPairing_norm (hp : p ≠ ∞) (hq : q ≠ ∞) (a : Lp 𝕜 q μ) :
    ‖((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).flip a‖ = ‖a‖ := by
  let L := ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).flip a
  apply le_antisymm
  · exact L.opNorm_le_bound (norm_nonneg a) (scalar_lpPairing_bound a)
  · by_cases ha : a = 0
    · simp [ha]
    have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have h := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    let hw := polarPower_memLp hp hq a
    let w : Lp 𝕜 p μ := hw.toLp _
    have hwn : ‖w‖ = ‖a‖ ^ (q.toReal - 1) := by
      rw [Lp.norm_toLp, polarPower_eLpNorm hp hq, ← ENNReal.toReal_rpow, Lp.norm_def]
    have hval : L w = (‖a‖ ^ q.toReal : ℝ) := by
      change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q w a = _
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      calc
        _ = ∫ x, ((‖a x‖ ^ q.toReal : ℝ) : 𝕜) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hw.coeFn_toLp] with x hx
          change w x * a x = _
          rw [hx, polarPower_mul h.symm.lt]
        _ = _ := by rw [integral_ofReal, integral_norm_rpow
          (ENNReal.HolderConjugate.ne_zero q p) hq]
    have hb := L.le_opNorm w
    rw [hval, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg hapos.le _), hwn] at hb
    have he : ‖a‖ ^ q.toReal = ‖a‖ * ‖a‖ ^ (q.toReal - 1) := by
      rw [mul_comm, ← Real.rpow_add_one hapos.ne']
      congr 1
      ring
    rw [he] at hb
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hapos _)).mp hb
end Measure

/-- Specialization to the canonical restricted Lebesgue spaces, including d=0. -/
theorem negative_lp_pairing_norm : NegativeLpPairingNormExpected.SharpNorm := by
  intro d 𝕜 _ Ω p hp ht
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro a
  apply scalar_lpPairing_norm ht
  exact ((ENNReal.HolderConjugate.lt_top_iff_one_lt (ENNReal.conjExponent p) p).mpr hp).ne

/-- There is no complex conjugation in the integral pairing itself. -/
theorem negative_lp_pairing_integral : NegativeLpPairingNormExpected.IntegralFormula := by
  intro d 𝕜 _ Ω p hp ht
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro a v
  constructor
  · change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing _ p _ v a = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    rfl
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm (v x) (a x)

end P102.U4
