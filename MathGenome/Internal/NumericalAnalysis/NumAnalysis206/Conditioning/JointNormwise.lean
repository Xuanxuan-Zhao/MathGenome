import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.JointNormwise
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped NNReal ENNReal
noncomputable section
universe u v w

namespace NumAnalysis206.Conditioning

abbrev jointNormwiseFeasible :=
  @Specs.NumAnalysis206.Conditioning.JointNormwise.jointNormwiseFeasible

abbrev jointNormwiseBackwardError :=
  @Specs.NumAnalysis206.Conditioning.JointNormwise.jointNormwiseBackwardError

section Construction
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- The rank one correction uses the norm-at-most-one version of Hahn--Banach,
which also works when the input vector or input space is zero. -/
lemma exists_jointNormwise_correction (x : X) (r : Y) (α β ε : ℝ≥0)
    (hD : 0 < (α : ℝ) * ‖x‖ + (β : ℝ))
    (hr : ‖r‖ ≤ (ε : ℝ) * ((α : ℝ) * ‖x‖ + (β : ℝ))) :
    ∃ (ΔA : X →L[𝕜] Y) (Δb : Y),
      ΔA x - Δb = r ∧ ‖ΔA‖₊ ≤ ε * α ∧ ‖Δb‖₊ ≤ ε * β := by
  let D : ℝ := (α : ℝ) * ‖x‖ + (β : ℝ)
  let c : Y := ((D⁻¹ : ℝ) : 𝕜) • r
  have hc : ‖c‖ = ‖r‖ / D := by
    change ‖((D⁻¹ : ℝ) : 𝕜) • r‖ = ‖r‖ / D
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hD)]
    rw [div_eq_mul_inv, mul_comm]
  have hce : ‖c‖ ≤ (ε : ℝ) := by
    rw [hc]
    exact (div_le_iff₀ hD).2 hr
  have hDc : (D : 𝕜) • c = r := by
    change (D : 𝕜) • (((D⁻¹ : ℝ) : 𝕜) • r) = r
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hD),
      RCLike.ofReal_one, one_smul]
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' 𝕜 x
  refine ⟨φ.smulRight (((α : ℝ) : 𝕜) • c), -(((β : ℝ) : 𝕜) • c), ?_, ?_, ?_⟩
  · calc
      (φ.smulRight (((α : ℝ) : 𝕜) • c)) x - -(((β : ℝ) : 𝕜) • c) =
          (D : 𝕜) • c := by
        simp only [ContinuousLinearMap.smulRight_apply, hφx, sub_neg_eq_add,
          smul_smul, ← add_smul]
        congr 1
        simp [D, RCLike.ofReal_add, RCLike.ofReal_mul, mul_comm]
      _ = r := hDc
  · change ‖φ.smulRight (((α : ℝ) : 𝕜) • c)‖₊ ≤ ε * α
    rw [← NNReal.coe_le_coe]
    change ‖φ.smulRight (((α : ℝ) : 𝕜) • c)‖ ≤ (ε : ℝ) * (α : ℝ)
    calc
      _ = ‖φ‖ * ((α : ℝ) * ‖c‖) := by
        simp [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      _ ≤ 1 * ((α : ℝ) * (ε : ℝ)) :=
        mul_le_mul hφ (mul_le_mul_of_nonneg_left hce α.2)
          (mul_nonneg α.2 (norm_nonneg c)) zero_le_one
      _ = (ε : ℝ) * (α : ℝ) := by ring
  · rw [← NNReal.coe_le_coe]
    change ‖-(((β : ℝ) : 𝕜) • c)‖ ≤ (ε : ℝ) * (β : ℝ)
    rw [norm_neg, norm_smul, RCLike.norm_ofReal]
    change |(β : ℝ)| * ‖c‖ ≤ (ε : ℝ) * (β : ℝ)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (β : ℝ) from β.2), mul_comm (ε : ℝ)]
    exact mul_le_mul_of_nonneg_left hce β.2

end Construction

theorem jointNormwiseFeasible_iff :
    Specs.NumAnalysis206.Conditioning.JointNormwise.jointNormwiseFeasible_iffStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b x α β ε
  constructor
  · rintro ⟨ΔA, Δb, heq, hA, hb⟩
    have hr : b - A x = ΔA x - Δb := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_apply, add_comm] using heq.symm
    rw [← NNReal.coe_le_coe] at hA hb ⊢
    change ‖ΔA‖ ≤ (ε : ℝ) * (α : ℝ) at hA
    change ‖Δb‖ ≤ (ε : ℝ) * (β : ℝ) at hb
    change ‖b - A x‖ ≤ (ε : ℝ) * ((α : ℝ) * ‖x‖ + (β : ℝ))
    calc
      _ = ‖ΔA x - Δb‖ := congrArg norm hr
      _ ≤ ‖ΔA x‖ + ‖Δb‖ := norm_sub_le _ _
      _ ≤ ‖ΔA‖ * ‖x‖ + ‖Δb‖ := add_le_add (ΔA.le_opNorm x) le_rfl
      _ ≤ (ε : ℝ) * ((α : ℝ) * ‖x‖ + (β : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_right hA (norm_nonneg x)]
  · intro h
    have hreal : ‖b - A x‖ ≤ (ε : ℝ) * ((α : ℝ) * ‖x‖ + (β : ℝ)) := by
      exact_mod_cast h
    by_cases hD : 0 < (α : ℝ) * ‖x‖ + (β : ℝ)
    · obtain ⟨ΔA, Δb, heq, hA, hb⟩ :=
        exists_jointNormwise_correction (𝕜 := 𝕜) x (b - A x) α β ε hD hreal
      refine ⟨ΔA, Δb, ?_, hA, hb⟩
      simpa only [add_apply, add_comm] using sub_eq_sub_iff_add_eq_add.mp heq
    · have hzero : b - A x = 0 := by
        apply norm_eq_zero.mp
        have hd : (α : ℝ) * ‖x‖ + (β : ℝ) = 0 :=
          le_antisymm (le_of_not_gt hD) (add_nonneg (mul_nonneg α.2 (norm_nonneg x)) β.2)
        rw [hd, mul_zero] at hreal
        exact le_antisymm hreal (norm_nonneg _)
      refine ⟨0, 0, ?_, by simp, by simp⟩
      simpa using (sub_eq_zero.mp hzero).symm

section Infimum
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

private lemma ratio_le_iff (A : X →L[𝕜] Y) (b : Y) (x : X) (α β ε : ℝ≥0) :
    (‖b - A x‖₊ : ℝ≥0∞) / ((α * ‖x‖₊ + β : ℝ≥0) : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ↔
      jointNormwiseFeasible A b x α β ε := by
  rw [ENNReal.div_le_iff_le_mul (.inr ENNReal.coe_ne_top) (.inl ENNReal.coe_ne_top)]
  constructor
  · intro h
    apply (jointNormwiseFeasible_iff A b x α β ε).mpr
    exact_mod_cast h
  · intro h
    have := (jointNormwiseFeasible_iff A b x α β ε).mp h
    exact_mod_cast this

end Infimum

theorem jointNormwiseBackwardError_formula :
    Specs.NumAnalysis206.Conditioning.JointNormwise.jointNormwiseBackwardError_formulaStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b x α β
  let q : ℝ≥0∞ := (‖b - A x‖₊ : ℝ≥0∞) / ((α * ‖x‖₊ + β : ℝ≥0) : ℝ≥0∞)
  change sInf {t | ∃ ε : ℝ≥0, jointNormwiseFeasible A b x α β ε ∧ ↑ε = t} = q
  apply le_antisymm
  · by_cases hq : q = ⊤
    · rw [hq]
      exact le_top
    · apply sInf_le
      refine ⟨q.toNNReal, ?_, ENNReal.coe_toNNReal hq⟩
      exact (ratio_le_iff A b x α β q.toNNReal).mp
        (le_of_eq (ENNReal.coe_toNNReal hq).symm)
  · apply le_sInf
    rintro t ⟨ε, hε, rfl⟩
    exact (ratio_le_iff A b x α β ε).mpr hε

theorem jointNormwiseBackwardError_attained :
    Specs.NumAnalysis206.Conditioning.JointNormwise.jointNormwiseBackwardError_attainedStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b x α β hfinite
  refine ⟨(jointNormwiseBackwardError A b x α β).toNNReal,
    ENNReal.coe_toNNReal hfinite, ?_⟩
  apply (ratio_le_iff A b x α β _).mp
  rw [← jointNormwiseBackwardError_formula A b x α β,
    ENNReal.coe_toNNReal hfinite]

end NumAnalysis206.Conditioning
