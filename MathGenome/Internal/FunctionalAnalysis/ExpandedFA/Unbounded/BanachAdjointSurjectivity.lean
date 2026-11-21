import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjointSurjectivity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachClosedRangeTheorem

/-! Surjectivity criteria for closed densely defined Banach-space operators,
`paper.tex`, fa2:p3:banach-closed-range. All duals are scalar-linear. -/

noncomputable section
open Set Metric
namespace ExpandedFA.Unbounded.BanachAdjointSurjectivity

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A lower bound in the ambient norm forces the kernel to vanish. -/
theorem kernel_eq_bot_of_bound (A : Operator 𝕜 X Y) (C : ℝ)
    (hb : ∀ x : A.domain, ‖(x : X)‖ ≤ C * ‖A x‖) : A.ker = ⊥ := by
  apply bot_unique
  intro x hx
  let z : A.domain := ⟨x, A.ker_le_domain hx⟩
  have hz : A z = 0 := A.coe_mem_ker_iff.mp hx
  have hn := hb z
  rw [hz, norm_zero, mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg x))

/-- The same lower bound implies closed range, without a density assumption. -/
theorem closed_range_of_bound [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hc : A.IsClosed) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x : A.domain, ‖(x : X)‖ ≤ C * ‖A x‖) :
    _root_.IsClosed (A.toFun.range : Set Y) := by
  apply BanachClosedRangeDistance.closed_range_of_distance_bound A hc C hC
  intro x
  exact (infDist_le_dist_of_mem A.ker.zero_mem).trans (by
    simpa only [dist_zero_right] using hb x)

/-- Onto operators have a closed range, including when the target is zero. -/
theorem closed_range_of_surjective (A : Operator 𝕜 X Y)
    (hs : Function.Surjective A.toFun) : _root_.IsClosed (A.toFun.range : Set Y) := by
  have hr : (A.toFun.range : Set Y) = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    exact hs y
  rw [hr]
  exact isClosed_univ

end ExpandedFA.Unbounded.BanachAdjointSurjectivity

namespace ExpandedFA.Unbounded
open BanachAdjointSurjectivity BanachClosedRangeTheorem

/-- A is onto precisely when its Banach adjoint has an ambient norm lower bound. -/
theorem banach_surjectivity_criterion :
    BanachAdjointSurjectivitySpec.SurjectivityCriterion := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hd hc
  constructor
  · intro hs
    obtain ⟨C, hC, hpre⟩ := bounded_preimages A hc (closed_range_of_surjective A hs)
    refine ⟨C, hC, fun q => ?_⟩
    apply (q : Y →L[𝕜] 𝕜).opNorm_le_bound (mul_nonneg hC.le (norm_nonneg _))
    intro y
    obtain ⟨x, hx, hxn⟩ := hpre y (hs y)
    calc
      ‖(q : Y →L[𝕜] 𝕜) y‖ = ‖banachAdjoint A q (x : X)‖ := by
        rw [banachAdjoint_apply A hd q x, hx]
      _ ≤ ‖banachAdjoint A q‖ * ‖(x : X)‖ := (banachAdjoint A q).le_opNorm _
      _ ≤ ‖banachAdjoint A q‖ * (C * ‖y‖) :=
        mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
      _ = (C * ‖banachAdjoint A q‖) * ‖y‖ := by ring
  · rintro ⟨C, hC, hb⟩
    have hk := kernel_eq_bot_of_bound (banachAdjoint A) C hb
    have hr := closed_range_of_bound (banachAdjoint A) (banachAdjoint_closed A hd) C hC hb
    have hAr := closed_range_of_adjoint_norm_closed A hd hc hr
    have heq := (range_eq_preannihilator_iff A hd).mp hAr
    intro y
    have hy : y ∈ A.toFun.range := by
      change y ∈ (A.toFun.range : Set Y)
      rw [heq]
      intro q hq
      have hq0 : q = 0 := by simpa only [hk, Submodule.mem_bot] using hq
      rw [hq0, zero_apply]
    exact hy

/-- The Banach adjoint is onto precisely when A has an ambient norm lower bound. -/
theorem banach_adjoint_surjectivity_criterion :
    BanachAdjointSurjectivitySpec.AdjointSurjectivityCriterion := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hd hc
  constructor
  · intro hs
    obtain ⟨C, hC, hpre⟩ := bounded_preimages (banachAdjoint A)
      (banachAdjoint_closed A hd) (closed_range_of_surjective (banachAdjoint A) hs)
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨f, hfn, hfx⟩ := exists_dual_vector'' 𝕜 (x : X)
    obtain ⟨q, hq, hqn⟩ := hpre f (hs f)
    have hfval : ‖f (x : X)‖ = ‖(x : X)‖ := by
      rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖(x : X)‖ = ‖f (x : X)‖ := hfval.symm
      _ = ‖(q : Y →L[𝕜] 𝕜) (A x)‖ := by
        rw [← hq, banachAdjoint_apply A hd q x]
      _ ≤ ‖(q : Y →L[𝕜] 𝕜)‖ * ‖A x‖ := (q : Y →L[𝕜] 𝕜).le_opNorm _
      _ ≤ C * ‖A x‖ := mul_le_mul_of_nonneg_right
        (hqn.trans (mul_le_of_le_one_right hC.le hfn)) (norm_nonneg _)
  · rintro ⟨C, hC, hb⟩
    have hk := kernel_eq_bot_of_bound A C hb
    have hr := closed_range_of_bound A hc C hC hb
    have heq := adjoint_range_eq_of_closed_range A hd hc hr
    intro f
    have hf : f ∈ (banachAdjoint A).toFun.range := by
      change f ∈ ((banachAdjoint A).toFun.range : Set _)
      rw [heq]
      intro x hx
      have hx0 : x = 0 := by simpa only [hk, Submodule.mem_bot] using hx
      rw [hx0, map_zero]
    exact hf

end ExpandedFA.Unbounded
