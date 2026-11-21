import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.DistanceSupportDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Tactic.Linarith

/-! Distance/support duality, paper.tex:6082–6121.
The upper bound is the dual norm inequality followed by approximation to the
infimum. For the lower bound normalize the quantitative real separators at
every positive radius below the distance, then extend them isometrically to
the scalar field. All suprema are extended suprema.
-/
noncomputable section
namespace ExpandedFA.Supplements.DistanceSupportDuality
universe u v
open Set Metric

def supportFunction : Spec.SupportFunctionType.{u,v} := Spec.SupportFunctionValue

theorem support_not_bot : Spec.SupportNotBot.{u,v} := by
  intro 𝕜 E _ _ _ K hK f
  obtain ⟨k, hk⟩ := hK
  have heval : (RCLike.re (f k) : EReal) ≤ Spec.SupportFunctionValue K f := by
    change _ ≤ ⨆ k ∈ K, (RCLike.re (f k) : EReal)
    exact le_iSup₂ (f := fun y (_ : y ∈ K) => (RCLike.re (f y) : EReal)) k hk
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) heval

theorem infinite_support_term : Spec.InfiniteSupportTerm.{u,v} := by
  intro 𝕜 E _ _ _ K f hf x
  rw [hf, EReal.sub_top]

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma le_supportFunction (K : Set E) (f : E →L[𝕜] 𝕜) (k : E) (hk : k ∈ K) :
    (RCLike.re (f k) : EReal) ≤ supportFunction K f := by
  change _ ≤ ⨆ k ∈ K, (RCLike.re (f k) : EReal)
  exact le_iSup₂ (f := fun y (_ : y ∈ K) => (RCLike.re (f y) : EReal)) k hk

lemma support_zero (K : Set E) (hK : K.Nonempty) :
    supportFunction K (0 : E →L[𝕜] 𝕜) = 0 := by
  obtain ⟨k, hk⟩ := hK
  apply le_antisymm
  · apply iSup₂_le
    intro y hy
    simp
  · simpa using le_supportFunction K (0 : E →L[𝕜] 𝕜) k hk

/-- Each term in the dual supremum is at most the distance. -/
lemma support_gap_le_infDist (K : Set E) (hK : K.Nonempty) (x : E)
    (f : E →L[𝕜] 𝕜) (hf : ‖f‖ ≤ 1) :
    (RCLike.re (f x) : EReal) - supportFunction K f ≤ (infDist x K : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  have hdr : infDist x K < r := EReal.coe_lt_coe_iff.mp hr
  obtain ⟨k, hk, hkr⟩ := (infDist_lt_iff hK).mp hdr
  have hle : RCLike.re (f x) - RCLike.re (f k) ≤ dist x k := by
    calc
      RCLike.re (f x) - RCLike.re (f k) = RCLike.re (f (x - k)) := by
        rw [map_sub, map_sub]
      _ ≤ ‖f (x - k)‖ := RCLike.re_le_norm _
      _ ≤ ‖f‖ * ‖x - k‖ := f.le_opNorm _
      _ ≤ 1 * ‖x - k‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ = dist x k := by rw [one_mul, dist_eq_norm]
  calc
    (RCLike.re (f x) : EReal) - supportFunction K f
      ≤ (RCLike.re (f x) : EReal) - (RCLike.re (f k) : EReal) :=
        EReal.sub_le_sub le_rfl (le_supportFunction K f k hk)
    _ = ((RCLike.re (f x) - RCLike.re (f k) : ℝ) : EReal) :=
      (EReal.coe_sub _ _).symm
    _ ≤ (r : EReal) := EReal.coe_le_coe_iff.mpr (hle.trans hkr.le)

section RealGeometry
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Positive radii strictly below the distance are realized as lower bounds
by normalized separators, without asserting realization of the distance. -/
lemma exists_support_gap (K : Set E) (hK : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (x : E) (r : ℝ) (hr : 0 < r) (hrd : r < infDist x K) :
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧
      (r : EReal) ≤ (RCLike.re (f x) : EReal) - supportFunction K f := by
  have hx : x ∉ K := by
    intro hx
    have := infDist_le_dist_of_mem (x := x) hx
    simp only [dist_self] at this
    linarith
  obtain ⟨h, hn, hb, _, hgap⟩ :=
    ExpandedFA.P1.C06.real_point_strong_separation_quantitative
      K x hK hc hv hx r hr hrd
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hn
  let g : E →L[ℝ] ℝ := ‖h‖⁻¹ • h
  have hg : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ hpos.ne']
  have hgk (k : E) (hk : k ∈ K) : r ≤ g x - g k := by
    have hks : h k ≤ sSup (h '' K) := le_csSup hb ⟨k, hk, rfl⟩
    change r ≤ ‖h‖⁻¹ * h x - ‖h‖⁻¹ * h k
    rw [← mul_sub, inv_mul_eq_div]
    exact (le_div_iff₀ hpos).mpr (by linarith)
  let f : E →L[𝕜] 𝕜 := StrongDual.extendRCLike g
  have hfre (y : E) : RCLike.re (f y) = g y :=
    StrongDual.re_extendRCLike_apply g y
  have hfs : supportFunction K f ≤ ((g x - r : ℝ) : EReal) := by
    apply iSup₂_le
    intro k hk
    rw [hfre]
    exact EReal.coe_le_coe_iff.mpr (by linarith [hgk k hk])
  refine ⟨f, ?_, ?_⟩
  · exact (StrongDual.norm_extendRCLike g).trans hg |>.le
  · calc
      (r : EReal) = (RCLike.re (f x) : EReal) - ((g x - r : ℝ) : EReal) := by
        rw [hfre, ← EReal.coe_sub]
        congr 1
        ring
      _ ≤ (RCLike.re (f x) : EReal) - supportFunction K f :=
        EReal.sub_le_sub le_rfl hfs

lemma distance_support (K : Set E) (hK : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (x : E) :
    (infDist x K : EReal) =
      ⨆ (f : E →L[𝕜] 𝕜) (_ : ‖f‖ ≤ 1),
        (RCLike.re (f x) : EReal) - supportFunction K f := by
  apply le_antisymm
  · have hzero : (0 : EReal) ≤
        ⨆ (f : E →L[𝕜] 𝕜) (_ : ‖f‖ ≤ 1),
          (RCLike.re (f x) : EReal) - supportFunction K f := by
      have hh := le_iSup₂ (f := fun (f : E →L[𝕜] 𝕜) (_ : ‖f‖ ≤ 1) =>
        (RCLike.re (f x) : EReal) - supportFunction K f)
        (0 : E →L[𝕜] 𝕜) (by simp : ‖(0 : E →L[𝕜] 𝕜)‖ ≤ 1)
      simpa only [zero_apply, map_zero, EReal.coe_zero, support_zero K hK,
        sub_zero] using hh
    by_contra hn
    obtain ⟨r, hsr, hrd⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have hr : 0 < r := EReal.coe_lt_coe_iff.mp (hzero.trans_lt hsr)
    obtain ⟨f, hf, hgap⟩ := exists_support_gap (𝕜 := 𝕜) K hK hc hv x r hr
      (EReal.coe_lt_coe_iff.mp hrd)
    have hterm := le_iSup₂ (f := fun (g : E →L[𝕜] 𝕜) (_ : ‖g‖ ≤ 1) =>
      (RCLike.re (g x) : EReal) - supportFunction K g) f hf
    exact (not_lt_of_ge (hgap.trans hterm)) hsr
  · apply iSup₂_le
    intro f hf
    exact support_gap_le_infDist K hK x f hf

end RealGeometry

theorem real_distance_support : Spec.RealDistanceSupport.{v} := by
  intro E _ _ K hK hc hv x
  exact distance_support K hK hc hv x

theorem complex_distance_support : Spec.ComplexDistanceSupport.{v} := by
  intro E _ _ K hK hc hv x
  exact distance_support K hK hc hv x

theorem complex_realification : Spec.ComplexRealification.{v} := by
  intro E _ _ h
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  refine ⟨f, ?_, ?_, StrongDual.norm_extendRCLike h, ?_⟩
  · intro x
    exact StrongDual.extendRCLike_apply (𝕜 := ℂ) h x
  · intro x
    exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x
  · intro g hg
    have heq : (StrongDual.extendRCLikeₗ (𝕜 := ℂ) (F := E)).symm g = h := by
      ext x
      exact hg x
    have := congrArg (StrongDual.extendRCLikeₗ (𝕜 := ℂ) (F := E)) heq
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end ExpandedFA.Supplements.DistanceSupportDuality
