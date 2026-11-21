import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TransposeNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualMaps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming

/-!
The reverse transpose estimate follows from the norming dual formula applied
to `T x`. The formula below follows from the accepted norming functional,
including at zero. Thus this proof needs no completeness assumption and
also applies to zero spaces.
-/

namespace ExpandedFA.P1.TransposeNorm

universe u v w

/-- Norming functionals identify the norm with the supremum over the dual
closed unit ball, for every vector including zero. -/
theorem norm_eq_dual_unitBall_sup (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖x‖ = sSup ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}) := by
  have hupper : ∀ b ∈ ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}),
      b ≤ ‖x‖ := by
    rintro b ⟨f, hf, rfl⟩
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hbdd : BddAbove ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}) :=
    ⟨‖x‖, hupper⟩
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
  have hmem : ‖x‖ ∈ ((fun f : E →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ ≤ 1}) := by
    refine ⟨f, hf, ?_⟩
    change ‖f x‖ = ‖x‖
    rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
  exact le_antisymm (le_csSup hbdd hmem) (csSup_le ⟨‖x‖, hmem⟩ hupper)

/-- The Banach transpose `T′f = f ∘ T` preserves the operator norm. -/
theorem banachTranspose_norm : Spec.BanachTransposeNormEquality.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ T
  apply le_antisymm (C04DualMaps.banachTranspose_norm_le 𝕜 E F T)
  apply T.opNorm_le_bound (norm_nonneg (C04Annihilators.banachTranspose 𝕜 E F T))
  intro x
  rw [norm_eq_dual_unitBall_sup 𝕜 F (T x)]
  apply csSup_le
  · exact ⟨0, ⟨0, by simp, by simp⟩⟩
  · rintro b ⟨f, hf, rfl⟩
    calc
      ‖f (T x)‖ = ‖C04Annihilators.banachTranspose 𝕜 E F T f x‖ := rfl
      _ ≤ ‖C04Annihilators.banachTranspose 𝕜 E F T f‖ * ‖x‖ :=
        (C04Annihilators.banachTranspose 𝕜 E F T f).le_opNorm x
      _ ≤ (‖C04Annihilators.banachTranspose 𝕜 E F T‖ * ‖f‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((C04Annihilators.banachTranspose 𝕜 E F T).le_opNorm f) (norm_nonneg x)
      _ ≤ (‖C04Annihilators.banachTranspose 𝕜 E F T‖ * 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hf
            (norm_nonneg (C04Annihilators.banachTranspose 𝕜 E F T))) (norm_nonneg x)
      _ = ‖C04Annihilators.banachTranspose 𝕜 E F T‖ * ‖x‖ := by rw [mul_one]

end ExpandedFA.P1.TransposeNorm
