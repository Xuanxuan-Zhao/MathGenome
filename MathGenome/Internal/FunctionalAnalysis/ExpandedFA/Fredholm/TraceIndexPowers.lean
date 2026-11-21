import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.TraceIndexPowers
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.TraceIndex

noncomputable section
universe u v w
namespace ExpandedFA.Fredholm.TraceIndexPowers
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]

/-- The finite geometric-series regularizer, constructed recursively.
Its defects are the powers of the original defects, even when the original
defects are not compact. -/
lemma exists_power_regularizer (T : H →L[𝕜] K) (S : K →L[𝕜] H) (m : ℕ) :
    ∃ R : K →L[𝕜] H,
      ContinuousLinearMap.id 𝕜 H - R.comp T =
        (ContinuousLinearMap.id 𝕜 H - S.comp T) ^ m ∧
      ContinuousLinearMap.id 𝕜 K - T.comp R =
        (ContinuousLinearMap.id 𝕜 K - T.comp S) ^ m := by
  induction m with
  | zero =>
    exact ⟨0, by simp [ContinuousLinearMap.one_def], by simp [ContinuousLinearMap.one_def]⟩
  | succ m ih =>
    obtain ⟨R, hH, hK⟩ := ih
    let D := ContinuousLinearMap.id 𝕜 H - S.comp T
    let E := ContinuousLinearMap.id 𝕜 K - T.comp S
    have hTD : T.comp D = E.comp T := by
      simp [D, E, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_assoc]
    refine ⟨S + D.comp R, ?_, ?_⟩
    · rw [pow_succ', ContinuousLinearMap.mul_def, ← hH,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc]
      dsimp [D]
      abel
    · rw [pow_succ', ContinuousLinearMap.mul_def, ← hK,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc, hTD,
        ContinuousLinearMap.comp_assoc]
      dsimp [E]
      abel

/-- Apply the first-power formula to the finite geometric-series regularizer. -/
theorem powered_trace_index : Spec.PoweredTraceIndex.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T S m _hm hH hK
  obtain ⟨R, hR_H, hR_K⟩ := exists_power_regularizer T S m
  have hH' : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (ContinuousLinearMap.id 𝕜 H - R.comp T) := by rwa [hR_H]
  have hK' : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (ContinuousLinearMap.id 𝕜 K - T.comp R) := by rwa [hR_K]
  obtain ⟨hT, hindex⟩ := TraceIndex.first_power_trace_index 𝕜 H K T R hH' hK'
  exact ⟨hT, by simpa only [hR_H, hR_K] using hindex⟩

end ExpandedFA.Fredholm.TraceIndexPowers
