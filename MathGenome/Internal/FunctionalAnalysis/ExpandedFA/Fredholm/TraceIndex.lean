import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.TraceIndex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonCalkin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity

noncomputable section
universe u v w
namespace ExpandedFA.Fredholm.TraceIndex
open TraceIdeals TraceClassDefinitions
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

lemma trace_sub (A B : H →L[𝕜] H) (hA : IsTraceClass A) (hB : IsTraceClass B) :
    trace (A - B) = trace A - trace B := by
  have ha := (TraceBasisCyclicity.diagonal_trace 𝕜 H A hA _
    TraceClassDefinitions.Spec.chosenBasis).2
  have hb := (TraceBasisCyclicity.diagonal_trace 𝕜 H B hB _
    TraceClassDefinitions.Spec.chosenBasis).2
  change (∑' i, inner 𝕜 (TraceClassDefinitions.Spec.chosenBasis i)
    ((A - B) (TraceClassDefinitions.Spec.chosenBasis i))) = _
  simpa only [sub_apply, inner_sub_right] using (ha.sub hb).tsum_eq

lemma trace_id_finite [FiniteDimensional 𝕜 H] :
    trace (ContinuousLinearMap.id 𝕜 H) = (Module.finrank 𝕜 H : 𝕜) := by
  let b := (stdOrthonormalBasis 𝕜 H).toHilbertBasis
  have ht := TraceNormIdeal.finite_rank_traceClass (ContinuousLinearMap.id 𝕜 H)
  have hh := (TraceBasisCyclicity.diagonal_trace 𝕜 H _ ht _ b).2.tsum_eq
  change TraceClassDefinitions.Spec.TraceValue (ContinuousLinearMap.id 𝕜 H) = _
  rw [← hh]
  simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]

/-- The trace of a finite orthogonal projection is its dimension. -/
lemma trace_starProjection (V : Submodule 𝕜 H) [FiniteDimensional 𝕜 V] :
    trace V.starProjection = (Module.finrank 𝕜 V : 𝕜) := by
  have hcyc := TraceBasisCyclicity.trace_comp_comm V.subtypeL V.orthogonalProjectionOnto
    (TraceNormIdeal.finite_rank_traceClass V.subtypeL)
  have hid : V.orthogonalProjectionOnto.comp V.subtypeL = ContinuousLinearMap.id 𝕜 V := by
    ext x
    simp
  rw [hid, trace_id_finite] at hcyc
  exact hcyc.symm

/-- A trace-class factor remains trace class after composition on the left. -/
lemma traceClass_comp_left {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace 𝕜 L] [CompleteSpace L]
    (A : K →L[𝕜] L) (B : H →L[𝕜] K)
    (hB : IsTraceClass B) : IsTraceClass (A.comp B) := by
  simpa only [ContinuousLinearMap.comp_id] using
    (TraceNormIdeal.two_sided_ideal 𝕜 H K H L B A
      (ContinuousLinearMap.id 𝕜 H) hB).1

/-- A trace-class factor remains trace class after composition on the right. -/
lemma traceClass_comp_right {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace 𝕜 L] [CompleteSpace L]
    (A : K →L[𝕜] L) (B : H →L[𝕜] K)
    (hA : IsTraceClass A) : IsTraceClass (A.comp B) := by
  simpa only [ContinuousLinearMap.id_comp] using
    (TraceNormIdeal.two_sided_ideal 𝕜 K L H L A
      (ContinuousLinearMap.id 𝕜 L) B hA).1

/-- Trace-class defects imply Fredholmness by the two-sided Atkinson theorem. -/
lemma fredholm_of_trace_defects (T : H →L[𝕜] K) (S : K →L[𝕜] H)
    (hD : IsTraceClass (ContinuousLinearMap.id 𝕜 H - S.comp T))
    (hE : IsTraceClass (ContinuousLinearMap.id 𝕜 K - T.comp S)) : IsFredholm T := by
  apply isFredholm_of_compact_parametrix T S
  · change Compactness.DefinitionsSpec.IsCompactLinearMapValue _
    simpa only [neg_sub] using
      (TraceNormIdeal.traceClass_neg _ hD).1.1
  · change Compactness.DefinitionsSpec.IsCompactLinearMapValue _
    simpa only [neg_sub] using
      (TraceNormIdeal.traceClass_neg _ hE).1.1

/-- The first-power trace-index formula, with arbitrary Hilbert dimensions. -/
theorem first_power_trace_index : Spec.FirstPowerTraceIndex.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T S hD hE
  have hT := fredholm_of_trace_defects T S hD hE
  refine ⟨hT, ?_⟩
  change (fredholmIndex T hT : 𝕜) =
    trace (ContinuousLinearMap.id 𝕜 H - S.comp T) -
      trace (ContinuousLinearMap.id 𝕜 K - T.comp S)
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : CompleteSpace T.range := hT.1.completeSpace_coe
  let : FiniteDimensional 𝕜 T.ker := hT.2.1
  let : FiniteDimensional 𝕜 (K ⧸ T.range) := hT.2.2
  let : FiniteDimensional 𝕜 T.rangeᗮ :=
    T.range.quotientEquivOrthogonal.toLinearEquiv.finiteDimensional
  obtain ⟨G, hGT, hTG⟩ := closed_range_generalized_inverse T hT.1
  let P := T.ker.starProjection
  let Q := T.rangeᗮ.starProjection
  have hTG' : T.comp G = ContinuousLinearMap.id 𝕜 K - Q := by
    rw [hTG]
    dsimp [Q]
    rw [T.range.starProjection_orthogonal]
    abel
  have hP : IsTraceClass P := by
    apply TraceNormIdeal.finite_rank_trace_class 𝕜 H H P
    dsimp [P]
    rw [Submodule.range_starProjection]
    infer_instance
  have hQ : IsTraceClass Q := by
    apply TraceNormIdeal.finite_rank_trace_class 𝕜 K K Q
    dsimp [Q]
    rw [Submodule.range_starProjection]
    infer_instance
  have hWT : IsTraceClass ((S - G).comp T) := by
    have heq : (S - G).comp T = P -
        (ContinuousLinearMap.id 𝕜 H - S.comp T) := by
      rw [ContinuousLinearMap.sub_comp, hGT]
      dsimp [P]
      abel
    rw [heq]
    exact TraceNormIdeal.traceClass_sub _ _ hP hD
  have hW : IsTraceClass (S - G) := by
    have heq : S - G = ((S - G).comp T).comp G + (S - G).comp Q := by
      rw [ContinuousLinearMap.comp_assoc, hTG', ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.comp_id]
      abel
    rw [heq]
    exact (TraceNormIdeal.traceClass_add _ _
      (traceClass_comp_right _ _ hWT) (traceClass_comp_left _ _ hQ)).1
  have hcyc := TraceBasisCyclicity.rectangular_cyclicity 𝕜 K H (S - G) T (Or.inl hW)
  have hcomm : trace (T.comp (S - G)) = trace ((S - G).comp T) := hcyc.2.2
  have hDeq : ContinuousLinearMap.id 𝕜 H - S.comp T = P - (S - G).comp T := by
    rw [ContinuousLinearMap.sub_comp, hGT]
    dsimp [P]
    abel
  have hEeq : ContinuousLinearMap.id 𝕜 K - T.comp S = Q - T.comp (S - G) := by
    rw [ContinuousLinearMap.comp_sub, hTG']
    abel
  have htrace : trace (ContinuousLinearMap.id 𝕜 H - S.comp T) -
      trace (ContinuousLinearMap.id 𝕜 K - T.comp S) = trace P - trace Q := by
    rw [hDeq, hEeq, trace_sub _ _ hP hcyc.2.1, trace_sub _ _ hQ hcyc.1,
      hcomm]
    abel
  rw [htrace, trace_starProjection, trace_starProjection]
  change (((Module.finrank 𝕜 T.ker : ℤ) -
    (Module.finrank 𝕜 (K ⧸ T.range) : ℤ) : ℤ) : 𝕜) = _
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    T.range.quotientEquivOrthogonal.toLinearEquiv.finrank_eq]

end ExpandedFA.Fredholm.TraceIndex
