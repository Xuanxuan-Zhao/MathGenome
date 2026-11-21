import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatTraceLift
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatExactTrace
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.TraceEndpointOne

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology

namespace P102.Trace
open P102.U4

namespace EndpointLift

lemma index_cases {d : ℕ} (α : SobolevIndex d 1) :
    α.val = 0 ∨ ∃ j, α.val = {j} := by
  have h := α.property
  by_cases hz : α.val.card = 0
  · exact Or.inl (Multiset.card_eq_zero.mp hz)
  · exact Or.inr (Multiset.card_eq_one.mp (by omega))

/-- Smooth functions with integrable first derivatives belong to the genuine
weak derivative graph. All coordinates, including order zero, are specified. -/
lemma smooth_mem {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (f : Space d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hi : ∀ α : SobolevIndex d 1, IntegrableOn (multiPartial f α.val) Ω) :
    ∃ u : Sobolev 𝕜 Ω 1 1,
      (∀ α : SobolevIndex d 1,
        (sobolevDerivative u α : Space d → 𝕜) =ᵐ[volume.restrict Ω]
          multiPartial f α.val) := by
  let v (α : SobolevIndex d 1) : DomainLp 𝕜 Ω 1 :=
    (memLp_one_iff_integrable.mpr (hi α)).toLp (multiPartial f α.val)
  have hv (α : SobolevIndex d 1) :
      (v α : Space d → 𝕜) =ᵐ[volume.restrict Ω] multiPartial f α.val :=
    MemLp.coeFn_toLp _
  have hv0 : (v (zeroSobolevIndex d 1) : Space d → 𝕜) =ᵐ[volume.restrict Ω] f := by
    simpa [zeroSobolevIndex, multiPartial, partialWord] using hv (zeroSobolevIndex d 1)
  have hfl : LocallyIntegrableOn f Ω volume :=
    hf.continuous.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hreg0 := (regular_injectivity d 𝕜 Ω _ _
    (domainLp_locallyIntegrable Ω 1 (v (zeroSobolevIndex d 1))) hfl).mpr hv0
  have heq (α : SobolevIndex d 1) :
      distributionPartial α.val (regularDistribution Ω (v (zeroSobolevIndex d 1))) =
        regularDistribution Ω (v α) := by
    rw [hreg0, derivative_classicalCompatibility d 𝕜 Ω α.val f (hf.of_le (by simp)).contDiffOn]
    exact ((regular_injectivity d 𝕜 Ω _ _
      (domainLp_locallyIntegrable Ω 1 (v α))
      ((hi α).locallyIntegrableOn)).mpr (hv α)).symm
  refine ⟨⟨WithLp.toLp 1 v, (mem_sobolevSubmodule_iff Ω 1 1 _).mpr ?_⟩, ?_⟩
  · intro α φ
    exact (distributionPartial_eq_regularLp_iff Ω 1 α.val _ _).mp (heq α) φ
  · exact hv

/-- Change from the finite product to Euclidean coordinates preserves volume. -/
lemma coordinates_measurePreserving (d : ℕ) :
    MeasurePreserving (ACL.coordinates d) volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin d)).symm
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))

lemma coordinate_vector (d : ℕ) (j : Fin d) :
    ACL.coordinates d (coordinateVector d j) =
      ExpandedFA.Distributions.coordinateVector j := by
  ext k
  by_cases hk : k = j
  · subst k
    simp [ACL.coordinates, coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single, ExpandedFA.Distributions.coordinateVector]
  · simp [ACL.coordinates, coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single, ExpandedFA.Distributions.coordinateVector, hk]

open ExpandedFA.PartIV.TraceEndpointOne in
/-- A smooth boundary tensor is lifted into this project's Euclidean weak
Sobolev graph, with a separate mass and normal-variation estimate. -/
lemma smooth_tensor {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hac : HasCompactSupport a)
    (f : Boundary m → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ u : HalfSobolev m 𝕜 1,
      (sobolevUnderlying u : Space (m+1) → 𝕜) =ᵐ[volume.restrict (halfSpace m)]
        (fun x => a (x (Fin.last m)) • f (transverseProjection (Fin.last m) (ACL.coordinates (m+1) x))) ∧
      ‖u‖ ≤ (Fintype.card (SobolevIndex (m+1) 1) : ℝ) *
        ((∫ t, ‖a t‖) * ((∫ y, ‖f y‖) + ∫ y, ‖fderiv ℝ f y‖) +
          (∫ t, ‖deriv a t‖) * ∫ y, ‖f y‖) := by
  let i := Fin.last m
  let e := ACL.coordinates (m+1)
  let H : (Fin (m+1) → ℝ) → 𝕜 := fun x => a (x i) • f (transverseProjection i x)
  let F : Space (m+1) → 𝕜 := H ∘ e
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    (ha.comp (ContinuousLinearMap.proj i : (Fin (m+1) → ℝ) →L[ℝ] ℝ).contDiff).smul
      (hf.comp (transverseProjection i).contDiff)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hH.comp e.contDiff
  have hai : Integrable a := ha.continuous.integrable_of_hasCompactSupport hac
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hadi : Integrable (deriv a) := (ha.continuous_deriv (by simp)).integrable_of_hasCompactSupport hac.deriv
  have hfdi : Integrable (fderiv ℝ f) := (hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hfc.fderiv ℝ)
  have hHi : Integrable H := tensor_integrable i a f hai hfi
  have hmp := coordinates_measurePreserving (m+1)
  have hFi : Integrable F := hmp.integrable_comp_of_integrable hHi
  let M : (Fin (m+1) → ℝ) → ℝ := fun x =>
    ‖a (x i)‖ * ‖fderiv ℝ f (transverseProjection i x)‖ +
      ‖deriv a (x i)‖ * ‖f (transverseProjection i x)‖
  have hM1 := tensor_integrable i (fun t => ‖a t‖) (fun y => ‖fderiv ℝ f y‖) hai.norm hfdi.norm
  have hM2 := tensor_integrable i (fun t => ‖deriv a t‖) (fun y => ‖f y‖) hadi.norm hfi.norm
  have hMi : Integrable M := hM1.add hM2
  have hME : Integrable (M ∘ e) := hmp.integrable_comp_of_integrable hMi
  have hD (j : Fin (m+1)) (x : Space (m+1)) :
      ‖fderiv ℝ F x (coordinateVector (m+1) j)‖ ≤ M (e x) := by
    have he : fderiv ℝ F x (coordinateVector (m+1) j) =
        fderiv ℝ H (e x) (ExpandedFA.Distributions.coordinateVector j) := by
      rw [fderiv_comp x (hH.differentiable (by simp) _) e.differentiableAt]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]
      exact congrArg (fderiv ℝ H (e x)) (coordinate_vector (m+1) j)
    rw [he]
    exact tensor_derivative_bound i a ha f hf (e x) j
  have hDi (j : Fin (m+1)) :
      Integrable (fun x => fderiv ℝ F x (coordinateVector (m+1) j)) :=
    hME.mono' ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      (ae_of_all _ (hD j))
  have hpartial (α : SobolevIndex (m+1) 1) : Integrable (multiPartial F α.val) := by
    rcases index_cases α with hz | ⟨j, hj⟩
    · simpa [hz, multiPartial, partialWord] using hFi
    · simpa [hj, multiPartial, partialWord] using hDi j
  obtain ⟨u, hu⟩ := smooth_mem (halfSpace m) F hF (fun α => (hpartial α).restrict)
  refine ⟨u, ?_, ?_⟩
  · simpa [sobolevUnderlying, zeroSobolevIndex, multiPartial, partialWord, F, H, Function.comp_def, i, e]
      using hu (zeroSobolevIndex (m+1) 1)
  let A := ∫ t, ‖a t‖
  let B := ∫ t, ‖deriv a t‖
  let G := ∫ y, ‖f y‖
  let D := ∫ y, ‖fderiv ℝ f y‖
  have hMInt : (∫ x, M x) = A * D + B * G := by
    change (∫ x : (Fin (m+1) → ℝ), ‖a (x i)‖ • ‖fderiv ℝ f (transverseProjection i x)‖ +
      ‖deriv a (x i)‖ • ‖f (transverseProjection i x)‖) = _
    rw [integral_add hM1 hM2]
    have h1 := tensor_norm_integral i a (fderiv ℝ f)
    have h2 := tensor_norm_integral i (deriv a) f
    simpa only [norm_smul, smul_eq_mul, A, B, G, D] using congrArg₂ (· + ·) h1 h2
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hG : 0 ≤ G := integral_nonneg fun _ => norm_nonneg _
  have hD0 : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hbound (α : SobolevIndex (m+1) 1) : ‖sobolevDerivative u α‖ ≤ A * (G + D) + B * G := by
    rw [lp_one_norm, integral_congr_ae ((hu α).mono fun x hx => congrArg norm hx)]
    apply le_trans (integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => norm_nonneg _) (hpartial α).norm)
    rcases index_cases α with hz | ⟨j, hj⟩
    · simp only [hz, multiPartial, Multiset.sort_zero, partialWord]
      change (∫ x, ‖H (e x)‖) ≤ _
      rw [hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun x => ‖H x‖), tensor_norm_integral]
      dsimp [A, B, G, D] at *
      nlinarith
    · simp only [hj, multiPartial, Multiset.sort_singleton, partialWord]
      apply le_trans (integral_mono (hDi j).norm hME (hD j))
      change (∫ x : Space (m+1), M (ACL.coordinates (m+1) x)) ≤ _
      rw [hmp.integral_comp e.toHomeomorph.measurableEmbedding M, hMInt]
      nlinarith
  rw [sobolev_norm]
  calc
    (∑ α : SobolevIndex (m+1) 1, ‖sobolevDerivative u α‖) ≤
        ∑ _α : SobolevIndex (m+1) 1, (A * (G + D) + B * G) := by
      exact Finset.sum_le_sum fun α _ => hbound α
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl

/-- Slice uniqueness identifies every slice trace with the trace carrying the
upstream smooth-restriction theorem. -/
lemma slice_trace_compatibility
    (hunique : FlatTraceExpected.SliceUniqueness)
    (htrace : FlatTraceExpected.TraceExists)
    {m : ℕ} (hm : 1 ≤ m) {𝕜 : Type} [RCLike 𝕜]
    (T : HalfSobolev m 𝕜 1 →L[𝕜] BoundaryLp m 𝕜 1) (hT : IsFlatTrace T)
    (u : HalfSobolev m 𝕜 1) (f : Space (m+1) → 𝕜)
    (hf : ContinuousOn f {x | 0 ≤ x (Fin.last m)})
    (hu : (sobolevUnderlying u : Space (m+1) → 𝕜) =ᵐ[volume.restrict (halfSpace m)] f) :
    (T u : Boundary m → 𝕜) =ᵐ[volume] fun z => f (point m z 0) := by
  obtain ⟨_, _, S, _, hS, hcompat⟩ := htrace m hm 𝕜 1 (by norm_num)
  have heq : T u = S u := by
    obtain ⟨F, hF, hF0⟩ := hT u
    obtain ⟨G, hG, hG0, _⟩ := hS u
    exact hF0.symm.trans ((hunique m 𝕜 1 u F G hF hG (by simp)).trans hG0)
  rw [heq]
  exact hcompat u f hf hu

open ExpandedFA.PartIV.TraceEndpointOne in
/-- The thickness is chosen separately for each smooth datum. The constant
uses only a fixed one-dimensional bump and the number of derivative indices. -/
lemma smooth_lift_bound {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : HalfSobolev m 𝕜 1 →L[𝕜] BoundaryLp m 𝕜 1)
    (hcompat : ∀ (u : HalfSobolev m 𝕜 1) (f : Space (m+1) → 𝕜),
      ContinuousOn f {x | 0 ≤ x (Fin.last m)} →
      (sobolevUnderlying u : Space (m+1) → 𝕜) =ᵐ[volume.restrict (halfSpace m)] f →
      (T u : Boundary m → 𝕜) =ᵐ[volume] fun z => f (point m z 0))
    (B : ℝ) (hB : 0 ≤ B)
    (hprofiles : ∀ ε > (0 : ℝ), ∃ b : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ b 0 = 1 ∧
      (∫ t, ‖b t‖) ≤ ε ∧ (∫ t, ‖deriv b t‖) ≤ B)
    (g : BoundaryLp m 𝕜 1) (hg : g ∈ compactSmoothBoundary (Fin.last m)) :
    ∃ u : HalfSobolev m 𝕜 1, T u = g ∧
      ‖u‖ ≤ ((Fintype.card (SobolevIndex (m+1) 1) : ℝ) * (B+1)) * ‖g‖ := by
  by_cases hz : g = 0
  · subst g
    exact ⟨0, map_zero T, by simp⟩
  obtain ⟨f, hgf, hfc, hf⟩ := hg
  let D : ℝ := ∫ y, ‖fderiv ℝ f y‖
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hz
  have hden : 0 < ‖g‖ + D + 1 := by positivity
  obtain ⟨a, ha, hac, ha0, hmass, hvar⟩ := hprofiles (‖g‖ / (‖g‖ + D + 1)) (div_pos hn hden)
  obtain ⟨u, hu, hnorm⟩ := smooth_tensor a ha hac f hf hfc
  have hG : (∫ y, ‖f y‖) = ‖g‖ := by
    rw [lp_one_norm]
    exact integral_congr_ae (hgf.symm.mono fun x hx => congrArg norm hx)
  refine ⟨u, ?_, ?_⟩
  · apply Lp.ext
    have hsm : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Space (m+1) => a (x (Fin.last m)) •
          f (transverseProjection (Fin.last m) (ACL.coordinates (m+1) x))) :=
      ((ha.comp (ContinuousLinearMap.proj (Fin.last m) : (Fin (m+1) → ℝ) →L[ℝ] ℝ).contDiff).smul
        (hf.comp (transverseProjection (Fin.last m)).contDiff)).comp (ACL.coordinates (m+1)).contDiff
    have ht := hcompat u _ hsm.continuous.continuousOn hu
    filter_upwards [ht, hgf] with z hz hgz
    rw [hz]
    have hc : ACL.coordinates (m+1) (point m z 0) =
        ExpandedFA.Sobolev.Lines.coordinateLine (Fin.last m) z 0 :=
      ACL.line_coordinates (Fin.last m) z 0
    have hh : point m z 0 (Fin.last m) = 0 :=
      ExpandedFA.Sobolev.Lines.coordinateLine_self (Fin.last m) z 0
    rw [hc, hh, transverseProjection_coordinateLine, ha0, one_smul]
    exact hgz.symm
  · apply hnorm.trans
    rw [hG]
    have hsmall : (∫ t, ‖a t‖) * (‖g‖ + D) ≤ ‖g‖ := by
      calc
        _ ≤ (‖g‖ / (‖g‖ + D + 1)) * (‖g‖ + D + 1) := by
          exact mul_le_mul hmass (by linarith) (by positivity) (by positivity)
        _ = ‖g‖ := div_mul_cancel₀ _ hden.ne'
    have hnormal := mul_le_mul_of_nonneg_right hvar (norm_nonneg g)
    have hN : 0 ≤ (Fintype.card (SobolevIndex (m+1) 1) : ℝ) := by positivity
    calc
      _ ≤ (Fintype.card (SobolevIndex (m+1) 1) : ℝ) * (‖g‖ + B * ‖g‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hsmall hnormal) hN
      _ = _ := by ring

/-- Completion supplies weak derivatives as limits in the closed derivative
graph, while continuity of the original trace recovers the boundary datum. -/
lemma endpoint (hunique : FlatTraceExpected.SliceUniqueness)
    (htrace : FlatTraceExpected.TraceExists) : FlatTraceLiftExpected.Endpoint := by
  obtain ⟨B, hB, hprofiles⟩ := ExpandedFA.PartIV.TraceEndpointOne.thin_profiles
  intro m hm
  let C : ℝ := (Fintype.card (SobolevIndex (m+1) 1) : ℝ) * (B + 1)
  have hC : 0 < C := by
    have hn : 0 < (Fintype.card (SobolevIndex (m+1) 1) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨zeroSobolevIndex (m+1) 1⟩
    exact mul_pos hn (by positivity)
  refine ⟨C + 1, by positivity, ?_⟩
  intro 𝕜 _
  constructor
  · obtain ⟨_, _, T, _, hT, _⟩ := htrace m hm 𝕜 1 (by norm_num)
    refine ⟨T, fun u => ?_⟩
    obtain ⟨F, hF, hF0, _⟩ := hT u
    exact ⟨F, hF, hF0⟩
  · intro T hT
    let K := (ExpandedFA.PartIV.TraceEndpointOne.compactSmoothBoundary (𝕜 := 𝕜)
      (Fin.last m)).toAddSubgroup
    let f : NormedAddGroupHom (HalfSobolev m 𝕜 1) (BoundaryLp m 𝕜 1) :=
      T.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖T‖ T.le_opNorm
    have hlift : f.SurjectiveOnWith K C := by
      intro g hg
      exact smooth_lift_bound T (slice_trace_compatibility hunique htrace hm T hT)
        B hB hprofiles g hg
    have hall := controlled_closure_of_complete hC (show (0 : ℝ) < 1 by norm_num) hlift
    intro g
    apply hall g
    have hd := ExpandedFA.PartIV.TraceEndpointOne.compactSmoothBoundary_dense (𝕜 := 𝕜) (Fin.last m)
    change g ∈ closure (ExpandedFA.PartIV.TraceEndpointOne.compactSmoothBoundary (𝕜 := 𝕜) (Fin.last m) : Set _)
    rw [hd.closure_eq]
    trivial

end EndpointLift

/-- The full flat trace and lift lemma: sharp bounded linear lifting for
1 < p < ∞, and quantitative surjectivity for p = 1. -/
theorem flat_trace_lift : FlatTraceLiftExpected.FlatTraceLift :=
  ⟨exact_flat_trace, EndpointLift.endpoint slice_unique flat_trace_exists⟩

end P102.Trace
