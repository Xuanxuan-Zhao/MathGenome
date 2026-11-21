import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelIntegration
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04
namespace ConditionalIntegration
universe u v w

/-- The first marginal in a joint-kernel law is necessarily the law of X. -/
theorem joint_first_marginal {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure Ω) (X : Ω → S) (Y : Ω → T)
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K]
    (hLaw : P.map (fun ω => (X ω, Y ω)) = μ.compProd K) : P.map X = μ := by
  calc
    P.map X = (P.map (fun ω => (X ω, Y ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (hX.prodMk hY)]
      rfl
    _ = (μ.compProd K).map Prod.fst := congrArg (fun ν => ν.map Prod.fst) hLaw
    _ = μ := Measure.fst_compProd μ K

/-- The joint-law conditional integration identity for nonnegative functions. -/
theorem nonnegative_joint :
    Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration.nonnegativeJointType := by
  intro Ω S T F mS mT P hP X Y hX hY μ hμP K hK hLaw f hf
  have hμ := joint_first_marginal P X Y hX hY μ K hLaw
  have hLaw : P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K := by
    simpa only [hμ] using hLaw
  have hm := kernel_lintegral_measurable K f hf
  refine ⟨hm.comp (Measurable.of_comap_le le_rfl), ?_⟩
  rintro A ⟨B, hB, rfl⟩
  calc
    (∫⁻ ω in X ⁻¹' B, ∫⁻ y, f (X ω, y) ∂K (X ω) ∂P) =
        ∫⁻ s in B, ∫⁻ y, f (s, y) ∂K s ∂P.map X :=
      (setLIntegral_map hB hm hX).symm
    _ = ∫⁻ z in B ×ˢ Set.univ, f z ∂(P.map X).compProd K := by
      simpa only [Measure.restrict_univ] using
        (Measure.setLIntegral_compProd hf hB MeasurableSet.univ).symm
    _ = ∫⁻ ω in X ⁻¹' B, f (X ω, Y ω) ∂P := by
      rw [← hLaw, setLIntegral_map (hB.prod MeasurableSet.univ) hf (hX.prodMk hY)]
      simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]

/-- Signed joint-law formula and all measurable extensions. -/
theorem real_joint :
    Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration.realJointType := by
  intro Ω S T F mS mT P hP X Y hX hY μ hμP K hK hLaw f hf hfi
  have hμ := joint_first_marginal P X Y hX hY μ K hLaw
  have hLaw : P.map (fun ω => (X ω, Y ω)) = (P.map X).compProd K := by
    simpa only [hμ] using hLaw
  have hfi' : Integrable f (kernelMeasure (P.map X) K) := by
    rw [kernelMeasure, ← hLaw]
    exact (integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).mpr hfi
  have hae := ae_of_ae_map hX.aemeasurable (kernel_ae_integrable (P.map X) K f hf hfi')
  have hm := kernel_integral_measurable K f hf
  have hi := (kernel_integral (P.map X) K f hf hfi').1.comp_measurable hX
  have hv : Ch03.IsRealConditionalExpectationVersion (mS.comap X) P
      (fun ω => f (X ω, Y ω)) (fun ω => ∫ y, f (X ω, y) ∂K (X ω)) := by
    refine ⟨hm.comp (Measurable.of_comap_le le_rfl), hi, ?_⟩
    rintro A ⟨B, hB, rfl⟩
    calc
      (∫ ω in X ⁻¹' B, ∫ y, f (X ω, y) ∂K (X ω) ∂P) =
          ∫ s in B, ∫ y, f (s, y) ∂K s ∂P.map X :=
        (setIntegral_map hB hm.stronglyMeasurable.aestronglyMeasurable hX.aemeasurable).symm
      _ = ∫ z in B ×ˢ Set.univ, f z ∂(P.map X).compProd K := by
        simpa only [Measure.restrict_univ] using
          (Measure.setIntegral_compProd hB MeasurableSet.univ hfi'.integrableOn).symm
      _ = ∫ ω in X ⁻¹' B, f (X ω, Y ω) ∂P := by
        rw [← hLaw, setIntegral_map (hB.prod MeasurableSet.univ)
          hf.stronglyMeasurable.aestronglyMeasurable (hX.prodMk hY).aemeasurable]
        simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
  refine ⟨hae, hv, ?_⟩
  intro g hg hgf
  have heq : (fun ω => g (X ω)) =ᵐ[P] (fun ω => ∫ y, f (X ω, y) ∂K (X ω)) := by
    filter_upwards [hae] with ω hω
    exact hgf (X ω) hω.2
  refine ⟨hg.comp (Measurable.of_comap_le le_rfl), hv.2.1.congr heq.symm, ?_⟩
  intro A hA
  exact (integral_congr_ae (ae_restrict_of_ae heq)).trans (hv.2.2 A hA)

/-- Rectangle tests identify the entire joint law of the G-measurable identity
and Y. Only finite-measure uniqueness on product rectangles is used. -/
theorem conditional_joint_law {Ω : Type u} {T : Type w}
    [F : MeasurableSpace Ω] [mT : MeasurableSpace T]
    (G : MeasurableSpace Ω) (P : Measure[F] Ω) [IsProbabilityMeasure P]
    (hGF : G ≤ F) (Y : Ω → T) (hY : Measurable[F] Y)
    (K : @Kernel Ω T G mT) [IsMarkovKernel K]
    (htest : ∀ A, MeasurableSet[G] A → ∀ B, MeasurableSet B →
      (∫⁻ ω in A, K ω B ∂P) = P (A ∩ Y ⁻¹' B)) :
    @Measure.map Ω (Ω × T) F (G.prod mT) (fun ω => (ω, Y ω)) P =
      (@Measure.map Ω Ω F G id P).compProd K := by
  have hId : @Measurable Ω Ω F G id := measurable_id'' hGF
  have hpair : @Measurable Ω (Ω × T) F (G.prod mT) (fun ω => (ω, Y ω)) :=
    hId.prodMk hY
  apply Measure.ext_prod
  intro A B hA hB
  calc
    (@Measure.map Ω (Ω × T) F (G.prod mT) (fun ω => (ω, Y ω)) P) (A ×ˢ B) =
        P (A ∩ Y ⁻¹' B) := by
      exact Measure.map_apply (μ := P) hpair (hA.prod hB)
    _ = ∫⁻ ω in A, K ω B ∂P := (htest A hA B hB).symm
    _ = ∫⁻ ω in A, K ω B ∂(@Measure.map Ω Ω F G id P) := by
      simpa only [Set.preimage_id, id_eq] using
        (@setLIntegral_map Ω Ω F G P (fun ω => K ω B) id A
          hA (K.measurable_coe hB) hId).symm
    _ = ((@Measure.map Ω Ω F G id P).compProd K) (A ×ˢ B) :=
      (Measure.compProd_apply_prod hA hB).symm

/-- Nonnegative conditional integration for the original sigma algebra G. -/
theorem nonnegative_conditional :
    Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration.nonnegativeConditionalType := by
  intro Ω T F mT G P hP hGF Y hY K hK htest f hf
  have hId : @Measurable Ω Ω F G id := measurable_id'' hGF
  have hLaw := @conditional_joint_law Ω T F mT G P hP hGF Y hY K hK htest
  have h := @nonnegative_joint Ω Ω T F G mT P hP id Y hId hY
    (@Measure.map Ω Ω F G id P) inferInstance K hK hLaw f hf
  simpa only [MeasurableSpace.comap_id, id_eq] using h

/-- Signed conditional integration, including all measurable exceptional values. -/
theorem real_conditional :
    Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration.realConditionalType := by
  intro Ω T F mT G P hP hGF Y hY K hK htest f hf hfi
  have hId : @Measurable Ω Ω F G id := measurable_id'' hGF
  have hLaw := @conditional_joint_law Ω T F mT G P hP hGF Y hY K hK htest
  have h := @real_joint Ω Ω T F G mT P hP id Y hId hY
    (@Measure.map Ω Ω F G id P) inferInstance K hK hLaw f hf hfi
  simpa only [MeasurableSpace.comap_id, id_eq] using h

end ConditionalIntegration
end ProbabilityFoundations.Ch04
