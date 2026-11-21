import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.ConditionalIndependence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.ConditionalLaws
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.DisintegrationUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelComposition

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch04
universe u v w

open Specs.ProbabilityFoundations.Ch04.ConditionalProductCriterion

theorem standardBorel_binary_product : binaryProductType.{v,w} := by
  intro T U _ _ hT hU
  let := (isStandardBorel_iff T).mp hT
  let := (isStandardBorel_iff U).mp hU
  exact (isStandardBorel_iff (T × U)).mpr inferInstance

theorem conditional_product_laws_exist : existenceType.{u,v,w} := by
  intro Ω T U F mT mU P _ G hG hT hU Y Z hY hZ
  let : MeasurableSpace Ω := F
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  let : Nonempty T := Nonempty.map Y inferInstance
  let : Nonempty U := Nonempty.map Z inferInstance
  obtain ⟨KY, hKY, hYlaw⟩ := conditional_law P G hG hT Y hY
  obtain ⟨KZ, hKZ, hZlaw⟩ := conditional_law P G hG hU Z hZ
  obtain ⟨KJ, hKJ, hJlaw⟩ := conditional_law P G hG
    (standardBorel_binary_product T U hT hU) (fun ω => (Y ω, Z ω)) (hY.prodMk hZ)
  exact ⟨KY, KZ, KJ, hKY, hKZ, hKJ, hYlaw, hZlaw, hJlaw⟩

/-- Evaluation of a conditional law, as a real number, is a conditional
expectation version of the corresponding event indicator. -/
lemma conditionalLaw_eval_condExp {Ω : Type u} {T : Type v}
    [F : MeasurableSpace Ω] [mT : MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ F)
    (Y : Ω → T) (hY : @Measurable Ω T F mT Y) (K : @Kernel Ω T G _) [IsMarkovKernel K]
    (hK : @IsConditionalLaw Ω T F mT P G hG Y K) (B : Set T) (hB : MeasurableSet B) :
    (fun ω => (K ω B).toReal) =ᵐ[P]
      @Ch03.realConditionalExpectation Ω G F P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) := by
  let : MeasurableSpace Ω := F
  have hm : Measurable[G] (fun ω => (K ω B).toReal) := (K.measurable_coe hB).ennreal_toReal
  apply ((Ch03.isRealConditionalExpectationVersion_iff G P hG _ _
    ((integrable_const (1 : ℝ)).indicator (hY hB))).mp ?_).2
  refine ⟨hm, ?_, ?_⟩
  · apply (integrable_const (1 : ℝ)).mono' (hm.mono hG le_rfl).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
  · intro A hA
    rw [setIntegral_trim hG hm.stronglyMeasurable hA]
    rw [integral_toReal (K.measurable_coe hB).aemeasurable
      (Filter.Eventually.of_forall fun ω => measure_lt_top (K ω) B), hK A hA B hB]
    rw [integral_indicator_const (μ := P.restrict A) (1 : ℝ) (hY hB),
      smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply (hY hB), Set.inter_comm]

/-- Conditional independence is equivalent to simultaneous equality of the joint
conditional law and the product of its two conditional laws. -/
theorem conditional_product_criterion : criterionType.{u,v,w} := by
  intro Ω T U F mT mU P _ G hG hT hU Y Z hY hZ KY KZ KJ _ _ _ hKY hKZ hKJ
  let : MeasurableSpace Ω := F
  have eY := conditionalLaw_eval_condExp P G hG Y hY KY hKY
  have eZ := conditionalLaw_eval_condExp P G hG Z hZ KZ hKZ
  have eJ := conditionalLaw_eval_condExp P G hG (fun ω => (Y ω, Z ω))
    (hY.prodMk hZ) KJ hKJ
  change IsConditionallyIndependent G P Y Z ↔ _
  constructor
  · intro hind
    let : MeasurableSpace Ω := G
    let L := productKernel KY KZ
    have hrect (B : Set T) (C : Set U) (hB : MeasurableSet B) (hC : MeasurableSet C) :
        (fun ω => KJ ω (B ×ˢ C)) =ᵐ[P] (fun ω => L ω (B ×ˢ C)) := by
      filter_upwards [eY B hB, eZ C hC, eJ (B ×ˢ C) (hB.prod hC), hind B C hB hC]
        with ω ey ez ej hi
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      rw [show L ω (B ×ˢ C) = KY ω B * KZ ω C from
        productKernel_apply_rectangle KY KZ ω B C, ENNReal.toReal_mul, ey, ez, ej]
      exact hi
    have hrectTrim (B : Set T) (C : Set U) (hB : MeasurableSet B) (hC : MeasurableSet C) :
        (fun ω => KJ ω (B ×ˢ C)) =ᵐ[P.trim hG] (fun ω => L ω (B ×ˢ C)) :=
      ae_eq_trim_of_measurable hG (KJ.measurable_coe (hB.prod hC))
        (L.measurable_coe (hB.prod hC)) (hrect B C hB hC)
    have hcomp : (P.trim hG).compProd KJ = (P.trim hG).compProd L := by
      apply Measure.ext_prod₃
      intro A B C hA hB hC
      rw [Measure.compProd_apply_prod hA (hB.prod hC),
        Measure.compProd_apply_prod hA (hB.prod hC)]
      exact lintegral_congr_ae (ae_restrict_of_ae (hrectTrim B C hB hC))
    let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
    let : StandardBorelSpace U := (isStandardBorel_iff U).mp hU
    have hae : KJ =ᵐ[P.trim hG] L := Kernel.ae_eq_of_compProd_eq hcomp
    obtain ⟨N, hN, hzero, heq⟩ :=
      (Ch01.almostSurely_iff_measurable_null (P.trim hG) (fun ω => KJ ω = L ω)).mp hae
    refine ⟨N, hN, ?_, ?_⟩
    · rwa [trim_measurableSet_eq hG hN] at hzero
    · intro ω hω
      exact (heq ω hω).trans (productKernel_apply KY KZ ω)
  · rintro ⟨N, hN, hzero, heq⟩ B C hB hC
    have hae : ∀ᵐ ω ∂P, KJ ω = (KY ω).prod (KZ ω) :=
      (Ch01.almostSurely_iff_measurable_null P _).mpr ⟨N, hG _ hN, hzero, heq⟩
    filter_upwards [eY B hB, eZ C hC, eJ (B ×ˢ C) (hB.prod hC), hae]
      with ω ey ez ej hk
    have hr : KJ ω (B ×ˢ C) = KY ω B * KZ ω C := by rw [hk, Measure.prod_prod]
    have ht := congrArg ENNReal.toReal hr
    rw [ENNReal.toReal_mul, ey, ez, ej] at ht
    exact ht

end ProbabilityFoundations.Ch04
