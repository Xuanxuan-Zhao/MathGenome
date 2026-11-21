import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Products
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach

/-! Finite products with their power-sum and maximum norms.
All metrics on `PiLp` have the product uniformity. In particular completeness
here is completeness of the displayed norm, not a separately chosen topology.
-/

noncomputable section
open scoped ENNReal NNReal
universe u v w
namespace ExpandedFA.P1.C02Products

/-- The manuscript finite p-norm. -/
def finiteProductPNorm : Spec.ProductPNormType.{u,v} :=
  Spec.ProductPNormValue

/-- The manuscript maximum norm, with empty maximum zero. -/
def finiteProductMaxNorm : Spec.ProductMaxNormType.{u,v} :=
  Spec.ProductMaxNormValue

theorem finite_product_norm_formulas : Spec.NormFormulas.{u,v} := by
  intro ι _ E _ p hp x
  constructor
  · simpa [Spec.ProductPNormValue, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
      using PiLp.norm_eq_sum (p := ENNReal.ofReal p)
        (by simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
          (lt_of_lt_of_le zero_lt_one hp)) (WithLp.toLp (ENNReal.ofReal p) x)
  · exact PiLp.norm_toLp x

theorem finite_product_norm_axioms :
  ∀ (𝕜 : Type w) [RCLike 𝕜] {ι : Type u} [Fintype ι]
    (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ), 1 ≤ p →
    C01Norm.NormAxioms 𝕜 (Spec.ProductPNormValue E p) ∧
    C01Norm.NormAxioms 𝕜 (Spec.ProductMaxNormValue E) := by
  intro 𝕜 _ ι _ E _ _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have axioms (q : ℝ≥0∞) [Fact (1 ≤ q)] :
      C01Norm.NormAxioms 𝕜 (fun x : ∀ i, E i => ‖WithLp.toLp q x‖) := by
    refine ⟨⟨fun x => norm_nonneg _, ?_, ?_⟩, ?_⟩
    · intro a x
      simpa only [WithLp.toLp_smul] using norm_smul a (WithLp.toLp q x)
    · intro x y
      simpa only [WithLp.toLp_add] using norm_add_le (WithLp.toLp q x) (WithLp.toLp q y)
    · intro x
      simp
  have hfin : Spec.ProductPNormValue E p =
      fun x => ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
    funext x
    exact ((finite_product_norm_formulas E p hp x).1).symm
  have hmax : Spec.ProductMaxNormValue E =
      fun x => ‖WithLp.toLp ∞ x‖ := by
    funext x
    exact ((finite_product_norm_formulas E p hp x).2).symm
  rw [hfin, hmax]
  exact ⟨axioms _, axioms _⟩

theorem finite_product_same_topology : Spec.SameTopology.{u,v} := by
  intro ι _ E _ p q _ _
  exact ⟨(PiLp.homeomorph p E).isHomeomorph,
    ((PiLp.homeomorph p E).trans (PiLp.homeomorph q E).symm).isHomeomorph⟩

theorem finite_product_norm_comparison : Spec.NormComparison.{u,v} := by
  intro ι _ E _ p hp x
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hmax : Spec.ProductMaxNormValue E x = ‖x‖ := rfl
  rw [← (finite_product_norm_formulas E p hp x).1, hmax]
  constructor
  · simpa using
      (PiLp.lipschitzWith_ofLp (ENNReal.ofReal p) E).dist_le_mul
        (WithLp.toLp (ENNReal.ofReal p) x) 0
  · simpa [NNReal.coe_rpow, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
      (PiLp.lipschitzWith_toLp (ENNReal.ofReal p) E).dist_le_mul x 0

theorem finite_product_coordinate_maps :
  ∀ (𝕜 : Type w) [RCLike 𝕜] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι),
    ∃ P : PiLp p E →L[𝕜] E i,
      (∀ x, P x = x i) ∧ ‖P‖ ≤ 1 ∧
      ∃ I : E i →L[𝕜] PiLp p E,
        (∀ a, WithLp.ofLp (I a) = Pi.single i a) ∧ ‖I‖ ≤ 1 := by
  intro 𝕜 _ ι _ _ E _ _ p _ i
  let P : PiLp p E →L[𝕜] E i := PiLp.proj p E i
  refine ⟨P, fun _ => rfl, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa [P] using PiLp.norm_apply_le x i
  · let I : E i →L[𝕜] PiLp p E :=
      LinearMap.mkContinuous
        ((WithLp.linearEquiv p 𝕜 (∀ i, E i)).symm.toLinearMap.comp
          (LinearMap.single 𝕜 E i))
        1 (fun a => by simpa using (PiLp.norm_single p E i a).le)
    refine ⟨I, fun a => rfl, ?_⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    simp [I, LinearMap.mkContinuous_apply]

theorem finite_product_banach_iff : Spec.BanachIff.{u,v} := by
  intro ι _ E _ p _
  constructor
  · intro h i
    letI : CompleteSpace (PiLp p E) := (C01Banach.isBanachSpace_iff_completeSpace _).mp h
    apply (C01Banach.isBanachSpace_iff_completeSpace _).mpr
    classical
    apply Metric.complete_of_cauchySeq_tendsto
    intro s hs
    have hiso : Isometry (PiLp.single p i : E i → PiLp p E) :=
      fun a b => PiLp.edist_single_same p E i a b
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hiso.uniformContinuous.comp_cauchySeq hs)
    refine ⟨a i, ?_⟩
    simpa [Function.comp_def] using ((PiLp.continuous_apply p E i).tendsto a).comp ha
  · intro h
    letI : ∀ i, CompleteSpace (E i) :=
      fun i => (C01Banach.isBanachSpace_iff_completeSpace _).mp (h i)
    exact (C01Banach.isBanachSpace_iff_completeSpace _).mpr inferInstance

theorem finite_product_empty : Spec.EmptyProduct.{u,v} := by
  intro ι _ _ E _ p _
  have hz (x : PiLp p E) : x = 0 := PiLp.ext (fun i => isEmptyElim i)
  refine ⟨fun x => ⟨hz x, by rw [hz x, norm_zero]⟩, ?_, ?_, fun i => isEmptyElim i⟩
  · intro x
    simp [Spec.ProductMaxNormValue, Finset.univ_eq_empty]
  · apply (finite_product_banach_iff E p).mpr
    exact fun i => isEmptyElim i

end ExpandedFA.P1.C02Products
