import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SchauderHaar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SchauderHatBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HaarBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HaarUnconditional

/-! Assembly of the classical Schauder and Haar basis theorem from its
accepted hat, Haar, and interior unconditionality prerequisites. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal unitInterval
universe u

namespace ExpandedFA.P1.SchauderHaar

/-- The nonsummable L1 Haar expansion supplied upstream rules out
unconditionality of the basis in the finite-subset-net sense. -/
theorem haar_l1_conditional : Spec.HaarL1Conditionality.{u} := by
  intro 𝕜 _ hu
  obtain ⟨f, hf⟩ := HaarBasis.haar_conditional 𝕜
  have hordered : C01Banach.Spec.HasSequentialSumValue _
      (fun n => HaarBasis.Spec.haarCoefficient f n • HaarBasis.Spec.haarLp 𝕜 1 n) f := by
    apply (C01Banach.hasSequentialSum_iff _ _ _).mpr
    exact HaarBasis.haar_convergence 𝕜 1 (by simp) f
  exact hf ((C15Unconditional.unconditionallyConvergent_iff_summable _).mp
    (hu.2 f (HaarBasis.Spec.haarCoefficient f) hordered))

/-- The hats preceded by 1,t form a conditional basis of C[0,1];
the Haar functions preceded by 1 form a basis of Lp for 1≤p<∞,
conditional at p=1 and unconditional for 1<p<∞. -/
theorem function_space_bases : Spec.FunctionSpaceBases.{u} := by
  intro 𝕜 _
  exact ⟨SchauderHatBasis.basis_property 𝕜,
    HaarBasis.haar_basis 𝕜,
    SchauderHatBasis.conditionality 𝕜,
    haar_l1_conditional 𝕜,
    HaarUnconditional.haar_unconditional_basis 𝕜⟩

end ExpandedFA.P1.SchauderHaar
