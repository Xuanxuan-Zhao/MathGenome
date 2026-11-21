import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Bounded Borel functions are actual functions, with the uniform norm.
No reference measure or almost-everywhere quotient occurs in this definition. -/

noncomputable section

namespace ExpandedFA.Supplements.BoundedBorelBidualSpec

open MeasureTheory Set
open scoped ENNReal
universe u

variable (K : Type u) [MeasurableSpace K] (𝕜 : Type) [RCLike 𝕜]

/-- The measurable subspace of the bounded scalar functions. -/
def boundedBorelSubmodule : Submodule 𝕜 (lp (fun _ : K => 𝕜) ∞) where
  carrier := {f | Measurable (f : K → 𝕜)}
  zero_mem' := measurable_const
  add_mem' hf hg := hf.add hg
  smul_mem' _c _ hf := measurable_const.smul hf

abbrev BoundedBorel := boundedBorelSubmodule K 𝕜

instance : CoeFun (BoundedBorel K 𝕜) (fun _ => K → 𝕜) :=
  ⟨fun f => f.val⟩

variable {K 𝕜}

/-- A full bidual embedding, with its value specified against every finite
scalar Radon measure representing a continuous functional. Thus the displayed
integral uses ordinary multiplication, with no conjugation. -/
def BorelEmbedding (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K],
    ∃ e : BoundedBorel K 𝕜 →ₗᵢ[𝕜]
        StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)),
      ∀ (h : BoundedBorel K 𝕜) (ν : VectorMeasure K 𝕜),
        FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon ν →
        Integrable h ν.variation ∧
        ∀ (L : StrongDual 𝕜 C(K, 𝕜)),
          (∀ f : C(K, 𝕜), L f = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral ν f) →
          e h L = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral ν h

def RealBorelEmbedding : Prop := BorelEmbedding.{u} ℝ

def ComplexBorelEmbedding : Prop := BorelEmbedding.{u} ℂ

end ExpandedFA.Supplements.BoundedBorelBidualSpec
