import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! The completeness portion of fa2:p4:sobolev-calculus, and the Hilbert
structure specified in fa2:p4:sobolev-definition. No boundary regularity,
positive dimension, or nonemptiness assumption is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.Sobolev

/-- Change only the finite product norm from ℓ¹ to ℓ². -/
def derivativeTupleToL2 (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (ExpandedFA.Distributions.Domain d)) (m : ℕ) :
    DerivativeTuple 𝕜 Ω m 2 ≃L[𝕜]
      PiLp 2 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2) :=
  (PiLp.continuousLinearEquiv 1 𝕜 _).trans
    (PiLp.continuousLinearEquiv 2 𝕜 _).symm

/-- Exactly the same derivative identities, in the Euclidean product norm. -/
def hilbertDerivativeGraph (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (ExpandedFA.Distributions.Domain d)) (m : ℕ) :
    Submodule 𝕜 (PiLp 2 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2)) :=
  (derivativeGraph 𝕜 Ω m 2).comap (derivativeTupleToL2 𝕜 Ω m).symm.toLinearMap

end ExpandedFA.Sobolev

namespace Specs.ExpandedFA.Sobolev.SobolevCompleteness
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions

def ClosedGraph : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  IsClosed (derivativeGraph 𝕜 Ω m p : Set (DerivativeTuple 𝕜 Ω m p))

def Banach : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  CompleteSpace (WeakDerivativeSpaces.SpaceValue 𝕜 d Ω m p)

def Separable : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  p < ∞ → SeparableSpace (WeakDerivativeSpaces.SpaceValue 𝕜 d Ω m p)

/-- Reflexivity means surjectivity of the canonical scalar-linear bidual map. -/
def Reflexive : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  1 < p → p < ∞ → Function.Surjective
    (NormedSpace.inclusionInDoubleDual 𝕜 (WeakDerivativeSpaces.SpaceValue 𝕜 d Ω m p))

/-- A Hilbert space realization with precisely the usual derivative-tuple
inner product, its Euclidean norm, and explicit equivalence to the sum norm. -/
def HilbertStructure : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ),
  CompleteSpace (hilbertDerivativeGraph 𝕜 Ω m) ∧
  ∃ e : WeakDerivativeSpaces.SpaceValue 𝕜 d Ω m 2 ≃L[𝕜] hilbertDerivativeGraph 𝕜 Ω m,
    (∀ u α, (e u).val α = u.val α) ∧
    (∀ u v, ⟪e u, e v⟫_𝕜 = ∑ α, ⟪u.val α, v.val α⟫_𝕜) ∧
    (∀ u, ‖e u‖ = WeakDerivativeSpaces.HilbertNormValue 𝕜 d Ω m u) ∧
    (∀ u, ‖e u‖ ≤ ‖u‖ ∧
      ‖u‖ ≤ (Fintype.card (DerivativeIndex d m) : ℝ) * ‖e u‖)

end Specs.ExpandedFA.Sobolev.SobolevCompleteness
