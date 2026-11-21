import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Independent statement of paper.tex:11754–11779.
`HilbertBasis` is an orthonormal basis, represented by its isometric coefficient
identification with ℓ². `HasSum` uses the net over all finite subsets. The
arbitrary index type strengthens the stated sequence theorem, including finite
and empty bases. The field is ℝ or ℂ, with inner products linear in the second
variable. No boundedness, compactness, or independence certificate is assumed.
-/
noncomputable section
open scoped lp

namespace ExpandedFA.CompactSpectral.QuadraticBasisPerturbations.Spec
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {ι : Type w}

/-- The image-of-an-orthonormal-basis definition, relative to the given basis. -/
def IsRieszBasis (e : HilbertBasis ι 𝕜 H) (y : ι → H) : Prop :=
  ∃ U : H ≃L[𝕜] H, ∀ i, U (e i) = y i

/-- Invertibility of the actual synthesis map and unique ℓ² expansions. -/
def RieszConclusion (e : HilbertBasis ι 𝕜 H) (y : ι → H)
    (B : H →L[𝕜] H) : Prop :=
  (∃ U : H ≃L[𝕜] H, U.toContinuousLinearMap = B) ∧
  IsRieszBasis e y ∧ ∀ x : H, ∃! c : ℓ²(ι, 𝕜), HasSum (fun i => c i • y i) x

def QuadraticPerturbations : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : HilbertBasis ι 𝕜 H) (y : ι → H),
    Summable (fun i => ‖y i - e i‖ ^ 2) →
    ∃ B : H →L[𝕜] H,
      (∀ i, B (e i) = y i) ∧
      (∀ c : ℓ²(ι, 𝕜), HasSum (fun i => c i • y i) (B (e.repr.symm c))) ∧
      IsCompactOperator (B - ContinuousLinearMap.id 𝕜 H) ∧
      ‖B - ContinuousLinearMap.id 𝕜 H‖ ≤ Real.sqrt (∑' i, ‖y i - e i‖ ^ 2) ∧
      (Function.Injective B ↔
        ∀ c : ℓ²(ι, 𝕜), HasSum (fun i => c i • y i) 0 → c = 0) ∧
      (Function.Injective B → RieszConclusion e y B) ∧
      ((∑' i, ‖y i - e i‖ ^ 2) < 1 → RieszConclusion e y B)

end ExpandedFA.CompactSpectral.QuadraticBasisPerturbations.Spec
