import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBasicity

/-! Assertion 1 of `fa2:p1:dual-bases` (paper.tex 4321–4327).
The coordinate functionals carry the inherited operator norm in their closed
linear span. Bounded completeness means convergence of ordered partial sums,
with arbitrary scalar coefficients. Shrinking uses the shared equivalent
norm-convergence definition. Both real and complex Banach spaces are included. -/

open scoped BigOperators

noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisBoundedComplete.Spec

/-- The dual coordinate basic sequence is boundedly complete exactly when
its original Schauder basis is shrinking. -/
def DualBoundedCompleteIffShrinking : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) (DualBasisBasicity.Spec.dualVector b) ↔
      DualBasisBasicity.Spec.IsShrinking b

/-- The assertion for a raw norm-convergent basis, with its continuous
coordinate functionals identified by the shared coordinate construction. -/
def RawDualBoundedCompleteIffShrinking : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = C15Basis.Spec.rawCoordinates h x i) ∧
      (DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜)
        (DualBasisBasicity.Spec.dualVector b) ↔ DualBasisBasicity.Spec.IsShrinking b)

/-- Finite-list version of assertion 1, including the empty basis of the zero
space. The finite initial sums retain exactly the indices whose value is < N. -/
def FiniteDualBoundedCompleteIffShrinking : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ} (b : UnconditionalSchauderBasis (Fin d) 𝕜 E),
    let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
    let e' : Fin d → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self i))⟩
    (∀ a : Fin d → 𝕜,
      BddAbove (Set.range (fun N => ‖∑ i ∈ Finset.univ.filter
        (fun i : Fin d => i.val < N), a i • e' i‖)) →
      ∃ f : F, Filter.Tendsto (fun N => ∑ i ∈ Finset.univ.filter
        (fun i : Fin d => i.val < N), a i • e' i) Filter.atTop (nhds f)) ↔
    (∀ f : E →L[𝕜] 𝕜, Filter.Tendsto (fun N => ∑ i ∈ Finset.univ.filter
      (fun i : Fin d => i.val < N), f (b i) • b.coord i) Filter.atTop (nhds f))

end ExpandedFA.P1.DualBasisBoundedComplete.Spec
