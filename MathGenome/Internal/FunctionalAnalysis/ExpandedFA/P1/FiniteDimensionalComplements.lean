import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteDimensionalComplements
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02TopologicalSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension

/-!
Finite-dimensional subspaces of arbitrary normed spaces are complemented.
We extend the bounded coordinates of a finite basis using the accepted
norm-preserving Hahn–Banach theorem. Their finite synthesis is a continuous
linear retraction onto the subspace. Its ambient-valued version is the
required bounded projection. No completeness of the ambient space is used.
-/
noncomputable section
namespace ExpandedFA.P1.FiniteDimensionalComplements

universe u v

/-- Extend the coordinates of a finite basis and synthesize a retraction. -/
theorem finite_dimensional_retraction
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M] :
    ∃ r : E →L[𝕜] M, ∀ m : M, r (m : E) = m := by
  let b := Module.finBasis 𝕜 M
  let f := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose g hg hnorm using fun i =>
    C05NormExtension.norm_preserving_extension 𝕜 E M (f i)
  let r : E →L[𝕜] M :=
    b.equivFunL.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi g)
  refine ⟨r, ?_⟩
  intro m
  apply b.equivFunL.injective
  ext i
  simp [r, hg, f]

/-- The projection has precisely the prescribed range and a closed kernel
giving the manuscript's bounded-coordinate direct sum. -/
theorem finite_dimensional_projection :
    Spec.Projection.{u, v} := by
  intro 𝕜 E _ _ _ M _
  obtain ⟨r, hr⟩ := finite_dimensional_retraction 𝕜 E M
  let P : E →L[𝕜] E := M.subtypeL.comp r
  have hfix (m : M) : P (m : E) = (m : E) := by
    change (r (m : E) : E) = (m : E)
    rw [hr]
  have hid : P.comp P = P := by
    ext x
    exact hfix (r x)
  have hrange : P.range = M := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (r y).property
    · intro x hx
      exact ⟨x, hfix ⟨x, hx⟩⟩
  have htop : Submodule.IsTopCompl M P.ker := by
    rw [← hrange]
    exact (ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker.mp hid).choose
  exact ⟨P, hid, hrange, hfix, P.isClosed_ker, htop⟩

/-- Both summands are closed, and the given subspace is complemented in the
previously established sense. -/
theorem finite_dimensional_complemented :
    Spec.ClosedComplement.{u, v} := by
  intro 𝕜 E _ _ _ M _
  obtain ⟨P, _, _, _, hclosed, htop⟩ := finite_dimensional_projection 𝕜 E M
  exact ⟨C01FiniteDimension.finite_dimensional_subspace_closed 𝕜 E M,
    ⟨P.ker, htop⟩, P.ker, hclosed, htop⟩

/-- The degenerate case has the explicit zero projection. -/
theorem zero_subspace_projection :
    Spec.ZeroProjection.{u, v} := by
  intro 𝕜 E _ _ _
  simp only
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · simp
  · change Submodule.IsTopCompl (⊥ : Submodule 𝕜 E) (0 : E →L[𝕜] E).ker
    simpa using (Submodule.isTopCompl_bot_top :
      Submodule.IsTopCompl (⊥ : Submodule 𝕜 E) ⊤)

end ExpandedFA.P1.FiniteDimensionalComplements
