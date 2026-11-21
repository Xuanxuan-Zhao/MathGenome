import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyDefinitions

/-!
The approximation property and bounded approximation property
(`fa2:p2:ap-definition`, paper.tex:9489–9494).

The definitions use the norm topology and bounded scalar-linear finite-rank
endomorphisms. They apply to real and complex Banach spaces, and more generally
to normed spaces. No nonemptiness or nonzero-space hypothesis is imposed.
-/

namespace ExpandedFA.Compactness

universe u v
noncomputable section

/-- Uniform approximation of the identity on every norm-compact set by
bounded finite-rank endomorphisms, without a common operator-norm bound. -/
def HasApproximationProperty (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ F : X →L[𝕜] X,
      FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
      sSup ((fun x : X => ‖F x - x‖) '' K) < ε

/-- One nonnegative operator-norm bound works for the approximants on every
norm-compact set and at every positive tolerance. -/
def HasBoundedApproximationProperty (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧
    ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ F : X →L[𝕜] X,
        FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
        ‖F‖ ≤ M ∧ sSup ((fun x : X => ‖F x - x‖) '' K) < ε

/-- For a compact set the error is continuous and attains its maximum when
the set is nonempty. For the empty set its real supremum is zero. -/
theorem approximation_error_lt_iff :
    ApproximationPropertyDefinitionsSpec.ApproximationErrorLtIff := by
  intro 𝕜 _ X _ _ F K hK ε hε
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [hε]
  · exact hK.sSup_lt_iff_of_continuous hne
      ((F.continuous.sub continuous_id).norm.continuousOn) ε

/-- The equivalent pointwise formulation retains all compact sets. -/
theorem hasApproximationProperty_iff_pointwise :
    ApproximationPropertyDefinitionsSpec.ApproximationPropertyIffPointwise := by
  intro 𝕜 X _ _ _
  constructor
  · intro h K hK ε hε
    obtain ⟨F, hF, herr⟩ := h K hK ε hε
    exact ⟨F, hF, (approximation_error_lt_iff F K hK ε hε).mp herr⟩
  · intro h K hK ε hε
    obtain ⟨F, hF, herr⟩ := h K hK ε hε
    exact ⟨F, hF, (approximation_error_lt_iff F K hK ε hε).mpr herr⟩

/-- The same pointwise reformulation keeps the bound outside the compact-set
and tolerance quantifiers. -/
theorem hasBoundedApproximationProperty_iff_pointwise :
    ApproximationPropertyDefinitionsSpec.BoundedApproximationPropertyIffPointwise := by
  intro 𝕜 X _ _ _
  constructor
  · rintro ⟨M, hM, h⟩
    refine ⟨M, hM, ?_⟩
    intro K hK ε hε
    obtain ⟨F, hF, hnorm, herr⟩ := h K hK ε hε
    exact ⟨F, hF, hnorm, (approximation_error_lt_iff F K hK ε hε).mp herr⟩
  · rintro ⟨M, hM, h⟩
    refine ⟨M, hM, ?_⟩
    intro K hK ε hε
    obtain ⟨F, hF, hnorm, herr⟩ := h K hK ε hε
    exact ⟨F, hF, hnorm, (approximation_error_lt_iff F K hK ε hε).mpr herr⟩

/-- Forgetting the common operator-norm bound gives AP. -/
theorem hasBoundedApproximationProperty_implies_hasApproximationProperty :
    ApproximationPropertyDefinitionsSpec.BoundedApproximationPropertyImpliesApproximationProperty := by
  intro 𝕜 X _ _ _ h K hK ε hε
  obtain ⟨M, _, h⟩ := h
  obtain ⟨F, hF, _, herr⟩ := h K hK ε hε
  exact ⟨F, hF, herr⟩

end
end ExpandedFA.Compactness
