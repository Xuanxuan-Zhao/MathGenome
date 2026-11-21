import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.HilbertBasisApproximationProperty
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.ApproximationPropertyOperatorForm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import Mathlib.Tactic.FieldSimp

/-! Hilbert AP and Schauder-basis BAP, paper.tex:9531–9571. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators
namespace ExpandedFA.Compactness
namespace HilbertBasisApproximationProperty
universe u v w
open HilbertBasisApproximationPropertySpec (finiteSubsetProjection)

/-- The finite-net argument works for arbitrary filters, in particular the
net of finite subsets of a possibly uncountable orthonormal basis. -/
theorem uniform_on_compact_of_strong_of_bound
    {𝕜 X α : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (P : α → X →L[𝕜] X) (l : Filter α) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, ‖P i‖ ≤ M)
    (hp : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (K : Set X) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, sSup ((fun x => ‖P i x - x‖) '' K) < ε := by
  let δ := ε / (2 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, _, ht, hcover⟩ := hK.finite_cover_balls hδ
  have he : ∀ᶠ i in l, ∀ y ∈ t, ‖P i y - y‖ < ε / 2 := by
    apply ht.eventually_all.mpr
    intro y _
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp (hp y) (ε / 2) (half_pos hε))
  filter_upwards [he] with i hi
  apply (approximation_error_lt_iff (P i) K hK ε hε).mpr
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - y‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hbd : ‖P i (x - y)‖ ≤ M * ‖x - y‖ :=
    ((P i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
  calc
    ‖P i x - x‖ = ‖(P i (x - y) + (P i y - y)) + (y - x)‖ := by
      rw [map_sub]; congr 1; abel
    _ ≤ ‖P i (x - y)‖ + ‖P i y - y‖ + ‖y - x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * ‖x - y‖ + ‖P i y - y‖ + ‖x - y‖ := by rw [norm_sub_rev y x]; linarith
    _ < (M + 1) * δ + ε / 2 := by nlinarith [hi y hyt]
    _ = ε := by dsimp [δ]; field_simp; ring

/-- A range contained in a finite-dimensional subspace has finite rank. -/
theorem finite_rank_of_range_le {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (P : X →L[𝕜] X) (V : Submodule 𝕜 X) [FiniteDimensional 𝕜 V]
    (h : ∀ x, P x ∈ V) : FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) := by
  apply FiniteDimensional.of_injective
    (Submodule.inclusion (show LinearMap.range P.toLinearMap ≤ V from ?_))
    (Submodule.inclusion_injective _)
  rintro _ ⟨x, rfl⟩
  exact h x

theorem finite_subset_projection_properties : HilbertBasisApproximationPropertySpec.FiniteSubsetProjectionProperties := by
  intro 𝕜 _ H ι _ _ e F
  let V := Submodule.span 𝕜 (e '' (F : Set ι))
  letI : FiniteDimensional 𝕜 V :=
    FiniteDimensional.span_of_finite 𝕜 (F.finite_toSet.image e)
  exact ⟨finite_rank_of_range_le V.starProjection V V.starProjection_apply_mem,
    V.starProjection_norm_le⟩

/-- Finite spans approximate each vector, by the accepted arbitrary-basis
expansion. Nearest-point minimality transfers its error to the projector. -/
theorem finite_subset_projection_tendsto
    {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {ι : Type w}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H)
    (he : Hilbert.OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e)
    (x : H) : Tendsto (fun F => finiteSubsetProjection (𝕜 := 𝕜) e F x) atTop (𝓝 x) := by
  have hc := Hilbert.OrthonormalExpansion.finiteSubsetNet_expansion 𝕜 H ι e he x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with F hF
  let V := Submodule.span 𝕜 (e '' (F : Set ι))
  letI : FiniteDimensional 𝕜 V :=
    FiniteDimensional.span_of_finite 𝕜 (F.finite_toSet.image e)
  let z := Hilbert.PreHilbertBesselParseval.fourierPartialSum 𝕜 e x F
  have hz : z ∈ V := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hmin : ‖x - V.starProjection x‖ ≤ ‖x - z‖ := by
    rw [V.starProjection_minimal]
    exact ciInf_le (show BddBelow (range fun y : V => ‖x - (y : H)‖) from
      ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩) (⟨z, hz⟩ : V)
  change dist (V.starProjection x) x < ε
  rw [dist_eq_norm, norm_sub_rev]
  exact hmin.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hF)

theorem hilbert_uniform_on_compact : HilbertBasisApproximationPropertySpec.HilbertUniformOnCompact := by
  intro 𝕜 _ H ι _ _ _ e he K hK ε hε
  exact uniform_on_compact_of_strong_of_bound (finiteSubsetProjection (𝕜 := 𝕜) e)
    atTop 1 zero_le_one (fun F => (finite_subset_projection_properties e F).2)
    (finite_subset_projection_tendsto e he) K hK ε hε

theorem hilbert_bap : HilbertBasisApproximationPropertySpec.HilbertBAP := by
  intro 𝕜 H _ _ _ _ K hK ε hε
  obtain ⟨ι, e, he⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_family 𝕜 H
  obtain ⟨F, hF⟩ := (hilbert_uniform_on_compact e he K hK ε hε).exists
  exact ⟨finiteSubsetProjection e F, (finite_subset_projection_properties e F).1,
    (finite_subset_projection_properties e F).2, hF⟩

theorem hilbert_ap : HilbertBasisApproximationPropertySpec.HilbertAP := by
  intro 𝕜 H _ _ _ _ K hK ε hε
  obtain ⟨P, hP, _, herr⟩ := hilbert_bap 𝕜 H K hK ε hε
  exact ⟨P, hP, herr⟩

/-- Any map written using a fixed finite list of range vectors has finite rank. -/
theorem finite_rank_of_finite_sum {𝕜 X ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (P : X →L[𝕜] X) (e : ι → X) (s : Finset ι) (a : X → ι → 𝕜)
    (hP : ∀ x, P x = ∑ i ∈ s, a x i • e i) :
    FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) := by
  let V := Submodule.span 𝕜 (e '' (s : Set ι))
  letI : FiniteDimensional 𝕜 V :=
    FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image e)
  apply finite_rank_of_range_le P V
  intro x
  rw [hP]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem schauder_uniform_on_compact : HilbertBasisApproximationPropertySpec.SchauderUniformOnCompact := by
  intro 𝕜 _ X _ _ _ e h
  obtain ⟨P, hP, _, _⟩ := P1.C15PartialSums.raw_partial_sum_bounds h
  refine ⟨P, P1.C15PartialSums.Spec.basisConstant P, hP.nonneg, hP.agrees, ?_, ?_⟩
  · intro N
    refine ⟨?_, le_ciSup hP.bounded N⟩
    apply finite_rank_of_finite_sum (P N) e (Finset.range N)
      (P1.C15Basis.Spec.rawCoordinates h)
    exact hP.agrees N
  · intro K hK ε hε
    apply uniform_on_compact_of_strong_of_bound P atTop _ hP.nonneg
      (fun N => le_ciSup hP.bounded N) _ K hK ε hε
    intro x
    simpa only [hP.agrees] using hP.converges x

theorem finite_basis_uniform_on_compact : HilbertBasisApproximationPropertySpec.FiniteBasisUniformOnCompact := by
  intro 𝕜 _ X _ _ _ d e h
  classical
  obtain ⟨P, hP, _, _, _, _⟩ := P1.C15PartialSums.finite_partial_sum_bounds h
  refine ⟨P, P1.C15PartialSums.Spec.basisConstant P, hP.nonneg, hP.agrees, ?_, ?_⟩
  · intro N
    refine ⟨?_, le_ciSup hP.bounded N⟩
    apply finite_rank_of_finite_sum (P N) e
      (Finset.univ.filter (fun i : Fin d => i.val < N))
      (P1.C15Basis.Spec.finiteCoordinates h)
    exact hP.agrees N
  · intro K hK ε hε
    apply uniform_on_compact_of_strong_of_bound P atTop _ hP.nonneg
      (fun N => le_ciSup hP.bounded N) _ K hK ε hε
    intro x
    simpa only [hP.agrees] using hP.converges x

theorem schauder_bap : HilbertBasisApproximationPropertySpec.SchauderBAP := by
  intro 𝕜 _ X _ _ _ e h
  obtain ⟨P, M, hM, _, hP, hc⟩ := schauder_uniform_on_compact h
  refine ⟨M, hM, fun K hK ε hε => ?_⟩
  obtain ⟨N, hN⟩ := (hc K hK ε hε).exists
  exact ⟨P N, (hP N).1, (hP N).2, hN⟩

theorem finite_basis_bap : HilbertBasisApproximationPropertySpec.FiniteBasisBAP := by
  intro 𝕜 _ X _ _ _ d e h
  obtain ⟨P, M, hM, _, hP, hc⟩ := finite_basis_uniform_on_compact h
  refine ⟨M, hM, fun K hK ε hε => ?_⟩
  obtain ⟨N, hN⟩ := (hc K hK ε hε).exists
  exact ⟨P N, (hP N).1, (hP N).2, hN⟩

theorem schauder_ap : HilbertBasisApproximationPropertySpec.SchauderAP := by
  intro 𝕜 _ X _ _ _ e h
  exact hasBoundedApproximationProperty_implies_hasApproximationProperty 𝕜 X (schauder_bap h)

theorem finite_basis_ap : HilbertBasisApproximationPropertySpec.FiniteBasisAP := by
  intro 𝕜 _ X _ _ _ d e h
  exact hasBoundedApproximationProperty_implies_hasApproximationProperty 𝕜 X (finite_basis_bap h)

/-- Assemble the operator equivalence with the AP results above without
reproving or assuming the accepted compact-disk converse. -/
theorem operator_form : HilbertBasisApproximationPropertySpec.OperatorForm.{u, v} :=
  hasApproximationProperty_iff_compact_operator_approximation

end HilbertBasisApproximationProperty
end ExpandedFA.Compactness
