import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.RayleighRitz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.PositiveMinMax
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
universe u v w
namespace ExpandedFA.CompactSpectral.RayleighRitz
open Filter
open scoped Topology InnerProductSpace
open PositiveMinMax.Spec Spec
variable {𝕜 : Type u} {H : Type v} {K : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

lemma eigenvalueSequence_exists [CompleteSpace H] (T : H →L[𝕜] H)
    (hp : T.IsPositive)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) :
    ∃ μ, EigenvalueSequence T μ ∧
      (∀ k, Admissible 𝕜 H k → CourantFischerAt T k (μ k)) ∧
      (Function.Injective T → ∀ k, Admissible 𝕜 H k → ReciprocalAt T k (μ k)) := by
  obtain ⟨I, e, a, hd, hcf, hrec⟩ := PositiveMinMax.positive_minmax 𝕜 H T hp hc
  exact ⟨paddedValue I a, ⟨I, e, a, hd, rfl⟩, hcf, hrec⟩

lemma eigenvalue_nonneg (T : H →L[𝕜] H) {μ : ℕ → ℝ}
    (hμ : EigenvalueSequence T μ) (k : ℕ) : 0 ≤ μ k := by
  classical
  obtain ⟨I, e, a, hd, rfl⟩ := hμ
  by_cases hk : k ∈ I
  · simpa [paddedValue, hk] using (hd.2.2.1 ⟨k, hk⟩).le
  · simp [paddedValue, hk]

lemma eigenvalue_zero_of_not_admissible (T : H →L[𝕜] H) {μ : ℕ → ℝ}
    (hμ : EigenvalueSequence T μ) (k : ℕ) (hk : ¬ Admissible 𝕜 H k) : μ k = 0 := by
  classical
  obtain ⟨I, e, a, hd, rfl⟩ := hμ
  have hki : k ∉ I := fun h => hk
    (PositiveMinMax.aboveDimension_of_entry hd.1 e hd.2.1 k h)
  simp [paddedValue, hki]

lemma courantFischer_of_sequence (T : H →L[𝕜] H) (hp : T.IsPositive)
    {μ : ℕ → ℝ} (hμ : EigenvalueSequence T μ) (k : ℕ)
    (hk : Admissible 𝕜 H k) : CourantFischerAt T k (μ k) := by
  obtain ⟨I, e, a, hd, rfl⟩ := hμ
  exact PositiveMinMax.courantFischer_of_sandwich T hp k _
    (PositiveMinMax.spectral_sandwich T hp I e a hd k hk)

/-- Rayleigh quotients of the compression are exactly the restricted quotients. -/
lemma rayleigh_compression (T : H →L[𝕜] H) (U : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] (x : U) :
    rayleigh (compression T U) x = rayleigh T (x : H) := by
  simp only [rayleigh, compression, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, U.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.norm_coe]

lemma compression_positive (T : H →L[𝕜] H) (hp : T.IsPositive)
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    (compression T U).IsPositive := hp.orthogonalProjectionOnto_comp U

lemma compression_compact (T : H →L[𝕜] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (compression T U).toLinearMap := by
  exact Compactness.compact_postcomp _ U.orthogonalProjectionOnto
    (Compactness.compact_precomp _ U.subtypeL hc)

/-- A norm perturbation changes every unit Rayleigh quotient by at most that norm. -/
lemma rayleigh_sub_le (S T : H →L[𝕜] H) (x : H) :
    rayleigh S x - rayleigh T x ≤ ‖S-T‖ := by
  have heq : rayleigh S x - rayleigh T x = rayleigh (S-T) x := by
    simp [rayleigh, inner_sub_right, map_sub, sub_div]
  rw [heq]
  exact PositiveMinMax.rayleigh_le_norm _ _

/-- The max--min characterization gives the exact Lipschitz constant one. -/
lemma eigenvalue_sub_le (S T : H →L[𝕜] H) (hpS : S.IsPositive) (hpT : T.IsPositive)
    {μ ν : ℕ → ℝ} (hμ : EigenvalueSequence S μ) (hν : EigenvalueSequence T ν)
    (k : ℕ) : μ k - ν k ≤ ‖S-T‖ := by
  by_cases hk : Admissible 𝕜 H k
  · have hS := courantFischer_of_sequence S hpS hμ k hk
    have hT := courantFischer_of_sequence T hpT hν k hk
    obtain ⟨L, hL, heq⟩ := hS.2.2.1.1
    have hne := (hT.1 L hL).1
    have hbdS := (hS.1 L hL).2.1
    have hbdT := (hT.1 L hL).2.1
    have hbound : sInf (rayleighValues S L) ≤ sInf (rayleighValues T L) + ‖S-T‖ := by
      apply (sub_le_iff_le_add).mp
      apply le_csInf hne
      rintro _ ⟨x, hx, hx0, rfl⟩
      have h := (csInf_le hbdS (show rayleigh S x ∈ rayleighValues S L from ⟨x, hx, hx0, rfl⟩))
      have h' := rayleigh_sub_le S T x
      linarith
    have hle := hT.2.2.1.2 (show sInf (rayleighValues T L) ∈
      {r | ∃ L, TrialSpace L (k+1) ∧ sInf (rayleighValues T L) = r} from ⟨L, hL, rfl⟩)
    linarith
  · rw [eigenvalue_zero_of_not_admissible S hμ k hk,
      eigenvalue_zero_of_not_admissible T hν k hk, sub_self]
    exact norm_nonneg _

lemma eigenvalue_lipschitz (S T : H →L[𝕜] H) (hpS : S.IsPositive) (hpT : T.IsPositive)
    {μ ν : ℕ → ℝ} (hμ : EigenvalueSequence S μ) (hν : EigenvalueSequence T ν)
    (k : ℕ) : |μ k - ν k| ≤ ‖S-T‖ := by
  apply abs_le.mpr
  constructor
  · have h := eigenvalue_sub_le T S hpT hpS hν hμ k
    rw [norm_sub_rev] at h
    linarith
  · exact eigenvalue_sub_le S T hpS hpT hμ hν k


lemma trialSpace_map (f : H →ₗ[𝕜] K) (hf : Function.Injective f)
    {L : Submodule 𝕜 H} {k : ℕ} (hL : TrialSpace L k) :
    TrialSpace (L.map f) k := by
  letI := hL.1
  exact ⟨inferInstance, (Submodule.equivMapOfInjective f hf L).finrank_eq.symm.trans hL.2⟩

/-- A Rayleigh-preserving linear embedding can only increase max--min values. -/
lemma eigenvalue_le_of_embedding (S : H →L[𝕜] H) (T : K →L[𝕜] K)
    (hpS : S.IsPositive) (hpT : T.IsPositive)
    {μ ν : ℕ → ℝ} (hμ : EigenvalueSequence S μ) (hν : EigenvalueSequence T ν)
    (f : H →ₗ[𝕜] K) (hf : Function.Injective f)
    (hr : ∀ x, rayleigh S x = rayleigh T (f x)) (k : ℕ) : μ k ≤ ν k := by
  by_cases hk : Admissible 𝕜 H k
  · have hkK : Admissible 𝕜 K k := by
      obtain ⟨e, he⟩ := hk
      exact ⟨f ∘ e, he.map' f (LinearMap.ker_eq_bot.mpr hf)⟩
    have hS := courantFischer_of_sequence S hpS hμ k hk
    have hT := courantFischer_of_sequence T hpT hν k hkK
    obtain ⟨L, hL, hval⟩ := hS.2.2.1.1
    have hmap := trialSpace_map f hf hL
    have hvals : rayleighValues T (L.map f) = rayleighValues S L := by
      ext r
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, hy0, hrfl⟩
        exact ⟨x, hx, fun hz => hy0 (by simp [hz]), by rwa [hr]⟩
      · rintro ⟨x, hx, hx0, hrfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, fun hz => hx0 (hf (by simpa using hz)), by rwa [← hr]⟩
    apply hT.2.2.1.2
    exact ⟨L.map f, hmap, by rw [hvals, hval]⟩
  · rw [eigenvalue_zero_of_not_admissible S hμ k hk]
    exact eigenvalue_nonneg T hν k

lemma compression_eigenvalue_le (T : H →L[𝕜] H) (hp : T.IsPositive)
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    {μ ν : ℕ → ℝ} (hμ : EigenvalueSequence (compression T U) μ)
    (hν : EigenvalueSequence T ν) (k : ℕ) : μ k ≤ ν k :=
  eigenvalue_le_of_embedding _ _ (compression_positive T hp U) hp hμ hν
    U.subtype Subtype.val_injective (rayleigh_compression T U) k

lemma compression_eigenvalue_mono (T : H →L[𝕜] H) (hp : T.IsPositive)
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) {μ ν : ℕ → ℝ}
    (hμ : EigenvalueSequence (compression T U) μ)
    (hν : EigenvalueSequence (compression T V) ν) (k : ℕ) : μ k ≤ ν k := by
  apply eigenvalue_le_of_embedding _ _ (compression_positive T hp U)
    (compression_positive T hp V) hμ hν (Submodule.inclusion hUV)
    (Submodule.inclusion_injective hUV) _ k
  intro x
  rw [rayleigh_compression, rayleigh_compression]
  rfl

lemma projection_strong_tendsto [CompleteSpace H] (V : TrialSequence 𝕜 H) (x : H) :
    Tendsto (fun n => (V.space n).starProjection x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := V.dense.exists_dist_lt x hε
  obtain ⟨N, hyN⟩ := Set.mem_iUnion.mp hy
  refine ⟨N, fun n hn => ?_⟩
  have hym : y ∈ V.space n := V.increasing hn hyN
  rw [dist_comm, dist_eq_norm, Submodule.starProjection_minimal]
  exact (ciInf_le_of_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ (⟨y, hym⟩ : V.space n) le_rfl).trans_lt
    (by simpa only [dist_eq_norm] using hxy)

/-- A common contraction bound turns strong convergence into uniform convergence
on a compact set. The finite-net argument does not use separability. -/
lemma compact_uniform_small (A : ℕ → H →L[𝕜] H)
    (hbound : ∀ n x, ‖A n x‖ ≤ ‖x‖)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 0))
    {C : Set H} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ C, ‖A n x‖ < ε := by
  obtain ⟨s, hsC, hsfin, hcover⟩ := hC.finite_cover_balls (half_pos hε)
  have hs : ∀ y ∈ s, ∀ᶠ n in atTop, ‖A n y‖ < ε/2 := by
    intro y _
    exact (tendsto_norm_zero.comp (hstrong y)).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hsfin.eventually_all.mpr hs] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x-y‖ < ε/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  calc
    ‖A n x‖ = ‖A n (x-y) + A n y‖ := by rw [map_sub, sub_add_cancel]
    _ ≤ ‖A n (x-y)‖ + ‖A n y‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + ‖A n y‖ := add_le_add (hbound n (x-y)) le_rfl
    _ < ε := by linarith [hn y hy]

lemma left_projection_error_tendsto [CompleteSpace H] (T : H →L[𝕜] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (V : TrialSequence 𝕜 H) :
    Tendsto (fun n => ‖(ContinuousLinearMap.id 𝕜 H - (V.space n).starProjection) ∘L T‖)
      atTop (𝓝 0) := by
  let A : ℕ → H →L[𝕜] H := fun n => ContinuousLinearMap.id 𝕜 H - (V.space n).starProjection
  have hbound : ∀ n x, ‖A n x‖ ≤ ‖x‖ := by
    intro n x
    change ‖(ContinuousLinearMap.id 𝕜 H - (V.space n).starProjection) x‖ ≤ ‖x‖
    rw [← Submodule.starProjection_orthogonal]
    exact (V.space n).orthogonal.norm_starProjection_apply_le x
  have hs : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 0) := by
    intro x
    simpa only [A, sub_apply, ContinuousLinearMap.id_apply, sub_self]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub
        (projection_strong_tendsto V x)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := compact_uniform_small A hbound hs hc (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (half_pos hε))
  intro x hx
  exact (hN n hn (T x) (subset_closure ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩)).le


lemma extendedCompression_error_le [CompleteSpace H] (T : H →L[𝕜] H)
    (hp : T.IsPositive) (U : Submodule 𝕜 H) [CompleteSpace U] :
    ‖extendedCompression T U - T‖ ≤
      2 * ‖(ContinuousLinearMap.id 𝕜 H - U.starProjection) ∘L T‖ := by
  let P := U.starProjection
  let Q := ContinuousLinearMap.id 𝕜 H - P
  have hP : P.adjoint = P := U.starProjection_isSymmetric.clm_adjoint_eq
  have hQ : Q.adjoint = Q := by
    dsimp only [Q]
    rw [map_sub, ContinuousLinearMap.adjoint_id, hP]
  have hT : T.adjoint = T := hp.isSymmetric.clm_adjoint_eq
  have hn : ‖T ∘L Q‖ = ‖Q ∘L T‖ := by
    rw [← ContinuousLinearMap.adjoint.norm_map (T ∘L Q), ContinuousLinearMap.adjoint_comp,
      hQ, hT]
  have hid : T - extendedCompression T U = Q ∘L T + P ∘L (T ∘L Q) := by
    ext x
    simp [extendedCompression, Q, P]
  rw [norm_sub_rev, hid]
  calc
    _ ≤ ‖Q ∘L T‖ + ‖P ∘L (T ∘L Q)‖ := norm_add_le _ _
    _ ≤ ‖Q ∘L T‖ + ‖P‖ * ‖T ∘L Q‖ :=
      add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖Q ∘L T‖ + 1 * ‖T ∘L Q‖ := by
      gcongr
      exact U.starProjection_norm_le
    _ = 2 * ‖Q ∘L T‖ := by rw [hn]; ring

lemma extendedCompression_tendsto [CompleteSpace H] (T : H →L[𝕜] H)
    (hp : T.IsPositive)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (V : TrialSequence 𝕜 H) :
    Tendsto (fun n => ‖extendedCompression T (V.space n) - T‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => extendedCompression_error_le T hp (V.space n))
  simpa using (left_projection_error_tendsto T hc V).const_mul 2

lemma trialSpace_admissible {L : Submodule 𝕜 H} {k : ℕ} (hL : TrialSpace L (k+1)) :
    Admissible 𝕜 H k := by
  letI := hL.1
  unfold Admissible
  rw [← hL.2]
  exact ⟨fun i => (Module.finBasis 𝕜 L i : H),
    (Module.finBasis 𝕜 L).linearIndependent.map' L.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)⟩

lemma le_eigenvalue_of_lower_trial (T : H →L[𝕜] H) (hp : T.IsPositive)
    {μ : ℕ → ℝ} (hμ : EigenvalueSequence T μ) {k : ℕ}
    (L : Submodule 𝕜 H) (hL : TrialSpace L (k+1)) (r : ℝ)
    (hr : ∀ x ∈ L, x ≠ 0 → r ≤ rayleigh T x) : r ≤ μ k := by
  have hcf := courantFischer_of_sequence T hp hμ k (trialSpace_admissible hL)
  apply le_trans _ (hcf.2.2.1.2 (show sInf (rayleighValues T L) ∈
    {s | ∃ L, TrialSpace L (k+1) ∧ sInf (rayleighValues T L) = s} from ⟨L, hL, rfl⟩))
  apply le_csInf (hcf.1 L hL).1
  rintro _ ⟨x, hx, hx0, rfl⟩
  exact hr x hx hx0

/-- Extending the compression by zero preserves its padded ordered eigenvalues,
including dimensions below k+1. -/
lemma extendedCompression_eigenvalue_eq [CompleteSpace H] (T : H →L[𝕜] H) (hp : T.IsPositive)
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    {μ ν : ℕ → ℝ} (hμ : EigenvalueSequence (extendedCompression T U) μ)
    (hν : EigenvalueSequence (compression T U) ν) (k : ℕ) : μ k = ν k := by
  classical
  have hpE := hp.conj_starProjection U
  have hpC := compression_positive T hp U
  have hcomp : compression (extendedCompression T U) U = compression T U := by
    ext x
    simp [compression, extendedCompression,
      U.starProjection_mem_subspace_eq_self, U.orthogonalProjectionOnto_starProjection_of_le le_rfl]
  have hle : ν k ≤ μ k := by
    apply compression_eigenvalue_le _ hpE U (hcomp.symm ▸ hν) hμ k
  apply le_antisymm _ hle
  obtain ⟨I, e, a, hd, rfl⟩ := hμ
  by_cases hk : k ∈ I
  · let g : Fin (k+1) → I := PositiveMinMax.prefixIndex hd.1 hk (k+1) le_rfl
    have hg := PositiveMinMax.prefixIndex_injective hd.1 hk (k+1) le_rfl
    let L : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range (e ∘ g))
    have hL : TrialSpace L (k+1) :=
      ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _),
        PositiveMinMax.finrank_span_fin _ (hd.2.1.comp g hg).linearIndependent⟩
    have heU : ∀ i, e i ∈ U := by
      intro i
      obtain ⟨x, hx⟩ := PositiveMinMax.eigenvectors_mem_range (extendedCompression T U) e a
        (fun i => (hd.2.2.1 i).ne') hd.2.2.2.2.1 i
      rw [← hx]
      exact U.starProjection_apply_mem _
    have hLU : L ≤ U := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact heU _)
    let LU : Submodule 𝕜 U := L.comap U.subtype
    let eqv : LU ≃ₗ[𝕜] L := Submodule.comapSubtypeEquivOfLe hLU
    letI := hL.1
    letI : FiniteDimensional 𝕜 LU := eqv.symm.finiteDimensional
    have hLUdim : TrialSpace LU (k+1) := ⟨inferInstance, eqv.finrank_eq.trans hL.2⟩
    simp only [paddedValue, dif_pos hk]
    apply le_eigenvalue_of_lower_trial _ hpC hν LU hLUdim
    intro x hx hx0
    rw [rayleigh_compression]
    have heq : rayleigh (extendedCompression T U) (x : H) = rayleigh T (x : H) := by
      rw [← rayleigh_compression (extendedCompression T U) U x, hcomp, rayleigh_compression]
    rw [← heq]
    apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (by simpa using hx0)))).mpr
    exact PositiveMinMax.quadratic_ge_on_span _ (e ∘ g) (hd.2.1.comp g hg) (a ∘ g)
      (fun i => hd.2.2.2.2.1 (g i)) _
      (fun i => hd.2.2.2.1 (show g i ≤ (⟨k, hk⟩ : I) from Nat.le_of_lt_succ i.isLt))
      (x : H) hx
  · simpa [paddedValue, hk] using eigenvalue_nonneg (compression T U) hν k


lemma extendedCompression_compact (T : H →L[𝕜] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (extendedCompression T U).toLinearMap := by
  exact Compactness.compact_postcomp _ U.starProjection
    (Compactness.compact_precomp _ U.starProjection hc)

/-- Monotone Rayleigh--Ritz approximation for arbitrary increasing closed trial
spaces with dense union, with exact norm error and the attained min--max and
injective reciprocal formulas. Index k is the manuscript index k+1. -/
theorem monotone_rayleigh_ritz : Spec.Principle.{u,v} := by
  intro 𝕜 H _ _ _ _ T hp hc V
  obtain ⟨μ, hμ, hcf, hrec⟩ := eigenvalueSequence_exists T hp hc
  have hv : ∀ n, ∃ ν, EigenvalueSequence (compression T (V.space n)) ν := by
    intro n
    obtain ⟨ν, hν, _, _⟩ := eigenvalueSequence_exists (compression T (V.space n))
      (compression_positive T hp _) (compression_compact T hc _)
    exact ⟨ν, hν⟩
  choose ν hν using hv
  have he : ∀ n k, |ν n k - μ k| ≤ ‖extendedCompression T (V.space n) - T‖ := by
    intro n k
    obtain ⟨ξ, hξ, _, _⟩ := eigenvalueSequence_exists (extendedCompression T (V.space n))
      (hp.conj_starProjection _) (extendedCompression_compact T hc _)
    have hEq := extendedCompression_eigenvalue_eq T hp (V.space n) hξ (hν n) k
    simpa only [hEq] using eigenvalue_lipschitz (extendedCompression T (V.space n)) T
      (hp.conj_starProjection _) hp hξ hμ k
  have hnorm := extendedCompression_tendsto T hp hc V
  refine ⟨μ, ν, hμ, hν, hcf, hrec, ?_, he, hnorm, ?_⟩
  · intro n k
    exact ⟨eigenvalue_nonneg _ (hν n) k,
      compression_eigenvalue_mono T hp _ _ (V.increasing (Nat.le_succ n)) (hν n) (hν (n+1)) k,
      compression_eigenvalue_le T hp _ (hν (n+1)) hμ k⟩
  · intro k
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (he n k).trans_lt
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hN n hn

end ExpandedFA.CompactSpectral.RayleighRitz
