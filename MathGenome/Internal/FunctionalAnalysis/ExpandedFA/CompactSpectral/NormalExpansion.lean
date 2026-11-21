import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.NormalExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.NormalEigenspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

/-!
Complex compact normal spectral expansion on arbitrary Hilbert spaces.
For each finite spectral sum, its remainder is compact and normal. Its
nonzero eigenvalues are precisely the omitted eigenvalues of N, so the
accepted normal-radius theorem gives the exact tail norm. Spectral finiteness
then proves unconditional convergence in operator norm. Evaluation gives
the vector series, and orthogonal complements give the kernel decomposition.
No basis choice or separability assumption is needed.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace ExpandedFA.CompactSpectral.NormalExpansion
universe u
open Filter
open scoped Topology InnerProductSpace
open Spec (eigenProjection spectralSum nonzeroEigenvalues tailModuli nonzeroSpan)
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma eigenProjection_mem (N : H →L[ℂ] H) (α : ℂ) (x : H) :
    eigenProjection N α x ∈ Module.End.eigenspace N.toLinearMap α := by
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) := (N.isClosed_eigenspace α).completeSpace_coe
  exact (Module.End.eigenspace N.toLinearMap α).starProjection_apply_mem x

lemma eigenProjection_self (N : H →L[ℂ] H) (α : ℂ) {x : H} (hx : x ∈ Module.End.eigenspace N.toLinearMap α) :
    eigenProjection N α x = x := by
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) := (N.isClosed_eigenspace α).completeSpace_coe
  exact Submodule.starProjection_eq_self_iff.mpr hx

lemma eigenProjection_star (N : H →L[ℂ] H) (α : ℂ) :
    star (eigenProjection N α) = eigenProjection N α := by
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) := (N.isClosed_eigenspace α).completeSpace_coe
  exact (isSelfAdjoint_starProjection (Module.End.eigenspace N.toLinearMap α)).star_eq

lemma eigenProjection_mul (N : H →L[ℂ] H) (hN : IsStarNormal N) (α β : ℂ) :
    eigenProjection N α * eigenProjection N β =
      if α = β then eigenProjection N α else 0 := by
  classical
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) := (N.isClosed_eigenspace α).completeSpace_coe
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap β) := (N.isClosed_eigenspace β).completeSpace_coe
  split_ifs with h
  · subst β
    exact (Module.End.eigenspace N.toLinearMap α).isIdempotentElem_starProjection.eq
  · exact (NormalEigenspaces.normal_orthogonal_eigenspaces H N hN).isOrtho h
      |>.starProjection_comp_starProjection

lemma eigenProjection_commute (N : H →L[ℂ] H) (hN : IsStarNormal N) (α β : ℂ) :
    Commute (eigenProjection N α) (eigenProjection N β) := by
  classical
  rw [commute_iff_eq, eigenProjection_mul N hN, eigenProjection_mul N hN]
  by_cases h : α = β
  · subst β; rfl
  · simp [h, Ne.symm h]

lemma operator_mul_eigenProjection (N : H →L[ℂ] H) (α : ℂ) :
    N * eigenProjection N α = α • eigenProjection N α := by
  ext x
  exact Module.End.mem_eigenspace_iff.mp (eigenProjection_mem N α x)

lemma eigenProjection_commute_operator (N : H →L[ℂ] H) (hN : IsStarNormal N) (α : ℂ) :
    Commute (eigenProjection N α) N := by
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) := (N.isClosed_eigenspace α).completeSpace_coe
  exact (Hilbert.Adjoint.reducing_iff_commutes_projection ℂ H (Module.End.eigenspace N.toLinearMap α)
    (N.isClosed_eigenspace α) N).mp (NormalEigenspaces.normal_reducing_eigenspaces H N hN α)

lemma eigenProjection_mul_operator (N : H →L[ℂ] H) (hN : IsStarNormal N) (α : ℂ) :
    eigenProjection N α * N = α • eigenProjection N α := by
  rw [(eigenProjection_commute_operator N hN α).eq, operator_mul_eigenProjection]

lemma spectralSum_normal (N : H →L[ℂ] H) (hN : IsStarNormal N) (s : Finset ℂ) :
    IsStarNormal (spectralSum N s) := by
  classical
  have hP (α : ℂ) : IsStarNormal (eigenProjection N α) :=
    (show IsSelfAdjoint (eigenProjection N α) from eigenProjection_star N α).isStarNormal
  unfold spectralSum
  induction s using Finset.induction_on with
  | empty => simpa using (inferInstance : IsStarNormal (0 : H →L[ℂ] H))
  | @insert α s ha ih =>
    rw [Finset.sum_insert ha]
    letI := ih
    letI := hP α
    have hc : Commute (α • eigenProjection N α)
        (star (∑ β ∈ s, β • eigenProjection N β)) := by
      rw [star_sum]
      apply Commute.sum_right
      intro β _
      rw [star_smul, eigenProjection_star]
      exact ((eigenProjection_commute N hN α β).smul_left α).smul_right (star β)
    exact hc.isStarNormal_add

lemma operator_commute_star_spectralSum (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (s : Finset ℂ) : Commute N (star (spectralSum N s)) := by
  rw [spectralSum, star_sum]
  apply Commute.sum_right
  intro α _
  rw [star_smul, eigenProjection_star]
  exact (eigenProjection_commute_operator N hN α).symm.smul_right (star α)

lemma remainder_normal (N : H →L[ℂ] H) (hN : IsStarNormal N) (s : Finset ℂ) :
    IsStarNormal (N - spectralSum N s) := by
  letI := hN
  letI := spectralSum_normal N hN s
  exact (operator_commute_star_spectralSum N hN s).isStarNormal_sub

lemma remainder_compact (N : H →L[ℂ] H) (hN : IsCompactOperator N) (s : Finset ℂ) :
    IsCompactOperator (N - spectralSum N s) := by
  have he : N - spectralSum N s = N * (1 - ∑ α ∈ s, eigenProjection N α) := by
    simp only [mul_sub, mul_one, Finset.mul_sum, operator_mul_eigenProjection, spectralSum]
  rw [he]
  exact hN.comp_clm _

lemma eigenProjection_mul_spectralSum (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (s : Finset ℂ) (α : ℂ) :
    eigenProjection N α * spectralSum N s =
      if α ∈ s then α • eigenProjection N α else 0 := by
  classical
  simp only [spectralSum, Finset.mul_sum, mul_smul_comm, eigenProjection_mul]
  simp only [smul_ite, smul_zero]
  simp

lemma eigenProjection_mul_remainder (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (s : Finset ℂ) (α : ℂ) (hα : α ∈ s) :
    eigenProjection N α * (N - spectralSum N s) = 0 := by
  rw [mul_sub, eigenProjection_mul_operator N hN,
    eigenProjection_mul_spectralSum N hN, if_pos hα, sub_self]

lemma eigenProjection_other (N : H →L[ℂ] H) (hN : IsStarNormal N) {α β : ℂ}
    (hβα : β ≠ α) {x : H} (hx : N x = α • x) : eigenProjection N β x = 0 := by
  have hp := eigenProjection_mul N hN β α
  rw [if_neg hβα] at hp
  have he := congrArg (fun A : H →L[ℂ] H => A x) hp
  simpa only [ContinuousLinearMap.mul_apply, eigenProjection_self N α
    (Module.End.mem_eigenspace_iff.mpr hx), ContinuousLinearMap.zero_apply] using he

lemma remainder_eigenvalue_iff (N : H →L[ℂ] H) (hN : IsStarNormal N)
    (s : Finset ℂ) (α : ℂ) (hα : α ≠ 0) :
    (∃ x : H, x ≠ 0 ∧ (N - spectralSum N s) x = α • x) ↔
      α ∈ nonzeroEigenvalues N ∧ α ∉ s := by
  classical
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hp (β : ℂ) (hβ : β ∈ s) : eigenProjection N β x = 0 := by
      have he := congrArg (fun A : H →L[ℂ] H => A x)
        (eigenProjection_mul_remainder N hN s β hβ)
      change eigenProjection N β ((N - spectralSum N s) x) = 0 at he
      rw [hx, map_smul] at he
      exact (smul_eq_zero.mp he).resolve_left hα
    have hsx : spectralSum N s x = 0 := by
      simp only [spectralSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact Finset.sum_eq_zero (fun β hβ => by rw [hp β hβ, smul_zero])
    have hNx : N x = α • x := by
      simpa only [ContinuousLinearMap.sub_apply, hsx, sub_zero] using hx
    refine ⟨⟨hα, x, hx0, hNx⟩, ?_⟩
    intro has
    exact hx0 ((eigenProjection_self N α (Module.End.mem_eigenspace_iff.mpr hNx)).symm.trans
      (hp α has))
  · rintro ⟨⟨_, x, hx0, hx⟩, hnot⟩
    refine ⟨x, hx0, ?_⟩
    have hsx : spectralSum N s x = 0 := by
      simp only [spectralSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      apply Finset.sum_eq_zero
      intro β hβ
      rw [eigenProjection_other N hN (show β ≠ α from fun he => hnot (he ▸ hβ)) hx, smul_zero]
    simp only [ContinuousLinearMap.sub_apply, hsx, sub_zero, hx]

lemma eigenvalue_norm_le (N : H →L[ℂ] H) {α : ℂ}
    (hα : ∃ x : H, x ≠ 0 ∧ N x = α • x) : ‖α‖ ≤ ‖N‖ := by
  obtain ⟨x, hx0, hx⟩ := hα
  have hb := N.le_opNorm x
  rw [hx, norm_smul] at hb
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx0)).mp hb

lemma tailModuli_bddAbove (N : H →L[ℂ] H) (s : Finset ℂ) :
    BddAbove (tailModuli N s) := by
  refine ⟨‖N‖, ?_⟩
  rintro _ ⟨α, ⟨hα, _⟩, rfl⟩
  exact eigenvalue_norm_le N hα.2

lemma real_sSup_le_nonneg {S : Set ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ S, x ≤ r) : sSup S ≤ r := by
  rcases S.eq_empty_or_nonempty with he | he
  · simpa [he] using hr
  · exact csSup_le he h

lemma tailModuli_sSup_nonneg (N : H →L[ℂ] H) (s : Finset ℂ) :
    0 ≤ sSup (tailModuli N s) := by
  rcases (tailModuli N s).eq_empty_or_nonempty with he | ⟨r, hr⟩
  · simp [he]
  · obtain ⟨α, hα, rfl⟩ := hr
    exact (norm_nonneg α).trans (le_csSup (tailModuli_bddAbove N s) ⟨α, hα, rfl⟩)

/-- Normality turns the omitted compact spectrum into the exact operator error. -/
theorem tail_norm : Spec.TailNorm.{u} := by
  intro H _ _ _ N hcompact hN s
  let R := N - spectralSum N s
  have hc : IsCompactOperator N := (Compactness.compact_iff_isCompactOperator _).mp hcompact
  have hRc : IsCompactOperator R := remainder_compact N hc s
  have hRn : IsStarNormal R := remainder_normal N hN s
  have hRspec (α : ℂ) (hα : α ≠ 0) :
      α ∈ spectrum ℂ R ↔ α ∈ nonzeroEigenvalues N ∧ α ∉ s := by
    have hRc' : Compactness.IsCompactLinearMap R.toLinearMap :=
      (Compactness.compact_iff_isCompactOperator _).mpr hRc
    exact (Fredholm.compact_nonzero_spectrum_iff_eigenvalue R hRc' α hα).trans
      (remainder_eigenvalue_iff N hN s α hα)
  have hradius : sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ R) = ‖R‖ :=
    CStar.SelfAdjointSpectrumNormalRadius.unital_normal_radius (H →L[ℂ] H) R hRn
  change ‖R‖ = sSup (tailModuli N s)
  apply le_antisymm
  · rw [← hradius]
    apply real_sSup_le_nonneg (tailModuli_sSup_nonneg N s)
    rintro _ ⟨α, hα, rfl⟩
    by_cases ha0 : α = 0
    · simpa [ha0] using tailModuli_sSup_nonneg N s
    · exact le_csSup (tailModuli_bddAbove N s) ⟨α, (hRspec α ha0).mp hα, rfl⟩
  · apply real_sSup_le_nonneg (norm_nonneg R)
    rintro _ ⟨α, hα, rfl⟩
    exact eigenvalue_norm_le R ((remainder_eigenvalue_iff N hN s α hα.1.1).mpr hα)

/-- Finite spectral sums converge even as an unconditional operator-valued sum. -/
theorem operator_expansion : Spec.OperatorExpansion.{u} := by
  intro H _ _ _ N hcompact hN
  classical
  change Tendsto (spectralSum N) atTop (𝓝 N)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let A : Set ℂ := {α | (∃ x : H, x ≠ 0 ∧ N x = α • x) ∧ ε / 2 ≤ ‖α‖}
  have hA : A.Finite :=
    NormalEigenspaces.compact_eigenvalues_finite_away_from_zero H N hcompact _ (by positivity)
  refine ⟨hA.toFinset, ?_⟩
  intro s hs
  rw [dist_eq_norm, norm_sub_rev, tail_norm H N hcompact hN s]
  apply lt_of_le_of_lt (real_sSup_le_nonneg (by positivity : 0 ≤ ε / 2) ?_)
    (half_lt_self hε)
  rintro _ ⟨α, ⟨hα, hnot⟩, rfl⟩
  apply le_of_lt
  by_contra! hge
  exact hnot (hs (hA.mem_toFinset.mpr ⟨hα.2, hge⟩))

/-- Evaluation preserves the norm-convergent expansion; the zero term vanishes. -/
theorem vector_expansion : Spec.VectorExpansion.{u} := by
  intro H _ _ _ N hcompact hN x
  have he : HasSum (fun α : ℂ => α • eigenProjection N α x) (N x) :=
    (ContinuousLinearMap.apply ℂ H x).hasSum (operator_expansion H N hcompact hN)
  apply (hasSum_subtype_iff_of_support_subset (s := {α : ℂ | α ≠ 0}) ?_).mpr he
  intro α hα
  by_contra hz
  have hz' : α = 0 := not_ne_iff.mp hz
  exact hα (by simp [hz'])

/-- The closed nonzero spectral span has exactly the kernel as its orthogonal
complement. This proof uses the operator expansion and retains arbitrary kernels. -/
lemma nonzeroSpan_orthogonal (N : H →L[ℂ] H)
    (hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap)
    (hN : IsStarNormal N) : (nonzeroSpan N).orthogonal = N.ker := by
  classical
  let V : Submodule ℂ H := ⨆ α : {α : ℂ // α ≠ 0}, Module.End.eigenspace N.toLinearMap α.val
  change V.topologicalClosure.orthogonal = N.ker
  rw [Submodule.orthogonal_closure]
  apply le_antisymm
  · intro x hx
    have hp (α : ℂ) (hα : α ≠ 0) : eigenProjection N α x = 0 := by
      letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) :=
        (N.isClosed_eigenspace α).completeSpace_coe
      apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
      exact Submodule.orthogonal_le (le_iSup (fun α : {α : ℂ // α ≠ 0} =>
        Module.End.eigenspace N.toLinearMap α.val) ⟨α, hα⟩) hx
    have he := vector_expansion H N hcompact hN x
    have hz : (fun α : {α : ℂ // α ≠ 0} => α.val • eigenProjection N α.val x) = 0 := by
      funext α
      simp [hp α.val α.property]
    rw [hz] at he
    exact he.unique hasSum_zero
  · intro x hx
    apply (Submodule.mem_orthogonal _ _).mpr
    have hxE : x ∈ Module.End.eigenspace N.toLinearMap 0 := by
      exact Module.End.mem_eigenspace_iff.mpr (by simpa using hx)
    have hle : V ≤ (Module.End.eigenspace N.toLinearMap 0).orthogonal := by
      apply iSup_le
      intro α
      exact (NormalEigenspaces.normal_orthogonal_eigenspaces H N hN).isOrtho α.property
    intro y hy
    exact (Submodule.mem_orthogonal' _ _).mp (hle hy) x hxE

/-- The orthogonal Hilbert decomposition, without a separability assumption. -/
theorem decomposition : Spec.Decomposition.{u} := by
  intro H _ _ _ N hcompact hN
  have hclosed : IsClosed (nonzeroSpan N : Set H) := Submodule.isClosed_topologicalClosure _
  have he := congrArg Submodule.orthogonal (nonzeroSpan_orthogonal N hcompact hN)
  rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq] at he
  refine ⟨he, ?_⟩
  rw [he]
  letI : CompleteSpace N.ker := N.isClosed_ker.completeSpace_coe
  exact N.ker.isCompl_orthogonal

/-- Threshold truncations take every larger modulus before smaller ones;
ties are included together. This also gives constant truncations for a finite
nonzero spectrum once the threshold is small enough. -/
theorem ordered_expansion : Spec.OrderedExpansion.{u} := by
  intro H _ _ _ N hcompact hN
  classical
  let A (n : ℕ) : Set ℂ :=
    {α | α ∈ nonzeroEigenvalues N ∧ 1 / (n + 1 : ℝ) ≤ ‖α‖}
  have hA (n : ℕ) : (A n).Finite := by
    apply (NormalEigenspaces.compact_eigenvalues_finite_away_from_zero H N hcompact
      (1 / (n + 1 : ℝ)) (by positivity)).subset
    intro α hα
    exact ⟨hα.1.2, hα.2⟩
  let s (n : ℕ) : Finset ℂ := (hA n).toFinset
  have hmem (n : ℕ) (α : ℂ) : α ∈ s n ↔
      α ∈ nonzeroEigenvalues N ∧ 1 / (n + 1 : ℝ) ≤ ‖α‖ := (hA n).mem_toFinset
  have hmono : Monotone s := by
    intro n m hnm α hα
    obtain ⟨he, hb⟩ := (hmem n α).mp hα
    apply (hmem m α).mpr
    refine ⟨he, le_trans ?_ hb⟩
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hexhaust : ∀ α ∈ nonzeroEigenvalues N, ∃ n, α ∈ s n := by
    intro α hα
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hα.1)
    exact ⟨n, (hmem n α).mpr ⟨hα, hn.le⟩⟩
  have homitted (n : ℕ) (β : ℂ) (hβ : β ∈ nonzeroEigenvalues N) (hb : β ∉ s n) :
      ‖β‖ < 1 / (n + 1 : ℝ) := by
    by_contra! hh
    exact hb ((hmem n β).mpr ⟨hβ, hh⟩)
  refine ⟨s, hmono, ?_, hexhaust, ?_, ?_⟩
  · intro n α hα
    exact ((hmem n α).mp hα).1
  · intro n α hα β hβ hb
    exact (homitted n β hβ hb).le.trans ((hmem n α).mp hα).2
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, ?_⟩
    intro m hnm
    rw [dist_eq_norm, norm_sub_rev, tail_norm H N hcompact hN]
    apply lt_of_le_of_lt (real_sSup_le_nonneg (by positivity : 0 ≤ 1 / (n + 1 : ℝ)) ?_) hn
    rintro _ ⟨β, ⟨hβ, hb⟩, rfl⟩
    have hb' : β ∉ s n := fun h => hb (hmono hnm h)
    exact (homitted n β hβ hb').le

end ExpandedFA.CompactSpectral.NormalExpansion
