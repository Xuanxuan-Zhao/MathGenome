import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.CompactSpectral
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace D13Unified.Ch10.CompactSpectral

open Module Filter
open scoped Topology ComplexConjugate
open Specs.D13Unified.Ch10.CompactSpectral

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- An eigenvalue of a nonnegative symmetric operator is real and nonnegative. -/
theorem eigenvalue_real_nonneg {K : H →L[𝕜] H} (hK : K.IsSymmetric)
    (hpos : ∀ x : H, 0 ≤ RCLike.re (inner 𝕜 (K x) x))
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue K.toLinearMap μ) :
    (RCLike.re μ : 𝕜) = μ ∧ 0 ≤ RCLike.re μ := by
  have hr : (RCLike.re μ : 𝕜) = μ :=
    RCLike.conj_eq_iff_re.mp (hK.conj_eigenvalue_eq_self hμ)
  refine ⟨hr, ?_⟩
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hKv : K v = (RCLike.re μ : 𝕜) • v := by
    rw [hr]
    exact Module.End.mem_eigenspace_iff.mp hv
  have h := hpos v
  rw [hKv, inner_smul_real_left, RCLike.smul_re, inner_self_eq_norm_sq] at h
  exact nonneg_of_mul_nonneg_left h (sq_pos_of_pos (norm_pos_iff.mpr hv0))

/-- The positive eigenspaces account for precisely the orthogonal complement of the kernel. -/
theorem positiveSpan_closure [CompleteSpace H] {K : H →L[𝕜] H} (hc : IsCompactOperator K)
    (hs : K.IsSymmetric)
    (hp : ∀ x : H, 0 ≤ RCLike.re (inner 𝕜 (K x) x)) :
    (positiveSpan K).topologicalClosure = K.kerᗮ := by
  have hmem {μ : 𝕜} (hμ : μ ≠ 0) {v : H}
      (hv : v ∈ Module.End.eigenspace K.toLinearMap μ) : v ∈ positiveSpan K := by
    by_cases hv0 : v = 0
    · simp [hv0]
    have he := eigenvalue_real_nonneg hs hp
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
    have hr : 0 < RCLike.re μ := lt_of_le_of_ne he.2 (by
      intro h
      apply hμ
      rw [← he.1, ← h]
      simp)
    apply (le_iSup_of_le (⟨RCLike.re μ, hr⟩ : {r : ℝ // 0 < r}) le_rfl :
      Module.End.eigenspace K.toLinearMap (RCLike.re μ : 𝕜) ≤ positiveSpan K)
    simpa only [he.1] using hv
  have horth : (positiveSpan K)ᗮ = K.ker := by
    apply le_antisymm
    · intro x hx
      have hKx : K x ∈ (⨆ μ, Module.End.eigenspace K.toLinearMap μ)ᗮ := by
        rw [← Submodule.iInf_orthogonal]
        simp only [Submodule.mem_iInf]
        intro μ v hv
        change inner 𝕜 v (K.toLinearMap x) = 0
        rw [← hs v x, Module.End.mem_eigenspace_iff.mp hv, inner_smul_left]
        by_cases hμ : μ = 0
        · simp [hμ]
        · rw [hx v (hmem hμ hv), mul_zero]
      rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hKx
      exact hKx
    · intro x hx
      simp only [positiveSpan, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro r v hv
      have h := hs v x
      rw [Module.End.mem_eigenspace_iff.mp hv, inner_smul_left,
        show K.toLinearMap x = 0 from hx, inner_zero_right] at h
      exact (mul_eq_zero.mp h).resolve_left (by simpa using (ne_of_gt r.property))
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth]

/-- A uniformly separated family inside a compact metric set has a finite index type. -/
theorem finite_index_of_compact_separated {ι X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : IsCompact S) (f : ι → X) (hf : ∀ i, f i ∈ S)
    {ε : ℝ} (hε : 0 < ε) (hsep : ∀ i j, i ≠ j → ε ≤ dist (f i) (f j)) :
    Finite ι := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hS.finite_cover_balls (half_pos hε)
  have hchoose : ∀ i, ∃ y : t, dist (f i) y.val < ε / 2 := by
    intro i
    have h := hcover (hf i)
    simp only [Set.mem_iUnion, Metric.mem_ball] at h
    obtain ⟨y, hy, hd⟩ := h
    exact ⟨⟨y, hy⟩, hd⟩
  choose c hc using hchoose
  have : Finite t := ht.to_subtype
  apply Finite.of_injective c
  intro i j hij
  by_contra hne
  have hd : dist (f i) (f j) < ε := calc
    dist (f i) (f j) ≤ dist (f i) (c i).val + dist (c i).val (f j) :=
      dist_triangle _ _ _
    _ = dist (f i) (c i).val + dist (f j) (c j).val := by
      rw [hij, dist_comm (c j).val (f j)]
    _ < ε / 2 + ε / 2 := add_lt_add (hc i) (hc j)
    _ = ε := by ring
  exact (not_lt_of_ge (hsep i j hne)) hd

/-- There are only finitely many distinct eigenvalues whose modulus exceeds a fixed
positive threshold. This uses compactness and symmetry, without positivity. -/
theorem finite_eigenvalues_above {K : H →L[𝕜] H} (hc : IsCompactOperator K)
    (hs : K.IsSymmetric) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ ∧ ε ≤ ‖μ‖}.Finite := by
  classical
  let S := {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ ∧ ε ≤ ‖μ‖}
  have hex : ∀ μ : S, ∃ v : H,
      v ∈ Module.End.eigenspace K.toLinearMap μ.val ∧ ‖v‖ = 1 := by
    intro μ
    obtain ⟨v, hv, hv0⟩ := μ.property.1.exists_hasEigenvector
    exact ⟨(‖v‖⁻¹ : 𝕜) • v,
      (Module.End.eigenspace K.toLinearMap μ.val).smul_mem _ hv,
      norm_smul_inv_norm hv0⟩
  choose v hv hn using hex
  have hnorm (μ : S) : ‖K (v μ)‖ = ‖μ.val‖ := by
    change ‖K.toLinearMap (v μ)‖ = ‖μ.val‖
    rw [Module.End.mem_eigenspace_iff.mp (hv μ), norm_smul, hn μ, mul_one]
  obtain ⟨C, hC, hsub⟩ := hc.image_closedBall_subset_compact (f := K.toLinearMap) 1
  have : Finite S := finite_index_of_compact_separated hC (fun μ : S => K (v μ))
    (fun μ => hsub ⟨v μ, by simp [Metric.mem_closedBall, hn μ], rfl⟩) hε (by
      intro μ ν hne
      have hne' : μ.val ≠ ν.val := fun h => hne (Subtype.ext h)
      have ho : inner 𝕜 (v μ) (v ν) = 0 :=
        hs.orthogonalFamily_eigenspaces hne' ⟨v μ, hv μ⟩ ⟨v ν, hv ν⟩
      have hi : inner 𝕜 (K (v μ)) (K (v ν)) = 0 := by
        change inner 𝕜 (K.toLinearMap (v μ)) (K.toLinearMap (v ν)) = 0
        rw [Module.End.mem_eigenspace_iff.mp (hv μ),
          Module.End.mem_eigenspace_iff.mp (hv ν), inner_smul_left, inner_smul_right, ho]
        simp
      have heq := norm_sub_sq (𝕜 := 𝕜) (K (v μ)) (K (v ν))
      rw [hi, map_zero, mul_zero, sub_zero, hnorm μ, hnorm ν] at heq
      rw [dist_eq_norm]
      have hm := μ.property.2
      have hn' := ν.property.2
      nlinarith [norm_nonneg (K (v μ) - K (v ν)), sq_nonneg (‖μ.val‖ - ε),
        sq_nonneg (‖ν.val‖ - ε)])
  exact Set.toFinite S

/-- Countability is a union of finite positive-threshold sets, also in a
nonseparable ambient Hilbert space. -/
theorem countable_nonzeroEigenvalues {K : H →L[𝕜] H} (hc : IsCompactOperator K)
    (hs : K.IsSymmetric) : (nonzeroEigenvalues K).Countable := by
  have hfin (n : ℕ) :
      {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ ∧ 1 / (n + 1 : ℝ) ≤ ‖μ‖}.Finite :=
    finite_eigenvalues_above hc hs (by positivity)
  apply (Set.countable_iUnion fun n : ℕ => (hfin n).countable).mono
  intro μ hμ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hμ.1)
  exact Set.mem_iUnion.mpr ⟨n, hμ.2, hn.le⟩

/-- The finite-threshold assertion with each eigenvalue repeated its finite multiplicity. -/
theorem finite_multiplicitySlots_above {K : H →L[𝕜] H} (hc : IsCompactOperator K)
    (hs : K.IsSymmetric) {ε : ℝ} (hε : 0 < ε) :
    {s : multiplicitySlots K | ε ≤ ‖s.1.val‖}.Finite := by
  classical
  have hf : {μ : nonzeroEigenvalues K | ε ≤ ‖μ.val‖}.Finite := by
    have h := (finite_eigenvalues_above hc hs hε).preimage
      (f := fun μ : nonzeroEigenvalues K => μ.val) Subtype.val_injective.injOn
    exact h.subset fun μ hμ => ⟨μ.property.2, hμ⟩
  apply hf.preimage' (f := fun s : multiplicitySlots K => s.1)
  intro μ _
  apply (Set.finite_range (fun i : Fin (Module.finrank 𝕜
    (Module.End.eigenspace K.toLinearMap μ.val)) =>
      (⟨μ, i⟩ : multiplicitySlots K))).subset
  rintro ⟨ν, i⟩ hν
  have h : ν = μ := hν
  subst ν
  exact ⟨i, rfl⟩

/-- Any sequence of distinct multiplicity slots has eigenvalues tending to zero. -/
theorem eigenvalue_sequence_tendsto_zero {K : H →L[𝕜] H}
    (hc : IsCompactOperator K) (hs : K.IsSymmetric)
    {e : ℕ → multiplicitySlots K} (he : Function.Injective e) :
    Tendsto (fun n => (e n).1.val) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf := (finite_multiplicitySlots_above hc hs hε).preimage he.injOn
  have hev : ∀ᶠ n in atTop, n ∉ e ⁻¹' {s : multiplicitySlots K | ε ≤ ‖s.1.val‖} := by
    rw [← Nat.cofinite_eq_atTop]
    exact hf.eventually_cofinite_notMem
  filter_upwards [hev] with n hn
  change ¬ ε ≤ ‖(e n).1.val‖ at hn
  simpa only [dist_zero_right] using not_le.mp hn

/-- Positive compact spectral theorem, including kernel, multiplicity, countability,
finite thresholds and arbitrary infinite enumerations. -/
theorem compact_positive_spectral : spectralTheorem := by
  intro 𝕜 H _ _ _ _ K hc hs hp
  refine ⟨positiveSpan_closure hc hs hp, ?_, countable_nonzeroEigenvalues hc hs,
    ?_, ?_⟩
  · exact fun μ hμ => ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ
  · exact fun ε hε => finite_multiplicitySlots_above hc hs hε
  · exact fun e => eigenvalue_sequence_tendsto_zero hc hs e.injective

end D13Unified.Ch10.CompactSpectral
