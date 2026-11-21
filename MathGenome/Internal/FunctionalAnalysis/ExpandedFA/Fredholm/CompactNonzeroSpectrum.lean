import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectStabilization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Batteries.Tactic.OpenPrivate

/-! Nonzero compact spectrum on the original, possibly incomplete, normed space. -/
namespace ExpandedFA.Fredholm
open Filter
open scoped Topology
open private compact_bounded_subsequence from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange
universe u v
variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

lemma nonzero_spectral_shift_factor (K : E →L[𝕂] E) (μ : 𝕂) (hμ : μ ≠ 0) :
    μ • LinearMap.id - K.toLinearMap =
      μ • (LinearMap.id - μ⁻¹ • K.toLinearMap) := by
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hμ, one_smul]

lemma nonzero_spectral_shift_power_kernel (K : E →L[𝕂] E)
    (μ : 𝕂) (hμ : μ ≠ 0) (m : ℕ) :
    LinearMap.ker ((μ • LinearMap.id - K.toLinearMap) ^ m) =
      CompactDefectStabilizationSpec.kernelChain (μ⁻¹ • K) m := by
  change LinearMap.ker ((μ • LinearMap.id - K.toLinearMap) ^ m) =
    LinearMap.ker ((LinearMap.id - μ⁻¹ • K.toLinearMap) ^ m)
  rw [nonzero_spectral_shift_factor K μ hμ, smul_pow,
    LinearMap.ker_smul _ _ (pow_ne_zero m hμ)]

lemma compact_smul (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (a : 𝕂) :
    Compactness.IsCompactLinearMap (a • K).toLinearMap := by
  exact (Compactness.compact_iff_isCompactOperator _).mpr
    (((Compactness.compact_iff_isCompactOperator _).mp hK).smul a)

/-- Stabilization implies surjectivity under injectivity, without open mapping. -/
lemma compact_identity_sub_surjective_of_injective (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (hinj : Function.Injective (ContinuousLinearMap.id 𝕂 E - K)) :
    Function.Surjective (ContinuousLinearMap.id 𝕂 E - K) := by
  let f := (ContinuousLinearMap.id 𝕂 E - K).toLinearMap
  obtain ⟨p, hp, h⟩ := riesz_decomposition K hK
  have hd := (h p le_rfl).2.2
  have hn : CompactDefectStabilizationSpec.kernelChain K p = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    have hi : Function.Injective f := hinj
    simpa only [Module.End.coe_pow] using hi.iterate p
  have hr : CompactDefectStabilizationSpec.rangeChain K p = ⊤ := by
    have hc := hd.1.isCompl.codisjoint
    rw [codisjoint_iff, hn, bot_sup_eq] at hc
    exact hc
  intro y
  have hy : y ∈ LinearMap.range (f ^ p) := by
    change y ∈ CompactDefectStabilizationSpec.rangeChain K p
    rw [hr]
    trivial
  have hy1 := f.iterateRange.monotone hp hy
  change y ∈ LinearMap.range (f ^ 1) at hy1
  rw [pow_one] at hy1
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy1
  exact ⟨x, hx⟩

/-- A non-eigenvalue gives an actual bounded inverse on E. -/
lemma compact_nonzero_shift_bounded_inverse (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (μ : 𝕂) (hμ : μ ≠ 0)
    (hne : ¬ ∃ x : E, x ≠ 0 ∧ K x = μ • x) :
    ∃ S : E →L[𝕂] E,
      (∀ x : E, S (μ • x - K x) = x) ∧ (∀ x : E, μ • S x - K (S x) = x) := by
  let L := μ⁻¹ • K
  have hL := compact_smul K hK μ⁻¹
  have hinj : Function.Injective (ContinuousLinearMap.id 𝕂 E - L) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have hx' : x - μ⁻¹ • K x = 0 := hx
    have he : K x = μ • x := by
      have ht := congrArg (fun y : E => μ • y) (sub_eq_zero.mp hx')
      simpa only [smul_inv_smul₀ hμ] using ht.symm
    by_contra hx0
    exact hne ⟨x, hx0, he⟩
  obtain ⟨e, he⟩ := compact_identity_sub_equiv L hL hinj
    (compact_identity_sub_surjective_of_injective L hL hinj)
  refine ⟨e.symm.toContinuousLinearMap.comp (μ⁻¹ • ContinuousLinearMap.id 𝕂 E), ?_, ?_⟩
  · intro x
    change e.symm (μ⁻¹ • (μ • x - K x)) = x
    have ht : μ⁻¹ • (μ • x - K x) = e x := by
      rw [he]
      simp [L, smul_sub, inv_smul_smul₀ hμ]
    rw [ht, e.symm_apply_apply]
  · intro x
    change μ • e.symm (μ⁻¹ • x) - K (e.symm (μ⁻¹ • x)) = x
    have ht := e.apply_symm_apply (μ⁻¹ • x)
    rw [he] at ht
    have ht' := congrArg (fun y : E => μ • y) ht
    simpa [L, smul_sub, smul_inv_smul₀ hμ] using ht'

theorem compact_nonzero_spectrum_iff_eigenvalue :
    CompactNonzeroSpectrumSpec.NonzeroSpectrumEigenvalue := by
  intro 𝕂 _ E _ _ K hK μ hμ
  change (μ ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    𝕂 (E →L[𝕂] E) K ↔ _)
  rw [BanachAlgebra.operator_spectrum_iff_no_bounded_inverse]
  constructor
  · intro h
    by_contra hne
    exact h (compact_nonzero_shift_bounded_inverse K hK μ hμ hne)
  · rintro ⟨x, hx, hxe⟩ ⟨S, hleft, _⟩
    have he := hleft x
    rw [hxe, sub_self, map_zero] at he
    exact hx he.symm

theorem compact_generalized_eigenspace_stabilizes :
    CompactNonzeroSpectrumSpec.GeneralizedEigenspaceStabilizes := by
  intro 𝕂 _ E _ _ K hK μ hμ
  let L := μ⁻¹ • K
  let A : E →ₗ[𝕂] E := μ • LinearMap.id - K.toLinearMap
  have hL := compact_smul K hK μ⁻¹
  obtain ⟨r, hr⟩ := (power_chains_stabilize L hL).1
  let p := max 1 r
  have hp : 1 ≤ p := le_max_left _ _
  have hrp : r ≤ p := le_max_right _ _
  have hscale (m : ℕ) : LinearMap.ker (A ^ m) =
      CompactDefectStabilizationSpec.kernelChain L m :=
    nonzero_spectral_shift_power_kernel K μ hμ m
  have hstable (m : ℕ) (hm : p ≤ m) :
      LinearMap.ker (A ^ m) = LinearMap.ker (A ^ p) := by
    rw [hscale m, hscale p, hr m (hrp.trans hm), hr p hrp]
  have hfin : FiniteDimensional 𝕂 (LinearMap.ker (A ^ p)) := by
    rw [hscale p]
    have hf := (identity_sub_compact_powers_closed_range_finite_kernel L hL p hp).2.1
    rw [ContinuousLinearMap.toLinearMap_pow] at hf
    exact hf
  refine ⟨p, hp, hfin, hstable, ?_⟩
  ext x
  constructor
  · rintro ⟨m, _, hx⟩
    by_cases hmp : m ≤ p
    · exact A.iterateKer.monotone hmp hx
    · rw [hstable m (le_of_not_ge hmp)] at hx
      exact hx
  · intro hx
    exact ⟨p, hp, hx⟩

/-- A compact image of a bounded sequence cannot remain separated. -/
lemma compact_bounded_not_separated (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (x : ℕ → E)
    (hb : Bornology.IsBounded (Set.range x))
    (hs : ∀ m n, m < n → (1 / 2 : ℝ) ≤ ‖K (x m) - K (x n)‖) : False := by
  obtain ⟨y, k, hk, hlim⟩ :=
    compact_bounded_subsequence K.toLinearMap hK x hb
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have hlt := hN (N + 1) (by omega)
  have hge := hs (k N) (k (N + 1)) (hk (by omega))
  rw [dist_eq_norm, norm_sub_rev] at hlt
  exact hlt.not_ge hge

/-- Distinct eigenvalues bounded away from zero cannot form an infinite sequence.
The proof applies Riesz's lemma to the finite initial eigenvector spans. -/
lemma compact_no_injective_eigenvalue_sequence (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (ε : ℝ) (hε : 0 < ε)
    (μ : ℕ → 𝕂) (hμ : Function.Injective μ) (hbound : ∀ n, ε ≤ ‖μ n‖)
    (v : ℕ → E) (hv : ∀ n, K (v n) = μ n • v n) (hv0 : ∀ n, v n ≠ 0) : False := by
  classical
  have hμ0 (n : ℕ) : μ n ≠ 0 := norm_pos_iff.mp (hε.trans_le (hbound n))
  have hlin : LinearIndependent 𝕂 v :=
    Module.End.eigenvectors_linearIndependent' K.toLinearMap μ hμ v (fun n =>
      ⟨Module.End.mem_eigenspace_iff.mpr (hv n), hv0 n⟩)
  let F (n : ℕ) : Submodule 𝕂 E := Submodule.span 𝕂 (v '' Set.Iio n)
  have hFfin (n : ℕ) : FiniteDimensional 𝕂 (F n) :=
    FiniteDimensional.span_of_finite 𝕂 ((Set.finite_Iio n).image v)
  have hmono : Monotone F := by
    intro m n hmn
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  have hstrict (n : ℕ) : F n < F (n + 1) := by
    apply lt_of_le_of_ne (hmono (Nat.le_succ n))
    intro heq
    apply hlin.notMem_span_image (show n ∉ Set.Iio n by simp)
    change v n ∈ F n
    rw [heq]
    exact Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have hchoose (n : ℕ) : ∃ x ∈ F (n + 1), ‖x‖ = 1 ∧
      ∀ y ∈ F n, (1 / 2 : ℝ) ≤ ‖x - y‖ := by
    let := hFfin n
    exact exists_unit_mem_separated (hstrict n) (F n).closed_of_finiteDimensional
  choose x hx hnorm hfar using hchoose
  have hKmem (n : ℕ) {y : E} (hy : y ∈ F n) : K y ∈ F n := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [hv i]
      exact (F n).smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => simpa using (F n).add_mem hy hz
    | smul a y _ hy => simpa using (F n).smul_mem a hy
  have hres (n : ℕ) {y : E} (hy : y ∈ F (n + 1)) :
      K y - μ n • y ∈ F n := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [hv i]
      by_cases hin : i < n
      · exact (F n).sub_mem
          ((F n).smul_mem _ (Submodule.subset_span ⟨i, hin, rfl⟩))
          ((F n).smul_mem _ (Submodule.subset_span ⟨i, hin, rfl⟩))
      · have : i = n := by
          have hi' : i < n + 1 := hi
          omega
        subst i
        simp
    | zero => simp
    | add y z _ _ hy hz =>
      simpa only [map_add, smul_add, add_sub_add_comm] using (F n).add_mem hy hz
    | smul a y _ hy =>
      simpa only [map_smul, smul_sub, smul_smul, mul_comm a] using (F n).smul_mem a hy
  let z (n : ℕ) : E := (μ n)⁻¹ • x n
  have hzbound (n : ℕ) : ‖z n‖ ≤ ε⁻¹ := by
    dsimp [z]
    rw [norm_smul, norm_inv, hnorm n, mul_one]
    exact (inv_le_inv₀ (hε.trans_le (hbound n)) hε).mpr (hbound n)
  have hb : Bornology.IsBounded (Set.range z) := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := ε⁻¹)).subset
    rintro _ ⟨n, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzbound n
  apply compact_bounded_not_separated K hK z hb
  intro j n hjn
  have hr : K (z n) - x n ∈ F n := by
    have ht := (F n).smul_mem (μ n)⁻¹ (hres n (hx n))
    simpa only [z, map_smul, smul_sub, inv_smul_smul₀ (hμ0 n)] using ht
  have hj : K (z j) ∈ F n :=
    hKmem n ((F n).smul_mem _ (hmono hjn (hx j)))
  have hfar' := hfar n (K (z j) - (K (z n) - x n)) ((F n).sub_mem hj hr)
  have heq : x n - (K (z j) - (K (z n) - x n)) = K (z n) - K (z j) := by abel
  rwa [heq, norm_sub_rev] at hfar'

/-- There are finitely many spectral values outside every ball about zero. -/
theorem compact_spectrum_finite_away_from_zero :
    CompactNonzeroSpectrumSpec.FiniteAwayFromZero.{u,v} := by
  intro 𝕂 _ E _ _ K hK ε hε
  classical
  by_contra hs
  let f := Set.Infinite.natEmbedding _ hs
  let μ : ℕ → 𝕂 := fun n => (f n).val
  have hμ : Function.Injective μ := Subtype.val_injective.comp f.injective
  have hbound (n : ℕ) : ε ≤ ‖μ n‖ := (f n).property.2
  have heigen (n : ℕ) : ∃ x : E, x ≠ 0 ∧ K x = μ n • x := by
    obtain ⟨x, hx, hk⟩ :=
      (compact_nonzero_spectrum_iff_eigenvalue K hK (μ n)
        (norm_pos_iff.mp (hε.trans_le (hbound n)))).mp (f n).property.1
    exact ⟨x, hx, hk⟩
  choose v hv0 hv using heigen
  exact compact_no_injective_eigenvalue_sequence K hK ε hε μ hμ hbound v hv hv0

/-- Even a non-spectral nonzero scalar has a neighborhood containing no
spectral value other than possibly itself. -/
lemma compact_spectrum_neighborhood (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (μ : 𝕂) (hμ : μ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ν : 𝕂,
      ν ∈ spectrum 𝕂 K → dist ν μ < r → ν = μ := by
  let S := {ν : 𝕂 | ν ∈ spectrum 𝕂 K ∧
    ‖μ‖ / 2 ≤ ‖ν‖}
  have hp : 0 < ‖μ‖ / 2 := half_pos (norm_pos_iff.mpr hμ)
  have hfin : S.Finite := compact_spectrum_finite_away_from_zero K hK _ hp
  have hU : (S \ {μ})ᶜ ∩ Metric.ball μ (‖μ‖ / 2) ∈ 𝓝 μ :=
    Filter.inter_mem ((hfin.sdiff.isClosed).compl_mem_nhds (by simp))
      (Metric.ball_mem_nhds μ hp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, ?_⟩
  intro ν hν hd
  have ht := hsub hd
  by_contra hne
  apply ht.1
  refine ⟨⟨hν, ?_⟩, hne⟩
  have hnorm := norm_sub_norm_le μ ν
  rw [← dist_eq_norm, dist_comm μ ν] at hnorm
  have hdist : dist ν μ < ‖μ‖ / 2 := ht.2
  linarith

theorem compact_spectrum_accumulation_only_zero :
    CompactNonzeroSpectrumSpec.AccumulationOnlyZero.{u,v} := by
  intro 𝕂 _ E _ _ K hK μ ha
  by_contra hμ
  obtain ⟨r, hr, h⟩ := compact_spectrum_neighborhood K hK μ hμ
  obtain ⟨ν, ⟨hd, hν⟩, hne⟩ :=
    accPt_iff_nhds.mp ha (Metric.ball μ r) (Metric.ball_mem_nhds μ hr)
  exact hne (h ν hν hd)

theorem compact_eigenvalues_finite_away_from_zero :
    CompactNonzeroSpectrumSpec.FiniteEigenvaluesAwayFromZero := by
  intro 𝕂 _ E _ _ K hK ε hε
  apply (compact_spectrum_finite_away_from_zero K hK ε hε).subset
  rintro μ ⟨he, hb⟩
  exact ⟨(compact_nonzero_spectrum_iff_eigenvalue K hK μ
    (norm_pos_iff.mp (hε.trans_le hb))).mpr he, hb⟩

/-- The full spectral assertion for bounded compact maps. -/
theorem compact_nonzero_spectral_conclusion (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    CompactNonzeroSpectrumSpec.SpectralConclusion K := by
  exact ⟨compact_nonzero_spectrum_iff_eigenvalue K hK,
    compact_generalized_eigenspace_stabilizes K hK,
    compact_spectrum_finite_away_from_zero K hK,
    compact_eigenvalues_finite_away_from_zero K hK,
    compact_spectrum_accumulation_only_zero K hK⟩

/-- No separate boundedness assumption on the original compact linear map. -/
theorem compact_nonzero_spectral_theory :
    CompactNonzeroSpectrumSpec.LinearCompactSpectralTheorem := by
  intro 𝕂 _ E _ _ K hK
  let Kb : E →L[𝕂] E := ⟨K, ((Compactness.compact_iff_isCompactOperator K).mp hK).continuous⟩
  exact ⟨Kb, rfl, compact_nonzero_spectral_conclusion Kb hK⟩

end ExpandedFA.Fredholm
