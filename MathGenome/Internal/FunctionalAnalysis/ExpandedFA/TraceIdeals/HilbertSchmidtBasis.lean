import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularApproximation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Quantitative Hilbert–Schmidt bounds and compactness for arbitrary real/complex
Hilbert spaces. The shared definitions handle all basis index universes and
infinite values. Finite column subsets, rather than an enumeration, give the
compact approximation net. Spectral multiplicities identify the canonical
singular square sum. Square-summable columns give the complete Hilbert
realization, and isometric matrix coordinates give its inner product.
-/
noncomputable section
namespace ExpandedFA.TraceIdeals.HilbertSchmidtBasis
universe u v w z t a b
open scoped InnerProductSpace ENNReal
open HilbertSchmidtDefinitions
open Filter Topology

section
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

lemma square_in_basis {ι : Type a} (T : H →L[𝕜] K) (e : ι → H)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e) :
    hilbertSchmidtSquare T = basisSquareSum T e := squareSum_in_basis T e he

theorem adjoint_square (T : H →L[𝕜] K) :
    hilbertSchmidtSquare (ContinuousLinearMap.adjoint T) = hilbertSchmidtSquare T := by
  obtain ⟨S, hS⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 K
  rw [square_in_basis T (Subtype.val : S → H) hS,
    square_in_basis (ContinuousLinearMap.adjoint T) (Subtype.val : R → K) hR]
  exact (adjoint_basis_identity T _ _ hS hR).symm

theorem adjoint_finiteness (T : H →L[𝕜] K) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T := by
  change hilbertSchmidtSquare (ContinuousLinearMap.adjoint T) < ∞ ↔ hilbertSchmidtSquare T < ∞
  rw [adjoint_square]

theorem adjoint_norm (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K))
    (h : IsHilbertSchmidt (ContinuousLinearMap.adjoint T.val)) :
    hilbertSchmidtNorm ⟨ContinuousLinearMap.adjoint T.val, h⟩ = hilbertSchmidtNorm T := by
  change Real.sqrt (hilbertSchmidtSquare (ContinuousLinearMap.adjoint T.val)).toReal =
    Real.sqrt (hilbertSchmidtSquare T.val).toReal
  rw [adjoint_square]

/-- An extended square bound, also valid for operators outside S₂. -/
theorem postcomp_square_bound {G : Type z} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] (T : H →L[𝕜] K) (A : K →L[𝕜] G) :
    hilbertSchmidtSquare (A.comp T) ≤ ENNReal.ofReal (‖A‖ ^ 2) * hilbertSchmidtSquare T := by
  obtain ⟨S, hS⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  rw [square_in_basis T (Subtype.val : S → H) hS,
    square_in_basis (A.comp T) (Subtype.val : S → H) hS]
  change (∑' i : S, ENNReal.ofReal (‖A (T i.val)‖ ^ 2)) ≤
    ENNReal.ofReal (‖A‖ ^ 2) * ∑' i : S, ENNReal.ofReal (‖T i.val‖ ^ 2)
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖A (T i.val)‖ ^ 2 ≤ (‖A‖ * ‖T i.val‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = ‖A‖ ^ 2 * ‖T i.val‖ ^ 2 := mul_pow _ _ _

theorem precomp_square_bound {D : Type z} [NormedAddCommGroup D]
    [InnerProductSpace 𝕜 D] [CompleteSpace D] (T : H →L[𝕜] K) (B : D →L[𝕜] H) :
    hilbertSchmidtSquare (T.comp B) ≤ ENNReal.ofReal (‖B‖ ^ 2) * hilbertSchmidtSquare T := by
  calc
    hilbertSchmidtSquare (T.comp B) =
        hilbertSchmidtSquare (ContinuousLinearMap.adjoint (T.comp B)) := (adjoint_square _).symm
    _ = hilbertSchmidtSquare ((ContinuousLinearMap.adjoint B).comp
        (ContinuousLinearMap.adjoint T)) := by rw [ContinuousLinearMap.adjoint_comp]
    _ ≤ ENNReal.ofReal (‖ContinuousLinearMap.adjoint B‖ ^ 2) *
        hilbertSchmidtSquare (ContinuousLinearMap.adjoint T) := postcomp_square_bound _ _
    _ = ENNReal.ofReal (‖B‖ ^ 2) * hilbertSchmidtSquare T := by
      rw [LinearIsometryEquiv.norm_map, adjoint_square]

/-- Parseval in the target and Cauchy–Schwarz in the source give a pointwise
bound; there is no need to enumerate either basis. -/
lemma apply_square_le (T : H →L[𝕜] K) (x : H) :
    ENNReal.ofReal (‖T x‖ ^ 2) ≤ hilbertSchmidtSquare T * ENNReal.ofReal (‖x‖ ^ 2) := by
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 K
  rw [← adjoint_square T,
    square_in_basis (ContinuousLinearMap.adjoint T) (Subtype.val : R → K) hR,
    parseval_ennreal (Subtype.val : R → K) hR (T x)]
  change (∑' j : R, ENNReal.ofReal (‖inner 𝕜 j.val (T x)‖ ^ 2)) ≤
    (∑' j : R, ENNReal.ofReal (‖ContinuousLinearMap.adjoint T j.val‖ ^ 2)) *
      ENNReal.ofReal (‖x‖ ^ 2)
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖inner 𝕜 (ContinuousLinearMap.adjoint T j.val) x‖ ^ 2 ≤
        (‖ContinuousLinearMap.adjoint T j.val‖ * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = _ := mul_pow _ _ _

theorem operator_norm_bound (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K)) :
    ‖T.val‖ ≤ hilbertSchmidtNorm T := by
  have hn : 0 ≤ hilbertSchmidtNorm T := Real.sqrt_nonneg _
  apply T.val.opNorm_le_bound hn
  intro x
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top T.property.ne ENNReal.ofReal_ne_top) (apply_square_le T.val x)
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul] at h
  have hs : hilbertSchmidtNorm T ^ 2 = (hilbertSchmidtSquare T.val).toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  rw [← hs, ← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg _))).mp h

lemma postcomp_finiteness {G : Type z} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] (T : H →L[𝕜] K) (A : K →L[𝕜] G)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (A.comp T) :=
  lt_of_le_of_lt (postcomp_square_bound T A)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)

lemma precomp_finiteness {D : Type z} [NormedAddCommGroup D]
    [InnerProductSpace 𝕜 D] [CompleteSpace D] (T : H →L[𝕜] K) (B : D →L[𝕜] H)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (T.comp B) :=
  lt_of_le_of_lt (precomp_square_bound T B)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)

theorem ideal_finiteness {D : Type z} {G : Type t}
    [NormedAddCommGroup D] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 D] [InnerProductSpace 𝕜 G] [CompleteSpace D] [CompleteSpace G]
    (T : H →L[𝕜] K) (A : K →L[𝕜] G) (B : D →L[𝕜] H)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (A.comp (T.comp B)) :=
  postcomp_finiteness _ A (precomp_finiteness T B hT)

lemma square_of_norm (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K)) :
    hilbertSchmidtNorm T ^ 2 = (hilbertSchmidtSquare T.val).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem ideal_norm_bound {D : Type z} {G : Type t}
    [NormedAddCommGroup D] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 D] [InnerProductSpace 𝕜 G] [CompleteSpace D] [CompleteSpace G]
    (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K))
    (A : K →L[𝕜] G) (B : D →L[𝕜] H)
    (h : IsHilbertSchmidt (A.comp (T.val.comp B))) :
    hilbertSchmidtNorm ⟨A.comp (T.val.comp B), h⟩ ≤ ‖A‖ * hilbertSchmidtNorm T * ‖B‖ := by
  have hb : hilbertSchmidtSquare (A.comp (T.val.comp B)) ≤
      ENNReal.ofReal (‖A‖ ^ 2) * (ENNReal.ofReal (‖B‖ ^ 2) * hilbertSchmidtSquare T.val) :=
    (postcomp_square_bound _ A).trans (mul_le_mul_right (precomp_square_bound T.val B) _)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top T.property.ne)) hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  rw [← square_of_norm ⟨A.comp (T.val.comp B), h⟩, ← square_of_norm T] at hr
  have hn : 0 ≤ hilbertSchmidtNorm T := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  calc
    hilbertSchmidtNorm ⟨A.comp (T.val.comp B), h⟩ ^ 2 ≤
        ‖A‖ ^ 2 * (‖B‖ ^ 2 * hilbertSchmidtNorm T ^ 2) := hr
    _ = (‖A‖ * hilbertSchmidtNorm T * ‖B‖) ^ 2 := by ring

lemma add_finiteness (S T : H →L[𝕜] K) (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) := by
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  have hs := (finiteness_in_basis S (Subtype.val : R → H) hR).mp hS
  have ht := (finiteness_in_basis T (Subtype.val : R → H) hR).mp hT
  apply (finiteness_in_basis (S + T) (Subtype.val : R → H) hR).mpr
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
    (f := fun i : R => 2 * (‖S i.val‖ ^ 2 + ‖T i.val‖ ^ 2))
  · intro i
    have h := norm_add_le (S i.val) (T i.val)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hdiff := sq_nonneg (‖S i.val‖ - ‖T i.val‖)
    change ‖S i.val + T i.val‖ ^ 2 ≤ _
    nlinarith
  · exact (hs.add ht).mul_left 2

lemma smul_finiteness (c : 𝕜) (T : H →L[𝕜] K) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (c • T) := by
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  apply (finiteness_in_basis (c • T) (Subtype.val : R → H) hR).mpr
  have hs := (finiteness_in_basis T (Subtype.val : R → H) hR).mp hT
  simpa only [smul_apply, norm_smul, mul_pow] using hs.mul_left (‖c‖ ^ 2)

theorem linear_subspace :
    ∃ M : Submodule 𝕜 (H →L[𝕜] K), ∀ T, T ∈ M ↔ IsHilbertSchmidt T := by
  exact ⟨{ carrier := {T | IsHilbertSchmidt T}
           zero_mem' := (zero_square (𝕜 := 𝕜) (H := H) (K := K)).2
           add_mem' := fun hS hT => add_finiteness _ _ hS hT
           smul_mem' := fun c _ hT => smul_finiteness c _ hT }, fun _ => Iff.rfl⟩

/-- Finite-column approximants, indexed by all finite subsets. -/
def columnTruncation {ι : Type a} (T : H →L[𝕜] K) (e : ι → H) (s : Finset ι) : H →L[𝕜] K :=
  ∑ i ∈ s, (innerSL 𝕜 (e i)).smulRight (T (e i))

omit [CompleteSpace H] [CompleteSpace K] in
lemma columnTruncation_on_basis {ι : Type a} (T : H →L[𝕜] K) (e : ι → H)
    (he : Orthonormal 𝕜 e) (s : Finset ι) (j : ι) :
    by classical exact columnTruncation T e s (e j) = if j ∈ s then T (e j) else 0 := by
  classical
  simp [columnTruncation, sum_apply, orthonormal_iff_ite.mp he, eq_comm]

lemma column_error_square {ι : Type a} (T : H →L[𝕜] K) (e : ι → H)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e) (s : Finset ι) :
    hilbertSchmidtSquare (T - columnTruncation T e s) =
      ∑' i : {i // i ∉ s}, ENNReal.ofReal (‖T (e i.val)‖ ^ 2) := by
  classical
  rw [square_in_basis (T - columnTruncation T e s) e he]
  change (∑' i, ENNReal.ofReal (‖(T - columnTruncation T e s) (e i)‖ ^ 2)) = _
  change _ = ∑' i : ↥((s : Set ι)ᶜ), ENNReal.ofReal (‖T (e i.val)‖ ^ 2)
  rw [tsum_subtype ((s : Set ι)ᶜ) (fun i => ENNReal.ofReal (‖T (e i)‖ ^ 2))]
  apply tsum_congr
  intro i
  simp only [sub_apply, columnTruncation_on_basis T e he.1 s i]
  by_cases hi : i ∈ s <;> simp [hi]

omit [CompleteSpace H] [CompleteSpace K] in
lemma columnTruncation_compact {ι : Type a} (T : H →L[𝕜] K) (e : ι → H) (s : Finset ι) :
    IsCompactOperator (columnTruncation T e s) := by
  classical
  apply (compactOperator (RingHom.id 𝕜) H K).sum_mem
  intro i hi
  have hc : IsCompactOperator (innerSL 𝕜 (e i)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hc.clm_comp ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (T (e i)))

theorem compactness (T : H →L[𝕜] K) (hT : IsHilbertSchmidt T) :
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap := by
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  let e : R → H := Subtype.val
  have herr (s : Finset R) : IsHilbertSchmidt (T - columnTruncation T e s) := by
    change hilbertSchmidtSquare (T - columnTruncation T e s) < ∞
    rw [column_error_square T e hR s]
    have ht : (∑' i : R, ENNReal.ofReal (‖T (e i)‖ ^ 2)) < ∞ := by
      change basisSquareSum T e < ∞
      rw [← square_in_basis T e hR]
      exact hT
    exact lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective
      (f := (Subtype.val : {i : R // i ∉ s} → R)) Subtype.val_injective
      (fun i : R => ENNReal.ofReal (‖T (e i)‖ ^ 2))) ht
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero
    (show (∑' i : R, ENNReal.ofReal (‖T (e i)‖ ^ 2)) ≠ ∞ from by
      change basisSquareSum T e ≠ ∞
      rw [← square_in_basis T e hR]
      exact hT.ne)
  have hs : Filter.Tendsto (fun s : Finset R => hilbertSchmidtNorm
      ⟨T - columnTruncation T e s, herr s⟩) Filter.atTop (nhds 0) := by
    simp only [hilbertSchmidtNorm, HilbertSchmidtDefinitions.Spec.HilbertSchmidtNormValue,
      column_error_square T e hR]
    convert (Real.continuous_sqrt.tendsto 0).comp
      ((ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp htail) using 1
    · funext s
      rfl
    · simp
  have hn : Filter.Tendsto (fun s : Finset R => ‖columnTruncation T e s - T‖)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun s => ?_) hs
    rw [norm_sub_rev]
    exact operator_norm_bound ⟨_, herr s⟩
  apply (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
  exact isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr hn)
    (Filter.Eventually.of_forall (columnTruncation_compact T e))


open ExpandedFA.CompactSpectral

/-- Pythagoras for the norm-convergent singular expansion. -/
lemma singular_expansion_norm_square (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (x : H) :
    HasSum (fun j => S.sigma j ^ 2 * ‖inner 𝕜 (S.rightVector j) x‖ ^ 2)
      (‖T x‖ ^ 2) := by
  classical
  have h := ((continuous_norm.pow 2).tendsto (T x)).comp (S.expansion x)
  change Tendsto (fun q : Finset S.Index => ∑ j ∈ q,
    S.sigma j ^ 2 * ‖inner 𝕜 (S.rightVector j) x‖ ^ 2) (SummationFilter.unconditional S.Index).filter (nhds (‖T x‖ ^ 2))
  convert h using 1
  funext q
  dsimp only [Function.comp_apply, Pi.pow_apply]
  rw [SingularApproximation.norm_sum_orthonormal_sq _ S.left_orthonormal]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive j), mul_pow]

/-- The extended square sum is the sum over any full singular system. -/
lemma square_eq_singular_system (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) :
    hilbertSchmidtSquare T = ∑' j, ENNReal.ofReal (S.sigma j ^ 2) := by
  obtain ⟨R, hR⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 H
  rw [square_in_basis T (Subtype.val : R → H) hR]
  change (∑' i : R, ENNReal.ofReal (‖T i.val‖ ^ 2)) = _
  calc
    _ = ∑' i : R, ∑' j, ENNReal.ofReal (S.sigma j ^ 2) *
        ENNReal.ofReal (‖inner 𝕜 (S.rightVector j) i.val‖ ^ 2) := by
      apply tsum_congr
      intro i
      have hs := singular_expansion_norm_square T S i.val
      rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
        (sq_nonneg _) (sq_nonneg _)) hs.summable]
      apply tsum_congr
      intro j
      exact ENNReal.ofReal_mul (sq_nonneg _)
    _ = ∑' j, ∑' i : R, ENNReal.ofReal (S.sigma j ^ 2) *
        ENNReal.ofReal (‖inner 𝕜 (S.rightVector j) i.val‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ENNReal.ofReal (S.sigma j ^ 2) := by
      apply tsum_congr
      intro j
      rw [ENNReal.tsum_mul_left]
      have hp := parseval_ennreal (Subtype.val : R → H) hR (S.rightVector j)
      simp only [S.right_orthonormal.norm_eq_one, one_pow, ENNReal.ofReal_one] at hp
      have hi : (∑' i : R, ENNReal.ofReal
          (‖inner 𝕜 (S.rightVector j) i.val‖ ^ 2)) = 1 := by
        simpa only [norm_inner_symm] using hp.symm
      rw [hi, mul_one]

/-- Grouping by positive spectral values identifies the unordered singular
system sum with the canonical sequence, including multiplicities. -/
lemma singular_system_sum_eq (T : H →L[𝕜] K)
    (hT : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) :
    (∑' j, ENNReal.ofReal (S.sigma j ^ 2)) = singularSquareSum T := by
  classical
  let a : ℕ → ℝ := fun n => SingularApproximation.Spec.SingularValueValue T (n + 1)
  have ha (n) : 0 ≤ a n :=
    (SingularApproximation.singular_sequence_properties 𝕜 H K T hT).1 _ (Nat.zero_lt_succ _)
  change _ = ∑' n, ENNReal.ofReal (a n ^ 2)
  rw [← ENNReal.tsum_fiberwise (fun j => ENNReal.ofReal (S.sigma j ^ 2)) S.sigma,
    ← ENNReal.tsum_fiberwise (fun n => ENNReal.ofReal (a n ^ 2)) a]
  apply tsum_congr
  intro c
  by_cases hc : 0 < c
  · have hm := SingularApproximation.singular_spectral_multiplicity 𝕜 H K T hT c hc
    let B : Set ℕ := {n | 0 < n ∧ SingularApproximation.Spec.SingularValueValue T n = c}
    have himage : Nat.succ '' {n | a n = c} = B := by
      ext n
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨Nat.zero_lt_succ m, hm⟩
      · rintro ⟨hn, he⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        exact ⟨m, he, rfl⟩
    have hpre : a ⁻¹' {c} = Nat.succ ⁻¹' B := by
      ext n
      simp [B, a]
    have hfin : (a ⁻¹' {c}).Finite := by
      rw [hpre]
      exact Set.Finite.preimage Nat.succ_injective.injOn hm.2.2.1
    have hcard : (a ⁻¹' {c}).ncard = {j | S.sigma j = c}.ncard := by
      calc
        _ = B.ncard := by
          rw [← himage]
          exact (Set.ncard_image_of_injective _ Nat.succ_injective).symm
        _ = _ := hm.2.2.2.trans (SingularApproximation.gram_eigenspace_multiplicity T S hc)
    have hecard : (a ⁻¹' {c}).encard = (S.sigma ⁻¹' {c}).encard := by
      change (a ⁻¹' {c}).encard = {j | S.sigma j = c}.encard
      rw [← hfin.cast_ncard_eq, ← (S.finite_multiplicity c hc).cast_ncard_eq, hcard]
    calc
      _ = ∑' _ : S.sigma ⁻¹' {c}, ENNReal.ofReal (c ^ 2) := by
        apply tsum_congr
        intro j
        rw [show S.sigma j.val = c from j.property]
      _ = (S.sigma ⁻¹' {c}).encard * ENNReal.ofReal (c ^ 2) := ENNReal.tsum_set_const _ _
      _ = (a ⁻¹' {c}).encard * ENNReal.ofReal (c ^ 2) := by rw [hecard]
      _ = ∑' _ : a ⁻¹' {c}, ENNReal.ofReal (c ^ 2) := (ENNReal.tsum_set_const _ _).symm
      _ = _ := by
        apply tsum_congr
        intro n
        rw [show a n.val = c from n.property]
  · have hc' : c ≤ 0 := le_of_not_gt hc
    have hz : (∑' j : S.sigma ⁻¹' {c}, ENNReal.ofReal (S.sigma j.val ^ 2)) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro j
      exact False.elim ((not_lt_of_ge hc') (j.property ▸ S.positive j.val))
    rw [hz]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    have hn : a n.val = 0 := le_antisymm (n.property.trans_le hc') (ha n.val)
    simp [hn]

theorem singular_square_identity (T : H →L[𝕜] K) (hT : IsHilbertSchmidt T) :
    hilbertSchmidtSquare T = singularSquareSum T := by
  have hc := compactness T hT
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hc
  exact (square_eq_singular_system T S).trans (singular_system_sum_eq T hc S)

theorem singular_norm_identity (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K)) :
    Summable (fun n : ℕ => SingularApproximation.Spec.SingularValueValue T.val (n + 1) ^ 2) ∧
      hilbertSchmidtNorm T ^ 2 = ∑' n : ℕ,
        SingularApproximation.Spec.SingularValueValue T.val (n + 1) ^ 2 := by
  have hfin : singularSquareSum T.val < ∞ := by
    rw [← singular_square_identity T.val T.property]
    exact T.property
  have hs := ENNReal.summable_toReal hfin.ne
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hs
  refine ⟨hs, ?_⟩
  rw [square_of_norm, singular_square_identity T.val T.property]
  change (∑' n : ℕ, ENNReal.ofReal
    (SingularApproximation.Spec.SingularValueValue T.val (n + 1) ^ 2)).toReal = _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => sq_nonneg _))]

/-- The square-sum norm identity in a vector-valued Hilbert sum. -/
lemma lp_hasSum_sq {ι : Type a} (c : lp (fun _ : ι => K) 2) :
    HasSum (fun i => ‖c i‖ ^ 2) (‖c‖ ^ 2) := by
  simpa using lp.hasSum_norm (p := 2) (by norm_num) c

lemma column_pairing_bound {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) (x : H) :
    Summable (fun i => ‖b.repr x i‖ * ‖c i‖) ∧
      (∑' i, ‖b.repr x i‖ * ‖c i‖) ≤ ‖c‖ * ‖x‖ := by
  have hx := lp_hasSum_sq (b.repr x)
  have hc := lp_hasSum_sq c
  obtain ⟨C, _, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (norm_nonneg (b.repr x)) (norm_nonneg c) (fun i => norm_nonneg _)
    (fun i => norm_nonneg _) (by simpa using hx) (by simpa using hc)
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  simpa only [LinearIsometryEquiv.norm_map, mul_comm] using hC

lemma column_summable {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) (x : H) :
    Summable (fun i => (b.repr x i) • c i) := by
  apply Summable.of_norm
  simpa only [norm_smul] using (column_pairing_bound b c x).1

/-- Synthesis from arbitrary square-summable columns. -/
def columnOperator {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) : H →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, b.repr x i • c i
      map_add' := fun x y => by
        simp only [map_add, lp.coeFn_add, Pi.add_apply, add_smul]
        exact (column_summable b c x).tsum_add (column_summable b c y)
      map_smul' := fun r x => by
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (column_summable b c x).tsum_const_smul r }
    ‖c‖ (fun x => by
      change ‖∑' i, b.repr x i • c i‖ ≤ _
      calc
        _ ≤ ∑' i, ‖b.repr x i • c i‖ := norm_tsum_le_tsum_norm (by
          simpa only [norm_smul] using (column_pairing_bound b c x).1)
        _ = ∑' i, ‖b.repr x i‖ * ‖c i‖ := tsum_congr (fun i => norm_smul _ _)
        _ ≤ ‖c‖ * ‖x‖ := (column_pairing_bound b c x).2)

lemma columnOperator_apply {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) (x : H) :
    columnOperator b c x = ∑' i, b.repr x i • c i := rfl

@[simp] lemma columnOperator_basis {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) (i : ι) : columnOperator b c (b i) = c i := by
  classical
  simp [columnOperator_apply, b.repr_self, Pi.single_apply]

/-- Column synthesis is linear also in the columns. -/
def columnSynthesis {ι : Type a} (b : HilbertBasis ι 𝕜 H) :
    lp (fun _ : ι => K) 2 →ₗ[𝕜] (H →L[𝕜] K) where
  toFun := columnOperator b
  map_add' c d := by
    ext x
    simp only [columnOperator_apply, add_apply, lp.coeFn_add, Pi.add_apply, smul_add]
    exact (column_summable b c x).tsum_add (column_summable b d x)
  map_smul' r c := by
    ext x
    simp only [columnOperator_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_comm (b.repr x _) r]
    exact (column_summable b c x).tsum_const_smul r

lemma hilbertBasis_isBasis {ι : Type a} (b : HilbertBasis ι 𝕜 H) :
    HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) b := by
  apply (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 H ι b b.orthonormal).mpr
  exact b.dense_span

lemma columnOperator_finiteness {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) : IsHilbertSchmidt (columnOperator b c) := by
  apply (finiteness_in_basis _ b (hilbertBasis_isBasis b)).mpr
  simpa only [columnOperator_basis] using (lp_hasSum_sq c).summable

lemma columnOperator_norm {ι : Type a} (b : HilbertBasis ι 𝕜 H)
    (c : lp (fun _ : ι => K) 2) (h : IsHilbertSchmidt (columnOperator b c)) :
    ‖c‖ = hilbertSchmidtNorm ⟨columnOperator b c, h⟩ := by
  have hn := (normSquare_in_basis ⟨columnOperator b c, h⟩ b (hilbertBasis_isBasis b)).2
  simp only [columnOperator_basis] at hn
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  exact (lp_hasSum_sq c).tsum_eq.symm.trans hn.symm

lemma columnSynthesis_injective {ι : Type a} (b : HilbertBasis ι 𝕜 H) :
    Function.Injective (columnSynthesis (K := K) b) := by
  intro c d h
  apply lp.ext
  funext i
  have hi := congrArg (fun T : H →L[𝕜] K => T (b i)) h
  simpa only [columnSynthesis, LinearMap.coe_mk, AddHom.coe_mk, columnOperator_basis] using hi

lemma columnSynthesis_range {ι : Type a} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    (∃ c, columnSynthesis b c = T) ↔ IsHilbertSchmidt T := by
  constructor
  · rintro ⟨c, rfl⟩
    exact columnOperator_finiteness b c
  · intro hT
    have hs := (finiteness_in_basis T b (hilbertBasis_isBasis b)).mp hT
    let c : lp (fun _ : ι => K) 2 := ⟨fun i => T (b i), memℓp_gen (by simpa using hs)⟩
    refine ⟨c, ?_⟩
    ext x
    change (∑' i, b.repr x i • T (b i)) = T x
    simpa only [map_smul] using (T.hasSum (b.hasSum_repr x)).tsum_eq

/-- Extended Parseval on the product index, with no countability hypothesis. -/
lemma matrix_square_size {ι : Type a} {κ : Type b} (T : H →L[𝕜] K)
    (e : ι → H) (f : κ → K)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e)
    (hf : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) f) :
    (∑' p : ι × κ, ENNReal.ofReal (‖inner 𝕜 (f p.2) (T (e p.1))‖ ^ 2)) =
      hilbertSchmidtSquare T := by
  rw [ENNReal.tsum_prod' (f := fun p : ι × κ =>
    ENNReal.ofReal (‖inner 𝕜 (f p.2) (T (e p.1))‖ ^ 2))]
  exact (matrix_identity T e f hf).symm.trans (square_in_basis T e he).symm

lemma matrix_memℓp {ι : Type a} {κ : Type b} (T : H →L[𝕜] K)
    (hT : IsHilbertSchmidt T) (e : ι → H) (f : κ → K)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e)
    (hf : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) f) :
    Memℓp (fun p : ι × κ => inner 𝕜 (f p.2) (T (e p.1))) 2 := by
  have hfin : (∑' p : ι × κ, ENNReal.ofReal
      (‖inner 𝕜 (f p.2) (T (e p.1))‖ ^ 2)) ≠ ∞ := by
    rw [matrix_square_size T e f he hf]
    exact hT.ne
  have hs := ENNReal.summable_toReal hfin
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hs
  exact memℓp_gen (by simpa using hs)

/-- Matrix coefficients in any two bases give a linear map into a scalar
Hilbert sum. This is used to prove the inner product formula by isometry. -/
def matrixCoordinates {J : Type t} (b : HilbertBasis J 𝕜 H)
    {ι : Type a} {κ : Type b} (e : ι → H) (f : κ → K)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e)
    (hf : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) f) :
    lp (fun _ : J => K) 2 →ₗ[𝕜] lp (fun _ : ι × κ => 𝕜) 2 where
  toFun c := ⟨fun p => inner 𝕜 (f p.2) (columnOperator b c (e p.1)),
    matrix_memℓp _ (columnOperator_finiteness b c) e f he hf⟩
  map_add' c d := by
    apply lp.ext
    funext p
    change inner 𝕜 (f p.2) (columnSynthesis b (c + d) (e p.1)) = _
    rw [map_add, add_apply, inner_add_right]
    rfl
  map_smul' r c := by
    apply lp.ext
    funext p
    change inner 𝕜 (f p.2) (columnSynthesis b (r • c) (e p.1)) = _
    rw [map_smul, smul_apply, inner_smul_right]
    rfl

lemma matrixCoordinates_norm {J : Type t} (b : HilbertBasis J 𝕜 H)
    {ι : Type a} {κ : Type b} (e : ι → H) (f : κ → K)
    (he : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) e)
    (hf : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) f)
    (c : lp (fun _ : J => K) 2) : ‖matrixCoordinates b e f he hf c‖ = ‖c‖ := by
  let M := matrixCoordinates b e f he hf c
  have hsq := lp_hasSum_sq M
  have hn : ENNReal.ofReal (‖M‖ ^ 2) = hilbertSchmidtSquare (columnOperator b c) := by
    rw [← hsq.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hsq.summable]
    exact matrix_square_size _ e f he hf
  have hn' := congrArg ENNReal.toReal hn
  rw [ENNReal.toReal_ofReal (sq_nonneg _),
    ← square_of_norm ⟨columnOperator b c, columnOperator_finiteness b c⟩,
    ← columnOperator_norm b c (columnOperator_finiteness b c)] at hn'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn'

theorem complete_hilbert_realization : Spec.CompleteHilbertRealization.{u, v, w, a, b} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  obtain ⟨R, b, _⟩ := exists_hilbertBasis 𝕜 H
  refine ⟨lp (fun _ : R => K) 2, inferInstance, inferInstance, inferInstance,
    columnSynthesis b, columnSynthesis_injective b, columnSynthesis_range b,
    columnOperator_norm b, ?_⟩
  intro ι κ e f he hf x y
  let M := matrixCoordinates b e f he hf
  have hs := lp.summable_inner (𝕜 := 𝕜) (M x) (M y)
  have hi := (LinearMap.norm_map_iff_inner_map_map M).mp
    (matrixCoordinates_norm b e f he hf) x y
  refine ⟨?_, ?_⟩
  · simpa only [M, matrixCoordinates, columnSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      RCLike.inner_apply', ← RCLike.star_def] using hs
  · calc
      inner 𝕜 x y = inner 𝕜 (M x) (M y) := hi.symm
      _ = _ := by
        rw [lp.inner_eq_tsum]
        apply tsum_congr
        intro p
        exact RCLike.inner_apply' _ _

end
end ExpandedFA.TraceIdeals.HilbertSchmidtBasis
