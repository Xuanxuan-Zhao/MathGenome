import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceNormIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
set_option maxHeartbeats 800000
universe u v w v₀ w₀ z
namespace ExpandedFA.TraceIdeals.TraceNormIdeal
open TraceClassDefinitions
open CompactSpectral
open Filter
open scoped Topology
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

lemma singular_nonneg (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) (n : ℕ) :
    0 ≤ TraceClassDefinitions.Spec.singularSequence T n :=
  (SingularApproximation.singular_sequence_properties 𝕜 H K T hT).1 (n + 1) (Nat.succ_pos n)

lemma traceNorm_nonneg (T : H →L[𝕜] K) (hT : IsTraceClass T) : 0 ≤ traceNorm T :=
  tsum_nonneg (singular_nonneg T hT.1)

/-- Finite orthonormal pairs satisfy the two Bessel bounds used by the trace
norm; the vectors in the two ambient spaces need not come from full bases. -/
lemma sum_inner_mul_le_one {ι : Type z} [Fintype ι]
    (a : ι → K) (b : ι → H) (ha : Orthonormal 𝕜 a) (hb : Orthonormal 𝕜 b)
    (x : K) (y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ i, ‖inner 𝕜 y (b i) * inner 𝕜 (a i) x‖ ≤ 1 := by
  have hp (i : ι) : ‖inner 𝕜 y (b i) * inner 𝕜 (a i) x‖ ≤
      (‖inner 𝕜 (b i) y‖ ^ 2 + ‖inner 𝕜 (a i) x‖ ^ 2) / 2 := by
    rw [norm_mul, norm_inner_symm y]
    nlinarith [sq_nonneg (‖inner 𝕜 (b i) y‖ - ‖inner 𝕜 (a i) x‖)]
  calc
    _ ≤ ∑ i, (‖inner 𝕜 (b i) y‖ ^ 2 + ‖inner 𝕜 (a i) x‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = ((∑ i, ‖inner 𝕜 (b i) y‖ ^ 2) + ∑ i, ‖inner 𝕜 (a i) x‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ 1 := by
      have h₁ := hb.sum_inner_products_le (s := Finset.univ) y
      have h₂ := ha.sum_inner_products_le (s := Finset.univ) x
      rw [hy] at h₁
      rw [hx] at h₂
      nlinarith

lemma finite_family_bound_of_expansion {J : Type*} {ι : Type*} [Fintype ι]
    (T : H →L[𝕜] K) (c : J → ℝ) (u : J → K) (v : J → H)
    (hc : ∀ j, 0 ≤ c j) (hsum : Summable c)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hexp : ∀ x, HasSum (fun j => ((c j : 𝕜) * inner 𝕜 (v j) x) • u j) (T x))
    (a : ι → K) (b : ι → H) (ha : Orthonormal 𝕜 a) (hb : Orthonormal 𝕜 b) :
    ∑ i, ‖inner 𝕜 (a i) (T (b i))‖ ≤ ∑' j, c j := by
  let d : J → ι → 𝕜 := fun j i => (c j : 𝕜) *
    (inner 𝕜 (v j) (b i) * inner 𝕜 (a i) (u j))
  have hd (j : J) (i : ι) : ‖d j i‖ ≤ c j := by
    have h₁ := norm_inner_le_norm (𝕜 := 𝕜) (v j) (b i)
    have h₂ := norm_inner_le_norm (𝕜 := 𝕜) (a i) (u j)
    rw [hv j, hb.norm_eq_one i, one_mul] at h₁
    rw [ha.norm_eq_one i, hu j, one_mul] at h₂
    simp only [d, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hc j)]
    exact mul_le_of_le_one_right (hc j)
      ((mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hs (i : ι) : Summable (fun j => ‖d j i‖) :=
    hsum.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hd j i)
  have he (i : ι) : (∑' j, d j i) = inner 𝕜 (a i) (T (b i)) := by
    have hh := (hexp (b i)).mapL (innerSL 𝕜 (a i))
    simp only [innerSL_apply_apply, inner_smul_right] at hh
    convert hh.tsum_eq using 1
    congr 1
    funext j
    dsimp [d]
    ring
  calc
    _ ≤ ∑ i, ∑' j, ‖d j i‖ := Finset.sum_le_sum (fun i _ => by
      rw [← he i]
      exact norm_tsum_le_tsum_norm (hs i))
    _ = ∑' j, ∑ i, ‖d j i‖ := (Summable.tsum_finsetSum (fun i _ => hs i)).symm
    _ ≤ ∑' j, c j := by
      apply Summable.tsum_le_tsum _ (summable_sum (fun i _ => hs i)) hsum
      intro j
      simp only [d, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hc j),
        ← Finset.mul_sum]
      apply mul_le_of_le_one_right (hc j)
      simpa only [norm_mul] using
        sum_inner_mul_le_one a b ha hb _ _ (hu j) (hv j)

lemma finite_family_bound {ι : Type*} [Fintype ι]
    (T : H →L[𝕜] K) (hT : IsTraceClass T)
    (a : ι → K) (b : ι → H) (ha : Orthonormal 𝕜 a) (hb : Orthonormal 𝕜 b) :
    ∑ i, ‖inner 𝕜 (a i) (T (b i))‖ ≤ traceNorm T := by
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT.1
  obtain ⟨hσ, hn⟩ := singularSystem_sum 𝕜 H K T hT S
  exact (finite_family_bound_of_expansion T S.sigma S.leftVector S.rightVector
    (fun j => (S.positive j).le) hσ S.left_orthonormal.norm_eq_one
    S.right_orthonormal.norm_eq_one S.expansion a b ha hb).trans_eq hn

/-- Summability of any singular expansion implies the original canonical
trace-class condition; no new definition of trace class is introduced. -/
lemma traceClass_of_singular_summable (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (hσ : Summable S.sigma) :
    IsTraceClass T := by
  let e : S.Index ≃ positiveIndices T := singularIndexEquiv T hT S
  have hs : Summable (fun j =>
      SingularApproximation.Spec.SingularValueValue T (e j).val) :=
    hσ.congr (fun j => (singularIndexEquiv_value T hT S j).symm)
  have hsub : Summable (fun n : positiveIndices T =>
      SingularApproximation.Spec.SingularValueValue T n.val) :=
    (e.summable_iff (f := fun n : positiveIndices T =>
      SingularApproximation.Spec.SingularValueValue T n.val)).mp hs
  have hf : Summable (SingularApproximation.Spec.SingularValueValue T) :=
    ((hasSum_subtype_iff_of_support_subset (positiveIndices_support T hT)).mp
      hsub.hasSum).summable
  exact ⟨hT, (summable_nat_add_iff 1).mpr hf⟩

lemma traceClass_of_finite_family_bound (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (C : ℝ)
    (h : ∀ (n : ℕ) (a : Fin n → K) (b : Fin n → H),
      Orthonormal 𝕜 a → Orthonormal 𝕜 b →
        ∑ i, ‖inner 𝕜 (a i) (T (b i))‖ ≤ C) :
    IsTraceClass T ∧ traceNorm T ≤ C := by
  classical
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  have hsum (s : Finset S.Index) : ∑ j ∈ s, S.sigma j ≤ C := by
    let e := s.equivFin.symm
    let a : Fin s.card → K := fun i => S.leftVector (e i).val
    let b : Fin s.card → H := fun i => S.rightVector (e i).val
    have hinj : Function.Injective (fun i => (e i).val) :=
      Subtype.val_injective.comp e.injective
    have ha : Orthonormal 𝕜 a := S.left_orthonormal.comp _ hinj
    have hb : Orthonormal 𝕜 b := S.right_orthonormal.comp _ hinj
    have he (i : Fin s.card) : ‖inner 𝕜 (a i) (T (b i))‖ = S.sigma (e i).val := by
      simp only [a, b, S.map_right, inner_smul_right,
        (orthonormal_iff_ite.mp S.left_orthonormal), mul_one, RCLike.norm_ofReal, ite_true,
        abs_of_pos (S.positive _)]
    have hh := h s.card a b ha hb
    simp only [he] at hh
    rw [show (∑ x, S.sigma (e x).val) = ∑ j : s, S.sigma j.val from
      e.sum_comp (fun j : s => S.sigma j.val)] at hh
    simpa only [Finset.sum_coe_sort] using hh
  have hσ := summable_of_sum_le (fun j => (S.positive j).le) hsum
  have ht := traceClass_of_singular_summable T hT S hσ
  refine ⟨ht, ?_⟩
  change TraceClassDefinitions.Spec.TraceNormValue T ≤ C
  rw [← (singularSystem_sum 𝕜 H K T ht S).2]
  exact hσ.tsum_le_of_sum_le hsum

theorem finite_family_characterization :
    Spec.FiniteFamilyCharacterization.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  intro T hT C _
  constructor
  · rintro ⟨hT, hC⟩ n a b ha hb
    exact (finite_family_bound T hT a b ha hb).trans hC
  · exact traceClass_of_finite_family_bound T hT C

lemma opNorm_le_traceNorm (T : H →L[𝕜] K) (hT : IsTraceClass T) : ‖T‖ ≤ traceNorm T := by
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT.1
  obtain ⟨hσ, hn⟩ := singularSystem_sum 𝕜 H K T hT S
  apply T.opNorm_le_bound (traceNorm_nonneg T hT)
  intro x
  have hp (j : S.Index) :
      ‖((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) • S.leftVector j‖ ≤
        S.sigma j * ‖x‖ := by
    simp only [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive j),
      S.left_orthonormal.norm_eq_one, mul_one]
    apply mul_le_mul_of_nonneg_left _ (S.positive j).le
    simpa only [S.right_orthonormal.norm_eq_one, one_mul] using
      norm_inner_le_norm (𝕜 := 𝕜) (S.rightVector j) x
  have hs := hσ.mul_right ‖x‖
  calc
    ‖T x‖ ≤ ∑' j, S.sigma j * ‖x‖ := (S.expansion x).norm_le_of_bounded hs.hasSum hp
    _ = traceNorm T * ‖x‖ := by rw [tsum_mul_right, hn]

lemma compact_iff_native (T : H →L[𝕜] K) :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap ↔ IsCompactOperator T :=
  Compactness.compact_iff_isCompactOperator T.toLinearMap

lemma traceClass_zero : IsTraceClass (0 : H →L[𝕜] K) := by
  have hc := (compact_iff_native (0 : H →L[𝕜] K)).mpr isCompactOperator_zero
  have hv := (SingularApproximation.singular_rank_cases 𝕜 H K 0 hc).2.2 rfl
  refine ⟨hc, ?_⟩
  change Summable (fun n => SingularApproximation.Spec.SingularValueValue
    (0 : H →L[𝕜] K) (n + 1))
  simp only [hv _ (Nat.succ_pos _)]
  exact summable_zero

@[simp] lemma traceNorm_zero : traceNorm (0 : H →L[𝕜] K) = 0 := by
  have hv := (SingularApproximation.singular_rank_cases 𝕜 H K 0 traceClass_zero.1).2.2 rfl
  change (∑' n, SingularApproximation.Spec.SingularValueValue (0 : H →L[𝕜] K) (n + 1)) = 0
  simp only [hv _ (Nat.succ_pos _), tsum_zero]

lemma traceClass_add (S T : H →L[𝕜] K) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) ∧ traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  have hc := (compact_iff_native (S + T)).mpr
    (((compact_iff_native S).mp hS.1).add ((compact_iff_native T).mp hT.1))
  apply traceClass_of_finite_family_bound (S + T) hc (traceNorm S + traceNorm T)
  intro n a b ha hb
  calc
    _ ≤ ∑ i, (‖inner 𝕜 (a i) (S (b i))‖ + ‖inner 𝕜 (a i) (T (b i))‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [add_apply, inner_add_right] using
        norm_add_le (inner 𝕜 (a i) (S (b i))) (inner 𝕜 (a i) (T (b i)))
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (finite_family_bound S hS a b ha hb)
      (finite_family_bound T hT a b ha hb)

lemma traceClass_smul_le (c : 𝕜) (T : H →L[𝕜] K) (hT : IsTraceClass T) :
    IsTraceClass (c • T) ∧ traceNorm (c • T) ≤ ‖c‖ * traceNorm T := by
  have hc := (compact_iff_native (c • T)).mpr (((compact_iff_native T).mp hT.1).smul c)
  apply traceClass_of_finite_family_bound (c • T) hc (‖c‖ * traceNorm T)
  intro n a b ha hb
  simp only [smul_apply, inner_smul_right, norm_mul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (finite_family_bound T hT a b ha hb) (norm_nonneg c)

lemma traceClass_smul (c : 𝕜) (T : H →L[𝕜] K) (hT : IsTraceClass T) :
    IsTraceClass (c • T) ∧ traceNorm (c • T) = ‖c‖ * traceNorm T := by
  obtain ⟨ht, hle⟩ := traceClass_smul_le c T hT
  refine ⟨ht, le_antisymm hle ?_⟩
  by_cases hc : c = 0
  · simp [hc]
  have hrev := (traceClass_smul_le c⁻¹ (c • T) ht).2
  rw [inv_smul_smul₀ hc] at hrev
  have hm := mul_le_mul_of_nonneg_left hrev (norm_nonneg c)
  rwa [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul] at hm

lemma traceClass_neg (T : H →L[𝕜] K) (hT : IsTraceClass T) :
    IsTraceClass (-T) ∧ traceNorm (-T) = traceNorm T := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using traceClass_smul (-1 : 𝕜) T hT

lemma traceClass_sub (S T : H →L[𝕜] K) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S - T) := by
  simpa only [sub_eq_add_neg] using (traceClass_add S (-T) hS (traceClass_neg T hT).1).1

lemma traceNorm_eq_zero_iff (T : H →L[𝕜] K) (hT : IsTraceClass T) :
    traceNorm T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ opNorm_le_traceNorm T hT) (norm_nonneg T))
  · rintro rfl
    exact traceNorm_zero

theorem normed_ideal_axioms : Spec.NormedIdealAxioms.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  exact ⟨traceClass_zero, traceNorm_zero,
    fun T hT => ⟨traceNorm_nonneg T hT, traceNorm_eq_zero_iff T hT, opNorm_le_traceNorm T hT⟩,
    traceClass_add, traceClass_smul⟩

theorem two_sided_ideal : Spec.TwoSidedIdeal.{u,v,w,v₀,w₀} := by
  intro 𝕜 _ H K H₀ K₀ _ _ _ _ _ _ _ _ _ _ _ _ T A B hT
  let U := A.comp (T.comp B)
  have hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue U.toLinearMap :=
    (compact_iff_native U).mpr ((((compact_iff_native T).mp hT.1).comp_clm B).clm_comp A)
  have hle (n : ℕ) : TraceClassDefinitions.Spec.singularSequence U n ≤
      ‖A‖ * ‖B‖ * TraceClassDefinitions.Spec.singularSequence T n :=
    SingularApproximation.singularValue_ideal 𝕜 H K H₀ K₀ T A B hT.1 (n + 1) (Nat.succ_pos n)
  have hs := hT.2.mul_left (‖A‖ * ‖B‖)
  have hu := hs.of_nonneg_of_le (singular_nonneg U hc) hle
  refine ⟨⟨hc, hu⟩, ?_⟩
  calc
    traceNorm U ≤ ∑' n, ‖A‖ * ‖B‖ * TraceClassDefinitions.Spec.singularSequence T n :=
      hu.tsum_le_tsum hle hs
    _ = ‖A‖ * traceNorm T * ‖B‖ := by
      rw [tsum_mul_left]
      change ‖A‖ * ‖B‖ * traceNorm T = _
      ring

/-- Finite matrix tests pass through an operator-norm limit. This is the
lower semicontinuity argument that upgrades the operator limit to a trace limit. -/
lemma traceClass_of_tendsto_bounded (T : ℕ → H →L[𝕜] K) (L : H →L[𝕜] K)
    (hL : Compactness.DefinitionsSpec.IsCompactLinearMapValue L.toLinearMap)
    (hconv : Tendsto T atTop (𝓝 L)) (C : ℝ)
    (hT : ∀ᶠ n in atTop, IsTraceClass (T n) ∧ traceNorm (T n) ≤ C) :
    IsTraceClass L ∧ traceNorm L ≤ C := by
  apply traceClass_of_finite_family_bound L hL C
  intro n a b ha hb
  have ht : Tendsto (fun m => ∑ i, ‖inner 𝕜 (a i) (T m (b i))‖) atTop
      (𝓝 (∑ i, ‖inner 𝕜 (a i) (L (b i))‖)) := by
    apply tendsto_finsetSum
    intro i _
    exact (tendsto_const_nhds.inner
      (((ContinuousLinearMap.apply 𝕜 K (b i)).continuous.tendsto L).comp hconv)).norm
  apply le_of_tendsto ht
  filter_upwards [hT] with m hm
  exact (finite_family_bound (T m) hm.1 a b ha hb).trans hm.2

theorem trace_norm_complete : Spec.TraceNormComplete.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  intro T hT hC
  have hOp : CauchySeq T := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact (opNorm_le_traceNorm _ (traceClass_sub _ _ (hT m) (hT n))).trans_lt (hN m hm n hn)
  obtain ⟨L, hconv⟩ := cauchySeq_tendsto_of_complete hOp
  have hcompact : Compactness.DefinitionsSpec.IsCompactLinearMapValue L.toLinearMap :=
    (compact_iff_native L).mpr (isCompactOperator_of_tendsto hconv
      (Eventually.of_forall (fun n => (compact_iff_native (T n)).mp (hT n).1)))
  have hdiff (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
      IsTraceClass (T n - L) ∧ traceNorm (T n - L) ≤ ε / 2 := by
    obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hdcompact := (compact_iff_native (T n - L)).mpr
      (((compact_iff_native (T n)).mp (hT n).1).sub ((compact_iff_native L).mp hcompact))
    apply traceClass_of_tendsto_bounded (fun m => T n - T m) (T n - L)
      hdcompact (tendsto_const_nhds.sub hconv) (ε / 2)
    filter_upwards [eventually_ge_atTop N] with m hm
    exact ⟨traceClass_sub _ _ (hT n) (hT m), (hN n hn m hm).le⟩
  have hL : IsTraceClass L := by
    obtain ⟨N, hN⟩ := hdiff 1 zero_lt_one
    have hh := traceClass_sub (T N) (T N - L) (hT N) (hN N le_rfl).1
    simpa only [sub_sub_cancel] using hh
  refine ⟨L, hL, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hdiff ε hε
  exact ⟨N, fun n hn => (hN n hn).2.trans_lt (half_lt_self hε)⟩

lemma finite_rank_traceClass (F : H →L[𝕜] K) [FiniteDimensional 𝕜 F.range] :
    IsTraceClass F := by
  have hn : IsCompactOperator F := by
    have hh := (isCompactOperator_of_locallyCompactSpace_dom F.rangeRestrict).clm_comp
      F.range.subtypeL
    exact hh
  have hc := (compact_iff_native F).mpr hn
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K F hc
  letI : Finite S.Index := S.finite_rank inferInstance
  exact traceClass_of_singular_summable F hc S Summable.of_finite

lemma truncation_finite_rank (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index) :
    FiniteDimensional 𝕜 (SingularApproximation.truncation T S s).range := by
  apply Module.rank_lt_aleph0_iff.mp
  exact (SingularApproximation.truncation_rank_le 𝕜 H K T S s).trans_lt
    (Cardinal.natCast_lt_aleph0 (n := s.card))

/-- The trace norm of a singular tail is bounded by the scalar tail. Unlike
an operator-norm estimate, this bound proves density for the stronger norm. -/
lemma truncation_trace_tail_bound (T : H →L[𝕜] K) (hT : IsTraceClass T)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index) :
    IsTraceClass (SingularApproximation.truncation T S s) ∧
    IsTraceClass (T - SingularApproximation.truncation T S s) ∧
    traceNorm (T - SingularApproximation.truncation T S s) ≤
      ∑' j : {j // j ∉ s}, S.sigma j.val := by
  classical
  let F := SingularApproximation.truncation T S s
  letI : FiniteDimensional 𝕜 F.range := truncation_finite_rank T S s
  have hF : IsTraceClass F := finite_rank_traceClass F
  have hR := traceClass_sub T F hT hF
  refine ⟨hF, hR, ?_⟩
  apply (traceClass_of_finite_family_bound (T - F) hR.1
    (∑' j : {j // j ∉ s}, S.sigma j.val) ?_).2
  intro n a b ha hb
  apply finite_family_bound_of_expansion (T - F)
    (fun j : {j // j ∉ s} => S.sigma j.val)
    (fun j => S.leftVector j.val) (fun j => S.rightVector j.val)
    (fun j => (S.positive j.val).le)
    ((singularSystem_sum 𝕜 H K T hT S).1.subtype _)
    (fun j => S.left_orthonormal.norm_eq_one j.val)
    (fun j => S.right_orthonormal.norm_eq_one j.val) _ a b ha hb
  intro x
  have hh := (s.hasSum_iff_compl).mp (S.expansion x)
  simpa only [F, SingularApproximation.truncation_apply, sub_apply] using hh

theorem finite_rank_dense : Spec.FiniteRankDense.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  intro T hT ε hε
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT.1
  have htend : Tendsto (fun s : Finset S.Index =>
      ∑' j : {j // j ∉ s}, S.sigma j.val) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero S.sigma
  obtain ⟨s, hs⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  obtain ⟨hF, hR, hbound⟩ := truncation_trace_tail_bound T hT S s
  exact ⟨SingularApproximation.truncation T S s, truncation_finite_rank T S s,
    hF, hR, hbound.trans_lt hs⟩

theorem finite_rank_trace_class : Spec.FiniteRankTraceClass.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ F hF
  letI := hF
  exact finite_rank_traceClass F

end ExpandedFA.TraceIdeals.TraceNormIdeal
