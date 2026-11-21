import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularExpansion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.Interval.Set.Nat

noncomputable section
universe u v w v₀ w₀
namespace ExpandedFA.CompactSpectral.SingularApproximation

section Normed
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [NormedSpace 𝕜 H] [NormedSpace 𝕜 K]

/-- The n-th approximation number, with n ≥ 1 and rank strictly less than n. -/
def approximationNumber (T : H →L[𝕜] K) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ F : H →L[𝕜] K,
    F.toLinearMap.rank < (n : Cardinal) ∧ r = ‖T - F‖}

private lemma errors_bddBelow (T : H →L[𝕜] K) (n : ℕ) :
    BddBelow {r : ℝ | ∃ F : H →L[𝕜] K,
      F.toLinearMap.rank < (n : Cardinal) ∧ r = ‖T - F‖} := by
  refine ⟨0, ?_⟩
  rintro r ⟨F, _, rfl⟩
  exact norm_nonneg _

private lemma errors_nonempty (T : H →L[𝕜] K) {n : ℕ} (hn : 0 < n) :
    {r : ℝ | ∃ F : H →L[𝕜] K,
      F.toLinearMap.rank < (n : Cardinal) ∧ r = ‖T - F‖}.Nonempty := by
  refine ⟨‖T - 0‖, 0, ?_, rfl⟩
  simpa using (show (0 : Cardinal.{w}) < (n : Cardinal.{w}) from Nat.cast_pos.mpr hn)

theorem approximationNumber_nonnegative : Spec.Nonnegative.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ T n hn
  apply le_csInf (errors_nonempty T hn)
  rintro r ⟨F, _, rfl⟩
  exact norm_nonneg _

theorem approximationNumber_le_error : Spec.LowerBound.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ T F n hF
  exact csInf_le (errors_bddBelow T n) ⟨F, hF, rfl⟩

theorem le_approximationNumber : Spec.GreatestLowerBound.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ T n hn c hc
  apply le_csInf (errors_nonempty T hn)
  rintro r ⟨F, hF, rfl⟩
  exact hc F hF

/-- Rank control works across unrelated universe levels. -/
lemma rank_comp_lt {H₀ : Type v₀} {K₀ : Type w₀}
    [NormedAddCommGroup H₀] [NormedAddCommGroup K₀]
    [NormedSpace 𝕜 H₀] [NormedSpace 𝕜 K₀]
    (F : H →L[𝕜] K) (A : K →L[𝕜] K₀) (B : H₀ →L[𝕜] H) {n : ℕ}
    (hF : F.toLinearMap.rank < (n : Cardinal)) :
    (A.comp (F.comp B)).toLinearMap.rank < (n : Cardinal) := by
  have hpre : (F.comp B).toLinearMap.rank < (n : Cardinal) :=
    lt_of_le_of_lt (LinearMap.rank_comp_le_left B.toLinearMap F.toLinearMap) hF
  have h := LinearMap.lift_rank_comp_le_right (F.comp B).toLinearMap A.toLinearMap
  have hpre' := Cardinal.lift_lt.mpr hpre
  have hh := lt_of_le_of_lt h hpre'
  apply Cardinal.lift_lt.mp
  simpa only [Cardinal.lift_natCast, ContinuousLinearMap.toLinearMap_comp] using hh

lemma norm_comp_sub_le {H₀ : Type v₀} {K₀ : Type w₀}
    [NormedAddCommGroup H₀] [NormedAddCommGroup K₀]
    [NormedSpace 𝕜 H₀] [NormedSpace 𝕜 K₀]
    (T F : H →L[𝕜] K) (A : K →L[𝕜] K₀) (B : H₀ →L[𝕜] H) :
    ‖A.comp (T.comp B) - A.comp (F.comp B)‖ ≤ ‖A‖ * ‖B‖ * ‖T - F‖ := by
  have heq : A.comp (T.comp B) - A.comp (F.comp B) = A.comp ((T - F).comp B) := by
    ext x
    simp
  rw [heq]
  calc
    ‖A.comp ((T - F).comp B)‖ ≤ ‖A‖ * ‖(T - F).comp B‖ := A.opNorm_comp_le _
    _ ≤ ‖A‖ * (‖T - F‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_left ((T - F).opNorm_comp_le B) (norm_nonneg _)
    _ = ‖A‖ * ‖B‖ * ‖T - F‖ := by ring

/-- The ideal property for approximation numbers requires no spectral theorem. -/
theorem approximationNumber_ideal : Spec.IdealInequality.{u, v, w, v₀, w₀} := by
  intro 𝕜 _ H K H₀ K₀ _ _ _ _ _ _ _ _ T A B n hn
  let c := ‖A‖ * ‖B‖
  have hc : 0 ≤ c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb (F : H →L[𝕜] K) (hF : F.toLinearMap.rank < (n : Cardinal)) :
      approximationNumber (A.comp (T.comp B)) n ≤ c * ‖T - F‖ :=
    (approximationNumber_le_error 𝕜 H₀ K₀ _ _ n (rank_comp_lt F A B hF)).trans
      (norm_comp_sub_le T F A B)
  change approximationNumber (A.comp (T.comp B)) n ≤ c * approximationNumber T n
  rcases eq_or_lt_of_le hc with hz | hp
  · have hzero := hb 0 (by
      simpa using (show (0 : Cardinal.{w}) < (n : Cardinal.{w}) from Nat.cast_pos.mpr hn))
    simpa only [← hz, zero_mul] using hzero
  · have hh : approximationNumber (A.comp (T.comp B)) n / c ≤ approximationNumber T n := by
      apply le_approximationNumber 𝕜 H K T n hn
      intro F hF
      exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hb F hF)
    exact (div_le_iff₀ hp).mp hh |>.trans_eq (mul_comm _ _)

theorem approximationNumber_rank_vanishing : Spec.RankVanishing.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ T n hn hT
  apply le_antisymm
  · simpa using approximationNumber_le_error 𝕜 H K T T n hT
  · exact approximationNumber_nonnegative 𝕜 H K T n hn

lemma approximationNumber_antitone (T : H →L[𝕜] K) {n m : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) : approximationNumber T m ≤ approximationNumber T n := by
  apply le_approximationNumber 𝕜 H K T n hn
  intro F hF
  exact approximationNumber_le_error 𝕜 H K T F m (hF.trans_le (by exact_mod_cast hnm))

end Normed

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- The stored right vectors are Gram eigenvectors with eigenvalue σ². -/
lemma gram_right (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (j : S.Index) :
    ContinuousLinearMap.adjoint T (T (S.rightVector j)) =
      ((S.sigma j ^ 2 : ℝ) : 𝕜) • S.rightVector j := by
  simp only [S.map_right, map_smul, S.adjoint_left, smul_smul, pow_two, RCLike.ofReal_mul]

lemma singular_value_le_norm (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (j : S.Index) :
    S.sigma j ≤ ‖T‖ := by
  have h := T.le_opNorm (S.rightVector j)
  simpa only [S.map_right, norm_smul, RCLike.norm_ofReal, abs_of_pos (S.positive j),
    S.right_orthonormal.norm_eq_one j, S.left_orthonormal.norm_eq_one j, mul_one] using h

/-- Truncation to any finite part of the positive singular system. -/
def truncation (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index) : H →L[𝕜] K :=
  ∑ j ∈ s, (innerSL 𝕜 (S.rightVector j)).smulRight ((S.sigma j : 𝕜) • S.leftVector j)

lemma truncation_apply (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index) (x : H) :
    truncation T S s x =
      ∑ j ∈ s, ((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) • S.leftVector j := by
  simp only [truncation, sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_smul, mul_comm]

theorem truncation_rank_le : Spec.TruncationRank.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  classical
  intro T S s
  have hr : (truncation T S s).range ≤ Submodule.span 𝕜 (s.image S.leftVector : Set K) := by
    rintro _ ⟨x, rfl⟩
    change truncation T S s x ∈ _
    rw [truncation_apply]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  exact (Submodule.rank_mono hr).trans
    ((rank_span_finset_le (s.image S.leftVector)).trans
      (by exact_mod_cast Finset.card_image_le))

theorem truncation_on_right : Spec.TruncationOnRight.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  classical
  intro T S s j
  change truncation T S s (S.rightVector j) = _
  rw [truncation_apply]
  simp only [orthonormal_iff_ite.mp S.right_orthonormal]
  simp [S.map_right]

theorem omitted_value_le_error : Spec.OmittedValueLowerBound.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T S s j hj
  have h := (T - truncation T S s).le_opNorm (S.rightVector j)
  have he := truncation_on_right 𝕜 H K T S s j
  change truncation T S s (S.rightVector j) = _ at he
  rw [ite_eq_right hj] at he
  simp only [sub_apply, he, sub_zero, S.map_right,
    norm_smul, RCLike.norm_ofReal, abs_of_pos (S.positive j),
    S.right_orthonormal.norm_eq_one j, S.left_orthonormal.norm_eq_one j, mul_one] at h
  exact h

/-- Pythagoras for scalar combinations of an orthonormal family. -/
lemma norm_sum_orthonormal_sq {J : Type*} (e : J → K)
    (he : Orthonormal 𝕜 e) (a : J → 𝕜) (s : Finset J) :
    ‖∑ j ∈ s, a j • e j‖ ^ 2 = ∑ j ∈ s, ‖a j‖ ^ 2 := by
  have h := congrArg RCLike.re (he.inner_sum a a s)
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_re, map_sum,
    RCLike.conj_mul, ← RCLike.ofReal_pow] using h

/-- Uniform bound for a finite singular sum whose coefficients are bounded by `c`. -/
lemma norm_singular_sum_le (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (q : Finset S.Index) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ j ∈ q, S.sigma j ≤ c) (x : H) :
    ‖∑ j ∈ q, ((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) • S.leftVector j‖ ≤
      c * ‖x‖ := by
  have hsq : ‖∑ j ∈ q,
      ((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) • S.leftVector j‖ ^ 2 ≤
      (c * ‖x‖) ^ 2 := by
    rw [norm_sum_orthonormal_sq _ S.left_orthonormal]
    calc
      _ ≤ ∑ j ∈ q, c ^ 2 * ‖inner 𝕜 (S.rightVector j) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive j), mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (le_of_lt (S.positive j)) (hq j hj) 2) (sq_nonneg _)
      _ = c ^ 2 * ∑ j ∈ q, ‖inner 𝕜 (S.rightVector j) x‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ c ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (S.right_orthonormal.sum_inner_products_le x) (sq_nonneg _)
      _ = (c * ‖x‖) ^ 2 := (mul_pow _ _ _).symm
  nlinarith [norm_nonneg (∑ j ∈ q,
    ((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) • S.leftVector j),
    mul_nonneg hc (norm_nonneg x)]

/-- The truncation error is bounded by any bound on the omitted singular values. -/
lemma truncation_error_le (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (s : Finset S.Index) {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ j, j ∉ s → S.sigma j ≤ c) :
    ‖T - truncation T S s‖ ≤ c := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have ht := ((S.expansion x).sub_const (truncation T S s x)).norm
  apply le_of_tendsto ht
  filter_upwards [Filter.eventually_ge_atTop s] with q hq
  change ‖(∑ j ∈ q, ((S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) x) •
    S.leftVector j) - truncation T S s x‖ ≤ c * ‖x‖
  rw [truncation_apply, ← Finset.sum_sdiff hq, add_sub_cancel_right]
  exact norm_singular_sum_le T S (q \ s) hc (fun j hj => hs j (Finset.mem_sdiff.mp hj).2) x

/-- On a span of right vectors with singular values at least `c`, `T` expands
norms by at least `c`. The indexing map permits finite subfamilies. -/
lemma norm_map_sum_ge (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    {J : Type*} (e : J → S.Index) (he : Function.Injective e)
    (q : Finset J) (a : J → 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ j ∈ q, c ≤ S.sigma (e j)) :
    c * ‖∑ j ∈ q, a j • S.rightVector (e j)‖ ≤
      ‖T (∑ j ∈ q, a j • S.rightVector (e j))‖ := by
  have hr : Orthonormal 𝕜 (fun j => S.rightVector (e j)) := S.right_orthonormal.comp e he
  have hl : Orthonormal 𝕜 (fun j => S.leftVector (e j)) := S.left_orthonormal.comp e he
  have hm : T (∑ j ∈ q, a j • S.rightVector (e j)) =
      ∑ j ∈ q, (a j * (S.sigma (e j) : 𝕜)) • S.leftVector (e j) := by
    simp only [map_sum, map_smul, S.map_right, smul_smul]
  have hsq : (c * ‖∑ j ∈ q, a j • S.rightVector (e j)‖) ^ 2 ≤
      ‖T (∑ j ∈ q, a j • S.rightVector (e j))‖ ^ 2 := by
    rw [mul_pow, norm_sum_orthonormal_sq _ hr, hm, norm_sum_orthonormal_sq _ hl,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive (e j)), mul_pow, mul_comm (c ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc (hq j hj) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (T (∑ j ∈ q, a j • S.rightVector (e j))),
    mul_nonneg hc (norm_nonneg (∑ j ∈ q, a j • S.rightVector (e j)))]

/-- A rank smaller than the number of selected singular directions forces the
approximation error to be at least their common lower bound. -/
lemma error_ge_of_rank_lt (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    (q : Finset S.Index) (F : H →L[𝕜] K) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ j ∈ q, c ≤ S.sigma j)
    (hF : F.toLinearMap.rank < (q.card : Cardinal)) : c ≤ ‖T - F‖ := by
  classical
  by_contra h
  have hlt : ‖T - F‖ < c := lt_of_not_ge h
  have hli : LinearIndependent 𝕜 (fun j : q => F (S.rightVector j)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    let x : H := ∑ j : q, a j • S.rightVector j
    have hxF : F x = 0 := by simpa only [x, map_sum, map_smul] using ha
    have hxge := norm_map_sum_ge T S (fun j : q => (j : S.Index)) Subtype.val_injective
      Finset.univ a hc (fun j _ => hq j j.property)
    change c * ‖x‖ ≤ ‖T x‖ at hxge
    have hxle := (T - F).le_opNorm x
    rw [sub_apply, hxF, sub_zero] at hxle
    have hx : x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg x]
    have hr := S.right_orthonormal.comp (fun j : q => (j : S.Index)) Subtype.val_injective
    exact Fintype.linearIndependent_iff.mp hr.linearIndependent a hx
  let f : q → F.range := fun j => ⟨F (S.rightVector j), ⟨S.rightVector j, rfl⟩⟩
  have hli' : LinearIndependent 𝕜 f := hli.of_comp F.range.subtype
  have hh := hli'.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_coe, Cardinal.lift_natCast] at hh
  have hlt' := Cardinal.lift_lt.mpr hF
  exact (not_lt_of_ge hh) (by simpa only [Cardinal.lift_natCast] using hlt')

/-- Any nonempty remainder of a positive family finite away from zero has
an element of greatest singular value. -/
lemma exists_largest_omitted (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (s : Finset S.Index)
    (hne : ∃ j, j ∉ s) :
    ∃ j, j ∉ s ∧ ∀ k, k ∉ s → S.sigma k ≤ S.sigma j := by
  classical
  obtain ⟨i, hi⟩ := hne
  let q := ((S.finite_away (S.sigma i) (S.positive i)).toFinset).filter (fun j => j ∉ s)
  have hiq : i ∈ q := by simp [q, hi]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image q S.sigma ⟨i, hiq⟩
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro k hk
  by_cases hki : S.sigma i ≤ S.sigma k
  · exact hmax k (by simp [q, hk, hki])
  · exact (le_of_not_ge hki).trans (hmax i hiq)

/-- A prefix of length at most `m`, containing the largest values, and containing
all indices when there are fewer than `m` of them. -/
lemma exists_top_prefix (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (m : ℕ) :
    ∃ s : Finset S.Index, s.card ≤ m ∧
      (s.card = m ∨ ∀ j, j ∈ s) ∧
      ∀ i ∈ s, ∀ j, j ∉ s → S.sigma j ≤ S.sigma i := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp, Or.inl rfl, by simp⟩
  | succ m ih =>
    obtain ⟨s, hcard, hfull, htop⟩ := ih
    by_cases hall : ∀ j, j ∈ s
    · exact ⟨s, hcard.trans (Nat.le_succ m), Or.inr hall, htop⟩
    · obtain ⟨j, hj, hmax⟩ := exists_largest_omitted T S s (by simpa using hall)
      have hcardeq : s.card = m := hfull.resolve_right hall
      refine ⟨insert j s, ?_, Or.inl ?_, ?_⟩
      · simp [Finset.card_insert_of_notMem hj, hcardeq]
      · simp [Finset.card_insert_of_notMem hj, hcardeq]
      · intro i hi k hk
        have hks : k ∉ s := fun h => hk (Finset.mem_insert_of_mem h)
        rcases Finset.mem_insert.mp hi with rfl | his
        · exact hmax k hks
        · exact htop i his k hks

/-- The approximation infimum is attained by the first `n-1` positive terms;
if the singular family has already ended, the truncation is the entire map. -/
lemma approximation_attained (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n) :
    ∃ s : Finset S.Index,
      s.card < n ∧ (s.card = n - 1 ∨ ∀ j, j ∈ s) ∧
      (∀ i ∈ s, ∀ j, j ∉ s → S.sigma j ≤ S.sigma i) ∧
      ‖T - truncation T S s‖ = approximationNumber T n ∧
      ((∀ j, j ∈ s) ∨ ∃ j, j ∉ s ∧ approximationNumber T n = S.sigma j) := by
  classical
  obtain ⟨s, hcard, hfull, htop⟩ := exists_top_prefix T S (n - 1)
  have hcardlt : s.card < n := lt_of_le_of_lt hcard (Nat.sub_lt hn (by decide))
  have hrank : (truncation T S s).toLinearMap.rank < (n : Cardinal) :=
    (truncation_rank_le 𝕜 H K T S s).trans_lt (by exact_mod_cast hcardlt)
  have hlower : approximationNumber T n ≤ ‖T - truncation T S s‖ :=
    approximationNumber_le_error 𝕜 H K T _ n hrank
  by_cases hall : ∀ j, j ∈ s
  · have herr : ‖T - truncation T S s‖ = 0 := le_antisymm
      (truncation_error_le T S s le_rfl (fun j hj => False.elim (hj (hall j)))) (norm_nonneg _)
    have ha : approximationNumber T n = 0 :=
      le_antisymm (hlower.trans_eq herr) (approximationNumber_nonnegative 𝕜 H K T n hn)
    exact ⟨s, hcardlt, hfull, htop, herr.trans ha.symm, Or.inl hall⟩
  · obtain ⟨j, hj, hmax⟩ := exists_largest_omitted T S s (by simpa using hall)
    have hsfull : s.card = n - 1 := hfull.resolve_right hall
    have hqcard : (insert j s).card = n := by
      rw [Finset.card_insert_of_notMem hj, hsfull, Nat.sub_add_cancel hn]
    have hsig : S.sigma j ≤ approximationNumber T n := by
      apply le_approximationNumber 𝕜 H K T n hn
      intro F hF
      apply error_ge_of_rank_lt T S (insert j s) F (le_of_lt (S.positive j))
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact le_rfl
        · exact htop k hk j hj
      · simpa only [hqcard] using hF
    have herr : ‖T - truncation T S s‖ ≤ S.sigma j :=
      truncation_error_le T S s (le_of_lt (S.positive j)) hmax
    have heq := le_antisymm (hlower.trans herr) hsig
    exact ⟨s, hcardlt, hfull, htop, le_antisymm (herr.trans hsig) hlower,
      Or.inr ⟨j, hj, heq⟩⟩

/-- Counting the positive singular directions strictly above a threshold gives
exactly the spectral order-statistic characterization of approximation numbers. -/
lemma approximationNumber_le_iff_count (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 < c) :
    approximationNumber T n ≤ c ↔ {j | c < S.sigma j}.ncard < n := by
  classical
  have hfin : {j | c < S.sigma j}.Finite :=
    (S.finite_away c hc).subset (fun j hj => (show c ≤ S.sigma j from le_of_lt hj))
  constructor
  · intro ha
    obtain ⟨s, hcard, _, _, herr, _⟩ := approximation_attained T S hn
    have hsub : {j | c < S.sigma j} ⊆ (s : Set S.Index) := by
      intro j hj
      by_contra hjs
      have hh := omitted_value_le_error 𝕜 H K T S s j hjs
      change S.sigma j ≤ ‖T - truncation T S s‖ at hh
      rw [herr] at hh
      exact (not_lt_of_ge (hh.trans ha)) hj
    exact (Set.ncard_le_ncard hsub s.finite_toSet).trans_lt (by simpa using hcard)
  · intro hcount
    let s := hfin.toFinset
    have hcard : s.card < n := by
      rw [Set.ncard_eq_toFinset_card _ hfin] at hcount
      exact hcount
    have hrank : (truncation T S s).toLinearMap.rank < (n : Cardinal) :=
      (truncation_rank_le 𝕜 H K T S s).trans_lt (by exact_mod_cast hcard)
    apply (approximationNumber_le_error 𝕜 H K T _ n hrank).trans
    apply truncation_error_le T S s (le_of_lt hc)
    intro j hj
    exact le_of_not_gt (by simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hj)

/-- Canonical, spectrally defined and zero-padded singular values, indexed from 1. -/
def singularValue (T : H →L[𝕜] K) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 < c ∧ ∃ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
    {j | c < S.sigma j}.ncard < n}

/-- The spectral definition agrees with the approximation infimum; no choice of
orthonormal bases or singular system remains in the answer. -/
lemma singularValue_eq_approximationNumber_of_system (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n) :
    singularValue T n = approximationNumber T n := by
  let a := approximationNumber T n
  have ha : 0 ≤ a := approximationNumber_nonnegative 𝕜 H K T n hn
  have hmem {c : ℝ} (hc : 0 < c) (hac : a ≤ c) :
      c ∈ {c : ℝ | 0 < c ∧ ∃ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
        {j | c < S.sigma j}.ncard < n} :=
    ⟨hc, S, (approximationNumber_le_iff_count T S hn hc).mp hac⟩
  have hne := Set.nonempty_of_mem (hmem (show 0 < a + 1 by linarith) (by linarith))
  have hbd : BddBelow {c : ℝ | 0 < c ∧ ∃ S : SingularExpansion.Spec.SingularSystem 𝕜 H K T,
        {j | c < S.sigma j}.ncard < n} := ⟨0, fun c hc => hc.1.le⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    exact csInf_le hbd (hmem (lt_of_le_of_lt ha hc) hc.le)
  · apply le_csInf hne
    rintro c ⟨hc, S', hcount⟩
    exact (approximationNumber_le_iff_count T S' hn hc).mpr hcount

lemma approximationNumber_eq_zero_iff (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n) :
    approximationNumber T n = 0 ↔ T.toLinearMap.rank < (n : Cardinal) := by
  constructor
  · intro hz
    obtain ⟨s, hs, _, _, herr, _⟩ := approximation_attained T S hn
    have heq : T = truncation T S s := sub_eq_zero.mp (norm_eq_zero.mp (herr.trans hz))
    rw [heq]
    exact (truncation_rank_le 𝕜 H K T S s).trans_lt (by exact_mod_cast hs)
  · exact approximationNumber_rank_vanishing 𝕜 H K T n hn

/-- The positive values are actual singular eigenvalues, rather than merely
limit points of the singular spectrum. -/
lemma approximationNumber_positive_value (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n)
    (ha : 0 < approximationNumber T n) :
    ∃ j, approximationNumber T n = S.sigma j := by
  obtain ⟨s, _, _, _, herr, hall | hval⟩ := approximation_attained T S hn
  · have hz := truncation_error_le T S s le_rfl (fun j hj => False.elim (hj (hall j)))
    rw [herr] at hz
    exact False.elim (not_lt_of_ge hz ha)
  · obtain ⟨j, _, hj⟩ := hval
    exact ⟨j, hj⟩

lemma approximationNumber_tendsto_zero (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) :
    Filter.Tendsto (approximationNumber T) Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let N := {j | ε / 2 < S.sigma j}.ncard + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _) hn
  have hc : {j | ε / 2 < S.sigma j}.ncard < n :=
    lt_of_lt_of_le (Nat.lt_succ_self _) hn
  have hb := (approximationNumber_le_iff_count T S hpos (half_pos hε)).mpr hc
  have hnon : 0 ≤ approximationNumber T n := approximationNumber_nonnegative 𝕜 H K T n hpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
  exact hb.trans_lt (half_lt_self hε)

/-- A positive Gram eigenvector has Fourier coefficients only in its own
singular eigenspace. -/
lemma gram_eigenvector_coefficient_zero (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    {a : ℝ} (ha : 0 < a) {x : H}
    (hx : ContinuousLinearMap.adjoint T (T x) = ((a ^ 2 : ℝ) : 𝕜) • x)
    (j : S.Index) (hj : S.sigma j ≠ a) : inner 𝕜 (S.rightVector j) x = 0 := by
  have hcoeff := congrArg (fun z => inner 𝕜 (S.rightVector j) z) hx
  have hsym : inner 𝕜 (S.rightVector j) (ContinuousLinearMap.adjoint T (T x)) =
      inner 𝕜 (ContinuousLinearMap.adjoint T (T (S.rightVector j))) x := by
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  rw [hsym, gram_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal] at hcoeff
  have hne : ((S.sigma j ^ 2 : ℝ) : 𝕜) ≠ ((a ^ 2 : ℝ) : 𝕜) := by
    intro h
    have hs : S.sigma j ^ 2 = a ^ 2 := RCLike.ofReal_injective h
    have : S.sigma j = a := by nlinarith [S.positive j]
    exact hj this
  exact (mul_eq_mul_right_iff.mp hcoeff).resolve_left hne

/-- The singular directions of value `a` form the entire Gram eigenspace for
`a²`. This identifies spectral multiplicity in the original Hilbert space. -/
lemma gram_eigenspace_eq_span (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    {a : ℝ} (ha : 0 < a) :
    Module.End.eigenspace ((ContinuousLinearMap.adjoint T).comp T).toLinearMap ((a ^ 2 : ℝ) : 𝕜) =
      Submodule.span 𝕜 (S.rightVector '' {j | S.sigma j = a}) := by
  classical
  let M := Submodule.span 𝕜 (S.rightVector '' {j | S.sigma j = a})
  letI : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜
    ((S.finite_multiplicity a ha).image S.rightVector)
  apply le_antisymm
  · intro x hx
    have hxe : ContinuousLinearMap.adjoint T (T x) = ((a ^ 2 : ℝ) : 𝕜) • x :=
      Module.End.mem_eigenspace_iff.mp hx
    have hmem : ContinuousLinearMap.adjoint T (T x) ∈ M := by
      apply M.closed_of_finiteDimensional.mem_of_tendsto (S.adjoint_expansion (T x))
      apply Filter.Eventually.of_forall
      intro q
      apply Submodule.sum_mem
      intro j hj
      by_cases hja : S.sigma j = a
      · exact Submodule.smul_mem M _ (Submodule.subset_span ⟨j, hja, rfl⟩)
      · have hz := gram_eigenvector_coefficient_zero T S ha hxe j hja
        have hz' : inner 𝕜 (S.leftVector j) (T x) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left, S.adjoint_left,
            inner_smul_left, hz, mul_zero]
        simp only [hz', mul_zero, zero_smul]
        exact M.zero_mem
    rw [hxe] at hmem
    have hane : ((a ^ 2 : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast (ne_of_gt (sq_pos_of_pos ha))
    have hh := M.smul_mem (((a ^ 2 : ℝ) : 𝕜)⁻¹) hmem
    simpa only [smul_smul, inv_mul_cancel₀ hane, one_smul] using hh
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change ContinuousLinearMap.adjoint T (T (S.rightVector j)) = _
    rw [gram_right, hj]

lemma gram_eigenspace_multiplicity (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T)
    {a : ℝ} (ha : 0 < a) :
    Module.finrank 𝕜 (Module.End.eigenspace ((ContinuousLinearMap.adjoint T).comp T).toLinearMap
      ((a ^ 2 : ℝ) : 𝕜)) = {j | S.sigma j = a}.ncard := by
  classical
  rw [gram_eigenspace_eq_span T S ha]
  let J := {j | S.sigma j = a}
  letI : Fintype J := (S.finite_multiplicity a ha).fintype
  have hrange : Set.range (fun j : J => S.rightVector j) =
      S.rightVector '' {j | S.sigma j = a} := by ext; simp [J]
  have hr : LinearIndependent 𝕜 (fun j : J => S.rightVector j) :=
    (S.right_orthonormal.comp (fun j : J => (j : S.Index)) Subtype.val_injective).linearIndependent
  rw [← hrange, finrank_span_eq_card hr]
  exact (Nat.card_eq_fintype_card).symm

/-- The companion count with a weak threshold handles repetitions exactly. -/
lemma le_approximationNumber_iff_count (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 < c) :
    c ≤ approximationNumber T n ↔ n ≤ {j | c ≤ S.sigma j}.ncard := by
  classical
  let q := (S.finite_away c hc).toFinset
  have hqcard : q.card = {j | c ≤ S.sigma j}.ncard :=
    (Set.ncard_eq_toFinset_card _ (S.finite_away c hc)).symm
  constructor
  · intro ha
    by_contra hnq
    have hcard : q.card < n := by rw [hqcard]; exact lt_of_not_ge hnq
    have hrank : (truncation T S q).toLinearMap.rank < (n : Cardinal) :=
      (truncation_rank_le 𝕜 H K T S q).trans_lt (by exact_mod_cast hcard)
    have hb : approximationNumber T n ≤ ‖T - truncation T S q‖ :=
      approximationNumber_le_error 𝕜 H K T _ n hrank
    by_cases hall : ∀ j, j ∈ q
    · have hh := truncation_error_le T S q le_rfl (fun j hj => False.elim (hj (hall j)))
      exact (not_lt_of_ge ((ha.trans hb).trans hh)) hc
    · obtain ⟨j, hj, hmax⟩ := exists_largest_omitted T S q (by simpa using hall)
      have hjc : S.sigma j < c := by
        apply lt_of_not_ge
        simpa only [q, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hj
      have hh := truncation_error_le T S q (S.positive j).le hmax
      exact (not_lt_of_ge (ha.trans (hb.trans hh))) hjc
  · intro hnq
    apply le_approximationNumber 𝕜 H K T n hn
    intro F hF
    apply error_ge_of_rank_lt T S q F hc.le
    · intro j hj
      simpa only [q, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hj
    · exact hF.trans_le (by exact_mod_cast (hnq.trans_eq hqcard.symm))

/-- Each positive eigenvalue is repeated exactly its Gram eigenspace dimension. -/
lemma approximationNumber_multiplicity (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {a : ℝ} (ha : 0 < a) :
    {n : ℕ | 0 < n ∧ approximationNumber T n = a}.ncard =
      Module.finrank 𝕜 (Module.End.eigenspace
        ((ContinuousLinearMap.adjoint T).comp T).toLinearMap ((a ^ 2 : ℝ) : 𝕜)) := by
  have hset : {n : ℕ | 0 < n ∧ approximationNumber T n = a} =
      Set.Ioc ({j | a < S.sigma j}.ncard) ({j | a ≤ S.sigma j}.ncard) := by
    ext n
    constructor
    · rintro ⟨hn, heq⟩
      constructor
      · exact (approximationNumber_le_iff_count T S hn ha).mp heq.le
      · exact (le_approximationNumber_iff_count T S hn ha).mp heq.ge
    · rintro ⟨hlt, hle⟩
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
      exact ⟨hn, le_antisymm ((approximationNumber_le_iff_count T S hn ha).mpr hlt)
        ((le_approximationNumber_iff_count T S hn ha).mpr hle)⟩
  rw [hset, Set.ncard_Ioc_nat, gram_eigenspace_multiplicity T S ha]
  have hdiff : {j | a ≤ S.sigma j} \ {j | a < S.sigma j} = {j | S.sigma j = a} := by
    ext j
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  rw [← hdiff]
  exact (Set.ncard_sdiff' (show {j | a < S.sigma j} ⊆ {j | a ≤ S.sigma j} from
    fun j hj => (show a ≤ S.sigma j from hj.le)) (S.finite_away a ha)).symm

lemma gram_eigenspace_finiteDimensional (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {a : ℝ} (ha : 0 < a) :
    FiniteDimensional 𝕜 (Module.End.eigenspace
      ((ContinuousLinearMap.adjoint T).comp T).toLinearMap ((a ^ 2 : ℝ) : 𝕜)) := by
  rw [gram_eigenspace_eq_span T S ha]
  exact FiniteDimensional.span_of_finite 𝕜 ((S.finite_multiplicity a ha).image S.rightVector)

lemma gram_hasEigenvalue_iff_approximationNumber (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {a : ℝ} (ha : 0 < a) :
    Module.End.HasEigenvalue ((ContinuousLinearMap.adjoint T).comp T).toLinearMap
      ((a ^ 2 : ℝ) : 𝕜) ↔ ∃ n, 0 < n ∧ approximationNumber T n = a := by
  constructor
  · intro heigen
    have hne : ∃ j, S.sigma j = a := by
      by_contra hno
      have hz : {j | S.sigma j = a} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun j hj => hno ⟨j, hj⟩)
      have hh := gram_eigenspace_eq_span T S ha
      rw [hz, Set.image_empty, Submodule.span_empty] at hh
      exact heigen hh
    have hpos : 0 < {j | S.sigma j = a}.ncard :=
      (Set.ncard_pos (S.finite_multiplicity a ha)).mpr hne
    rw [← gram_eigenspace_multiplicity T S ha,
      ← approximationNumber_multiplicity T S ha] at hpos
    exact Set.nonempty_of_ncard_ne_zero hpos.ne.symm
  · rintro ⟨n, hn, heq⟩
    obtain ⟨j, hj⟩ := approximationNumber_positive_value T S hn (heq.symm ▸ ha)
    have hja : S.sigma j = a := hj.symm.trans heq
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := S.rightVector j)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · change ContinuousLinearMap.adjoint T (T (S.rightVector j)) = _
      rw [gram_right, hja]
    · exact S.right_orthonormal.ne_zero j

lemma approximationNumber_finite_fiber (T : H →L[𝕜] K)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) {a : ℝ} (ha : 0 < a) :
    {n : ℕ | 0 < n ∧ approximationNumber T n = a}.Finite := by
  apply (Set.finite_Iic {j | a ≤ S.sigma j}.ncard).subset
  intro n hn
  exact (le_approximationNumber_iff_count T S hn.1 ha).mp hn.2.ge


/-- Every nonzero eigenvalue of the Gram operator is a strictly positive real
square, over both real and complex scalars. -/
lemma gram_nonzero_eigenvalue_is_square (T : H →L[𝕜] K) {μ : 𝕜} (hμ : μ ≠ 0)
    (he : Module.End.HasEigenvalue ((ContinuousLinearMap.adjoint T).comp T).toLinearMap μ) :
    ∃ a : ℝ, 0 < a ∧ μ = ((a ^ 2 : ℝ) : 𝕜) := by
  obtain ⟨x, hx⟩ := he.exists_hasEigenvector
  have hxne : x ≠ 0 := hx.2
  have hxe : ContinuousLinearMap.adjoint T (T x) = μ • x := hx.apply_eq_smul
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hTx : T x ≠ 0 := by
    intro hz
    have hh : μ • x = 0 := by rw [← hxe, hz, map_zero]
    exact hxne ((smul_eq_zero.mp hh).resolve_left hμ)
  have hTxnorm : 0 < ‖T x‖ := norm_pos_iff.mpr hTx
  have hnK : (‖x‖ : 𝕜) ≠ 0 := by exact_mod_cast hxnorm.ne.symm
  have hinner : μ * (‖x‖ : 𝕜) ^ 2 = (‖T x‖ : 𝕜) ^ 2 := by
    have h := congrArg (fun z => inner 𝕜 x z) hxe
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
      inner_smul_right] using h.symm
  refine ⟨‖T x‖ / ‖x‖, div_pos hTxnorm hxnorm, ?_⟩
  calc
    μ = (‖T x‖ : 𝕜) ^ 2 / (‖x‖ : 𝕜) ^ 2 :=
      (eq_div_iff (pow_ne_zero 2 hnK)).mpr hinner
    _ = ((‖T x‖ : 𝕜) / (‖x‖ : 𝕜)) ^ 2 := (div_pow _ _ _).symm
    _ = (((‖T x‖ / ‖x‖) ^ 2 : ℝ) : 𝕜) := by push_cast; rfl

/-- Full source formula, including the attaining top spectral truncation. -/
theorem best_approximation : Spec.BestApproximation.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT n hn
  obtain ⟨S₀⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  have hv : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S₀ hn
  refine ⟨hv, ?_⟩
  intro S
  obtain ⟨q, hq, hfull, htop, herr, _⟩ := approximation_attained T S hn
  refine ⟨q, hq, hfull, htop,
    (truncation_rank_le 𝕜 H K T S q).trans_lt (by exact_mod_cast hq),
    herr.trans hv.symm, ?_, ?_⟩
  · intro hall
    apply (sub_eq_zero.mp (norm_eq_zero.mp ?_)).symm
    exact le_antisymm
      (truncation_error_le T S q le_rfl (fun j hj => False.elim (hj (hall j)))) (norm_nonneg _)
  · intro hrank
    apply (sub_eq_zero.mp (norm_eq_zero.mp ?_)).symm
    exact herr.trans (approximationNumber_rank_vanishing 𝕜 H K T n hn hrank)

/-- Nonnegative decreasing sequence, zero padding at the rank, and decay to zero. -/
theorem singular_sequence_properties : Spec.SequenceProperties.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  have hv (n : ℕ) (hn : 0 < n) : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hv n hn]
    exact approximationNumber_nonnegative 𝕜 H K T n hn
  · intro n m hnm
    change Spec.SingularValueValue T (m + 1) ≤ Spec.SingularValueValue T (n + 1)
    rw [hv (m + 1) (Nat.succ_pos _), hv (n + 1) (Nat.succ_pos _)]
    exact approximationNumber_antitone T (Nat.succ_pos _) (Nat.succ_le_succ hnm)
  · apply (approximationNumber_tendsto_zero T S).congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hv n hn).symm
  · intro n hn
    rw [hv n hn]
    exact approximationNumber_eq_zero_iff T S hn
  · intro n hn
    rw [hv n hn]
    constructor
    · intro h
      exact le_of_not_gt (fun hlt => (ne_of_gt h) ((approximationNumber_eq_zero_iff T S hn).mpr hlt))
    · intro hr
      have hne : approximationNumber T n ≠ 0 :=
        fun h => (not_lt_of_ge hr) ((approximationNumber_eq_zero_iff T S hn).mp h)
      exact lt_of_le_of_ne (approximationNumber_nonnegative 𝕜 H K T n hn) hne.symm

theorem singular_rank_cases : Spec.RankCases.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT
  obtain ⟨_, _, _, hzero, hpos⟩ := singular_sequence_properties 𝕜 H K T hT
  refine ⟨?_, ?_, ?_⟩
  · intro hfin n hn
    letI := hfin
    have hr : T.toLinearMap.rank = (Module.finrank 𝕜 T.range : Cardinal) :=
      (Module.finrank_eq_rank 𝕜 T.range).symm
    have hp := hpos n hn
    have hz := hzero n hn
    rw [hr] at hp hz
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hz⟩
  · intro hinfinite n hn
    apply (hpos n hn).mpr
    have hr : Cardinal.aleph0 ≤ Module.rank 𝕜 T.range := by
      apply le_of_not_gt
      intro h
      exact hinfinite ((Module.rank_lt_aleph0_iff (R := 𝕜) (M := T.range)).mp h)
    exact (show (n : Cardinal) < Cardinal.aleph0 from Cardinal.natCast_lt_aleph0).le.trans hr
  · intro hz n hn
    apply (hzero n hn).mpr
    subst T
    simpa using (show (0 : Cardinal.{w}) < (n : Cardinal.{w}) from Nat.cast_pos.mpr hn)

theorem singular_spectral_counting : Spec.SpectralCounting.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T _ S
  have hv (n : ℕ) (hn : 0 < n) : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S hn
  refine ⟨?_, ?_, ?_⟩
  · intro c hc n hn
    rw [hv n hn]
    exact approximationNumber_le_iff_count T S hn hc
  · intro c hc n hn
    rw [hv n hn]
    exact le_approximationNumber_iff_count T S hn hc
  · intro n hn ha
    rw [hv n hn] at ha ⊢
    exact approximationNumber_positive_value T S hn ha

theorem singular_spectral_multiplicity : Spec.SpectralMultiplicity.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT a ha
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  have hv (n : ℕ) (hn : 0 < n) : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S hn
  have hset : {n : ℕ | 0 < n ∧ Spec.SingularValueValue T n = a} =
      {n : ℕ | 0 < n ∧ approximationNumber T n = a} := by
    ext n
    by_cases hn : 0 < n
    · simp only [Set.mem_ofPred_eq, hn, true_and, hv n hn]
    · simp only [Set.mem_ofPred_eq, hn, false_and]
  refine ⟨gram_eigenspace_finiteDimensional T S ha, ?_, ?_, ?_⟩
  · rw [gram_hasEigenvalue_iff_approximationNumber T S ha]
    constructor
    · rintro ⟨n, hn, heq⟩
      exact ⟨n, hn, (hv n hn).trans heq⟩
    · rintro ⟨n, hn, heq⟩
      exact ⟨n, hn, (hv n hn).symm.trans heq⟩
  · rw [hset]
    exact approximationNumber_finite_fiber T S ha
  · rw [hset]
    exact approximationNumber_multiplicity T S ha


theorem singular_gram_spectrum : Spec.GramSpectrum.{u, v, w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT μ hμ
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  have hv (n : ℕ) (hn : 0 < n) : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S hn
  constructor
  · intro he
    obtain ⟨a, ha, hμa⟩ := gram_nonzero_eigenvalue_is_square T hμ he
    rw [hμa] at he
    obtain ⟨n, hn, hna⟩ := (gram_hasEigenvalue_iff_approximationNumber T S ha).mp he
    have hh : Spec.SingularValueValue T n = a := (hv n hn).trans hna
    exact ⟨n, hn, hh.symm ▸ ha, by rw [hh]; exact hμa⟩
  · rintro ⟨n, hn, hpos, heq⟩
    rw [heq]
    exact (gram_hasEigenvalue_iff_approximationNumber T S hpos).mpr ⟨n, hn, (hv n hn).symm⟩

/-- Two-sided ideal property, on arbitrary compatible Hilbert spaces. -/
theorem singularValue_ideal : Spec.SingularIdealInequality.{u, v, w, v₀, w₀} := by
  intro 𝕜 _ H K H₀ K₀ _ _ _ _ _ _ _ _ _ _ _ _ T A B hT n hn
  have hTc := (ExpandedFA.Compactness.compact_iff_isCompactOperator T.toLinearMap).mp hT
  have hcomp : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (A.comp (T.comp B)).toLinearMap :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr ((hTc.comp_clm B).clm_comp A)
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H K T hT
  obtain ⟨S'⟩ := SingularExpansion.compact_singular_system 𝕜 H₀ K₀ (A.comp (T.comp B)) hcomp
  have hv : Spec.SingularValueValue T n = approximationNumber T n :=
    singularValue_eq_approximationNumber_of_system T S hn
  have hv' : Spec.SingularValueValue (A.comp (T.comp B)) n =
      approximationNumber (A.comp (T.comp B)) n :=
    singularValue_eq_approximationNumber_of_system _ S' hn
  rw [hv, hv']
  exact approximationNumber_ideal 𝕜 H K H₀ K₀ T A B n hn

end Hilbert
end ExpandedFA.CompactSpectral.SingularApproximation
