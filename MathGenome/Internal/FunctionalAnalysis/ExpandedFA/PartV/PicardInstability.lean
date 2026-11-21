import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.PicardInstability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularExpansion
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
universe u v w
namespace ExpandedFA.PartV.PicardInstability
open Filter
open scoped Topology ENNReal
open Spec

variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- A finite complete singular expansion has finite-dimensional range. -/
lemma finite_range_of_finite_system (K : H →L[𝕜] G)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H G K)
    [Finite S.Index] : FiniteDimensional 𝕜 K.range := by
  let V := Submodule.span 𝕜 (Set.range S.leftVector)
  let : FiniteDimensional 𝕜 V :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  have hsub : K.range ≤ V := by
    rintro _ ⟨x, rfl⟩
    apply V.closed_of_finiteDimensional.mem_of_tendsto (S.expansion x)
    apply Eventually.of_forall
    intro F
    apply Submodule.sum_mem
    intro j _
    exact V.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  exact FiniteDimensional.of_injective (Submodule.inclusion hsub)
    (Submodule.inclusion_injective hsub)

/-- A bound on perpendicular preimages bounds every singular value away from
zero. Compactness then leaves only finitely many singular directions. -/
theorem infinite_rank_instability : Spec.InfiniteRankInstability.{u,v,w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ K hc hr
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system 𝕜 H G K hc
  rintro ⟨C, hC⟩
  have hb (j : S.Index) : 1 ≤ C * S.sigma j := by
    have hp : S.rightVector j ∈ K.ker.orthogonal := by
      rw [← S.right_closedSpan]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩)
    have h := hC _ hp
    rwa [S.right_orthonormal.norm_eq_one, S.map_right, norm_smul,
      S.left_orthonormal.norm_eq_one, mul_one, RCLike.norm_ofReal,
      abs_of_pos (S.positive j)] at h
  have ht : 0 < |C| + 1 := by positivity
  have hall : ∀ j, 1 / (|C| + 1) ≤ S.sigma j := by
    intro j
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_right (le_abs_self C) (S.positive j).le
    nlinarith [hb j, S.positive j]
  have hfinite : (Set.univ : Set S.Index).Finite :=
    (S.finite_away _ (one_div_pos.mpr ht)).subset (fun j _ => hall j)
  let : Finite S.Index := Finite.of_finite_univ hfinite
  exact hr (finite_range_of_finite_system K S)

omit [CompleteSpace H] [CompleteSpace G] in
/-- A sequence of unit perpendicular preimages of data converging to zero
rules out every inverse norm bound, with the inherited norm on the data. -/
lemma no_estimate_of_sequence (K : H →L[𝕜] G) (e : ℕ → H)
    (he : ∀ n, ‖e n‖ = 1) (hp : ∀ n, e n ∈ K.ker.orthogonal)
    (hg : Tendsto (fun n => K (e n)) atTop (𝓝 0)) : NoInverseEstimate K := by
  rintro ⟨C, hC⟩
  have hl : Tendsto (fun n => C * ‖K (e n)‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hg.norm
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto hl (Eventually.of_forall (fun n => by
    simpa only [he n] using hC (e n) (hp n)))
  norm_num at hle

section Diagonal
variable (𝕜 : Type u) [RCLike 𝕜]

private lemma coordinate_norm_le (x : SquareSpace 𝕜) (n : ℕ) :
    ‖x n / ((n+1 : ℕ) : 𝕜)‖ ≤ ‖x n‖ := by
  rw [norm_div, RCLike.norm_natCast]
  exact div_le_self (norm_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

def diagonal : SquareSpace 𝕜 →L[𝕜] SquareSpace 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => x n / ((n+1 : ℕ) : 𝕜),
        (lp.memℓp x).mono' (coordinate_norm_le 𝕜 x)⟩
      map_add' := fun x y => lp.ext (by funext n; exact add_div _ _ _)
      map_smul' := fun c x => lp.ext (by funext n; exact mul_div_assoc _ _ _) }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (coordinate_norm_le 𝕜 x))

@[simp] lemma diagonal_apply (x : SquareSpace 𝕜) (n : ℕ) :
    diagonal 𝕜 x n = x n / ((n+1 : ℕ) : 𝕜) := rfl

lemma reciprocal_mem : Memℓp (fun n : ℕ => 1 / ((n+1 : ℕ) : 𝕜)) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  simpa only [norm_div, norm_one, RCLike.norm_natCast, ENNReal.toReal_ofNat,
    Real.rpow_two, one_div_pow] using ht

def reciprocal : SquareSpace 𝕜 := ⟨_, reciprocal_mem 𝕜⟩

lemma reciprocal_not_mem_range : reciprocal 𝕜 ∉ (diagonal 𝕜).range := by
  rintro ⟨x, hx⟩
  have hxone (n : ℕ) : x n = 1 := by
    have h := congrArg (fun y : SquareSpace 𝕜 => y n) hx
    change x n / ((n+1 : ℕ) : 𝕜) = 1 / ((n+1 : ℕ) : 𝕜) at h
    exact (div_left_inj' (by exact_mod_cast Nat.succ_ne_zero n)).mp h
  have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [hxone, norm_one, Real.one_rpow] at hs
  have hzero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  exact one_ne_zero hzero

lemma diagonal_injective : Function.Injective (diagonal 𝕜) := by
  intro x y h
  apply lp.ext
  funext n
  have hn : ((n+1 : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (div_left_inj' hn).mp (congrArg (fun z : SquareSpace 𝕜 => z n) h)

lemma diagonal_unit_image (n : ℕ) :
    diagonal 𝕜 (lp.single 2 n 1) = lp.single 2 n (1 / ((n+1 : ℕ) : 𝕜)) := by
  apply lp.ext
  funext m
  by_cases hm : m = n
  · subst m; simp
  · rw [diagonal_apply]
    simp only [lp.single_apply_ne _ _ _ hm, zero_div]

lemma diagonal_data_tendsto :
    Tendsto (fun n => diagonal 𝕜 (lp.single 2 n 1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hn (n : ℕ) : ‖diagonal 𝕜 (lp.single 2 n 1)‖ =
      1 / ((n+1 : ℕ) : ℝ) := by
    rw [diagonal_unit_image, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
      norm_div, norm_one, RCLike.norm_natCast]
  simp_rw [hn]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem truncation_coordinate_bound (N : ℕ) (x : SquareSpace 𝕜) (n : ℕ) :
    ‖if n < N then x n / ((n + 1 : ℕ) : 𝕜) else 0‖ ≤ ‖x n‖ := by
  split_ifs
  · rw [norm_div, RCLike.norm_natCast]
    exact div_le_self (norm_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  · simp

/-- Retain precisely the first `N` positive manuscript coordinates. -/
def truncation (N : ℕ) : SquareSpace 𝕜 →L[𝕜] SquareSpace 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => if n < N then x n / ((n + 1 : ℕ) : 𝕜) else 0,
        (lp.memℓp x).mono' (truncation_coordinate_bound 𝕜 N x)⟩
      map_add' := fun x y => lp.ext (by
        funext n
        change (if n < N then (x n + y n) / ((n + 1 : ℕ) : 𝕜) else 0) =
          (if n < N then x n / ((n + 1 : ℕ) : 𝕜) else 0) +
          (if n < N then y n / ((n + 1 : ℕ) : 𝕜) else 0)
        split_ifs <;> simp [add_div])
      map_smul' := fun c x => lp.ext (by
        funext n; dsimp; split_ifs <;> simp [mul_div_assoc]) }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (truncation_coordinate_bound 𝕜 N x))

@[simp] theorem truncation_apply (N : ℕ) (x : SquareSpace 𝕜) (n : ℕ) :
    truncation 𝕜 N x n = if n < N then x n / ((n + 1 : ℕ) : 𝕜) else 0 := rfl

theorem truncation_finite_rank (N : ℕ) :
    FiniteDimensional 𝕜 (truncation 𝕜 N).toLinearMap.range := by
  let R := (truncation 𝕜 N).toLinearMap.range
  let f : R →ₗ[𝕜] (Fin N → 𝕜) :=
    { toFun := fun x i => x.val i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply lp.ext
  funext n
  by_cases hn : n < N
  · exact congrFun h ⟨n, hn⟩
  · obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    have hax := congrArg (fun z : SquareSpace 𝕜 => z n) ha
    have hby := congrArg (fun z : SquareSpace 𝕜 => z n) hb
    change (if n < N then a n / ((n + 1 : ℕ) : 𝕜) else 0) = x.val n at hax
    change (if n < N then b n / ((n + 1 : ℕ) : 𝕜) else 0) = y.val n at hby
    rw [ite_eq_right hn] at hax hby
    exact hax.symm.trans hby

theorem tail_norm_le (N : ℕ) (x : SquareSpace 𝕜) :
    ‖(diagonal 𝕜 - truncation 𝕜 N) x‖ ≤
      (1 / ((N + 1 : ℕ) : ℝ)) * ‖x‖ := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hmono : ‖(diagonal 𝕜 - truncation 𝕜 N) x‖ ≤
      ‖(1 / ((N + 1 : ℕ) : ℝ)) • x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    change ‖x n / ((n + 1 : ℕ) : 𝕜) -
      (if n < N then x n / ((n + 1 : ℕ) : 𝕜) else 0)‖ ≤
      ‖(1 / ((N + 1 : ℕ) : ℝ)) • x n‖
    by_cases hn : n < N
    · simp [hn]
    · simp only [hn, ite_false, sub_zero, norm_div, RCLike.norm_natCast,
        norm_smul, Real.norm_eq_abs, abs_one]
      have hle : ((N + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hn) 1
      calc
        ‖x n‖ / ((n + 1 : ℕ) : ℝ) ≤ ‖x n‖ / ((N + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hN hle
        _ = (1 / ((N + 1 : ℕ) : ℝ)) * ‖x n‖ := by ring
  simpa only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hN)] using hmono


lemma truncation_tendsto : Tendsto (truncation 𝕜) atTop (𝓝 (diagonal 𝕜)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => 1 / ((N+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun N => norm_nonneg _) _ hlim
  intro N
  rw [norm_sub_rev]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (tail_norm_le 𝕜 N)

lemma diagonal_compact :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (diagonal 𝕜).toLinearMap := by
  have hc (N : ℕ) : IsCompactOperator (truncation 𝕜 N) := by
    let := truncation_finite_rank 𝕜 N
    have h : IsCompactOperator (truncation 𝕜 N).rangeRestrict :=
      isCompactOperator_of_locallyCompactSpace_dom _
    exact h.continuous_comp continuous_subtype_val
  have hh : IsCompactOperator (diagonal 𝕜) :=
    isClosed_setOfPred_isCompactOperator.mem_of_tendsto (truncation_tendsto 𝕜)
      (Eventually.of_forall hc)
  exact (Compactness.compact_iff_isCompactOperator _).mpr hh

lemma diagonal_no_estimate : NoInverseEstimate (diagonal 𝕜) := by
  apply no_estimate_of_sequence (diagonal 𝕜) (fun n => lp.single 2 n 1)
  · intro n; simp
  · intro n z hz
    change diagonal 𝕜 z = 0 at hz
    have hz0 : z = 0 := diagonal_injective 𝕜 (by simpa using hz)
    simp [hz0]
  · exact diagonal_data_tendsto 𝕜

/-- An unsolvable square-summable datum coexists with uniquely solvable
vanishing data whose solutions have norm one. -/
theorem diagonal_example : Spec.DiagonalExample.{u} := by
  intro 𝕜 _
  refine ⟨diagonal 𝕜, reciprocal 𝕜, diagonal_apply 𝕜, (fun n => rfl),
    diagonal_compact 𝕜, diagonal_injective 𝕜, reciprocal_not_mem_range 𝕜,
    diagonal_unit_image 𝕜, diagonal_data_tendsto 𝕜, ?_, diagonal_no_estimate 𝕜⟩
  intro n
  refine ⟨by simp, fun x => ⟨fun h => diagonal_injective 𝕜 h,
    fun h => congrArg (diagonal 𝕜) h⟩⟩

end Diagonal
end ExpandedFA.PartV.PicardInstability
