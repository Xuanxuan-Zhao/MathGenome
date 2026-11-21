import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15CoordinateContinuity

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.C15PartialSums
open ExpandedFA.P1.C15Basis ExpandedFA.P1.BasisNormCompleteness
open ExpandedFA.P1.C15CoordinateContinuity

abbrev basisConstant := @Spec.basisConstant

namespace PartialSumBoundsProof
open ExpandedFA.P1.C15PartialSums.Spec (ProjectionBounds)
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Abstract projection-family estimates use the uniform bound already proved in
coordinate continuity, rather than assuming the desired basis constant finite. -/
theorem projection_bounds (P : ℕ → E → E) (T : ℕ → E →L[𝕜] E)
    (hT : ∀ N x, T N x = P N x)
    (hz : ∀ x, P 0 x = 0)
    (hc : ∀ N M x, P N (P M x) = P (min N M) x)
    (hp : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ N x, ‖P N x‖ ≤ C * ‖x‖) :
    ProjectionBounds P T := by
  obtain ⟨C, hC, hb⟩ := hb
  have hnorm (N) : ‖T N‖ ≤ C :=
    (T N).opNorm_le_bound hC (fun x => by simpa only [hT] using hb N x)
  have hbounded : BddAbove (Set.range fun N => ‖T N‖) := by
    exact ⟨C, by rintro _ ⟨N, rfl⟩; exact hnorm N⟩
  have hle (N) : ‖T N‖ ≤ basisConstant T := le_ciSup hbounded N
  have hK : 0 ≤ basisConstant T := (norm_nonneg (T 0)).trans (hle 0)
  have hpoint (N) (x : E) : ‖P N x‖ ≤ basisConstant T * ‖x‖ := by
    rw [← hT]
    exact (T N).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hle N) (norm_nonneg x))
  refine ⟨hT, hz, hc, hp, hbounded, hK, ?_, hpoint, ?_⟩
  · intro hnontriv
    let := hnontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hh : ‖x‖ ≤ basisConstant T * ‖x‖ :=
      le_of_tendsto (hp x).norm (Filter.Eventually.of_forall (fun N => hpoint N x))
    nlinarith [norm_pos_iff.mpr hx]
  · intro N x
    have hbx : BddAbove (Set.range fun M => ‖P M x‖) :=
      ⟨C * ‖x‖, by rintro _ ⟨M, rfl⟩; exact hb M x⟩
    apply ciSup_le
    intro M
    rw [hc]
    exact le_ciSup hbx (min M N)

/-- Projecting a finite combination discards exactly the indices outside the set. -/
theorem proj_sum_subset {ι : Type*} {L : SummationFilter ι}
    (b : GeneralSchauderBasis ι 𝕜 E L) (a : ι → 𝕜)
    (s t : Finset ι) (hst : s ⊆ t) :
    b.proj s (∑ i ∈ t, a i • b i) = ∑ i ∈ s, a i • b i := by
  classical
  simp only [map_sum, map_smul, GeneralSchauderBasis.proj_apply_basis_mem,
    smul_ite, smul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hst h, h⟩⟩

end PartialSumBoundsProof

open ExpandedFA.P1.C15PartialSums.Spec (ProjectionBounds)

/-- All projection and quantitative basis bounds for the original ordered expansion. -/
theorem raw_partial_sum_bounds : Spec.RawBounds := by
  intro 𝕜 E _ _ _ _ e h
  classical
  obtain ⟨b, hbe, hba, hbp⟩ := raw_native_basis h
  have he (i : ℕ) : b i = e i := congrFun hbe i
  have hc (N M : ℕ) (x : E) :
      rawPartialSum h N (rawPartialSum h M x) = rawPartialSum h (min N M) x := by
    simpa only [hbp] using b.proj_comp N M x
  obtain ⟨C, hC, hb⟩ := raw_basis_norm_equivalent h
  have hp (N : ℕ) (x : E) : ‖rawPartialSum h N x‖ ≤ C * ‖x‖ :=
    (CoordinateContinuityProof.norm_le_sup _ (raw_basis_complete h).bounded N x).trans (hb x)
  have H := PartialSumBoundsProof.projection_bounds (rawPartialSum h) b.proj hbp
    (rawPartialSum_zero h) hc (rawPartialSum_tendsto h) ⟨C, hC, hp⟩
  refine ⟨b.proj, H, ?_, ?_⟩
  · intro a m N hmN
    have ht : b.proj m (orderedPartialSum e a N) = orderedPartialSum e a m := by
      change GeneralSchauderBasis.proj b (Finset.range m)
        (∑ i ∈ Finset.range N, a i • e i) = ∑ i ∈ Finset.range m, a i • e i
      simpa only [he] using PartialSumBoundsProof.proj_sum_subset b a
        (Finset.range m) (Finset.range N) (Finset.range_mono hmN)
    have hh := (b.proj m).le_opNorm (orderedPartialSum e a N)
    rw [ht] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_ciSup H.bounded m) (norm_nonneg _))
  · intro i x
    rw [← norm_smul, ← BasisNormProof.raw_increment h x i]
    exact (norm_sub_le _ _).trans (by
      linarith [H.norm_bound (i + 1) x, H.norm_bound i x])

/-- A finite-list increment, including the final nonzero increment. -/
theorem finitePartialSum_increment {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := 𝕜) e)
    (x : E) (i : Fin d) :
    finitePartialSum h (i.val + 1) x - finitePartialSum h i.val x =
      finiteCoordinates h x i • e i := by
  classical
  simp only [finitePartialSum, ExpandedFA.P1.C15Basis.Spec.finitePartialSum, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  have hh (j : Fin d) :
      (if j.val < i.val + 1 then finiteCoordinates h x j • e j else 0) -
        (if j.val < i.val then finiteCoordinates h x j • e j else 0) =
      if j = i then finiteCoordinates h x i • e i else 0 := by
    by_cases hji : j = i
    · subst j
      simp
    · have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
      by_cases hj : j.val < i.val
      · simp [hji, hj, show j.val < i.val + 1 by omega]
      · simp [hji, hj, show ¬j.val < i.val + 1 by omega]
  simp_rw [hh]
  simp

/-- Finite bases have the same constant and estimates, with stabilization and
zero constant for the empty list stated explicitly. -/
theorem finite_partial_sum_bounds : Spec.FiniteBounds := by
  intro 𝕜 E _ _ _ _ d e h
  classical
  let : DecidableEq (Fin d) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨b, hbe, hba, hbp⟩ := finite_native_basis h
  let S (N : ℕ) : Finset (Fin d) := Finset.univ.filter (fun i => i.val < N)
  let T (N : ℕ) : E →L[𝕜] E := b.proj (S N)
  have he (i : Fin d) : b i = e i := congrFun hbe i
  have hT (N : ℕ) (x : E) : T N x = finitePartialSum h N x := hbp N x
  have hc (N M : ℕ) (x : E) :
      finitePartialSum h N (finitePartialSum h M x) = finitePartialSum h (min N M) x := by
    have hs : S N ∩ S M = S (min N M) := by
      ext i
      simp only [S, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hh := b.proj_comp (S N) (S M) x
    have hh' := hh.trans (congrArg (fun A : Finset (Fin d) => b.proj A x) hs)
    simpa only [show ∀ N x, b.proj (S N) x = finitePartialSum h N x from hT] using hh'
  have hconv (x : E) : Tendsto (fun N => finitePartialSum h N x) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    exact (finitePartialSum_of_le h N hN x).symm
  obtain ⟨C, hC, hb⟩ := finite_basis_norm_equivalent h
  have hp (N : ℕ) (x : E) : ‖finitePartialSum h N x‖ ≤ C * ‖x‖ :=
    (CoordinateContinuityProof.norm_le_sup _ (finite_basis_complete h).bounded N x).trans (hb x)
  have H := PartialSumBoundsProof.projection_bounds (finitePartialSum h) T hT
    (finitePartialSum_zero h) hc hconv ⟨C, hC, hp⟩
  refine ⟨T, H, ?_, ?_, finitePartialSum_of_le h, ?_⟩
  · intro a m N hmN
    have hsub : S m ⊆ S N := by
      intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    have ht : T m (∑ i ∈ S N, a i • e i) = ∑ i ∈ S m, a i • e i := by
      simpa only [T, he] using PartialSumBoundsProof.proj_sum_subset b a (S m) (S N) hsub
    have hh := (T m).le_opNorm (∑ i ∈ S N, a i • e i)
    rw [ht] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_ciSup H.bounded m) (norm_nonneg _))
  · intro i x
    rw [← norm_smul, ← finitePartialSum_increment h x i]
    exact (norm_sub_le _ _).trans (by
      linarith [H.norm_bound (i.val + 1) x, H.norm_bound i.val x])
  · intro hd
    have hz (N) : T N = 0 := by
      ext x
      rw [hT]
      have hempty : S N = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i _
        have := i.isLt
        omega
      change (∑ i ∈ S N, finiteCoordinates h x i • e i) = 0
      rw [hempty, Finset.sum_empty]
    simp [Spec.basisConstant, hz]

end ExpandedFA.P1.C15PartialSums
