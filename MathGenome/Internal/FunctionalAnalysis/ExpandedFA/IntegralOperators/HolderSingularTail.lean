import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.HolderSingularTail
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceNormIdeal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open scoped BigOperators
namespace ExpandedFA.IntegralOperators.HolderSingularTail

open TraceIdeals.HilbertSchmidtDefinitions
open TraceIdeals.HilbertSchmidtBasis
open CompactSpectral
open MeasureTheory

universe u v w
section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

/-- Rank-n perturbations shift the canonical singular sequence by at most n.
Both operators are compact, but no summability is required for this lemma. -/
lemma singularValue_rank_perturbation (T A : E →L[𝕜] F)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (hR : Compactness.DefinitionsSpec.IsCompactLinearMapValue (T-A).toLinearMap)
    (n : ℕ) (hA : A.toLinearMap.rank ≤ (n : Cardinal)) (j : ℕ) :
    SingularApproximation.Spec.SingularValueValue T (j+n+1) ≤
      SingularApproximation.Spec.SingularValueValue (T-A) (j+1) := by
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 E F (T-A) hR
  obtain ⟨q, _, _, _, hq, herr, _, _⟩ :=
    ((SingularApproximation.best_approximation 𝕜 E F (T-A) hR
      (j+1) (Nat.succ_pos j)).2 S)
  let B := SingularApproximation.Spec.TruncationValue (T-A) S q
  have hrank : (A+B).toLinearMap.rank < ((j+n+1 : ℕ) : Cardinal) := by
    have hq' : B.toLinearMap.rank ≤ (j : Cardinal) :=
      Cardinal.lt_natCast_add_one_iff.mp (by
        simpa only [Nat.cast_add, Nat.cast_one] using hq)
    have hle : (A+B).toLinearMap.rank ≤ ((n+j : ℕ) : Cardinal) := by
      simpa only [ContinuousLinearMap.toLinearMap_add, Nat.cast_add] using
        (LinearMap.rank_add_le A.toLinearMap B.toLinearMap).trans (add_le_add hA hq')
    exact hle.trans_lt (by exact_mod_cast (show n+j < j+n+1 by omega))
  rw [(SingularApproximation.best_approximation 𝕜 E F T hT
    (j+n+1) (by omega)).1]
  calc
    _ ≤ ‖T - (A+B)‖ :=
      SingularApproximation.approximationNumber_le_error 𝕜 E F T (A+B) _ hrank
    _ = ‖(T-A)-B‖ := by congr 1; abel
    _ = _ := herr

/-- The extended squared tail inequality, valid also for n=0, zero spaces,
finite-rank maps and arbitrary Hilbert-space dimensions. -/
theorem projection_tail : Spec.ProjectionTail.{u,v,w} := by
  intro 𝕜 _ E F _ _ _ _ _ _ T hT M _ n hM
  let P : F →L[𝕜] F := M.subtypeL.comp M.orthogonalProjectionOnto
  let A : E →L[𝕜] F := P.comp T
  let R : E →L[𝕜] F := (ContinuousLinearMap.id 𝕜 F - P).comp T
  have hR : IsHilbertSchmidt R := postcomp_finiteness T _ hT
  have hA : A.toLinearMap.rank ≤ (n : Cardinal) := by
    apply (LinearMap.rank_comp_le_left T.toLinearMap P.toLinearMap).trans
    exact (LinearMap.rank_comp_le_left M.orthogonalProjectionOnto.toLinearMap M.subtype).trans
      ((LinearMap.rank_le_domain M.subtype).trans hM)
  have hRA : R = T-A := by ext x; simp [R, A, P]
  have hcT := compactness T hT
  have hcR := compactness R hR
  have hnonT := (SingularApproximation.singular_sequence_properties 𝕜 E F T hcT).1
  change (∑' j : ℕ, ENNReal.ofReal
    (TraceIdeals.TraceClassDefinitions.Spec.singularSequence T (j+n) ^ 2)) ≤
      hilbertSchmidtSquare R
  rw [singular_square_identity R hR]
  apply ENNReal.tsum_le_tsum
  intro j
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀
  · exact hnonT _ (by omega)
  · have hh := singularValue_rank_perturbation T A hcT (hRA ▸ hcR) n hA j
    simpa only [TraceIdeals.TraceClassDefinitions.Spec.singularSequence, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, ← hRA] using hh

end Hilbert

/-- The square of the geometric block majorant, with exactly the exponent in
our trace bound. This identity also holds when the Hölder constant vanishes. -/
lemma dyadic_majorant_square (α H : ℝ) (m : ℕ) :
    (H * ((2 : ℝ) ^ (1 / 2 - α)) ^ m) ^ 2 =
      (2 : ℝ) ^ m * (H ^ 2 * ((2 : ℝ) ^ m) ^ (-2 * α)) := by
  have ht : (0 : ℝ) ≤ 2 := by norm_num
  calc
    _ = H ^ 2 * (2 : ℝ) ^ ((1 / 2 - α) * ((m : ℝ) * 2)) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast ht]
      push_cast
      rfl
    _ = H ^ 2 * ((2 : ℝ) ^ m * ((2 : ℝ) ^ m) ^ (-2 * α)) := by
      congr 1
      rw [← Real.rpow_natCast_mul ht, ← Real.rpow_natCast (2 : ℝ) m,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ = _ := by ring

/-- Cauchy–Schwarz on a dyadic block followed by the square-tail hypothesis. -/
lemma dyadic_block_bound (s : ℕ → ℝ) (α H : ℝ) (hH : 0 ≤ H)
    (hs : Summable (fun j => s j ^ 2))
    (ht : ∀ n : ℕ, 0 < n →
      (∑' j : ℕ, s (j+n) ^ 2) ≤ H ^ 2 * (n : ℝ) ^ (-2 * α)) (m : ℕ) :
    (∑ j ∈ Finset.Ico (2^m) (2^(m+1)), s j) ≤
      H * ((2 : ℝ) ^ (1 / 2 - α)) ^ m := by
  have hn : 2^m ≤ 2^(m+1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico (2^m) (2^(m+1)))
    (fun _ : ℕ => (1 : ℝ)) s
  have hcard : (Finset.Ico (2^m) (2^(m+1))).card = 2^m := by
    simp only [Nat.card_Ico, pow_succ]
    omega
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hcs
  have htail : (∑ j ∈ Finset.Ico (2^m) (2^(m+1)), s j ^ 2) ≤
      ∑' j : ℕ, s (j+2^m) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_comm (2^m)]
    apply Summable.sum_le_tsum
    · intro j _
      exact sq_nonneg _
    · exact (summable_nat_add_iff (2^m)).mpr hs
  have hh := mul_le_mul_of_nonneg_left (htail.trans (ht (2^m) (by positivity)))
    (show (0 : ℝ) ≤ (2^m : ℕ) by positivity)
  push_cast at hh hcs
  have hsq := hcs.trans hh
  rw [← dyadic_majorant_square] at hsq
  exact le_of_sq_le_sq hsq (by positivity)

/-- The sum through a complete dyadic prefix is bounded by the corresponding
finite geometric sum. This is a finite identity, not an exchange of two tsums. -/
lemma dyadic_prefix_bound (s : ℕ → ℝ) (α H : ℝ) (hH : 0 ≤ H)
    (hs : Summable (fun j => s j ^ 2))
    (ht : ∀ n : ℕ, 0 < n →
      (∑' j : ℕ, s (j+n) ^ 2) ≤ H ^ 2 * (n : ℝ) ^ (-2 * α)) (m : ℕ) :
    (∑ j ∈ Finset.range (2^m), s j) ≤
      s 0 + ∑ j ∈ Finset.range m, H * ((2 : ℝ) ^ (1 / 2 - α)) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Finset.sum_range_add_sum_Ico s
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ m)), Finset.sum_range_succ]
    exact (add_le_add ih (dyadic_block_bound s α H hH hs ht m)).trans_eq (by ring)

theorem dyadic_estimate : Spec.DyadicEstimate := by
  intro s α H B hnonneg hs hα hH hB ht
  let q : ℝ := (2 : ℝ) ^ (1 / 2 - α)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
    linarith
  have hg : Summable (fun m : ℕ => H * q^m) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left H
  have hgeom : (∑' m : ℕ, H * q^m) = H / (1-q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
  have hbound (N : ℕ) : (∑ j ∈ Finset.range N, s j) ≤ B + H / (1-q) := by
    have hn : N ≤ 2^N := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc
      _ ≤ ∑ j ∈ Finset.range (2^N), s j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
          (fun i _ _ => hnonneg i)
      _ ≤ s 0 + ∑ j ∈ Finset.range N, H * q^j := dyadic_prefix_bound s α H hH hs ht N
      _ ≤ B + ∑' j : ℕ, H * q^j := add_le_add hB
        (hg.sum_le_tsum _ (fun i _ => mul_nonneg hH (pow_nonneg hq0 i)))
      _ = B + H / (1-q) := by rw [hgeom]
  exact ⟨summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩


/-- No sign assumption on the Hölder constant is added to the source: its
nonnegativity already follows by testing the two interval endpoints. -/
lemma holderFirst_nonneg {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (α H : ℝ) (hk : Spec.HolderFirst k α H) : 0 ≤ H := by
  let a : Spec.I := ⟨0, by constructor <;> norm_num⟩
  let b : Spec.I := ⟨1, by constructor <;> norm_num⟩
  have hh := (norm_nonneg (k (a,a) - k (b,a))).trans (hk a b a)
  simpa [a, b] using hh

lemma stepSubspace_rank_le (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    Module.rank 𝕜 (Spec.stepSubspace 𝕜 n) ≤ (n : Cardinal) := by
  have hh := (rank_span_le (R := 𝕜)
    (Set.range (Spec.cellVector (𝕜 := 𝕜) n))).trans
    (Cardinal.mk_range_le (f := Spec.cellVector (𝕜 := 𝕜) n))
  convert hh using 1 <;> simp [Spec.stepSubspace]
  rfl

lemma cellProjection_rank_le (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (Spec.cellProjection 𝕜 n).toLinearMap.rank ≤ (n : Cardinal) :=
  (LinearMap.rank_comp_le_left (Spec.stepSubspace 𝕜 n).orthogonalProjectionOnto.toLinearMap
    (Spec.stepSubspace 𝕜 n).subtype).trans
    ((LinearMap.rank_le_domain (Spec.stepSubspace 𝕜 n).subtype).trans
      (stepSubspace_rank_le 𝕜 n))

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

/-- The dyadic criterion, now for the actual canonical singular values and
trace norm of an operator. -/
lemma trace_bound_of_square_tail (T : E →L[𝕜] F) (hT : IsHilbertSchmidt T)
    (α H : ℝ) (hα : 1 / 2 < α) (hH : 0 ≤ H)
    (ht : ∀ n : ℕ, 0 < n →
      (∑' j : ℕ, TraceIdeals.TraceClassDefinitions.Spec.singularSequence T (j+n) ^ 2) ≤
        H ^ 2 * (n : ℝ) ^ (-2 * α)) :
    TraceIdeals.TraceClassDefinitions.IsTraceClass T ∧
    TraceIdeals.TraceClassDefinitions.traceNorm T ≤
      hilbertSchmidtNorm ⟨T,hT⟩ + H / (1 - (2 : ℝ) ^ (1 / 2 - α)) := by
  have hc := compactness T hT
  have hn := (SingularApproximation.singular_sequence_properties 𝕜 E F T hc).1
  have hfirst : TraceIdeals.TraceClassDefinitions.Spec.singularSequence T 0 ≤
      hilbertSchmidtNorm ⟨T,hT⟩ := by
    rw [TraceIdeals.TraceClassDefinitions.Spec.singularSequence,
      (SingularApproximation.best_approximation 𝕜 E F T hc 1 (by decide)).1]
    calc
      _ ≤ ‖T - 0‖ := SingularApproximation.approximationNumber_le_error 𝕜 E F T 0 1 (by simp)
      _ = ‖T‖ := by simp
      _ ≤ _ := operator_norm_bound ⟨T,hT⟩
  obtain ⟨hs, hbound⟩ := dyadic_estimate
    (TraceIdeals.TraceClassDefinitions.Spec.singularSequence T) α H
    (hilbertSchmidtNorm ⟨T,hT⟩) (fun j => hn (j+1) (Nat.succ_pos j))
    (singular_norm_identity ⟨T,hT⟩).1 hα hH hfirst ht
  exact ⟨⟨hc,hs⟩,hbound⟩

end Hilbert

/-- Assemble the first-variable conclusion from the cell projection estimate. -/
lemma firstVariable_of_averaging_error (havg : Spec.AveragingError) : Spec.FirstVariable := by
  intro 𝕜 _ k α H hα hα1 hk
  have hH := holderFirst_nonneg k α H hk
  have hT : IsHilbertSchmidt (Spec.kernel k) :=
    (TraceIdeals.HilbertSchmidtKernels.kernel_isometry Spec.μ Spec.μ (Spec.kernelClass k)).1
  have ht (n : ℕ) (hn : 0 < n) :
      (∑' j : ℕ, TraceIdeals.TraceClassDefinitions.Spec.singularSequence
        (Spec.kernel k) (j+n) ^ 2) ≤ H ^ 2 * (n : ℝ) ^ (-2 * α) := by
    obtain ⟨_,hR,hbound⟩ := havg 𝕜 k α H hα hα1 hk n hn
    let R := (ContinuousLinearMap.id 𝕜 (Spec.L2 𝕜) - Spec.cellProjection 𝕜 n).comp (Spec.kernel k)
    have hs := (summable_nat_add_iff n).mpr (singular_norm_identity ⟨Spec.kernel k,hT⟩).1
    have hh := projection_tail 𝕜 (Spec.L2 𝕜) (Spec.L2 𝕜) (Spec.kernel k) hT
      (Spec.stepSubspace 𝕜 n) n (stepSubspace_rank_le 𝕜 n)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hs] at hh
    have hh' := ENNReal.toReal_mono hR.ne hh
    rw [ENNReal.toReal_ofReal (tsum_nonneg (fun j => sq_nonneg _)),
      ← square_of_norm ⟨R,hR⟩] at hh'
    calc
      _ ≤ hilbertSchmidtNorm ⟨R,hR⟩ ^ 2 := hh'
      _ ≤ (H * (n : ℝ) ^ (-α)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
      _ = H ^ 2 * (n : ℝ) ^ (-2 * α) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        congr 2
        norm_num
        ring
  have hh := trace_bound_of_square_tail (Spec.kernel k) hT α H hα hH ht
  have hiso : hilbertSchmidtNorm ⟨Spec.kernel k,hT⟩ = ‖Spec.kernelClass k‖ :=
    (TraceIdeals.HilbertSchmidtKernels.kernel_isometry Spec.μ Spec.μ (Spec.kernelClass k)).2 hT
  rw [hiso] at hh
  exact hh


section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

lemma traceClass_adjoint_le (T : E →L[𝕜] F) (hT : IsHilbertSchmidt T)
    (ht : TraceIdeals.TraceClassDefinitions.IsTraceClass T) :
    TraceIdeals.TraceClassDefinitions.IsTraceClass (ContinuousLinearMap.adjoint T) ∧
      TraceIdeals.TraceClassDefinitions.traceNorm (ContinuousLinearMap.adjoint T) ≤
        TraceIdeals.TraceClassDefinitions.traceNorm T := by
  apply TraceIdeals.TraceNormIdeal.traceClass_of_finite_family_bound _
    (compactness _ ((adjoint_finiteness T).mpr hT))
  intro n a b ha hb
  have hh := TraceIdeals.TraceNormIdeal.finite_family_bound T ht b a hb ha
  simpa only [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh

lemma traceClass_adjoint_norm (T : E →L[𝕜] F) (hT : IsHilbertSchmidt T)
    (ht : TraceIdeals.TraceClassDefinitions.IsTraceClass T) :
    TraceIdeals.TraceClassDefinitions.IsTraceClass (ContinuousLinearMap.adjoint T) ∧
      TraceIdeals.TraceClassDefinitions.traceNorm (ContinuousLinearMap.adjoint T) =
        TraceIdeals.TraceClassDefinitions.traceNorm T := by
  obtain ⟨ha, hle⟩ := traceClass_adjoint_le T hT ht
  have hrev := (traceClass_adjoint_le _ ((adjoint_finiteness T).mpr hT) ha).2
  rw [ContinuousLinearMap.adjoint_adjoint] at hrev
  exact ⟨ha, le_antisymm hle hrev⟩

end Hilbert

/-- The actual conjugate-transposed continuous kernel on the same square. -/
def adjointKernel {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜)) :
    C(Spec.I × Spec.I, 𝕜) :=
  star (k.comp ⟨Prod.swap, continuous_swap⟩)

lemma adjointKernel_class {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜)) :
    Spec.kernelClass (adjointKernel k) =
      ExpandedFA.PartV.L2KernelCompactSpec.dagger Spec.μ Spec.μ (Spec.kernelClass k) := by
  apply Lp.ext
  have hk := (MeasureTheory.Measure.measurePreserving_swap (μ := Spec.μ) (ν := Spec.μ)).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ := Spec.μ.prod Spec.μ) k)
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ := Spec.μ.prod Spec.μ)
    (adjointKernel k), ExpandedFA.PartV.L2KernelCompact.dagger_coe
      Spec.μ Spec.μ (Spec.kernelClass k), hk] with p hp hd hk
  change (Spec.kernelClass (adjointKernel k) : Spec.I × Spec.I → 𝕜) p = _ at hp ⊢
  rw [hp, hd]
  change star (k p.swap) = star (Spec.kernelClass k p.swap)
  change Spec.kernelClass k p.swap = k p.swap at hk
  rw [hk]

lemma adjointKernel_operator {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜)) :
    Spec.kernel (adjointKernel k) = ContinuousLinearMap.adjoint (Spec.kernel k) := by
  change ExpandedFA.PartV.L2Kernel.kernelOperator Spec.μ Spec.μ
    (Spec.kernelClass (adjointKernel k)) = ContinuousLinearMap.adjoint
      (ExpandedFA.PartV.L2Kernel.kernelOperator Spec.μ Spec.μ (Spec.kernelClass k))
  rw [ExpandedFA.PartV.L2KernelCompact.kernelOperator_adjoint, adjointKernel_class]

lemma adjointKernel_norm {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜)) :
    ‖Spec.kernelClass (adjointKernel k)‖ = ‖Spec.kernelClass k‖ := by
  rw [adjointKernel_class]
  exact ExpandedFA.PartV.L2KernelCompact.dagger_norm Spec.μ Spec.μ (Spec.kernelClass k)

lemma holderSecond_adjointKernel {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (α H : ℝ) (hk : Spec.HolderSecond k α H) :
    Spec.HolderFirst (adjointKernel k) α H := by
  intro x x' y
  change ‖star (k (y,x)) - star (k (y,x'))‖ ≤ _
  rw [← star_sub, norm_star]
  exact hk y x x'

/-- The second-variable conclusion reduces to the first through the genuine
adjoint, preserving the original trace norm and kernel L² norm. -/
lemma secondVariable_of_firstVariable (hfirst : Spec.FirstVariable) : Spec.SecondVariable := by
  intro 𝕜 _ k α H hα hα1 hk
  obtain ⟨ht, hbound⟩ := hfirst 𝕜 (adjointKernel k) α H hα hα1
    (holderSecond_adjointKernel k α H hk)
  have hT : IsHilbertSchmidt (Spec.kernel (adjointKernel k)) :=
    (TraceIdeals.HilbertSchmidtKernels.kernel_isometry Spec.μ Spec.μ
      (Spec.kernelClass (adjointKernel k))).1
  obtain ⟨hTC, hnorm⟩ := traceClass_adjoint_norm _ hT ht
  rw [adjointKernel_operator, ContinuousLinearMap.adjoint_adjoint] at hTC hnorm
  rw [adjointKernel_norm, adjointKernel_operator] at hbound
  change TraceIdeals.TraceClassDefinitions.traceNorm
    (ContinuousLinearMap.adjoint (Spec.kernel k)) ≤ _ at hbound
  rw [← hnorm] at hbound
  exact ⟨hTC, hbound⟩

open scoped InnerProductSpace
open MeasureTheory.Measure
open ExpandedFA.PartV.L2Kernel (kernelOperator)
open ExpandedFA.PartV.L2KernelCompact (kernelAssignment)
open ExpandedFA.PartV.L2HilbertSchmidt (productVector)

lemma unitInterval_mass : Spec.μ Set.univ = 1 := by
  change (volume.comap (Subtype.val : Spec.I → ℝ)) Set.univ = 1
  rw [comap_subtype_coe_apply measurableSet_Icc, Set.image_univ, Subtype.range_coe,
    Real.volume_Icc]
  norm_num

lemma unitSquare_mass : (Spec.μ.prod Spec.μ) Set.univ = 1 := by
  rw [← Set.univ_prod_univ, Measure.prod_prod, unitInterval_mass, mul_one]

lemma ae_lt_one : ∀ᵐ (x : Spec.I) ∂Spec.μ, (x : ℝ) < 1 := by
  have hz : Spec.μ {x : Spec.I | (x : ℝ) = 1} = 0 := by
    rw [show Spec.μ = volume.comap (Subtype.val : Spec.I → ℝ) from rfl,
      comap_subtype_coe_apply measurableSet_Icc]
    apply measure_mono_null (t := {1})
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · exact measure_singleton 1
  rw [ae_iff]
  apply measure_mono_null (t := {x : Spec.I | (x : ℝ) = 1}) _ hz
  intro x hx
  exact le_antisymm x.property.2 (not_lt.mp hx)

/-- Left endpoints of the equal cells, as points of the compact interval. -/
def cellSample (n : ℕ) (i : Fin n) : Spec.I :=
  ⟨(i.val : ℝ) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
    constructor
    · positivity
    · exact (div_le_one hn).mpr (by exact_mod_cast i.isLt.le)⟩

lemma cell_unique (n : ℕ) (i j : Fin n) (x : Spec.I)
    (hi : x ∈ Spec.cell n i) (hj : x ∈ Spec.cell n j) : i = j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi' : (i.val : ℝ) ≤ (x : ℝ) * n ∧ (x : ℝ) * n < (i.val : ℝ) + 1 :=
    ⟨(div_le_iff₀ hn).mp hi.1, (lt_div_iff₀ hn).mp hi.2⟩
  have hj' : (j.val : ℝ) ≤ (x : ℝ) * n ∧ (x : ℝ) * n < (j.val : ℝ) + 1 :=
    ⟨(div_le_iff₀ hn).mp hj.1, (lt_div_iff₀ hn).mp hj.2⟩
  apply Fin.ext
  have : (i.val : ℝ) < (j.val : ℝ) + 1 ∧ (j.val : ℝ) < (i.val : ℝ) + 1 := by constructor <;> linarith
  have h₁ : i.val < j.val + 1 := by exact_mod_cast this.1
  have h₂ : j.val < i.val + 1 := by exact_mod_cast this.2
  omega

lemma exists_cell (n : ℕ) (hn : 0 < n) (x : Spec.I) (hx : (x : ℝ) < 1) :
    ∃ i : Fin n, x ∈ Spec.cell n i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnon : 0 ≤ (x : ℝ) * n := mul_nonneg x.property.1 hn'.le
  have hi : ⌊(x : ℝ) * n⌋₊ < n := (Nat.floor_lt hnon).mpr (by nlinarith)
  refine ⟨⟨_, hi⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hn').mpr (Nat.floor_le hnon)
  · exact (lt_div_iff₀ hn').mpr (Nat.lt_floor_add_one _)

lemma cell_distance (n : ℕ) (i : Fin n) (x : Spec.I) (hx : x ∈ Spec.cell n i) :
    |(x : ℝ) - (cellSample n i : ℝ)| ≤ (n : ℝ)⁻¹ := by
  change |(x : ℝ) - (i.val : ℝ) / n| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have h : ((i.val : ℝ) + 1) / n = (i.val : ℝ) / n + (n : ℝ)⁻¹ := by
    rw [add_div, one_div]
  linarith [hx.2]

/-- Continuous sections used for the sampled finite-rank kernel. -/
def sampleSection {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) (i : Fin n) : C(Spec.I, 𝕜) :=
  k.comp ⟨fun y => (cellSample n i, y), continuous_const.prodMk continuous_id⟩

def sampleTensor {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) (i : Fin n) : Lp 𝕜 2 (Spec.μ.prod Spec.μ) :=
  productVector Spec.μ Spec.μ (Spec.cellVector n i)
    (star (ContinuousMap.toLp (𝕜 := 𝕜) 2 Spec.μ (sampleSection k n i)))

def sampledKernel {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) : Lp 𝕜 2 (Spec.μ.prod Spec.μ) := ∑ i : Fin n, sampleTensor k n i

lemma sampleTensor_coe {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) (i : Fin n) :
    (sampleTensor k n i : Spec.I × Spec.I → 𝕜) =ᵐ[Spec.μ.prod Spec.μ]
      fun p => (Spec.cell n i).indicator (fun _ => (1 : 𝕜)) p.1 * k (cellSample n i, p.2) := by
  have hv : (Spec.cellVector n i : Spec.I → 𝕜) =ᵐ[Spec.μ]
      (Spec.cell n i).indicator (fun _ => (1 : 𝕜)) := MemLp.coeFn_toLp _
  have hu := Lp.coeFn_star (ContinuousMap.toLp (𝕜 := 𝕜) 2 Spec.μ (sampleSection k n i))
  have hc := ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ := Spec.μ) (sampleSection k n i)
  filter_upwards [ExpandedFA.PartV.L2HilbertSchmidt.productVector_coe Spec.μ Spec.μ
    (Spec.cellVector n i) (star (ContinuousMap.toLp (𝕜 := 𝕜) 2 Spec.μ (sampleSection k n i))),
    (quasiMeasurePreserving_fst (μ := Spec.μ) (ν := Spec.μ)).ae_eq_comp hv,
    (quasiMeasurePreserving_snd (μ := Spec.μ) (ν := Spec.μ)).ae_eq_comp hu,
    (quasiMeasurePreserving_snd (μ := Spec.μ) (ν := Spec.μ)).ae_eq_comp hc]
    with p hp hv hu hc
  change (productVector Spec.μ Spec.μ _ _ : Spec.I × Spec.I → 𝕜) p = _
  simp only [Function.comp_apply, Pi.star_apply] at hv hu hc
  rw [hp, hv, hu, hc]
  change (Spec.cell n i).indicator (fun _ => (1 : 𝕜)) p.1 *
    star (star ((sampleSection k n i) p.2)) = _
  rw [star_star]
  rfl

lemma sampledKernel_coe {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜)) (n : ℕ) :
    (sampledKernel k n : Spec.I × Spec.I → 𝕜) =ᵐ[Spec.μ.prod Spec.μ]
      fun p => ∑ i : Fin n, (Spec.cell n i).indicator (fun _ => (1 : 𝕜)) p.1 *
        k (cellSample n i, p.2) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (sampleTensor k n),
    (ae_all_iff).mpr (fun i => sampleTensor_coe k n i)] with p hp h
  exact hp.trans (Finset.sum_congr rfl (fun i _ => h i))

lemma sampledKernel_value {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) (i : Fin n) (x y : Spec.I) (hx : x ∈ Spec.cell n i) :
    (∑ j : Fin n, (Spec.cell n j).indicator (fun _ => (1 : 𝕜)) x *
      k (cellSample n j, y)) = k (cellSample n i, y) := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hji
    have hj : x ∉ Spec.cell n j := fun hj => hji (cell_unique n j i x hj hx)
    simp [hj]
  · simp

lemma sampledKernel_error {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (α H : ℝ) (hα : 0 ≤ α) (hk : Spec.HolderFirst k α H) (n : ℕ) (hn : 0 < n) :
    ‖Spec.kernelClass k - sampledKernel k n‖ ≤ H * (n : ℝ) ^ (-α) := by
  have hH := holderFirst_nonneg k α H hk
  have hC : 0 ≤ H * (n : ℝ) ^ (-α) := by positivity
  have hbound : ∀ᵐ p ∂Spec.μ.prod Spec.μ,
      ‖(Spec.kernelClass k - sampledKernel k n) p‖ ≤ H * (n : ℝ) ^ (-α) := by
    filter_upwards [Lp.coeFn_sub (Spec.kernelClass k) (sampledKernel k n),
      ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ := Spec.μ.prod Spec.μ) k,
      sampledKernel_coe k n, (quasiMeasurePreserving_fst (μ := Spec.μ) (ν := Spec.μ)).ae ae_lt_one]
      with p hp hk' hs hx
    rw [hp, Pi.sub_apply, hk', hs]
    obtain ⟨i, hi⟩ := exists_cell n hn p.1 hx
    rw [sampledKernel_value k n i p.1 p.2 hi]
    calc
      _ ≤ H * |(p.1 : ℝ) - (cellSample n i : ℝ)| ^ α := hk _ _ _
      _ ≤ H * ((n : ℝ)⁻¹) ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (cell_distance n i p.1 hi) hα) hH
      _ = _ := by rw [Real.inv_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ)), Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  simpa [measureUnivNNReal, unitSquare_mass] using Lp.norm_le_of_ae_bound hC hbound

lemma kernelOperator_productVector {𝕜 : Type} [RCLike 𝕜]
    (v u f : Spec.L2 𝕜) :
    kernelOperator Spec.μ Spec.μ (productVector Spec.μ Spec.μ v u) f = ⟪u, f⟫_𝕜 • v := by
  apply ext_inner_left 𝕜
  intro w
  rw [← ExpandedFA.PartV.L2HilbertSchmidt.productVector_coefficient,
    ExpandedFA.PartV.L2HilbertSchmidt.productVector_inner, inner_smul_right, mul_comm]

lemma sampledKernel_range {𝕜 : Type} [RCLike 𝕜] (k : C(Spec.I × Spec.I, 𝕜))
    (n : ℕ) (f : Spec.L2 𝕜) :
    kernelOperator Spec.μ Spec.μ (sampledKernel k n) f ∈ Spec.stepSubspace 𝕜 n := by
  classical
  change kernelAssignment Spec.μ Spec.μ (∑ i : Fin n, sampleTensor k n i) f ∈ _
  rw [_root_.map_sum, _root_.sum_apply]
  apply Submodule.sum_mem
  intro i _
  change kernelOperator Spec.μ Spec.μ (productVector Spec.μ Spec.μ _ _) f ∈ _
  rw [kernelOperator_productVector]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

lemma projection_square_le_error {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (M : Submodule 𝕜 F) [M.HasOrthogonalProjection] (T A : E →L[𝕜] F)
    (hA : ∀ x, A x ∈ M) :
    hilbertSchmidtSquare ((ContinuousLinearMap.id 𝕜 F - M.starProjection).comp T) ≤
      hilbertSchmidtSquare (T-A) := by
  obtain ⟨S,hS⟩ := ExpandedFA.Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset 𝕜 E
  rw [square_in_basis _ (Subtype.val : S → E) hS,
    square_in_basis _ (Subtype.val : S → E) hS]
  apply ENNReal.tsum_le_tsum
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (norm_nonneg _)
  change ‖T x.val - M.starProjection (T x.val)‖ ≤ ‖T x.val - A x.val‖
  rw [Submodule.starProjection_minimal]
  have hb : BddBelow (Set.range (fun y : M => ‖T x.val - (y : F)‖)) :=
    ⟨0, by rintro _ ⟨y,rfl⟩; exact norm_nonneg _⟩
  exact ciInf_le hb ⟨A x.val, hA x.val⟩

/-- The cell projection has no larger Hilbert–Schmidt error than the sampled
step kernel. The comparison uses only orthogonal projection minimality. -/
theorem averaging_error : Spec.AveragingError := by
  intro 𝕜 _ k α H hα _ hk n hn
  refine ⟨cellProjection_rank_le 𝕜 n, ?_⟩
  let Q := ContinuousLinearMap.id 𝕜 (Spec.L2 𝕜) - Spec.cellProjection 𝕜 n
  let R := Q.comp (Spec.kernel k)
  have hT : IsHilbertSchmidt (Spec.kernel k) :=
    (TraceIdeals.HilbertSchmidtKernels.kernel_isometry Spec.μ Spec.μ (Spec.kernelClass k)).1
  have hR : IsHilbertSchmidt R := postcomp_finiteness _ Q hT
  refine ⟨hR, ?_⟩
  have herr : kernelOperator Spec.μ Spec.μ (Spec.kernelClass k - sampledKernel k n) =
      Spec.kernel k - kernelOperator Spec.μ Spec.μ (sampledKernel k n) :=
    map_sub (kernelAssignment Spec.μ Spec.μ) _ _
  have hsq := projection_square_le_error (Spec.stepSubspace 𝕜 n) (Spec.kernel k)
    (kernelOperator Spec.μ Spec.μ (sampledKernel k n)) (sampledKernel_range k n)
  change hilbertSchmidtSquare R ≤ _ at hsq
  rw [← herr, ExpandedFA.PartV.L2HilbertSchmidt.kernel_square_norm] at hsq
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsq
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ← square_of_norm ⟨R, hR⟩] at hr
  exact (le_of_sq_le_sq hr (norm_nonneg _)).trans
    (sampledKernel_error k α H (by linarith) hk n hn)

/-- The quantitative first-variable Hölder trace-class criterion. -/
theorem firstVariable : Spec.FirstVariable := firstVariable_of_averaging_error averaging_error

/-- The same criterion for Hölder regularity in the second variable. -/
theorem secondVariable : Spec.SecondVariable := secondVariable_of_firstVariable firstVariable

end ExpandedFA.IntegralOperators.HolderSingularTail
