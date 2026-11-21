import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.Perm

/-! Completed complex Hilbert exterior powers, realized in square-summable
subset coordinates with the Gram determinant normalization. The induced
operators are constructed from actual summable singular expansions, including
the full kernels, then identified with the unique continuous exterior functor.
Their canonical trace norms give factorial bounds and the defining Fredholm
series converges absolutely. No normality or separability is assumed. -/
noncomputable section
universe u v w z
namespace ExpandedFA.FredholmDeterminant.TraceClassDefinitions

abbrev algebraicExteriorMap := @Spec.AlgebraicExteriorMapValue
abbrev principalMinor := @Spec.PrincipalMinorValue
abbrev exteriorTrace := @Spec.ExteriorTraceValue
abbrev fredholmDeterminant := @Spec.FredholmDeterminantValue

theorem exterior_zero_scalar_identity : Spec.ExteriorZeroScalarIdentity.{v} := by
  intro H _ _ T
  exact exteriorPower.zeroEquiv_naturality T.toLinearMap

theorem exterior_one_identity : Spec.ExteriorOneIdentity.{v} := by
  intro H _ _ T
  exact exteriorPower.oneEquiv_naturality T.toLinearMap

theorem exterior_matrix_coefficient : Spec.ExteriorMatrixCoefficient.{v} := by
  intro H _ _ n T x y
  simp only [Spec.AlgebraicExteriorMapValue, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  exact Matrix.det_transpose _

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type w} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)

@[simp] lemma principalMinor_empty : principalMinor b T ∅ = 1 := by
  classical
  exact Matrix.det_isEmpty

@[simp] lemma principalMinor_singleton (i : ι) :
    principalMinor b T {i} = inner ℂ (b i) (T (b i)) := by
  classical
  let : Unique ({i} : Finset ι) := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by intro j; apply Subtype.ext; exact Finset.mem_singleton.mp j.property }
  exact Matrix.det_unique _

variable [CompleteSpace H]

theorem scalar_identity_trace : Spec.ScalarIdentityTrace := by
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := ℂ)
  have h := b.tsum_inner_mul_inner (1 : ℂ) 1
  simpa [Spec.ScalarIdentityTrace, TraceIdeals.TraceClassDefinitions.Spec.TraceValue,
    b, inner, RCLike.inner_apply] using h

theorem exterior_trace_zero : Spec.ExteriorTraceZero.{v} := by
  intro H _ _ _ T
  classical
  let e : Set.powersetCard
      (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℂ) (H := H)) 0 :=
    ⟨∅, rfl⟩
  have he (s : Set.powersetCard
      (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℂ) (H := H)) 0) :
      s = e := by
    apply Subtype.ext
    exact Finset.card_eq_zero.mp s.property
  change (∑' s : Set.powersetCard
      (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℂ) (H := H)) 0,
    principalMinor (TraceIdeals.TraceClassDefinitions.Spec.chosenBasis
      (𝕜 := ℂ) (H := H)) T s.val) = 1
  rw [tsum_eq_single e (fun s hs => (hs (he s)).elim)]
  exact principalMinor_empty _ T

theorem exterior_trace_one : Spec.ExteriorTraceOne.{v} := by
  intro H _ _ _ T
  classical
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  let e := Set.powersetCard.ofSingleton (α :=
    TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℂ) (H := H))
  change (∑' s : Set.powersetCard _ 1, principalMinor b T s.val) =
    ∑' i, inner ℂ (b i) (T (b i))
  rw [← e.tsum_eq (fun s => principalMinor b T s.val)]
  apply tsum_congr
  intro i
  exact principalMinor_singleton b T i

theorem determinant_at_zero : Spec.DeterminantAtZero.{v} := by
  intro H _ _ _ T
  change (∑' n : ℕ, (0 : ℂ) ^ n * exteriorTrace T n) = 1
  rw [tsum_eq_single 0]
  · simpa using exterior_trace_zero H T
  · intro n hn
    simp [zero_pow hn]

theorem factorial_series_majorant : Spec.FactorialSeriesMajorant := by
  intro a C _ hC z
  have hle (n : ℕ) : ‖z ^ n * a n‖ ≤ (‖z‖ * C) ^ n / (n.factorial : ℝ) := by
    calc
      _ = ‖z‖ ^ n * ‖a n‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖z‖ ^ n * (C ^ n / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hC n) (pow_nonneg (norm_nonneg z) n)
      _ = _ := by rw [← mul_div_assoc, ← mul_pow]
  have hmajorant := Real.summable_pow_div_factorial (‖z‖ * C)
  have habs := hmajorant.of_nonneg_of_le (fun n => norm_nonneg _) hle
  refine ⟨habs, (norm_tsum_le_tsum_norm habs).trans ?_⟩
  calc
    (∑' n, ‖z ^ n * a n‖) ≤ ∑' n : ℕ, (‖z‖ * C) ^ n / (n.factorial : ℝ) :=
      habs.tsum_le_tsum hle hmajorant
    _ = Real.exp (‖z‖ * C) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

namespace SummableExpansion

/-! These results construct compactness and canonical trace class from actual
norm-convergent expansion data. No trace-class certificate or sorting of the
weights is assumed; orthonormal factors give the exact trace norm. -/

variable {𝕜 : Type u} [RCLike 𝕜]
 {X : Type v} {Y : Type w}
 [NormedAddCommGroup X] [NormedAddCommGroup Y]
 [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]

lemma sum_inner_bound {I : Type z} {e : I → X} {f : I → Y}
    (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (u : Y) (v : X) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s : Finset I) :
    ∑ i ∈ s, ‖inner 𝕜 v (e i)‖ * ‖inner 𝕜 (f i) u‖ ≤ 1 := by
  have hp (i : I) : ‖inner 𝕜 v (e i)‖ * ‖inner 𝕜 (f i) u‖ ≤
      (‖inner 𝕜 (e i) v‖ ^ 2 + ‖inner 𝕜 (f i) u‖ ^ 2) / 2 := by
    rw [norm_inner_symm v]
    nlinarith [sq_nonneg (‖inner 𝕜 (e i) v‖ - ‖inner 𝕜 (f i) u‖)]
  calc
    _ ≤ ∑ i ∈ s, (‖inner 𝕜 (e i) v‖ ^ 2 + ‖inner 𝕜 (f i) u‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = ((∑ i ∈ s, ‖inner 𝕜 (e i) v‖ ^ 2) +
        ∑ i ∈ s, ‖inner 𝕜 (f i) u‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ 1 := by
      have h₁ := he.sum_inner_products_le (s := s) v
      have h₂ := hf.sum_inner_products_le (s := s) u
      rw [hv] at h₁
      rw [hu] at h₂
      nlinarith


lemma compact_of_expansion [CompleteSpace Y] {I : Type z}
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (T : X →L[𝕜] Y)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) :
    IsCompactOperator T := by
  classical
  let F : I → X →L[𝕜] Y := fun j => (a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j)
  have hnorm (j : I) : ‖F j‖ = a j := by
    simp [F, norm_smul, InnerProductSpace.norm_rankOne, he j, hf j,
      abs_of_nonneg (ha j)]
  have hs : Summable F := (hsum.congr (fun j => (hnorm j).symm)).of_norm
  have heq : (∑' j, F j) = T := by
    ext x
    have hh := hs.hasSum.mapL (ContinuousLinearMap.apply 𝕜 Y x)
    exact hh.unique (by simpa [F, smul_apply, smul_smul] using hexp x)
  rw [← heq]
  apply isCompactOperator_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : X → Y))
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs]
    apply IsCompactOperator.add _ ih
    change IsCompactOperator ((a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j))
    apply IsCompactOperator.smul
    exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (e j))).clm_comp
      (ContinuousLinearMap.toSpanSingleton 𝕜 (f j))

lemma finite_singular_bound {I J : Type*}
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : J → X) (f : J → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (T : X →L[𝕜] Y)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x))
    (b : I → ℝ) (hb : ∀ i, 0 ≤ b i)
    (E : I → X) (F : I → Y) (hE : Orthonormal 𝕜 E) (hF : Orthonormal 𝕜 F)
    (hmap : ∀ i, T (E i) = (b i : 𝕜) • F i) (s : Finset I) :
    ∑ i ∈ s, b i ≤ ∑' j, a j := by
  let q : I → J → ℝ := fun i j => a j * ‖inner 𝕜 (e j) (E i)‖ * ‖inner 𝕜 (F i) (f j)‖
  have hq0 (i : I) (j : J) : 0 ≤ q i j := by exact mul_nonneg (mul_nonneg (ha j) (norm_nonneg _)) (norm_nonneg _)
  have hinner₁ (i : I) (j : J) : ‖inner 𝕜 (e j) (E i)‖ ≤ 1 := by
    simpa [he j, hE.norm_eq_one i] using norm_inner_le_norm (𝕜 := 𝕜) (e j) (E i)
  have hinner₂ (i : I) (j : J) : ‖inner 𝕜 (F i) (f j)‖ ≤ 1 := by
    simpa [hf j, hF.norm_eq_one i] using norm_inner_le_norm (𝕜 := 𝕜) (F i) (f j)
  have hqle (i : I) (j : J) : q i j ≤ a j := by
    dsimp [q]
    calc
      _ ≤ a j * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hinner₁ i j) (ha j)) (hinner₂ i j)
        (norm_nonneg _) (by simpa using ha j)
      _ = a j := by ring
  have hqs (i : I) : Summable (q i) := hsum.of_nonneg_of_le (hq0 i) (hqle i)
  have hbi (i : I) : b i ≤ ∑' j, q i j := by
    let d : J → 𝕜 := fun j => (a j : 𝕜) * inner 𝕜 (e j) (E i) * inner 𝕜 (F i) (f j)
    have hnorm (j : J) : ‖d j‖ = q i j := by
      simp [d, q, norm_mul, abs_of_nonneg (ha j)]
    have hd : Summable (fun j => ‖d j‖) := (hqs i).congr (fun j => (hnorm j).symm)
    have hdx : HasSum d (b i : 𝕜) := by
      have hx := (hexp (E i)).mapL (innerSL 𝕜 (F i))
      convert hx using 1
      · ext j
        simp only [d, innerSL_apply_apply, inner_smul_right]
      · simp [hmap i, hF.norm_eq_one i]
    calc
      b i = ‖(b i : 𝕜)‖ := by simp [abs_of_nonneg (hb i)]
      _ = ‖∑' j, d j‖ := congrArg norm hdx.tsum_eq.symm
      _ ≤ ∑' j, ‖d j‖ := norm_tsum_le_tsum_norm hd
      _ = _ := tsum_congr hnorm
  have hcol (j : J) : (∑ i ∈ s, q i j) ≤ a j := by
    calc
      _ = a j * (∑ i ∈ s, ‖inner 𝕜 (e j) (E i)‖ * ‖inner 𝕜 (F i) (f j)‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [q]
        ring
      _ ≤ a j * 1 := mul_le_mul_of_nonneg_left
        (sum_inner_bound hE hF (f j) (e j) (hf j) (he j) s) (ha j)
      _ = _ := mul_one _
  have hcols : Summable (fun j => ∑ i ∈ s, q i j) :=
    hsum.of_nonneg_of_le (fun j => Finset.sum_nonneg (fun i _ => hq0 i j)) hcol
  calc
    _ ≤ ∑ i ∈ s, ∑' j, q i j := Finset.sum_le_sum (fun i _ => hbi i)
    _ = ∑' j, ∑ i ∈ s, q i j := (Summable.tsum_finsetSum (fun i _ => hqs i)).symm
    _ ≤ ∑' j, a j := hcols.tsum_le_tsum hcol hsum

lemma traceClass_of_expansion [CompleteSpace X] [CompleteSpace Y] {I : Type z}
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (T : X →L[𝕜] Y)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ≤ ∑' j, a j := by
  let hT := compact_of_expansion a ha hsum e f he hf T hexp
  have hTc : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator T.toLinearMap).mpr hT
  obtain ⟨S⟩ := ExpandedFA.CompactSpectral.SingularExpansion.compact_singular_system 𝕜 X Y T hTc
  have hb (s : Finset S.Index) : ∑ i ∈ s, S.sigma i ≤ ∑' j, a j :=
    finite_singular_bound a ha hsum e f he hf T hexp S.sigma
      (fun i => (S.positive i).le) S.rightVector S.leftVector
      S.right_orthonormal S.left_orthonormal S.map_right s
  have hσ : Summable S.sigma := summable_of_sum_le (fun i => (S.positive i).le) hb
  open ExpandedFA.CompactSpectral ExpandedFA.TraceIdeals.TraceClassDefinitions in
  have hc : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T := by
    let eσ := singularIndexEquiv T hTc S
    have hval (j : S.Index) : SingularApproximation.Spec.SingularValueValue T (eσ j).val =
        S.sigma j := singularIndexEquiv_value T hTc S j
    have hsub : Summable (fun n : positiveIndices T =>
        SingularApproximation.Spec.SingularValueValue T n.val) :=
      eσ.summable_iff.mp (hσ.congr (fun j => (hval j).symm))
    have hfull : Summable (SingularApproximation.Spec.SingularValueValue T) :=
      ((hasSum_subtype_iff_of_support_subset (positiveIndices_support T hTc)).mp
        hsub.hasSum).summable
    exact ⟨hTc, (summable_nat_add_iff 1).mpr hfull⟩
  refine ⟨hc, ?_⟩
  rw [← (ExpandedFA.TraceIdeals.TraceClassDefinitions.singularSystem_sum 𝕜 X Y T hc S).2]
  exact Real.tsum_le_of_sum_le (fun i => (S.positive i).le) hb

lemma traceNorm_eq_of_orthonormal_expansion [CompleteSpace X] [CompleteSpace Y] {I : Type z}
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (T : X →L[𝕜] Y)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T = ∑' j, a j := by
  have hc := traceClass_of_expansion a ha hsum e f he.norm_eq_one hf.norm_eq_one T hexp
  have hmap (j : I) : T (e j) = (a j : 𝕜) • f j := by
    rw [← (hexp (e j)).tsum_eq, tsum_eq_single j]
    · simp [he.norm_eq_one j]
    · intro k hkj
      simp [he.inner_eq_zero hkj]
  obtain ⟨S⟩ := ExpandedFA.CompactSpectral.SingularExpansion.compact_singular_system 𝕜 X Y T hc.1.1
  obtain ⟨hσ, hnorm⟩ := ExpandedFA.TraceIdeals.TraceClassDefinitions.singularSystem_sum 𝕜 X Y T hc.1 S
  have hb (s : Finset I) : ∑ j ∈ s, a j ≤ ∑' i, S.sigma i :=
    finite_singular_bound S.sigma (fun i => (S.positive i).le) hσ
      S.rightVector S.leftVector S.right_orthonormal.norm_eq_one
      S.left_orthonormal.norm_eq_one T S.expansion a ha e f he hf hmap s
  refine ⟨hc.1, le_antisymm hc.2 ?_⟩
  rw [← hnorm]
  exact Real.tsum_le_of_sum_le ha hb

end SummableExpansion

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
open scoped lp Classical
variable {α H : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] lemma embed_ιMulti (b : HilbertBasis α ℂ H) (x : Fin n → H) :
    embed b (exteriorPower.ιMulti ℂ n x) = wedgeAlternating b x :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

lemma wedge_basis (b : HilbertBasis α ℂ H) (t : Set.powersetCard α n) :
    wedgeAlternating b (fun j => b (enumeration t j)) = lp.single 2 t (1 : ℂ) := by
  classical
  apply lp.ext
  funext s
  rw [wedgeAlternating_apply, lp.single_apply]
  by_cases hst : s = t
  · subst t
    rw [Pi.single_eq_same]
    suffices (fun i j : Fin n => b.repr (b (enumeration s i)) (enumeration s j)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) by rw [this, Matrix.det_one]
    ext i j
    rw [b.repr_apply_apply, (orthonormal_iff_ite.mp b.orthonormal)]
    simp [Matrix.one_apply, (enumeration s).injective.eq_iff, eq_comm]
  · rw [Pi.single_eq_of_ne hst]
    obtain ⟨a, hat, has⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp
      (Ne.symm hst)
    obtain ⟨j, hj⟩ := (enumeration_range t).symm.subset hat
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro k
    rw [b.repr_apply_apply, b.orthonormal.inner_eq_zero]
    intro heq
    apply has
    rw [← hj, ← heq]
    exact (enumeration_range s).subset ⟨k, rfl⟩

lemma basis_eq_wedge (b : HilbertBasis α ℂ H) (t : Set.powersetCard α n) :
    basis α n t = wedgeAlternating b (fun j => b (enumeration t j)) := by
  rw [wedge_basis]
  change (LinearIsometryEquiv.refl ℂ (Space α n)).symm _ = _
  apply (LinearIsometryEquiv.refl ℂ (Space α n)).symm_apply_eq.mpr
  rw [LinearIsometryEquiv.coe_refl, id_eq]
  apply lp.ext
  funext i
  by_cases h : i = t <;> simp [lp.single_apply, Pi.single_apply, h]


lemma dense_wedges (b : HilbertBasis α ℂ H) :
    (Submodule.span ℂ (Set.range (fun x : Fin n → H => wedgeAlternating b x))).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← (basis α n).dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨(fun j => b (enumeration s j)), (basis_eq_wedge b s).symm⟩

end ExteriorCoordinates


open scoped BigOperators lp Classical
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
lemma tsum_fin_prod {α : Type*} (n : ℕ) (f : Fin n → α → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) (hs : ∀ i, Summable (f i)) :
    (∑' a : Fin n → α, ∏ i, f i (a i)) = ∏ i, ∑' a, f i a := by
  induction n with
  | zero => simp
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n+1) => α)
      have htail := summable_fin_prod n (fun i => f i.succ) (fun i => hf i.succ) (fun i => hs i.succ)
      have hprod := (hs 0).mul_of_nonneg htail (hf 0)
        (fun a => Finset.prod_nonneg (fun i _ => hf i.succ (a i)))
      calc
        _ = ∑' p : α × (Fin n → α), f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
          rw [← e.tsum_eq]
          apply tsum_congr
          intro p
          simp [e, Fin.consEquiv, Fin.prod_univ_succ]
        _ = (∑' a, f 0 a) * ∑' a : Fin n → α, ∏ i, f i.succ (a i) :=
          ((hs 0).tsum_mul_tsum htail hprod).symm
        _ = _ := by rw [ih _ (fun i => hf i.succ) (fun i => hs i.succ), Fin.prod_univ_succ]
end ExteriorCoordinates
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
open scoped lp
lemma lp_tuple_restrict_norm_le {α β : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℂ))
    (g : β → (Fin n → α)) (hg : Function.Injective g)
    (u : ℓ²(β, ℂ)) (hu : ∀ b, u b = ∏ i, f i (g b i)) :
    ‖u‖ ≤ ∏ i, ‖f i‖ := by
  have hs (i : Fin n) : Summable (fun a => ‖f i a‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f i).property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have hp (i : Fin n) : (∑' a, ‖f i a‖ ^ 2) = ‖f i‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (f i)).symm
  have htotal : (∑' a : Fin n → α, ∏ i, ‖f i (a i)‖ ^ 2) = (∏ i, ‖f i‖) ^ 2 := by
    rw [tsum_fin_prod n (fun i a => ‖f i a‖ ^ 2) (fun i a => sq_nonneg _) hs]
    simp_rw [hp]
    rw [← Finset.prod_pow]
  apply lp.norm_le_of_tsum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [hu, norm_prod, ← Finset.prod_pow]
  have hsum := summable_fin_prod n (fun i a => ‖f i a‖ ^ 2) (fun i a => sq_nonneg _) hs
  exact (tsum_comp_le_tsum_of_inj hsum
    (fun a => Finset.prod_nonneg (fun i _ => sq_nonneg _)) hg).trans_eq (by simpa only [← Finset.prod_pow] using htotal)
end ExteriorCoordinates
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
open scoped lp

def tupleRestriction {α β : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℂ))
    (g : β → (Fin n → α)) (hg : Function.Injective g) : ℓ²(β, ℂ) := by
  refine ⟨(fun b => ∏ i, f i (g b i)), ?_⟩
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_prod, ← Finset.prod_pow]
  apply (summable_fin_prod n (fun i a => ‖f i a‖ ^ 2) (fun i a => sq_nonneg _) ?_).comp_injective hg
  intro i
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (f i).property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

lemma tupleRestriction_norm_le {α β : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℂ))
    (g : β → (Fin n → α)) (hg : Function.Injective g) :
    ‖tupleRestriction f g hg‖ ≤ ∏ i, ‖f i‖ :=
  lp_tuple_restrict_norm_le f g hg _ (fun _ => rfl)

lemma permutedEnumeration_injective {α : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun s : Set.powersetCard α n => fun i => enumeration s (σ i)) := by
  intro s t hst
  apply enumeration_injective
  funext i
  have hh := congrFun hst (σ.symm i)
  simpa using hh

def monomial {α : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℂ)) (σ : Equiv.Perm (Fin n)) :
    Space α n := tupleRestriction f _ (permutedEnumeration_injective σ)

lemma norm_monomial_le {α : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℂ)) (σ : Equiv.Perm (Fin n)) :
    ‖monomial f σ‖ ≤ ∏ i, ‖f i‖ := tupleRestriction_norm_le f _ _

variable {H α : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma wedge_eq_sum_monomial (b : HilbertBasis α ℂ H) (x : Fin n → H) :
    wedgeAlternating b x = ∑ σ : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • monomial (fun i => b.repr (x i)) σ) := by
  apply lp.ext
  funext s
  simp only [wedgeAlternating_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, monomial, tupleRestriction]
  exact (Matrix.det_transpose (fun i j : Fin n => b.repr (x j) (enumeration s i))).trans
    (Matrix.det_apply' _)

lemma norm_wedge_le (b : HilbertBasis α ℂ H) (x : Fin n → H) :
    ‖wedgeAlternating b x‖ ≤ (n.factorial : ℝ) * ∏ i, ‖x i‖ := by
  rw [wedge_eq_sum_monomial]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖(((Equiv.Perm.sign σ : ℤ) : ℂ) •
        monomial (fun i => b.repr (x i)) σ)‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ i, ‖x i‖ := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [norm_smul, hsign, one_mul]
      simpa using norm_monomial_le (fun i => b.repr (x i)) σ
    _ = _ := by simp [Fintype.card_perm]
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {H α : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def continuousWedgeAlternating (b : HilbertBasis α ℂ H) : H [⋀^Fin n]→L[ℂ] Space α n :=
  (wedgeAlternating b).mkContinuous (n.factorial : ℝ) (norm_wedge_le b)

@[simp] lemma continuousWedgeAlternating_apply (b : HilbertBasis α ℂ H) (x : Fin n → H) :
    continuousWedgeAlternating b x = wedgeAlternating b x := rfl
end ExteriorCoordinates



open scoped BigOperators lp Classical
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma clm_ext_hilbertBasis (b : HilbertBasis α ℂ H) (f g : H →L[ℂ] E)
    (h : ∀ i, f (b i) = g (b i)) : f = g := by
  have hs : Submodule.span ℂ (Set.range b) ≤ LinearMap.ker (f - g).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (b i) - g (b i) = 0
    exact sub_eq_zero.mpr (h i)
  have hc := (Submodule.span ℂ (Set.range b)).topologicalClosure_minimal hs
    (f-g).isClosed_ker
  rw [b.dense_span] at hc
  ext x
  have hh := hc (show x ∈ (⊤ : Submodule ℂ H) from trivial)
  exact sub_eq_zero.mp hh

lemma cmlm_ext_hilbertBasis (b : HilbertBasis α ℂ H) (n : ℕ)
    (f g : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) E)
    (h : ∀ a : Fin n → α, f (fun i => b (a i)) = g (fun i => b (a i))) : f = g := by
  induction n with
  | zero =>
      ext x
      have hh := h (fun i => Fin.elim0 i)
      convert hh using 1 <;> congr 1 <;> exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
      apply (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (n+1) => H) E).injective
      apply clm_ext_hilbertBasis b
      intro a
      apply ih
      intro v
      rw [continuousMultilinearCurryLeftEquiv_apply, continuousMultilinearCurryLeftEquiv_apply]
      convert h (Fin.cons a v) using 1 <;> congr 1 <;>
        exact (Fin.comp_cons b a v).symm
end ExteriorCoordinates
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α : Type*} {n : ℕ}
lemma exists_enumeration_perm (a : Fin n ↪ α) :
    ∃ (s : Set.powersetCard α n) (p : Equiv.Perm (Fin n)),
      (fun i => enumeration s (p i)) = a := by
  let s : Set.powersetCard α n := ⟨Finset.univ.map a, by simp⟩
  let e : Fin n ≃ s := Equiv.ofBijective
    (fun i => ⟨a i, by simp [s]⟩)
    ⟨fun i j h => a.injective (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hy
      exact ⟨i, Subtype.ext hi⟩⟩
  let p : Equiv.Perm (Fin n) := e.trans (Finset.equivFinOfCardEq s.property)
  refine ⟨s, p, ?_⟩
  funext i
  simp [enumeration, p, e, Equiv.ofBijective]
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def gramAlternating (x : Fin n → H) : H [⋀^Fin n]→L[ℂ] ℂ :=
  { Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi (fun i => (innerSL ℂ (x i)).toLinearMap)) with
    cont := by
      apply Continuous.matrix_det
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (innerSL ℂ (x j)).continuous.comp (continuous_apply i) }

lemma gramAlternating_apply (x y : Fin n → H) :
    gramAlternating x y = Matrix.det (fun i j => inner ℂ (x i) (y j)) := by
  change Matrix.det (fun i j => inner ℂ (x j) (y i)) = _
  exact Matrix.det_transpose _

set_option backward.isDefEq.respectTransparency false in
lemma gram_enumeration (b : HilbertBasis α ℂ H) (x : Fin n → H)
    (s : Set.powersetCard α n) :
    inner ℂ (wedgeAlternating b x)
        (wedgeAlternating b (fun j => b (enumeration s j))) =
      gramAlternating x (fun j => b (enumeration s j)) := by
  rw [wedge_basis, lp.inner_single_right, gramAlternating_apply]
  rw [RCLike.inner_apply, one_mul, wedgeAlternating_apply]
  rw [(starRingEnd ℂ).map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, b.repr_apply_apply, inner_conj_symm]
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H E : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma cam_ext_enumeration (b : HilbertBasis α ℂ H)
    (f g : H [⋀^Fin n]→L[ℂ] E)
    (h : ∀ s : Set.powersetCard α n,
      f (fun j => b (enumeration s j)) = g (fun j => b (enumeration s j))) : f = g := by
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply cmlm_ext_hilbertBasis b
  intro a
  by_cases ha : Function.Injective a
  · obtain ⟨s, p, hp⟩ := exists_enumeration_perm ⟨a, ha⟩
    have hp' : (fun i => b (a i)) = (fun j => b (enumeration s j)) ∘ p := by
      funext i
      exact congrArg b (congrFun hp i).symm
    change f (fun i => b (a i)) = g (fun i => b (a i))
    rw [hp']
    change f.toAlternatingMap ((fun j => b (enumeration s j)) ∘ p) =
      g.toAlternatingMap ((fun j => b (enumeration s j)) ∘ p)
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
    exact congrArg (fun z : E => Equiv.Perm.sign p • z) (h s)
  · have hba : ¬ Function.Injective (fun i => b (a i)) :=
      fun hinj => ha (fun i j hh => hinj (congrArg b hh))
    exact (f.map_eq_zero_of_not_injective _ hba).trans
      (g.map_eq_zero_of_not_injective _ hba).symm
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma inner_wedge (b : HilbertBasis α ℂ H) (x y : Fin n → H) :
    inner ℂ (wedgeAlternating b x) (wedgeAlternating b y) =
      Matrix.det (fun i j => inner ℂ (x i) (y j)) := by
  let f := (innerSL ℂ (wedgeAlternating b x)).compContinuousAlternatingMap
    (continuousWedgeAlternating b)
  have hh : f = gramAlternating x := cam_ext_enumeration b f _ (fun s => gram_enumeration b x s)
  have he := congrArg (fun q : H [⋀^Fin n]→L[ℂ] ℂ => q y) hh
  exact he.trans (gramAlternating_apply x y)
end ExteriorCoordinates


open scoped lp Classical
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α β H : Type*} {n : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orthonormal_wedges (b : HilbertBasis α ℂ H) (u : β → H) (hu : Orthonormal ℂ u) :
    Orthonormal ℂ (fun s : Set.powersetCard β n =>
      wedgeAlternating b (fun j => u (enumeration s j))) := by
  let e : HilbertBasis β ℂ ℓ²(β, ℂ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply orthonormal_iff_ite.mpr
  intro s t
  rw [inner_wedge]
  have hmat : (fun i j : Fin n => inner ℂ (u (enumeration s i)) (u (enumeration t j))) =
      (fun i j : Fin n => inner ℂ (e (enumeration s i)) (e (enumeration t j))) := by
    funext i j
    rw [orthonormal_iff_ite.mp hu, orthonormal_iff_ite.mp e.orthonormal]
  rw [hmat, ← inner_wedge e, ← basis_eq_wedge e s, ← basis_eq_wedge e t]
  exact orthonormal_iff_ite.mp (basis β n).orthonormal s t

def inducedBasisFamily (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H)
    (s : Set.powersetCard β n) : Space α n :=
  wedgeAlternating b (fun j => c (enumeration s j))

lemma inducedBasisFamily_orthonormal (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H) :
    Orthonormal ℂ (inducedBasisFamily (n := n) b c) := by
  apply orthonormal_iff_ite.mpr
  intro s t
  change inner ℂ (wedgeAlternating b (fun j => c (enumeration s j)))
    (wedgeAlternating b (fun j => c (enumeration t j))) = _
  rw [inner_wedge, ← inner_wedge c, ← basis_eq_wedge c s, ← basis_eq_wedge c t]
  exact orthonormal_iff_ite.mp (basis β n).orthonormal s t

lemma inducedBasisFamily_orthogonal_eq_bot (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H) :
    (Submodule.span ℂ (Set.range (inducedBasisFamily (n := n) b c))).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  have hh (s : Set.powersetCard β n) :
      inner ℂ z (inducedBasisFamily b c s) = 0 := by
    exact Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self s)) hz
  let f : H [⋀^Fin n]→L[ℂ] ℂ :=
    (innerSL ℂ z).compContinuousAlternatingMap (continuousWedgeAlternating b)
  have hf : f = 0 := cam_ext_enumeration c f 0 (fun s => hh s)
  have hzero : (innerSL ℂ z) = (0 : Space α n →L[ℂ] ℂ) := by
    apply clm_ext_hilbertBasis (basis α n)
    intro s
    rw [basis_eq_wedge b s]
    exact congrArg (fun F : H [⋀^Fin n]→L[ℂ] ℂ => F (fun j => b (enumeration s j))) hf
  change z = 0
  have hself := congrArg (fun F : Space α n →L[ℂ] ℂ => F z) hzero
  exact inner_self_eq_zero.mp hself

def inducedBasis (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H) :
    HilbertBasis (Set.powersetCard β n) ℂ (Space α n) :=
  HilbertBasis.mkOfOrthogonalEqBot (inducedBasisFamily_orthonormal b c)
    (inducedBasisFamily_orthogonal_eq_bot b c)

@[simp] lemma inducedBasis_apply (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H)
    (s : Set.powersetCard β n) :
    inducedBasis b c s = wedgeAlternating b (fun j => c (enumeration s j)) := by
  change (HilbertBasis.mkOfOrthogonalEqBot _ _) s = _
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

lemma inducedBasis_repr_wedge (b : HilbertBasis α ℂ H) (c : HilbertBasis β ℂ H)
    (s : Set.powersetCard β n) (x : Fin n → H) :
    (inducedBasis b c).repr (wedgeAlternating b x) s =
      Matrix.det (fun i j => inner ℂ (c (enumeration s i)) (x j)) := by
  rw [HilbertBasis.repr_apply_apply, inducedBasis_apply, inner_wedge]

end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {I H E : Type*} {n : ℕ}
  [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E]

lemma alternating_eq_on_family (r : I → H) (f g : H [⋀^Fin n]→ₗ[ℂ] E)
    (h : ∀ s : Set.powersetCard I n,
      f (fun j => r (enumeration s j)) = g (fun j => r (enumeration s j)))
    (a : Fin n → I) : f (fun i => r (a i)) = g (fun i => r (a i)) := by
  by_cases ha : Function.Injective a
  · obtain ⟨s, p, hp⟩ := exists_enumeration_perm ⟨a, ha⟩
    have hp' : (fun i => r (a i)) = (fun j => r (enumeration s j)) ∘ p := by
      funext i
      exact congrArg r (congrFun hp i).symm
    rw [hp', f.map_perm, g.map_perm, h s]
  · have hba : ¬ Function.Injective (fun i => r (a i)) :=
      fun hinj => ha (fun i j hh => hinj (congrArg r hh))
    exact (f.map_eq_zero_of_not_injective _ hba).trans
      (g.map_eq_zero_of_not_injective _ hba).symm
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {I J α β H K : Type*} {n : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma naturality_of_sum_basis
    (b : HilbertBasis α ℂ H) (d : HilbertBasis β ℂ K)
    (c : HilbertBasis (I ⊕ J) ℂ H) (T : H →L[ℂ] K)
    (A : Space α n →L[ℂ] Space β n)
    (hTzero : ∀ j, T (c (Sum.inr j)) = 0)
    (hApos : ∀ s : Set.powersetCard I n,
      A (wedgeAlternating b (fun i => c (Sum.inl (enumeration s i)))) =
        wedgeAlternating d (fun i => T (c (Sum.inl (enumeration s i)))))
    (hAker : ∀ x : Fin n → H,
      (∃ i, ∀ j, inner ℂ (c (Sum.inl j)) (x i) = 0) →
        A (wedgeAlternating b x) = 0)
    (x : Fin n → H) :
    A (wedgeAlternating b x) = wedgeAlternating d (fun i => T (x i)) := by
  let f := A.compContinuousAlternatingMap (continuousWedgeAlternating b)
  let g : H [⋀^Fin n]→L[ℂ] Space β n :=
    (continuousWedgeAlternating d).compContinuousLinearMap T
  suffices hfg : f = g by exact congrArg (fun q : H [⋀^Fin n]→L[ℂ] Space β n => q x) hfg
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply cmlm_ext_hilbertBasis c
  intro a
  change A (wedgeAlternating b (fun i => c (a i))) =
    wedgeAlternating d (fun i => T (c (a i)))
  by_cases hk : ∃ i j, a i = Sum.inr j
  · obtain ⟨i,j,hij⟩ := hk
    rw [hAker _ ⟨i, fun j' => by
      rw [hij]
      exact c.orthonormal.inner_eq_zero (by simp)⟩]
    symm
    apply (wedgeAlternating d).map_coord_zero i
    rw [hij, hTzero]
  · have hleft : ∀ i, ∃ j, a i = Sum.inl j := by
      intro i
      cases h : a i with
      | inl j => exact ⟨j,rfl⟩
      | inr j => exact (hk ⟨i,j,h⟩).elim
    let u (i : Fin n) := Classical.choose (hleft i)
    have hu : (fun i => c (a i)) = (fun i => c (Sum.inl (u i))) := by
      funext i
      exact congrArg c (Classical.choose_spec (hleft i))
    change f (fun i => c (a i)) = g (fun i => c (a i))
    rw [hu]
    exact alternating_eq_on_family (fun j => c (Sum.inl j)) f.toAlternatingMap
      g.toAlternatingMap hApos u
end ExteriorCoordinates
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {I α H : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma inner_wedge_eq_zero_of_slot (b : HilbertBasis α ℂ H) (r : I → H)
    (s : Set.powersetCard I n) (x : Fin n → H)
    (hx : ∃ i, ∀ j, inner ℂ (r j) (x i) = 0) :
    inner ℂ (wedgeAlternating b (fun j => r (enumeration s j))) (wedgeAlternating b x) = 0 := by
  rw [inner_wedge]
  obtain ⟨i,hi⟩ := hx
  exact Matrix.det_eq_zero_of_column_eq_zero i (fun j => hi (enumeration s j))

lemma prod_enumeration {M : Type*} [CommMonoid M] (s : Set.powersetCard I n) (f : I → M) :
    (∏ i, f (enumeration s i)) = ∏ j ∈ s.val, f j := by
  rw [← Finset.prod_coe_sort s.val f]
  exact Fintype.prod_equiv (Finset.equivFinOfCardEq s.property).symm _ _ (fun _ => rfl)

lemma wedge_smul_family (b : HilbertBasis α ℂ H) (r : I → H)
    (a : I → ℝ) (s : Set.powersetCard I n) :
    wedgeAlternating b (fun j => (a (enumeration s j) : ℂ) • r (enumeration s j)) =
      ((∏ j ∈ s.val, a j : ℝ) : ℂ) •
        wedgeAlternating b (fun j => r (enumeration s j)) := by
  rw [AlternatingMap.map_smul_univ, prod_enumeration s (fun j => (a j : ℂ)),
    Complex.ofReal_prod]
end ExteriorCoordinates

abbrev coordinateSpace := @Spec.CoordinateSpaceValue
abbrev coordinateWedge := @Spec.CoordinateWedgeValue
abbrev coordinateEmbedding := @Spec.CoordinateEmbeddingValue

theorem coordinate_wedge_gram : Spec.CoordinateWedgeGram.{v,w} := by
  intro H _ _ ι b n x y
  exact ExteriorCoordinates.inner_wedge b x y

theorem coordinate_wedge_dense : Spec.CoordinateWedgeDense.{v,w} := by
  intro H _ _ ι b n
  exact ExteriorCoordinates.dense_wedges b

theorem coordinate_wedge_continuous : Spec.CoordinateWedgeContinuous.{v,w} := by
  intro H _ _ ι b n
  exact (ExteriorCoordinates.continuousWedgeAlternating (n := n) b).cont

namespace SummableExpansion
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
  {I : Type z}

def rankOneSeries (a : I → ℝ) (e : I → X) (f : I → Y) : X →L[𝕜] Y :=
  ∑' j, (a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j)

lemma summable_weighted_rankOne [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    Summable (fun j => (a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j)) := by
  apply Summable.of_norm
  simpa [norm_smul, InnerProductSpace.norm_rankOne, he, hf, abs_of_nonneg (ha _)] using hsum

lemma rankOneSeries_hasSum [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    HasSum (fun j => (a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j))
      (rankOneSeries (𝕜 := 𝕜) a e f) := (summable_weighted_rankOne (𝕜 := 𝕜) a ha hsum e f he hf).hasSum

lemma rankOneSeries_expansion [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) (x : X) :
    HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (rankOneSeries (𝕜 := 𝕜) a e f x) := by
  have h := (rankOneSeries_hasSum (𝕜 := 𝕜) a ha hsum e f he hf).mapL (ContinuousLinearMap.apply 𝕜 Y x)
  simpa [smul_smul] using h

lemma rankOneSeries_norm_le [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    ‖rankOneSeries (𝕜 := 𝕜) a e f‖ ≤ ∑' j, a j := by
  have hnorm : Summable (fun j => ‖(a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j)‖) := by
    simpa [norm_smul, InnerProductSpace.norm_rankOne, he, hf, abs_of_nonneg (ha _)] using hsum
  simpa [rankOneSeries, norm_smul, InnerProductSpace.norm_rankOne, he, hf,
    abs_of_nonneg (ha _)] using norm_tsum_le_tsum_norm hnorm

lemma rankOneSeries_compact [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    IsCompactOperator (rankOneSeries (𝕜 := 𝕜) a e f) :=
  compact_of_expansion a ha hsum e f he hf _ (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he hf)

lemma rankOneSeries_traceClass [CompleteSpace X] [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (rankOneSeries (𝕜 := 𝕜) a e f) ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (rankOneSeries (𝕜 := 𝕜) a e f) ≤ ∑' j, a j :=
  traceClass_of_expansion a ha hsum e f he hf _ (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he hf)

lemma rankOneSeries_traceNorm_eq [CompleteSpace X] [CompleteSpace Y]
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (rankOneSeries (𝕜 := 𝕜) a e f) ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (rankOneSeries (𝕜 := 𝕜) a e f) = ∑' j, a j :=
  traceNorm_eq_of_orthonormal_expansion a ha hsum e f he hf _
    (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he.norm_eq_one hf.norm_eq_one)

end SummableExpansion

namespace SummableExpansion
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  {I : Type z}

lemma diagonal_formula_of_expansion
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e f : I → X) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (T : X →L[𝕜] X)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x))
    {ι : Type w} (b : HilbertBasis ι 𝕜 X) :
    Summable (fun i => ‖inner 𝕜 (b i) (T (b i))‖) ∧
      HasSum (fun i => inner 𝕜 (b i) (T (b i)))
        (∑' j, (a j : 𝕜) * inner 𝕜 (e j) (f j)) := by
  let d : I → ι → 𝕜 := fun j i => (a j : 𝕜) *
    (inner 𝕜 (e j) (b i) * inner 𝕜 (b i) (f j))
  have hrow (j : I) : Summable (fun i => ‖d j i‖) := by
    exact (((b.summable_inner_mul_inner (e j) (f j)).mul_left (a j : 𝕜)).norm)
  have hrow_bound (j : I) : (∑' i, ‖d j i‖) ≤ a j := by
    simp only [d, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (ha j), tsum_mul_left]
    simpa using mul_le_mul_of_nonneg_left
      (ExpandedFA.TraceIdeals.TraceClassDefinitions.tsum_norm_inner_mul_inner_le_one
        b (f j) (e j) (hf j) (he j)) (ha j)
  have habs : Summable (fun p : I × ι => ‖d p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨hrow, hsum.of_nonneg_of_le (fun j => tsum_nonneg (fun i => norm_nonneg _)) hrow_bound⟩
  have hab : Summable (Function.uncurry d) := habs.of_norm
  have hdiag (i : ι) : (∑' j, d j i) = inner 𝕜 (b i) (T (b i)) := by
    have hh := (hexp (b i)).mapL (innerSL 𝕜 (b i))
    simp only [innerSL_apply_apply, inner_smul_right] at hh
    convert hh.tsum_eq using 1
    congr 1
    funext j
    dsimp [d]
    ring
  have hsumdiag : Summable (fun i => inner 𝕜 (b i) (T (b i))) := by
    simpa only [Function.uncurry_apply_pair, Prod.swap, hdiag] using hab.prod_symm.prod
  refine ⟨hsumdiag.norm, hsumdiag.hasSum_iff.mpr ?_⟩
  calc
    _ = ∑' i, ∑' j, d j i := tsum_congr (fun i => (hdiag i).symm)
    _ = ∑' j, ∑' i, d j i := hab.tsum_comm
    _ = _ := tsum_congr (fun j =>
      ((b.hasSum_inner_mul_inner (e j) (f j)).mul_left (a j : 𝕜)).tsum_eq)

lemma trace_formula_of_expansion
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e f : I → X) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (T : X →L[𝕜] X)
    (hexp : ∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue T =
      ∑' j, (a j : 𝕜) * inner 𝕜 (e j) (f j) :=
  (diagonal_formula_of_expansion a ha hsum e f he hf T hexp
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis).2.tsum_eq

lemma rankOneSeries_trace
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e f : I → X) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue (rankOneSeries (𝕜 := 𝕜) a e f) =
      ∑' j, (a j : 𝕜) * inner 𝕜 (e j) (f j) :=
  trace_formula_of_expansion a ha hsum e f he hf _
    (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he hf)

end SummableExpansion

namespace SummableExpansion
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  {I : Type z}

lemma rankOneSeries_apply_right
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : Orthonormal 𝕜 e) (hf : ∀ j, ‖f j‖ = 1) (j : I) :
    rankOneSeries (𝕜 := 𝕜) a e f (e j) = (a j : 𝕜) • f j := by
  rw [← (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he.norm_eq_one hf (e j)).tsum_eq,
    tsum_eq_single j]
  · simp [he.norm_eq_one j]
  · intro k hkj
    simp [he.inner_eq_zero hkj]

lemma rankOneSeries_apply_eq_zero
    (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (e : I → X) (f : I → Y) (he : ∀ j, ‖e j‖ = 1) (hf : ∀ j, ‖f j‖ = 1)
    (x : X) (hx : ∀ j, inner 𝕜 (e j) x = 0) :
    rankOneSeries (𝕜 := 𝕜) a e f x = 0 := by
  have h := (rankOneSeries_expansion (𝕜 := 𝕜) a ha hsum e f he hf x).tsum_eq.symm
  simpa [hx] using h

end SummableExpansion

section SingularCriterion

open CompactSpectral TraceIdeals.TraceClassDefinitions

/-- Summability of the positive singular system is sufficient for the canonical
trace-class definition. No zero padding or separability is assumed. -/
theorem traceClass_of_summable_singularSystem
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem ℂ H K T) (hσ : Summable S.sigma) :
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T = ∑' j, S.sigma j := by
  let e := singularIndexEquiv T hT S
  have hval (j : S.Index) : SingularApproximation.Spec.SingularValueValue T (e j).val =
      S.sigma j := singularIndexEquiv_value T hT S j
  have hsub : Summable (fun n : positiveIndices T =>
      SingularApproximation.Spec.SingularValueValue T n.val) :=
    e.summable_iff.mp (hσ.congr (fun j => (hval j).symm))
  have hfull : Summable (SingularApproximation.Spec.SingularValueValue T) :=
    ((hasSum_subtype_iff_of_support_subset (positiveIndices_support T hT)).mp
      hsub.hasSum).summable
  have hc : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T :=
    ⟨hT, (summable_nat_add_iff 1).mpr hfull⟩
  exact ⟨hc, (singularSystem_sum ℂ H K T hc S).2.symm⟩

end SingularCriterion

section SingularBases

variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {J : Type*}

/-- Extend an orthonormal family spanning the kernel's orthogonal complement
to a basis of the entire space. The additional directions are killed by T. -/
lemma orthonormal_kernel_basis_extension (T : H →L[ℂ] K) (v : J → H)
    (hv : Orthonormal ℂ v)
    (hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = T.ker.orthogonal) :
    ∃ (W : Set H) (b : HilbertBasis W ℂ H) (e : J ↪ W),
      (∀ j, b (e j) = v j) ∧ ∀ k, k ∉ Set.range e → T (b k) = 0 := by
  obtain ⟨W, b, hW, hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  let e : J ↪ W := {
    toFun := fun j => ⟨v j, hW ⟨j, rfl⟩⟩
    inj' := fun i j hij => hv.linearIndependent.injective (congrArg Subtype.val hij) }
  have he (j : J) : b (e j) = v j := congrFun hb (e j)
  refine ⟨W, b, e, he, ?_⟩
  intro k hk
  have hp : b k ∈ (Submodule.span ℂ (Set.range v)).orthogonal := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← he j]
      exact b.orthonormal.inner_eq_zero (fun h => hk ⟨j, h⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
    | smul a x hx ih => simp [inner_smul_left, ih]
  have hperp : (Submodule.span ℂ (Set.range v)).orthogonal = T.ker := by
    rw [← Submodule.orthogonal_closure, hspan, Submodule.orthogonal_orthogonal]
  change b k ∈ T.ker
  rw [← hperp]
  exact hp

lemma orthonormal_kernel_sum_basis_extension (T : H →L[ℂ] K) (v : I → H)
    (hv : Orthonormal ℂ v)
    (hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = T.ker.orthogonal) :
    ∃ (J : Type v) (c : HilbertBasis (I ⊕ J) ℂ H),
      (∀ j, c (Sum.inl j) = v j) ∧ ∀ k, T (c (Sum.inr k)) = 0 := by
  classical
  obtain ⟨W,b,e,he,hk⟩ := orthonormal_kernel_basis_extension T v hv hspan
  let J := {k : W // k ∉ Set.range e}
  let q : I ⊕ J ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl J)).trans
      (Equiv.sumCompl (fun k : W => k ∈ Set.range e))
  let r : I ⊕ J → H := fun k => b (q k)
  have hrange : Set.range r = Set.range b := by
    change Set.range (b ∘ q) = _
    rw [Set.range_comp, q.surjective.range_eq, Set.image_univ]
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range r)).topologicalClosure := by
    rw [hrange, b.dense_span]
  let c : HilbertBasis (I ⊕ J) ℂ H := HilbertBasis.mk
    (b.orthonormal.comp q q.injective) hsp
  have hc (k : I ⊕ J) : c k = b (q k) := congrFun (HilbertBasis.coe_mk _ _) k
  refine ⟨J, c, ?_, ?_⟩
  · intro j
    rw [hc]
    exact he j
  · intro k
    rw [hc]
    exact hk k.val k.property

theorem singular_basis_extensions : Spec.SingularBasisExtensions.{v,w} := by
  intro H _ _ _ K _ _ _ T S
  obtain ⟨W, b, e, he, hk⟩ := orthonormal_kernel_basis_extension T S.rightVector
    S.right_orthonormal S.right_closedSpan
  obtain ⟨V, c, f, hf, hl⟩ := orthonormal_kernel_basis_extension T.adjoint S.leftVector
    S.left_orthonormal S.left_closedSpan
  exact ⟨W, b, e, V, c, f, he, hf, hk, hl⟩

variable [CompleteSpace K]

lemma algebraic_singular_transport (T : H →L[ℂ] K)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T)
    (n : ℕ) (j : Fin n → S.Index) :
    exteriorPower.map n T.toLinearMap
      (exteriorPower.ιMulti ℂ n (fun i => S.rightVector (j i))) =
        ((∏ i, S.sigma (j i) : ℝ) : ℂ) •
          exteriorPower.ιMulti ℂ n (fun i => S.leftVector (j i)) := by
  rw [exteriorPower.map_apply_ιMulti]
  have h : (T.toLinearMap ∘ fun i => S.rightVector (j i)) =
      (fun i => (S.sigma (j i) : ℂ) • S.leftVector (j i)) := by
    funext i
    exact S.map_right (j i)
  rw [h, AlternatingMap.map_smul_univ, Complex.ofReal_prod]

lemma algebraic_adjoint_singular_transport (T : H →L[ℂ] K)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T)
    (n : ℕ) (j : Fin n → S.Index) :
    exteriorPower.map n T.adjoint.toLinearMap
      (exteriorPower.ιMulti ℂ n (fun i => S.leftVector (j i))) =
        ((∏ i, S.sigma (j i) : ℝ) : ℂ) •
          exteriorPower.ιMulti ℂ n (fun i => S.rightVector (j i)) := by
  rw [exteriorPower.map_apply_ιMulti]
  have h : (T.adjoint.toLinearMap ∘ fun i => S.leftVector (j i)) =
      (fun i => (S.sigma (j i) : ℂ) • S.rightVector (j i)) := by
    funext i
    exact S.adjoint_left (j i)
  rw [h, AlternatingMap.map_smul_univ, Complex.ofReal_prod]

end SingularBases

section SubsetProducts

variable {α : Type w}

/-- The elementary symmetric sum recurrence, on actual finite subsets. -/
lemma sum_subset_products_insert [DecidableEq α] (a : α) (s : Finset α) (ha : a ∉ s)
    (f : α → ℝ) (n : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (n + 1), ∏ i ∈ t, f i) =
      (∑ t ∈ s.powersetCard (n + 1), ∏ i ∈ t, f i) +
        f a * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i := by
  classical
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.prod_insert (fun hat => ha ((Finset.mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu htu
      have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (Finset.erase · a) htu
  · apply Finset.disjoint_left.mpr
    intro t ht hit
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hit
    exact ha ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self a u))

/-- Finite elementary symmetric sums obey the sharp factorial majorant. -/
lemma sum_subset_products_le (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : Finset α) (n : ℕ) :
    (∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i) ≤
      (∑ i ∈ s, f i) ^ n / (n.factorial : ℝ) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n <;> simp [Finset.powersetCard_eq_filter, Finset.sum_filter]
  | @insert a s ha ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [sum_subset_products_insert a s ha f n, Finset.sum_insert ha]
      have hfa := hf a
      have hs : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg (fun i _ => hf i)
      have hfac : (0 : ℝ) < n.factorial := by positivity
      have hsucc : (0 : ℝ) < n + 1 := by positivity
      calc
        _ ≤ (∑ i ∈ s, f i) ^ (n + 1) / ((n + 1).factorial : ℝ) +
            f a * ((∑ i ∈ s, f i) ^ n / (n.factorial : ℝ)) :=
          add_le_add (ih (n + 1)) (mul_le_mul_of_nonneg_left (ih n) (hf a))
        _ = ((∑ i ∈ s, f i) ^ (n + 1) +
            (n + 1 : ℝ) * (∑ i ∈ s, f i) ^ n * f a) /
            ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
        _ ≤ ((∑ i ∈ s, f i) + f a) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          simpa using pow_add_mul_le_add_pow hs (by positivity :
            0 ≤ 2 * (∑ i ∈ s, f i) + f a) (n + 1)
        _ = _ := by rw [add_comm (f a)]

/-- The factorial bound for arbitrary, possibly uncountable, index types.
Finite subfamilies are bounded using the union of the subsets they contain. -/
lemma summable_subset_products (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hsum : Summable f) (n : ℕ) :
    Summable (fun s : Set.powersetCard α n => ∏ i ∈ s.val, f i) ∧
      (∑' s : Set.powersetCard α n, ∏ i ∈ s.val, f i) ≤
        (∑' i, f i) ^ n / (n.factorial : ℝ) := by
  classical
  have hn (s : Set.powersetCard α n) : 0 ≤ ∏ i ∈ s.val, f i :=
    Finset.prod_nonneg (fun i _ => hf i)
  have hb (F : Finset (Set.powersetCard α n)) :
      (∑ s ∈ F, ∏ i ∈ s.val, f i) ≤ (∑' i, f i) ^ n / (n.factorial : ℝ) := by
    let U := F.biUnion (fun s => s.val)
    have hsub : F.image (fun s => s.val) ⊆ U.powersetCard n := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_biUnion_of_mem (fun t => t.val) ht, t.property⟩
    calc
      _ = ∑ s ∈ F.image (fun s => s.val), ∏ i ∈ s, f i := by
        rw [Finset.sum_image]
        exact fun s _ t _ h => Subtype.ext h
      _ ≤ ∑ s ∈ U.powersetCard n, ∏ i ∈ s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun s _ _ => Finset.prod_nonneg (fun i _ => hf i))
      _ ≤ (∑ i ∈ U, f i) ^ n / (n.factorial : ℝ) :=
        sum_subset_products_le f hf U n
      _ ≤ (∑' i, f i) ^ n / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hf i))
            (hsum.sum_le_tsum U (fun i _ => hf i)) n) (by positivity)
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

theorem subset_product_bound : Spec.SubsetProductBound.{w} := by
  intro α f hf hsum n
  exact summable_subset_products f hf hsum n

/-- Absolute finite-subset expansion has an exponential majorant. -/
lemma summable_all_subset_products (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hsum : Summable f) :
    Summable (fun s : Finset α => ∏ i ∈ s, f i) ∧
      (∑' s : Finset α, ∏ i ∈ s, f i) ≤ Real.exp (∑' i, f i) := by
  classical
  let e (n : ℕ) := ∑' s : Set.powersetCard α n, ∏ i ∈ s.val, f i
  have he (n : ℕ) := summable_subset_products f hf hsum n
  have hen (n : ℕ) : 0 ≤ e n := tsum_nonneg (fun s =>
    Finset.prod_nonneg (fun i _ => hf i))
  have he_sum : Summable e := (Real.summable_pow_div_factorial (∑' i, f i)).of_nonneg_of_le
    hen (fun n => (he n).2)
  have hall : Summable (fun p : (n : ℕ) × Set.powersetCard α n =>
      ∏ i ∈ p.2.val, f i) :=
    (summable_sigma_of_nonneg (fun p => Finset.prod_nonneg (fun i _ => hf i))).mpr
      ⟨fun n => (he n).1, he_sum⟩
  refine ⟨Set.powersetCard.prodEquiv.summable_iff.mp hall, ?_⟩
  calc
    _ = ∑' p : (n : ℕ) × Set.powersetCard α n, ∏ i ∈ p.2.val, f i :=
      (Set.powersetCard.prodEquiv.tsum_eq (fun s : Finset α => ∏ i ∈ s, f i)).symm
    _ = ∑' n, e n := hall.tsum_sigma
    _ ≤ ∑' n : ℕ, (∑' i, f i) ^ n / (n.factorial : ℝ) :=
      he_sum.tsum_le_tsum (fun n => (he n).2) (Real.summable_pow_div_factorial _)
    _ = Real.exp (∑' i, f i) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem subset_generating_bound : Spec.SubsetGeneratingBound.{w} := by
  intro α f hf hsum r hr
  simpa only [tsum_mul_left] using
    summable_all_subset_products (fun i => r * f i) (fun i => mul_nonneg hr (hf i))
      (hsum.mul_left r)

end SubsetProducts

namespace GramDeterminant

open Module InnerProductSpace

variable {𝕜 E α : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype α] [DecidableEq α]
  [LinearOrder α] [LocallyFiniteOrderBot α] [FiniteDimensional 𝕜 E]

lemma norm_basis_det_le_prod (b : OrthonormalBasis α 𝕜 E) (v : α → E) :
    ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  have hdim : finrank 𝕜 E = Fintype.card α := Module.finrank_eq_card_basis b.toBasis
  let c : OrthonormalBasis α 𝕜 E := gramSchmidtOrthonormalBasis hdim v
  have hbc : ‖b.toBasis.det v‖ = ‖c.toBasis.det v‖ := by
    change ‖(b.toBasis.toMatrix v).det‖ = ‖(c.toBasis.toMatrix v).det‖
    rw [← b.toBasis.toMatrix_mul_toMatrix c.toBasis v, Matrix.det_mul, norm_mul]
    change ‖b.toBasis.det c‖ * ‖c.toBasis.det v‖ = ‖c.toBasis.det v‖
    rw [b.det_to_matrix_orthonormalBasis, one_mul]
  rw [hbc, show c.toBasis.det v = ∏ i, inner 𝕜 (c i) (v i) from
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => by
    simpa only [c.orthonormal.norm_eq_one, one_mul] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (v i))

omit [FiniteDimensional 𝕜 E] in
lemma norm_det_mixedGram_le (x y : α → E) :
    ‖Matrix.det (fun i j => inner 𝕜 (x i) (y j))‖ ≤
      ∏ i, ‖x i‖ * ‖y i‖ := by
  classical
  let A : Matrix α α 𝕜 := fun i j => inner 𝕜 (x i) (y j)
  by_cases hy : LinearIndependent 𝕜 y
  · let U := Submodule.span 𝕜 (Set.range y)
    let by' : Basis α 𝕜 U := Basis.span hy
    let : FiniteDimensional 𝕜 U := Module.Finite.of_basis by'
    have hdim : finrank 𝕜 U = Fintype.card α := Module.finrank_eq_card_basis by'
    let c : OrthonormalBasis α 𝕜 U := gramSchmidtOrthonormalBasis hdim by'
    let xU : α → U := fun i => U.orthogonalProjectionOnto (x i)
    let yU : α → U := fun i => ⟨y i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hA : A = (c.toBasis.toMatrix xU).conjTranspose * c.toBasis.toMatrix yU := by
      ext i j
      change inner 𝕜 (x i) (y j) = _
      rw [← U.inner_orthogonalProjectionOnto_eq_of_mem_right (yU j) (x i)]
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        RCLike.star_def, inner_conj_symm]
        using (c.sum_inner_mul_inner (xU i) (yU j)).symm
    calc
      ‖A.det‖ = ‖c.toBasis.det xU‖ * ‖c.toBasis.det yU‖ := by
        rw [hA, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star]
        rfl
      _ ≤ (∏ i, ‖xU i‖) * ∏ i, ‖yU i‖ :=
        mul_le_mul (norm_basis_det_le_prod c xU) (norm_basis_det_le_prod c yU)
          (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      _ = ∏ i, ‖xU i‖ * ‖yU i‖ := (Finset.prod_mul_distrib).symm
      _ ≤ ∏ i, ‖x i‖ * ‖y i‖ := by
        apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro i _
        exact mul_le_mul_of_nonneg_right (U.norm_orthogonalProjectionOnto_apply_le (x i))
          (norm_nonneg (y i))
  · have hdet : A.det = 0 := by
      apply Matrix.det_eq_zero_of_not_linearIndependent_cols
      intro h
      apply hy
      let g : E →ₗ[𝕜] (α → 𝕜) := LinearMap.pi (fun i => (innerSL 𝕜 (x i)).toLinearMap)
      exact LinearIndependent.of_comp g h
    rw [show Matrix.det (fun i j => inner 𝕜 (x i) (y j)) = A.det from rfl, hdet, norm_zero]
    exact Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

omit [FiniteDimensional 𝕜 E] [LinearOrder α] [LocallyFiniteOrderBot α] in
lemma norm_det_mixedGram_le' (x y : α → E) :
    ‖Matrix.det (fun i j => inner 𝕜 (x i) (y j))‖ ≤
      ∏ i, ‖x i‖ * ‖y i‖ := by
  classical
  let : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  let : LocallyFiniteOrderBot α := LocallyFiniteOrderBot.ofIic α
    (fun a => Finset.univ.filter (fun x => x ≤ a)) (by intro a x; simp)
  exact norm_det_mixedGram_le x y

end GramDeterminant

namespace Coefficients

variable {J H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma weighted_square_summable (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u : J → H) (hu : Orthonormal ℂ u) (x : H) :
    Summable (fun j => c j * ‖inner ℂ (u j) x‖ ^ 2) := by
  apply (hs.mul_right (‖x‖ ^ 2)).of_nonneg_of_le
  · intro j; exact mul_nonneg (hc j) (sq_nonneg _)
  · intro j
    apply mul_le_mul_of_nonneg_left _ (hc j)
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [hu.norm_eq_one, one_mul] using norm_inner_le_norm (𝕜 := ℂ) (u j) x

lemma weighted_coords_memℓp (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u : J → H) (hu : Orthonormal ℂ u) (x : H) :
    Memℓp (fun j => (Real.sqrt (c j) : ℂ) * inner ℂ (u j) x) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  convert weighted_square_summable c hc hs u hu x using 1
  funext j
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hc j)]

def weightedCoords (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u : J → H) (hu : Orthonormal ℂ u) (x : H) : lp (fun _ : J => ℂ) 2 :=
  ⟨(fun j => (Real.sqrt (c j) : ℂ) * inner ℂ (u j) x),
    weighted_coords_memℓp c hc hs u hu x⟩

lemma weightedCoords_sq (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u : J → H) (hu : Orthonormal ℂ u) (x : H) :
    ‖weightedCoords c hc hs u hu x‖ ^ 2 = ∑' j, c j * ‖inner ℂ (u j) x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (weightedCoords c hc hs u hu x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  apply tsum_congr
  intro j
  change ‖(Real.sqrt (c j) : ℂ) * inner ℂ (u j) x‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hc j)]

lemma weightedCoords_inner (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u v : J → H) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (x y : H) :
    inner ℂ (weightedCoords c hc hs u hu x) (weightedCoords c hc hs v hv y) =
      ∑' j, (c j : ℂ) * inner ℂ x (u j) * inner ℂ (v j) y := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ ((Real.sqrt (c j) : ℂ) * inner ℂ (u j) x)
    ((Real.sqrt (c j) : ℂ) * inner ℂ (v j) y) = _
  rw [RCLike.inner_apply, map_mul, Complex.conj_ofReal, inner_conj_symm]
  have hsq : (Real.sqrt (c j) : ℂ) * (Real.sqrt (c j) : ℂ) = (c j : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hc j)
  calc
    _ = ((Real.sqrt (c j) : ℂ) * (Real.sqrt (c j) : ℂ)) *
        inner ℂ x (u j) * inner ℂ (v j) y := by ring
    _ = _ := by rw [hsq]

variable [CompleteSpace H]

lemma singular_inner_factorization (T : H →L[ℂ] H)
    (S : ExpandedFA.CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H H T)
    (hs : Summable S.sigma) (x y : H) :
    inner ℂ x (T y) = inner ℂ
      (weightedCoords S.sigma (fun j => (S.positive j).le) hs S.leftVector S.left_orthonormal x)
      (weightedCoords S.sigma (fun j => (S.positive j).le) hs S.rightVector S.right_orthonormal y) := by
  rw [weightedCoords_inner]
  have h := (S.expansion y).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply, inner_smul_right] at h
  rw [← h.tsum_eq]
  apply tsum_congr
  intro j
  ac_rfl

omit [CompleteSpace H] in
lemma weightedCoords_basis_sum (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (u : J → H) (hu : Orthonormal ℂ u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖weightedCoords c hc hs u hu (b i)‖ ^ 2) ∧
      (∑' i, ‖weightedCoords c hc hs u hu (b i)‖ ^ 2) = ∑' j, c j := by
  let f : J → ι → ℝ := fun j i => c j * ‖inner ℂ (u j) (b i)‖ ^ 2
  have hrow (j : J) : HasSum (f j) (c j) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr (u j))
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
      hu.norm_eq_one, one_pow] at h
    simpa only [f, HilbertBasis.repr_apply_apply, norm_inner_symm, mul_one]
      using h.mul_left (c j)
  have habs : Summable (fun p : J × ι => f p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => mul_nonneg (hc p.1) (sq_nonneg _))).mpr
      ⟨fun j => (hrow j).summable, hs.congr (fun j => (hrow j).tsum_eq.symm)⟩
  have hsq (i : ι) : ‖weightedCoords c hc hs u hu (b i)‖ ^ 2 = ∑' j, f j i :=
    weightedCoords_sq c hc hs u hu (b i)
  refine ⟨habs.prod_symm.prod.congr (fun i => (hsq i).symm), ?_⟩
  calc
    _ = ∑' i, ∑' j, f j i := tsum_congr hsq
    _ = ∑' j, ∑' i, f j i := habs.tsum_comm
    _ = ∑' j, c j := tsum_congr (fun j => (hrow j).tsum_eq)

open ExpandedFA.FredholmDeterminant.TraceClassDefinitions

lemma principal_minor_singular_bound (T : H →L[ℂ] H)
    (S : ExpandedFA.CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H H T)
    (hs : Summable S.sigma) (b : HilbertBasis ι ℂ H) (n : ℕ) :
    Summable (fun s : Set.powersetCard ι n => ‖principalMinor b T s.val‖) ∧
      (∑' s : Set.powersetCard ι n, ‖principalMinor b T s.val‖) ≤
        (∑' j, S.sigma j) ^ n / (n.factorial : ℝ) := by
  classical
  let hc : ∀ j, 0 ≤ S.sigma j := fun j => (S.positive j).le
  let L (i : ι) := weightedCoords S.sigma hc hs S.leftVector S.left_orthonormal (b i)
  let R (i : ι) := weightedCoords S.sigma hc hs S.rightVector S.right_orthonormal (b i)
  let q (i : ι) : ℝ := (‖L i‖ ^ 2 + ‖R i‖ ^ 2) / 2
  have hL := weightedCoords_basis_sum S.sigma hc hs S.leftVector S.left_orthonormal b
  have hR := weightedCoords_basis_sum S.sigma hc hs S.rightVector S.right_orthonormal b
  have hq : Summable q := (hL.1.add hR.1).div_const 2
  have hqn (i : ι) : 0 ≤ q i := by dsimp [q]; positivity
  have hqsum : ∑' i, q i = ∑' j, S.sigma j := by
    dsimp only [q]
    rw [tsum_div_const, hL.1.tsum_add hR.1, hL.2, hR.2]
    ring
  have hpoint (s : Finset ι) : ‖principalMinor b T s‖ ≤ ∏ i ∈ s, q i := by
    have hmat : (fun i j : s => inner ℂ (b i.val) (T (b j.val))) =
        (fun i j : s => inner ℂ (L i.val) (R j.val)) := by
      funext i j
      exact singular_inner_factorization T S hs (b i.val) (b j.val)
    change ‖Matrix.det (fun i j : s => inner ℂ (b i.val) (T (b j.val)))‖ ≤ _
    rw [hmat]
    calc
      _ ≤ ∏ i : s, ‖L i.val‖ * ‖R i.val‖ := GramDeterminant.norm_det_mixedGram_le' _ _
      _ ≤ ∏ i : s, q i.val := by
        apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro i _
        dsimp only [q]
        nlinarith [sq_nonneg (‖L i.val‖ - ‖R i.val‖)]
      _ = ∏ i ∈ s, q i := Finset.prod_attach s q
  have hmajor := summable_subset_products q hqn hq n
  have hsummable : Summable (fun s : Set.powersetCard ι n => ‖principalMinor b T s.val‖) :=
    hmajor.1.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => hpoint s.val)
  have hcompare : (∑' s : Set.powersetCard ι n, ‖principalMinor b T s.val‖) ≤
      ∑' s : Set.powersetCard ι n, ∏ i ∈ s.val, q i := by
    exact hsummable.tsum_le_tsum (fun s : Set.powersetCard ι n => hpoint s.val) hmajor.1
  refine ⟨hsummable, hcompare.trans ?_⟩
  rw [← hqsum]
  exact hmajor.2

lemma principal_minor_traceNorm_bound (T : H →L[ℂ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.IsTraceClass (𝕜 := ℂ) T)
    (b : HilbertBasis ι ℂ H) (n : ℕ) :
    Summable (fun s : Set.powersetCard ι n => ‖principalMinor b T s.val‖) ∧
      (∑' s : Set.powersetCard ι n, ‖principalMinor b T s.val‖) ≤
        ExpandedFA.TraceIdeals.TraceClassDefinitions.traceNorm T ^ n / (n.factorial : ℝ) := by
  obtain ⟨S⟩ := ExpandedFA.CompactSpectral.SingularExpansion.compact_singular_system ℂ H H T hT.1
  obtain ⟨hs, hnorm⟩ := ExpandedFA.TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ H H T hT S
  simpa only [hnorm] using principal_minor_singular_bound T S hs b n

lemma exterior_trace_factorial_bound (T : H →L[ℂ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.IsTraceClass (𝕜 := ℂ) T) (n : ℕ) :
    ‖exteriorTrace T n‖ ≤
      ExpandedFA.TraceIdeals.TraceClassDefinitions.traceNorm T ^ n / (n.factorial : ℝ) := by
  let b := ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  have h := principal_minor_traceNorm_bound T hT b n
  exact (norm_tsum_le_tsum_norm h.1).trans h.2

lemma fredholm_series_bound (T : H →L[ℂ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.IsTraceClass (𝕜 := ℂ) T) (z : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * exteriorTrace T n‖) ∧
      ‖fredholmDeterminant T z‖ ≤ Real.exp (‖z‖ *
        ExpandedFA.TraceIdeals.TraceClassDefinitions.traceNorm T) := by
  obtain ⟨S⟩ := ExpandedFA.CompactSpectral.SingularExpansion.compact_singular_system ℂ H H T hT.1
  have hnorm := (ExpandedFA.TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ H H T hT S).2
  have hn : 0 ≤ ExpandedFA.TraceIdeals.TraceClassDefinitions.traceNorm T := by
    change 0 ≤ ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T
    rw [← hnorm]
    exact tsum_nonneg (fun j => (S.positive j).le)
  exact factorial_series_majorant (fun n => exteriorTrace T n) _ hn
    (exterior_trace_factorial_bound T hT) z

end Coefficients

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
open ExpandedFA.FredholmDeterminant.TraceClassDefinitions
open ExpandedFA.FredholmDeterminant.TraceClassDefinitions.SummableExpansion
variable {I J α β H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma exterior_of_sum_singular_data
    (b : HilbertBasis α ℂ H) (d : HilbertBasis β ℂ K)
    (c : HilbertBasis (I ⊕ J) ℂ H) (l : I → K) (hl : Orthonormal ℂ l)
    (T : H →L[ℂ] K) (a : I → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : Summable a)
    (hTr : ∀ j, T (c (Sum.inl j)) = (a j : ℂ) • l j)
    (hTk : ∀ j, T (c (Sum.inr j)) = 0) (n : ℕ) :
    ∃ A : Space α n →L[ℂ] Space β n,
      (∀ x : Fin n → H, A (wedgeAlternating b x) =
        wedgeAlternating d (fun i => T (x i))) ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue A ∧
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue A =
        ∑' s : Set.powersetCard I n, ∏ j ∈ s.val, a j := by
  let w (s : Set.powersetCard I n) : ℝ := ∏ j ∈ s.val, a j
  let r (j : I) := c (Sum.inl j)
  let e (s : Set.powersetCard I n) := wedgeAlternating b (fun j => r (enumeration s j))
  let f (s : Set.powersetCard I n) := wedgeAlternating d (fun j => l (enumeration s j))
  have hr : Orthonormal ℂ r := c.orthonormal.comp Sum.inl Sum.inl_injective
  have he : Orthonormal ℂ e := orthonormal_wedges b r hr
  have hf : Orthonormal ℂ f := orthonormal_wedges d l hl
  have hw : ∀ s, 0 ≤ w s := fun s => Finset.prod_nonneg (fun j _ => ha j)
  have hs : Summable w := (summable_subset_products a ha hsum n).1
  let A := rankOneSeries (𝕜 := ℂ) w e f
  refine ⟨A, ?_, (rankOneSeries_traceNorm_eq w hw hs e f he hf).1,
    (rankOneSeries_traceNorm_eq w hw hs e f he hf).2⟩
  intro x
  apply naturality_of_sum_basis b d c T A hTk ?_ ?_ x
  · intro s
    change A (e s) = _
    rw [rankOneSeries_apply_right w hw hs e f he hf.norm_eq_one]
    have hh : (fun i => T (c (Sum.inl (enumeration s i)))) =
        (fun i => (a (enumeration s i) : ℂ) • l (enumeration s i)) :=
      funext (fun i => hTr (enumeration s i))
    rw [hh, wedge_smul_family]
    rfl
  · intro y hy
    apply rankOneSeries_apply_eq_zero w hw hs e f he.norm_eq_one hf.norm_eq_one
    intro s
    exact inner_wedge_eq_zero_of_slot b r s y hy
end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H : Type*} {n : ℕ} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma diagonal_principalMinor (b : HilbertBasis α ℂ H)
    (A : Space α n →L[ℂ] Space α n) (T : H →L[ℂ] H)
    (hA : ∀ x : Fin n → H, A (wedgeAlternating b x) = wedgeAlternating b (T ∘ x))
    (s : Set.powersetCard α n) :
    inner ℂ (basis α n s) (A (basis α n s)) =
      ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue b T s.val := by
  classical
  rw [basis_eq_wedge b s, hA, inner_wedge]
  let e : Fin n ≃ s.val := (Finset.equivFinOfCardEq s.property).symm
  let M : Matrix s.val s.val ℂ := fun i j => inner ℂ (b i.val) (T (b j.val))
  change Matrix.det (M.submatrix e e) = Matrix.det M
  exact Matrix.det_submatrix_equiv_self e M

lemma principalMinor_hasSum_of_traceClass (b : HilbertBasis α ℂ H)
    (A : Space α n →L[ℂ] Space α n) (T : H →L[ℂ] H)
    (hA : ∀ x : Fin n → H, A (wedgeAlternating b x) = wedgeAlternating b (T ∘ x))
    (htr : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue A) :
    Summable (fun s : Set.powersetCard α n =>
      ‖ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue b T s.val‖) ∧
    HasSum (fun s : Set.powersetCard α n =>
      ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue b T s.val)
      (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue A) := by
  have hdiag := ExpandedFA.TraceIdeals.TraceClassDefinitions.diagonal_trace ℂ (Space α n)
    A htr (Set.powersetCard α n) (basis α n)
  simpa only [diagonal_principalMinor b A T hA] using hdiag

variable [CompleteSpace H]
lemma exteriorTrace_eq_trace (T : H →L[ℂ] H)
    (A : Space (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
      (𝕜 := ℂ) (H := H)) n →L[ℂ]
      Space (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
        (𝕜 := ℂ) (H := H)) n)
    (hA : ∀ x : Fin n → H, A (wedgeAlternating
      (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)) x) =
        wedgeAlternating
          (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)) (T ∘ x))
    (htr : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue A) :
    ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue T n =
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue A := by
  exact (principalMinor_hasSum_of_traceClass _ A T hA htr).2.tsum_eq

end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates

def emptySubset (α : Type*) : Set.powersetCard α 0 := ⟨∅, rfl⟩

lemma powersetCard_zero_eq (α : Type*) (s : Set.powersetCard α 0) :
    s = emptySubset α := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp s.property

def zeroEquiv (α : Type*) : Space α 0 ≃ₗᵢ[ℂ] ℂ where
  toFun f := f (emptySubset α)
  invFun z := lp.single 2 (emptySubset α) z
  left_inv f := by
    apply lp.ext
    funext s
    rw [powersetCard_zero_eq α s]
    simp [lp.single_apply]
  right_inv z := by simp [lp.single_apply]
  map_add' f g := rfl
  map_smul' z f := rfl
  norm_map' f := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [tsum_eq_single (emptySubset α) (fun s hs => (hs (powersetCard_zero_eq α s)).elim)] at h
    exact ((sq_eq_sq₀ (norm_nonneg f) (norm_nonneg (f (emptySubset α)))).mp h).symm

@[simp] lemma zeroEquiv_apply (α : Type*) (f : Space α 0) :
    zeroEquiv α f = f (emptySubset α) := rfl

variable {α H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] lemma zeroEquiv_wedge (b : HilbertBasis α ℂ H) (x : Fin 0 → H) :
    zeroEquiv α (wedgeAlternating b x) = 1 := by
  change Matrix.det (fun i j : Fin 0 => b.repr (x i) (enumeration (emptySubset α) j)) = 1
  exact Matrix.det_isEmpty

lemma operator_zero_eq_id (b : HilbertBasis α ℂ H)
    (A : Space α 0 →L[ℂ] Space α 0) (T : H →L[ℂ] H)
    (hA : ∀ x : Fin 0 → H, A (wedgeAlternating b x) = wedgeAlternating b (T ∘ x)) :
    A = ContinuousLinearMap.id ℂ (Space α 0) := by
  apply clm_ext_hilbertBasis (basis α 0)
  intro s
  rw [basis_eq_wedge b s, hA]
  change wedgeAlternating b (T ∘ (fun j => b (enumeration s j))) =
    wedgeAlternating b (fun j => b (enumeration s j))
  congr 1
  exact funext (fun j => Fin.elim0 j)

lemma operator_zero_scalar_identity (b : HilbertBasis α ℂ H)
    (A : Space α 0 →L[ℂ] Space α 0) (T : H →L[ℂ] H)
    (hA : ∀ x : Fin 0 → H, A (wedgeAlternating b x) = wedgeAlternating b (T ∘ x)) (z : ℂ) :
    zeroEquiv α (A ((zeroEquiv α).symm z)) = z := by
  rw [operator_zero_eq_id b A T hA]
  exact (zeroEquiv α).apply_symm_apply z

end ExteriorCoordinates

namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma map_unique (n : ℕ) (b : HilbertBasis α ℂ H) (A B : Space α n →L[ℂ] E)
    (h : ∀ x : Fin n → H, A (wedgeAlternating b x) = B (wedgeAlternating b x)) : A = B := by
  apply clm_ext_hilbertBasis (basis α n)
  intro s
  rw [basis_eq_wedge b s]
  exact h _

def oneLinear (b : HilbertBasis α ℂ H) : H →ₗ[ℂ] Space α 1 :=
  (AlternatingMap.ofSubsingleton ℂ H (Space α 1) (0 : Fin 1)).symm (wedgeAlternating b)

lemma oneLinear_apply (b : HilbertBasis α ℂ H) (x : H) :
    oneLinear b x = wedgeAlternating b (fun _ : Fin 1 => x) := rfl


def oneIsometry (b : HilbertBasis α ℂ H) : H →ₗᵢ[ℂ] Space α 1 :=
  (oneLinear b).isometryOfInner (by
    intro x y
    rw [oneLinear_apply, oneLinear_apply, inner_wedge]
    exact Matrix.det_unique _)

lemma oneIsometry_surjective [CompleteSpace H] (b : HilbertBasis α ℂ H) :
    Function.Surjective (oneIsometry b) := by
  let U := oneIsometry b
  have hc : IsClosed (U.toLinearMap.range : Set (Space α 1)) :=
    U.isometry.isClosedEmbedding.isClosed_range
  have hw : Submodule.span ℂ (Set.range (fun x : Fin 1 → H => wedgeAlternating b x)) ≤
      U.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨x 0, ?_⟩
    change oneLinear b (x 0) = wedgeAlternating b x
    rw [oneLinear_apply]
    congr 1
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  have hh := (Submodule.span ℂ (Set.range (fun x : Fin 1 → H => wedgeAlternating b x))).topologicalClosure_minimal hw hc
  rw [dense_wedges b] at hh
  have hr : U.toLinearMap.range = ⊤ := le_antisymm le_top hh
  exact LinearMap.range_eq_top.mp hr

def oneEquiv [CompleteSpace H] (b : HilbertBasis α ℂ H) : Space α 1 ≃ₗᵢ[ℂ] H :=
  (LinearIsometryEquiv.ofSurjective (oneIsometry b) (oneIsometry_surjective b)).symm

@[simp] lemma oneEquiv_wedge [CompleteSpace H] (b : HilbertBasis α ℂ H) (x : H) :
    oneEquiv b (wedgeAlternating b (fun _ : Fin 1 => x)) = x := by
  change (LinearIsometryEquiv.ofSurjective (oneIsometry b) (oneIsometry_surjective b)).symm
    ((LinearIsometryEquiv.ofSurjective (oneIsometry b) (oneIsometry_surjective b)) x) = x
  exact LinearIsometryEquiv.symm_apply_apply _ _

end ExteriorCoordinates
namespace ExteriorCoordinates
open Spec.ExteriorCoordinates
variable {α β H K : Type*} {n : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
@[simp] lemma oneEquiv_symm_apply (b : HilbertBasis α ℂ H) (x : H) :
    (oneEquiv b).symm x = wedgeAlternating b (fun _ : Fin 1 => x) := by
  exact (oneEquiv b).symm_apply_eq.mpr (oneEquiv_wedge b x).symm

lemma oneEquiv_naturality (b : HilbertBasis α ℂ H) (d : HilbertBasis β ℂ K)
    (T : H →L[ℂ] K) (A : Space α 1 →L[ℂ] Space β 1)
    (h : ∀ x : Fin 1 → H, A (wedgeAlternating b x) =
      wedgeAlternating d (fun i => T (x i))) (x : H) :
    oneEquiv d (A ((oneEquiv b).symm x)) = T x := by
  rw [oneEquiv_symm_apply, h, oneEquiv_wedge]
end ExteriorCoordinates

abbrev coordinateOperator {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    {α : Type u} {β : Type z} (b : HilbertBasis α ℂ E) (d : HilbertBasis β ℂ F)
    (T : E →L[ℂ] F) (n : ℕ) :
    Spec.CoordinateSpaceValue α n →L[ℂ] Spec.CoordinateSpaceValue β n :=
  Spec.CoordinateOperatorValue b d T n
abbrev exteriorOperator := @Spec.ExteriorOperatorValue

section CoordinateOperator
variable {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
  {α : Type u} {β : Type z}

lemma coordinateOperator_eq_of_naturality (b : HilbertBasis α ℂ E) (d : HilbertBasis β ℂ F)
    (T : E →L[ℂ] F) (n : ℕ)
    (A : Spec.CoordinateSpaceValue α n →L[ℂ] Spec.CoordinateSpaceValue β n)
    (hA : ∀ x : Fin n → E, A (Spec.CoordinateWedgeValue b n x) =
      Spec.CoordinateWedgeValue d n (T ∘ x)) : coordinateOperator b d T n = A := by
  classical
  have hex : ∃ B : Spec.CoordinateSpaceValue α n →L[ℂ] Spec.CoordinateSpaceValue β n,
      ∀ x : Fin n → E, B (Spec.CoordinateWedgeValue b n x) =
        Spec.CoordinateWedgeValue d n (T ∘ x) := ⟨A, hA⟩
  dsimp only [coordinateOperator, Spec.CoordinateOperatorValue]
  rw [dite_eq_left hex]
  apply ExteriorCoordinates.clm_ext_hilbertBasis (Spec.ExteriorCoordinates.basis α n)
  intro s
  rw [ExteriorCoordinates.basis_eq_wedge b s]
  exact (Classical.choose_spec hex _).trans (hA _).symm

variable [CompleteSpace E] [CompleteSpace F]
lemma coordinateOperator_singular (b : HilbertBasis α ℂ E) (d : HilbertBasis β ℂ F)
    (T : E →L[ℂ] F) (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ E F T)
    (hsum : Summable S.sigma) (n : ℕ) :
    (∀ x : Fin n → E, coordinateOperator b d T n (Spec.CoordinateWedgeValue b n x) =
      Spec.CoordinateWedgeValue d n (T ∘ x)) ∧
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (coordinateOperator b d T n) ∧
    TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (coordinateOperator b d T n) =
      ∑' s : Set.powersetCard S.Index n, ∏ j ∈ s.val, S.sigma j := by
  obtain ⟨J,c,hc,hk⟩ := orthonormal_kernel_sum_basis_extension T S.rightVector
    S.right_orthonormal S.right_closedSpan
  obtain ⟨A,hn,ht,hv⟩ := ExteriorCoordinates.exterior_of_sum_singular_data b d c S.leftVector
    S.left_orthonormal T S.sigma (fun j => (S.positive j).le) hsum
    (fun j => by rw [hc]; exact S.map_right j) hk n
  have heq := coordinateOperator_eq_of_naturality b d T n A hn
  rw [heq]
  exact ⟨hn,ht,hv⟩
end CoordinateOperator

theorem exterior_construction : Spec.ExteriorConstruction.{v} := by
  intro H _ _ _ T hT n
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ H H T hT.1
  obtain ⟨hs,hnorm⟩ := TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ H H T hT S
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  have hp := coordinateOperator_singular b b T S hs n
  refine ⟨hp.1,hp.2.1,?_,?_⟩
  · change TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (coordinateOperator b b T n) ≤ _
    rw [hp.2.2, ← hnorm]
    exact (summable_subset_products S.sigma (fun j => (S.positive j).le) hs n).2
  · exact (ExteriorCoordinates.exteriorTrace_eq_trace T _ hp.1 hp.2.1).symm

theorem exterior_singular_traceNorm : Spec.ExteriorSingularTraceNorm.{v} := by
  intro H _ _ _ T hT S n
  have hs := (TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ H H T hT S).1
  exact (coordinateOperator_singular _ _ T S hs n).2.2

theorem exterior_low_degrees : Spec.ExteriorLowDegrees.{v} := by
  intro H _ _ _ T hT
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
  have h0 := (exterior_construction T hT 0).1
  have h1 := (exterior_construction T hT 1).1
  refine ⟨⟨ExteriorCoordinates.zeroEquiv _, ?_, ?_⟩,
    ⟨ExteriorCoordinates.oneEquiv b, ?_, ?_⟩⟩
  · exact ExteriorCoordinates.zeroEquiv_wedge b
  · exact ExteriorCoordinates.operator_zero_scalar_identity b _ T h0
  · exact ExteriorCoordinates.oneEquiv_wedge b
  · exact ExteriorCoordinates.oneEquiv_naturality b b T _ h1

abbrev rankOneSeries := @Spec.RankOneSeriesValue

theorem nuclear_expansion_criterion : Spec.NuclearExpansionCriterion.{u,v,w,z} := by
  intro 𝕜 _ E F _ _ _ _ _ _ I a ha hs e f he hf T hexp
  exact SummableExpansion.traceClass_of_expansion a ha hs e f he hf T hexp

theorem orthonormal_expansion_traceNorm : Spec.OrthonormalExpansionTraceNorm.{u,v,w,z} := by
  intro 𝕜 _ E F _ _ _ _ _ _ I a ha hs e f he hf T hexp
  exact SummableExpansion.traceNorm_eq_of_orthonormal_expansion a ha hs e f he hf T hexp

theorem nuclear_expansion_trace : Spec.NuclearExpansionTrace.{u,v,z} := by
  intro 𝕜 _ X _ _ _ I a ha hs e f he hf T hexp
  exact SummableExpansion.trace_formula_of_expansion a ha hs e f he hf T hexp

theorem principal_minor_traceNorm_bound : Spec.PrincipalMinorTraceNormBound.{v,w} := by
  intro H _ _ _ T hT ι b n
  exact Coefficients.principal_minor_traceNorm_bound T hT b n

theorem exterior_trace_factorial_bound : Spec.ExteriorTraceFactorialBound.{v} := by
  intro H _ _ _ T hT n
  exact Coefficients.exterior_trace_factorial_bound T hT n

theorem fredholm_series_bound : Spec.FredholmSeriesBound.{v} := by
  intro H _ _ _ T hT z
  exact Coefficients.fredholm_series_bound T hT z

lemma exterior_algebraic_compatibility (T : H →L[ℂ] H)
    (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    (exteriorOperator T n).toLinearMap.comp
      (coordinateEmbedding TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n) =
    (coordinateEmbedding TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n).comp
      (algebraicExteriorMap n T) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    coordinateEmbedding, Spec.CoordinateEmbeddingValue, ExteriorCoordinates.embed_ιMulti,
    algebraicExteriorMap, Spec.AlgebraicExteriorMapValue,
    exteriorPower.map_apply_ιMulti, ContinuousLinearMap.coe_coe]
  exact (exterior_construction T hT n).1 x

end ExpandedFA.FredholmDeterminant.TraceClassDefinitions
