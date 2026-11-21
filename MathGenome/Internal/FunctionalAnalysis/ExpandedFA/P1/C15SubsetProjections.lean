import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15SubsetProjections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15CoordinateContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Basic.Denumerable

noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
universe u v w
namespace ExpandedFA.P1.C15SubsetProjections
namespace SubsetProjectionProof
variable {𝕜 : Type u} {E : Type v} {ι : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable (b : UnconditionalSchauderBasis ι 𝕜 E)

def subseries (A : Set ι) (x : E) : E :=
  ∑' i, A.indicator (fun j => b.coord j x • b j) i

lemma subseries_hasSum (A : Set ι) (x : E) :
    HasSum (A.indicator (fun i => b.coord i x • b i)) (subseries b A x) :=
  ((b.expansion x).summable.indicator A).hasSum

lemma subseries_bound {C : ℝ} (hC : ∀ F : Finset ι, ‖b.proj F‖ ≤ C)
    (A : Set ι) (x : E) : ‖subseries b A x‖ ≤ C * ‖x‖ := by
  classical
  apply le_of_tendsto ((subseries_hasSum b A x).norm)
  apply Filter.Eventually.of_forall
  intro F
  have heq : (∑ i ∈ F, A.indicator (fun j => b.coord j x • b j) i) =
      b.proj (F.filter (fun i => i ∈ A)) x := by
    simp [GeneralSchauderBasis.proj_apply, Finset.sum_filter, Set.indicator_apply]
  rw [heq]
  exact (ContinuousLinearMap.le_opNorm _ x).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg x))

lemma subseries_add (A : Set ι) (x y : E) :
    subseries b A (x + y) = subseries b A x + subseries b A y := by
  classical
  apply HasSum.unique (subseries_hasSum b A (x + y))
  convert (subseries_hasSum b A x).add (subseries_hasSum b A y) using 1
  ext i
  by_cases hi : i ∈ A <;> simp [hi, add_smul]

lemma subseries_smul (A : Set ι) (c : 𝕜) (x : E) :
    subseries b A (c • x) = c • subseries b A x := by
  classical
  apply HasSum.unique (subseries_hasSum b A (c • x))
  convert (subseries_hasSum b A x).const_smul c using 1
  ext i
  by_cases hi : i ∈ A <;> simp [hi, smul_smul]

/-- Linearity is proved from limits; boundedness follows from the uniform
bound on finite coordinate projections. -/
def projection (A : Set ι) : E →L[𝕜] E :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := subseries b A
      map_add' := subseries_add b A
      map_smul' := subseries_smul b A }
    (by obtain ⟨C, hC⟩ := b.exists_norm_proj_le
        exact ⟨C, subseries_bound b hC A⟩)

lemma projection_hasSum (A : Set ι) (x : E) :
    HasSum (A.indicator (fun i => b.coord i x • b i)) (projection b A x) :=
  subseries_hasSum b A x

lemma coord_projection (A : Set ι) (x : E) (i : ι) :
    b.coord i (projection b A x) = A.indicator (fun j => b.coord j x) i := by
  classical
  have h := (b.coord i).hasSum (projection_hasSum b A x)
  have ht : HasSum (fun j => b.coord i (A.indicator (fun k => b.coord k x • b k) j))
      (A.indicator (fun j => b.coord j x) i) := by
    have hs := hasSum_single (f := fun j =>
      b.coord i (A.indicator (fun k => b.coord k x • b k) j)) i (by
        intro j hji
        by_cases hj : j ∈ A <;>
          simp [hj, b.ortho, Ne.symm hji])
    by_cases hi : i ∈ A <;> simpa [hi, b.ortho, Pi.single_apply] using hs
  exact h.unique ht

omit [CompleteSpace E] in
lemma ext_coordinates {x y : E} (h : ∀ i, b.coord i x = b.coord i y) : x = y := by
  apply (b.expansion x).unique
  simpa only [h] using b.expansion y

lemma projection_idempotent (A : Set ι) (x : E) :
    projection b A (projection b A x) = projection b A x := by
  apply ext_coordinates b
  intro i
  simp only [coord_projection]
  classical
  by_cases hi : i ∈ A <;> simp [Set.indicator_apply, hi]

lemma projection_basis (A : Set ι) (i : ι) (hi : i ∈ A) :
    projection b A (b i) = b i := by
  apply ext_coordinates b
  intro j
  classical
  by_cases hj : j ∈ A
  · simp [coord_projection, hj]
  · have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
    simp [coord_projection, hj, b.ortho, Pi.single_apply, hji]

lemma range_projection (A : Set ι) :
    (projection b A).range = (Submodule.span 𝕜 (b.basis '' A)).topologicalClosure := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (projection_hasSum b A x)
    apply Filter.Eventually.of_forall
    intro F
    apply Submodule.sum_mem
    intro i hi
    by_cases hai : i ∈ A
    · simp only [Set.indicator_of_mem hai]
      exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨i, hai, rfl⟩))
    · simp [Set.indicator_of_notMem hai]
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨b i, projection_basis b A i hi⟩
    · apply ContinuousLinearMap.IsIdempotentElem.isClosed_range
      ext x
      exact projection_idempotent b A x

end SubsetProjectionProof
/-- The result holds for arbitrary native unconditional index types. -/
theorem native_subset_projections : Spec.NativeSubsetProjections := by
  intro 𝕜 E ι _ _ _ _ b
  classical
  let P := SubsetProjectionProof.projection b
  refine ⟨P, ?_, ?_, SubsetProjectionProof.projection_idempotent b,
    SubsetProjectionProof.range_projection b, ?_, ?_, ?_⟩
  · exact SubsetProjectionProof.projection_hasSum b
  · intro A x i
    simpa only [Set.indicator_apply] using SubsetProjectionProof.coord_projection b A x i
  · obtain ⟨C, hC⟩ := b.exists_norm_proj_le
    have hCpos : 0 ≤ C := by simpa using hC ∅
    exact ⟨C, hCpos, fun A => ContinuousLinearMap.opNorm_le_bound _ hCpos
      (SubsetProjectionProof.subseries_bound b hC A)⟩
  · ext x
    apply SubsetProjectionProof.ext_coordinates b
    intro i
    simp [P, SubsetProjectionProof.coord_projection]
  · ext x
    apply SubsetProjectionProof.ext_coordinates b
    intro i
    simp [P, SubsetProjectionProof.coord_projection]

open C15Basis C15CoordinateContinuity

/-- Ordered expansion in the raw basis and in the upstream series interface
are equivalent in the displayed norm. -/
theorem rawBasis_iff_uniqueOrderedExpansions {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (e : ℕ → E) :
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e ↔
      C15Unconditional.HasUniqueOrderedExpansions 𝕜 E e := by
  constructor
  · rintro ⟨hne, hex⟩
    refine ⟨hne, fun x => ?_⟩
    obtain ⟨a, ha, hua⟩ := hex x
    exact ⟨a, (C01Banach.hasSequentialSum_iff E _ x).mpr ha,
      fun b hb => hua b ((C01Banach.hasSequentialSum_iff E _ x).mp hb)⟩
  · rintro ⟨hne, hex⟩
    refine ⟨hne, fun x => ?_⟩
    obtain ⟨a, ha, hua⟩ := hex x
    exact ⟨a, (C01Banach.hasSequentialSum_iff E _ x).mp ha,
      fun b hb => hua b ((C01Banach.hasSequentialSum_iff E _ x).mpr hb)⟩

/-- No native coordinate boundedness is assumed; it is supplied by the
accepted raw coordinate-continuity theorem. -/
theorem raw_subset_projections : Spec.RawSubsetProjections := by
  intro 𝕜 E _ _ _ _ e h hu
  obtain ⟨b, hb, hc, _⟩ := raw_native_basis h
  let bu : UnconditionalSchauderBasis ℕ 𝕜 E :=
    { basis := b.basis
      coord := b.coord
      ortho := b.ortho
      expansion := by
        intro x
        have hx := (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 E e).mp hu |>.2
          x (rawCoordinates h x)
          ((C01Banach.hasSequentialSum_iff E _ x).mpr (rawCoordinates_tendsto h x))
        simpa only [hb, hc] using
          (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp hx }
  have hp := native_subset_projections bu
  have hcoords : (fun x i => bu.coord i x) = C15Basis.Spec.rawCoordinates h := by
    funext x i
    exact hc i x
  simpa only [bu, hb, hcoords] using hp

/-- The manuscript formulation, with unconditionality as the only basis input. -/
theorem unconditional_subset_projections : Spec.UnconditionalSubsetProjections := by
  intro 𝕜 E _ _ _ _ e hu
  let h := (rawBasis_iff_uniqueOrderedExpansions e).mpr hu.1
  exact ⟨h, raw_subset_projections h hu⟩

/-- Finite and empty lists use their genuine finite index type. -/
theorem finite_subset_projections : Spec.FiniteSubsetProjections := by
  intro 𝕜 E _ _ _ _ d e h
  obtain ⟨b, hb, hc, _⟩ := finite_native_basis h
  have hp := native_subset_projections b
  have hcoords : (fun x i => b.coord i x) = C15Basis.Spec.finiteCoordinates h := by
    funext x i
    exact hc i x
  simpa only [hb, hcoords] using hp

open ExpandedFA.P1.C15SubsetProjections.Spec C01SequenceSpaces

/-- Every finite exponent p ≥ 1, including p = 1. -/
theorem canonical_lp_unconditional_expansion : Spec.LpExpansion.{u} := by
  intro 𝕜 _ p _ hp x
  have he (n : ℕ) : x n • lp.single p n (1 : 𝕜) =
      lp.single (E := fun _ : ℕ => 𝕜) p n (x n) := by
    rw [← lp.single_smul]
    simp
  simp_rw [he]
  exact lp.hasSum_single hp x

namespace SequenceExamples
variable {𝕜 : Type u} [RCLike 𝕜]

lemma c0_finiteSubsum_apply (x : SequenceC0 𝕜) (F : Finset ℕ) (j : ℕ) :
    (C15Unconditional.Spec.finiteSubsumValue (fun n => x.val n • c0Unit 𝕜 n) F).val j =
      if j ∈ F then x.val j else 0 := by
  classical
  change (∑ i ∈ F, x.val i • c0Unit 𝕜 i).val j = _
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul_of_tower, c0Unit, ← lp.single_smul, smul_eq_mul,
    mul_one, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

end SequenceExamples
open SequenceExamples

theorem canonical_c0_unconditional_expansion :
    Spec.C0Expansion.{u} := by
  intro 𝕜 _ x
  change Tendsto (C15Unconditional.Spec.finiteSubsumValue (fun n => x.val n • c0Unit 𝕜 n)) atTop (𝓝 x)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp x.property (ε / 2) (half_pos hε)
  refine ⟨Finset.range M, fun F hF => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  change ‖(C15Unconditional.Spec.finiteSubsumValue (fun n => x.val n • c0Unit 𝕜 n) F).val - x.val‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (half_pos hε).le
  intro j
  change ‖(C15Unconditional.Spec.finiteSubsumValue (fun n => x.val n • c0Unit 𝕜 n) F).val j - x.val j‖ ≤ ε / 2
  rw [c0_finiteSubsum_apply]
  split_ifs with hj
  · simpa using (half_pos hε).le
  · have hjM : M ≤ j := by
      by_contra hn
      exact hj (hF (Finset.mem_range.mpr (Nat.lt_of_not_ge hn)))
    simpa using (hM j hjM).le

namespace SequenceExamples
variable {𝕜 : Type u} [RCLike 𝕜]

/-- Evaluating an ordered finite synthesis retains precisely the first N coordinates. -/
lemma lp_partialSum_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ → 𝕜) (N j : ℕ) :
    orderedPartialSum (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1) a N j =
      if j < N then a j else 0 := by
  classical
  simp only [orderedPartialSum, C15Basis.Spec.orderedPartialSum,
    ← lp.single_smul, smul_eq_mul, mul_one, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Finset.sum_pi_single, Finset.mem_range]

lemma c0_partialSum_apply (a : ℕ → 𝕜) (N j : ℕ) :
    (orderedPartialSum (c0Unit 𝕜) a N).val j = if j < N then a j else 0 := by
  have he (n) : (c0Unit 𝕜 n).val = lp.single ∞ n (1 : 𝕜) := rfl
  change (∑ i ∈ Finset.range N, a i • c0Unit 𝕜 i).val j = _
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul_of_tower, he]
  exact lp_partialSum_apply ∞ a N j

/-- Coordinate continuity forces uniqueness of any ordered convergent expansion. -/
lemma lp_expansion_unique (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : SequenceLp 𝕜 p)
    (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum (fun n => lp.single p n (1 : 𝕜)) a) atTop (𝓝 x)) :
    a = fun n => x n := by
  funext j
  have h := (lp.lipschitzWith_one_eval p j).continuous.continuousAt.tendsto.comp ha
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (lp_partialSum_apply p a N j).trans (ite_eq_left hN) |>.symm

lemma c0_expansion_unique (x : SequenceC0 𝕜) (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum (c0Unit 𝕜) a) atTop (𝓝 x)) :
    a = fun n => x.val n := by
  funext j
  have h := (lp.lipschitzWith_one_eval ∞ j).continuous.continuousAt.tendsto.comp
    (continuous_subtype_val.tendsto x |>.comp ha)
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (c0_partialSum_apply a N j).trans (ite_eq_left hN) |>.symm

end SequenceExamples

/-- The standard ℓᵖ vectors have unique ordered expansions, and those
expansions converge as finite-subset nets. -/
theorem canonical_lp_unconditional : Spec.LpUnconditional.{u} := by
  intro 𝕜 _ p _ hp
  have hb : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜)
      (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1) := by
    constructor
    · intro n hn
      have hz := congrArg (fun x : SequenceLp 𝕜 p => x n) hn
      simp at hz
    · intro x
      exact ⟨(fun n => x n),
        ((C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp
          (canonical_lp_unconditional_expansion 𝕜 p hp x)).tendsto_sum_nat,
        fun a ha => lp_expansion_unique p x a ha⟩
  apply (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 _ _).mpr
  refine ⟨(rawBasis_iff_uniqueOrderedExpansions _).mp hb, ?_⟩
  intro x a ha
  have he := lp_expansion_unique p x a ((C01Banach.hasSequentialSum_iff _ _ _).mp ha)
  rw [he]
  exact canonical_lp_unconditional_expansion 𝕜 p hp x

/-- Null-sequence tails are uniformly small after discarding any coordinates. -/
theorem canonical_c0_unconditional : Spec.C0Unconditional.{u} := by
  intro 𝕜 _
  have hb : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (c0Unit 𝕜) := by
    constructor
    · intro n hn
      have hz := congrArg (fun x : SequenceC0 𝕜 => x.val n) hn
      simp [c0Unit] at hz
    · intro x
      exact ⟨(fun n => x.val n),
        ((C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp
          (canonical_c0_unconditional_expansion 𝕜 x)).tendsto_sum_nat,
        fun a ha => c0_expansion_unique x a ha⟩
  apply (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 _ _).mpr
  refine ⟨(rawBasis_iff_uniqueOrderedExpansions _).mp hb, ?_⟩
  intro x a ha
  have he := c0_expansion_unique x a ((C01Banach.hasSequentialSum_iff _ _ _).mp ha)
  rw [he]
  exact canonical_c0_unconditional_expansion 𝕜 x

/-- Density of the orthonormal span gives its finite-subset expansion in
both real and complex Hilbert spaces, without an enumeration assumption. -/
theorem complete_orthonormal_unconditional_expansion :
    Spec.HilbertExpansion.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc x
  exact ExpandedFA.Hilbert.OrthonormalExpansion.finiteSubsetNet_expansion 𝕜 H I e
    ((ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 H I e he).mpr hc) x

namespace HilbertExamples
variable {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Scalar-linear pairing identifies coefficients before any Schauder
coordinate map is postulated. -/
lemma orthonormal_ordered_coefficients {e : ℕ → H} (he : Orthonormal 𝕜 e)
    (x : H) (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum e a) atTop (𝓝 x)) :
    a = fun n => inner 𝕜 (e n) x := by
  funext j
  have ht := ((innerSL 𝕜 (e j)).continuous.tendsto x).comp ha
  apply tendsto_nhds_unique _ ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (he.inner_right_sum a (Finset.mem_range.mpr hN)).symm

lemma orthonormal_finite_coefficients {d : ℕ} {e : Fin d → H}
    (he : Orthonormal 𝕜 e) (x : H) (a : Fin d → 𝕜)
    (ha : (∑ i, a i • e i) = x) : a = fun i => inner 𝕜 (e i) x := by
  funext i
  rw [← ha]
  exact (he.inner_right_fintype a i).symm

lemma complete_reindex {I : Type u} (e : I → H)
    (hc : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤)
    {J : Type*} (σ : J ≃ I) :
    (Submodule.span 𝕜 (Set.range (e ∘ σ))).topologicalClosure = ⊤ := by
  have hr : Set.range (e ∘ σ) = Set.range e := σ.surjective.range_comp e
  rwa [hr]

end HilbertExamples
open HilbertExamples

theorem complete_orthonormal_sequence_unconditional :
    Spec.HilbertSequence.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc σ
  have ho : Orthonormal 𝕜 (e ∘ σ) := he.comp σ σ.injective
  have ht := complete_reindex e hc σ
  have hx (x : H) := complete_orthonormal_unconditional_expansion (e ∘ σ) ho ht x
  have huniq (x : H) (a : ℕ → 𝕜)
      (ha : C01Banach.Spec.HasSequentialSumValue H (fun n => a n • e (σ n)) x) :
      a = fun n => inner 𝕜 (e (σ n)) x :=
    orthonormal_ordered_coefficients ho x a ((C01Banach.hasSequentialSum_iff _ _ _).mp ha)
  refine ⟨?_, huniq⟩
  apply (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 H (e ∘ σ)).mpr
  constructor
  · refine ⟨ho.ne_zero, fun x => ?_⟩
    exact ⟨(fun n => inner 𝕜 (e (σ n)) x),
      C15Unconditional.hasUnconditionalSum_hasSequentialSum _ x (hx x),
      fun a ha => huniq x a ha⟩
  · intro x a ha
    rw [huniq x a ha]
    exact hx x

theorem complete_orthonormal_finite_unconditional :
    Spec.HilbertFinite.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc d σ
  have ho : Orthonormal 𝕜 (e ∘ σ) := he.comp σ σ.injective
  have ht := complete_reindex e hc σ
  have huniq (x : H) (a : Fin d → 𝕜) (ha : (∑ n, a n • e (σ n)) = x) :
      a = fun n => inner 𝕜 (e (σ n)) x :=
    orthonormal_finite_coefficients ho x a ha
  refine ⟨?_, huniq⟩
  apply C15Unconditional.finiteBasis_isUnconditional
  refine ⟨ho.ne_zero, fun x => ?_⟩
  have hx := (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp
    (complete_orthonormal_unconditional_expansion (e ∘ σ) ho ht x)
  have hsum : (∑ n, inner 𝕜 (e (σ n)) x • e (σ n)) = x :=
    (hasSum_fintype _).unique hx
  exact ⟨(fun n => inner 𝕜 (e (σ n)) x), hsum, fun a ha => huniq x a ha⟩

/-- Countable finite systems include the empty basis of the zero space. -/
theorem complete_orthonormal_countable_unconditional :
    Spec.HilbertCountable.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ _ e he hc
  cases finite_or_infinite I with
  | inl hf =>
    let : Finite I := hf
    let := Fintype.ofFinite I
    let σ := (Fintype.equivFin I).symm
    exact Or.inl ⟨_, σ, (complete_orthonormal_finite_unconditional e he hc _ σ).1⟩
  | inr hi =>
    let : Infinite I := hi
    obtain ⟨σ⟩ : Nonempty (ℕ ≃ I) := nonempty_equiv_of_countable
    exact Or.inr ⟨σ, (complete_orthonormal_sequence_unconditional e he hc σ).1⟩

end ExpandedFA.P1.C15SubsetProjections
