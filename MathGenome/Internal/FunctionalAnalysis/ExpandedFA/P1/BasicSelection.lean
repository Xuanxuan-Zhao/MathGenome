import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasicSelection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15BasisCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EquivalentBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.BasicSelection
open ExpandedFA.P1.C15Basis.Spec ExpandedFA.P1.EquivalentBases.Spec
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite set of ambient norm-one-or-less functionals approximately norms
an entire finite-dimensional subspace, including its zero vector. -/
theorem finite_norming_set (P : Submodule 𝕜 E) [FiniteDimensional 𝕜 P]
    {c : ℝ} (hc : 1 < c) :
    ∃ F : Finset (E →L[𝕜] 𝕜),
      (∀ f ∈ F, ‖f‖ ≤ 1) ∧
      ∀ z ∈ P, ∃ f ∈ F, ‖z‖ ≤ c * ‖f z‖ := by
  classical
  let D := {f : E →L[𝕜] 𝕜 // ‖f‖ ≤ 1}
  let U (f : D) : Set P := {z | 1 < c * ‖f.val z.val‖}
  have ho (f : D) : IsOpen (U f) :=
    isOpen_lt continuous_const
      (continuous_const.mul (f.val.continuous.comp continuous_subtype_val).norm)
  have hcov : Metric.sphere (0 : P) 1 ⊆ ⋃ f : D, U f := by
    intro z hz
    have hz' : ‖(z : E)‖ = 1 := by simpa using hz
    obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E z.val
    refine Set.mem_iUnion.mpr ⟨⟨f, hf⟩, ?_⟩
    change 1 < c * ‖f z.val‖
    simpa [hfx, hz'] using hc
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : P) 1).elim_finite_subcover U ho hcov
  refine ⟨insert 0 (t.image Subtype.val), ?_, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · simp
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hf
      exact f.property
  · intro z hz
    by_cases hz0 : z = 0
    · exact ⟨0, Finset.mem_insert_self _ _, by simp [hz0]⟩
    let w : P := ⟨(‖z‖⁻¹ : 𝕜) • z, P.smul_mem _ hz⟩
    have hw : w ∈ Metric.sphere (0 : P) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖(‖z‖⁻¹ : 𝕜) • z‖ = 1
      exact norm_smul_inv_norm hz0
    obtain ⟨f, hft, hf⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨f.val, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f, hft, rfl⟩), ?_⟩
    have hf0 : 1 < c * ‖f.val ((‖z‖⁻¹ : 𝕜) • z)‖ := hf
    have hf' : 1 ≤ c * (‖z‖⁻¹ * ‖f.val z‖) := by
      simpa only [map_smul, norm_smul, norm_inv, RCLike.norm_coe_norm] using hf0.le
    calc
      ‖z‖ = ‖z‖ * 1 := by ring
      _ ≤ ‖z‖ * (c * (‖z‖⁻¹ * ‖f.val z‖)) :=
        mul_le_mul_of_nonneg_left hf' (norm_nonneg z)
      _ = c * ‖f.val z‖ := by
        rw [← mul_assoc, mul_comm ‖z‖ c, mul_assoc c, ← mul_assoc ‖z‖,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0), one_mul]

/-- Finitely many continuous linear tests cannot separate all vectors of an
infinite-dimensional space; their common kernel contains a unit vector. -/
theorem unit_vector_in_kernels (hInf : ¬FiniteDimensional 𝕜 E)
    (F : Finset (E →L[𝕜] 𝕜)) :
    ∃ x : E, ‖x‖ = 1 ∧ ∀ f ∈ F, f x = 0 := by
  classical
  let S : E →ₗ[𝕜] (F → 𝕜) :=
    { toFun := fun x f => f.val x
      map_add' := fun x y => by ext f; exact map_add f.val x y
      map_smul' := fun a x => by ext f; exact map_smul f.val a x }
  have hn : ¬Function.Injective S := fun hi => hInf (FiniteDimensional.of_injective S hi)
  have hnz : ∃ z : E, z ≠ 0 ∧ S z = 0 := by
    by_contra h
    push Not at h
    apply hn
    intro x y hxy
    have hz : S (x - y) = 0 := by simp [map_sub, hxy]
    have hz0 : x - y = 0 := by
      by_contra hne
      exact h (x - y) hne hz
    exact sub_eq_zero.mp hz0
  obtain ⟨z, hz0, hz⟩ := hnz
  have hz' : ∀ f ∈ F, f z = 0 := by
    intro f hf
    exact congrFun hz ⟨f, hf⟩
  refine ⟨(‖z‖⁻¹ : 𝕜) • z, norm_smul_inv_norm hz0, ?_⟩
  intro f hf
  simp [map_smul, hz' f hf]

/-- The retained finite norming sets annihilate every subsequent vector. This
bounds every prefix directly by the same c, without an infinite product. -/
theorem exists_normalized_prefix_bound (hInf : ¬FiniteDimensional 𝕜 E)
    {c : ℝ} (hc : 1 < c) :
    ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
      ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
        ‖orderedPartialSum x a m‖ ≤ c * ‖orderedPartialSum x a N‖ := by
  classical
  let A := E × Finset (E →L[𝕜] 𝕜)
  let Q (b : A) (t : Set A) : Prop :=
    ‖b.1‖ = 1 ∧ (∀ f ∈ b.2, ‖f‖ ≤ 1) ∧
    (∀ z ∈ Submodule.span 𝕜 (insert b.1 (Prod.fst '' t)),
      ∃ f ∈ b.2, ‖z‖ ≤ c * ‖f z‖) ∧
    ∀ b' ∈ t, ∀ f ∈ b'.2, f b.1 = 0
  have hstep (t : Set A) (ht : t.Finite) : ∃ b, Q b t := by
    let F := ht.toFinset.biUnion Prod.snd
    obtain ⟨z, hz, hzF⟩ := unit_vector_in_kernels hInf F
    let P := Submodule.span 𝕜 (insert z (Prod.fst '' t))
    haveI : FiniteDimensional 𝕜 P := FiniteDimensional.span_of_finite 𝕜 ((ht.image _).insert z)
    obtain ⟨G, hG, hn⟩ := finite_norming_set (𝕜 := 𝕜) P hc
    refine ⟨(z, G), hz, hG, hn, ?_⟩
    intro b hb f hf
    apply hzF f
    exact Finset.mem_biUnion.mpr ⟨b, ht.mem_toFinset.mpr hb, hf⟩
  obtain ⟨b, hb⟩ := Set.seq_of_forall_finite_exists hstep
  let x : ℕ → E := fun n => (b n).1
  refine ⟨x, fun n => (hb n).1, ?_⟩
  intro a m N hmN
  cases m with
  | zero => simp only [orderedPartialSum, Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
  | succ m =>
    have hmem : orderedPartialSum x a (m + 1) ∈
        Submodule.span 𝕜 (insert (b m).1 (Prod.fst '' (b '' Set.Iio m))) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) with h | rfl
      · exact Set.mem_insert_of_mem _ ⟨b i, ⟨i, h, rfl⟩, rfl⟩
      · exact Set.mem_insert _ _
    obtain ⟨f, hf, hnorm⟩ := (hb m).2.2.1 _ hmem
    have heq : f (orderedPartialSum x a N) = f (orderedPartialSum x a (m + 1)) := by
      simp only [orderedPartialSum, map_sum, map_smul]
      symm
      apply Finset.sum_subset (Finset.range_mono hmN)
      intro i hi hin
      have hmi : m < i := by
        have := Finset.mem_range.mp hi
        have := Nat.not_lt.mp (fun h => hin (Finset.mem_range.mpr h))
        omega
      have hzero : f (x i) = 0 :=
        (hb i).2.2.2 (b m) ⟨m, hmi, rfl⟩ f hf
      simp [hzero]
    calc
      ‖orderedPartialSum x a (m + 1)‖ ≤ c * ‖f (orderedPartialSum x a (m + 1))‖ := hnorm
      _ = c * ‖f (orderedPartialSum x a N)‖ := by rw [heq]
      _ ≤ c * ‖orderedPartialSum x a N‖ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact (f.le_opNorm _).trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right ((hb m).2.1 f hf) (norm_nonneg _))

/-- A version of the kernel construction carrying arbitrary auxiliary data.
The extension condition is local to finitely many previous data and tests. -/
theorem kernel_sequence {I : Type*} (P : I → E → Prop) (r : I → I → Prop)
    (extend : ∀ t : Finset I, ∀ F : Finset (E →L[𝕜] 𝕜),
      ∃ i z, P i z ∧ z ≠ 0 ∧ (∀ j ∈ t, r j i) ∧ (∀ f ∈ F, f z = 0))
    {c : ℝ} (hc : 1 < c) :
    ∃ i : ℕ → I, ∃ x : ℕ → E,
      (∀ n, P (i n) (x n)) ∧ (∀ n, x n ≠ 0) ∧
      (∀ m n, m < n → r (i m) (i n)) ∧
      ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
        ‖orderedPartialSum x a m‖ ≤ c * ‖orderedPartialSum x a N‖ := by
  classical
  let A := I × E × Finset (E →L[𝕜] 𝕜)
  let Q (b : A) (t : Set A) : Prop :=
    P b.1 b.2.1 ∧ b.2.1 ≠ 0 ∧ (∀ f ∈ b.2.2, ‖f‖ ≤ 1) ∧
    (∀ z ∈ Submodule.span 𝕜 (insert b.2.1 ((fun d : A => d.2.1) '' t)),
      ∃ f ∈ b.2.2, ‖z‖ ≤ c * ‖f z‖) ∧
    ∀ b' ∈ t, r b'.1 b.1 ∧ ∀ f ∈ b'.2.2, f b.2.1 = 0
  have hstep (t : Set A) (ht : t.Finite) : ∃ b, Q b t := by
    let F := ht.toFinset.biUnion (fun d : A => d.2.2)
    obtain ⟨i, z, hzP, hz0, hir, hzF⟩ := extend (ht.toFinset.image Prod.fst) F
    let V := Submodule.span 𝕜 (insert z ((fun d : A => d.2.1) '' t))
    haveI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 ((ht.image _).insert z)
    obtain ⟨G, hG, hn⟩ := finite_norming_set (𝕜 := 𝕜) V hc
    refine ⟨(i, z, G), hzP, hz0, hG, hn, ?_⟩
    intro b hb
    refine ⟨hir b.1 (Finset.mem_image.mpr ⟨b, ht.mem_toFinset.mpr hb, rfl⟩), ?_⟩
    intro f hf
    exact hzF f (Finset.mem_biUnion.mpr ⟨b, ht.mem_toFinset.mpr hb, hf⟩)
  obtain ⟨b, hb⟩ := Set.seq_of_forall_finite_exists hstep
  let x : ℕ → E := fun n => (b n).2.1
  refine ⟨fun n => (b n).1, x, fun n => (hb n).1,
    fun n => (hb n).2.1, ?_, ?_⟩
  · intro m n hmn
    exact ((hb n).2.2.2.2 (b m) ⟨m, hmn, rfl⟩).1
  · intro a m N hmN
    cases m with
    | zero => simp only [orderedPartialSum, Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
    | succ m =>
      have hmem : orderedPartialSum x a (m + 1) ∈
          Submodule.span 𝕜 (insert (b m).2.1 ((fun d : A => d.2.1) '' (b '' Set.Iio m))) := by
        apply Submodule.sum_mem
        intro i hi
        apply Submodule.smul_mem
        apply Submodule.subset_span
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) with h | rfl
        · exact Set.mem_insert_of_mem _ ⟨b i, ⟨i, h, rfl⟩, rfl⟩
        · exact Set.mem_insert _ _
      obtain ⟨f, hf, hnorm⟩ := (hb m).2.2.2.1 _ hmem
      have heq : f (orderedPartialSum x a N) = f (orderedPartialSum x a (m + 1)) := by
        simp only [orderedPartialSum, map_sum, map_smul]
        symm
        apply Finset.sum_subset (Finset.range_mono hmN)
        intro i hi hin
        have hmi : m < i := by
          have := Nat.not_lt.mp (fun h => hin (Finset.mem_range.mpr h))
          omega
        have hzero : f (x i) = 0 :=
          ((hb i).2.2.2.2 (b m) ⟨m, hmi, rfl⟩).2 f hf
        simp [hzero]
      calc
        ‖orderedPartialSum x a (m + 1)‖ ≤ c * ‖f (orderedPartialSum x a (m + 1))‖ := hnorm
        _ = c * ‖f (orderedPartialSum x a N)‖ := by rw [heq]
        _ ≤ c * ‖orderedPartialSum x a N‖ := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact (f.le_opNorm _).trans (by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right ((hb m).2.2.1 f hf) (norm_nonneg _))

/-- Weakly null vectors can be corrected into finitely many exact kernels
with any fixed positive error tolerance. The right inverse is defined only
on the finite-dimensional range of the finite evaluation map. -/
theorem eventually_kernel_approximation (s : ℕ → E)
    (hs : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 0))
    (F : Finset (E →L[𝕜] 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z : E, ‖z - s n‖ < ε ∧ ∀ f ∈ F, f z = 0 := by
  classical
  let S : E →L[𝕜] (F → 𝕜) := ContinuousLinearMap.pi (fun f : F => f.val)
  let S' : E →L[𝕜] S.range := S.rangeRestrict
  obtain ⟨R, hR⟩ := S'.exists_rightInverse_of_surjective (by
    exact LinearMap.range_rangeRestrict S.toLinearMap)
  have hS : Tendsto (fun n => S (s n)) atTop (𝓝 0) :=
    tendsto_pi_nhds.mpr (fun f => hs f.val)
  have hS' : Tendsto (fun n => S' (s n)) atTop (𝓝 0) := by
    exact tendsto_subtype_rng.mpr hS
  have hRS : Tendsto (fun n => R (S' (s n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (R.continuous.tendsto 0).comp hS'
  have he := (Metric.tendsto_atTop.mp hRS) ε hε
  obtain ⟨N, hN⟩ := he
  filter_upwards [eventually_ge_atTop N] with n hn
  refine ⟨s n - R (S' (s n)), ?_, ?_⟩
  · simpa only [sub_sub_cancel_left, norm_neg, dist_zero_right] using hN n hn
  · intro f hf
    have hid : S' (R (S' (s n))) = S' (s n) := by
      exact congrArg (fun L : S.range →L[𝕜] S.range => L (S' (s n))) hR
    have hi : f (R (S' (s n))) = f (s n) :=
      congrFun (congrArg Subtype.val hid) ⟨f, hf⟩
    simp [map_sub, hi]

/-- The finite estimate passes to the actual continuous truncations on the
closed span. In particular it bounds their real supremum, not an auxiliary norm. -/
theorem basic_sequence_of_prefix_bound [CompleteSpace E] {x : ℕ → E}
    (hx : ∀ n, x n ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
      ‖orderedPartialSum x a m‖ ≤ c * ‖orderedPartialSum x a N‖) :
    ∃ h : IsBasicSequence (𝕜 := 𝕜) x,
      ∃ T : ℕ → closedSpan (𝕜 := 𝕜) x →L[𝕜] closedSpan (𝕜 := 𝕜) x,
        (∀ N z, T N z = rawPartialSum h N z) ∧
        C15PartialSums.Spec.basisConstant T ≤ c := by
  have he (n) : spanVector (𝕜 := 𝕜) x n ≠ 0 := by
    intro h
    exact hx n (congrArg Subtype.val h)
  have hcoe (a : ℕ → 𝕜) (N : ℕ) :
      ((orderedPartialSum (spanVector (𝕜 := 𝕜) x) a N : closedSpan (𝕜 := 𝕜) x) : E) = orderedPartialSum x a N := by
    simp [orderedPartialSum, spanVector]
  have hp (a : ℕ → 𝕜) (m N : ℕ) (hmN : m ≤ N) :
      ‖orderedPartialSum (spanVector (𝕜 := 𝕜) x) a m‖ ≤
        c * ‖orderedPartialSum (spanVector (𝕜 := 𝕜) x) a N‖ := by
    change ‖((orderedPartialSum (spanVector (𝕜 := 𝕜) x) a m : closedSpan (𝕜 := 𝕜) x) : E)‖ ≤
      c * ‖((orderedPartialSum (spanVector (𝕜 := 𝕜) x) a N : closedSpan (𝕜 := 𝕜) x) : E)‖
    simpa only [hcoe] using hb a m N hmN
  have hd : Dense (Submodule.span 𝕜 (Set.range (spanVector (𝕜 := 𝕜) x)) :
      Set (closedSpan (𝕜 := 𝕜) x)) := by
    have hh := EquivalentBases.synthesis_dense (𝕜 := 𝕜) x
    change Dense (Set.range (Finsupp.linearCombination 𝕜 (spanVector x))) at hh
    simpa only [← LinearMap.coe_range, Finsupp.range_linearCombination] using hh
  have h : IsBasicSequence (𝕜 := 𝕜) x :=
    C15BasisCriterion.BasisCriterionProof.basis_of_prefix_bound he hd ⟨c, hp⟩
  obtain ⟨T, hT, _, _⟩ := C15PartialSums.raw_partial_sum_bounds h
  refine ⟨h, T, hT.agrees, ?_⟩
  have hcoord (a : ℕ →₀ 𝕜) : a = rawCoordinates h (EquivalentBases.synthesis x a) := by
    apply C15Basis.rawCoordinates_unique h
    obtain ⟨N, hN⟩ := C15BasisCriterion.BasisCriterionProof.finite_stabilizes (spanVector (𝕜 := 𝕜) x) a
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).symm⟩)
  have hn (N : ℕ) : ‖T N‖ ≤ c := by
    apply (T N).opNorm_le_bound hc
    intro z
    refine (EquivalentBases.synthesis_dense (𝕜 := 𝕜) x).induction_on z
      (isClosed_le (T N).continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro a
    rw [hT.agrees]
    change ‖orderedPartialSum (spanVector x) (rawCoordinates h (EquivalentBases.synthesis x a)) N‖ ≤ _
    rw [← hcoord a]
    exact C15BasisCriterion.BasisCriterionProof.prefix_bound hp a N
  exact ciSup_le hn

/-- Existence with the prescribed numerical basis constant. -/
theorem normalized_basic_sequence : Spec.NormalizedBasicSequence := by
  intro 𝕜 E _ _ _ _ hInf M hM
  obtain ⟨x, hx, hb⟩ := exists_normalized_prefix_bound hInf hM
  refine ⟨x, hx, ?_⟩
  apply basic_sequence_of_prefix_bound (fun n => ?_) (by linarith) hb
  intro h
  have := hx n
  simp [h] at this

/-- The norm lower bound is selected from the failure of norm convergence;
zero and arbitrarily small discarded terms cause no additional hypothesis. -/
theorem weakly_null_basic_subsequence : Spec.WeaklyNullBasicSubsequence := by
  intro 𝕜 E _ _ _ _ s hs hn
  classical
  have hscalar (f : E →L[𝕜] 𝕜) : Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
    simpa only [map_zero] using C12BoundedSequences.weak_evaluation_tendsto 𝕜 E s 0 hs f
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨a, ha, hna⟩ := hn
  have hfreq : ∃ᶠ n in atTop, a ≤ ‖s n‖ := by
    apply frequently_atTop.mpr
    intro N
    simpa only [dist_zero_right] using hna N
  let P (i : ℕ × ℕ) (z : E) : Prop :=
    a / 2 ≤ ‖z‖ ∧ ‖z - s i.2‖ ≤ a / 64 * (1 / 2 : ℝ) ^ i.1
  let r (i j : ℕ × ℕ) : Prop := i.1 < j.1 ∧ i.2 < j.2
  have hext (t : Finset (ℕ × ℕ)) (F : Finset (E →L[𝕜] 𝕜)) :
      ∃ i z, P i z ∧ z ≠ 0 ∧ (∀ j ∈ t, r j i) ∧ (∀ f ∈ F, f z = 0) := by
    let k := t.sup Prod.fst + 1
    let N := t.sup Prod.snd + 1
    let ε : ℝ := a / 64 * (1 / 2 : ℝ) ^ k
    have hε : 0 < ε := by positivity
    have hεa : ε ≤ a / 2 := by
      have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ a / 64)
      dsimp [ε]
      linarith
    obtain ⟨n, hnorm, hcorr, hnN⟩ :=
      (hfreq.and_eventually ((eventually_kernel_approximation s hscalar F hε).and
        (eventually_ge_atTop N))).exists
    obtain ⟨z, hz, hzF⟩ := hcorr
    have htri : ‖s n‖ ≤ ‖z - s n‖ + ‖z‖ := by
      simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (s n - z) z
    have hzlow : a / 2 ≤ ‖z‖ := by linarith
    refine ⟨(k, n), z, ⟨hzlow, hz.le⟩, ?_, ?_, hzF⟩
    · exact norm_pos_iff.mp (by linarith)
    · intro j hj
      have h₁ : j.1 ≤ t.sup Prod.fst := Finset.le_sup hj
      have h₂ : j.2 ≤ t.sup Prod.snd := Finset.le_sup hj
      exact ⟨by dsimp [k]; omega, by dsimp [N] at hnN; omega⟩
  obtain ⟨i, x, hP, hx, hir, hb⟩ := kernel_sequence P r hext (c := 2) (by norm_num)
  have hk : StrictMono (fun n => (i n).1) := fun m n hmn => (hir m n hmn).1
  have hi : StrictMono (fun n => (i n).2) := fun m n hmn => (hir m n hmn).2
  obtain ⟨h, T, hT, hK⟩ := basic_sequence_of_prefix_bound hx (by norm_num : (0 : ℝ) ≤ 2) hb
  have hlow (n) : a / 2 ≤ ‖x n‖ := (hP n).1
  have hmajor (n) : ‖s ((i n).2) - x n‖ / ‖x n‖ ≤ (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ n := by
    apply (div_le_iff₀ (by linarith [hlow n] : 0 < ‖x n‖)).mpr
    have herr : ‖s ((i n).2) - x n‖ ≤ a / 64 * (1 / 2 : ℝ) ^ (i n).1 := by
      simpa only [norm_sub_rev] using (hP n).2
    calc
      ‖s ((i n).2) - x n‖ ≤ a / 64 * (1 / 2 : ℝ) ^ (i n).1 := herr
      _ ≤ a / 64 * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hk.id_le n)) (by positivity)
      _ ≤ (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ n * ‖x n‖ := by
        nlinarith [hlow n, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hgeom : Summable (fun n : ℕ => (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ n) :=
    summable_geometric_two.mul_left _
  have hsum : Summable (fun n => ‖s ((i n).2) - x n‖ / ‖x n‖) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _) (norm_nonneg _)) hmajor hgeom
  have htotal : (∑' n, ‖s ((i n).2) - x n‖ / ‖x n‖) ≤ 1 / 16 := by
    calc
      _ ≤ ∑' n : ℕ, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ n := hsum.tsum_le_tsum hmajor hgeom
      _ = 1 / 16 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  have htotal0 : 0 ≤ ∑' n, ‖s ((i n).2) - x n‖ / ‖x n‖ :=
    tsum_nonneg (fun n => div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsmall : 2 * C15PartialSums.Spec.basisConstant T *
      (∑' n, ‖s ((i n).2) - x n‖ / ‖x n‖) < 1 := by
    have := mul_le_mul_of_nonneg_right hK htotal0
    nlinarith
  exact ⟨fun n => (i n).2, hi,
    (EquivalentBases.small_perturbation h T hT hsum hsmall).1⟩

end ExpandedFA.P1.BasicSelection
