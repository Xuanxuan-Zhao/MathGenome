import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C0NotComplemented
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

noncomputable section
open Filter
open scoped Topology ENNReal

namespace ExpandedFA.P1.C0NotComplemented
open C01SequenceSpaces
universe u

open Classical

/-- Coding the finite initial segment of an infinite binary branch. -/
def branchCode (b : ℕ → Bool) (n : ℕ) : ℕ :=
  Encodable.encode (List.ofFn fun i : Fin n => b i)

def branchSet (b : ℕ → Bool) : Set ℕ := Set.range (branchCode b)

lemma branchCode_injective (b : ℕ → Bool) : Function.Injective (branchCode b) := by
  intro n m h
  have h' := Encodable.encode_injective h
  simpa using congrArg List.length h'

lemma branchSet_infinite (b : ℕ → Bool) : (branchSet b).Infinite :=
  Set.infinite_range_of_injective (branchCode_injective b)

lemma branchSet_inter_finite {b c : ℕ → Bool} (hbc : b ≠ c) :
    (branchSet b ∩ branchSet c).Finite := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, b k ≠ c k := Function.ne_iff.mp hbc
  apply (Set.finite_range (fun n : Fin (k + 1) => branchCode b n)).subset
  rintro x ⟨⟨n, rfl⟩, ⟨m, hm⟩⟩
  have heq := Encodable.encode_injective hm
  have hmn : m = n := by simpa using congrArg List.length heq
  subst m
  have hn : n ≤ k := by
    by_contra hn
    have hkn : k < n := by omega
    have heval := congrArg (fun l : List Bool => l[k]?) heq
    have : c k = b k := by simpa [List.getElem?_eq_getElem, hkn] using heval
    exact hk this.symm
  exact ⟨⟨n, by omega⟩, rfl⟩

/-- The bounded characteristic sequence of an arbitrary subset of ℕ. -/
def indicator (𝕜 : Type u) [RCLike 𝕜] (A : Set ℕ) : SequenceLInfinity 𝕜 :=
  ⟨fun n => if n ∈ A then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

@[simp] lemma indicator_apply (𝕜 : Type u) [RCLike 𝕜] (A : Set ℕ) (n : ℕ) :
    indicator 𝕜 A n = if n ∈ A then 1 else 0 := rfl

lemma finite_support_mem_c0 {𝕜 : Type u} [RCLike 𝕜] (x : SequenceLInfinity 𝕜)
    (hx : (Function.support (fun n => x n)).Finite) : x ∈ sequenceC0Submodule 𝕜 := by
  apply tendsto_const_nhds.congr'
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hx.eventually_cofinite_notMem] with n hn
  simpa [Function.mem_support, eq_comm] using hn

lemma indicator_not_mem_c0 {𝕜 : Type u} [RCLike 𝕜] {A : Set ℕ} (hA : A.Infinite) :
    indicator 𝕜 A ∉ sequenceC0Submodule 𝕜 := by
  intro h
  have he := (tendsto_order.1 h.norm).2 (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  obtain ⟨n, hn, hlarge⟩ := hA.exists_notMem_finset (Finset.range (N + 1))
  have hlarge : N < n := by simpa using hlarge
  have := hN n hlarge.le
  norm_num [hn] at this

/-- A phase turning a scalar into its nonnegative modulus. Zero causes no exception. -/
def phase {𝕜 : Type u} [RCLike 𝕜] (z : 𝕜) : 𝕜 := (‖z‖ : 𝕜) / z

lemma phase_mul {𝕜 : Type u} [RCLike 𝕜] (z : 𝕜) :
    phase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, div_mul_cancel₀ _ hz]

lemma norm_phase_le {𝕜 : Type u} [RCLike 𝕜] (z : 𝕜) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, norm_div, div_self (norm_ne_zero_iff.mpr hz)]

/-- Finitely many almost disjoint sets become disjoint outside a finite set. -/
lemma finite_collision_set {ι : Type*} (A : ι → Set ℕ)
    (hA : ∀ i j, i ≠ j → (A i ∩ A j).Finite) (s : Finset ι) :
    ∃ B : Set ℕ, B.Finite ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i ∩ A j ⊆ B := by
  classical
  let B := ⋃ i ∈ s, ⋃ j ∈ s, if i = j then (∅ : Set ℕ) else A i ∩ A j
  refine ⟨B, ?_, ?_⟩
  · apply s.finite_toSet.biUnion
    intro i hi
    apply s.finite_toSet.biUnion
    intro j hj
    by_cases h : i = j
    · simp [h]
    · simpa [h] using hA i j h
  · intro i hi j hj hij n hn
    simp only [B, Set.mem_iUnion]
    exact ⟨i, hi, j, hj, by simpa [hij] using hn⟩

/-- Cutting off a finite set does not change a functional annihilating c₀. -/
lemma map_indicator_sdiff {𝕜 : Type u} [RCLike 𝕜]
    (f : SequenceLInfinity 𝕜 →L[𝕜] 𝕜)
    (hf : ∀ x ∈ sequenceC0Submodule 𝕜, f x = 0)
    (A B : Set ℕ) (hB : B.Finite) :
    f (indicator 𝕜 (A \ B)) = f (indicator 𝕜 A) := by
  have hz : f (indicator 𝕜 A - indicator 𝕜 (A \ B)) = 0 := by
    apply hf
    apply finite_support_mem_c0
    apply hB.subset
    intro n hn
    by_contra hnB
    apply hn
    simp only [lp.coeFn_sub, Pi.sub_apply, indicator_apply]
    simp [hnB]
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- The finite ℓ¹ bound for the values of an annihilating functional on an
almost disjoint family. This includes complex phases. -/
lemma sum_norm_map_indicator_le {𝕜 : Type u} [RCLike 𝕜] {ι : Type*}
    (A : ι → Set ℕ) (hA : ∀ i j, i ≠ j → (A i ∩ A j).Finite)
    (f : SequenceLInfinity 𝕜 →L[𝕜] 𝕜)
    (hf : ∀ x ∈ sequenceC0Submodule 𝕜, f x = 0) (s : Finset ι) :
    ∑ i ∈ s, ‖f (indicator 𝕜 (A i))‖ ≤ ‖f‖ := by
  classical
  obtain ⟨B, hB, hdis⟩ := finite_collision_set A hA s
  let a : ι → 𝕜 := fun i => phase (f (indicator 𝕜 (A i)))
  let y : SequenceLInfinity 𝕜 := ∑ i ∈ s, a i • indicator 𝕜 (A i \ B)
  have hy : ‖y‖ ≤ 1 := by
    apply lp.norm_le_of_forall_le (by norm_num)
    intro n
    change ‖(∑ i ∈ s, a i • indicator 𝕜 (A i \ B)) n‖ ≤ 1
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
    by_cases hn : ∃ i ∈ s, n ∈ A i \ B
    · obtain ⟨i, hi, hni⟩ := hn
      rw [Finset.sum_eq_single i]
      · simpa [indicator_apply, hni] using norm_phase_le (f (indicator 𝕜 (A i)))
      · intro j hj hji
        have hnj : n ∉ A j \ B := by
          intro hnj
          exact hni.2 (hdis i hi j hj hji.symm ⟨hni.1, hnj.1⟩)
        simp [hnj]
      · simp [hi]
    · have hz : ∀ i ∈ s, n ∉ A i \ B := by simpa using hn
      have hz' : ∀ i ∈ s, a i • indicator 𝕜 (A i \ B) n = 0 := by
        intro i hi
        simp only [indicator_apply, ite_eq_right (hz i hi), smul_zero]
      rw [Finset.sum_eq_zero hz']
      simp
  have hfy : f y = ((∑ i ∈ s, ‖f (indicator 𝕜 (A i))‖ : ℝ) : 𝕜) := by
    simp only [y, map_sum, map_smul, smul_eq_mul]
    simp_rw [map_indicator_sdiff f hf _ B hB]
    simp only [a, phase_mul]
  calc
    _ = ‖f y‖ := by rw [hfy, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    _ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
    _ ≤ ‖f‖ := by nlinarith [norm_nonneg f]

/-- Each annihilating functional sees only countably many almost disjoint indicators. -/
lemma countable_indicator_support {𝕜 : Type u} [RCLike 𝕜] {ι : Type*}
    (A : ι → Set ℕ) (hA : ∀ i j, i ≠ j → (A i ∩ A j).Finite)
    (f : SequenceLInfinity 𝕜 →L[𝕜] 𝕜)
    (hf : ∀ x ∈ sequenceC0Submodule 𝕜, f x = 0) :
    {i | f (indicator 𝕜 (A i)) ≠ 0}.Countable := by
  have hs : Summable (fun i => ‖f (indicator 𝕜 (A i))‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _)
      (sum_norm_map_indicator_le A hA f hf)
  simpa [Function.support] using hs.countable_support

/-- Cantor's diagonal argument, in a form useful for the binary-branch family. -/
lemma exists_branch_outside_countable (S : Set (ℕ → Bool)) (hS : S.Countable) :
    ∃ b : ℕ → Bool, b ∉ S := by
  obtain ⟨g, hg⟩ := Set.countable_iff_exists_subset_range.mp hS
  refine ⟨fun n => !(g n n), ?_⟩
  intro hb
  obtain ⟨n, hn⟩ := hg hb
  have he := congrFun hn n
  cases h : g n n <;> simp [h] at he

/-- There is no bounded retraction of bounded scalar sequences onto null sequences. -/
lemma no_retraction (𝕜 : Type u) [RCLike 𝕜]
    (P : SequenceLInfinity 𝕜 →L[𝕜] SequenceLInfinity 𝕜)
    (hfix : ∀ x ∈ sequenceC0Submodule 𝕜, P x = x)
    (hrange : ∀ x, P x ∈ sequenceC0Submodule 𝕜) : False := by
  let Q : SequenceLInfinity 𝕜 →L[𝕜] SequenceLInfinity 𝕜 :=
    ContinuousLinearMap.id 𝕜 _ - P
  let f : ℕ → SequenceLInfinity 𝕜 →L[𝕜] 𝕜 :=
    fun n => (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ n).comp Q
  have hf : ∀ n, ∀ x ∈ sequenceC0Submodule 𝕜, f n x = 0 := by
    intro n x hx
    change (x - P x) n = 0
    rw [hfix x hx, sub_self]
    rfl
  have hc : ∀ n, {b | f n (indicator 𝕜 (branchSet b)) ≠ 0}.Countable :=
    fun n => countable_indicator_support branchSet (fun _ _ => branchSet_inter_finite)
      (f n) (hf n)
  obtain ⟨b, hb⟩ := exists_branch_outside_countable
    (⋃ n, {b | f n (indicator 𝕜 (branchSet b)) ≠ 0}) (Set.countable_iUnion hc)
  have hQ : Q (indicator 𝕜 (branchSet b)) = 0 := by
    apply lp.ext
    funext n
    have hz : f n (indicator 𝕜 (branchSet b)) = 0 := by
      by_contra h
      exact hb (Set.mem_iUnion.mpr ⟨n, h⟩)
    exact hz
  have heq : indicator 𝕜 (branchSet b) = P (indicator 𝕜 (branchSet b)) := by
    change indicator 𝕜 (branchSet b) - P (indicator 𝕜 (branchSet b)) = 0 at hQ
    exact sub_eq_zero.mp hQ
  exact indicator_not_mem_c0 (branchSet_infinite b) (heq ▸ hrange _)

/-- The actual canonical c₀ submodule is not the range of any bounded projection. -/
theorem no_bounded_projection : Spec.NoProjection.{u} := by
  intro 𝕜 _ ⟨P, hPP, hr⟩
  apply no_retraction 𝕜 P
  · intro x hx
    have hx' : x ∈ P.range := hr.symm ▸ hx
    obtain ⟨y, rfl⟩ := hx'
    exact congrArg (fun T : SequenceLInfinity 𝕜 →L[𝕜] SequenceLInfinity 𝕜 => T y) hPP
  · intro x
    rw [← hr]
    exact ⟨x, rfl⟩

/-- Noncomplementation in the native topological direct-sum sense. -/
theorem not_complemented : Spec.NotComplemented.{u} := by
  intro 𝕜 _ ⟨P, hP⟩
  apply no_retraction 𝕜 ((sequenceC0Submodule 𝕜).subtypeL.comp P)
  · intro x hx
    exact congrArg Subtype.val (hP ⟨x, hx⟩)
  · intro x
    exact (P x).property

end ExpandedFA.P1.C0NotComplemented
