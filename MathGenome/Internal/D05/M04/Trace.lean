import MathGenome.Internal.Specs.D05.M04.Trace
import MathGenome.Internal.D05.M04.ChangeBasis
import MathGenome.Internal.D05.M04.MatrixProduct

/-! Trace and its invariance, with the trace-functional theorem, K05.04.trace. -/
namespace D05.M04.Trace

open scoped BigOperators
open Specs.D05.M04.MatrixOfMap

theorem trace_definition : Specs.D05.M04.Trace.trace_definition := by
  intro R ι _ _ A
  rfl

theorem trace_mul_expansion : Specs.D05.M04.Trace.trace_mul_expansion := by
  intro R ι κ _ _ _ A B
  rfl

theorem trace_mul_comm : Specs.D05.M04.Trace.trace_mul_comm := by
  intro R ι κ _ _ _ A B
  rw [trace_mul_expansion, trace_mul_expansion, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem trace_conjugate : Specs.D05.M04.Trace.trace_conjugate := by
  intro R ι _ _ _ A P Q _ hPQ
  rw [trace_mul_comm, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]

theorem trace_nonsingular_conjugate : Specs.D05.M04.Trace.trace_nonsingular_conjugate := by
  intro R ι _ _ _ A P hP
  exact trace_conjugate A P P⁻¹ (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).mp hP))
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).mp hP))

theorem trace_matrix_of_map : Specs.D05.M04.Trace.trace_matrix_of_map := by
  intro K V _ _ _ _ n b T
  exact LinearMap.trace_eq_matrix_trace K b T

theorem basis_trace_invariant : Specs.D05.M04.Trace.basis_trace_invariant := by
  intro R V _ _ _ n m b c T
  exact (LinearMap.trace_eq_matrix_trace R b T).symm.trans
    (LinearMap.trace_eq_matrix_trace R c T)

theorem change_basis_trace : Specs.D05.M04.Trace.change_basis_trace := by
  intro R V _ _ _ n b c T
  exact ⟨congrArg Matrix.trace (D05.M04.ChangeBasis.change_basis b c b c T),
    basis_trace_invariant c b T⟩

theorem trace_linear_combination : Specs.D05.M04.Trace.trace_linear_combination := by
  intro R ι _ _ a b A B
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

theorem operator_trace_linear_combination :
    Specs.D05.M04.Trace.operator_trace_linear_combination := by
  intro K V _ _ _ _ a b S T
  simp only [map_add, map_smul, smul_eq_mul]

theorem trace_empty : Specs.D05.M04.Trace.trace_empty := by
  intro R ι _ _ _ A
  exact Matrix.trace_eq_zero_of_isEmpty A

theorem operator_trace_zero_dimension : Specs.D05.M04.Trace.operator_trace_zero_dimension := by
  intro K V _ _ _ _ T h
  have : Subsingleton V := (Module.finrank_zero_iff.mp h)
  have hT : T = 0 := Subsingleton.elim _ _
  rw [hT, map_zero]

private def commutatorSpan (K : Type*) [Field K] (n : ℕ) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K {C | ∃ A B : Matrix (Fin n) (Fin n) K, C = A * B - B * A}

private theorem commutator_mem_span {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) :
    A * B - B * A ∈ commutatorSpan K n :=
  Submodule.subset_span ⟨A, B, rfl⟩

/-- Subtracting the trace in one diagonal slot leaves a sum of commutators. -/
private theorem centered_mem_span {K : Type*} [Field K] {n : ℕ}
    (k : Fin n) (A : Matrix (Fin n) (Fin n) K) :
    A - Matrix.trace A • Matrix.single k k 1 ∈ commutatorSpan K n := by
  have hsingle (i j : Fin n) (a : K) :
      Matrix.single i j a - Matrix.trace (Matrix.single i j a) • Matrix.single k k 1 ∈
        commutatorSpan K n := by
    by_cases hij : i = j
    · subst j
      have hd : Matrix.single i i (1 : K) - Matrix.single k k 1 ∈ commutatorSpan K n := by
        simpa only [Matrix.single_mul_single_same, one_mul] using
          commutator_mem_span (Matrix.single i k (1 : K)) (Matrix.single k i 1)
      simpa only [Matrix.trace_single_eq_same, smul_sub, Matrix.smul_single,
        smul_eq_mul, mul_one] using (commutatorSpan K n).smul_mem a hd
    · have ho : Matrix.single i j (1 : K) ∈ commutatorSpan K n := by
        simpa only [Matrix.single_mul_single_same, one_mul,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij) _, sub_zero] using
          commutator_mem_span (Matrix.single i i (1 : K)) (Matrix.single i j 1)
      simpa only [Matrix.trace_single_eq_of_ne i j a hij, zero_smul, sub_zero,
        Matrix.smul_single, smul_eq_mul, mul_one] using
        (commutatorSpan K n).smul_mem a ho
  let g : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K :=
    LinearMap.id - (Matrix.traceLinearMap (Fin n) K K).smulRight (Matrix.single k k 1)
  change g A ∈ commutatorSpan K n
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact hsingle i j (A i j)

theorem commutator_span_eq_ker : Specs.D05.M04.Trace.commutator_span_eq_ker := by
  intro K _ n
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro C ⟨A, B, rfl⟩
    change Matrix.trace (A * B - B * A) = 0
    rw [Matrix.trace_sub, trace_mul_comm, sub_self]
  · intro A hA
    change Matrix.trace A = 0 at hA
    by_cases hn : 0 < n
    · change A ∈ commutatorSpan K n
      have h := centered_mem_span ⟨0, hn⟩ A
      simpa only [hA, zero_smul, sub_zero] using h
    · have : IsEmpty (Fin n) := ⟨fun i => hn (Nat.zero_lt_of_lt i.isLt)⟩
      have hzero : A = 0 := Subsingleton.elim _ _
      rw [hzero]
      exact Submodule.zero_mem _

theorem cyclic_functional_iff : Specs.D05.M04.Trace.cyclic_functional_iff := by
  intro K _ n hn f
  let k : Fin n := ⟨0, hn⟩
  let E : Matrix (Fin n) (Fin n) K := Matrix.single k k 1
  have hE : Matrix.trace E = 1 := Matrix.trace_single_eq_same k 1
  constructor
  · intro hf
    have hker : commutatorSpan K n ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro C ⟨A, B, rfl⟩
      change f (A * B - B * A) = 0
      rw [map_sub, hf, sub_self]
    have hfactor : f = f E • Matrix.traceLinearMap (Fin n) K K := by
      apply LinearMap.ext
      intro A
      have h := hker (centered_mem_span k A)
      change f (A - Matrix.trace A • E) = 0 at h
      simpa only [map_sub, map_smul, sub_eq_zero, smul_eq_mul,
        LinearMap.smul_apply, Matrix.traceLinearMap_apply, mul_comm] using h
    refine ⟨f E, hfactor, ?_⟩
    intro c hc
    have heq := congrArg (fun g : Matrix (Fin n) (Fin n) K →ₗ[K] K => g E) hc
    simpa only [LinearMap.smul_apply, Matrix.traceLinearMap_apply, hE,
      smul_eq_mul, mul_one] using heq.symm
  · rintro ⟨c, rfl, _⟩ A B
    change c • Matrix.trace (A * B) = c • Matrix.trace (B * A)
    rw [trace_mul_comm]

theorem normalized_cyclic_functional : Specs.D05.M04.Trace.normalized_cyclic_functional := by
  intro K _ n hn f hf hnorm hchar
  obtain ⟨c, hc, _⟩ := (cyclic_functional_iff hn f).mp hf
  have hcn : c * (n : K) = 1 * (n : K) := by
    simpa only [hc, LinearMap.smul_apply, Matrix.traceLinearMap_apply,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul, one_mul] using hnorm
  have hc1 : c = 1 := (mul_right_cancel₀ hchar) hcn
  simpa only [hc1, one_smul] using hc

theorem empty_functional : Specs.D05.M04.Trace.empty_functional := by
  intro K _ f
  constructor
  · apply LinearMap.ext
    intro A
    have hA : A = 0 := Subsingleton.elim _ _
    simp only [hA, map_zero]
  · intro c
    apply LinearMap.ext
    intro A
    simp only [LinearMap.smul_apply, Matrix.traceLinearMap_apply,
      Matrix.trace_fin_zero, smul_zero, LinearMap.zero_apply]

theorem normalization_counterexample : Specs.D05.M04.Trace.normalization_counterexample := by
  refine ⟨by intros; rfl, by decide, ?_⟩
  intro h
  have heq := congrArg
    (fun f : Matrix (Fin 2) (Fin 2) (ZMod 2) →ₗ[ZMod 2] ZMod 2 =>
      f (Matrix.single 0 0 1)) h
  simp only [LinearMap.zero_apply, Matrix.traceLinearMap_apply,
    Matrix.trace_single_eq_same, zero_ne_one] at heq

end D05.M04.Trace
