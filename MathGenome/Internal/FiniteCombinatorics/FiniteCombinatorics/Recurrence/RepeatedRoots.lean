import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.InitialValues
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.RootSequences
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.AlgebraMap
import Lean.Elab.Tactic.Omega

/-!
# Repeated characteristic roots

The basis assertion in `paper.tex`, Theorem p204:W16 (lines 489–548).
We use the accepted coefficient sequences and recurrence solution module.
The shift realizes polynomial annihilation, each root chain is triangular on
initial entries, and distinct generalized eigenspaces are independent. Counting
polynomial degrees then supplies the dimension needed for spanning.
-/

noncomputable section
open scoped BigOperators
open Polynomial
universe u
namespace FiniteCombinatorics.Recurrence
variable {K : Type u} [Field K]

/-- Iterating the left shift advances the index by the exponent. -/
theorem leftShift_pow_apply (k : ℕ) (a : ℕ → K) (n : ℕ) :
    (leftShift ^ k) a n = a (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (leftShift ^ k) a (n + 1) = a (n + (k + 1))
    rw [ih]
    congr 1
    omega

/-- The characteristic polynomial acting by shift encodes the recurrence. -/
theorem mem_solutionSpace_iff_aeval {r : ℕ} (c : Fin r → K) (a : ℕ → K) :
    a ∈ solutionSpace c ↔ (aeval leftShift (characteristicPolynomial c)) a = 0 := by
  rw [characteristicPolynomial_eq]
  simp only [map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C]
  change (∀ n, a (n + r) = ∑ j : Fin r, c j * a (n + j)) ↔ _
  rw [funext_iff]
  simp [LinearMap.sub_apply, LinearMap.sum_apply,
    leftShift_pow_apply, Algebra.algebraMap_eq_smul_one, sub_eq_zero]

/-- A polynomial multiple of an annihilator also annihilates a vector. -/
theorem aeval_apply_eq_zero_of_dvd {p q : K[X]} {a : ℕ → K}
    (h : p ∣ q) (ha : (aeval leftShift p) a = 0) :
    (aeval leftShift q) a = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [mul_comm p q, map_mul, Module.End.mul_apply, ha, map_zero]

/-- Every root chain is independent, including at the root zero. -/
theorem rootSequence_linearIndependent (lam : K) (m : ℕ) :
    LinearIndependent K (fun j : Fin m => rootSequence lam j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro d hd j
  have h : ∀ n, ∀ j : Fin m, j.val = n → d j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have heval := congrFun hd n
      have hs : ∑ k : Fin m, d k * rootSequence lam k n = d j := by
        rw [Finset.sum_eq_single j]
        · simp [rootSequence_coeff, hj]
        · intro k _ hkj
          by_cases hk : k.val < n
          · rw [ih k.val hk k rfl, zero_mul]
          · have hnk : n < k.val := by
              have : k.val ≠ n := fun h => hkj (Fin.ext (h.trans hj.symm))
              omega
            simp [rootSequence_coeff, Nat.not_le_of_gt hnk]
        · simp
      simpa only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hs] using heval
  exact h j.val j rfl

/-- Root chains for distinct roots are independent together. -/
theorem rootSequences_linearIndependent (s : Finset K) (m : K → ℕ) :
    LinearIndependent K (fun i : Σ lam : s, Fin (m lam.val) =>
      rootSequence i.1.val i.2.val) := by
  classical
  have hmem (lam : s) (j : Fin (m lam.val)) :
      rootSequence lam.val j.val ∈ (leftShift (K := K)).genEigenspace lam.val ⊤ := by
    apply Module.End.mem_genEigenspace_top.mpr
    exact ⟨j.val + 1, rootSequence_annihilation lam.val j.val⟩
  have hle (lam : s) : Submodule.span K (Set.range (fun j : Fin (m lam.val) =>
      rootSequence lam.val j.val)) ≤ (leftShift (K := K)).genEigenspace lam.val ⊤ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem lam j
  apply linearIndependent_iUnion_finite
    (f := fun (lam : s) (j : Fin (m lam.val)) => rootSequence lam.val j.val)
    (fun lam => rootSequence_linearIndependent lam.val _)
  intro lam t _ hnot
  have hi := (leftShift (K := K)).independent_genEigenspace ⊤
  have hi' := hi.comp (f := fun lam : s => lam.val) Subtype.val_injective
  exact (hi'.disjoint_biSup hnot).mono (hle lam) (iSup₂_mono fun mu _ => hle mu)

/-- A root vector lies in any recurrence whose characteristic polynomial contains
its required power of the corresponding linear factor. -/
theorem rootSequence_mem_of_dvd {r : ℕ} (c : Fin r → K) (lam : K) (j : ℕ)
    (h : (X - C lam) ^ (j + 1) ∣ characteristicPolynomial c) :
    rootSequence lam j ∈ solutionSpace c := by
  rw [mem_solutionSpace_iff_aeval]
  apply aeval_apply_eq_zero_of_dvd h
  simpa only [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    show (1 : Module.End K (ℕ → K)) = LinearMap.id from rfl] using
    rootSequence_annihilation lam j

/-- Under a split factorization every proposed basis vector is a solution. -/
theorem rootSequence_mem_solutionSpace {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (i : Σ lam : s, Fin (m lam.val)) :
    rootSequence i.1.val i.2.val ∈ solutionSpace c := by
  apply rootSequence_mem_of_dvd
  rw [hp]
  exact (pow_dvd_pow _ (Nat.succ_le_of_lt i.2.isLt)).trans
    (Finset.dvd_prod_of_mem (fun lam => (X - C lam) ^ m lam) i.1.property)

/-- Multiplicities in the split characteristic polynomial sum to its order. -/
theorem sum_root_multiplicities {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam) :
    ∑ lam ∈ s, m lam = r := by
  have hdeg : (characteristicPolynomial c).natDegree = r := by
    exact Polynomial.natDegree_eq_of_degree_eq_some (recurrence c).charPoly_degree_eq_order
  rw [hp, Polynomial.natDegree_prod_of_monic] at hdeg
  · simpa using hdeg
  · intro lam _
    exact (Polynomial.monic_X_sub_C lam).pow _

/-- The root sequences, regarded as elements of the solution space. -/
def rootSolutionFamily {r : ℕ} (c : Fin r → K) (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (i : Σ lam : s, Fin (m lam.val)) : solutionSpace c :=
  ⟨rootSequence i.1.val i.2.val, rootSequence_mem_solutionSpace c s m hp i⟩

/-- A basis of all solutions for a split characteristic polynomial.
No nonzero-root or characteristic-zero assumption is used. -/
def repeatedRootBasis {r : ℕ} (c : Fin r → K) (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam) :
    Module.Basis (Σ lam : s, Fin (m lam.val)) K (solutionSpace c) := by
  classical
  apply basisOfLinearIndependentOfCardEqFinrank' (rootSolutionFamily c s m hp)
  · exact (rootSequences_linearIndependent s m).of_comp (solutionSpace c).subtype
  · rw [solutionSpace_finrank, Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.univ_eq_attach, Finset.sum_attach] using
      sum_root_multiplicities c s m hp

@[simp] theorem repeatedRootBasis_apply {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (i : Σ lam : s, Fin (m lam.val)) :
    (repeatedRootBasis c s m hp i : ℕ → K) = rootSequence i.1.val i.2.val := by
  classical
  simp [repeatedRootBasis, rootSolutionFamily]

/-- The repeated-root family is a basis under precisely the split-root hypotheses
of p204:W16. Roots are indexed by a finite set, so they are distinct. -/
theorem exists_repeatedRootBasis {r : ℕ} (c : Fin r → K) (_hr : 1 ≤ r)
    (s : Finset K) (m : K → ℕ) (_hm : ∀ lam ∈ s, 0 < m lam)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam) :
    ∃ B : Module.Basis (Σ lam : s, Fin (m lam.val)) K (solutionSpace c),
      ∀ i, (B i : ℕ → K) = rootSequence i.1.val i.2.val :=
  ⟨repeatedRootBasis c s m hp, repeatedRootBasis_apply c s m hp⟩

/-- Every solution has one and only one expansion in the repeated-root family. -/
theorem existsUnique_root_expansion {r : ℕ} (c : Fin r → K) (_hr : 1 ≤ r)
    (s : Finset K) (m : K → ℕ) (_hm : ∀ lam ∈ s, 0 < m lam)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (a : ℕ → K) (ha : IsSolution c a) :
    ∃! d : (Σ lam : s, Fin (m lam.val)) → K,
      a = ∑ i, d i • rootSequence i.1.val i.2.val := by
  classical
  let B := repeatedRootBasis c s m hp
  let v : solutionSpace c := ⟨a, ha⟩
  have heq : a = ∑ i, B.repr v i • rootSequence i.1.val i.2.val := by
    have h := congrArg (fun w : solutionSpace c => (w : ℕ → K)) (B.sum_repr v)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, B, repeatedRootBasis_apply] using h.symm
  refine ⟨fun i => B.repr v i, heq, ?_⟩
  intro d hd
  funext i
  exact (rootSequences_linearIndependent s m).eq_coords_of_eq (hd.symm.trans heq) i

end FiniteCombinatorics.Recurrence
