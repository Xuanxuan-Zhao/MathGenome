import MathGenome.Internal.Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Finiteness.Basic

/-!
The determinant trick for a stable finite submodule (paper.tex:7185–7227).
The finite-module Cayley–Hamilton theorem applies to restricted
multiplication without requiring a basis. Multiplying its annihilator by
X ensures a positive displayed exponent, including for the zero module.
-/

universe u v

namespace D07.Ch22.DeterminantTrickStableFiniteSubmodule

open Polynomial
open scoped BigOperators

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- Stability under x extends to stability under the whole subalgebra R[x].
Thus multiplication really defines the action used in the faithfulness
hypothesis of the specification. -/
theorem adjoin_mul_mem (x : B) (M : Submodule R B)
    (hx : ∀ m ∈ M, x * m ∈ M) {y : B}
    (hy : y ∈ Algebra.adjoin R ({x} : Set B)) :
    ∀ m ∈ M, y * m ∈ M := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hx
  | algebraMap r =>
    intro m hm
    simpa only [← Algebra.smul_def] using M.smul_mem r hm
  | add y z _ _ hy hz =>
    intro m hm
    simpa only [add_mul] using M.add_mem (hy m hm) (hz m hm)
  | mul y z _ _ hy hz =>
    intro m hm
    simpa only [mul_assoc] using hy (z * m) (hz m hm)

/-- Evaluation at restricted multiplication is ambient multiplication by
the evaluated polynomial. -/
theorem coe_aeval_mul (x : B) (M : Submodule R B) (f : Module.End R M)
    (hf : ∀ m : M, (f m : B) = x * (m : B)) (p : R[X]) (m : M) :
    ((aeval f p) m : B) = aeval x p * (m : B) := by
  have hpow (n : ℕ) (m : M) : ((f ^ n) m : B) = x ^ n * (m : B) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, hf, ih, pow_succ', mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, add_mul]
  | monomial n r =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow,
      Algebra.smul_def, mul_assoc]

/-- The basic monic annihilator, before choosing a positive displayed
exponent. It also applies when the module or coefficient ring is zero. -/
theorem exists_monic_annihilator (x : B) (M : Submodule R B)
    (hM : M.FG) (hx : ∀ m ∈ M, x * m ∈ M) :
    ∃ p : R[X], p.Monic ∧ ∀ m ∈ M, aeval x p * m = 0 := by
  have : Module.Finite R M := Module.Finite.of_fg hM
  let f : Module.End R M := (LinearMap.mulLeft R x).restrict hx
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  refine ⟨p, hp, ?_⟩
  intro m hm
  have he := coe_aeval_mul x M f (fun _ => rfl) p ⟨m, hm⟩
  simpa only [hpf, LinearMap.zero_apply, Submodule.coe_zero] using he.symm

/-- Multiplication by X gives an annihilator whose displayed leading
exponent is strictly positive, without a nontriviality assumption on R. -/
theorem exists_positive_monic_annihilator (x : B) (M : Submodule R B)
    (hM : M.FG) (hx : ∀ m ∈ M, x * m ∈ M) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → R,
      let p : R[X] := X ^ n + ∑ i ∈ Finset.range n, C (a i) * X ^ i
      p.Monic ∧ ∀ m ∈ M, aeval x p * m = 0 := by
  obtain ⟨p, hp, hann⟩ := exists_monic_annihilator x M hM hx
  let q : R[X] := X * p
  have hq : q.Monic := monic_X.mul hp
  have hqann : ∀ m ∈ M, aeval x q * m = 0 := by
    intro m hm
    simp only [q, map_mul, aeval_X, mul_assoc, hann m hm, mul_zero]
  cases subsingleton_or_nontrivial R with
  | inl hR =>
    have := hR
    have hB : Subsingleton B := by
      apply subsingleton_of_zero_eq_one
      have h := congrArg (algebraMap R B) (Subsingleton.elim (0 : R) 1)
      simpa only [map_zero, map_one] using h
    have := hB
    exact ⟨1, Nat.zero_lt_one, fun _ => 0, Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩
  | inr hR =>
    have := hR
    have hdeg : q.natDegree = p.natDegree + 1 :=
      Polynomial.natDegree_X_mul hp.ne_zero
    refine ⟨q.natDegree, by omega, q.coeff, ?_⟩
    rw [← hq.as_sum]
    exact ⟨hq, hqann⟩

theorem stableFiniteSubmodule :
    Specs.D07.Ch22.DeterminantTrickStableFiniteSubmodule.StableFiniteSubmodule.{u, v} := by
  intro R B _ _ _ x M hM hx
  obtain ⟨n, hn, a, hp, hann⟩ := exists_positive_monic_annihilator x M hM hx
  let p : R[X] := X ^ n + ∑ i ∈ Finset.range n, C (a i) * X ^ i
  refine ⟨n, hn, a, hp, hann, ?_, ?_⟩
  · intro h1
    have heq : aeval x p = 0 := by simpa only [mul_one] using hann 1 h1
    exact ⟨heq, ⟨p, hp, heq⟩⟩
  · intro hfaith
    let x' : Algebra.adjoin R ({x} : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
    have heq' : aeval x' p = 0 := by
      apply hfaith (aeval x' p) 0
      intro m hm
      simpa only [aeval_subalgebra_coe, x', Subalgebra.coe_zero, zero_mul] using hann m hm
    have heq : aeval x p = 0 := by
      have h := congrArg (fun y : Algebra.adjoin R ({x} : Set B) => (y : B)) heq'
      simpa only [aeval_subalgebra_coe, x', Subalgebra.coe_zero] using h
    exact ⟨heq, ⟨p, hp, heq⟩⟩

end D07.Ch22.DeterminantTrickStableFiniteSubmodule
