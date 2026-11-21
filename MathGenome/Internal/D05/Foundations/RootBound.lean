import MathGenome.Internal.Specs.D05.Foundations.RootBound
import MathGenome.Internal.D05.Foundations.Division
import Mathlib.Algebra.Polynomial.Roots

/-!
The factor theorem and the distinct-root bound for formal polynomials.
Factoring at one root preserves every different root. Induction on a finite
set therefore extracts its full product of linear factors. Degree additivity
then bounds the cardinality; it requires no splitting of the polynomial.
-/

namespace D05.Foundations.RootBound

open Polynomial

/-- Evaluation at a scalar detects divisibility by its monic linear factor,
including when the polynomial is zero. -/
theorem factorTheorem : D05.Specs.RootBound.factorTheorem := by
  intro K _ p a
  exact Polynomial.dvd_iff_isRoot.symm

/-- A quotient at a root retains every other root and, for a nonzero dividend,
has degree exactly one less. -/
theorem divisionAtRoot : D05.Specs.RootBound.divisionAtRoot := by
  intro K _ p a ha
  obtain ⟨q, hq⟩ := (factorTheorem K p a).1 ha
  refine ⟨q, hq, ?_, ?_⟩
  · intro b hba
    simp [hq, sub_ne_zero.mpr hba]
  · intro hp
    have hq0 : q ≠ 0 := by
      intro hz
      exact hp (by simp [hq, hz])
    refine ⟨hq0, ?_⟩
    rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
      Polynomial.natDegree_X_sub_C, Nat.add_comm]

/-- Extract the linear factors at any finite set of distinct roots. -/
theorem factorizationAtDistinctRoots {K : Type*} [Field K]
    (s : Finset K) (p : Polynomial K) (h : ∀ a ∈ s, p.eval a = 0) :
    ∃ q : Polynomial K, p = (∏ a ∈ s, (X - C a)) * q := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact ⟨p, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨q, hpq, hother, _⟩ :=
        divisionAtRoot K p a (h a (Finset.mem_insert_self a s))
      have hq : ∀ b ∈ s, q.eval b = 0 := by
        intro b hb
        have hba : b ≠ a := by
          intro heq
          exact ha (heq ▸ hb)
        exact (hother b hba).2 (h b (Finset.mem_insert_of_mem hb))
      obtain ⟨r, hqr⟩ := ih q hq
      refine ⟨r, ?_⟩
      rw [hpq, hqr, Finset.prod_insert ha, mul_assoc]

/-- Repeated division, with the exact degree accounting when p is nonzero. -/
theorem repeatedDivision : D05.Specs.RootBound.repeatedDivision := by
  intro K _ p s h
  obtain ⟨q, hpq⟩ := factorizationAtDistinctRoots s p h
  refine ⟨q, hpq, ?_⟩
  intro hp
  have hq : q ≠ 0 := by
    intro hz
    exact hp (by simp [hpq, hz])
  refine ⟨hq, ?_⟩
  have hprod : (∏ a ∈ s, (X - C a : Polynomial K)) ≠ 0 :=
    (Polynomial.monic_prod_X_sub_C (fun a : K => a) s).ne_zero
  rw [hpq, Polynomial.natDegree_mul hprod hq,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

/-- The degree bound follows by counting the extracted linear factors. -/
theorem distinctRootBound : D05.Specs.RootBound.distinctRootBound := by
  intro K _ p hp s h
  obtain ⟨q, _, hdegree⟩ := repeatedDivision K p s h
  calc
    s.card ≤ s.card + q.natDegree := Nat.le_add_right _ _
    _ = p.natDegree := (hdegree hp).2

/-- All scalar roots form a finite set, bounded by the degree. -/
theorem rootSetBound : D05.Specs.RootBound.rootSetBound := by
  intro K _ p hp
  classical
  have hfinite : Set.Finite {a : K | p.eval a = 0} :=
    Polynomial.finite_setOfPred_isRoot hp
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply distinctRootBound K p hp
  intro a ha
  exact hfinite.mem_toFinset.mp ha

end D05.Foundations.RootBound
