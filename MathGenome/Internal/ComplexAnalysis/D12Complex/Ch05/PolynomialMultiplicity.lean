import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.PolynomialMultiplicity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Polynomial and analytic multiplicities (paper.tex:1403–1417).

Monic division by X - C a gives the maximal power and its remaining
polynomial, which is nonzero at a. Evaluating this algebraic identity
produces a local holomorphic factorization. Uniqueness of local order
identifies its exponent with analytic multiplicity. Only division by
this one specified linear factor is used; the polynomial need not split.
-/
noncomputable section
open Polynomial Filter
open scoped Topology

namespace D12Complex.PolynomialMultiplicity
open LocalZeroFactorization

theorem polynomial_holomorphic (P : Polynomial ℂ) :
    HolomorphicOn Set.univ (fun z => P.eval z) := by
  exact ⟨isOpen_univ, fun _ _ => P.differentiableAt⟩

private lemma polynomial_holomorphicNear (P : Polynomial ℂ) (a : ℂ) :
    HolomorphicNear (fun z => P.eval z) a :=
  ⟨Set.univ, Set.mem_univ a, polynomial_holomorphic P⟩

/-- The linear-division process cannot continue beyond the degree.
Mathlib's rootMultiplicity is defined by the first nondividing next
power, rather than by a list of all complex roots. -/
theorem polynomial_linear_factorization (P : Polynomial ℂ) (hP : P ≠ 0) (a : ℂ) :
    P.rootMultiplicity a ≤ P.natDegree ∧
      ∃ Q : Polynomial ℂ,
        P = (X - C a) ^ P.rootMultiplicity a * Q ∧ Q.eval a ≠ 0 := by
  constructor
  · have h := ((monic_X_sub_C a).pow (P.rootMultiplicity a)).natDegree_le_of_dvd
      hP (P.pow_rootMultiplicity_dvd a)
    simpa only [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] using h
  · refine ⟨P /ₘ (X - C a) ^ P.rootMultiplicity a,
      (P.pow_mul_divByMonic_rootMultiplicity_eq a).symm, ?_⟩
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hP

theorem polynomial_hasFiniteOrder (P : Polynomial ℂ) (hP : P ≠ 0) (a : ℂ) :
    HasFiniteOrder (fun z => P.eval z) a (P.rootMultiplicity a) := by
  obtain ⟨_, Q, hQ, hQa⟩ := polynomial_linear_factorization P hP a
  refine ⟨(fun z => Q.eval z), polynomial_holomorphicNear Q a, hQa, ?_⟩
  apply Filter.Eventually.of_forall
  intro z
  simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] using
    congrArg (fun R : Polynomial ℂ => R.eval z) hQ

theorem polynomial_order_eq_rootMultiplicity (P : Polynomial ℂ) (hP : P ≠ 0) (a : ℂ) :
    order (fun z => P.eval z) a = (P.rootMultiplicity a : ℕ∞) := by
  exact (order_eq_nat_iff _ a (polynomial_holomorphicNear P a) _).mpr
    (polynomial_hasFiniteOrder P hP a)

theorem polynomial_hasFiniteOrder_iff (P : Polynomial ℂ) (hP : P ≠ 0)
    (a : ℂ) (m : ℕ) :
    HasFiniteOrder (fun z => P.eval z) a m ↔ m = P.rootMultiplicity a := by
  rw [← order_eq_nat_iff _ a (polynomial_holomorphicNear P a) m,
    polynomial_order_eq_rootMultiplicity P hP a]
  exact ⟨fun h => (WithTop.coe_inj.mp h).symm, fun h => by rw [h]⟩

theorem polynomial_multiplicity (P : Polynomial ℂ) (hP : P ≠ 0)
    (a : ℂ) (ha : P.eval a = 0) :
    ∃ m : ℕ, 0 < m ∧
      HasFiniteOrder (fun z => P.eval z) a m ∧
      order (fun z => P.eval z) a = (m : ℕ∞) ∧
      IsGreatest {n : ℕ | (X - C a) ^ n ∣ P} m ∧ m ≤ P.natDegree := by
  refine ⟨P.rootMultiplicity a, (rootMultiplicity_pos hP).mpr ha,
    polynomial_hasFiniteOrder P hP a, polynomial_order_eq_rootMultiplicity P hP a,
    ?_, (polynomial_linear_factorization P hP a).1⟩
  exact ⟨P.pow_rootMultiplicity_dvd a, fun _ hn => (le_rootMultiplicity_iff hP).mpr hn⟩

end D12Complex.PolynomialMultiplicity
