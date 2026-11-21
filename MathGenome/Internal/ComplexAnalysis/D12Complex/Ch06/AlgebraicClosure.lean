import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.AlgebraicClosure
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.Liouville
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.PolynomialMultiplicity
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Algebra.Polynomial

/-! Liouville and algebraic closure (paper.tex:1455–1473).

Root existence is proved using the project's disk-estimate Liouville
result. Polynomial growth and compactness give a global minimum of its
modulus. If this minimum were positive, the reciprocal would be a bounded
entire function. Degree induction then splits off successive linear factors.
No complex algebraic-closure instance or library FTA is used in this proof.
-/
noncomputable section
open Polynomial

namespace D12Complex.AlgebraicClosure

/-- Reuse the preliminary disk-estimate theorem with its exact hypotheses. -/
theorem bounded_entire_constant :
    Specs.D12Complex.Ch06.AlgebraicClosure.bounded_entire_constant_type :=
  Liouville.bounded_entire_constant

/-- The minimum modulus supplies a uniform bound for a root-free reciprocal. -/
theorem polynomial_exists_root_of_natDegree_pos (P : Polynomial ℂ)
    (hP : 0 < P.natDegree) : ∃ a : ℂ, P.eval a = 0 := by
  by_contra! hroot
  obtain ⟨b, hb⟩ := P.exists_forall_norm_le
  have hbpos : 0 < ‖P.eval b‖ := norm_pos_iff.mpr (hroot b)
  have hf : HolomorphicOn Set.univ (fun z => (P.eval z)⁻¹) :=
    ⟨isOpen_univ, fun z _ => P.differentiableAt.inv (hroot z)⟩
  have hbound : ∀ z : ℂ, ‖(P.eval z)⁻¹‖ ≤ ‖P.eval b‖⁻¹ := by
    intro z
    rw [norm_inv]
    exact inv_anti₀ hbpos (hb z)
  obtain ⟨c, hc⟩ := bounded_entire_constant (fun z => (P.eval z)⁻¹)
    (‖P.eval b‖⁻¹) hf (inv_nonneg.mpr (norm_nonneg _)) hbound
  have hconst : P = C (P.eval b) := by
    apply Polynomial.funext
    intro z
    simp only [eval_C]
    exact inv_injective ((hc z).trans (hc b).symm)
  have hdeg := congrArg Polynomial.natDegree hconst
  simp only [natDegree_C] at hdeg
  omega

/-- The statement for every polynomial which is not a constant. -/
theorem polynomial_exists_root :
    Specs.D12Complex.Ch06.AlgebraicClosure.polynomial_exists_root_type := by
  intro P hP
  apply polynomial_exists_root_of_natDegree_pos P
  by_contra h
  have hdeg : P.natDegree = 0 := Nat.eq_zero_of_not_pos h
  exact hP ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩

/-- Split off one root and repeat at the strictly smaller degree. -/
theorem polynomial_splits (P : Polynomial ℂ) : P.Splits := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hzero : P.natDegree = 0
    · exact Splits.of_natDegree_eq_zero hzero
    have hpos : 0 < P.natDegree := Nat.pos_of_ne_zero hzero
    obtain ⟨a, ha⟩ := polynomial_exists_root_of_natDegree_pos P hpos
    have hdeg : (P /ₘ (X - C a)).natDegree < n := by
      rw [natDegree_divByMonic P (monic_X_sub_C a), natDegree_X_sub_C, ← hn]
      omega
    have hsplit := ih _ hdeg (P /ₘ (X - C a)) rfl
    rw [← mul_divByMonic_eq_iff_isRoot.mpr ha]
    exact (Splits.X_sub_C a).mul hsplit

/-- All linear factors, including their algebraic and analytic multiplicities. -/
theorem polynomial_factorization :
    Specs.D12Complex.Ch06.AlgebraicClosure.polynomial_factorization_type := by
  intro P n hn hpos
  classical
  have hP : P ≠ 0 := by
    intro hzero
    simp [hzero] at hn
    omega
  have hs := polynomial_splits P
  refine ⟨P.roots, hs.natDegree_eq_card_roots.symm.trans hn, ?_,
    hs.eq_prod_roots, hs.eval_eq_prod_roots, ?_⟩
  · intro a ha
    exact (mem_roots hP).mp ha
  · intro a
    refine ⟨count_roots P, ?_⟩
    change LocalZeroFactorization.order (fun z => P.eval z) a = _
    rw [PolynomialMultiplicity.polynomial_order_eq_rootMultiplicity P hP a,
      count_roots]

end D12Complex.AlgebraicClosure
