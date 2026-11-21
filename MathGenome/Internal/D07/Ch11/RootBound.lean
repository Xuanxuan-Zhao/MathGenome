import MathGenome.Internal.Specs.D07.Ch11.RootBound
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import MathGenome.Internal.D07.Ch11.FactorRemainder

/-!
K07.11.root_bound. The canonical root multiset counts maximal powers of
monic linear factors, and its cardinality is bounded by the degree over
any commutative domain. Passing to its underlying set gives both finiteness
and the distinct-root bound. Summing the counts gives the multiplicity
bound without a splitting assumption. Zero is handled separately.
-/

universe u

namespace D07.Ch11.RootBound

open Polynomial
open Specs.D07.Ch11.RootBound

theorem roots_finite : RootsFinite.{u} := by
  intro R _ _ f hf
  exact Polynomial.finite_setOfPred_isRoot hf

theorem distinct_root_bound : DistinctRootBound.{u} := by
  intro R _ _ f n hf hn
  classical
  have hset : {a : R | f.eval a = 0} = (f.roots.toFinset : Set R) := by
    ext a
    exact (Multiset.mem_toFinset.trans (Polynomial.mem_roots hf)).symm
  refine ⟨roots_finite R f hf, ?_⟩
  rw [hset, Set.ncard_coe_finset]
  have hcard : (f.roots.card : WithBot ℕ) ≤ (n : WithBot ℕ) := by
    simpa only [hn] using (Polynomial.card_roots hf)
  exact (Multiset.toFinset_card_le _).trans (WithBot.coe_le_coe.mp hcard)

theorem root_multiset_correct : RootMultisetCorrect.{u} := by
  intro R _ _ f hf a
  classical
  exact ⟨Polynomial.mem_roots hf, Polynomial.count_roots f⟩

theorem multiplicity_characterization : MultiplicityCharacterization.{u} := by
  intro R _ _ f hf a k
  exact (Polynomial.le_rootMultiplicity_iff hf).symm

theorem multiplicity_sum_bound : MultiplicitySumBound.{u} := by
  intro R _ _ f n hf hn s hs
  classical
  have hset : s = f.roots.toFinset := by
    ext a
    exact (hs a).trans (Multiset.mem_toFinset.trans (Polynomial.mem_roots hf)).symm
  rw [hset]
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq]
  have hcard : (f.roots.card : WithBot ℕ) ≤ (n : WithBot ℕ) := by
    simpa only [hn] using (Polynomial.card_roots hf)
  exact WithBot.coe_le_coe.mp hcard

theorem zero_polynomial_exception : ZeroPolynomialException.{u} := by
  intro R _ _ a
  refine ⟨Polynomial.eval_zero, fun _ => dvd_zero _, ?_⟩
  rintro ⟨m, hm⟩
  exact (Nat.not_succ_le_self m) ((hm (m + 1)).mp (dvd_zero _))

end D07.Ch11.RootBound
