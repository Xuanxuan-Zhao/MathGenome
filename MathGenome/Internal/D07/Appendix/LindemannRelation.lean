import MathGenome.Internal.Specs.D07.Appendix.LindemannRelation
import MathGenome.Internal.D07.Appendix.LindemannRelationIntegerScaling
import MathGenome.Internal.D07.Appendix.LindemannRelationFactorialIntegralityCongruence
import MathGenome.Internal.D07.Appendix.LindemannRelationExponentialIntegralIdentity
import MathGenome.Internal.D07.Appendix.LindemannRelationFactorialEstimate

/-!
The special Lindemann relation follows by comparing the arithmetic lower
bound for J_p with the integral upper bound, for one sufficiently large
prime avoiding k*a*Q(0). No transcendence theorem is used.
-/

noncomputable section
namespace D07.Appendix.LindemannRelation

open Polynomial
open Specs.D07.Appendix.LindemannRelationFactorialIntegralityCongruence
open Specs.D07.Appendix.LindemannRelationFactorialEstimate
  (sourcePolynomial auxiliaryPolynomial weightedIntegralSum)
open Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity (derivativeSum)

/-- The arithmetic and analytic prerequisites use the same normalized polynomial. -/
lemma sourcePolynomial_eq_f (a : ℤ) (Q : ℤ[X]) (p : ℕ) :
    sourcePolynomial a Q p = f a Q p := by
  simp only [sourcePolynomial, auxiliaryPolynomial, f, H, algebraMap_int_eq]

/-- Substitution by a linear polynomial and scalar normalization do not
increase the auxiliary polynomial's natural degree. -/
lemma normalized_degree_le (a : ℤ) (Q : ℤ[X]) (p : ℕ) :
    (f a Q p).natDegree ≤ (H Q p).natDegree := by
  unfold f
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  calc
    _ ≤ ((H Q p).map (Int.castRingHom ℂ)).natDegree * 1 :=
      Nat.mul_le_mul_left _ ((natDegree_C_mul_le _ _).trans (by simp))
    _ ≤ (H Q p).natDegree := by simpa using natDegree_map_le

/-- Assembly for already scaled integer root data. -/
theorem scaled_relation_nonzero (m : ℕ) (β : Fin m → ℂ) (k : ℕ)
    (a : ℤ) (Q : ℤ[X]) (hk : 0 < k) (ha : 0 < a)
    (hmonic : Q.Monic) (hQ0 : Q.coeff 0 ≠ 0)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j))) :
    (k : ℂ) + ∑ j, Complex.exp (β j) ≠ 0 := by
  intro hrel
  have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
  obtain ⟨p, _, hp, havoid, hsmall⟩ :=
    LindemannRelationFactorialEstimate.arbitrarily_large_small_integrals
      m β a (k : ℤ) Q ha hkZ hQ0 hQ 1 zero_lt_one 0
  obtain ⟨_, _, w, _, _, _, _, hlower⟩ :=
    LindemannRelationFactorialIntegralityCongruence.integrality_congruences
      m β (k : ℤ) a Q p hkZ ha hmonic hQ0 hp havoid hQ
  have hdeg : (f a Q p).natDegree ≤ N m p := by
    calc
      _ ≤ (H Q p).natDegree := normalized_degree_le a Q p
      _ = _ := LindemannRelationFactorialIntegralityCongruence.auxiliary_degree
        m β a Q hmonic p hp.pos hQ
  have hid := LindemannRelationExponentialIntegralIdentity.summed_exponential_integral_identity
    (f a Q p) (N m p) hdeg m β k hrel
  have heq : -J β (k : ℤ) a Q p = weightedIntegralSum β a Q p := by
    simpa only [J, F, derivativeSum, weightedIntegralSum, sourcePolynomial_eq_f,
      Int.cast_natCast] using hid
  have hnorm : ‖J β (k : ℤ) a Q p‖ =
      ‖weightedIntegralSum β a Q p‖ := by
    simpa only [norm_neg] using congrArg norm heq
  exact (not_lt_of_ge hlower) (hnorm ▸ hsmall)

theorem special_relation : Specs.D07.Appendix.LindemannRelation.SpecialRelation := by
  intro β P hβ hP k hk
  obtain ⟨a, Q, ha, hmonic, hQ0, _, _, hQ⟩ :=
    LindemannRelationIntegerScaling.integer_scaling β P hβ hP
  have hQfin :=
    LindemannRelationFactorialEstimate.scaled_root_list_factorization β a Q hQ
  have hne := scaled_relation_nonzero β.length (fun j => β[j.val])
    k a Q hk ha hmonic hQ0 hQfin
  simpa only [Fin.sum_univ_fun_getElem] using hne

theorem special_relation_fin : Specs.D07.Appendix.LindemannRelation.SpecialRelationFin := by
  intro m β P hβ hP k hk
  have hn : ∀ b ∈ List.ofFn β, b ≠ 0 := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hβ j
  have hp : P.map (algebraMap ℚ ℂ) =
      ((List.ofFn β).map (fun b => X - C b)).prod := by
    simpa only [List.map_ofFn, Fin.prod_ofFn, Function.comp_def] using hP
  simpa only [List.map_ofFn, Fin.sum_ofFn, Function.comp_def] using special_relation (List.ofFn β) P hn hp k hk

end D07.Appendix.LindemannRelation
