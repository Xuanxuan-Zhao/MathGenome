import MathGenome.Internal.Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! The elementary-symmetric substitution respects and reflects the grading. -/

universe u
noncomputable section

namespace D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity

open MvPolynomial
open Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity

variable {R : Type u} [CommRing R] {n : ℕ}

theorem elementary_isHomogeneous (j : ℕ) :
    (esymm (Fin n) R j).IsHomogeneous j := by
  classical
  unfold esymm
  apply IsHomogeneous.sum
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, hcard] using
    IsHomogeneous.prod s (fun i : Fin n => (X i : MvPolynomial (Fin n) R))
      (fun _ => 1) (fun i _ => isHomogeneous_X R i)

theorem substituted_monomial_isHomogeneous (b : Fin n →₀ ℕ) (r : R) :
    (aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) (monomial b r)).IsHomogeneous
      (Finsupp.weight (fun i : Fin n => i.val + 1) b) := by
  classical
  rw [aeval_monomial, algebraMap_eq]
  apply IsHomogeneous.C_mul
  simpa only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul,
    Nat.mul_comm] using
    IsHomogeneous.prod b.support (fun i => esymm (Fin n) R (i.val + 1) ^ b i)
      (fun i => (i.val + 1) * b i)
      (fun i _ => (elementary_isHomogeneous (R := R) (n := n) (i.val + 1)).pow (b i))

theorem component_compatibility : ComponentCompatibility.{u} := by
  intro R _ n d G
  classical
  induction G using MvPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | monomial b r =>
    have hsource := isWeightedHomogeneous_monomial (fun i : Fin n => i.val + 1) b r rfl
    have htarget := substituted_monomial_isHomogeneous b r
    rw [weightedHomogeneousComponent_of_mem hsource, homogeneousComponent_of_mem htarget]
    split_ifs <;> simp

theorem homogeneity_equivalence : HomogeneityEquivalence.{u} := by
  intro R _ n d G
  have hinj : Function.Injective
      (aeval (R := R) (fun i : Fin n => esymm (Fin n) R (i.val + 1))) := by
    intro p q h
    apply esymmAlgHom_fin_injective R (le_refl n)
    apply Subtype.ext
    simpa only [esymmAlgHom_apply] using h
  constructor
  · intro h
    have heq : weightedHomogeneousComponent (fun i : Fin n => i.val + 1) d G = G := by
      apply hinj
      rw [component_compatibility R n d G, homogeneousComponent_eq_self h]
    rw [← heq]
    exact weightedHomogeneousComponent_isWeightedHomogeneous d G
  · intro h
    rw [← h.weightedHomogeneousComponent_same, component_compatibility R n d G]
    exact homogeneousComponent_isHomogeneous d _

theorem unique_weighted_expression : UniqueWeightedExpression.{u} := by
  intro R _ n d f hsym hhom
  obtain ⟨G, hG⟩ := (esymmAlgHom_fin_bijective R n).2 ⟨f, hsym⟩
  have heval : aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G = f := by
    simpa only [esymmAlgHom_apply] using congrArg Subtype.val hG
  refine ⟨G, heval, (homogeneity_equivalence R n d G).mp (heval.symm ▸ hhom), ?_⟩
  intro H hH
  apply esymmAlgHom_fin_injective R (le_refl n)
  apply Subtype.ext
  simpa only [esymmAlgHom_apply] using hH.trans heval.symm

end D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity
