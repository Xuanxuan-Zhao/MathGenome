import MathGenome.Internal.Specs.D07.Ch19.SymmetricPolynomialTheorem
import MathGenome.Internal.D07.Ch19.SymmetricFunctions
import MathGenome.Internal.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! The fundamental symmetric-polynomial theorem over every commutative ring. -/

universe u
noncomputable section

namespace D07.Ch19.SymmetricPolynomialTheorem

open MvPolynomial
open Specs.D07.Ch19.SymmetricPolynomialTheorem

/-- Injectivity and surjectivity of the canonical elementary-symmetric algebra
homomorphism give uniqueness and existence, respectively. Its underlying map
is exactly the required formal substitution. -/
theorem unique_expression : UniqueExpression.{u} := by
  intro R _ n f hsym
  obtain ⟨G, hG⟩ := (esymmAlgHom_fin_bijective R n).2 ⟨f, hsym⟩
  have heval : aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G = f := by
    simpa only [esymmAlgHom_apply] using congrArg Subtype.val hG
  refine ⟨G, heval, ?_⟩
  intro H hH
  apply esymmAlgHom_fin_injective R (le_refl n)
  apply Subtype.ext
  simpa only [esymmAlgHom_apply] using hH.trans heval.symm

theorem substitution_isomorphism : SubstitutionIsomorphism.{u} := by
  intro R _ n
  refine ⟨esymmAlgEquiv (Fin n) R (Fintype.card_fin n), ?_⟩
  intro G
  exact esymmAlgHom_apply G

theorem component_compatibility : ComponentCompatibility.{u} :=
  D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.component_compatibility

theorem homogeneity_equivalence : HomogeneityEquivalence.{u} :=
  D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.homogeneity_equivalence

theorem unique_weighted_expression : UniqueWeightedExpression.{u} :=
  D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.unique_weighted_expression

end D07.Ch19.SymmetricPolynomialTheorem
