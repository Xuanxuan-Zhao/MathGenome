import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statement of paper.tex, Lemma `lem:polyhedral-support`.
The ambient space has its original Hausdorff real vector topology.
The finite index types may be empty. `WithTop ℝ` excludes minus infinity;
`toEReal` is used only to express the possibly unbounded primal infimum.
The maximum clauses include boundedness, attainment and its exact value.
-/
noncomputable section
open Set
universe u v w
namespace VariationalNotes.Ch04.Specs
open ConvexAnalysis.Specs

def polyhedral_support : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (f : E → WithTop ℝ) (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ₗ[ℝ] ℝ) (d : J → ℝ),
    Proper f → IsConvex f →
    let P : Set E := {x | (∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)}
    (ConvexGeometry.Specs.relativeInterior (effectiveDomain f) ∩ P).Nonempty →
    ∀ p : ℝ, (⨅ x : P, toEReal (f x.val)) = (p : EReal) →
    ∃ (lam : I → ℝ) (nu : J → ℝ), (∀ i, 0 ≤ lam i) ∧
      let n : E →ₗ[ℝ] ℝ := (∑ i, lam i • a i) + ∑ j, nu j • e j
      let M : ℝ := (∑ i, lam i * b i) + ∑ j, nu j * d j
      (∀ x ∈ effectiveDomain f,
        p ≤ (f x).untopD 0 + (∑ i, lam i * (a i x - b i)) +
          ∑ j, nu j * (e j x - d j)) ∧
      (∃ z ∈ P, n z = M ∧ ∀ x ∈ P, n x ≤ M) ∧
      BddAbove (n '' P) ∧ sSup (n '' P) = M ∧
      (∀ x ∈ effectiveDomain f, p ≤ (f x).untopD 0 + n x - sSup (n '' P))

end VariationalNotes.Ch04.Specs
