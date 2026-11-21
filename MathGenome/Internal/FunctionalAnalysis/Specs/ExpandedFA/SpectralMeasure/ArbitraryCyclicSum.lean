import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.CyclicModel
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Independent statements for paper.tex 12463–12493. The direct sum and the
sum measure have arbitrary index sets. In particular no sigma-finiteness,
separability, positive mass, or common scalar control measure is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.SpectralMeasure.ArbitraryCyclicSum.Spec
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The linear orbit under the original generated C*-algebra. -/
def algebraOrbit (N : H →L[ℂ] H) (e : H) : StarAlgebra.elemental ℂ N →ₗ[ℂ] H where
  toFun a := (a : H →L[ℂ] H) e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The closed cyclic subspace, using the ambient operator algebra. -/
def cyclicSpace (N : H →L[ℂ] H) (e : H) : Submodule ℂ H :=
  (LinearMap.range (algebraOrbit N e)).topologicalClosure

/-- Reuse the shared reduction predicate: both orthogonal summands are invariant. -/
abbrev IsReducing (N : H →L[ℂ] H) (V : Submodule ℂ H) : Prop :=
  Hilbert.Adjoint.Spec.ReducingSubspaceValue ℂ H V N

/-- An arbitrary orthogonal family of nonzero cyclic reducing spaces whose
closed span is all of H, together with the actual Hilbert direct-sum unitary.
An empty family is permitted and covers the zero Hilbert space. -/
def Decomposition (N : H →L[ℂ] H) : Prop :=
  ∃ s : Set H,
    (∀ e ∈ s, e ≠ 0) ∧
    s.Pairwise (fun e f => cyclicSpace N e ⟂ cyclicSpace N f) ∧
    (∀ e ∈ s, IsReducing N (cyclicSpace N e)) ∧
    (⨆ e : s, cyclicSpace N (e : H)).topologicalClosure = ⊤ ∧
    ∃ U : lp (fun e : s => cyclicSpace N (e : H)) 2 ≃ₗᵢ[ℂ] H,
      ∀ f, U f = ∑' e : s, ((f e : cyclicSpace N (e : H)) : H)

/-- Sum measure on the measurable disjoint union. For a measurable set B
its value is the ENNReal sum (supremum of finite subsums) of component masses. -/
def disjointMeasure {I : Type v} {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) : Measure (Sigma S) :=
  Measure.sum (fun i => (μ i).map (Sigma.mk i))

/-- An actual multiplication representation, with a bounded measurable
symbol and almost-everywhere pointwise multiplication on native L².
The component spaces can be taken to be copies of compact complex spectra,
so it suffices to quantify over small component carriers. -/
def MultiplicationModel (N : H →L[ℂ] H) : Prop :=
  ∃ (I : Type u) (S : I → Type) (m : ∀ i, MeasurableSpace (S i))
    (μ : ∀ i, @Measure (S i) (m i)),
    letI := m
    (∀ i, IsFiniteMeasure (μ i)) ∧
    ∃ (g : Sigma S → ℂ), Measurable g ∧ (∀ x, ‖g x‖ ≤ ‖N‖) ∧
    ∃ (M : Lp ℂ 2 (disjointMeasure μ) →L[ℂ] Lp ℂ 2 (disjointMeasure μ))
      (U : Lp ℂ 2 (disjointMeasure μ) ≃ₗᵢ[ℂ] H),
      (∀ f, M f =ᵐ[disjointMeasure μ] fun x => g x * f x) ∧
      (∀ f, U (M f) = N (U f))

def OrthogonalDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N → Decomposition N

def MultiplicationTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N → MultiplicationModel N

/-- The complete assigned statement, including the already proved cyclic
stage with e corresponding to 1, and both arbitrary-H conclusions. -/
def FullTheorem : Prop :=
  CyclicModel.Spec.CyclicModelTheorem.{u} ∧
  OrthogonalDecomposition.{u} ∧ MultiplicationTheorem.{u}
end ExpandedFA.SpectralMeasure.ArbitraryCyclicSum.Spec
