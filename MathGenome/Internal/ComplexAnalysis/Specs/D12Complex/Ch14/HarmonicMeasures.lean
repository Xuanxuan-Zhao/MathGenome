import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.RegularDirichlet
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.MeanValueStrongPrinciple
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Harmonic measures, paper.tex:2693–2698. A finite nonempty compact partition
of the boundary suffices; in particular the parts may be its connected components.
All uniqueness and sum identities concern the closure, since total representatives
have unconstrained values outside it. -/
noncomputable section
open Set
open scoped BigOperators

namespace Specs.D12Complex.Ch14.HarmonicMeasures
open _root_.D12Complex

/-- Nonempty, pairwise disjoint compact sets whose union is the boundary.
This slightly more general hypothesis includes precisely the boundary-component
families in the source, without imposing any extra boundary smoothness. -/
def IsCompactBoundaryPartition_type := {ι : Type} → Set ℂ → (ι → Set ℂ) → Prop
def IsCompactBoundaryPartition_value : IsCompactBoundaryPartition_type := fun Ω C =>
  (∀ j, IsCompact (C j)) ∧ (∀ j, (C j).Nonempty) ∧
    Pairwise (fun j k => Disjoint (C j) (C k)) ∧ (⋃ j, C j) = frontier Ω

def componentBoundaryData_type := {ι : Type} → (ι → Set ℂ) → ι → ℂ → ℝ
def componentBoundaryData_value : componentBoundaryData_type := fun C j z =>
  @ite ℝ (z ∈ C j) (Classical.propDecidable _) 1 0

def harmonicMeasure_type := {ι : Type} → Set ℂ → (ι → Set ℂ) → ι → ℂ → ℝ
def harmonicMeasure_value : harmonicMeasure_type := fun Ω C j =>
  RegularDirichlet.perronSolution_value Ω (componentBoundaryData_value C j)

def boundaryData_continuous_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsCompactBoundaryPartition_value Ω C → ∀ j,
    ContinuousOn (componentBoundaryData_value C j) (frontier Ω)

def harmonicMeasure_solution_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → ∀ j,
    RegularDirichlet.IsDirichletSolution_value Ω (componentBoundaryData_value C j)
      (harmonicMeasure_value Ω C j) ∧
    (∀ u, RegularDirichlet.IsDirichletSolution_value Ω (componentBoundaryData_value C j) u →
      EqOn u (harmonicMeasure_value Ω C j) (closure Ω))

def harmonicMeasure_boundary_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → ∀ j k (ξ : ℂ), ξ ∈ C k →
      harmonicMeasure_value Ω C j ξ = @ite ℝ (j = k) (Classical.propDecidable _) 1 0

def harmonicMeasure_bounds_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → ∀ j z, z ∈ closure Ω →
      0 ≤ harmonicMeasure_value Ω C j z ∧ harmonicMeasure_value Ω C j z ≤ 1

def harmonicMeasure_sum_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → ∀ z ∈ closure Ω,
      ∑ j, harmonicMeasure_value Ω C j z = 1

/-- The finite linear combination is the unique solution with arbitrary real
component values. This includes existence for those data and identifies the
Perron solution on the whole closure. -/
def harmonicMeasure_componentSolution_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → ∀ c : ι → ℝ,
      HarmonicOn Ω (fun z => ∑ j, c j * harmonicMeasure_value Ω C j z) ∧
      ContinuousOn (fun z => ∑ j, c j * harmonicMeasure_value Ω C j z) (closure Ω) ∧
      (∀ k ξ, ξ ∈ C k → (∑ j, c j * harmonicMeasure_value Ω C j ξ) = c k) ∧
      (∀ u, HarmonicOn Ω u → ContinuousOn u (closure Ω) →
        (∀ k ξ, ξ ∈ C k → u ξ = c k) →
        EqOn u (fun z => ∑ j, c j * harmonicMeasure_value Ω C j z) (closure Ω)) ∧
      EqOn (RegularDirichlet.perronSolution_value Ω
        (fun z => ∑ j, c j * componentBoundaryData_value C j z))
        (fun z => ∑ j, c j * harmonicMeasure_value Ω C j z) (closure Ω)

def harmonicMeasure_strict_type : Prop :=
  ∀ {ι : Type} [Fintype ι] (Ω : Set ℂ) (C : ι → Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsCompactBoundaryPartition_value Ω C → 1 < Fintype.card ι →
    ∀ j z, z ∈ Ω → 0 < harmonicMeasure_value Ω C j z ∧ harmonicMeasure_value Ω C j z < 1

end Specs.D12Complex.Ch14.HarmonicMeasures
