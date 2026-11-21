import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBasicity
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Coefficient model and assertion 2 of `fa2:p1:dual-bases`.
The ambient space is Banach, as stipulated at the start of Chapter 15.
All series are ordered norm-convergent series; all duals are continuous
scalar-linear duals. Indices are zero based, with `range N` the first N terms.
The dual basis is the one with evaluation coordinates, rather than an
arbitrary basis of its underlying space. -/
open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisCoefficients.Spec
open ExpandedFA.P1.DualBasisBasicity.Spec
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance : NormedAddCommGroup (E →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (E →L[𝕜] 𝕜) := inferInstance

/-- Restriction of canonical evaluation to the coordinate closed span F. -/
def evaluation (b : SchauderBasis 𝕜 E) : E →L[𝕜] (dualSpan b →L[𝕜] 𝕜) :=
  (dualSpan b).subtypeL.flip

/-- The coefficient sequence of an element of F'. -/
def coefficients (b : SchauderBasis 𝕜 E) (Φ : dualSpan b →L[𝕜] 𝕜) : ℕ → 𝕜 :=
  fun i => Φ (dualVector b i)

def CoefficientRepresentation : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E) (a : ℕ → 𝕜),
    (∃! Φ : dualSpan b →L[𝕜] 𝕜, coefficients b Φ = a) ↔
      BddAbove (Set.range (fun N =>
        ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a N‖))

def EvaluationImage : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E) (Φ : dualSpan b →L[𝕜] 𝕜),
    (∃ x : E, evaluation b x = Φ) ↔
      ∃ x : E, Tendsto
        (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis (coefficients b Φ))
        atTop (𝓝 x)

def EvaluationClosedSpan : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E) (d : SchauderBasis 𝕜 (dualSpan b)),
    d.basis = dualVector b → (∀ i f, d.coord i f = f.val (b i)) →
      (evaluation b).range = (Submodule.span 𝕜 (Set.range d.coord)).topologicalClosure

def ShrinkingBoundedlyComplete : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E) (d : SchauderBasis 𝕜 (dualSpan b)),
    d.basis = dualVector b → (∀ i f, d.coord i f = f.val (b i)) →
      (IsShrinking d ↔ IsBoundedlyComplete (𝕜 := 𝕜) b.basis)

/-- The dual basis exists with the prescribed vectors and coordinates, and
satisfies assertion 2. This packages the criterion without conditional
existence of a dual Schauder basis. -/
def DualShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    ∃ d : SchauderBasis 𝕜 (dualSpan b), d.basis = dualVector b ∧
      (∀ i f, d.coord i f = f.val (b i)) ∧
      (IsShrinking d ↔ IsBoundedlyComplete (𝕜 := 𝕜) b.basis)

/-- Apply the criterion to the manuscript's original basis definition,
which assumes unique ordered expansions but does not assume continuous
coordinate maps. The continuous realization is part of the conclusion. -/
def RawDualShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = ExpandedFA.P1.C15Basis.Spec.rawCoordinates h x i) ∧
      ∃ d : SchauderBasis 𝕜 (dualSpan b), d.basis = dualVector b ∧
        (∀ i f, d.coord i f = f.val (b i)) ∧
        (IsShrinking d ↔ IsBoundedlyComplete (𝕜 := 𝕜) e)

/-- Finite lists, including the empty basis of the zero space. Every finite
coefficient family is represented uniquely; every element of F' is evaluation
at its primal synthesis. Dual coordinate expansions are exact, and primal
coefficient sums are bounded and converge, giving the finite shrinking and
bounded-completeness cases. -/
def FiniteCoefficientModel : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {n : ℕ} (b : UnconditionalSchauderBasis (Fin n) 𝕜 E),
    let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
    let e' : Fin n → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self i))⟩
    let ev : E →L[𝕜] (F →L[𝕜] 𝕜) := F.subtypeL.flip
    (∀ a : Fin n → 𝕜, ∃! Φ : F →L[𝕜] 𝕜, ∀ i, Φ (e' i) = a i) ∧
    (∀ Φ : F →L[𝕜] 𝕜, ev (∑ i, Φ (e' i) • b i) = Φ) ∧
    (∀ Φ : F →L[𝕜] 𝕜, ∑ i, Φ (e' i) • ev (b i) = Φ) ∧
    (∀ a : Fin n → 𝕜,
      BddAbove (Set.range fun N =>
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), a i • b i‖) ∧
      Tendsto (fun N => ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N),
        a i • b i) atTop (𝓝 (∑ i, a i • b i)))
end ExpandedFA.P1.DualBasisCoefficients.Spec
