import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Independent statements for the basicity/definitions portion of
`fa2:p1:dual-bases`, paper.tex 4278–4302. Indices are zero based: the tail
following the first N vectors is {b j | N ≤ j}. All duals are scalar-linear
continuous duals with their operator norms. Native ordered Schauder bases
are available for every raw Banach-space basis by the accepted coordinate
continuity theorem; no unconditional convergence is imposed. -/

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisBasicity.Spec
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The norm-closed linear span of the coordinate functionals inside E'. -/
def dualSpan (b : SchauderBasis 𝕜 E) : Submodule 𝕜 (E →L[𝕜] 𝕜) :=
  (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure

/-- The coordinate functionals, viewed as vectors in their own closed span. -/
def dualVector (b : SchauderBasis 𝕜 E) (i : ℕ) : dualSpan b :=
  ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i))⟩

def tailSpace (b : SchauderBasis 𝕜 E) (N : ℕ) : Submodule 𝕜 E :=
  (Submodule.span 𝕜 (b '' {j | N ≤ j})).topologicalClosure

/-- Shrinking means norm convergence of every dual coordinate expansion. -/
def IsShrinking (b : SchauderBasis 𝕜 E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, Tendsto (fun N => f.comp (b.proj N)) atTop (𝓝 f)

/-- Ordered coefficient series with bounded initial sums must converge.
This predicate applies to the primal or dual basic sequence alike. -/
def IsBoundedlyComplete (e : ℕ → E) : Prop :=
  ∀ a : ℕ → 𝕜,
    BddAbove (Set.range (fun N => ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a N‖)) →
    ∃ x : E, Tendsto (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a) atTop (𝓝 x)

def DualBasicity : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (dualVector b)

def DualBasisConstruction : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    ∃ d : SchauderBasis 𝕜 (dualSpan b), d.basis = dualVector b ∧
      ∀ i f, d.coord i f = f.val (b i)

def ShrinkingCharacterization : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    (IsShrinking b ↔ dualSpan b = ⊤) ∧
    (IsShrinking b ↔ ∀ f : E →L[𝕜] 𝕜,
      Tendsto (fun N => ‖f.comp (tailSpace b N).subtypeL‖) atTop (𝓝 0))

/-- The same basicity assertion on the manuscript's original raw basis,
with the continuous coordinates explicitly identified. -/
def RawDualBasicity : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = ExpandedFA.P1.C15Basis.Spec.rawCoordinates h x i) ∧
      ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (dualVector b)

/-- Finite lists, including the empty basis, have dual basicity, exhaust the
whole dual, have eventually exact dual expansions and vanishing closed tails.
Every finite coefficient series converges, so bounded completeness is automatic. -/
def FiniteDualFacts : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ} (b : UnconditionalSchauderBasis (Fin d) 𝕜 E),
    let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
    let e' : Fin d → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self i))⟩
    ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e' ∧
    F = ⊤ ∧
    (∀ f : E →L[𝕜] 𝕜, ∀ N, d ≤ N →
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < N), f (b i) • b.coord i = f) ∧
    (∀ f : E →L[𝕜] 𝕜,
      Tendsto (fun N => ‖f.comp
        ((Submodule.span 𝕜 (b '' {i : Fin d | N ≤ i.val})).topologicalClosure).subtypeL‖)
        atTop (𝓝 0)) ∧
    (∀ a : Fin d → 𝕜, ∃ x : E,
      Tendsto (fun N => ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < N),
        a i • b i) atTop (𝓝 x))

-- Expected definition types and their full values.
def dualSpanType := ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E], SchauderBasis 𝕜 E → Submodule 𝕜 (E →L[𝕜] 𝕜)
def dualSpanValue : dualSpanType := @dualSpan

def dualVectorType := ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E], (b : SchauderBasis 𝕜 E) → ℕ → dualSpan b
def dualVectorValue : dualVectorType := @dualVector

def tailSpaceType := ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E], SchauderBasis 𝕜 E → ℕ → Submodule 𝕜 E
def tailSpaceValue : tailSpaceType := @tailSpace

def IsShrinkingType := ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E], SchauderBasis 𝕜 E → Prop
def IsShrinkingValue : IsShrinkingType := @IsShrinking

def IsBoundedlyCompleteType := ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E], (ℕ → E) → Prop
def IsBoundedlyCompleteValue : IsBoundedlyCompleteType := @IsBoundedlyComplete
end ExpandedFA.P1.DualBasisBasicity.Spec
