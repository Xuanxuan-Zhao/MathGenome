import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisCoefficients
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBoundedComplete
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Reflexive

/-! The complete theorem `fa2:p1:dual-bases`, paper.tex 4278–4339.
All duals are continuous scalar-linear duals; series use ordered partial sums.
The raw-basis statements preserve the manuscript's definition, without assuming
coordinate continuity. Finite lists include the empty basis of the zero space.
The definitions of shrinking, bounded completeness, and the coordinate closed
span are the accepted shared definitions, rather than extra hypotheses. -/

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBases.Spec
open DualBasisBasicity.Spec

/-- James's reflexivity criterion for any ordered Schauder basis. -/
def ReflexivityCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      IsShrinking b ∧ IsBoundedlyComplete (𝕜 := 𝕜) b.basis

/-- All assertions, using the actual coordinate sequence in its closed span. -/
def BasisFacts {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E) : Prop :=
  C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (dualVector b) ∧
  (IsShrinking b ↔ dualSpan b = ⊤) ∧
  (IsShrinking b ↔ ∀ f : E →L[𝕜] 𝕜,
    Tendsto (fun N => ‖f.comp (tailSpace b N).subtypeL‖) atTop (𝓝 0)) ∧
  ∃ d : SchauderBasis 𝕜 (dualSpan b), d.basis = dualVector b ∧
    (∀ i f, d.coord i f = f.val (b i)) ∧
    (IsBoundedlyComplete (𝕜 := 𝕜) d.basis ↔ IsShrinking b) ∧
    (IsShrinking d ↔ IsBoundedlyComplete (𝕜 := 𝕜) b.basis) ∧
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      IsShrinking b ∧ IsBoundedlyComplete (𝕜 := 𝕜) b.basis)

def DualBases : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E), BasisFacts b

def RawDualBases : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = C15Basis.Spec.rawCoordinates h x i) ∧ BasisFacts b

/-- The finite versions use the same ordered cutoff convention as the source. -/
def finiteShrinking {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
    (b : UnconditionalSchauderBasis (Fin n) 𝕜 E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, Tendsto (fun N =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), f (b i) • b.coord i)
    atTop (𝓝 f)

def finiteBoundedlyComplete {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ} (e : Fin n → E) : Prop :=
  ∀ a : Fin n → 𝕜, BddAbove (Set.range (fun N =>
    ‖∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), a i • e i‖)) →
    ∃ x : E, Tendsto (fun N =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N), a i • e i)
      atTop (𝓝 x)

def FiniteBasisFacts {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
    (b : UnconditionalSchauderBasis (Fin n) 𝕜 E) : Prop :=
  let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
  let e' : Fin n → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i))⟩
  C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e' ∧
  (finiteShrinking b ↔ F = ⊤) ∧
  (finiteShrinking b ↔ ∀ f : E →L[𝕜] 𝕜,
    Tendsto (fun N => ‖f.comp
      ((Submodule.span 𝕜 (b '' {i : Fin n | N ≤ i.val})).topologicalClosure).subtypeL‖)
      atTop (𝓝 0)) ∧
  ∃ d : UnconditionalSchauderBasis (Fin n) 𝕜 F, d.basis = e' ∧
    (∀ i f, d.coord i f = f.val (b i)) ∧
    (finiteBoundedlyComplete (𝕜 := 𝕜) d.basis ↔ finiteShrinking b) ∧
    (finiteShrinking d ↔ finiteBoundedlyComplete (𝕜 := 𝕜) b.basis) ∧
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      finiteShrinking b ∧ finiteBoundedlyComplete (𝕜 := 𝕜) b.basis)

def FiniteDualBases : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {n : ℕ} (b : UnconditionalSchauderBasis (Fin n) 𝕜 E), FiniteBasisFacts b

def RawFiniteDualBases : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {n : ℕ} {e : Fin n → E} (h : C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    ∃ b : UnconditionalSchauderBasis (Fin n) 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = C15Basis.Spec.finiteCoordinates h x i) ∧ FiniteBasisFacts b

end ExpandedFA.P1.DualBases.Spec
