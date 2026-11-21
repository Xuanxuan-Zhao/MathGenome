import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.MeasureTheory.Function.L2Space

/-! The minimal momentum operator on the unit interval, and the maximal
operator with the same differential expression. R¹ is the accepted Sobolev
coordinate model; `linePoint` identifies it measure preservingly with R. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Unbounded.IntervalDerivative
open ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

abbrev interval : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
abbrev L2 := DomainLp ℂ (lineDomain interval) 2
abbrev H1 := W1p ℂ interval 2

/-- The original closure of compactly supported smooth functions in H¹. -/
def zeroBoundary : Submodule ℂ H1 :=
  ZeroSpaceValue ℂ 1 (lineDomain interval) 1 2 (by norm_num)

def baseMap : H1 →ₗ[ℂ] L2 where
  toFun := baseLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def derivativeMap : H1 →ₗ[ℂ] L2 where
  toFun := derivativeLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Graph parametrization by the actual weak derivative, with coefficient -i. -/
def momentumPair : H1 →ₗ[ℂ] L2 × L2 :=
  baseMap.prod ((-Complex.I) • derivativeMap)

def maximalGraph : Submodule ℂ (L2 × L2) := momentumPair.range

def minimalGraph : Submodule ℂ (L2 × L2) :=
  (momentumPair.comp zeroBoundary.subtype).range

/-- Mathlib's graph-to-partial-map construction. The graph identities below
prove that these canonical submodules really are single-valued graphs. -/
def minimal : Operator ℂ L2 L2 := minimalGraph.toLinearPMap

def maximal : Operator ℂ L2 L2 := maximalGraph.toLinearPMap

end ExpandedFA.Unbounded.IntervalDerivative

namespace Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint
open _root_.ExpandedFA.Unbounded _root_.ExpandedFA.Unbounded.IntervalDerivative
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.OneDimensional

/-- These identities also specify the action, not only the operator domains. -/
def Graphs : Prop := minimal.graph = minimalGraph ∧ maximal.graph = maximalGraph

def Domains : Prop := minimal.domain = zeroBoundary.map baseMap ∧
  maximal.domain = baseMap.range

def DenseDomain : Prop := Dense (minimal.domain : Set L2)

def AbsolutelyContinuousRepresentatives : Prop := ∀ (u : H1) (f : ℝ → ℂ),
  PrimitiveRepresentative u f → AbsolutelyContinuousOnInterval f 0 1

/-- On the open interval the AC representative has the accepted weak
derivative as its ordinary almost-everywhere derivative. -/
def RepresentativeDerivative : Prop := ∀ (u : H1) (f : ℝ → ℂ),
  PrimitiveRepresentative u f →
    ∀ᵐ t ∂volume.restrict (interval : Set ℝ),
      HasDerivAt f (lineFunction (derivativeLp u) t) t

def BoundaryForm : Prop := ∀ (u v : H1) (f g : ℝ → ℂ),
  PrimitiveRepresentative u f → PrimitiveRepresentative v g →
    inner ℂ ((-Complex.I) • derivativeLp u) (baseLp v) -
      inner ℂ (baseLp u) ((-Complex.I) • derivativeLp v) =
        Complex.I * (star (f 1) * g 1 - star (f 0) * g 0)

/-- Equality of partial maps includes equality of their exact domains. -/
def AdjointEquality : Prop := HilbertAdjointSpec.adjointValue minimal = maximal

/-- The explicit existential domain and differential expression, independently
of any arbitrary chosen representative or choice of Sobolev preimage. -/
def AdjointDomain : Prop := ∀ v : L2,
  v ∈ (HilbertAdjointSpec.adjointValue minimal).domain ↔
    ∃ u : H1, baseLp u = v

def AdjointAction : Prop := ∀ (u : H1)
  (hu : baseLp u ∈ (HilbertAdjointSpec.adjointValue minimal).domain),
  HilbertAdjointSpec.adjointValue minimal ⟨baseLp u, hu⟩ = (-Complex.I) • derivativeLp u

end Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint
