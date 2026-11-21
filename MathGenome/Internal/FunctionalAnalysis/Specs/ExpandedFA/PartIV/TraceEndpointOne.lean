import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HalfSpaceExtension

/-! Independent scope of paper.tex, fa2:p4:sharp-trace, p=1 clause.
The boundary of the coordinate half-space has d-1 transverse coordinates,
with ordinary product Lebesgue measure, also when d=1. A coordinate i : Fin d
specifies a genuine half-space; there is no half-space in dimension zero.
Scalars range over both ℝ and ℂ. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.PartIV.TraceEndpointOne
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Lines ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

abbrev HalfSpaceW11 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (i : Fin d) :=
  SpaceValue 𝕜 d (upper i) 1 1

abbrev FlatL1 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (i : Fin d) :=
  Lp 𝕜 1 (volume : Measure (Transverse i))

/-- The trace is the bounded scalar-linear extension of genuine smooth
boundary restriction. This predicate assumes neither surjectivity nor a lift. -/
def IsFlatTrace {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d)
    (T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i) : Prop :=
  ∀ (u : HalfSpaceW11 𝕜 i) (f : Domain d → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) f →
    u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
    T u =ᵐ[volume] fun y : Transverse i => f (coordinateLine i y 0)

end ExpandedFA.PartIV.TraceEndpointOne

namespace Specs.ExpandedFA.PartIV.TraceEndpointOne
open _root_.ExpandedFA.PartIV.TraceEndpointOne

/-- Every datum, including zero, has an extension in the original weak
Sobolev derivative graph. This is a statement about every genuine trace,
so the conclusion cannot be realized by choosing an unrelated surjection. -/
def Surjectivity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i), IsFlatTrace i T →
  ∀ g : FlatL1 𝕜 i, ∃ u : HalfSpaceW11 𝕜 i, T u = g

/-- A trace exists and is unique; its range is the whole boundary L1 space.
There is no linear or continuous choice of the extensions in this statement. -/
def OntoTraceExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d),
  ∃! T : HalfSpaceW11 𝕜 i →L[𝕜] FlatL1 𝕜 i,
    IsFlatTrace i T ∧ Function.Surjective T

end Specs.ExpandedFA.PartIV.TraceEndpointOne
