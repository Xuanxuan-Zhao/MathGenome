import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-! Structure and ordinary trace, paper.tex:3669–3704.
The structure assertions hold on every open set, a stronger statement than the
bounded positive-dimensional source setting. For traces the physical dimension
is n+1, so n=0 includes dimension one. The shared graph-chart hypothesis is
bounded Lipschitz openness, without connectedness or nonemptiness. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ContDiff

namespace VariationalNotes.Sobolev

/-- Euclidean vector data with the ordinary normalized Hausdorff surface measure. -/
abbrev BoundaryVectorLp {n : ℕ} (Ω : Opens (Domain (n+1))) (m : ℕ) (p : Exponent) :=
  Lp (Vector m) p.ennreal (P102.Trace.Ordinary.boundaryMeasure Ω)

/-- The trace agrees with every smooth ambient representative on the boundary. -/
def IsVectorTrace {n m : ℕ} {Ω : Opens (Domain (n+1))} {p : Exponent}
    (T : W1p Ω m p →L[ℝ] BoundaryVectorLp Ω m p) : Prop :=
  ∀ (u : W1p Ω m p) (f : Domain (n+1) → Vector m), ContDiff ℝ ∞ f →
    (value Ω m p u : Domain (n+1) → Vector m) =ᵐ[domainMeasure Ω] f →
    (T u : Domain (n+1) → Vector m) =ᵐ[P102.Trace.Ordinary.boundaryMeasure Ω] f

namespace StructureExpected

def Banach : Prop := ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
  CompleteSpace (W1p Ω m p)

def Reflexive : Prop := ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
  1 < p.real → ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ (W1p Ω m p)

def AffineClosed : Prop := ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
  (u₀ : W1p Ω m p), IsClosed (affineClass Ω m p u₀) ∧
    IsClosed ((toWeakSpace ℝ (W1p Ω m p)) '' affineClass Ω m p u₀)

/-- Bounded linear ordinary trace in the actual norm, including p=1.
Smooth compatibility identifies the map as the ordinary trace, and the kernel
is the actual closure of compactly supported smooth vector functions. -/
def Trace : Prop := ∀ (n m : ℕ)
  (e : P102.U4.GraphPieces.Ambient n ≃ₗᵢ[ℝ] Domain (n+1))
  (Ω : Opens (Domain (n+1))),
  P102.Sobolev.Geometry.IsLipschitzOpen
    (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient n)) →
  ∀ p : Exponent, ∃ T : W1p Ω m p →L[ℝ] BoundaryVectorLp Ω m p,
    IsVectorTrace T ∧ T.ker = zeroSubmodule Ω m p ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖T u‖ ≤ C * ‖u‖

end StructureExpected
end VariationalNotes.Sobolev
