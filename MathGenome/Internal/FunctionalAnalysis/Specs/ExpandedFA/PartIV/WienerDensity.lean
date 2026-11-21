import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerLocalIdeal
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
open MeasureTheory
open scoped Topology

namespace ExpandedFA.PartIV.WienerDensity
open ExpandedFA.Fourier ExpandedFA.PartIV.WienerLocalIdeal

/-- The closed complex linear span of all ordinary translates of an L¹ kernel. -/
def closedTranslateSpan {d : ℕ} (K : L1 d) : Submodule ℂ (L1 d) :=
  (Submodule.span ℂ (Set.range (fun y => translate y K))).topologicalClosure

abbrev RealL1 (d : ℕ) := Lp ℝ 1 (volume : Measure (Euclidean d))

def realTranslate {d : ℕ} (y : Euclidean d) (f : RealL1 d) : RealL1 d :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) f

def RealTranslationInvariant {d : ℕ} (Y : Submodule ℝ (RealL1 d)) : Prop :=
  ∀ y f, f ∈ Y → realTranslate y f ∈ Y

def closedRealTranslateSpan {d : ℕ} (K : RealL1 d) : Submodule ℝ (RealL1 d) :=
  (Submodule.span ℝ (Set.range (fun y => realTranslate y K))).topologicalClosure

end ExpandedFA.PartIV.WienerDensity

namespace Specs.ExpandedFA.PartIV.WienerDensity
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.WienerLocalIdeal
open _root_.ExpandedFA.PartIV.WienerDensity

/-- The closed translation-invariant subspace criterion, including dimension zero. -/
def SubspaceCriterion : Prop := ∀ (d : ℕ) (Y : Submodule ℂ (L1 d)),
  IsClosed (Y : Set (L1 d)) → TranslationInvariant Y →
  (Y = ⊤ ↔ ∀ ξ : Euclidean d, ∃ f : L1 d, f ∈ Y ∧ integralFourier f ξ ≠ 0)

/-- The single-kernel version uses the closure of its actual translation span. -/
def TranslateCriterion : Prop := ∀ (d : ℕ) (K : L1 d),
  closedTranslateSpan K = ⊤ ↔ ∀ ξ : Euclidean d, integralFourier K ξ ≠ 0

/-- The real-scalar variant, with the usual complex-valued Fourier transform. -/
def RealSubspaceCriterion : Prop := ∀ (d : ℕ) (Y : Submodule ℝ (RealL1 d)),
  IsClosed (Y : Set (RealL1 d)) → RealTranslationInvariant Y →
  (Y = ⊤ ↔ ∀ ξ : Euclidean d, ∃ f : RealL1 d,
    f ∈ Y ∧ integralFourier (fun x => (f x : ℂ)) ξ ≠ 0)

def RealTranslateCriterion : Prop := ∀ (d : ℕ) (K : RealL1 d),
  closedRealTranslateSpan K = ⊤ ↔
    ∀ ξ : Euclidean d, integralFourier (fun x => (K x : ℂ)) ξ ≠ 0

end Specs.ExpandedFA.PartIV.WienerDensity
