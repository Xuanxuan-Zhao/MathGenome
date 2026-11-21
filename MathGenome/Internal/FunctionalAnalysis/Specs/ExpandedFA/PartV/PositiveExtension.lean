import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Sublinear
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent specification of `fa2:p5:positive-extension`, paper.tex:23168–23194.
The algebraic extension even permits a preorder (a nonproper positive cone).
The order-unit norm uses a partial order and the Archimedean order-unit condition.
There are no completeness, closedness, or nonzero-space assumptions. -/

noncomputable section
universe u
namespace ExpandedFA.PartV.PositiveExtension

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]

/-- Positivity uses the ambient positive cone, including on subspaces. -/
def PositiveOn (M : Submodule ℝ E) (f : M →ₗ[ℝ] ℝ) : Prop :=
  ∀ m : M, 0 ≤ (m : E) → 0 ≤ f m

/-- The subspace is cofinal for the vector order. -/
def Majorizing (M : Submodule ℝ E) : Prop := ∀ x : E, ∃ m : M, x ≤ (m : E)

/-- The real numbers whose infimum defines the dominated-extension majorant. -/
def MajorantValues (M : Submodule ℝ E) (f : M →ₗ[ℝ] ℝ) (x : E) : Set ℝ :=
  {r | ∃ m : M, x ≤ (m : E) ∧ f m = r}

def majorant (M : Submodule ℝ E) (f : M →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  sInf (MajorantValues M f x)

/-- A positive order unit bounds every vector in a symmetric scalar interval. -/
def IsOrderUnit (e : E) : Prop :=
  0 ≤ e ∧ ∀ x : E, ∃ t : ℝ, 0 ≤ t ∧ -(t • e) ≤ x ∧ x ≤ t • e

/-- Archimedeanity relative to the order unit: infinitesimal upper bounds imply
nonpositivity. Equivalently, `x + ε • e ≥ 0` for every `ε > 0` implies `x ≥ 0`. -/
def ArchimedeanUnit (e : E) : Prop :=
  ∀ x : E, (∀ ε : ℝ, 0 < ε → x ≤ ε • e) → x ≤ 0

def UnitBounds (e x : E) : Set ℝ :=
  {t | 0 ≤ t ∧ -(t • e) ≤ x ∧ x ≤ t • e}

/-- The order-unit gauge, including the zero space. -/
def orderUnitGauge (e x : E) : ℝ := sInf (UnitBounds e x)

namespace Spec

def MajorantConstruction : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (M : Submodule ℝ E), Majorizing M →
    ∀ (f : M →ₗ[ℝ] ℝ), PositiveOn M f →
    (∀ x, (MajorantValues M f x).Nonempty ∧ BddBelow (MajorantValues M f x)) ∧
    Specs.ExpandedFA.P1.C05Sublinear.isSublinearValue (majorant M f) ∧
    (∀ m : M, majorant M f (m : E) = f m)

def ExtensionTheorem : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (M : Submodule ℝ E), Majorizing M →
    ∀ (f : M →ₗ[ℝ] ℝ), PositiveOn M f →
    ∃ L : E →ₗ[ℝ] ℝ, (∀ m : M, L (m : E) = f m) ∧
      (∀ x, 0 ≤ x → 0 ≤ L x) ∧ (∀ x, L x ≤ majorant M f x)

def OrderUnitMajorizes : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
    (M : Submodule ℝ E) (e : E), e ∈ M → IsOrderUnit e → Majorizing M

def OrderUnitPositiveExtension : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (M : Submodule ℝ E) (e : E), e ∈ M → IsOrderUnit e →
    ∀ (f : M →ₗ[ℝ] ℝ), PositiveOn M f →
    ∃ L : E →ₗ[ℝ] ℝ, (∀ m : M, L (m : E) = f m) ∧
      (∀ x, 0 ≤ x → 0 ≤ L x)

/-- This proves that the gauge really is a norm, rather than assuming it is one. -/
def OrderUnitNormAxioms : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (e : E), IsOrderUnit e → ArchimedeanUnit e →
    ExpandedFA.P1.C01Norm.NormAxioms ℝ (orderUnitGauge e)

/-- Native metric and normed-space realization of the gauge, with precisely the
original additive and scalar operations. No prior norm on `E` is needed. -/
def OrderUnitSpaceRealization : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [m : Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (e : E), IsOrderUnit e → ArchimedeanUnit e →
    ∃ p : Seminorm ℝ E, (∀ x, p x = orderUnitGauge e x) ∧
      ∃ hd : ∀ x, p x = 0 → x = 0,
        letI := ExpandedFA.P1.C01Norm.normedGroup p hd
        (∃ n : NormedSpace ℝ E, n.toModule = m) ∧
          ExpandedFA.P1.C01Norm.NormGeometry (orderUnitGauge e)

def OrderUnitNormalization : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (e : E), IsOrderUnit e → (e = 0 → orderUnitGauge e e = 0) ∧
      (e ≠ 0 → orderUnitGauge e e = 1)

/-- Any native norm equal to the established order-unit norm gives the claimed
continuous extension and its exact operator norm. The zero-space case is included. -/
def BoundedPositiveExtension : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    (M : Submodule ℝ E) (e : E) (he : e ∈ M),
    IsOrderUnit e → ArchimedeanUnit e →
    (∀ x : E, ‖x‖ = orderUnitGauge e x) →
    ∀ (f : M →ₗ[ℝ] ℝ), PositiveOn M f →
    ∃ L : E →L[ℝ] ℝ, (∀ m : M, L (m : E) = f m) ∧
      (∀ x, 0 ≤ x → 0 ≤ L x) ∧ ‖L‖ = f ⟨e, he⟩

end Spec
end ExpandedFA.PartV.PositiveExtension
