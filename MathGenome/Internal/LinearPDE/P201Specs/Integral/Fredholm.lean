import MathGenome.Internal.LinearPDE.P201Specs.Integral.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The full compact-kernel Fredholm bridge, paper.tex:4298–4366.
All dimensions are complex dimensions. The quotient is by the actual range;
the transpose acts on the continuous complex-linear dual. No full-support,
regularity, metrizability, or nonemptiness assumption is needed. -/

universe u
open MeasureTheory
namespace P201.Integral.Fredholm.Spec

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The source's unnormalized operator zI − T. -/
noncomputable def fredholmMap (T : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  z • ContinuousLinearMap.id ℂ E - T

/-- Composition with a bounded operator, with no conjugation of scalars. -/
noncomputable def transpose (T : E →L[ℂ] E) :
    StrongDual ℂ E →L[ℂ] StrongDual ℂ E :=
  ExpandedFA.P1.C04Annihilators.Spec.BanachTransposeValue ℂ E E T

/-- The complete conclusion for the specified operator and nonzero parameter. -/
def Conclusion (T : E →L[ℂ] E) (z : ℂ) : Prop :=
  let F := fredholmMap T z
  let Ft := transpose F
  Ft = z • ContinuousLinearMap.id ℂ (StrongDual ℂ E) - transpose T ∧
  IsClosed (F.range : Set E) ∧
  FiniteDimensional ℂ F.ker ∧
  FiniteDimensional ℂ (E ⧸ F.range) ∧
  FiniteDimensional ℂ Ft.ker ∧
  Module.finrank ℂ F.ker = Module.finrank ℂ (E ⧸ F.range) ∧
  Module.finrank ℂ (E ⧸ F.range) = Module.finrank ℂ Ft.ker ∧
  (∀ g : E, (∃ f : E, F f = g) ↔
    ∀ ℓ : StrongDual ℂ E, ℓ ∈ Ft.ker → ℓ g = 0) ∧
  (∀ g f₀ : E, F f₀ = g → ∀ f : E,
    F f = g ↔ ∃ v ∈ F.ker, f = f₀ + v) ∧
  ((∃ e : E ≃L[ℂ] E, ∀ f, e f = F f) ∨
    (0 < Module.finrank ℂ F.ker ∧ 0 < Module.finrank ℂ Ft.ker))

/-- Includes the integral representation, integrability, output continuity,
norm bound, and compactness from the operator part of the same source theorem.
The Fredholm clauses use exactly that canonical operator on C(K,ℂ). -/
def FullTheorem : Prop :=
  ContinuousKernel.Spec.KernelTheorem.{u} ∧
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k : C(K × K, ℂ)) (z : ℂ), z ≠ 0 →
    Conclusion (ContinuousKernel.Spec.OperatorValue μ k) z

end P201.Integral.Fredholm.Spec
