import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! Intrinsic real Fredholm and spectral comparison with the canonical Hilbert
complexification; paper.tex:67–73, 10586–10664, 10690–10717. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Fredholm.RealFredholmComplexification
universe v w
open TraceIdeals.RealComplexification hiding Space
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification
open DefinitionsSpec
namespace Spec
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complex subspace S + iS inside the existing canonical Space H. -/
def complexSubspace (S : Submodule ℝ H) : Submodule ℂ (Space H) where
  carrier := {p | p.1 ∈ S ∧ p.2 ∈ S}
  zero_mem' := ⟨S.zero_mem, S.zero_mem⟩
  add_mem' := fun hp hq => ⟨S.add_mem hp.1 hq.1, S.add_mem hp.2 hq.2⟩
  smul_mem' a p hp := by
    rw [csmul]
    exact ⟨S.sub_mem (S.smul_mem a.re hp.1) (S.smul_mem a.im hp.2),
      S.add_mem (S.smul_mem a.im hp.1) (S.smul_mem a.re hp.2)⟩

def KernelRange : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    (TraceIdeals.RealComplexification.Spec.operator T).ker = complexSubspace T.ker ∧
    (TraceIdeals.RealComplexification.Spec.operator T).range = complexSubspace T.range ∧
    (∀ p : Space K, p ∈ (TraceIdeals.RealComplexification.Spec.operator T).range ↔
      ∃ x y : H, p = complexPair K (T x) (T y))

def ClosedRange : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    IsClosed (T.range : Set K) ↔
      IsClosed ((TraceIdeals.RealComplexification.Spec.operator T).range : Set (Space K))

def KernelIdentification : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    ∃ e : Space T.ker ≃ₗᵢ[ℂ] (TraceIdeals.RealComplexification.Spec.operator T).ker,
      ∀ p, (e p).val = complexPair H p.1.val p.2.val

def CokernelIdentification : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    IsClosed (T.range : Set K) →
    ∃ e : Space T.range.orthogonal ≃ₗᵢ[ℂ]
        (TraceIdeals.RealComplexification.Spec.operator T).range.orthogonal,
      ∀ p, (e p).val = complexPair K p.1.val p.2.val

/-- The algebraic cokernel clauses also include nonclosed ranges. -/
def Dimensions : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    (FiniteDimensional ℝ T.ker ↔
      FiniteDimensional ℂ (TraceIdeals.RealComplexification.Spec.operator T).ker) ∧
    (FiniteDimensional ℝ (K ⧸ T.range) ↔
      FiniteDimensional ℂ (Space K ⧸ (TraceIdeals.RealComplexification.Spec.operator T).range)) ∧
    (FiniteDimensional ℝ T.ker → Module.finrank ℝ T.ker =
      Module.finrank ℂ (TraceIdeals.RealComplexification.Spec.operator T).ker) ∧
    (FiniteDimensional ℝ (K ⧸ T.range) → Module.finrank ℝ (K ⧸ T.range) =
      Module.finrank ℂ (Space K ⧸ (TraceIdeals.RealComplexification.Spec.operator T).range))

def Fredholm : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    IsFredholmValue T ↔ IsFredholmValue (TraceIdeals.RealComplexification.Spec.operator T)

def Index : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K)
    (h : IsFredholmValue T) (hC : IsFredholmValue (TraceIdeals.RealComplexification.Spec.operator T)),
    fredholmIndexValue T h = fredholmIndexValue (TraceIdeals.RealComplexification.Spec.operator T) hC

local instance [CompleteSpace H] : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

def Spectrum : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (r : ℝ),
    r ∈ spectrum ℝ T ↔ (r : ℂ) ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator T)

def Shift : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (r : ℝ),
    TraceIdeals.RealComplexification.Spec.operator (T - r • ContinuousLinearMap.id ℝ H) =
      TraceIdeals.RealComplexification.Spec.operator T - (r : ℂ) • ContinuousLinearMap.id ℂ (Space H) ∧
    (¬ IsFredholmValue (T - r • ContinuousLinearMap.id ℝ H) ↔
      ¬ IsFredholmValue (TraceIdeals.RealComplexification.Spec.operator T -
        (r : ℂ) • ContinuousLinearMap.id ℂ (Space H))) ∧
    (∀ (h : IsFredholmValue (T - r • ContinuousLinearMap.id ℝ H))
      (hC : IsFredholmValue (TraceIdeals.RealComplexification.Spec.operator T -
        (r : ℂ) • ContinuousLinearMap.id ℂ (Space H))),
      fredholmIndexValue (T - r • ContinuousLinearMap.id ℝ H) h =
      fredholmIndexValue (TraceIdeals.RealComplexification.Spec.operator T -
        (r : ℂ) • ContinuousLinearMap.id ℂ (Space H)) hC)

def Normality : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H),
    IsStarNormal T ↔ IsStarNormal (TraceIdeals.RealComplexification.Spec.operator T)
end Spec
end ExpandedFA.Fredholm.RealFredholmComplexification
