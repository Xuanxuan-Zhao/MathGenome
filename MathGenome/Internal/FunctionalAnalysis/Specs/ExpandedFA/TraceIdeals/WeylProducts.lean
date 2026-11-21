import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularApproximation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Finset.Prod

/-!
Product stage of `fa2:p2:weyl-inequalities`, paper.tex:11486–11516.

The field is complex; the Hilbert space may be zero or nonseparable.
Algebraic multiplicity means the dimension of the FULL generalized
eigenspace, not the ordinary eigenspace. Compact Riesz theory makes
this dimension finite at nonzero scalars. Singular values are the accepted
spectral order statistics (one-based, zero-padded).

We state the stronger, order-independent finite-selection version: a scalar
may occur at most its algebraic multiplicity. Thus every initial segment of
the decreasing-modulus list is covered, even when the last entry cuts through
a Jordan block. No invariant subspace or determinant estimate is assumed.
-/
noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.WeylProducts.Spec

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def algebraicMultiplicity (T : H →L[ℂ] H) (z : ℂ) : ℕ :=
  Module.finrank ℂ (Module.End.maxGenEigenspace T.toLinearMap z)

/-- A finite selection of actual nonzero eigenvalues, with algebraic multiplicity.
Ordering is unnecessary for the stronger product estimate. -/
def EigenvalueSelection (T : H →L[ℂ] H) {n : ℕ} (ev : Fin n → ℂ) : Prop := by
  classical
  exact (∀ i, ev i ≠ 0 ∧ Module.End.HasEigenvalue T.toLinearMap (ev i)) ∧
    ∀ z : ℂ, (Finset.univ.filter (fun i => ev i = z)).card ≤ algebraicMultiplicity T z

/-- Padding by zeros does not count the (possibly infinite-dimensional)
zero generalized eigenspace. -/
def PaddedEigenvalueSelection (T : H →L[ℂ] H) {n : ℕ} (ev : Fin n → ℂ) : Prop := by
  classical
  exact (∀ i, ev i ≠ 0 → Module.End.HasEigenvalue T.toLinearMap (ev i)) ∧
    ∀ z : ℂ, z ≠ 0 →
      (Finset.univ.filter (fun i => ev i = z)).card ≤ algebraicMultiplicity T z

/-- The full required product bound. Any initial segment of the manuscript's
list satisfies `EigenvalueSelection`; this statement also permits reordering
or selecting eigenvalues further down that list. The empty product is included. -/
def WeylProduct : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ (n : ℕ) (ev : Fin n → ℂ), EigenvalueSelection T ev →
      (∏ i, ‖ev i‖) ≤
        ∏ i : Fin n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1)

/-- The same statement with arbitrary zero padding. -/
def PaddedWeylProduct : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ (n : ℕ) (ev : Fin n → ℂ), PaddedEigenvalueSelection T ev →
      (∏ i, ‖ev i‖) ≤
        ∏ i : Fin n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1)

/-- Analytic determinant bound, in the project's spectral convention. -/
def FiniteDeterminantBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
    letI : CompleteSpace E := FiniteDimensional.complete ℂ E
    ∀ (A : E →L[ℂ] E), ‖A.toLinearMap.det‖ ≤
      ∏ i : Fin (Module.finrank ℂ E),
        CompactSpectral.SingularApproximation.Spec.SingularValueValue A (i.val + 1)

/-- The analytic bound for an actual finite-dimensional invariant subspace.
The determinant belongs to the restriction, with the inherited Hilbert norm. -/
def InvariantDeterminantBound : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ (M : Submodule ℂ H) [FiniteDimensional ℂ M]
      (hM : ∀ x ∈ M, T x ∈ M),
      ‖(T.toLinearMap.restrict hM).det‖ ≤
        ∏ i : Fin (Module.finrank ℂ M),
          CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1)

/-- Finite-dimensional invariant realization of the selected algebraic
multiplicities, with the determinant of the actual restriction. -/
def CompactInvariantRealization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ (n : ℕ) (ev : Fin n → ℂ), EigenvalueSelection T ev →
      ∃ M : Submodule ℂ H, FiniteDimensional ℂ M ∧
        ∃ hM : ∀ x ∈ M, T x ∈ M,
          Module.finrank ℂ M = n ∧ (T.toLinearMap.restrict hM).det = ∏ i, ev i

def RealizationImpliesWeyl : Prop := CompactInvariantRealization.{u} → WeylProduct.{u}
def WeylImpliesPaddedWeyl : Prop := WeylProduct.{u} → PaddedWeylProduct.{u}

end ExpandedFA.TraceIdeals.WeylProducts.Spec
