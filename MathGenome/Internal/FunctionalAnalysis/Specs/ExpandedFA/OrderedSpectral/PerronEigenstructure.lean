import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Independent statement of the eigenstructure part of
`fa2:p2:perron-cq`, paper.tex:11692–11745. The power convergence and
Markov normalization are allocated to `PerronPowers`.

The functions and dual are complex scalar-linear. Positivity refers to the
pointwise real cone, and never to a Hilbert quadratic form. The Borel
measurable structure is arbitrary up to `BorelSpace`, so this imposes no
countability, metrizability, or measure hypothesis on the compact space. -/
namespace ExpandedFA.OrderedSpectral.PerronEigenstructure.Spec

open MeasureTheory
universe u
variable {Q : Type u} [TopologicalSpace Q]

def RealValued (f : C(Q, ℂ)) : Prop := ∀ q, (f q).im = 0

def Nonnegative (f : C(Q, ℂ)) : Prop := ∀ q, (f q).im = 0 ∧ 0 ≤ (f q).re

def StrictlyPositive (f : C(Q, ℂ)) : Prop := ∀ q, (f q).im = 0 ∧ 0 < (f q).re

variable [CompactSpace Q]

def PreservesReal (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : Prop :=
  ∀ f, RealValued f → RealValued (K f)

def StronglyPositive (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : Prop :=
  ∀ f, Nonnegative f → f ≠ 0 → StrictlyPositive (K f)

noncomputable def radius (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : ℝ :=
  Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectralRadiusValue
    ℂ (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) K

/-- Every positive power kernel is exactly the eigenline: algebraic, not
merely geometric, simplicity. Nonzeroness of u is supplied by strict
positivity on a nonempty Q. -/
def AlgebraicallySimple (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (r : ℝ)
    (u : C(Q, ℂ)) : Prop :=
  ∀ n : ℕ, 0 < n →
    LinearMap.ker (((r : ℂ) • LinearMap.id - K.toLinearMap) ^ n) =
      Submodule.span ℂ {u}

variable [MeasurableSpace Q]

/-- A normalized positive Radon eigenmeasure and its actual continuous
scalar-linear functional. The integral contains no conjugation. -/
def Eigenmeasure (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (r : ℝ)
    (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q) : Prop :=
  FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ ∧
  μ Set.univ = 1 ∧
  (∀ f : C(Q, ℂ), Integrable f μ ∧ φ f = ∫ q, f q ∂μ) ∧
  (∀ f : C(Q, ℂ), φ (K f) = (r : ℂ) * φ f)

/-- The full assigned conclusion, with an actual positive Borel measure,
strictly positive eigenfunction, algebraic simplicity, and the strict bound
for every other complex eigenvalue (including zero). -/
def Conclusion (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : Prop :=
  0 < radius K ∧
  ∃ (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q),
    StrictlyPositive u ∧ K u = (radius K : ℂ) • u ∧
    AlgebraicallySimple K (radius K) u ∧
    Eigenmeasure K (radius K) φ μ ∧
    (φ u).im = 0 ∧ 0 < (φ u).re ∧
    ∀ (ζ : ℂ) (z : C(Q, ℂ)), z ≠ 0 → K z = ζ • z →
      ζ ≠ (radius K : ℂ) → ‖ζ‖ < radius K

def EigenstructureTheorem : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    IsCompactOperator K → PreservesReal K → StronglyPositive K → Conclusion K



/-- Independent type of the assembly step from an eigenpair and eigenmeasure.
Their existence is asserted separately by `EigenstructureTheorem`. -/
def AssemblyFromWitnesses : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    PreservesReal K → StronglyPositive K → 0 < radius K →
    ∀ (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q),
      StrictlyPositive u → K u = (radius K : ℂ) • u →
      Eigenmeasure K (radius K) φ μ →
      (φ u).im = 0 → 0 < (φ u).re → Conclusion K



/-- Completed comparison lemma. Compactness of the operator is not needed
once a strictly positive eigenpair is given. -/
def PeripheralEigenvector : Prop :=
  ∀ {Q : Type u} [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    PreservesReal K → StronglyPositive K → ∀ {r : ℝ}, 0 < r →
    ∀ {u : C(Q, ℂ)}, StrictlyPositive u → K u = (r : ℂ) • u →
    ∀ {ζ : ℂ} {z : C(Q, ℂ)}, z ≠ 0 → K z = ζ • z → r ≤ ‖ζ‖ →
      ζ = (r : ℂ) ∧ ∃ a : ℂ, z = a • u

/-- Completed Jordan-chain exclusion lemma, with explicit dual data. -/
def AlgebraicSimplicityFromEigenfunctional : Prop :=
  ∀ {Q : Type u} [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    PreservesReal K → StronglyPositive K → ∀ {r : ℝ}, 0 < r →
    ∀ {u : C(Q, ℂ)}, StrictlyPositive u → K u = (r : ℂ) • u →
    ∀ (φ : C(Q, ℂ) →L[ℂ] ℂ), (∀ f, φ (K f) = (r : ℂ) * φ f) →
      φ u ≠ 0 → AlgebraicallySimple K r u

end ExpandedFA.OrderedSpectral.PerronEigenstructure.Spec
