import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
Independent specification for the construction, density, closedness, adjoint,
normality and real-valued self-adjointness in paper.tex 13803–13846.
The product and sum rules and the strict product-domain example are allocated
separately to `ops_calculus_domains`.

Functions take values in ℂ, hence are finite everywhere. The measurable base
space and complex Hilbert space are arbitrary, including empty/zero cases.
There is no scalar control measure or separability hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace ExpandedFA.Unbounded.MeasurableSpectralCalculus
universe u v

section Limits
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The actual convergence domain, with its ambient linear structure. -/
def convergenceDomain (T : ℕ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | ∃ y, Tendsto (fun n => T n x) atTop (nhds y)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa only [map_add] using ha.add hb⟩
  smul_mem' := by
    rintro c x ⟨y, hy⟩
    exact ⟨c • y, by simpa only [map_smul] using hy.const_smul c⟩

/-- The norm limit, defined only on the subspace where that limit exists. -/
def limitOperator (T : ℕ → H →L[ℂ] H) : Operator ℂ H H where
  domain := convergenceDomain T
  toFun :=
    { toFun := fun x => atTop.limUnder (fun n => T n x)
      map_add' := by
        intro x y
        change (atTop.limUnder (fun n => T n ((x : H) + (y : H)))) = _
        exact (by
          simpa only [map_add] using
            ((tendsto_nhds_limUnder x.2).add (tendsto_nhds_limUnder y.2)).limUnder_eq)
      map_smul' := by
        intro c x
        change (atTop.limUnder (fun n => T n (c • (x : H)))) =
          c • atTop.limUnder (fun n => T n (x : H))
        exact (by
          simpa only [map_smul] using
            ((tendsto_nhds_limUnder x.2).const_smul c).limUnder_eq) }

end Limits

section Spectral
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Only bounded-calculus data and laws. These are consequences of the
accepted PVM axioms, not new hypotheses about an unbounded integral.
Uniform simple approximation fixes the bounded integral canonically. -/
structure BoundedRealization (E : SpectralMeasure.ProjectionValuedMeasure S H) where
  measure : H → Measure S
  integral : (S → ℂ) → H →L[ℂ] H
  finite : ∀ x, IsFiniteMeasure (measure x)
  measure_apply : ∀ x B, MeasurableSet B →
    measure x B = ENNReal.ofReal (‖E B x‖ ^ 2)
  simple : ∀ f : SimpleFunc S ℂ,
    integral f = SpectralMeasure.Spec.SimpleIntegralValue E f
  uniform_limit : ∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f →
    ∀ a : ℕ → SimpleFunc S ℂ, TendstoUniformly (fun n => a n) f atTop →
      Tendsto (fun n => SpectralMeasure.Spec.SimpleIntegralValue E (a n))
        atTop (nhds (integral f))
  one : integral (fun _ => 1) = 1
  add : ∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → integral (f + g) = integral f + integral g
  smul : ∀ (c : ℂ) f, SpectralMeasure.Spec.IsBoundedMeasurable f →
    integral (c • f) = c • integral f
  mul : ∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → integral (f * g) = integral f * integral g
  map_star : ∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → integral (star f) = star (integral f)
  bound : ∀ f C, SpectralMeasure.Spec.IsBoundedMeasurable f →
    0 ≤ C → (∀ s, ‖f s‖ ≤ C) → ‖integral f‖ ≤ C
  norm_sq : ∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → ∀ x,
    ‖integral f x‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂measure x

/-- The manuscript's truncation at the nonnegative integer n. -/
def truncation (f : S → ℂ) (n : ℕ) : S → ℂ :=
  {s | ‖f s‖ ≤ (n : ℝ)}.indicator f

def cutoffIndicator (f : S → ℂ) (n : ℕ) : S → ℂ :=
  {s | ‖f s‖ ≤ (n : ℝ)}.indicator (fun _ => 1)

/-- The maximal square-integrability condition uses the nonnegative integral.
In particular it is not the always-finite, totalized Bochner integral. -/
def SquareIntegrable {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) (f : S → ℂ) (x : H) : Prop :=
  (∫⁻ s, ENNReal.ofReal (‖f s‖ ^ 2) ∂C.measure x) < ⊤

/-- The proposed operator is the limit on exactly the convergence domain.
The theorem below must identify that domain with square integrability. -/
def measurableIntegral {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) (f : S → ℂ) : Operator ℂ H H :=
  limitOperator (fun n => C.integral (truncation f n))

namespace Spec

/-- Full mathematical obligation; ordinary partial-map equality
includes equality of domains, in particular both normal product domains. -/
def MeasurableCalculus {E : SpectralMeasure.ProjectionValuedMeasure S H}
    (C : BoundedRealization E) : Prop :=
  ∀ f : S → ℂ, Measurable f →
    (∀ x, x ∈ (measurableIntegral C f).domain ↔ SquareIntegrable C f x) ∧
    Dense ((measurableIntegral C f).domain : Set H) ∧
    (measurableIntegral C f).IsClosed ∧
    (measurableIntegral C f).adjoint = measurableIntegral C (star f) ∧
    OperatorDomainsSpec.productValue (measurableIntegral C f).adjoint
        (measurableIntegral C f) =
      OperatorDomainsSpec.productValue (measurableIntegral C f)
        (measurableIntegral C f).adjoint ∧
    ((∀ s, (f s).im = 0) → (measurableIntegral C f).adjoint = measurableIntegral C f) ∧
    (∀ x : (measurableIntegral C f).domain,
      Tendsto (fun n => C.integral (truncation f n) x) atTop (nhds (measurableIntegral C f x)))

def BoundedRealizationExists : Prop :=
  ∀ E : SpectralMeasure.ProjectionValuedMeasure S H, Nonempty (BoundedRealization E)

def MeasurableCalculusExists : Prop :=
  ∀ E : SpectralMeasure.ProjectionValuedMeasure S H,
    ∃ C : BoundedRealization E, MeasurableCalculus C

end Spec
end Spectral

namespace Spec

def MeasurableIntegralType :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure S H},
    BoundedRealization E → (S → ℂ) → Operator ℂ H H

def MeasurableIntegralValue : MeasurableIntegralType.{u, v} :=
  fun {_ _} _ _ _ _ {_} C f => measurableIntegral C f

def MeasurableCalculusInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E),
    MeasurableCalculus C

def MeasurableCalculusExistsInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    MeasurableCalculusExists (S := S) (H := H)

end Spec
end ExpandedFA.Unbounded.MeasurableSpectralCalculus
