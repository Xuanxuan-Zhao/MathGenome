import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Canonical truncations and convergence-domain integral. The maximal-domain,
closedness, adjoint and integral identities below are proof obligations, not
fields of an assumed realization of the unbounded calculus. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal

namespace ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
open ExpandedFA.SpectralMeasure
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The cutoff uses the absolute value, allowing arbitrary signed symbols. -/
def truncationSet (f : S → ℝ) (n : ℕ) : Set S := {s | |f s| ≤ (n : ℝ)}

theorem measurableSet_truncationSet {f : S → ℝ} (hf : Measurable f) (n : ℕ) :
    MeasurableSet (truncationSet f n) := measurableSet_le (continuous_abs.measurable.comp hf) measurable_const

/-- Everywhere bounded measurable truncation, without any a.e. quotient. -/
def truncation (f : S → ℝ) (hf : Measurable f) (n : ℕ) : RealBoundedFunction S where
  toFun := (truncationSet f n).indicator f
  measurable := hf.indicator (measurableSet_truncationSet hf n)
  bounded := ⟨n, Nat.cast_nonneg n, fun s => by
    by_cases hs : s ∈ truncationSet f n
    · simpa only [indicator_of_mem hs] using (show |f s| ≤ (n : ℝ) from hs)
    · simp only [indicator_of_notMem hs, abs_zero]; exact Nat.cast_nonneg n⟩

variable {E : RealProjectionValuedMeasure S H}

def truncatedOperator (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) (n : ℕ) : H →L[ℝ] H := C.integral (truncation f hf n)

/-- Convergence is a genuine domain predicate, not a totalized Bochner integral. -/
def convergenceDomain (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : Submodule ℝ H where
  carrier := {x | ∃ y, Tendsto (fun n => truncatedOperator C f hf n x) atTop (𝓝 y)}
  zero_mem' := ⟨0, by simpa using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))⟩
  add_mem' := by
    rintro x z ⟨y, hy⟩ ⟨w, hw⟩
    exact ⟨y + w, by simpa only [map_add] using hy.add hw⟩
  smul_mem' := by
    rintro c x ⟨y, hy⟩
    exact ⟨c • y, by simpa only [map_smul] using hy.const_smul c⟩

/-- The unique norm limit, used only on the actual convergence subspace. -/
def limitLinear (C : RealBoundedRealization E) (f : S → ℝ) (hf : Measurable f) :
    convergenceDomain C f hf →ₗ[ℝ] H where
  toFun x := limUnder atTop (fun n => truncatedOperator C f hf n x)
  map_add' x y := by
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact tendsto_nhds_limUnder (x + y).property
    · simpa only [Submodule.coe_add, map_add] using
        (tendsto_nhds_limUnder x.property).add (tendsto_nhds_limUnder y.property)
  map_smul' c x := by
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact tendsto_nhds_limUnder (c • x).property
    · simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using
        (tendsto_nhds_limUnder x.property).const_smul c

/-- Fixed canonical value; the implementation must identify its domain with
square integrability and establish all the analytic properties. -/
def measurableIntegralValue (C : RealBoundedRealization E) (f : S → ℝ)
    (hf : Measurable f) : Operator ℝ H H :=
  ⟨convergenceDomain C f hf, limitLinear C f hf⟩

/-- Nonnegative extended moment, retaining the infinite case. -/
def squareMoment (C : RealBoundedRealization E) (f : S → ℝ) (x : H) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (|f s| ^ 2) ∂(C.scalar x)

namespace Spec

/-- Independent fixed type and value of the exported norm-limit construction. -/
def MeasurableIntegralType :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {E : RealProjectionValuedMeasure S H}, (C : RealBoundedRealization E) →
    (f : S → ℝ) → Measurable f → Operator ℝ H H

def MeasurableIntegralValueExpected : MeasurableIntegralType.{u, v} :=
  @measurableIntegralValue

/-- All conclusions for a single finite real measurable symbol. This is a
proposition to prove, never an input certificate for the construction. -/
def SymbolLaws (C : RealBoundedRealization E) (f : S → ℝ) (hf : Measurable f) : Prop :=
  let A := measurableIntegralValue C f hf
  (∀ x, x ∈ A.domain ↔ squareMoment C f x < ∞) ∧
  (∀ x, squareMoment C f x < ∞ ↔
    ∃ y, Tendsto (fun n => truncatedOperator C f hf n x) atTop (𝓝 y)) ∧
  (∃ D : Submodule ℝ H, (D : Set H) = {x | squareMoment C f x < ∞}) ∧
  (∀ x : A.domain, Tendsto (fun n => truncatedOperator C f hf n x) atTop (𝓝 (A x))) ∧
  Dense (A.domain : Set H) ∧
  A.IsClosed ∧
  HilbertAdjointSpec.adjointValue A = A ∧
  (OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A =
    OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A)) ∧
  ((OperatorDomainsSpec.productValue (HilbertAdjointSpec.adjointValue A) A).domain =
    (OperatorDomainsSpec.productValue A (HilbertAdjointSpec.adjointValue A)).domain) ∧
  (∀ x : A.domain,
    squareMoment C f x = ENNReal.ofReal (‖A x‖ ^ 2) ∧
    Integrable (fun s => |f s| ^ 2) (C.scalar x) ∧
    ‖A x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂(C.scalar x)) ∧
  (∀ (x : H) (y : A.domain),
    Integrable f (C.coefficient x y).variation ∧
    ⟪x, A y⟫_ℝ = (C.coefficient x y).integral f (ContinuousLinearMap.lsmul ℝ ℝ))

/-- Bounded symbols have the full domain and the given bounded value. -/
def IntegralLawsFor (C : RealBoundedRealization E) : Prop :=
  (∀ (f : S → ℝ) (hf : Measurable f), SymbolLaws C f hf) ∧
  (∀ g : RealBoundedFunction S,
    measurableIntegralValue C g g.measurable = (C.integral g).toLinearMap.toPMap ⊤)

/-- No choice of the given bounded realization is excluded. -/
def EveryRealization : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E), IntegralLawsFor C

/-- A bounded realization and the maximal integral exist for each given PVM;
downstream applications need not assume either unbounded existence or its laws. -/
def RealizationExists : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H), ∃ C : RealBoundedRealization E, IntegralLawsFor C

end Spec
end ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
