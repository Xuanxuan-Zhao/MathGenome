import MathGenome.Internal.LinearPDE.P201Specs.Heat.FormOperator
import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus

noncomputable section
open scoped InnerProductSpace ComplexConjugate NNReal
universe u v
namespace P201.Heat.FormDomainExpected
open ExpandedFA ExpandedFA.Unbounded
open ClosedNonnegativeForms

/-- The second representation identity. All hypotheses concern the original
closed form and a self-adjoint square root of its canonical operator.
In particular the domain identity is a conclusion, never input data. -/
def RootIdentification : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (q : NonnegativeForm 𝕜 H), q.IsClosed →
    ∀ S : Operator 𝕜 H H, Dense (S.domain : Set H) → S.adjoint = S →
    OperatorDomainsSpec.productValue S S = q.associatedOperator →
    S.domain = q.domain ∧
    ∀ (x : q.domain) (hx : (x : H) ∈ S.domain),
      RCLike.re (q.form x x) = ‖S ⟨x, hx⟩‖ ^ 2

/-- Complete real associated-operator theorem. The spectral calculus is an
existential conclusion and its coordinate integral is the upstream operator. -/
def RealTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : CoerciveForm V H),
    FormOperatorExpected.Representation d ∧
    ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
      C.integral RealNonnegativeSpectralCalculus.coordinate = d.operator ∧
      (RealNonnegativeSpectralCalculus.squareRoot C).domain =
        LinearMap.range d.j.toLinearMap ∧
      ∀ (v : V) (hv : d.j v ∈ (RealNonnegativeSpectralCalculus.squareRoot C).domain),
        d.a v v = ‖RealNonnegativeSpectralCalculus.squareRoot C ⟨d.j v, hv⟩‖ ^ 2


/-- The actual complex spectral symbols on the nonnegative half-line. -/
def complexCoordinate (s : ℝ≥0) : ℂ := (s : ℝ)
def complexRoot (s : ℝ≥0) : ℂ := Real.sqrt (s : ℝ)

/-- General complex closed-form version, for arbitrary Hermitian forms. -/
def ComplexClosedTheorem : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (q : NonnegativeForm ℂ H), q.IsClosed →
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C complexCoordinate = q.associatedOperator ∧
      (MeasurableSpectralCalculus.measurableIntegral C complexRoot).domain = q.domain ∧
      ∀ (x : q.domain)
        (hx : (x : H) ∈ (MeasurableSpectralCalculus.measurableIntegral C complexRoot).domain),
        (q.form x x).re =
          ‖MeasurableSpectralCalculus.measurableIntegral C complexRoot ⟨x, hx⟩‖ ^ 2

/-- The complex Dirichlet clause, stated on every open set (hence in particular
on every nonempty bounded Lipschitz domain in positive dimension). The form is
an arbitrary bounded linear-first Hermitian coercive form, not a coefficient form.
The exact graph explicitly fixes the same associated operator as E10. -/
def ComplexDirichletTheorem : Prop :=
  ∀ {n : ℕ} (Ω : P201Specs.Domain n)
    (a : P201Specs.H10 ℂ Ω →L[ℂ] P201Specs.H10 ℂ Ω →L⋆[ℂ] ℂ),
    (∀ v w, conj (a v w) = a w v) →
    (∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ (a v v).re) →
    ∃ b : P201.Elliptic.DenseForm ℂ (P201Specs.Lp ℂ Ω 2),
      (∀ x h, (x, h) ∈ b.associatedOperator.graph ↔
        ∃ v : P201Specs.H10 ℂ Ω, P201Specs.hZeroUnderlying Ω v = x ∧
          ∀ w, a v w = inner ℂ (P201Specs.hZeroUnderlying Ω w) h) ∧
      Dense (b.associatedOperator.domain : Set (P201Specs.Lp ℂ Ω 2)) ∧
      b.associatedOperator.adjoint = b.associatedOperator ∧
      (∀ x : b.associatedOperator.domain,
        0 ≤ (inner ℂ (x : P201Specs.Lp ℂ Ω 2) (b.associatedOperator x)).re) ∧
      ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 (P201Specs.Lp ℂ Ω 2))
        (C : MeasurableSpectralCalculus.BoundedRealization E),
        MeasurableSpectralCalculus.measurableIntegral C complexCoordinate = b.associatedOperator ∧
        (MeasurableSpectralCalculus.measurableIntegral C complexRoot).domain =
          LinearMap.range (P201Specs.hZeroUnderlying (𝕜 := ℂ) Ω).toLinearMap ∧
        ∀ (v : P201Specs.H10 ℂ Ω)
          (hv : P201Specs.hZeroUnderlying Ω v ∈
            (MeasurableSpectralCalculus.measurableIntegral C complexRoot).domain),
          a v v = (‖MeasurableSpectralCalculus.measurableIntegral C complexRoot
            ⟨P201Specs.hZeroUnderlying Ω v, hv⟩‖ ^ 2 : ℝ)

end P201.Heat.FormDomainExpected
