import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.DominatedEulerLagrange
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalRegularDomains
import Mathlib.Geometry.Euclidean.Volume.Measure

/-! Independent scope of paper.tex:4306–4335. The coefficients below are the
composed fields A = F_s(x,u,Du) and P = F_Z(x,u,Du). Nothing in the proposition
depends on a choice of their integrand representation. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace ContDiff

namespace VariationalNotes.Sobolev.NaturalBoundary

abbrev RegularDomain {d : ℕ} (Ω : Opens (Domain d)) :=
  Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain (Ω : Set (Domain d))

/-- The usual one-sided C¹ convention: values and first derivatives extend
continuously to the closure. No extension outside the closure is assumed. -/
def C1UpToClosure {d m : ℕ} (Ω : Opens (Domain d))
    (P : Domain d → Gradient m d) : Prop :=
  ContinuousOn P (closure (Ω : Set (Domain d))) ∧
    ∃ L : Domain d → (Domain d →L[ℝ] Gradient m d),
      ContinuousOn L (closure (Ω : Set (Domain d))) ∧
      ∀ x ∈ Ω, HasFDerivAt P (L x) x

/-- Smooth tests on some open neighborhood of the closure, with arbitrary
values outside that neighborhood. Global smoothness is not imposed. -/
def SmoothNearClosure {d m : ℕ} (Ω : Opens (Domain d))
    (φ : Domain d → Vector m) : Prop :=
  ∃ U : Set (Domain d), IsOpen U ∧ closure (Ω : Set (Domain d)) ⊆ U ∧
    ContDiffOn ℝ ∞ φ U

/-- Classical Jacobian, with target coordinate first, as in `testGradient`. -/
def jacobian {d m : ℕ} (φ : Domain d → Vector m) (x : Domain d) : Gradient m d :=
  WithLp.toLp 2 (fun ij => (fderiv ℝ φ x (P102.U4.coordinateVector d ij.2)) ij.1)

/-- Row-wise classical divergence, evaluated only in the open domain. -/
def divergence {d m : ℕ} (P : Domain d → Gradient m d) (x : Domain d) : Vector m :=
  WithLp.toLp 2 (fun i => ∑ j : Fin d,
    fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j))

/-- Matrix action on the geometric outward unit normal. -/
def normalFlux {d m : ℕ} {Ω : Opens (Domain d)} (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d) (x : frontier (Ω : Set (Domain d))) : Vector m :=
  WithLp.toLp 2 (fun i => ∑ j : Fin d, P x (i,j) *
    Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hΩ x j)

def density {d m : ℕ} (A : Domain d → Vector m) (P : Domain d → Gradient m d)
    (φ : Domain d → Vector m) (x : Domain d) : ℝ :=
  ⟪A x, φ x⟫_ℝ + frobenius (P x) (jacobian φ x)

/-- Integrability is explicit, preventing a totalized undefined Bochner
integral from certifying stationarity. -/
def Stationary {d m : ℕ} (Ω : Opens (Domain d))
    (A : Domain d → Vector m) (P : Domain d → Gradient m d) : Prop :=
  ∀ φ : Domain d → Vector m, SmoothNearClosure Ω φ →
    Integrable (density A P φ) (domainMeasure Ω) ∧
      (∫ x, density A P φ x ∂domainMeasure Ω) = 0

/-- For smooth ambient tests, this is their classical zero boundary trace. -/
def ZeroBoundaryValues {d m : ℕ} (Ω : Opens (Domain d))
    (φ : Domain d → Vector m) : Prop :=
  ∀ x ∈ frontier (Ω : Set (Domain d)), φ x = 0

/-- Euclidean-normalized surface measure on the actual boundary, including
counting measure when d = 1. -/
def boundaryMeasure {d : ℕ} (Ω : Opens (Domain d)) :
    Measure (frontier (Ω : Set (Domain d))) :=
  Measure.comap Subtype.val (Measure.euclideanHausdorffMeasure (d - 1))

def boundaryPairing {d m : ℕ} {Ω : Opens (Domain d)} (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d) (φ : Domain d → Vector m) : ℝ :=
  ∫ x, ⟪normalFlux hΩ P x, φ x⟫_ℝ ∂boundaryMeasure Ω

namespace Expected

/-- Complete natural boundary equivalence, under precisely one-sided C¹
regularity. The state derivative needs continuity only in the open domain. -/
def NaturalBoundaryEquivalence : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (hm : 1 ≤ m) (hΩ : RegularDomain Ω)
    (A : Domain d → Vector m) (P : Domain d → Gradient m d),
    ContinuousOn A Ω → C1UpToClosure Ω P →
    (Stationary Ω A P ↔
      (∀ x ∈ Ω, A x = divergence P x) ∧
      ∀ x : frontier (Ω : Set (Domain d)), normalFlux hΩ P x = 0)

/-- Boundary test restrictions detect the continuous normal flux. Continuity
of the geometric normal and positive area of boundary graph neighborhoods
must be established in the proof, not assumed as certificates. -/
def BoundaryDetection : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d), ContinuousOn P (closure (Ω : Set (Domain d))) →
    (∀ φ : Domain d → Vector m, SmoothNearClosure Ω φ →
      Integrable (fun x => ⟪normalFlux hΩ P x, φ x⟫_ℝ) (boundaryMeasure Ω) ∧
        boundaryPairing hΩ P φ = 0) →
    ∀ x : frontier (Ω : Set (Domain d)), normalFlux hΩ P x = 0

/-- The first step of the proposition, with classical divergence. -/
def InteriorEquation : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d))
    (A : Domain d → Vector m) (P : Domain d → Gradient m d),
    ContinuousOn A Ω → C1UpToClosure Ω P → Stationary Ω A P →
    ∀ x ∈ Ω, A x = divergence P x

/-- A zero trace kills the boundary term for every flux. This includes a.e.
zero traces and does not postulate any normal boundary condition. -/
def ZeroTracePairing : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d)
    (t : frontier (Ω : Set (Domain d)) → Vector m),
    t =ᵐ[boundaryMeasure Ω] 0 →
    Integrable (fun x => ⟪normalFlux hΩ P x, t x⟫_ℝ) (boundaryMeasure Ω) ∧
      (∫ x, ⟪normalFlux hΩ P x, t x⟫_ℝ ∂boundaryMeasure Ω) = 0

/-- Smooth tests with prescribed zero boundary values have zero boundary
pairing, without a hypothesis on the flux. -/
def ZeroBoundaryPairing : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d) (φ : Domain d → Vector m),
    ZeroBoundaryValues Ω φ → boundaryPairing hΩ P φ = 0

/-- Identity matrix flux has zero divergence and nonzero normal flux at every
boundary point. Thus the interior equation and zero-trace boundary tests
cannot force the natural boundary condition, even for smooth coefficients. -/
def FixedBoundaryContrast : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω),
    ∃ P : Domain d → Gradient d d,
      ContDiff ℝ ∞ P ∧ C1UpToClosure Ω P ∧
      (∀ x, divergence P x = 0) ∧
      (∀ φ : Domain d → Vector d, ZeroBoundaryValues Ω φ → boundaryPairing hΩ P φ = 0) ∧
      ∀ x : frontier (Ω : Set (Domain d)), normalFlux hΩ P x ≠ 0

end Expected
end VariationalNotes.Sobolev.NaturalBoundary
