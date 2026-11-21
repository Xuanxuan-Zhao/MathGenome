import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Orientation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary

/-! Directed substitution, paper.tex 4343–4375.
The integral on a relatively open parameter domain is the Darboux integral of
its ambient zero extension on a box enclosing its support. The domain itself
need not be bounded or Jordan. At a half-space boundary the derivative is the
unique derivative WITHIN the domain, independently of values outside it.
No integrability or substitution certificate occurs in the hypotheses. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace Specs.D04.C15.DirectedSubstitution
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.PullbackCalculus.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
namespace Model

/-- Proper coefficient integrability, including relative half-space domains. -/
def ProperIntegrable {k : ℕ} {S : Set (E k)} (f : S → ℝ) : Prop :=
  Bornology.IsBounded (support (zeroExtension f)) ∧
    ∃ Q : Box k, Encloses (support (zeroExtension f)) Q ∧
      Integrable (zeroExtension f) Q

/-- The same support-enclosing-box convention as the upstream open integral. -/
def coefficientIntegral {k : ℕ} {S : Set (E k)} (f : S → ℝ) : ℝ := openIntegral f

/-- Pullback defined by the full derivative determined by the relative domain.
For an open domain this agrees with the shared Euclidean pullback. -/
def pullbackWithin {k : ℕ} (S : Set (E k)) (h : E k → E k)
    (η : FormField k k) : FormField k k :=
  fun x => (η (h x)).compLinearMap (fderivWithin ℝ h S x).toLinearMap

end Model
open Model

abbrev ProperIntegrableType := {k : ℕ} → {S : Set (E k)} → (S → ℝ) → Prop
def ProperIntegrableValue : ProperIntegrableType := @Model.ProperIntegrable
abbrev coefficientIntegralType := {k : ℕ} → {S : Set (E k)} → (S → ℝ) → ℝ
def coefficientIntegralValue : coefficientIntegralType := @Model.coefficientIntegral
abbrev pullbackWithinType := {k : ℕ} → Set (E k) → (E k → E k) →
  FormField k k → FormField k k
def pullbackWithinValue : pullbackWithinType := @Model.pullbackWithin

/-- All dimensions, connected open domains; the existential sign also covers
an empty domain. The coefficient represents the actual normalized top form. -/
def directed_openType : Prop :=
  ∀ {k : ℕ} (e : OpenPartialHomeomorph (E k) (E k)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    IsPreconnected e.source →
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ x ∈ e.source, Real.sign ((fderiv ℝ e x).det) = σ) ∧
      ∀ f : e.target → ℝ, Continuous f → HasCompactSupport f →
        let g : e.source → ℝ := fun x =>
          pullback e (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
        OpenIntegrable f ∧ OpenIntegrable g ∧
          coefficientIntegral g = σ * coefficientIntegral f

/-- Each component receives its own sign, even for disconnected overlaps. -/
def directed_open_componentType : Prop :=
  ∀ {k : ℕ} (e : OpenPartialHomeomorph (E k) (E k)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ a ∈ e.source, let C := connectedComponentIn e.source a
    ∀ f : (e '' C) → ℝ, Continuous f → HasCompactSupport f →
      let g : C → ℝ := fun x =>
        pullback e (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
      OpenIntegrable f ∧ OpenIntegrable g ∧
        coefficientIntegral g = Real.sign ((fderiv ℝ e a).det) * coefficientIntegral f

/-- No regularity or support conditions are necessary in dimension zero. -/
def directed_zeroType : Prop :=
  ∀ {U V : Set (E 0)} (e : U ≃ₜ V) (h : E 0 → E 0) (f : V → ℝ),
    (∀ x : U, h x = e x) →
    let g : U → ℝ := fun x =>
      pullback h (fun y => zeroExtension f y • volumeForm 0) x (standardBasis 0)
    (∀ x, (fderiv ℝ h x).det = 1) ∧
    ProperIntegrable f ∧ ProperIntegrable g ∧
    coefficientIntegral f = zeroExtension f 0 ∧
    coefficientIntegral g = zeroExtension g 0 ∧ coefficientIntegral g = coefficientIntegral f

def empty_integralType : Prop :=
  ∀ {k : ℕ} (f : (∅ : Set (E k)) → ℝ),
    ProperIntegrable f ∧ coefficientIntegral f = 0

/-- Existence of the proper Riemann integral up to the genuine flat boundary.
Continuity and compact support are relative to S, not to its interior. -/
def halfspace_integrableType : Prop :=
  ∀ {k : ℕ} (S : Set (E (k+1))),
    (∃ O : Set (E (k+1)), IsOpen O ∧ S = halfSpace (k+1) ∩ O) →
    ∀ f : S → ℝ, Continuous f → HasCompactSupport f → ProperIntegrable f

/-- Connected chart overlap, allowing half-space charts and arbitrary locally
extendible representatives. No ambient differentiability of raw chart functions
at boundary points is assumed. -/
def directed_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → IsPreconnected (chartOverlap c d) →
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ x ∈ chartOverlap c d,
        Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) = σ) ∧
      ∀ f : chartOverlap d c → ℝ, Continuous f → HasCompactSupport f →
        let g : chartOverlap c d → ℝ := fun x =>
          pullbackWithin (chartOverlap c d) (chartTransition c d)
            (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
        ProperIntegrable f ∧ ProperIntegrable g ∧
          coefficientIntegral g = σ * coefficientIntegral f

/-- On disconnected chart overlaps the same conclusion is asserted on every
component and its transition image. The derivative is still the one determined
by the original overlap; restriction does not select an arbitrary extension. -/
def directed_chart_componentType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ a ∈ chartOverlap c d,
    let C := connectedComponentIn (chartOverlap c d) a
    ∀ f : (chartTransition c d '' C) → ℝ, Continuous f → HasCompactSupport f →
      let g : C → ℝ := fun x =>
        pullbackWithin (chartOverlap c d) (chartTransition c d)
          (fun y => zeroExtension f y • volumeForm k) x (standardBasis k)
      (Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) a).det) = 1 ∨
       Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) a).det) = -1) ∧
      (∀ x ∈ C, Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det) =
        Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) a).det)) ∧
      ProperIntegrable f ∧ ProperIntegrable g ∧
        coefficientIntegral g =
          Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) a).det) *
            coefficientIntegral f

end Specs.D04.C15.DirectedSubstitution
