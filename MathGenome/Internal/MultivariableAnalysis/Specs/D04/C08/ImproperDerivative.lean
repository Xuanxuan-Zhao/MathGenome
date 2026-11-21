import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.UniformTailsContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.UniformC1Limit
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces

/-! `d04:08:improper-derivative`. The proper differentiation conclusions are
hypotheses here: the truncated integrals are C¹ on neighborhoods of the ball,
and their total derivatives are the proper operator integrals. This formulation
retains the signed, fixed-exhaustion theorem. Domination is a separate sufficient
condition, and finite iteration has explicit hypotheses at every order. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C08.ImproperDerivative
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model
open Specs.D04.C06.AbsoluteConvergence.Model
open Specs.D04.C08.ProperDerivative.Model
open Specs.D04.C08.UniformTailsContinuity.Model

/-- Uniform convergence, continuous total derivative, and the directional
integral formula for the canonical limit along K. Radius zero is allowed. -/
def improper_derivativeType : Prop :=
  ∀ {n m k : ℕ} {Ω : Set (E n)} {P : Set (E m)} {K : ℕ → Set (E n)}
    (f : E n → E m → E k) (p₀ : E m) (r : ℝ),
    IsOpen Ω → RegularExhaustion Ω K → IsOpen P → 0 ≤ r →
    Metric.closedBall p₀ r ⊆ P →
    (∀ p ∈ P, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
    (∀ j, ∃ U, IsOpen U ∧ Metric.closedBall p₀ r ⊆ U ∧
      CrOn 1 U (truncatedIntegral K f j)) →
    (∀ j p, p ∈ Metric.closedBall p₀ r →
      OperatorRegionIntegrable (fun x : K j => totalDerivative (f x) p)) →
    (∀ j p, p ∈ Metric.closedBall p₀ r →
      totalDerivative (truncatedIntegral K f j) p =
        operatorRegionIntegral (fun x : K j => totalDerivative (f x) p)) →
    (∃ a, Tendsto (fun j => truncatedIntegral K f j p₀) atTop (𝓝 a)) →
    ∀ G : E m → E m →L[ℝ] E k,
    TendstoUniformlyOn
      (fun j p => operatorRegionIntegral (fun x : K j => totalDerivative (f x) p))
      G atTop (Metric.closedBall p₀ r) →
    let F := fun p => exhaustionIntegral K (fun x => f x p)
    TendstoUniformlyOn (truncatedIntegral K f) F atTop (Metric.closedBall p₀ r) ∧
    ContinuousOn G (Metric.closedBall p₀ r) ∧
    CrOn 1 (interior (Metric.closedBall p₀ r)) F ∧
    ∀ p ∈ interior (Metric.closedBall p₀ r),
      HasFDerivAt F (G p) p ∧ totalDerivative F p = G p ∧
      ∀ h, Tendsto
        (fun j => vectorRegionIntegral (fun x : K j => totalDerivative (f x) p h))
        atTop (𝓝 (totalDerivative F p h))

/-- Operator-norm domination implies uniform Cauchy convergence of the actual
operator integrals. Integrability is required on the prescribed truncations. -/
def domination_derivative_tailsType : Prop :=
  ∀ {n m k : ℕ} {Ω : Set (E n)} {K : ℕ → Set (E n)} {B : Set (E m)}
    (A : E n → E m → E m →L[ℝ] E k),
    IsOpen Ω → RegularExhaustion Ω K →
    (∀ j p, p ∈ B → OperatorRegionIntegrable (fun x : K j => A x p)) →
    ∀ {M : E n → ℝ}, AbsolutelyConvergent Ω M → (∀ x ∈ Ω, 0 ≤ M x) →
    (∀ p ∈ B, ∀ x ∈ Ω, ‖A x p‖ ≤ M x) →
    UniformCauchySeqOn
      (fun j p => operatorRegionIntegral (fun x : K j => A x p)) atTop B ∧
    ∃ G : E m → E m →L[ℝ] E k,
      TendstoUniformlyOn (fun j p => operatorRegionIntegral (fun x : K j => A x p))
        G atTop B

/-- Finite iteration. At order q the truncated q-th derivatives are C¹ near B,
their next derivatives have uniform Cauchy tails, and their base-point values
converge. The displayed proper-integral identities identify the tensors with
integrals of the parameter derivatives; no infinite-order assertion is made. -/
def finite_improper_derivativesType : Prop :=
  ∀ {n m k : ℕ} {Ω : Set (E n)} {P : Set (E m)} {K : ℕ → Set (E n)}
    (f : E n → E m → E k) (p₀ : E m) (r : ℝ) (s : ℕ),
    IsOpen Ω → RegularExhaustion Ω K → IsOpen P → 0 ≤ r →
    Metric.closedBall p₀ r ⊆ P →
    (∀ q ≤ s, ∀ j, ∃ U, IsOpen U ∧ Metric.closedBall p₀ r ⊆ U ∧
      CrOn 1 U (higherDifferential q (truncatedIntegral K f j))) →
    (∀ q ≤ s, UniformCauchySeqOn
      (fun j => totalDerivative (higherDifferential q (truncatedIntegral K f j)))
      atTop (Metric.closedBall p₀ r)) →
    (∀ q ≤ s, ∃ a, Tendsto
      (fun j => higherDifferential q (truncatedIntegral K f j) p₀) atTop (𝓝 a)) →
    (∀ q ≤ s + 1, ∀ j p, p ∈ Metric.closedBall p₀ r → ∀ v : Fin q → E m,
      VectorRegionIntegrable (fun x : K j => higherDifferential q (f x) p v) ∧
      higherDifferential q (truncatedIntegral K f j) p v =
        vectorRegionIntegral (fun x : K j => higherDifferential q (f x) p v)) →
    let F := fun p => exhaustionIntegral K (fun x => f x p)
    TendstoUniformlyOn (truncatedIntegral K f) F atTop (Metric.closedBall p₀ r) ∧
    CrOn (s + 1) (interior (Metric.closedBall p₀ r)) F ∧
    ∀ q ≤ s + 1,
      (∃ H : E m → Differential (E m) (E k) q,
        TendstoUniformlyOn (fun j => higherDifferential q (truncatedIntegral K f j))
          H atTop (Metric.closedBall p₀ r) ∧
        EqOn (higherDifferential q F) H (interior (Metric.closedBall p₀ r))) ∧
      ∀ p ∈ interior (Metric.closedBall p₀ r), ∀ v : Fin q → E m,
        Tendsto (fun j => vectorRegionIntegral
          (fun x : K j => higherDifferential q (f x) p v))
          atTop (𝓝 (higherDifferential q F p v))

/-- Absolute convergence adds independence of the exhaustion; it is not needed
in the signed differentiation theorem. -/
def absolute_exhaustion_independenceType : Prop :=
  ∀ {n m k : ℕ} {Ω : Set (E n)} {K L : ℕ → Set (E n)}
    (f : E n → E m → E k) (B : Set (E m)), IsOpen Ω →
    RegularExhaustion Ω K → RegularExhaustion Ω L →
    (∀ p ∈ B, VectorAbsolutelyConvergent Ω (fun x => f x p)) →
    ∀ p ∈ B, exhaustionIntegral K (fun x => f x p) =
      vectorImproperIntegral Ω (fun x => f x p) ∧
      exhaustionIntegral K (fun x => f x p) = exhaustionIntegral L (fun x => f x p)
end Specs.D04.C08.ImproperDerivative
