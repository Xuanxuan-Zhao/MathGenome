import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.SegmentFTC

/-! Independent specification of d04:03:taylor-integral. The first formula
uses source order k = n+1, so that n ranges over all natural numbers. The
second formula is the degree-(n+1) remainder for C^(n+1) data. The third
is the degree-n remainder for C^(n+1) data, including n=0. All integrals
are coordinatewise proper scalar Riemann integrals, with integrability
asserted as part of the conclusions. -/
noncomputable section
open Set
namespace Specs.D04.C03.TaylorIntegral
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.SegmentFTC.Model
open Specs.D04.C03.HigherInterfaces.Model

def taylor_integralType : Prop :=
  ∀ {d m : ℕ} (n : ℕ) (U : Set (E d)) (f : E d → E m) (a h : E d),
    IsOpen U → CrOn (n+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) →
    ∃ hv : VectorRiemannIntegrable
      (fun t : ℝ => (1-t)^n • differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h) 0 1,
      f (a+h) = taylorPolynomial n f a h + (n.factorial : ℝ)⁻¹ • vectorRiemannIntegral _ hv

def taylor_remainder_integral_subType : Prop :=
  ∀ {d m : ℕ} (n : ℕ) (U : Set (E d)) (f : E d → E m) (a h : E d),
    IsOpen U → CrOn (n+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) →
    ∃ hv : VectorRiemannIntegrable
      (fun t : ℝ => (1-t)^n • differentialDiagonal
        (higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a) h) 0 1,
      taylorRemainder (n+1) f a h = (n.factorial : ℝ)⁻¹ • vectorRiemannIntegral _ hv

def taylor_remainder_integralType : Prop :=
  ∀ {d m : ℕ} (n : ℕ) (U : Set (E d)) (f : E d → E m) (a h : E d),
    IsOpen U → CrOn (n+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) →
    ∃ hv : VectorRiemannIntegrable
      (fun t : ℝ => (1-t)^n • differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h) 0 1,
      taylorRemainder n f a h = (n.factorial : ℝ)⁻¹ • vectorRiemannIntegral _ hv

end Specs.D04.C03.TaylorIntegral
