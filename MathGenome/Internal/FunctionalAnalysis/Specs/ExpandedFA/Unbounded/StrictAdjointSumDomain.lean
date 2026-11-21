import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MultiplierTranspose
import Mathlib.MeasureTheory.Measure.Count

/-! The example at fa2:p3:adjoint-sum-strict. Counting-measure L² on ℕ is
complex ℓ², with coordinate n corresponding to the manuscript's n+1. In
particular the reciprocal sequence below has entries 1, 1/2, 1/3, ... . -/
noncomputable section
open MeasureTheory
namespace ExpandedFA.Unbounded.StrictAdjointSumDomain
open Multiplication

abbrev H := Lp ℂ 2 (Measure.count : Measure ℕ)
def weight (n : ℕ) : ℂ := (n + 1 : ℕ)
def A : Operator ℂ H H := maximalMultiplier Measure.count 2 weight
def B : Operator ℂ H H := -A
abbrev J := InnerProductSpace.toDual ℂ H

namespace Spec

def Coordinates : Prop :=
  (∀ x : H, x ∈ A.domain ↔ MemLp (fun n => weight n * x n) 2 Measure.count) ∧
  (∀ (x : A.domain) (n : ℕ), A x n = weight n * (x : H) n) ∧
  B.domain = A.domain ∧ ∀ x : B.domain, B x = -A x

def ClosedSelfAdjoint : Prop :=
  Dense (A.domain : Set H) ∧ Dense (B.domain : Set H) ∧
  A.IsClosed ∧ B.IsClosed ∧ IsSelfAdjoint A ∧ IsSelfAdjoint B

def ReciprocalExcluded : Prop :=
  ∃ v : H, (∀ n : ℕ, v n = (weight n)⁻¹) ∧ v ∉ A.domain

def Sum : Prop :=
  (A + B).domain = A.domain ∧ ∀ x : (A + B).domain, (A + B) x = 0

def HilbertDomains : Prop :=
  (HilbertAdjointSpec.adjointValue (A + B)).domain = ⊤ ∧
  (∀ x : (HilbertAdjointSpec.adjointValue (A + B)).domain,
    HilbertAdjointSpec.adjointValue (A + B) x = 0) ∧
  (HilbertAdjointSpec.adjointValue A + HilbertAdjointSpec.adjointValue B).domain =
    A.domain ∧
  (∀ x : (HilbertAdjointSpec.adjointValue A + HilbertAdjointSpec.adjointValue B).domain,
    (HilbertAdjointSpec.adjointValue A + HilbertAdjointSpec.adjointValue B) x = 0) ∧
  (HilbertAdjointSpec.adjointValue A + HilbertAdjointSpec.adjointValue B).domain <
    (HilbertAdjointSpec.adjointValue (A + B)).domain

/-- Exact graph transport through the conjugate-linear Riesz equivalence to
scalar-linear continuous functionals. This is also a domain transport. -/
def RieszTransport : Prop :=
  ∀ (T : Operator ℂ H H), Dense (T.domain : Set H) →
    (∀ y z : H,
      (J y, J z) ∈ (BanachAdjointSpec.adjointValue T).graph ↔
      (y, z) ∈ (HilbertAdjointSpec.adjointValue T).graph) ∧
    (∀ y : H, J y ∈ (BanachAdjointSpec.adjointValue T).domain ↔
      y ∈ (HilbertAdjointSpec.adjointValue T).domain)

def BanachDomains : Prop :=
  (BanachAdjointSpec.adjointValue (A + B)).domain = ⊤ ∧
  (∀ x : (BanachAdjointSpec.adjointValue (A + B)).domain,
    BanachAdjointSpec.adjointValue (A + B) x = 0) ∧
  (∀ y : H, J y ∈ (BanachAdjointSpec.adjointValue A).domain ↔ y ∈ A.domain) ∧
  (∀ y : H, J y ∈ (BanachAdjointSpec.adjointValue B).domain ↔ y ∈ A.domain) ∧
  (∀ x : (BanachAdjointSpec.adjointValue A + BanachAdjointSpec.adjointValue B).domain,
    (BanachAdjointSpec.adjointValue A + BanachAdjointSpec.adjointValue B) x = 0) ∧
  (BanachAdjointSpec.adjointValue A + BanachAdjointSpec.adjointValue B).domain <
    (BanachAdjointSpec.adjointValue (A + B)).domain ∧
  (∃ v : H, (∀ n : ℕ, v n = (weight n)⁻¹) ∧
    J v ∈ (BanachAdjointSpec.adjointValue (A + B)).domain ∧
    J v ∉ (BanachAdjointSpec.adjointValue A + BanachAdjointSpec.adjointValue B).domain)

end Spec
end ExpandedFA.Unbounded.StrictAdjointSumDomain
