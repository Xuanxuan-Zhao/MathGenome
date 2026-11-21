import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Convex.Star

/-! The radial operator in every positive degree, indexed as `k + 1`.
Integration is the shared scalar Riemann integral over the closed unit interval
in E₁, with its ordinary coordinate. No compactness condition on U is imposed. -/
noncomputable section
open scoped BigOperators Classical
open Set
namespace Specs.D04.C13.HomotopyOperatorRegularity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

def unitInterval : Set (E 1) := {t | t 0 ∈ Icc (0 : ℝ) 1}

def scalarIntegral (f : ℝ → ℝ) : ℝ :=
  regionIntegral (fun t : unitInterval => f (t.val 0))

def ScalarIntegrable (f : ℝ → ℝ) : Prop :=
  RegionIntegrable (fun t : unitInterval => f (t.val 0))

def IsContinuousForm {n k : ℕ} (U : Set (E n)) (ω : FormField n k) : Prop :=
  ∀ I : MultiIndex n k, ContinuousOn (fun x => coefficient (standardBasis n) (ω x) I) U

def radialPoint {n : ℕ} (a x : E n) (t : ℝ) : E n := a + t • (x - a)

def homotopyIntegrand {n k : ℕ} (a : E n) (ω : FormField n (k+1))
    (x : E n) (v : Fin k → E n) (t : ℝ) : ℝ :=
  t ^ k * ω (radialPoint a x t) (Fin.cons (x-a) v)

/-- Reconstruction from the integrals of the coefficients of the contraction.
Its agreement with integration on arbitrary vectors is a theorem. -/
def homotopyOperator {n k : ℕ} (a : E n) (ω : FormField n (k+1)) : FormField n k :=
  fun x => ∑ I : MultiIndex n k,
    scalarIntegral (homotopyIntegrand a ω x (fun j => standardBasis n (indexTuple I j))) •
      dx (standardBasis n) I
end Model
open Model

abbrev unitIntervalType := Set (E 1)
def unitIntervalValue : unitIntervalType := Model.unitInterval
abbrev scalarIntegralType := (ℝ → ℝ) → ℝ
def scalarIntegralValue : scalarIntegralType := Model.scalarIntegral
abbrev ScalarIntegrableType := (ℝ → ℝ) → Prop
def ScalarIntegrableValue : ScalarIntegrableType := Model.ScalarIntegrable
abbrev IsContinuousFormType := {n k : ℕ} → Set (E n) → FormField n k → Prop
def IsContinuousFormValue : IsContinuousFormType := @Model.IsContinuousForm
abbrev radialPointType := {n : ℕ} → E n → E n → ℝ → E n
def radialPointValue : radialPointType := @Model.radialPoint
abbrev homotopyIntegrandType := {n k : ℕ} → E n → FormField n (k+1) →
  E n → (Fin k → E n) → ℝ → ℝ
def homotopyIntegrandValue : homotopyIntegrandType := @Model.homotopyIntegrand
abbrev homotopyOperatorType := {n k : ℕ} → E n → FormField n (k+1) → FormField n k
def homotopyOperatorValue : homotopyOperatorType := @Model.homotopyOperator

def homotopy_integrableType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsContinuousForm U ω →
    ∀ x ∈ U, ∀ v : Fin k → E n, ScalarIntegrable (homotopyIntegrand a ω x v)

def homotopy_applyType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsContinuousForm U ω →
    ∀ x ∈ U, ∀ v : Fin k → E n,
      homotopyOperator a ω x v = scalarIntegral (homotopyIntegrand a ω x v)

def homotopy_continuousType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsContinuousForm U ω →
    IsContinuousForm U (homotopyOperator a ω)

def homotopy_isCrType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)) (r : Option ℕ),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsCrForm r U ω →
    IsCrForm r U (homotopyOperator a ω)
def homotopy_zeroType : Prop :=
  ∀ {n k : ℕ} (a : E n), homotopyOperator a (0 : FormField n (k+1)) = 0

def homotopy_above_dimensionType : Prop :=
  ∀ {n k : ℕ} (a : E n) (ω : FormField n (k+1)),
    n < k+1 → homotopyOperator a ω = 0

end Specs.D04.C13.HomotopyOperatorRegularity
