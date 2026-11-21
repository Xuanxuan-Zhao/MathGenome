import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathsLength
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The two line integrals of paper.tex, d04:09:integrals. Fields are ambient
extensions; only their values on the trace enter any assertion. Integrability
uses the shared proper Riemann integral, including its boundedness condition. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C09.LineIntegrals
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.SingleVariableAnalysis.Ch08.Integral
namespace Model

def PieceIntegrable {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (H : E n → E n → ℝ) : Prop :=
  ∀ i, realIntegrableValue (fun t => H (γ t) (d.velocity i t))
    (d.partition.point i.castSucc) (d.partition.point i.succ)

def pieceIntegral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (H : E n → E n → ℝ) (h : PieceIntegrable d H) : ℝ :=
  ∑ i, realIntegralValue (fun t => H (γ t) (d.velocity i t)) (h i)

def ScalarIntegrable {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (f : E n → ℝ) : Prop := PieceIntegrable d (fun x v => f x * ‖v‖)

def scalarLineIntegral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (f : E n → ℝ) (h : ScalarIntegrable d f) : ℝ :=
  pieceIntegral d (fun x v => f x * ‖v‖) h

def CovectorIntegrable {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (α : E n → E n →L[ℝ] ℝ) : Prop := PieceIntegrable d (fun x v => α x v)

def covectorLineIntegral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (α : E n → E n →L[ℝ] ℝ) (h : CovectorIntegrable d α) : ℝ :=
  pieceIntegral d (fun x v => α x v) h

/-- The Euclidean metric correspondence; the first argument is the field. -/
def workCovector {n} (F : E n → E n) (x : E n) : E n →L[ℝ] ℝ :=
  innerSL ℝ (F x)

def WorkIntegrable {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (F : E n → E n) : Prop := PieceIntegrable d (fun x v => inner ℝ (F x) v)

def workLineIntegral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (F : E n → E n) (h : WorkIntegrable d F) : ℝ :=
  pieceIntegral d (fun x v => inner ℝ (F x) v) h
/-- The coefficients of a covector in the standard dual basis. -/
def covectorVector {n} (α : E n → E n →L[ℝ] ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => α x (standardBasis n i))
end Model
open Model

def scalar_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (f : E n → ℝ), ContinuousOn f (trace γ) → ScalarIntegrable d f

def covector_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ),
  ContinuousOn α (trace γ) → CovectorIntegrable d α

def work_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (F : E n → E n), ContinuousOn F (trace γ) → WorkIntegrable d F

/-- This also gives partition independence for arbitrary bounded Riemann data,
without presupposing continuity of the field. -/
def pieceIntegral_independentType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d e : PiecewiseC1Data γ) (H : E n → E n → ℝ)
  (hd : PieceIntegrable d H) (he : PieceIntegrable e H),
  pieceIntegral d H hd = pieceIntegral e H he

def scalarLineIntegral_independentType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d e : PiecewiseC1Data γ) (f : E n → ℝ)
  (hd : ScalarIntegrable d f) (he : ScalarIntegrable e f),
  scalarLineIntegral d f hd = scalarLineIntegral e f he

def covectorLineIntegral_independentType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d e : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
  (hd : CovectorIntegrable d α) (he : CovectorIntegrable e α),
  covectorLineIntegral d α hd = covectorLineIntegral e α he

def pieceIntegral_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) (h : PieceIntegrable d H),
  pieceIntegral d H h = 0

def workCovector_applyType : Prop := ∀ {n} (F : E n → E n) (x v : E n),
  workCovector F x v = inner ℝ (F x) v

def workCovector_coordinatesType : Prop := ∀ {n} (F : E n → E n) (x v : E n),
  workCovector F x v = ∑ i, F x i * v i

def covector_eq_workType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (F : E n → E n)
  (hc : CovectorIntegrable d (workCovector F)) (hw : WorkIntegrable d F),
  covectorLineIntegral d (workCovector F) hc = workLineIntegral d F hw

def covector_coordinatesType : Prop := ∀ {n} (α : E n → E n →L[ℝ] ℝ) (x v : E n),
  α x v = ∑ i, α x (standardBasis n i) * v i

def workCovector_covectorVectorType : Prop := ∀ {n} (α : E n → E n →L[ℝ] ℝ) (x : E n),
  workCovector (covectorVector α) x = α x

def covectorLineIntegral_eq_coordinatesType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
  (hc : CovectorIntegrable d α) (hw : WorkIntegrable d (covectorVector α)),
  covectorLineIntegral d α hc = workLineIntegral d (covectorVector α) hw

def pieceIntegrable_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (H : E n → E n → ℝ), PieceIntegrable d H

def scalarLineIntegral_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f),
  scalarLineIntegral d f h = 0

def covectorLineIntegral_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ) (h : CovectorIntegrable d α),
  covectorLineIntegral d α h = 0

abbrev PieceIntegrableType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  PiecewiseC1Data γ → (E n → E n → ℝ) → Prop
def PieceIntegrableValue : PieceIntegrableType := @Model.PieceIntegrable
abbrev pieceIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) → (H : E n → E n → ℝ) → PieceIntegrable d H → ℝ
def pieceIntegralValue : pieceIntegralType := @Model.pieceIntegral
abbrev ScalarIntegrableType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  PiecewiseC1Data γ → (E n → ℝ) → Prop
def ScalarIntegrableValue : ScalarIntegrableType := @Model.ScalarIntegrable
abbrev scalarLineIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) → (f : E n → ℝ) → ScalarIntegrable d f → ℝ
def scalarLineIntegralValue : scalarLineIntegralType := @Model.scalarLineIntegral
abbrev CovectorIntegrableType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  PiecewiseC1Data γ → (E n → E n →L[ℝ] ℝ) → Prop
def CovectorIntegrableValue : CovectorIntegrableType := @Model.CovectorIntegrable
abbrev covectorLineIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) → (α : E n → E n →L[ℝ] ℝ) → CovectorIntegrable d α → ℝ
def covectorLineIntegralValue : covectorLineIntegralType := @Model.covectorLineIntegral
abbrev workCovectorType := {n : ℕ} → (E n → E n) → E n → E n →L[ℝ] ℝ
def workCovectorValue : workCovectorType := @Model.workCovector
abbrev WorkIntegrableType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  PiecewiseC1Data γ → (E n → E n) → Prop
def WorkIntegrableValue : WorkIntegrableType := @Model.WorkIntegrable
abbrev workLineIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) → (F : E n → E n) → WorkIntegrable d F → ℝ
def workLineIntegralValue : workLineIntegralType := @Model.workLineIntegral
abbrev covectorVectorType := {n : ℕ} → (E n → E n →L[ℝ] ℝ) → E n → E n
def covectorVectorValue : covectorVectorType := @Model.covectorVector

end Specs.D04.C09.LineIntegrals
