import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent specification of Proposition d13:18:norm-independence.

A change of norm is represented by a continuous linear equivalence `e` between
normed realizations of the same real vector space. The second norm of `w` is
`‖e w‖`; the SAME operator in that realization is `e L e⁻¹`. No isometry is
assumed. In finite dimensions every linear equivalence supplies such an `e`.
This includes complex spaces viewed as real spaces, and complex-linear maps
viewed as real-linear maps; their vector and induced operator norms agree.

The general family statement covers arbitrary filters with elapsed time tending
to +∞. The four specializations below use exactly the upstream derivative,
flow and matrix-product families, retaining the actual domains. Both directional
and operator rates preserve all actual extended-real limits, partial values
(including nonexistence), and limsups. Zero vectors are allowed as images.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch18.NormIndependence
open Specs.D13Unified.Ch18.GrowthDefinitions

/-- The same linear operator in the second normed realization. -/
def transportedOperator {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (L : E →L[ℝ] E) :
    F →L[ℝ] F := e.toContinuousLinearMap.comp (L.comp e.symm.toContinuousLinearMap)

/-- Existence and value of limits and partial limits, and equality of limsups. -/
def RateAgreement {ι : Type*} (l : Filter ι) (r s : ι → EReal) : Prop :=
  (∀ z : EReal, Tendsto r l (𝓝 z) ↔ Tendsto s l (𝓝 z)) ∧
  partialLimit l r = partialLimit l s ∧ limsup r l = limsup s l

end D13Unified.Ch18.NormIndependence

namespace Specs.D13Unified.Ch18.NormIndependence
open _root_.D13Unified.Ch18.GrowthDefinitions
open _root_.D13Unified.Ch18.NormIndependence
open Specs.D13Unified.Ch18.GrowthDefinitions
universe u v w q

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Changing norm does not change the derivative being measured. -/
def derivativeTransportStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) (f : E → E) (s : Set E) (x : E),
  IsOpen s → x ∈ s → DifferentiableWithinAt ℝ f s x →
  fderivWithin ℝ (fun y => e (f (e.symm y))) (e '' s) (e x) =
    transportedOperator e (fderivWithin ℝ f s x)

/-- Uniform comparison before division by elapsed time. -/
def normComparisonStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F), ∃ K : ℝ, 1 ≤ K ∧
    (∀ (v w : E), v ≠ 0 →
      (‖e w‖ / ‖e v‖ ≤ K * (‖w‖ / ‖v‖)) ∧
      (‖w‖ / ‖v‖ ≤ K * (‖e w‖ / ‖e v‖))) ∧
    (∀ L : E →L[ℝ] E,
      ‖transportedOperator e L‖ ≤ K * ‖L‖ ∧ ‖L‖ ≤ K * ‖transportedOperator e L‖)

/-- A uniform additive logarithmic error before division by time. -/
def logarithmicComparisonStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F), ∃ B : ℝ, 0 ≤ B ∧
    (∀ (v w : E), v ≠ 0 → w ≠ 0 →
      |Real.log (‖e w‖ / ‖e v‖) - Real.log (‖w‖ / ‖v‖)| ≤ B) ∧
    (∀ L : E →L[ℝ] E, L ≠ 0 →
      |Real.log ‖transportedOperator e L‖ - Real.log ‖L‖| ≤ B)

def operatorFamilyStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) {ι : Type w} (l : Filter ι) [l.NeBot]
    (t : ι → ℝ), Tendsto t l atTop → ∀ (L : ι → E →L[ℝ] E),
    RateAgreement l (fun i => operatorRate (L i) (t i))
      (fun i => operatorRate (transportedOperator e (L i)) (t i))

def familyStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) {ι : Type w} (l : Filter ι) [l.NeBot]
    (t : ι → ℝ), Tendsto t l atTop → ∀ (L : ι → E →L[ℝ] E) (v : E), v ≠ 0 →
    RateAgreement l (fun i => directionalRate (L i) v (t i))
      (fun i => directionalRate (transportedOperator e (L i)) (e v) (t i)) ∧
    RateAgreement l (fun i => operatorRate (L i) (t i))
      (fun i => operatorRate (transportedOperator e (L i)) (t i))

/-- Finite-dimensional norm equivalence is supplied, rather than assumed as a
certificate of agreement of growth rates. -/
def finiteDimensionalStatement : Prop :=
  [FiniteDimensional ℝ E] → [FiniteDimensional ℝ F] →
  ∀ (e : E ≃ₗ[ℝ] F) {ι : Type w} (l : Filter ι) [l.NeBot]
    (t : ι → ℝ), Tendsto t l atTop → ∀ (L : ι → E →L[ℝ] E) (v : E), v ≠ 0 →
    RateAgreement l (fun i => directionalRate (L i) v (t i))
      (fun i => directionalRate (transportedOperator e.toContinuousLinearEquiv (L i)) (e v) (t i)) ∧
    RateAgreement l (fun i => operatorRate (L i) (t i))
      (fun i => operatorRate (transportedOperator e.toContinuousLinearEquiv (L i)) (t i))

def discreteStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) (f : C1SelfMap E) (x : f.domain) (v : E) (hv : v ≠ 0),
  let L := fun n : ℕ => fderivWithin ℝ (f.value^[n+1]) f.domain x
  RateAgreement atTop (fun n => discreteDirectionalRate f x v hv (n+1) (Nat.succ_pos n))
    (fun n => directionalRate (transportedOperator e (L n)) (e v) (n+1)) ∧
  RateAgreement atTop (fun n => operatorRate (L n) (n+1))
    (fun n => operatorRate (transportedOperator e (L n)) (n+1))

def flowStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) (Φ : DifferentiableTimeFamily E) (x v : E) (hv : v ≠ 0)
    (hc : ForwardComplete Φ x),
  let L := fun t : Ioi (0 : ℝ) => fderivWithin ℝ (Φ.value t) {y | ((t : ℝ),y) ∈ Φ.domain} x
  RateAgreement atTop
    (fun t : Ioi (0 : ℝ) => flowDirectionalRate Φ x v hv t t.property (hc t t.property.le))
    (fun t => directionalRate (transportedOperator e (L t)) (e v) t) ∧
  RateAgreement atTop
    (fun t : Ioi (0 : ℝ) => flowOperatorRate Φ x t t.property (hc t t.property.le))
    (fun t => operatorRate (transportedOperator e (L t)) t)

def cocycleStatement : Prop :=
  ∀ (e : E ≃L[ℝ] F) {X : Type q} (T : X → X) (A : X → E →L[ℝ] E)
    (x : X) (v : E) (hv : v ≠ 0),
  RateAgreement atTop (fun n : ℕ => cocycleDirectionalRate T A x v hv (n+1) (Nat.succ_pos n))
    (fun n => cocycleDirectionalRate T (fun y => transportedOperator e (A y)) x (e v)
      (by simpa using hv) (n+1) (Nat.succ_pos n)) ∧
  cocycleDirectionalExponent T A x v hv =
    cocycleDirectionalExponent T (fun y => transportedOperator e (A y)) x (e v) (by simpa using hv) ∧
  cocycleOperatorUpperRate T A x =
    cocycleOperatorUpperRate T (fun y => transportedOperator e (A y)) x

def matrixStatement : Prop :=
  [FiniteDimensional ℝ E] → [FiniteDimensional ℝ F] →
  ∀ (e : E ≃L[ℝ] F) {X : Type q} {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    (T : X → X) (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : E) (hv : v ≠ 0),
  RateAgreement atTop (fun n : ℕ => matrixDirectionalRate b T A x v hv (n+1) (Nat.succ_pos n))
    (fun n => matrixDirectionalRate (b.map e.toLinearEquiv) T A x (e v) (by simpa using hv)
      (n+1) (Nat.succ_pos n)) ∧
  matrixDirectionalExponent b T A x v hv =
    matrixDirectionalExponent (b.map e.toLinearEquiv) T A x (e v) (by simpa using hv) ∧
  matrixOperatorUpperRate b T A x = matrixOperatorUpperRate (b.map e.toLinearEquiv) T A x

/- The bindings below close all space and norm parameters to full Prop types. -/
def normComparisonExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], normComparisonStatement.{u,v} (E := E) (F := F)

def logarithmicComparisonExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], logarithmicComparisonStatement.{u,v} (E := E) (F := F)

def operatorFamilyExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], operatorFamilyStatement.{u,v,w} (E := E) (F := F)

def familyExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], familyStatement.{u,v,w} (E := E) (F := F)

def finiteDimensionalExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], finiteDimensionalStatement.{u,v,w} (E := E) (F := F)

def discreteExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], discreteStatement.{u,v} (E := E) (F := F)

def flowExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], flowStatement.{u,v} (E := E) (F := F)

def cocycleExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], cocycleStatement.{u,v,q} (E := E) (F := F)

def matrixExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], matrixStatement.{u,v,q} (E := E) (F := F)

def derivativeTransportExpected : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F], derivativeTransportStatement.{u,v} (E := E) (F := F)

/-- The complex operator assertion also covers zero-dimensional spaces. -/
def complexOperatorFamilyStatement : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {ι : Type w} (l : Filter ι) [l.NeBot]
    (t : ι → ℝ), Tendsto t l atTop → ∀ (L : ι → E →L[ℂ] E),
    RateAgreement l (fun i => logarithmicRate (t i) ‖L i‖)
      (fun i => logarithmicRate (t i)
        ‖e.toContinuousLinearMap.comp ((L i).comp e.symm.toContinuousLinearMap)‖)

/-- The same assertion for complex-linear operator families. Restricting scalars
preserves both vector norms and the induced operator norm. -/
def complexFamilyStatement : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {ι : Type w} (l : Filter ι) [l.NeBot]
    (t : ι → ℝ), Tendsto t l atTop → ∀ (L : ι → E →L[ℂ] E) (v : E), v ≠ 0 →
    RateAgreement l (fun i => logarithmicRate (t i) (‖L i v‖ / ‖v‖))
      (fun i => logarithmicRate (t i) (‖e (L i v)‖ / ‖e v‖)) ∧
    RateAgreement l (fun i => logarithmicRate (t i) ‖L i‖)
      (fun i => logarithmicRate (t i)
        ‖e.toContinuousLinearMap.comp ((L i).comp e.symm.toContinuousLinearMap)‖)

end Specs.D13Unified.Ch18.NormIndependence
