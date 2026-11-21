import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SubdivisionUniformVector
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! Independent statements for paper.tex, d04:09:paths and d04:09:length.
Paths are represented by ambient functions restricted to their stated interval.
No assertion concerns values outside that interval. The scalar partitions and
Riemann integral are exactly the shared D03/F3 representations. -/
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace Specs.D04.C09.PathsLength
open Specs.D04.C01.EuclideanInterfaces.Model
open SingleVariableAnalysis.Riemann
open Specs.SingleVariableAnalysis.Ch08.Integral
namespace Model

structure IntervalPath (n : ℕ) (a b : ℝ) where
  ordered : a ≤ b
  toFun : ℝ → E n
  continuousOn : ContinuousOn toFun (Icc a b)

instance {n a b} : CoeFun (IntervalPath n a b) (fun _ => ℝ → E n) := ⟨IntervalPath.toFun⟩

def trace {n a b} (γ : IntervalPath n a b) : Set (E n) := γ '' Icc a b

def SimpleArc {n a b} (γ : IntervalPath n a b) : Prop := Set.InjOn γ (Icc a b)

def SimpleClosed {n a b} (γ : IntervalPath n a b) : Prop :=
  γ a = γ b ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    γ s = γ t → s = t ∨ (s = a ∧ t = b) ∨ (s = b ∧ t = a)

/-- A continuous derivative on the closed piece, including the one-sided
endpoint derivatives. Only positive-length pieces occur in join partitions. -/
def C1Piece {n} (γ v : ℝ → E n) (a b : ℝ) : Prop :=
  ContinuousOn v (Icc a b) ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t

structure PiecewiseC1Data {n a b} (γ : IntervalPath n a b) where
  partition : PartitionData a b
  velocity : Fin partition.n → ℝ → E n
  smooth : ∀ i, C1Piece γ (velocity i)
    (partition.point i.castSucc) (partition.point i.succ)

def PiecewiseC1 {n a b} (γ : IntervalPath n a b) : Prop := Nonempty (PiecewiseC1Data γ)

def PiecewiseRegular {n a b} (γ : IntervalPath n a b) : Prop :=
  ∃ d : PiecewiseC1Data γ, ∀ i, ∀ t ∈ Icc (d.partition.point i.castSucc)
    (d.partition.point i.succ), d.velocity i t ≠ 0

def polygonalLength {n} (γ : ℝ → E n) {a b} (P : PartitionData a b) : ℝ :=
  ∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖

/-- Length in the extended nonnegative reals: no default value at an
unbounded family of polygonal sums. -/
def length {n} (γ : ℝ → E n) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ P : PartitionData a b, ENNReal.ofReal (polygonalLength γ P)

def piecewiseSpeedIntegral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)) : ℝ :=
  ∑ i, realIntegralValue (fun t => ‖d.velocity i t‖) (h i)
end Model
open Model

abbrev IntervalPathType := ℕ → ℝ → ℝ → Type
def IntervalPathValue : IntervalPathType := Model.IntervalPath
abbrev traceType := {n : ℕ} → {a b : ℝ} → IntervalPath n a b → Set (E n)
def traceValue : traceType := @Model.trace
abbrev SimpleArcType := {n : ℕ} → {a b : ℝ} → IntervalPath n a b → Prop
def SimpleArcValue : SimpleArcType := @Model.SimpleArc
def SimpleClosedType := SimpleArcType
def SimpleClosedValue : SimpleClosedType := @Model.SimpleClosed
abbrev C1PieceType := {n : ℕ} → (ℝ → E n) → (ℝ → E n) → ℝ → ℝ → Prop
def C1PieceValue : C1PieceType := @Model.C1Piece
abbrev PiecewiseC1DataType := {n : ℕ} → {a b : ℝ} → IntervalPath n a b → Type
def PiecewiseC1DataValue : PiecewiseC1DataType := @Model.PiecewiseC1Data
def PiecewiseC1Type := SimpleArcType
def PiecewiseC1Value : PiecewiseC1Type := @Model.PiecewiseC1
def PiecewiseRegularType := SimpleArcType
def PiecewiseRegularValue : PiecewiseRegularType := @Model.PiecewiseRegular
abbrev polygonalLengthType := {n : ℕ} → (ℝ → E n) → {a b : ℝ} → PartitionData a b → ℝ
def polygonalLengthValue : polygonalLengthType := @Model.polygonalLength
abbrev lengthType := {n : ℕ} → (ℝ → E n) → ℝ → ℝ → ℝ≥0∞
def lengthValue : lengthType := @Model.length
abbrev piecewiseSpeedIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) →
  (∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ)) → ℝ
def piecewiseSpeedIntegralValue : piecewiseSpeedIntegralType := @Model.piecewiseSpeedIntegral

def polygonalLength_refinementType : Prop := ∀ {n} (γ : ℝ → E n) {a b}
  (P R : PartitionData a b), Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue R P →
    polygonalLength γ P ≤ polygonalLength γ R

def length_eq_variationType : Prop := ∀ {n} (γ : ℝ → E n) {a b}, a ≤ b →
  length γ a b = eVariationOn γ (Icc a b)

def length_addType : Prop := ∀ {n} (γ : ℝ → E n) {a c b}, a ≤ c → c ≤ b →
  length γ a b = length γ a c + length γ c b

def polygonalLength_degenerateType : Prop := ∀ {n} (γ : ℝ → E n) (a : ℝ)
  (P : PartitionData a a), polygonalLength γ P = 0

def length_degenerateType : Prop := ∀ {n} (γ : ℝ → E n) (a : ℝ), length γ a a = 0

def length_constantType : Prop := ∀ {n} (x : E n) (a b : ℝ), length (fun _ => x) a b = 0

def length_zero_dimensionType : Prop := ∀ (γ : ℝ → E 0) (a b : ℝ), length γ a b = 0

def constant_piecewiseC1Type : Prop := ∀ {n a b} (γ : IntervalPath n a b) (x : E n),
  (∀ t ∈ Icc a b, γ t = x) → PiecewiseC1 γ

def constant_not_regularType : Prop := ∀ {n a b} (γ : IntervalPath n a b) (x : E n),
  a < b → (∀ t ∈ Icc a b, γ t = x) → ¬ PiecewiseRegular γ

def speed_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ), ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ)

def length_speed_integralType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ)),
  length γ a b = ENNReal.ofReal (piecewiseSpeedIntegral d h) ∧ length γ a b < ∞

/-- Uniform mesh statement, over every partition containing the joins. -/
def polygonalLength_mesh_limitType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ)),
  ∀ ε > 0, ∃ δ > 0, ∀ P : PartitionData a b,
    Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue P d.partition →
    Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P < δ →
    |polygonalLength γ P - piecewiseSpeedIntegral d h| < ε
def piecewiseC1_finiteType : Prop := ∀ {n a b} (γ : IntervalPath n a b),
  PiecewiseC1 γ → length γ a b < ∞

def piecewiseSpeedIntegral_degenerateType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ)),
  piecewiseSpeedIntegral d h = 0

end Specs.D04.C09.PathsLength
