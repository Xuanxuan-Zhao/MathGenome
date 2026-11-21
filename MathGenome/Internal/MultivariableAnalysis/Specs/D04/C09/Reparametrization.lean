import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.LineIntegrals
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution

/-! Reparametrization of the actual interval paths and proper Riemann
integrals of Chapter 9. All endpoint derivatives are within-derivatives.
The inverse and its regularity are part of the parameter-change data. -/
noncomputable section
open Set
namespace Specs.D04.C09.Reparametrization
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
namespace Model

structure ScalarC1Data (h : ℝ → ℝ) (c d : ℝ) where
  partition : SingleVariableAnalysis.Riemann.PartitionData c d
  derivative : Fin partition.n → ℝ → ℝ
  smooth : ∀ i, Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.C1OnInterval
    h (derivative i) (partition.point i.castSucc) (partition.point i.succ)

/-- A continuous piecewise C¹ bijection with piecewise C¹ inverse and
nonvanishing derivatives on each positive-length closed piece. Empty
partitions are allowed on singleton intervals. -/
structure ParameterChange (a b c d : ℝ) where
  source_ordered : c ≤ d
  target_ordered : a ≤ b
  toFun : ℝ → ℝ
  inverse : ℝ → ℝ
  continuousOn : ContinuousOn toFun (Icc c d)
  inverse_continuousOn : ContinuousOn inverse (Icc a b)
  mapsTo : MapsTo toFun (Icc c d) (Icc a b)
  inverse_mapsTo : MapsTo inverse (Icc a b) (Icc c d)
  left_inv : ∀ t ∈ Icc c d, inverse (toFun t) = t
  right_inv : ∀ t ∈ Icc a b, toFun (inverse t) = t
  forward : ScalarC1Data toFun c d
  backward : ScalarC1Data inverse a b
  regular : ∀ i, ∀ t ∈ Icc (forward.partition.point i.castSucc)
    (forward.partition.point i.succ), forward.derivative i t ≠ 0

instance {a b c d} : CoeFun (ParameterChange a b c d) (fun _ => ℝ → ℝ) :=
  ⟨ParameterChange.toFun⟩

def reparametrize {n a b c d} (γ : IntervalPath n a b) (h : ParameterChange a b c d) :
    IntervalPath n c d where
  ordered := h.source_ordered
  toFun := γ ∘ h
  continuousOn := γ.continuousOn.comp h.continuousOn h.mapsTo
end Model
open Model

abbrev ScalarC1DataType := (ℝ → ℝ) → ℝ → ℝ → Type
def ScalarC1DataValue : ScalarC1DataType := Model.ScalarC1Data
abbrev ParameterChangeType := ℝ → ℝ → ℝ → ℝ → Type
def ParameterChangeValue : ParameterChangeType := Model.ParameterChange
abbrev reparametrizeType := {n : ℕ} → {a b c d : ℝ} →
  IntervalPath n a b → ParameterChange a b c d → IntervalPath n c d
def reparametrizeValue : reparametrizeType := @Model.reparametrize

def monotonicityType : Prop := ∀ {a b c d} (h : ParameterChange a b c d),
  StrictMonoOn h (Icc c d) ∨ StrictAntiOn h (Icc c d)

def singleton_iffType : Prop := ∀ {a b c d} (h : ParameterChange a b c d),
  a = b ↔ c = d

def trace_reparametrizeType : Prop := ∀ {n a b c d} (γ : IntervalPath n a b)
  (h : ParameterChange a b c d), trace (reparametrize γ h) = trace γ

def piecewiseC1_reparametrizeType : Prop := ∀ {n a b c d} (γ : IntervalPath n a b)
  (h : ParameterChange a b c d), PiecewiseC1 γ → PiecewiseC1 (reparametrize γ h)

def length_reparametrizeType : Prop := ∀ {n a b c d} (γ : IntervalPath n a b)
  (h : ParameterChange a b c d), length (reparametrize γ h) c d = length γ a b

/-- The integrability assumptions refer to the actual bounded Riemann
integrands on both sets of pieces, and permit discontinuous trace data. -/
def scalar_reparametrizeType : Prop := ∀ {n a b c d} {γ : IntervalPath n a b}
  (h : ParameterChange a b c d) (v : PiecewiseC1Data γ)
  (w : PiecewiseC1Data (reparametrize γ h)) (f : E n → ℝ)
  (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f),
  scalarLineIntegral w f hw = scalarLineIntegral v f hv

def covector_reparametrize_increasingType : Prop := ∀ {n a b c d}
  {γ : IntervalPath n a b} (h : ParameterChange a b c d)
  (hm : StrictMonoOn h (Icc c d)) (v : PiecewiseC1Data γ)
  (w : PiecewiseC1Data (reparametrize γ h)) (α : E n → E n →L[ℝ] ℝ)
  (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α),
  covectorLineIntegral w α hw = covectorLineIntegral v α hv

def covector_reparametrize_decreasingType : Prop := ∀ {n a b c d}
  {γ : IntervalPath n a b} (h : ParameterChange a b c d)
  (hm : StrictAntiOn h (Icc c d)) (v : PiecewiseC1Data γ)
  (w : PiecewiseC1Data (reparametrize γ h)) (α : E n → E n →L[ℝ] ℝ)
  (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α),
  covectorLineIntegral w α hw = -covectorLineIntegral v α hv

/-- Continuous data have the required Riemann integrability automatically. -/
def continuous_reparametrizeType : Prop := ∀ {n a b c d}
  {γ : IntervalPath n a b} (h : ParameterChange a b c d)
  (v : PiecewiseC1Data γ) (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ),
  ContinuousOn f (trace γ) → ContinuousOn α (trace γ) →
  ∃ w : PiecewiseC1Data (reparametrize γ h),
    ∃ hv : ScalarIntegrable v f, ∃ hw : ScalarIntegrable w f,
    ∃ hαv : CovectorIntegrable v α, ∃ hαw : CovectorIntegrable w α,
    scalarLineIntegral w f hw = scalarLineIntegral v f hv ∧
    (StrictMonoOn h (Icc c d) →
      covectorLineIntegral w α hαw = covectorLineIntegral v α hαv) ∧
    (StrictAntiOn h (Icc c d) →
      covectorLineIntegral w α hαw = -covectorLineIntegral v α hαv)

/-- Both source and new parameter integrals vanish on singleton intervals. -/
def degenerate_reparametrizeType : Prop := ∀ {n a c d}
  {γ : IntervalPath n a a} (h : ParameterChange a a c d)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reparametrize γ h))
  (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
  (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f)
  (hαv : CovectorIntegrable v α) (hαw : CovectorIntegrable w α),
  length γ a a = 0 ∧ length (reparametrize γ h) c d = 0 ∧
  scalarLineIntegral v f hv = 0 ∧ scalarLineIntegral w f hw = 0 ∧
  covectorLineIntegral v α hαv = 0 ∧ covectorLineIntegral w α hαw = 0
end Specs.D04.C09.Reparametrization
