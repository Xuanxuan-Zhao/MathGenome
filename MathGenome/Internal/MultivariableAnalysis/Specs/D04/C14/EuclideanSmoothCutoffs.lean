import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statements for the explicit Euclidean cutoff construction.
Support means topological support (the closure of the nonzero set).
No positivity assumption on the dimension or nonemptiness of K is imposed. -/
noncomputable section
open Set
open scoped Topology BigOperators ContDiff
namespace Specs.D04.C14.EuclideanSmoothCutoffs
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
namespace Model

def cutoffSeed (t : ℝ) : ℝ := if 0 < t then Real.exp (-1 / t) else 0

def cutoffStep (t : ℝ) : ℝ := cutoffSeed t / (cutoffSeed t + cutoffSeed (1 - t))

def radialCutoff {n : ℕ} (p : E n) (r R : ℝ) (x : E n) : ℝ :=
  cutoffStep ((R ^ 2 - ‖x - p‖ ^ 2) / (R ^ 2 - r ^ 2))

def finiteCutoff {n : ℕ} {ι : Type} (I : Finset ι) (p : ι → E n)
    (r R : ι → ℝ) (x : E n) : ℝ :=
  1 - ∏ i ∈ I, (1 - radialCutoff (p i) (r i) (R i) x)

/-- A real-valued map with range in [0,1] represents the requested map into that interval. -/
def CutoffFor {n : ℕ} (K O : Set (E n)) (χ : E n → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ SmoothOn Set.univ χ ∧
  (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
  (∃ V, IsOpen V ∧ K ⊆ V ∧ EqOn χ (fun _ => 1) V) ∧
  IsCompact (tsupport χ) ∧ tsupport χ ⊆ O
end Model

abbrev cutoffSeedType := ℝ → ℝ
def cutoffSeedValue : cutoffSeedType := Model.cutoffSeed
abbrev cutoffStepType := ℝ → ℝ
def cutoffStepValue : cutoffStepType := Model.cutoffStep
abbrev radialCutoffType := {n : ℕ} → E n → ℝ → ℝ → E n → ℝ
def radialCutoffValue : radialCutoffType := @Model.radialCutoff
abbrev finiteCutoffType := {n : ℕ} → {ι : Type} → Finset ι →
  (ι → E n) → (ι → ℝ) → (ι → ℝ) → E n → ℝ
def finiteCutoffValue : finiteCutoffType := @Model.finiteCutoff

def cutoffSeed_propertiesType : Prop :=
  ContDiff ℝ ∞ Model.cutoffSeed ∧ HasDerivAt Model.cutoffSeed 0 0 ∧
  (∀ t, 0 ≤ Model.cutoffSeed t) ∧
  (∀ t, t ≤ 0 → Model.cutoffSeed t = 0) ∧
  (∀ t, 0 < t → 0 < Model.cutoffSeed t)

def cutoffStep_propertiesType : Prop :=
  ContDiff ℝ ∞ Model.cutoffStep ∧
  (∀ t, 0 < Model.cutoffSeed t + Model.cutoffSeed (1 - t)) ∧
  (∀ t, Model.cutoffStep t ∈ Icc (0 : ℝ) 1) ∧
  (∀ t, t ≤ 0 → Model.cutoffStep t = 0) ∧
  (∀ t, 1 ≤ t → Model.cutoffStep t = 1)

def radialCutoff_propertiesType : Prop :=
  ∀ {n : ℕ} (p : E n) (r R : ℝ), 0 < r → r < R →
    ContDiff ℝ ∞ (Model.radialCutoff p r R) ∧
    (∀ x, Model.radialCutoff p r R x ∈ Icc (0 : ℝ) 1) ∧
    EqOn (Model.radialCutoff p r R) (fun _ => 1) (Metric.closedBall p r) ∧
    (∀ x, x ∉ Metric.ball p R → Model.radialCutoff p r R x = 0) ∧
    tsupport (Model.radialCutoff p r R) ⊆ Metric.closedBall p R ∧
    IsCompact (tsupport (Model.radialCutoff p r R))

def finiteCutoff_propertiesType : Prop :=
  ∀ {n : ℕ} {ι : Type} (I : Finset ι) (p : ι → E n) (r R : ι → ℝ)
    (K O : Set (E n)),
    (∀ i ∈ I, 0 < r i ∧ r i < R i) →
    (∀ i ∈ I, Metric.closedBall (p i) (R i) ⊆ O) →
    K ⊆ ⋃ i ∈ I, Metric.ball (p i) (r i) →
    Model.CutoffFor K O (Model.finiteCutoff I p r R)

def exists_smooth_cutoffType : Prop :=
  ∀ {n : ℕ} (K O : Set (E n)), IsCompact K → IsOpen O → K ⊆ O →
    ∃ χ : E n → ℝ, Model.CutoffFor K O χ

def exists_euclidean_smooth_cutoffType : Prop :=
  ∀ {n : ℕ} (K O : Set (E n)), Compact K → Open O → K ⊆ O →
    ∃ χ : E n → ℝ, Model.CutoffFor K O χ
end Specs.D04.C14.EuclideanSmoothCutoffs
