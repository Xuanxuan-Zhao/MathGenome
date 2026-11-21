import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.ComplexGreenBridge

/-! The raw finite-curve boundary-display obligation, supporting
paper.tex:2674–2678. The input consists of ordinary regular curves and local
continuous inverses on the actual frontier, with no D04 chart or flux certificate. -/
noncomputable section
set_option linter.unusedVariables false
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace D12Complex.ParametrizedBoundaryDisplay
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

/-- The permitted ordinary local regular extension condition. The total function
κ restricts to the continuous inverse from the actual relative frontier onto
an open real interval. In particular the image is exactly `frontier V ∩ W`. -/
def LocalRegularExtension (V : Set ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∃ (δ : ℝ) (W : Set ℂ) (η : ℝ → ℂ) (κ : ℂ → ℝ),
    0 < δ ∧ IsOpen W ∧ γ t ∈ W ∧
    ContDiffOn ℝ 1 η (Ioo (t - δ) (t + δ)) ∧
    (∀ s ∈ Ioo (t - δ) (t + δ), deriv η s ≠ 0) ∧
    EqOn η γ (Icc a b ∩ Ioo (t - δ) (t + δ)) ∧
    MapsTo η (Ioo (t - δ) (t + δ)) (frontier V ∩ W) ∧
    MapsTo κ (frontier V ∩ W) (Ioo (t - δ) (t + δ)) ∧
    (∀ s ∈ Ioo (t - δ) (t + δ), κ (η s) = s) ∧
    (∀ z ∈ frontier V ∩ W, η (κ z) = z) ∧
    ContinuousOn κ (frontier V ∩ W)

/-- All supplied raw curve hypotheses; the global curves need be regular only
on the supplied open parameter neighborhoods. No orientation is prescribed. -/
structure RegularBoundaryCurves (V : Set ℂ) (m : ℕ)
    (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) (T : Fin m → Set ℝ) : Prop where
  ordered : ∀ i, a i < b i
  params_open : ∀ i, IsOpen (T i)
  params_contain : ∀ i, Icc (a i) (b i) ⊆ T i
  regular : ∀ i, ContDiffOn ℝ 1 (γ i) (T i)
  nonzero : ∀ i t, t ∈ Icc (a i) (b i) → deriv (γ i) t ≠ 0
  cover : frontier V = ⋃ i, γ i '' Icc (a i) (b i)
  injective : ∀ i, InjOn (γ i) (Ioo (a i) (b i))
  disjoint : ∀ i j, i ≠ j → Disjoint (γ i '' Ioo (a i) (b i)) (γ j '' Ioo (a j) (b j))
  local_extension : ∀ i, LocalRegularExtension V (γ i) (a i) (b i)

/-- The full actual unit-normal frame needed by the scalar bridge. -/
def PatchFrame {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (P : Patch 1 U) (s : PointSign) : Prop :=
  ∀ x ∈ P.region,
    ‖patchNormal hD P x‖ = 1 ∧
    (∀ i, inner ℝ (patchNormal hD P x)
      (fderiv ℝ P.map x (standardBasis 1 i)) = 0) ∧
    0 < s.val * omega 2 (Fin.cons (patchNormal hD P x)
      (fun i => fderiv ℝ P.map x (standardBasis 1 i)))

/-- The actual outward normal, extended by zero off the boundary. -/
def normalAt {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V)) (z : ℂ) : ℂ := by
  classical
  exact planeIsometry.symm (if hz : planeIsometry z ∈ frontier (planeIsometry '' V)
    then outwardNormal hV ⟨planeIsometry z, hz⟩ else 0)

/-- The literal real scalar flux integrand of a supplied parametrized curve. -/
def literalIntegrand {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (γ : ℝ → ℂ) (u v : ℂ → ℝ) (t : ℝ) : ℝ :=
  (u (γ t) * inner ℝ (gradient v (γ t)) (normalAt hV (γ t)) -
    v (γ t) * inner ℝ (gradient u (γ t)) (normalAt hV (γ t))) * ‖deriv γ t‖


end D12Complex.ParametrizedBoundaryDisplay

namespace Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay
open _root_.D12Complex _root_.D12Complex.ComplexGreenBridge
open _root_.D12Complex.ParametrizedBoundaryDisplay
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model

/-- The complete geometric conclusion. Count and literal global patch maps are
fixed by the input arrays, including when endpoints coincide or m=0. -/
def boundary_display_type : Prop :=
  ∀ (V O : Set ℂ) (hD : IsClassicalRegularDomain (planeIsometry '' V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    (m : ℕ) (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) (T : Fin m → Set ℝ),
    RegularBoundaryCurves V m γ a b T →
    ∃ (B : BoundaryDisplay hD (planeIsometry '' O)) (hc : B.count = m),
      (∀ i, (B.patch (Fin.cast hc.symm i)).region = intervalIsometry '' Icc (a i) (b i)) ∧
      (∀ i x, (B.patch (Fin.cast hc.symm i)).map x =
        planeIsometry (γ i (intervalIsometry.symm x))) ∧
      (∀ i, (B.patch (Fin.cast hc.symm i)).domain ⊆ intervalIsometry '' T i) ∧
      (∀ j, PatchFrame hD (B.patch j) (B.sign j)) ∧
      (∀ j, B.seams.dim j = 0)

/-- The literal scalar harmonic flux conclusion for the supplied arrays. -/
def parametrized_harmonic_green_type : Prop :=
  ∀ (V O : Set ℂ) (hD : IsClassicalRegularDomain (planeIsometry '' V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    (m : ℕ) (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) (T : Fin m → Set ℝ),
    RegularBoundaryCurves V m γ a b T →
    ∀ (u v : ℂ → ℝ), ContDiffOn ℝ 2 u O → ContDiffOn ℝ 2 v O →
      (∀ z ∈ V, coordinateLaplacian u z = 0) →
      (∀ z ∈ V, coordinateLaplacian v z = 0) →
      (∀ i, IntervalIntegrable (literalIntegrand hD (γ i) u v)
        MeasureTheory.volume (a i) (b i)) ∧
      (∑ i, ∫ t in a i..b i, literalIntegrand hD (γ i) u v t) = 0

def LocalRegularExtension_type := Set ℂ → (ℝ → ℂ) → ℝ → ℝ → Prop
def LocalRegularExtension_value : LocalRegularExtension_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.LocalRegularExtension

def RegularBoundaryCurves_type :=
  (V : Set ℂ) → (m : ℕ) → (Fin m → ℝ → ℂ) →
    (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → Set ℝ) → Prop
def RegularBoundaryCurves_value : RegularBoundaryCurves_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.RegularBoundaryCurves

open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

def PatchFrame_type := {D U : Set (E 2)} → IsClassicalRegularDomain D →
  Patch 1 U → PointSign → Prop
def PatchFrame_value : PatchFrame_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.PatchFrame

def normalAt_type := {V : Set ℂ} →
  IsClassicalRegularDomain (planeIsometry '' V) → ℂ → ℂ
def normalAt_value : normalAt_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.normalAt

def literalIntegrand_type := {V : Set ℂ} →
  IsClassicalRegularDomain (planeIsometry '' V) → (ℝ → ℂ) →
  (ℂ → ℝ) → (ℂ → ℝ) → ℝ → ℝ
def literalIntegrand_value : literalIntegrand_type :=
  @_root_.D12Complex.ParametrizedBoundaryDisplay.literalIntegrand

end Specs.D12Complex.Ch14.ParametrizedBoundaryDisplay
