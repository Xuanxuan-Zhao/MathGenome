import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! Canonical coefficient model for paper.tex:18784–18792. The circle has period
2π and its Haar measure has mass one. No theorem in this file assumes any of
the analytic, boundary, or multiplier conclusions of the Hardy-space goal. -/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.PartIV.HardyDiskSpec

abbrev H2 : Type := lp (fun _ : ℕ => ℂ) 2
abbrev Circle := AddCircle (2 * π)
abbrev BoundaryL2 : Type := Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π))
def disk : Set ℂ := Metric.ball 0 1
abbrev Disk := {z : ℂ // z ∈ disk}

/-- Evaluation is the actual Taylor series, initially defined on all of ℂ.
All assertions about its convergence or analyticity are restricted to the disk. -/
def eval (f : H2) (z : ℂ) : ℂ := ∑' n : ℕ, f n * z ^ n

def modes (n : ℕ) : BoundaryL2 := fourierLp 2 (n : ℤ)

theorem modes_orthonormal : Orthonormal ℂ modes :=
  orthonormal_fourier.comp (fun n : ℕ => (n : ℤ)) (by intro i j h; change (i : ℤ) = (j : ℤ) at h; omega)

/-- Boundary Fourier synthesis; this has the coefficient norm by construction. -/
def boundary : H2 →ₗᵢ[ℂ] BoundaryL2 :=
  modes_orthonormal.orthogonalFamily.linearIsometry

/-- The closed nonnegative-Fourier subspace, defined by its actual integrals. -/
def nonnegativeFourier : Submodule ℂ BoundaryL2 where
  carrier := {g | ∀ k : ℤ, k < 0 → fourierCoeff g k = 0}
  zero_mem' := by simp [← fourierBasis_repr]
  add_mem' := by
    intro f g hf hg k hk
    rw [← fourierBasis_repr, map_add]
    change fourierBasis.repr f k + fourierBasis.repr g k = 0
    rw [fourierBasis_repr, fourierBasis_repr, hf k hk, hg k hk, add_zero]
  smul_mem' := by
    intro c f hf k hk
    rw [← fourierBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply,
      fourierBasis_repr, hf k hk, smul_zero]

/-- Bounded holomorphic functions on the disk itself; zero extension is used only
for expressing complex differentiability on this open subset of ℂ. -/
def zeroExtend (b : Disk → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ disk then b ⟨z, hz⟩ else 0

def HInfinity := {b : Disk → ℂ // DifferentiableOn ℂ (zeroExtend b) disk ∧
  ∃ C : ℝ, ∀ z : Disk, ‖b z‖ ≤ C}

def infinityNorm (b : HInfinity) : ℝ := ⨆ z : Disk, ‖b.val z‖

/-- The coefficient shift, constructed without presupposing analytic evaluation. -/
def shiftedModes (n : ℕ) : H2 := lp.single 2 (n + 1) 1

theorem shiftedModes_orthonormal : Orthonormal ℂ shiftedModes := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [shiftedModes, lp.inner_single_left, lp.single_apply, Pi.single_apply,
    RCLike.inner_apply]

def shift : H2 →ₗᵢ[ℂ] H2 := shiftedModes_orthonormal.orthogonalFamily.linearIsometry

/-- Innerness includes boundedness in the disk and actual a.e. boundary modulus. -/
def IsInner (f : H2) : Prop :=
  (∃ C : ℝ, ∀ z ∈ disk, ‖eval f z‖ ≤ C) ∧
    ∀ᵐ t ∂AddCircle.haarAddCircle, ‖boundary f t‖ = 1

/-- Cyclicity for multiplication by z, not an alternative factorization definition. -/
def IsOuter (f : H2) : Prop :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => (shift^[n]) f))).topologicalClosure = ⊤

/-- The normalized Poisson integral of the boundary function. -/
def poissonExtension (f : H2) (z : ℂ) : ℂ :=
  ∫ t : Circle, ((1 - ‖z‖ ^ 2) / ‖fourier (T := 2 * π) 1 t - z‖ ^ 2) •
    boundary f t ∂AddCircle.haarAddCircle

-- Full expected mathematical conclusions, independently stated.
def CoefficientNorm : Prop := ∀ f : H2, HasSum (fun n => ‖f n‖ ^ 2) (‖f‖ ^ 2)
def AnalyticEvaluation : Prop := ∀ f : H2, AnalyticOnNhd ℂ (eval f) disk
def EvaluationHasSum : Prop := ∀ (f : H2) (z : ℂ), z ∈ disk →
  HasSum (fun n => f n * z ^ n) (eval f z)
def EvaluationBound : Prop := ∀ (f : H2) (z : ℂ), z ∈ disk →
  ‖eval f z‖ ≤ ‖f‖ / Real.sqrt (1 - ‖z‖ ^ 2)
def EvaluationInjective : Prop := ∀ f g : H2,
  Set.EqOn (eval f) (eval g) disk → f = g

def BoundarySeries : Prop := ∀ f : H2,
  HasSum (fun n : ℕ => f n • fourierLp (T := 2 * π) 2 (n : ℤ)) (boundary f)
def BoundaryCoefficients : Prop := ∀ (f : H2) (k : ℤ),
  fourierCoeff (boundary f) k = if 0 ≤ k then f k.toNat else 0
def BoundaryRange : Prop := LinearMap.range boundary.toLinearMap = nonnegativeFourier
def BoundaryClosed : Prop := IsClosed (nonnegativeFourier : Set BoundaryL2)
def BoundaryUnitary : Prop := ∃ U : H2 ≃ₗᵢ[ℂ] nonnegativeFourier,
  ∀ f : H2, (U f).val = boundary f
def ShiftEvaluation : Prop := ∀ (f : H2) (z : ℂ), z ∈ disk →
  eval (shift f) z = z * eval f z

def PoissonEvaluation : Prop := ∀ (f : H2) (z : ℂ), z ∈ disk →
  poissonExtension f z = eval f z
/-- Genuine radial L² convergence of the analytic values. -/
def RadialConvergence : Prop := ∀ f : H2,
  ∃ g : ℝ → BoundaryL2,
    (∀ r, 0 ≤ r → r < 1 →
      (g r : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
        (fun t => eval f ((r : ℂ) * fourier (T := 2 * π) 1 t))) ∧
    Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 (boundary f))
/-- All bounded holomorphic functions, not a restricted multiplier class. -/
def BoundedAnalyticCoefficients : Prop := ∀ b : HInfinity,
  ∃ f : H2, ∀ z : Disk, eval f z = b.val z

def BoundedMultiplier : Prop := ∀ b : HInfinity,
  ∃ M : H2 →L[ℂ] H2,
    (∀ (f : H2) (z : Disk), eval (M f) z = b.val z * eval f z) ∧
    ‖M‖ ≤ infinityNorm b

def HilbertComplete : Prop := CompleteSpace H2
def BoundaryNorm : Prop := ∀ f : H2, ‖boundary f‖ = ‖f‖
def EvaluationFunctional : Prop := ∀ z : Disk,
  ∃ E : H2 →L[ℂ] ℂ, (∀ f : H2, E f = eval f z) ∧
    ‖E‖ ≤ (Real.sqrt (1 - ‖z.val‖ ^ 2))⁻¹

def MonomialEvaluation : Prop := ∀ (n : ℕ) (c z : ℂ),
  eval (lp.single (E := fun _ : ℕ => ℂ) 2 n c) z = c * z ^ n

def PolynomialDensity : Prop :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => lp.single 2 n (1 : ℂ)))).topologicalClosure = ⊤

-- Type/value contracts for the public canonical objects.
def H2Type := Type
def H2Value : H2Type := H2
def CircleType := Type
def CircleValue : CircleType := Circle
def BoundaryL2Type := Type
def BoundaryL2Value : BoundaryL2Type := BoundaryL2
def DiskSetType := Set ℂ
def DiskSetValue : DiskSetType := disk
def DiskType := Type
def DiskValue : DiskType := Disk
def HInfinityType := Type
def HInfinityValue : HInfinityType := HInfinity
def InfinityNormType := HInfinity → ℝ
def InfinityNormValue : InfinityNormType := infinityNorm
def EvaluationType := H2 → ℂ → ℂ
def EvaluationValue : EvaluationType := eval
def BoundaryType := H2 →ₗᵢ[ℂ] BoundaryL2
def BoundaryValue : BoundaryType := boundary
def ShiftType := H2 →ₗᵢ[ℂ] H2
def ShiftValue : ShiftType := shift
def InnerType := H2 → Prop
def InnerValue : InnerType := IsInner
def OuterType := H2 → Prop
def OuterValue : OuterType := IsOuter
def NonnegativeFourierType := Submodule ℂ BoundaryL2
def NonnegativeFourierValue : NonnegativeFourierType := nonnegativeFourier
def PoissonExtensionType := H2 → ℂ → ℂ
def PoissonExtensionValue : PoissonExtensionType := poissonExtension

end ExpandedFA.PartIV.HardyDiskSpec
