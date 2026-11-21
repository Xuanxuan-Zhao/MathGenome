import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Plancherel

/-! Independent specification of paper.tex:1091–1102, with the bilinear
pairing fixed at paper.tex:53,1049. All dimensions, including zero, are allowed.
`Tempered` carries bounded convergence; `WeakTempered` carries pointwise
convergence. No continuity of the identity in the reverse direction is assumed. -/
noncomputable section
open MeasureTheory LineDeriv
open scoped FourierTransform

namespace P102.Specs.U3.TemperedFourier
open P102.U3 (coordinateVector coordinateMul)

def strongMap_type := (d : ℕ) → Tempered d →L[ℂ] Tempered d
def weakMap_type := (d : ℕ) → WeakTempered d →L[ℂ] WeakTempered d

def fourierStrong_value : strongMap_type :=
  fun d => ContinuousLinearMap.precomp ℂ (fourierValue d)
def checkStrong_value : strongMap_type :=
  fun d => ContinuousLinearMap.precomp ℂ (checkValue d)
def fourierWeak_value : weakMap_type :=
  fun d => FourierTransform.fourierCLM ℂ (WeakTempered d)
def checkWeak_value : weakMap_type :=
  fun d => FourierTransform.fourierInvCLM ℂ (WeakTempered d)

def coordinateMap_type := {d : ℕ} → Fin d → Tempered d →L[ℂ] Tempered d
/-- The negative sign is part of the distributional derivative. -/
def derivative_value : coordinateMap_type := fun {_} j =>
  ContinuousLinearMap.precomp ℂ (-lineDerivOpCLM ℂ (Test _) (coordinateVector j))
def multiply_value : coordinateMap_type := fun {_} j =>
  ContinuousLinearMap.precomp ℂ (coordinateMul j)

/-- This is an underlying functional, with the strong topology on the dual.
The Lp embedding is continuous in its *test* argument for every p≥1. -/
def regularLp_type := {d : ℕ} → {p : ENNReal} → [Fact (1 ≤ p)] →
  Lp (α := Euclidean d) ℂ p volume → Tempered d
def regularLp_value : regularLp_type := fun {_} {_} [_] f => Lp.toTemperedDistribution f

/-- A regular distribution is induced by the bilinear integral, with each test
product genuinely integrable. The transformed L¹ function need not be in L¹. -/
def Induces {d : ℕ} (U : Tempered d) (f : Euclidean d → ℂ) : Prop :=
  ∀ φ : Test d, Integrable (fun x => f x * φ x) ∧ U φ = ∫ x, f x * φ x

def transposition_type : Prop := ∀ (d : ℕ) (U : Tempered d) (φ : Test d),
  fourierStrong_value d U φ = U (fourierValue d φ) ∧
  checkStrong_value d U φ = U (checkValue d φ)

def strongInverse_type : Prop := ∀ d : ℕ,
  (checkStrong_value d).comp (fourierStrong_value d) = ContinuousLinearMap.id ℂ (Tempered d) ∧
  (fourierStrong_value d).comp (checkStrong_value d) = ContinuousLinearMap.id ℂ (Tempered d)

def weakInverse_type : Prop := ∀ d : ℕ,
  (checkWeak_value d).comp (fourierWeak_value d) = ContinuousLinearMap.id ℂ (WeakTempered d) ∧
  (fourierWeak_value d).comp (checkWeak_value d) = ContinuousLinearMap.id ℂ (WeakTempered d)

/-- The same functionals and transformations underlie the two topologies. -/
def strongWeak_type : Prop := ∀ (d : ℕ) (U : Tempered d),
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Test d) ℂ
    (fourierStrong_value d U) =
      fourierWeak_value d (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ
        (RingHom.id ℂ) (Test d) ℂ U) ∧
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Test d) ℂ
    (checkStrong_value d U) =
      checkWeak_value d (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ
        (RingHom.id ℂ) (Test d) ℂ U)

/-- Explicit bounded-set bridge for BOTH signs. Uniform testing on B after
transposition is exactly uniform testing on its bounded Fourier image. -/
def boundedTesting_type : Prop := ∀ (d : ℕ) (B : Set (Test d)),
  Bornology.IsVonNBounded ℂ B →
    Bornology.IsVonNBounded ℂ (fourierValue d '' B) ∧
    Bornology.IsVonNBounded ℂ (checkValue d '' B) ∧
    ∀ (U : Tempered d) (V : Set ℂ),
      ((∀ φ ∈ B, fourierStrong_value d U φ ∈ V) ↔
        ∀ ψ ∈ fourierValue d '' B, U ψ ∈ V) ∧
      ((∀ φ ∈ B, checkStrong_value d U φ ∈ V) ↔
        ∀ ψ ∈ checkValue d '' B, U ψ ∈ V)

def continuity_type : Prop := ∀ d : ℕ,
  Continuous (fourierStrong_value d) ∧ Continuous (checkStrong_value d) ∧
  Continuous (fourierWeak_value d) ∧ Continuous (checkWeak_value d)

/-- Both a continuous linear equivalence and its inverse have the requested
transposition formulas. Thus these are automorphisms in each topology. -/
def strongAutomorphism_type : Prop := ∀ d : ℕ,
  ∃ e : Tempered d ≃L[ℂ] Tempered d,
    (∀ U, e U = fourierStrong_value d U) ∧ (∀ U, e.symm U = checkStrong_value d U)
def weakAutomorphism_type : Prop := ∀ d : ℕ,
  ∃ e : WeakTempered d ≃L[ℂ] WeakTempered d,
    (∀ U, e U = fourierWeak_value d U) ∧ (∀ U, e.symm U = checkWeak_value d U)

def coordinateActions_type : Prop := ∀ {d : ℕ} (j : Fin d)
  (U : Tempered d) (φ : Test d),
  derivative_value j U φ = -U (∂_{coordinateVector j} φ) ∧
  multiply_value j U φ = U (coordinateMul j φ)

def fourierDerivative_type : Prop := ∀ {d : ℕ} (j : Fin d) (U : Tempered d),
  fourierStrong_value d (derivative_value j U) =
    (2 * Real.pi * Complex.I) • multiply_value j (fourierStrong_value d U)

def fourierMultiply_type : Prop := ∀ {d : ℕ} (j : Fin d) (U : Tempered d),
  fourierStrong_value d (multiply_value j U) =
    (-(2 * Real.pi * Complex.I)⁻¹) • derivative_value j (fourierStrong_value d U)

def regularL1_type : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ) (hf : Integrable f),
  Induces (regularLp_value (memLp_one_iff_integrable.mpr hf).toLp) f

def l1Compatibility_type : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ) (hf : Integrable f),
  Induces (fourierStrong_value d (regularLp_value (memLp_one_iff_integrable.mpr hf).toLp))
    (𝓕 f) ∧
  Induces (checkStrong_value d (regularLp_value (memLp_one_iff_integrable.mpr hf).toLp))
    (𝓕⁻ f)

def regularL2_type : Prop := ∀ (d : ℕ) (f : Lp (α := Euclidean d) ℂ 2 volume),
  Induces (regularLp_value f) (f : Euclidean d → ℂ)

def l2Compatibility_type : Prop := ∀ (d : ℕ) (f : Lp (α := Euclidean d) ℂ 2 volume),
  fourierStrong_value d (regularLp_value f) =
    regularLp_value (Plancherel.fourierL2_value (Euclidean d) ℂ f) ∧
  checkStrong_value d (regularLp_value f) =
    regularLp_value ((Plancherel.fourierL2_value (Euclidean d) ℂ).symm f)

end P102.Specs.U3.TemperedFourier
