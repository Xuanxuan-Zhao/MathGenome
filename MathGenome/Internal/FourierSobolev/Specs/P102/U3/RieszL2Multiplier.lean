import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Plancherel
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Independent statements for the kernel/L² stage of paper.tex:1161–1184.
Lebesgue volume and the negative-sign 2π Fourier transform are fixed by the
upstream interfaces. The later weak-(1,1), Lᵖ and a.e. convergence extension is
allocated to `u3_riesz_transforms` and is not assumed here. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff

namespace P102.Specs.U3.Riesz
open P102.Specs.U3 (Euclidean)

abbrev L2 (d : ℕ) := Lp (α := Euclidean d) ℂ 2 volume

def constantType := ℕ → ℝ
def constantValue : constantType := fun d =>
  Real.Gamma (((d : ℝ) + 1) / 2) / Real.pi ^ (((d : ℝ) + 1) / 2)

def kernelType := (d : ℕ) → Fin d → Euclidean d → ℝ
/-- The value at zero is totalized to zero, and plays no role in truncations. -/
def kernelValue : kernelType := fun d j x => constantValue d * x j / ‖x‖ ^ (d + 1)

def symbolType := (d : ℕ) → Fin d → Euclidean d → ℂ
def symbolValue : symbolType := fun _ j ξ => -Complex.I * ((ξ j / ‖ξ‖ : ℝ) : ℂ)

/-- Any finite complex value at the null frequency is allowed. -/
def symbolAtOrigin {d : ℕ} (j : Fin d) (a : ℂ) (ξ : Euclidean d) : ℂ :=
  if ξ = 0 then a else symbolValue d j ξ

/-- The canonical upstream Plancherel action, not a newly chosen Fourier map. -/
abbrev F2 (d : ℕ) := P102.Specs.U3.Plancherel.fourierL2_value (Euclidean d) ℂ

def IsMultiplier {d : ℕ} (j : Fin d) (a : ℂ) (R : L2 d →L[ℂ] L2 d) : Prop :=
  ∀ f : L2 d, (F2 d (R f) : Euclidean d → ℂ) =ᵐ[volume]
    fun ξ => symbolAtOrigin j a ξ * (F2 d f : Euclidean d → ℂ) ξ

def smoothStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ j : Fin d,
  ContDiffOn ℝ ∞ (kernelValue d j) ({0}ᶜ : Set (Euclidean d))

def homogeneousStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ (j : Fin d)
  (r : ℝ), 0 < r → ∀ x : Euclidean d,
  kernelValue d j (r • x) = r ^ (-(d : ℤ)) * kernelValue d j x

/-- Surface measure is the native polar-coordinate surface measure induced by
standard Euclidean volume: a cone has measure d times its unit-ball volume.
Integrability is explicit, so the zero integral cannot be a totalized undefined
integral. In dimension one this is counting measure on the two endpoints. -/
def sphereMeanStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ j : Fin d,
  Integrable (fun θ : Metric.sphere (0 : Euclidean d) 1 => kernelValue d j θ.val)
    (volume : Measure (Euclidean d)).toSphere ∧
  (∫ θ : Metric.sphere (0 : Euclidean d) 1, kernelValue d j θ.val
    ∂(volume : Measure (Euclidean d)).toSphere) = 0

/-- The operator norm of the real Fréchet derivative equals the Euclidean
norm of the gradient of this real scalar function. C depends only on d. -/
def derivativeBoundStatement : Prop := ∀ d : ℕ, 1 ≤ d →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (x : Euclidean d), x ≠ 0 →
    ‖fderiv ℝ (kernelValue d j) x‖ ≤ C / ‖x‖ ^ (d + 1)

/-- Construction and contractivity of the multiplier, for every origin value. -/
def multiplierStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ (j : Fin d) (a : ℂ),
  ∃ R : L2 d →L[ℂ] L2 d, ‖R‖ ≤ 1 ∧ IsMultiplier j a R

def uniquenessStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ (j : Fin d) (a b : ℂ)
  (R S : L2 d →L[ℂ] L2 d), IsMultiplier j a R → IsMultiplier j b S → R = S

/-- Ordinary physical-space truncations: there is no Gaussian cutoff in the
statement of the final identification. The integral order matches the source. -/
def truncation {d : ℕ} (j : Fin d) (ε : ℝ) (f : Euclidean d → ℂ)
    (x : Euclidean d) : ℂ :=
  ∫ z in {z : Euclidean d | ε < ‖z‖}, (kernelValue d j z : ℂ) * f (x - z)

def principalValueType := (d : ℕ) → Fin d → (Euclidean d → ℂ) → Euclidean d → ℂ

def principalValueValue : principalValueType := fun d j f x =>
  ∫ z, (kernelValue d j z : ℂ) * (f (x - z) - f (x + z)) / 2

/-- The existence part is recorded separately so partial progress cannot be
mistaken for the Fourier identification, which remains in principalValueStatement. -/
def principalValueExistsStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ (j : Fin d)
  (f : Euclidean d → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f →
    MemLp f 2 volume ∧
    (∀ (ε : ℝ), 0 < ε → ∀ x : Euclidean d,
      IntegrableOn (fun z => (kernelValue d j z : ℂ) * f (x - z))
        {z : Euclidean d | ε < ‖z‖}) ∧
    (∀ x, Tendsto (fun ε => truncation j ε f x) (𝓝[>] 0)
      (𝓝 (principalValueValue d j f x)))

/-- Pointwise existence on all smooth compactly supported inputs, L² membership
of the resulting representative, and equality with the canonical multiplier.
The conditional hypothesis here is only the independently constructed frequency
action; it does not assume any physical-kernel identification. -/
def principalValueStatement : Prop := ∀ d : ℕ, 1 ≤ d → ∀ (j : Fin d) (a : ℂ)
  (R : L2 d →L[ℂ] L2 d), IsMultiplier j a R →
  ∀ f : Euclidean d → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
    (∀ (ε : ℝ), 0 < ε → ∀ x : Euclidean d,
      IntegrableOn (fun z => (kernelValue d j z : ℂ) * f (x - z))
        {z : Euclidean d | ε < ‖z‖}) ∧
    ∃ (g : Euclidean d → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume),
      (∀ x, Tendsto (fun ε => truncation j ε f x) (𝓝[>] 0) (𝓝 (g x))) ∧
      hg.toLp g = R (hf.toLp f)

/-- The canonical coordinate model of ℝ¹, for the exact Hilbert specialization. -/
def line (x : ℝ) : Euclidean 1 := WithLp.toLp 2 (fun _ => x)

def oneDimensionalStatement : Prop :=
  constantValue 1 = 1 / Real.pi ∧
  (∀ x : ℝ, kernelValue 1 0 (line x) = 1 / (Real.pi * x)) ∧
  (∀ ξ : ℝ, symbolValue 1 0 (line ξ) = -Complex.I * (Real.sign ξ : ℂ))

end P102.Specs.U3.Riesz
