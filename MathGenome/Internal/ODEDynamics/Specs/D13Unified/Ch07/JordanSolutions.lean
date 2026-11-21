import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.ExponentialCalculus
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open scoped Matrix.Norms.Operator

namespace D13Unified.Ch07

/-- The constant matrix equation on its full time-state domain. Complex states
are regarded as a real normed space, so the independent variable remains real. -/
def matrixODE {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) : D13Unified.ODE (n → 𝕂) where
  domain := Set.univ
  isOpen_domain := isOpen_univ
  field := fun p => A.mulVec p.val.2
  continuous_field := by
    fun_prop

end D13Unified.Ch07

namespace Specs.D13Unified.Ch07.JordanSolutions
open _root_.D13Unified _root_.D13Unified.Ch07
open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)
open Specs.D13Unified.Ch01.SolutionConcepts (classicalSolutionOnValue)
universe u

def blockType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (μ : ℂ) (m : ℕ), 1 ≤ m → N ^ m = 0 → ∀ t : ℝ,
    exponentialValue (μ • (1 : Matrix n n ℂ) + N) t =
      Complex.exp (μ * (t : ℂ)) •
        ∑ j ∈ Finset.range m, (t ^ j / (Nat.factorial j : ℝ)) • N ^ j

def similarityType : Prop :=
  ∀ {𝕂 : Type} {n : Type u} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (P : (Matrix n n 𝕂)ˣ) (A : Matrix n n 𝕂) (t : ℝ),
    exponentialValue (P.val * A * (P⁻¹).val) t =
      P.val * exponentialValue A t * (P⁻¹).val

/-- The full solution formula on the solution's actual interval. -/
def solutionType : Prop :=
  ∀ {𝕂 : Type} {n : Type u} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (I : OpenTimeInterval) (x : ℝ → n → 𝕂),
    classicalSolutionOnValue (matrixODE A) I x → ∀ s ∈ I.carrier,
      ∀ t ∈ I.carrier, x t = (exponentialValue A (t - s)).mulVec (x s)

/-- The formula also supplies a global solution for every initial vector. -/
def solutionExistsType : Prop :=
  ∀ {𝕂 : Type} {n : Type u} [RCLike 𝕂] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕂) (s : ℝ) (v : n → 𝕂),
    ContDiff ℝ 1 (fun r => (exponentialValue A (r - s)).mulVec v) ∧
    (∀ t, HasDerivAt (fun r => (exponentialValue A (r - s)).mulVec v)
      (A.mulVec ((exponentialValue A (t - s)).mulVec v)) t) ∧
    (exponentialValue A (s - s)).mulVec v = v

/-- Each component of every solution is an exponential polynomial. The
polynomials and exponents are fixed for the entire interval, not chosen per time. -/
def complexRepresentationType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (I : OpenTimeInterval) (x : ℝ → n → ℂ),
    classicalSolutionOnValue (matrixODE A) I x → ∀ s ∈ I.carrier,
    ∃ (r : ℕ) (μ : Fin r → ℂ) (p : n → Fin r → Polynomial ℂ),
      ∀ t ∈ I.carrier, ∀ k,
        x t k = ∑ l : Fin r, (p k l).eval ((t - s : ℝ) : ℂ) *
          Complex.exp (μ l * ((t - s : ℝ) : ℂ))

/-- Real solutions, including those arising from nontrivial complex Jordan
blocks, are finite sums of real polynomial coefficients times sine and cosine
exponentials. This includes zero dimension and real eigenvalues (β = 0). -/
def realRepresentationType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (I : OpenTimeInterval) (x : ℝ → n → ℝ),
    classicalSolutionOnValue (matrixODE A) I x → ∀ s ∈ I.carrier,
    ∃ (r : ℕ) (α β : Fin r → ℝ) (p q : n → Fin r → Polynomial ℝ),
      ∀ t ∈ I.carrier, ∀ k,
        x t k = ∑ l : Fin r,
          Real.exp (α l * (t - s)) *
            ((p k l).eval (t - s) * Real.cos (β l * (t - s)) +
             (q k l).eval (t - s) * Real.sin (β l * (t - s)))

/-- The explicit real/imaginary bridge for an individual complex Jordan term.
Its conjugate has the same real part and the opposite imaginary part. -/
def realTermType : Prop :=
  ∀ (c : ℂ) (α β t : ℝ) (j : ℕ),
    ((t : ℂ) ^ j * Complex.exp ((α + β * Complex.I) * t) * c).re =
      t ^ j * Real.exp (α * t) *
        (c.re * Real.cos (β * t) - c.im * Real.sin (β * t)) ∧
    ((t : ℂ) ^ j * Complex.exp ((α + β * Complex.I) * t) * c).im =
      t ^ j * Real.exp (α * t) *
        (c.re * Real.sin (β * t) + c.im * Real.cos (β * t))

/-- A complex solution of the complexification of a real matrix equation has
real and imaginary parts solving the original real equation, on the same interval. -/
def realImaginarySolutionType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (I : OpenTimeInterval) (z : ℝ → n → ℂ),
    classicalSolutionOnValue (matrixODE (A.map Complex.ofReal)) I z →
      classicalSolutionOnValue (matrixODE A) I (fun t k => (z t k).re) ∧
      classicalSolutionOnValue (matrixODE A) I (fun t k => (z t k).im)

/-- Specialization to one generalized eigenspace of a real matrix at
α + iβ. Both real orbit components have precisely the stated sine/cosine
polynomial form with that same α and β. The conjugate pair uses −β. -/
def realGeneralizedEigenvectorType : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (α β : ℝ) (v : n → ℂ) (m : ℕ), 1 ≤ m →
    (((A.map Complex.ofReal - (α + β * Complex.I) • 1) ^ m).mulVec v = 0) →
    ∃ a b : n → Polynomial ℝ, ∀ t : ℝ, ∀ k,
      ((exponentialValue (A.map Complex.ofReal) t).mulVec v k).re =
        Real.exp (α * t) *
          ((a k).eval t * Real.cos (β * t) - (b k).eval t * Real.sin (β * t)) ∧
      ((exponentialValue (A.map Complex.ofReal) t).mulVec v k).im =
        Real.exp (α * t) *
          ((a k).eval t * Real.sin (β * t) + (b k).eval t * Real.cos (β * t))

end Specs.D13Unified.Ch07.JordanSolutions


