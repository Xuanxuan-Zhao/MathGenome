import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Spectrum

/-! Independent statements for paper.tex, d13:10:resolvent. Natural index n
corresponds to j=n+1. Ambient functions are identified only on [a,b]. -/
noncomputable section
open MeasureTheory Set Filter
namespace Specs.D13Unified.Ch10.Resolvent
open RegularProblem

/-- The actual real Dirichlet eigenbasis, with no operator certificates. -/
structure SpectralData (P : Problem) where
  lam : ℕ → ℝ
  phi : ℕ → ℝ → ℝ
  memLp : ∀ n, MemLp (fun x => (phi n x : ℂ)) 2 (weightedMeasureValue P)
  basis : HilbertBasis ℕ ℂ (hilbertValue P)
  increasing : StrictMono lam
  divergent : Tendsto lam atTop atTop
  classical : ∀ n, classicalEigenfunctionValue P dirichletValue (lam n : ℂ)
    (fun x => (phi n x : ℂ))
  represents : ∀ n, basis n = toHilbertValue P (fun x => (phi n x : ℂ)) (memLp n)
  exhaustive : ∀ (z : ℂ) (y : ℝ → ℂ),
    classicalEigenfunctionValue P dirichletValue z y → ∃ n, z = (lam n : ℂ)

/-- C¹ at included endpoints means one-sided derivatives. The flux is
absolutely continuous and its ambient derivative has the prescribed value AE. -/
def solutionValue (P : Problem) (z : ℂ) (f : hilbertValue P) (y : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 1 y (intervalValue P) ∧
  AbsolutelyContinuousOnInterval
    (fun x => (P.p x : ℂ) * derivativeValue P y x) P.a P.b ∧
  y P.a = 0 ∧ y P.b = 0 ∧
  ∀ᵐ x ∂baseMeasureValue P,
    HasDerivAt (fun t => (P.p t : ℂ) * derivativeValue P y t)
      (((P.q x : ℂ) - z * (P.w x : ℂ)) * y x - (P.w x : ℂ) * f x) x

def solutionType := (P : Problem) → ℂ → hilbertValue P → (ℝ → ℂ) → Prop

def EigenbasisExists : Prop := ∀ P : Problem, Nonempty (SpectralData P)

/-- Uniqueness is on the entire closed interval, not on arbitrary values
chosen outside it. The series converges in the weighted Hilbert space. -/
def Nonresonant : Prop := ∀ (P : Problem) (D : SpectralData P)
  (z : ℂ), (∀ n, z ≠ (D.lam n : ℂ)) → ∀ f : hilbertValue P,
  ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasureValue P)),
    solutionValue P z f y ∧
    HasSum (fun n => (paperInnerValue P f (D.basis n) / ((D.lam n : ℂ) - z)) •
      D.basis n) (toHilbertValue P y hy) ∧
    ∀ v : ℝ → ℂ, solutionValue P z f v → EqOn v y (intervalValue P)

/-- At resonance, compatibility is necessary and sufficient. Every scalar
multiple of the real normalized eigenfunction can be added, and this lists
all solutions, with equality at both endpoints as well as the interior. -/
def Resonant : Prop := ∀ (P : Problem) (D : SpectralData P) (k : ℕ)
  (f : hilbertValue P),
  ((∃ y : ℝ → ℂ, solutionValue P (D.lam k : ℂ) f y) ↔
    paperInnerValue P f (D.basis k) = 0) ∧
  (paperInnerValue P f (D.basis k) = 0 →
    ∃ y₀ : ℝ → ℂ, solutionValue P (D.lam k : ℂ) f y₀ ∧
      (∀ t : ℂ, solutionValue P (D.lam k : ℂ) f
        (fun x => y₀ x + t * (D.phi k x : ℂ))) ∧
      ∀ y : ℝ → ℂ, solutionValue P (D.lam k : ℂ) f y →
        ∃ t : ℂ, EqOn y (fun x => y₀ x + t * (D.phi k x : ℂ)) (intervalValue P))

def Equation : Prop := ∀ (P : Problem) (z : ℂ) (f : hilbertValue P)
  (y : ℝ → ℂ), solutionValue P z f y → ∀ᵐ x ∂baseMeasureValue P,
    expressionValue P y x - z * (P.w x : ℂ) * y x = (P.w x : ℂ) * f x

end Specs.D13Unified.Ch10.Resolvent
