import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PeriodicDistributionInterface
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Independent statements for the Fourier part of `fa2:p4:periodic-distributions`,
paper.tex:20549–20606. The underlying smooth topology and continuous linear dual
are the accepted canonical torus interface. Haar measure has mass one. Fourier
coefficients and pairings are complex linear in the test, without conjugation.
The lattice weight uses the Euclidean norm, including in dimension zero.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace ExpandedFA.PartIV.Periodic

/-- The genuine smooth character exp(2π i n·x) on the quotient torus. -/
noncomputable def character {d : ℕ} (n : Lattice d) : Smooth ℂ d :=
  ⟨UnitAddTorus.mFourier n, by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ExpandedFA.Distributions.Domain d =>
      ∏ i, fourier (n i) ((x i : ℝ) : UnitAddCircle))
    simp_rw [fourier_coe_apply]
    apply contDiff_prod
    intro i _
    apply ContDiff.cexp
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff)).div_const _⟩

/-- Normalized product Haar measure on (ℝ/ℤ)^d. -/
noncomputable def torusHaar (d : ℕ) : Measure (Torus d) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

/-- The ordinary integral Fourier coefficient of a smooth function. -/
noncomputable def testFourierCoeff {d : ℕ} (φ : Smooth ℂ d) (n : Lattice d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-n) x * φ.val x ∂torusHaar d

/-- Distributional coefficients use the negative exponential. -/
noncomputable def distributionCoeff {d : ℕ} (U : TorusDistribution ℂ d)
    (n : Lattice d) : ℂ := U (character (-n))

noncomputable def frequencyNorm {d : ℕ} (n : Lattice d) : ℝ :=
  ‖(WithLp.toLp 2 (integerVector n) : EuclideanSpace ℝ (Fin d))‖

/-- There is no fixed upper bound on the allowable polynomial degree. -/
def PolynomialGrowth {d : ℕ} (c : Lattice d → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, ‖c n‖ ≤ C * (1 + frequencyNorm n) ^ N

/-- The finite Fourier distribution, expressed as its action on a smooth test. -/
noncomputable def finiteFourierPairing {d : ℕ} (c : Lattice d → ℂ)
    (s : Finset (Lattice d)) (φ : Smooth ℂ d) : ℂ :=
  ∑ n ∈ s, c n * testFourierCoeff φ (-n)

end ExpandedFA.PartIV.Periodic

namespace Specs.ExpandedFA.PartIV.PeriodicDistributions
open _root_.ExpandedFA.PartIV.Periodic

/-- Every distribution has some finite polynomial growth degree. -/
def polynomialGrowthType : Prop := ∀ (d : ℕ) (U : TorusDistribution ℂ d),
  PolynomialGrowth (distributionCoeff U)

/-- Absolute convergence and the value of the distribution on every smooth test. -/
def reconstructionType : Prop := ∀ (d : ℕ) (U : TorusDistribution ℂ d)
    (φ : Smooth ℂ d),
  Summable (fun n => ‖distributionCoeff U n * testFourierCoeff φ (-n)‖) ∧
    HasSum (fun n => distributionCoeff U n * testFourierCoeff φ (-n)) (U φ)

/-- Every polynomial-growth sequence gives a unique continuous complex-linear
functional, with both its coefficients and the absolutely convergent formula.
The quantifier covers all natural polynomial degrees, and imposes no d>0. -/
def converseType : Prop := ∀ (d : ℕ) (c : Lattice d → ℂ), PolynomialGrowth c →
  ∃! U : TorusDistribution ℂ d,
    (∀ n, distributionCoeff U n = c n) ∧
    ∀ φ : Smooth ℂ d,
      Summable (fun n => ‖c n * testFourierCoeff φ (-n)‖) ∧
      HasSum (fun n => c n * testFourierCoeff φ (-n)) (U φ)

/-- The coefficients alone determine the distribution. -/
def uniquenessType : Prop := ∀ (d : ℕ) (U V : TorusDistribution ℂ d),
  distributionCoeff U = distributionCoeff V → U = V

/-- Finite sums are continuous complex-linear functionals and converge on every
smooth test as the finite frequency sets exhaust the lattice. -/
def finiteSumsType : Prop := ∀ (d : ℕ) (c : Lattice d → ℂ), PolynomialGrowth c →
  ∃ U : TorusDistribution ℂ d,
    (∀ n, distributionCoeff U n = c n) ∧
    (∀ s : Finset (Lattice d), ∃ V : TorusDistribution ℂ d,
      ∀ φ, V φ = finiteFourierPairing c s φ) ∧
    ∀ φ : Smooth ℂ d,
      Tendsto (fun s : Finset (Lattice d) => finiteFourierPairing c s φ) atTop (𝓝 (U φ))

/-- Uniform weighted Fourier estimate used by the implementation, stated
independently of its proof. -/
def weightedEstimateType : Prop := ∀ (d N : ℕ),
  ∃ (A : ℝ≥0) (L : ℕ), ∀ φ : Smooth ℂ d,
    Summable (fun n => (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖) ∧
      (∑' n, (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖) ≤
        A * smoothPartialSeminorm ℂ d L φ

/-- The finite distributions exist independently of any growth hypothesis. -/
def finiteDistributionExistsType : Prop := ∀ (d : ℕ) (c : Lattice d → ℂ)
    (s : Finset (Lattice d)), ∃ V : TorusDistribution ℂ d,
      ∀ φ, V φ = finiteFourierPairing c s φ

end Specs.ExpandedFA.PartIV.PeriodicDistributions
