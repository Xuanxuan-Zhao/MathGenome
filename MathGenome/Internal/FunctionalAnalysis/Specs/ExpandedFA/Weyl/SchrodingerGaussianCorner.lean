import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.GaussianCorner
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The concrete Gaussian and the four conclusions at paper.tex:16402–16417.
The configuration square length is the sum of squares, not the Pi norm.
The scalar product is conjugate-linear in the first variable. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace ExpandedFA.Weyl.SchrodingerGaussianCornerSpec
open RegularWeylRepresentationSpec GaussianCornerSpec

def configurationSquare {d : ℕ} (t : Configuration d) : ℝ := ∑ j, (t j) ^ 2

def vacuumNormalization (d : ℕ) : ℝ := Real.pi ^ (-(d : ℝ) / 4)

def vacuumFunction (d : ℕ) (t : Configuration d) : ℂ :=
  (vacuumNormalization d * Real.exp (-configurationSquare t / 2) : ℝ)

lemma vacuumFunction_memLp (d : ℕ) : MemLp (vacuumFunction d) 2 volume := by
  have hc : Continuous (vacuumFunction d) := by
    unfold vacuumFunction configurationSquare
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi : Integrable (fun t : Configuration d => ∏ j, Real.exp (-(t j) ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin d) (x : ℝ) => Real.exp (-x ^ 2))
      (fun _ => by simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
  convert hi.const_mul (vacuumNormalization d ^ 2) using 1
  ext t
  simp only [vacuumFunction, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 2
  simp only [configurationSquare, ← Finset.sum_neg_distrib]
  ring

def vacuum (d : ℕ) : SchrodingerSpace d :=
  (vacuumFunction_memLp d).toLp (vacuumFunction d)

def VacuumNorm : Prop := ∀ (d : ℕ) (_hd : 0 < d), ‖vacuum d‖ = 1

def VacuumCoefficient : Prop := ∀ (d : ℕ) (_hd : 0 < d) (z : PhaseSpace d),
  inner ℂ (vacuum d) (SchrodingerActionValue z (vacuum d)) = (gaussianWeight z : ℂ)

/-- The rank-one identity is for the normalized strong Gaussian integral itself. -/
def ConcreteGaussianProjection : Prop := ∀ (d : ℕ) (_hd : 0 < d)
    (R : RegularRepresentation d (SchrodingerSpace d)),
  (∀ z f, R.W z f = SchrodingerActionValue z f) →
  ∀ f, gaussianVectorIntegral R f = inner ℂ (vacuum d) f • vacuum d

def VacuumOrbitDense : Prop := ∀ (d : ℕ) (_hd : 0 < d),
  (Submodule.span ℂ (Set.range (fun z : PhaseSpace d =>
    SchrodingerActionValue z (vacuum d)))).topologicalClosure = ⊤

end ExpandedFA.Weyl.SchrodingerGaussianCornerSpec
