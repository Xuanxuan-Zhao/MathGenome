import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Convex.Function

/-! The first example in paper.tex, ex:direct-limitations (3973–3983).
The real functions below are absolutely continuous representatives on [0,1].
The two representation statements connect this model to the shared Sobolev
weak-derivative graph; thus no regularity of a competitor is added. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace VariationalNotes.Sobolev.LinearGrowth

def one : Exponent := ⟨1, le_rfl⟩
def intervalDomain : TopologicalSpace.Opens (Domain 1) :=
  ⟨{x | x 0 ∈ Ioo (0 : ℝ) 1}, isOpen_Ioo.preimage (by fun_prop)⟩
abbrev ScalarW11 := W1p intervalDomain 1 one

/-- Both the value and weak derivative are those of the very same class. -/
def Represents (w : ScalarW11) (f : ℝ → ℝ) : Prop :=
  (coordinateLp intervalDomain one (0 : Fin 1) (value intervalDomain 1 one w)
    =ᵐ[domainMeasure intervalDomain] fun x => f (x 0)) ∧
  (coordinateLp intervalDomain one ((0 : Fin 1), (0 : Fin 1))
    (gradient intervalDomain 1 one w)
    =ᵐ[domainMeasure intervalDomain] fun x => deriv f (x 0))

/-- Endpoint values refer to the AC representative, not arbitrary L¹ values. -/
def Admissible (f : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval f 0 1 ∧ f 0 = 0 ∧ f 1 = 1

def integrand (x z : ℝ) : ℝ := (1 + x) * |z|
def energy (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, integrand x (deriv f x)
/-- This is the source W^{1,1} norm, with its p=1 sum. -/
def sourceNorm (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, |f x|) + ∫ x in (0 : ℝ)..1, |deriv f x|
def ramp (n : ℕ) (x : ℝ) : ℝ := min ((n : ℝ) * x) 1

/-- The endpoint class inside the shared, genuine W^{1,1} quotient space. -/
def boundaryClass : Set ScalarW11 := {w | ∃ f : ℝ → ℝ, Admissible f ∧ Represents w f}

/-- The real energy of the actual weak-gradient class, in real coordinates. -/
def classEnergy (w : ScalarW11) : ℝ :=
  ∫ t in (0 : ℝ)..1, integrand t
    ((coordinateLp intervalDomain one ((0 : Fin 1), (0 : Fin 1))
      (gradient intervalDomain 1 one w)) (WithLp.toLp 2 (fun _ : Fin 1 => t)))

namespace Expected

def RepresentativeExistence : Prop :=
  ∀ w : ScalarW11, ∃ f : ℝ → ℝ,
    AbsolutelyContinuousOnInterval f 0 1 ∧ Represents w f

def RepresentativeLift : Prop :=
  ∀ f : ℝ → ℝ, AbsolutelyContinuousOnInterval f 0 1 →
    ∃ w : ScalarW11, Represents w f

def RepresentativeUniqueness : Prop :=
  ∀ (w : ScalarW11) (f g : ℝ → ℝ),
    AbsolutelyContinuousOnInterval f 0 1 → AbsolutelyContinuousOnInterval g 0 1 →
    Represents w f → Represents w g → EqOn f g (Icc (0 : ℝ) 1)

def EnergyRepresentation : Prop :=
  ∀ (w : ScalarW11) (f : ℝ → ℝ), Represents w f → classEnergy w = energy f

def NormIdentification : Prop :=
  ∀ (w : ScalarW11) (f : ℝ → ℝ),
    AbsolutelyContinuousOnInterval f 0 1 → Represents w f → ‖w‖ = sourceNorm f

def ConvexGradient : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ConvexOn ℝ univ (integrand x)

def PointwiseGrowth : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| ≤ integrand x z ∧ integrand x z ≤ 2 * |z|

/-- A quantitative coercivity bound on the entire endpoint class. -/
def Coercivity : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → sourceNorm f ≤ 2 * energy f

def StrictBound : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → 1 < energy f

def RampAdmissible : Prop := ∀ n : ℕ, 0 < n → Admissible (ramp n)
def RampEnergy : Prop := ∀ n : ℕ, 0 < n → energy (ramp n) = 1 + 1 / (2 * (n : ℝ))

def Infimum : Prop := IsGLB (energy '' {f | Admissible f}) 1

def Nonattainment : Prop :=
  ¬ ∃ f : ℝ → ℝ, Admissible f ∧ ∀ g : ℝ → ℝ, Admissible g → energy f ≤ energy g

def ClassCoercivity : Prop := ∀ w ∈ boundaryClass, ‖w‖ ≤ 2 * classEnergy w

def ClassStrictBound : Prop := ∀ w ∈ boundaryClass, 1 < classEnergy w

def ClassRamp : Prop := ∀ n : ℕ, 0 < n → ∃ w ∈ boundaryClass,
  Represents w (ramp n) ∧ classEnergy w = 1 + 1 / (2 * (n : ℝ))

def ClassInfimum : Prop := IsGLB (classEnergy '' boundaryClass) 1

def ClassNonattainment : Prop :=
  ¬ ∃ w ∈ boundaryClass, ∀ v ∈ boundaryClass, classEnergy w ≤ classEnergy v

end Expected
end VariationalNotes.Sobolev.LinearGrowth
