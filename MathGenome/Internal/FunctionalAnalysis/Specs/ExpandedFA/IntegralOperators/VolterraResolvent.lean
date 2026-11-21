import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import Specs.ExpandedFA.PartV.VolterraResolvent
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Linarith

/-! Independent scalar specialization of `fa2:p2:kernel-compactness`.
The scalar operator is the existing canonical Banach-valued operator, with
kernel acting by multiplication. Translation is literally x ↦ x-a, with
Jacobian one; there is no normalization by the interval length. -/
noncomputable section
open Set MeasureTheory
open ExpandedFA.PartV
namespace ExpandedFA.IntegralOperators.VolterraResolvent

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- Multiplication by the scalar kernel, using the canonical operator interface. -/
def multiplicationKernel (k : C(volterraTriangle a b, 𝕜)) :
    C(volterraTriangle a b, 𝕜 →L[𝕜] 𝕜) :=
  (⟨ContinuousLinearMap.mul 𝕜 𝕜, (ContinuousLinearMap.mul 𝕜 𝕜).continuous⟩ :
    C(𝕜, 𝕜 →L[𝕜] 𝕜)).comp k

abbrev scalarVolterra (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) :=
  VolterraOperatorSpec.OperatorValue 𝕜 𝕜 a b hab (multiplicationKernel k)

/-- A continuous extension used only outside the actual integration interval. -/
def scalarIntegrand (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜))
    (f : C(VolterraInterval a b, 𝕜)) (x : VolterraInterval a b) (y : ℝ) : 𝕜 :=
  k (volterraRetraction x y) * f (projIcc a b hab y)

/-- The inverse coordinate map is x ↦ x-a, including when a=b. -/
def intervalTranslation (_hab : a ≤ b) :
    VolterraInterval 0 (b-a) ≃ₜ VolterraInterval a b where
  toFun t := ⟨(t : ℝ) + a, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun x := ⟨(x : ℝ) - a, by constructor <;> linarith [x.property.1, x.property.2]⟩
  left_inv t := by ext; simp
  right_inv x := by ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const

def triangleTranslation (a b : ℝ) :
    C(volterraTriangle 0 (b-a), volterraTriangle a b) where
  toFun p := ⟨(p.val.1 + a, p.val.2 + a), by
    rcases p.property with ⟨h₁, h₂, h₃⟩
    exact ⟨by linarith, by linarith, by linarith⟩⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val |>.add continuous_const).prodMk
      (continuous_snd.comp continuous_subtype_val |>.add continuous_const)).subtype_mk _

def translatedKernel (k : C(volterraTriangle a b, 𝕜)) :
    C(volterraTriangle 0 (b-a), 𝕜) := k.comp (triangleTranslation a b)

def translatedFunction (hab : a ≤ b) (f : C(VolterraInterval a b, 𝕜)) :
    C(VolterraInterval 0 (b-a), 𝕜) := f.comp ⟨intervalTranslation hab, (intervalTranslation hab).continuous⟩

namespace Spec

universe u v

/-- Reuse the same compact integral operator on an arbitrary compact Hausdorff Q.
The upstream statement is valid for all finite Borel measures, hence includes
all finite regular Borel measures in the manuscript. -/
def CompactKernels : Prop := ContinuousKernelCompactness.Spec.CanonicalProperties.{u,v}

/-- Endomorphism Neumann series, also on the zero Banach space. -/
def NeumannSeries : Prop := ∀ (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : X →L[𝕜] X), ‖T‖ < 1 →
    IsUnit (1-T) ∧ HasSum (fun n : ℕ => T^n) (Ring.inverse (1-T))

def ScalarFormula : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)),
    (∀ (f : C(VolterraInterval a b, 𝕜)) (x : VolterraInterval a b),
      scalarVolterra hab k f x = ∫ y in a..(x : ℝ), scalarIntegrand hab k f x y) ∧
    (∀ (f : C(VolterraInterval a b, 𝕜)) (x : VolterraInterval a b) (y : ℝ)
      (hy : y ∈ Icc a (x : ℝ)),
      scalarIntegrand hab k f x y =
        k ⟨((x : ℝ),y), hy.1, hy.2, x.property.2⟩ *
          f ⟨y, hy.1, hy.2.trans x.property.2⟩) ∧
    (∀ p, ‖multiplicationKernel k p‖ = ‖k p‖)

def FactorialBound : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (M : ℝ),
    (∀ p, ‖k p‖ ≤ M) → ∀ n : ℕ,
      ‖scalarVolterra hab k ^ n‖ ≤ M^n * (b-a)^n / (n.factorial : ℝ)

def InverseSeries : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜),
    IsUnit (1 - lam • scalarVolterra hab k) ∧
    Summable (fun n : ℕ => ‖lam^n • scalarVolterra hab k ^ n‖) ∧
    HasSum (fun n : ℕ => lam^n • scalarVolterra hab k ^ n)
      (Ring.inverse (1 - lam • scalarVolterra hab k))

/-- This is the source's nondegenerate-interval spectral assertion; no assertion
of nonempty spectrum on a zero state space is introduced. -/
def ComplexSpectrum : Prop := ∀ (a b : ℝ) (hab : a < b)
    (k : C(volterraTriangle a b, ℂ)),
    spectrum ℂ (scalarVolterra hab.le k) = {0}

def SingletonInverse : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a : ℝ) (k : C(volterraTriangle a a, 𝕜)),
    scalarVolterra (le_refl a) k = 0 ∧
    ∀ lam : 𝕜, Ring.inverse (1 - lam • scalarVolterra (le_refl a) k) = 1

/-- The affine coordinate change preserves the supremum norm and conjugates
with the canonical scalar specialization on [0,b-a]. -/
def AffineIdentification : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b),
    ∃ e : C(VolterraInterval a b, 𝕜) ≃ₗᵢ[𝕜] C(VolterraInterval 0 (b-a), 𝕜),
      (∀ f t, e f t = f (intervalTranslation hab t)) ∧
      (∀ g x, e.symm g x = g ((intervalTranslation hab).symm x)) ∧
      ∀ (k : C(volterraTriangle a b, 𝕜)) (f : C(VolterraInterval a b, 𝕜)),
        e (scalarVolterra hab k f) =
          scalarVolterra (sub_nonneg.mpr hab) (translatedKernel k) (e f)

end Spec
end ExpandedFA.IntegralOperators.VolterraResolvent
