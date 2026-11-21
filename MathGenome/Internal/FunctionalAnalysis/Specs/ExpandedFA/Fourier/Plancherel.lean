import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Fourier.LpSpace

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexInnerProductSpace

noncomputable section

namespace ExpandedFA.Fourier

abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean d))

/-- The canonical unitary Fourier transform, with the negative 2πi convention. -/
noncomputable def l2Fourier (d : ℕ) : L2 d ≃ₗᵢ[ℂ] L2 d :=
  Lp.fourierTransformₗᵢ (Euclidean d) ℂ

end ExpandedFA.Fourier

namespace Specs.ExpandedFA.Fourier.Plancherel
open _root_.ExpandedFA.Fourier

abbrev unitaryType := ∀ d : ℕ, L2 d ≃ₗᵢ[ℂ] L2 d
noncomputable def unitaryValue : unitaryType := l2Fourier

def extensionType : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d),
  l2Fourier d (f.toLp 2) = (schwartzFourier f).toLp 2

/-- Uniqueness even among all continuous linear extensions. -/
def uniquenessType : Prop := ∀ (d : ℕ) (T : L2 d →L[ℂ] L2 d),
  (∀ f : Schwartz ℂ d, T (f.toLp 2) = (schwartzFourier f).toLp 2) →
  ∀ f, T f = l2Fourier d f

def surjectiveType : Prop := ∀ d : ℕ, Function.Surjective (l2Fourier d)

def integralAgreementType : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ)
    (_h1 : Integrable f) (h2 : MemLp f 2),
  (l2Fourier d (h2.toLp f) : Euclidean d → ℂ) =ᵐ[volume] integralFourier f

/-- The integral transform of an L¹ ∩ L² function is itself square-integrable. -/
def integralMemLpType : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
  Integrable f → MemLp f 2 → MemLp (integralFourier f) 2

def parsevalType : Prop := ∀ (d : ℕ) (f g : L2 d),
  inner ℂ (l2Fourier d f) (l2Fourier d g) = inner ℂ f g

def normType : Prop := ∀ (d : ℕ) (f : L2 d), ‖l2Fourier d f‖ = ‖f‖

/-- Parseval with the manuscript's f * conjugate(g) order. -/
def integralParsevalType : Prop := ∀ (d : ℕ) (f g : L2 d),
  (∫ x, (l2Fourier d f) x * star ((l2Fourier d g) x)) =
    ∫ x, f x * star (g x)

def classicalParsevalType : Prop := ∀ (d : ℕ) (f g : Euclidean d → ℂ),
  Integrable f → Integrable g → MemLp f 2 → MemLp g 2 →
  (∫ ξ, integralFourier f ξ * star (integralFourier g ξ)) =
    ∫ x, f x * star (g x)

def classicalNormType : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
  Integrable f → MemLp f 2 →
  (∫ ξ, ‖integralFourier f ξ‖ ^ 2) = ∫ x, ‖f x‖ ^ 2

end Specs.ExpandedFA.Fourier.Plancherel
