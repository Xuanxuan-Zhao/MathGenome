import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! The L² portion of paper.tex, `fa2:p4:laplace-hankel`, lines 19598–19619.
The restricted Lebesgue measure realizes the positive half-line without imposing
any condition on representatives outside that half-line. Scalars may be real or complex. -/
open MeasureTheory
noncomputable section
namespace ExpandedFA.PartIV.LaplaceL2Spec

abbrev halfLine : Measure ℝ := volume.restrict (Set.Ioi 0)
abbrev Space (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 halfLine

def laplaceKernel (𝕜 : Type) [RCLike 𝕜] (s t : ℝ) : 𝕜 :=
  RCLike.ofReal (Real.exp (-(s * t)))

def laplaceIntegral {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (s : ℝ) : 𝕜 :=
  ∫ t, laplaceKernel 𝕜 s t * f t ∂halfLine

def carlemanIntegral {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (s : ℝ) : 𝕜 :=
  ∫ t, f t / RCLike.ofReal (s + t) ∂halfLine

/-- Full integral compatibility on L² inputs is stronger than compatibility on
the dense bounded compactly supported inputs used in the printed proof.
The product integrability clause explicitly justifies Fubini for the square. -/
def LaplaceTheorem : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    ∃ L H : Space 𝕜 →L[𝕜] Space 𝕜,
      ‖L‖ ≤ Real.sqrt Real.pi ∧
      (∀ f g, inner 𝕜 (L f) g = inner 𝕜 f (L g)) ∧
      H = L.comp L ∧
      ∀ (f : ℝ → 𝕜) (hf : MemLp f 2 halfLine),
        (∀ s > 0, Integrable (fun t => laplaceKernel 𝕜 s t * f t) halfLine) ∧
        (∀ s > 0, Integrable (fun t => f t / RCLike.ofReal (s + t)) halfLine) ∧
        (L (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] laplaceIntegral f ∧
        (H (hf.toLp f) : ℝ → 𝕜) =ᵐ[halfLine] carlemanIntegral f ∧
        (∀ s > 0, Integrable (fun p : ℝ × ℝ =>
          laplaceKernel 𝕜 s p.1 * (laplaceKernel 𝕜 p.1 p.2 * f p.2))
          (halfLine.prod halfLine)) ∧
        (∀ s > 0, laplaceIntegral (laplaceIntegral f) s = carlemanIntegral f s)

end ExpandedFA.PartIV.LaplaceL2Spec
