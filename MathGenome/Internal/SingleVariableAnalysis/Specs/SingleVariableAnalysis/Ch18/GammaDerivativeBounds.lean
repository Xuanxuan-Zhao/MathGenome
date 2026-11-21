import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-! The domination and endpoint-tail part of K03.18.gamma_regular
(paper.tex:4108–4117). The order is a natural number, including zero.
Parameters range over the entire closed interval [α,β], with 0 < α ≤ β.
All convergence below is convergence of proper Darboux truncations, separately
at zero and at infinity; absolute convergence uses the absolute integrand.
The actual differentiation and smoothness conclusions are separate obligations.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
open Set
namespace E
export Ch10.OneEndpoint (leftConvergesValue rightConvergesValue
  leftHasIntegralValue rightHasIntegralValue)
end E
namespace U
export Ch14.UniformImproper (leftUniformConvergesValue rightUniformConvergesValue)
end U

abbrev kernelType := ℕ → ℝ → ℝ → ℝ
/-- The kth parameter-derivative integrand, using the existing Gamma kernel. -/
def kernelValue : kernelType := fun k s t =>
  GammaDefinition.gammaKernelValue s t * (Real.log t) ^ k

abbrev zeroMajorantType := ℝ → ℕ → ℝ → ℝ
def zeroMajorantValue : zeroMajorantType := fun α k t =>
  t ^ (α - 1) * |Real.log t| ^ k

def infinityMajorant (C t : ℝ) : ℝ := C * Real.exp (-t / 2)

def zeroBound : Prop := ∀ (k : ℕ) (α s t : ℝ), α ≤ s → 0 < t → t ≤ 1 →
  |kernelValue k s t| ≤ zeroMajorantValue α k t

def infinityBound : Prop := ∀ (k : ℕ) (β : ℝ), ∃ C : ℝ, 0 < C ∧
  ∀ (s t : ℝ), s ≤ β → 1 ≤ t → |kernelValue k s t| ≤ infinityMajorant C t

/-- Both displayed dominating functions have genuine improper integrals. -/
def majorantConvergence : Prop :=
  (∀ (α : ℝ) (k : ℕ), 0 < α →
    E.leftConvergesValue .real (zeroMajorantValue α k) (0 : WithBot ℝ) 1) ∧
  (∀ C : ℝ, E.rightConvergesValue .real (infinityMajorant C) 1 ⊤)

def absoluteConvergence : Prop := ∀ (k : ℕ) (s : ℝ), 0 < s →
  E.leftConvergesValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ)) (0 : WithBot ℝ) 1 ∧
  E.rightConvergesValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ)) 1 ⊤

/-- Signed and absolute endpoint integrals converge uniformly in s, with
independent truncation thresholds at the two ends. -/
def uniformAtOrder (k : ℕ) (α β : ℝ) : Prop :=
  U.leftUniformConvergesValue .real (Icc α β)
    (fun t s => kernelValue k s.val t) (0 : WithBot ℝ) 1 ∧
  U.rightUniformConvergesValue .real (Icc α β)
    (fun t s => kernelValue k s.val t) 1 ⊤ ∧
  U.leftUniformConvergesValue .real (Icc α β)
    (fun t s => (|kernelValue k s.val t| : ℝ)) (0 : WithBot ℝ) 1 ∧
  U.rightUniformConvergesValue .real (Icc α β)
    (fun t s => (|kernelValue k s.val t| : ℝ)) 1 ⊤

def uniformConvergence : Prop := ∀ (k : ℕ) (α β : ℝ), 0 < α → α ≤ β →
  uniformAtOrder k α β

/-- Quantitative domination of the actual improper absolute tails. No linked
zero/infinity limiting process or cancellation is used. -/
def tailBounds : Prop := ∀ (k : ℕ) (α β : ℝ), 0 < α → α ≤ β →
  ∃ C : ℝ, 0 < C ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ G : ℝ, 0 ≤ G ∧
      E.leftHasIntegralValue .real (zeroMajorantValue α k) (0 : WithBot ℝ) η G ∧
      ∀ s ∈ Icc α β, ∃ L : ℝ,
        E.leftHasIntegralValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ)) (0 : WithBot ℝ) η L ∧
        0 ≤ L ∧ L ≤ G) ∧
    (∀ R : ℝ, 1 ≤ R → ∃ G : ℝ, 0 ≤ G ∧
      E.rightHasIntegralValue .real (infinityMajorant C) R ⊤ G ∧
      ∀ s ∈ Icc α β, ∃ L : ℝ,
        E.rightHasIntegralValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ)) R ⊤ L ∧
        0 ≤ L ∧ L ≤ G)

/-- The actual absolute tails tend to zero uniformly in the parameter.
The small-zero and large-infinity cutoffs are chosen independently. -/
def uniformlySmallTails : Prop := ∀ (k : ℕ) (α β : ℝ), 0 < α → α ≤ β →
  ∀ ε : ℝ, 0 < ε →
    (∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ η : ℝ, 0 < η → η < δ → ∀ s ∈ Icc α β, ∃ L : ℝ,
        E.leftHasIntegralValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ))
          (0 : WithBot ℝ) η L ∧ 0 ≤ L ∧ L < ε) ∧
    (∃ R₀ : ℝ, 1 ≤ R₀ ∧
      ∀ R : ℝ, R₀ < R → ∀ s ∈ Icc α β, ∃ L : ℝ,
        E.rightHasIntegralValue .real (fun t : ℝ => (|kernelValue k s t| : ℝ))
          R ⊤ L ∧ 0 ≤ L ∧ L < ε)

/-- In particular the same statements hold for the next order, as required
when differentiating the kth integral. -/
def orderAndNext : Prop := ∀ (k : ℕ) (α β : ℝ), 0 < α → α ≤ β →
  uniformAtOrder k α β ∧ uniformAtOrder (k + 1) α β

end Specs.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
