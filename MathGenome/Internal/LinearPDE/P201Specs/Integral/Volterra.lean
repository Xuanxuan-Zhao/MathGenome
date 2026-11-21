import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.VolterraResolvent
import Specs.ExpandedFA.PartV.VolterraResolventKernel

/-! Independent scalar statements for paper.tex, Theorem 6.2 (4368–4436).
The index n of `iteratedKernel` denotes the paper's k_(n+1). Retractions
extend integrands only outside the displayed integration intervals. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace P201.Integral.Volterra
open ExpandedFA.PartV
open ExpandedFA.IntegralOperators.VolterraResolvent

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- The actual scalar bounded Volterra operator, identified with its integral
in `OperatorFormula`, without extra assumptions on the continuous kernel. -/
abbrev operator (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) := scalarVolterra hab k

/-- This is k_(n+1), starting with k_1=k, independently of operator powers. -/
def iteratedKernel (k : C(volterraTriangle a b, 𝕜)) : ℕ → volterraTriangle a b → 𝕜
  | 0 => k
  | n + 1 => fun p => ∫ r in p.val.2..p.val.1,
      k (kernelLeftPoint p r) * iteratedKernel k n (kernelRightPoint p r)

/-- Reduced resolvent: k_1 + λ k_2 + λ² k_3 + ... . -/
def reducedResolvent (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜)
    (p : volterraTriangle a b) : 𝕜 := ∑' n : ℕ, lam ^ n * iteratedKernel k n p

/-- The equation uses the native scalar integral and continuous data. -/
def IsSolution (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜)
    (g u : C(VolterraInterval a b, 𝕜)) : Prop :=
  ∀ t, u t = g t + lam * ∫ s in a..(t : ℝ), scalarIntegrand hab k u t s

namespace Spec

def OperatorFormula : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)),
    (∀ u t, operator hab k u t = ∫ s in a..(t : ℝ), scalarIntegrand hab k u t s) ∧
    (∀ (u : C(VolterraInterval a b, 𝕜)) (t : VolterraInterval a b)
      (s : ℝ) (hs : s ∈ Icc a (t : ℝ)),
      scalarIntegrand hab k u t s =
        k ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩ *
          u ⟨s, hs.1, hs.2.trans t.property.2⟩) ∧
    ‖operator hab k‖ ≤ ‖k‖ * (b-a)

def Factorial : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)),
    (∀ (n : ℕ) (u : C(VolterraInterval a b, 𝕜)) (t : VolterraInterval a b),
      ‖(operator hab k ^ n) u t‖ ≤
        ‖k‖ ^ n * ‖u‖ * ((t : ℝ)-a) ^ n / (n.factorial : ℝ)) ∧
    (∀ n : ℕ, ‖operator hab k ^ n‖ ≤ ‖k‖ ^ n * (b-a)^n / (n.factorial : ℝ))

def InverseSeries : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜),
    let V := operator hab k
    IsUnit (1 - lam • V) ∧
    Summable (fun n : ℕ => ‖lam ^ n • V ^ n‖) ∧
    HasSum (fun n : ℕ => lam ^ n • V ^ n) (Ring.inverse (1 - lam • V)) ∧
    ‖Ring.inverse (1 - lam • V)‖ ≤ Real.exp (‖lam‖ * ‖k‖ * (b-a))

def Kernels : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)),
    (∀ p, iteratedKernel k 0 p = k p) ∧
    (∀ (p : volterraTriangle a b) (r : ℝ) (hr : r ∈ Icc p.val.2 p.val.1),
      kernelLeftPoint p r = ⟨(p.val.1,r), p.property.1.trans hr.1, hr.2, p.property.2.2⟩ ∧
      kernelRightPoint p r = ⟨(r,p.val.2), p.property.1, hr.1, hr.2.trans p.property.2.2⟩) ∧
    (∀ n, Continuous (iteratedKernel k n)) ∧
    (∀ n p, ‖iteratedKernel k n p‖ ≤
      ‖k‖^(n+1) * (p.val.1-p.val.2)^n / (n.factorial : ℝ)) ∧
    (∀ (n : ℕ) (u : C(VolterraInterval a b, 𝕜)) (t : VolterraInterval a b),
      (operator hab k ^ (n+1)) u t = ∫ s in a..(t : ℝ),
        iteratedKernel k n (volterraRetraction t s) * u (projIcc a b hab s))

def ResolventSeries : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜),
    Continuous (reducedResolvent k lam) ∧
    (∀ p, Summable (fun n : ℕ => ‖lam ^ n * iteratedKernel k n p‖) ∧
      HasSum (fun n : ℕ => lam ^ n * iteratedKernel k n p) (reducedResolvent k lam p)) ∧
    TendstoUniformly (fun N p => ∑ n ∈ Finset.range N, lam ^ n * iteratedKernel k n p)
      (reducedResolvent k lam) atTop ∧
    TendstoUniformly (fun N p => ∑ n ∈ Finset.range N, ‖lam ^ n * iteratedKernel k n p‖)
      (fun p => ∑' n : ℕ, ‖lam ^ n * iteratedKernel k n p‖) atTop ∧
    (∀ p, reducedResolvent k lam p = k p + lam * ∫ r in p.val.2..p.val.1,
      k (kernelLeftPoint p r) * reducedResolvent k lam (kernelRightPoint p r))

def Solvability : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜)) (lam : 𝕜)
    (g : C(VolterraInterval a b, 𝕜)),
    ∃ u : C(VolterraInterval a b, 𝕜), IsSolution hab k lam g u ∧
      (∀ v, IsSolution hab k lam g v → v = u) ∧
      u = Ring.inverse (1 - lam • operator hab k) g ∧
      (∀ t, u t = g t + lam * ∫ s in a..(t : ℝ),
        reducedResolvent k lam (volterraRetraction t s) * g (projIcc a b hab s)) ∧
      (∀ u₀ : C(VolterraInterval a b, 𝕜),
        let T := fun v => g + lam • operator hab k v
        Tendsto (fun n : ℕ => T^[n] u₀) atTop (𝓝 u) ∧
        TendstoUniformly (fun n : ℕ => ⇑(T^[n] u₀)) u atTop)

def BoundaryCases : Prop :=
    (∀ (𝕜 : Type*) [RCLike 𝕜] (a : ℝ) (k : C(volterraTriangle a a, 𝕜)),
      operator (le_refl a) k = 0 ∧
      (∀ n p, iteratedKernel k (n+1) p = 0) ∧
      (∀ (lam : 𝕜) (g u : C(VolterraInterval a a, 𝕜)),
        IsSolution (le_refl a) k lam g u ↔ u = g)) ∧
    (∀ (𝕜 : Type*) [RCLike 𝕜] (a b : ℝ) (hab : a ≤ b)
      (k : C(volterraTriangle a b, 𝕜)),
      (∀ p, reducedResolvent k 0 p = k p) ∧
      (∀ g u, IsSolution hab k 0 g u ↔ u = g) ∧
      Ring.inverse (1 - (0 : 𝕜) • operator hab k) = 1)

end Spec
end P201.Integral.Volterra
