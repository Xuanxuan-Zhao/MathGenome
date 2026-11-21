import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.PrimeProduct

/-! Independent statements of Theorem 3.10 (paper.tex:1236–1240).
The functions are exactly the prime and prime-power sums fixed in C08a.
The comparison convention is that of paper.tex:861–866, for real x → +∞. -/
namespace P203Specs.Chebyshev

/-- Two eventual inequalities with positive real constants and a real threshold. -/
def Asymp (F G : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → c * G x ≤ F x ∧ F x ≤ C * G x

/-- Big-O bounds the absolute value; the error scale is sqrt x. -/
def PsiSubTheta : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => PrimeProduct.psi x - PrimeProduct.theta x) Real.sqrt

def ThetaAsymp : Prop := Asymp PrimeProduct.theta (fun x => x)

def PsiAsymp : Prop := Asymp PrimeProduct.psi (fun x => x)

def PiCountAsymp : Prop :=
  Asymp (fun x => (PrimeProduct.piCount x : ℝ)) (fun x => x / Real.log x)

end P203Specs.Chebyshev
