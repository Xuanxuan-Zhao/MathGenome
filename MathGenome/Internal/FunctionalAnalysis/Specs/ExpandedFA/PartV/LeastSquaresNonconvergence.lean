import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.PicardInstability

/-! The explicit exact-data example `fa2:p5:least-squares-nonconvergence`,
paper.tex 22703–22745. Coordinates start at zero. All scalar quantifiers
include both ℝ and ℂ, with the native conjugate-linear-first inner product. -/
noncomputable section
universe u
namespace ExpandedFA.PartV.LeastSquaresNonconvergence.Spec
open Filter
open scoped Topology

abbrev Space (𝕜 : Type u) [RCLike 𝕜] := PicardInstability.Spec.SquareSpace 𝕜

def q (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

/-- The exceptional values at zero and one, followed by the intentionally
unordered even and odd eigenvalues in the manuscript. -/
def eigenvalue (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j = 1 then 1 else
    if j % 2 = 0 then q ((j / 2) ^ 2) else q (j / 2)

def trials (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : Submodule 𝕜 (Space 𝕜) :=
  Submodule.span 𝕜 ((fun j : ℕ => (lp.single 2 j 1 : Space 𝕜)) '' {j | j ≤ n})

def IsMinimizer {𝕜 : Type u} [RCLike 𝕜]
    (S : Space 𝕜 →L[𝕜] Space 𝕜) (f : Space 𝕜) (n : ℕ) (x : Space 𝕜) : Prop :=
  x ∈ trials 𝕜 n ∧ ∀ y ∈ trials 𝕜 n, ‖S x - f‖ ≤ ‖S y - f‖

/-- The two tail series in the zeroth normal equation are over j > n. -/
def tailSquare (n : ℕ) : ℝ := ∑' j : {j : ℕ // n < j}, q j.val ^ 2

def tailWeighted (n : ℕ) : ℝ :=
  ∑' j : {j : ℕ // n < j}, eigenvalue j.val * q j.val ^ 2

/-- Full structural properties of the *specified* operator, including its
rank-one perturbation formula. No assumed compactness certificate is used. -/
def OperatorConstruction : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (g : Space 𝕜) (A S : Space 𝕜 →L[𝕜] Space 𝕜),
      (∀ j, g j = (q j : 𝕜)) ∧
      (∀ x j, A x j = (eigenvalue j : 𝕜) * x j) ∧
      (∀ x, S x = A x + x 0 • g) ∧
      IsCompactOperator A ∧ IsCompactOperator S ∧
      Function.Injective S ∧ DenseRange S

/-- The finite-dimensional nested trials really have dense union. -/
def TrialProperties : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ n, FiniteDimensional 𝕜 (trials 𝕜 n)) ∧
    Monotone (trials 𝕜) ∧ Dense (⋃ n, (trials 𝕜 n : Set (Space 𝕜)))

/-- The entire example, including uniqueness, solvable exact data, the
coordinate normal equations, the lower bound, and actual divergence along
all even indices (not merely failure of convergence). -/
def LeastSquaresNonconvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (g : Space 𝕜) (A S : Space 𝕜 →L[𝕜] Space 𝕜) (x : ℕ → Space 𝕜),
      (∀ j, g j = (q j : 𝕜)) ∧
      (∀ z j, A z j = (eigenvalue j : 𝕜) * z j) ∧
      (∀ z, S z = A z + z 0 • g) ∧
      IsCompactOperator S ∧ Function.Injective S ∧ DenseRange S ∧
      (∀ n, IsMinimizer S (S g) n (x n) ∧
        ∀ y, IsMinimizer S (S g) n y → y = x n) ∧
      Tendsto (fun n => ‖S (x n) - S g‖) atTop (𝓝 0) ∧
      (∀ n j, 0 < j → j ≤ n →
        (eigenvalue j : 𝕜) * (x n j - g j) = (1 - x n 0) * g j) ∧
      (∀ n, (x n 0 - 1) * ((1 + tailSquare n : ℝ) : 𝕜) =
        (tailWeighted n : 𝕜)) ∧
      (∀ n, 0 < n →
        eigenvalue (n+1) * q (n+1) ^ 2 * q n /
          ((1 + ‖g‖ ^ 2) * eigenvalue n) ≤ ‖x n - g‖) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
        c * (2 : ℝ) ^ ((k : ℤ) ^ 2 - 7 * (k : ℤ) - 2) ≤ ‖x (2*k) - g‖) ∧
      Tendsto (fun k => ‖x (2*k) - g‖) atTop atTop

end ExpandedFA.PartV.LeastSquaresNonconvergence.Spec
