import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.Compact

/-!
Independent statements for the no-common-zero paragraph of K03.16.stone_real,
paper.tex:3931. A `NonUnitalSubalgebra` is closed under real linear
combinations and products, but need not contain the constant function one.
All closures and norms below are in the canonical sup-norm space C(K,ℝ).
The finite sum of squares and zero-constant polynomial approximations record
the construction as well as its density consequence. Empty K is included.
-/
noncomputable section
open scoped Topology

namespace Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero

def sumSquares {K : Set ℝ} (A : NonUnitalSubalgebra ℝ C(K, ℝ))
    (s : Finset A) : C(K, ℝ) :=
  ∑ u ∈ s, (u : C(K, ℝ)) * (u : C(K, ℝ))

def polynomialMap {K : Set ℝ} (p : Polynomial ℝ) (t : C(K, ℝ)) : C(K, ℝ) :=
  ⟨fun x => p.eval (t x), p.continuous.comp t.continuous⟩

def positiveSumSquares : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
    ∃ (s : Finset A) (m M : ℝ), 0 < m ∧ m ≤ M ∧
      ∀ x : K, m ≤ sumSquares A s x ∧ sumSquares A s x ≤ M

def polynomialUnitApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ))
    (t : C(K, ℝ)), t ∈ A →
    ∀ (m M : ℝ), 0 < m → m ≤ M →
    (∀ x : K, m ≤ t x ∧ t x ≤ M) →
    ∀ ε : ℝ, 0 < ε → ∃ p : Polynomial ℝ,
      (Polynomial.X * p).coeff 0 = 0 ∧
      polynomialMap (Polynomial.X * p) t ∈ A ∧
      ‖(1 : C(K, ℝ)) - polynomialMap (Polynomial.X * p) t‖ < ε

def unitInClosure : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
      (1 : C(K, ℝ)) ∈ closure (A : Set C(K, ℝ))

/-- The manuscript's sequence t*pⱼ(t), with an explicit vanishing error. -/
def unitApproximationSequence : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
    ∃ (s : Finset A) (m M : ℝ) (p : ℕ → Polynomial ℝ),
      0 < m ∧ m ≤ M ∧
      (∀ x : K, m ≤ sumSquares A s x ∧ sumSquares A s x ≤ M) ∧
      (∀ n, (Polynomial.X * p n).coeff 0 = 0 ∧
        polynomialMap (Polynomial.X * p n) (sumSquares A s) ∈ A ∧
        ‖(1 : C(K, ℝ)) - polynomialMap (Polynomial.X * p n) (sumSquares A s)‖ <
          1 / ((n : ℝ) + 1)) ∧
      Filter.Tendsto (fun n => polynomialMap (Polynomial.X * p n) (sumSquares A s))
        Filter.atTop (𝓝 (1 : C(K, ℝ)))

def closureEqTop : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) → A.topologicalClosure = ⊤

def uniformClosureEqUniv : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
      closure (A : Set C(K, ℝ)) = Set.univ

def uniformApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
      ∃ g ∈ A, ‖f - g‖ < ε

def pointwiseApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : NonUnitalSubalgebra ℝ C(K, ℝ)),
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
    (∀ x : K, ∃ u ∈ A, u x ≠ 0) →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
      ∃ g ∈ A, ∀ x : K, |f x - g x| < ε

end Specs.SingleVariableAnalysis.Ch16.StoneNoCommonZero
