import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

/-!
Independent specification of K03.16.stone_complex, paper.tex:3930–3940.
The domain is precisely a compact subset of ℝ, with its induced topology.
A complex `Subalgebra` contains all complex constants. The hypothesis
`∀ u ∈ A, star u ∈ A` is pointwise conjugation closure: the canonical star
on continuous complex maps sends u(x) to conj(u(x)). No density is assumed.
The real algebra is the inverse image of A under the canonical inclusion
C(K,ℝ) → C(K,ℂ). Thus its elements represent exactly A's real-valued maps.
The norm on continuous maps over compact K is the uniform norm. Empty and
singleton K are included; no nonemptiness hypothesis is imposed.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch16.StoneComplex

open scoped Topology

/-- Pointwise inclusion of real continuous functions into complex ones. -/
def realLift (K : Set ℝ) : C(K, ℝ) →ₐ[ℝ] C(K, ℂ) :=
  Complex.ofRealAm.compLeftContinuous ℝ Complex.continuous_ofReal

/-- The canonical continuous real and imaginary components. -/
def realPart (K : Set ℝ) (u : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => (u x).re, Complex.continuous_re.comp u.continuous⟩

def imagPart (K : Set ℝ) (u : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => (u x).im, Complex.continuous_im.comp u.continuous⟩

def realSubalgebraType : Type :=
  ∀ K : Set ℝ, Subalgebra ℂ C(K, ℂ) → Subalgebra ℝ C(K, ℝ)

def realSubalgebraValue : realSubalgebraType := fun K A =>
  (A.restrictScalars ℝ).comap (realLift K)

def realSubalgebraMembership : Prop :=
  ∀ (K : Set ℝ) (A : Subalgebra ℂ C(K, ℂ)) (g : C(K, ℝ)),
    g ∈ realSubalgebraValue K A ↔ realLift K g ∈ A

/-- The inverse image represents exactly the real-valued functions of A. -/
def realSubalgebraRepresentation : Prop :=
  ∀ (K : Set ℝ) (A : Subalgebra ℂ C(K, ℂ)) (f : C(K, ℂ)),
    (f ∈ A ∧ ∀ x : K, (f x).im = 0) ↔
      ∃ g ∈ realSubalgebraValue K A, realLift K g = f

/-- Explicit identification of pointwise star with complex conjugation. -/
def conjugationApply : Prop :=
  ∀ (K : Set ℝ) (u : C(K, ℂ)) (x : K), (star u) x = star (u x)

/-- The two algebraic formulas used to obtain real-valued members of A. -/
def componentFormulas : Prop :=
  ∀ (K : Set ℝ) (u : C(K, ℂ)),
    realLift K (realPart K u) = (2 : ℂ)⁻¹ • (u + star u) ∧
    realLift K (imagPart K u) = (2 * Complex.I)⁻¹ • (u - star u)

def componentsMem : Prop :=
  ∀ (K : Set ℝ) (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) → ∀ u ∈ A,
      realPart K u ∈ realSubalgebraValue K A ∧
      imagPart K u ∈ realSubalgebraValue K A

/-- Separation is witnessed by at least one of the two actual components. -/
def componentSeparation : Prop :=
  ∀ (K : Set ℝ) (u : C(K, ℂ)) (x y : K), u x ≠ u y →
    realPart K u x ≠ realPart K u y ∨ imagPart K u x ≠ imagPart K u y

def realSubalgebraSeparates : Prop :=
  ∀ (K : Set ℝ) (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) →
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      ∀ x y : K, x ≠ y → ∃ g ∈ realSubalgebraValue K A, g x ≠ g y

def uniformApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) →
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      ∀ (f : C(K, ℂ)) (ε : ℝ), 0 < ε → ∃ g ∈ A, ‖f - g‖ < ε

def pointwiseApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) →
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      ∀ (f : C(K, ℂ)) (ε : ℝ), 0 < ε →
        ∃ g ∈ A, ∀ x : K, ‖f x - g x‖ < ε

def uniformClosureEqUniv : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) →
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) →
      closure (A : Set C(K, ℂ)) = Set.univ

def closureEqTop : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℂ C(K, ℂ)),
    (∀ u ∈ A, star u ∈ A) →
    (∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) → A.topologicalClosure = ⊤

end Specs.SingleVariableAnalysis.Ch16.StoneComplex
