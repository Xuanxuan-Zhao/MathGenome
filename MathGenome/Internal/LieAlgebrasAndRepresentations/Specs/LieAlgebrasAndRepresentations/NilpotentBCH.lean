import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalBCH
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import Mathlib.Algebra.Lie.Derivation.Basic

/-! LA-A09, notes/005/lie-algebras-and-representations.tex, lines 559–589.
Finite polynomials below are finite linear combinations of binary bracket trees.
Their tensor interpretations are fixed to the coefficients of the upstream
universal BCH, so an unrelated polynomial group law cannot satisfy this contract.
The scalar parameter in `curve` records substitution along an affine line;
coefficient one is the algebraic directional derivative, over any base field.
There are no topology, dimension, or positive-class hypotheses.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.NilpotentBCH
universe u v w

inductive Word (ι : Type v) : Type v
  | letter : ι → Word ι
  | bracket : Word ι → Word ι → Word ι

def Word.length {ι : Type v} : Word ι → ℕ
  | .letter _ => 1
  | .bracket a b => a.length + b.length

def Word.eval {k : Type u} {ι : Type v} {L : Type w}
    [Field k] [LieRing L] [LieAlgebra k L] (f : ι → L) : Word ι → L
  | .letter i => f i
  | .bracket a b => ⁅a.eval (k := k) f, b.eval (k := k) f⁆

/-- A finite linear combination, with repetitions and zero coefficients allowed. -/
abbrev Polynomial (k : Type u) (ι : Type v) := List (k × Word ι)

def Polynomial.eval {k : Type u} {ι : Type v} {L : Type w}
    [Field k] [LieRing L] [LieAlgebra k L] (f : ι → L) (P : Polynomial k ι) : L :=
  (P.map fun a => a.1 • a.2.eval (k := k) f).sum

def Polynomial.Homogeneous {k : Type u} {ι : Type v}
    (P : Polynomial k ι) (n : ℕ) : Prop := ∀ a ∈ P, a.2.length = n

def Polynomial.component {k : Type u} {ι : Type v}
    (P : Polynomial k ι) (n : ℕ) : Polynomial k ι :=
  P.filter fun a => a.2.length == n

def Polynomial.scale {k : Type u} {ι : Type v} [Field k]
    (r : k) (P : Polynomial k ι) : Polynomial k ι :=
  P.map fun a => (r * a.1, a.2)

def Polynomial.bracket {k : Type u} {ι : Type v} [Field k]
    (P Q : Polynomial k ι) : Polynomial k ι :=
  P.flatMap fun a => Q.map fun b => (a.1 * b.1, Word.bracket a.2 b.2)

/-- Coefficients after replacing each letter f(i) by f(i)+t g(i).
The bracket uses ordinary Cauchy convolution and has no graded signs. -/
def Word.curve {k : Type u} {ι : Type v} {L : Type w}
    [Field k] [LieRing L] [LieAlgebra k L] (f g : ι → L) : Word ι → ℕ → L
  | .letter i, n => if n = 0 then f i else if n = 1 then g i else 0
  | .bracket a b, n => ∑ ij ∈ Finset.antidiagonal n,
      ⁅a.curve (k := k) f g ij.1, b.curve (k := k) f g ij.2⁆

def Polynomial.curve {k : Type u} {ι : Type v} {L : Type w}
    [Field k] [LieRing L] [LieAlgebra k L]
    (f g : ι → L) (P : Polynomial k ι) (n : ℕ) : L :=
  (P.map fun a => a.1 • a.2.curve (k := k) f g n).sum

def Polynomial.directionalDerivative {k : Type u} {ι : Type v} {L : Type w}
    [Field k] [LieRing L] [LieAlgebra k L]
    (f g : ι → L) (P : Polynomial k ι) : L := P.curve f g 1

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A homogeneous expression for a particular coefficient of formal BCH. -/
def RepresentsCoefficient (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : Polynomial k (FormalBCH.Two k)) : Prop :=
  P.Homogeneous n ∧ P.eval (TensorAlgebra.ι k) =
    PowerSeries.coeff n (FormalBCH.universalBCH k).val

/-- Choice has no certificate built in: `coefficientExpected` must prove that
the chosen expression really represents the specified homogeneous coefficient. -/
def coefficientPolynomial (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    Polynomial k (FormalBCH.Two k) :=
  Classical.epsilon (RepresentsCoefficient k n)

def truncatedPolynomial (k : Type u) [Field k] [CharZero k] (c : ℕ) :
    Polynomial k (FormalBCH.Two k) :=
  (List.range (c + 1)).flatMap (coefficientPolynomial k)

def inputMap {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
    (x y : L) : FormalBCH.Two k →ₗ[k] L where
  toFun a := a 0 • x + a 1 • y
  map_add' a b := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' r a := by simp [smul_add, mul_smul]

/-- Evaluation of the formal BCH polynomial through bracket length c. -/
def product {k : Type u} {L : Type v} [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] (c : ℕ) (x y : L) : L :=
  (truncatedPolynomial k c).eval (inputMap x y)

def derivative {k : Type u} {L : Type v} [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] (c : ℕ) (x y dx dy : L) : L :=
  (truncatedPolynomial k c).directionalDerivative (inputMap x y) (inputMap dx dy)

end LieAlgebrasAndRepresentations.NilpotentBCH

namespace Specs.LieAlgebrasAndRepresentations.NilpotentBCH
open _root_.LieAlgebrasAndRepresentations.NilpotentBCH
open _root_.LieAlgebrasAndRepresentations
universe u v w

def polynomialExpectedType := ∀ (k : Type u) [Field k] [CharZero k],
  ℕ → Polynomial k (FormalBCH.Two k)
def polynomialExpectedValue : polynomialExpectedType.{u} := coefficientPolynomial

def productExpectedType := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L], ℕ → L → L → L
def productExpectedValue : productExpectedType.{u,v} := @product

def derivativeExpectedType := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L], ℕ → L → L → L → L → L
def derivativeExpectedValue : derivativeExpectedType.{u,v} := @derivative

def coefficientExpected : Prop := ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ),
  RepresentsCoefficient k n (coefficientPolynomial k n)

/-- Vanishing of every individual longer bracket, with arbitrary parenthesization. -/
def vanishingExpected : Prop := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] (c : ℕ),
  DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
  ∀ (ι : Type w) (f : ι → L) (a : Word ι), c < a.length → a.eval (k := k) f = 0

/-- Cutoffs agree whenever both are at least the asserted nilpotency class. -/
def cutoffExpected : Prop := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] (c d : ℕ), c ≤ d →
  DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
  ∀ x y : L, product (k := k) c x y = product (k := k) d x y

def groupExpected : Prop := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] (c : ℕ),
  DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
  (∀ x y z : L, product (k := k) c (product (k := k) c x y) z = product (k := k) c x (product (k := k) c y z)) ∧
  (∀ x : L, product (k := k) c 0 x = x ∧ product (k := k) c x 0 = x) ∧
  (∀ x : L, product (k := k) c (-x) x = 0 ∧ product (k := k) c x (-x) = 0)

/-- Source and target may have different nilpotency bounds. -/
def naturalityExpected : Prop := ∀ {k : Type u} {L : Type v} {M : Type w}
  [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  (c d : ℕ), DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
  DerivedLowerSeries.lowerCentralSeries_value k M (d + 1) = ⊥ →
  ∀ (F : L →ₗ⁅k⁆ M) (x y : L), F (product (k := k) c x y) = product (k := k) d (F x) (F y)

def derivationExpected : Prop := ∀ {k : Type u} {L : Type v} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] (c : ℕ),
  DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥ →
  ∀ (D : LieDerivation k L L) (x y : L),
    D (product (k := k) c x y) = derivative (k := k) c x y (D x) (D y)

end Specs.LieAlgebrasAndRepresentations.NilpotentBCH
