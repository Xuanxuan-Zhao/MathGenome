import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Lie.TraceForm

/-!
LA-J09 (Witt example), notes/005/lie-algebras-and-representations.tex,
lines 5403–5439. The coefficient field is arbitrary of prime characteristic
p > 3. Fin p indexes e_{-1}, ..., e_{p-2}, so index n means e_{n-1}.
The algebra is the actual derivation algebra of k[X]/(X^p).
-/

noncomputable section

open Module

universe u

namespace LieAlgebrasAndRepresentations.Witt

abbrev Truncated (k : Type u) [Field k] (p : ℕ) :=
  AdjoinRoot (Polynomial.X ^ p : Polynomial k)

abbrev Algebra (k : Type u) [Field k] (p : ℕ) :=
  Derivation k (Truncated k p) (Truncated k p)

def t (k : Type u) [Field k] (p : ℕ) : Truncated k p :=
  AdjoinRoot.root (Polynomial.X ^ p : Polynomial k)

/-- Extension by zero implements the source's out-of-range convention. -/
def basisAt {k : Type u} [Field k] {p : ℕ}
    (b : Basis (Fin p) k (Algebra k p)) (n : ℤ) : Algebra k p :=
  if h : 0 ≤ n + 1 ∧ n + 1 < (p : ℤ) then
    b ⟨(n + 1).toNat, by omega⟩ else 0

/-- The source basis, its realization as t^{i+1}D, and its full bracket law. -/
def IsPresentation {k : Type u} [Field k] {p : ℕ}
    (b : Basis (Fin p) k (Algebra k p)) : Prop :=
  (∀ i, b i (t k p) = t k p ^ (i : ℕ)) ∧
  (∀ (i : Fin p) (h : 0 < p) (x : Truncated k p),
    b i x = t k p ^ (i : ℕ) * b ⟨0, h⟩ x) ∧
  (∀ i j : Fin p,
    ⁅b i, b j⁆ = ((j : ℕ) - (i : ℕ) : k) •
      basisAt b ((i : ℕ) + (j : ℕ) - 2 : ℤ))

end LieAlgebrasAndRepresentations.Witt

namespace Specs.LieAlgebrasAndRepresentations.WittKillingBoundary

open LieAlgebrasAndRepresentations.Witt

def presentation_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p], 3 < p →
    ∃ b : Basis (Fin p) k (Algebra k p), IsPresentation b

/-- Simplicity is asserted for actual Lie ideals, with nonabelianness explicit. -/
def simplicity_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p], 3 < p →
    (∃ x y : Algebra k p, ⁅x, y⁆ ≠ 0) ∧
    ∀ I : LieIdeal k (Algebra k p), I = ⊥ ∨ I = ⊤

def killing_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p], 3 < p →
    ∀ x y : Algebra k p, killingForm k (Algebra k p) x y = 0

/-- The example is finite dimensional and violates the characteristic-zero
solvability implication of Cartan's Killing criterion. -/
def boundary_type :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p], 3 < p →
    Module.finrank k (Algebra k p) = p ∧ ¬ LieAlgebra.IsSolvable (Algebra k p)

end Specs.LieAlgebrasAndRepresentations.WittKillingBoundary
