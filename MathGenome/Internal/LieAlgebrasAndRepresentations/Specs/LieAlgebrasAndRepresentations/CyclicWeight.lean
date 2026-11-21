import Mathlib.Algebra.Lie.LieTheorem

/-!
The cyclic-space calculation, LA-cyclic-weight, source
notes/005/lie-algebras-and-representations.tex, lines 654–686.
The chapter assumes finite-dimensional representations, and this lemma assumes
characteristic zero, but does not require algebraic closure or solvability.
Take the acting algebra to be b + kx and b to be its ideal. We state the result
for any acting Lie algebra and any of its ideals, which includes that case.
The weight is an arbitrary function: linearity need not be assumed.

The scalar-action conclusion below is stronger than constant diagonal on the
cyclic basis: it says that the restriction of each b to W is lambda(b) times
the identity. In particular its matrix in every basis of W is that scalar
matrix. This stronger conclusion follows after commutator vanishing, even
though the source first proves triangularity and then uses a trace argument.
-/

universe u v w t

namespace Specs.LieAlgebrasAndRepresentations.CyclicWeight

variable {k : Type u} [Field k]
variable {G : Type v} [LieRing G] [LieAlgebra k G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [LieRingModule G V] [LieModule k G V]

/-- The original subspace k[x]v, with the action of x iterated n times. -/
def cyclicSpace (x : G) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun n : ℕ => (LieModule.toEnd k G V x ^ n) v)

/-- All four conclusions of the cyclic-space calculation. The scalar-action conclusion
implies the claimed constant diagonal, in every basis. -/
def cyclic_weight_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V]
    (B : LieIdeal k G) (x : G) (χ : B → k) (v : V),
    v ≠ 0 → (∀ b : B, ⁅b, v⁆ = χ b • v) →
    (∀ z ∈ cyclicSpace (k := k) x v, ⁅x, z⁆ ∈ cyclicSpace (k := k) x v) ∧
    (∀ b : B, ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ ∈ cyclicSpace (k := k) x v) ∧
    (∀ b : B, ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ = χ b • z) ∧
    (∀ b : B, χ ⁅x, b⁆ = 0) ∧
    (∀ z : V, (∀ b : B, ⁅b, z⁆ = χ b • z) →
      ∀ b : B, ⁅b, ⁅x, z⁆⁆ = χ b • ⁅x, z⁆)

/-- Explicit matrix entries in any basis of the cyclic space: in particular,
this gives the constant diagonal in the source's cyclic basis. -/
def cyclic_weight_diagonal_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V]
    (B : LieIdeal k G) (x : G) (χ : B → k) (v : V),
    v ≠ 0 → (∀ b : B, ⁅b, v⁆ = χ b • v) →
    ∀ {ι : Type t} [DecidableEq ι]
      (e : Module.Basis ι k (cyclicSpace (k := k) x v)) (b : B),
    ∃ hb : ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ ∈ cyclicSpace (k := k) x v,
      ∀ i j : ι,
        e.repr ⟨⁅b, (e j : V)⁆, hb (e j) (e j).property⟩ i =
          if i = j then χ b else 0

end Specs.LieAlgebrasAndRepresentations.CyclicWeight
