import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.YoungIdempotents
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtClassification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! FR A09, source lines 424–444. All actions are the original Specht actions.
The final contract uses the actual tensor product with the complex sign line.
There is no positivity assumption on n. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Transposing cells, from the transposed shape back to the original shape. -/
def transposeCells {n : ℕ} (p : Partition n) : Cell (transpose p) ≃ Cell p where
  toFun c := ⟨c.val.swap, by
    change c.val.swap ∈ YoungDiagram.ofPartition p
    have h : c.val ∈ YoungDiagram.ofPartition (Nat.Partition.conjugate p) := c.property
    simpa [Nat.Partition.conjugate, YoungDiagram.mem_transpose] using h⟩
  invFun c := ⟨c.val.swap, by
    change c.val.swap ∈ YoungDiagram.ofPartition (Nat.Partition.conjugate p)
    have h : c.val ∈ YoungDiagram.ofPartition p := c.property
    simpa [Nat.Partition.conjugate, YoungDiagram.mem_transpose] using h⟩
  left_inv c := Subtype.ext (Prod.swap_swap c.val)
  right_inv c := Subtype.ext (Prod.swap_swap c.val)

def transposeTableau {n : ℕ} {p : Partition n} (t : Tableau p) : Tableau (transpose p) :=
  (transposeCells p).trans t

/-- Linear extension of g ↦ sgn(g)g. -/
def signAutomorphism (n : ℕ) : GroupAlgebra n →ₗ[ℂ] GroupAlgebra n :=
  (Finsupp.linearCombination ℂ (fun g : SymmetricGroup n =>
    MonoidAlgebra.single g (permutationSign g))).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ : GroupAlgebra n ≃ₗ[ℂ] (SymmetricGroup n →₀ ℂ)).toLinearMap

/-- The one-dimensional sign representation on ℂ. -/
def signRepresentation (n : ℕ) : Representation ℂ (SymmetricGroup n) ℂ where
  toFun g := permutationSign g • LinearMap.id
  map_one' := by
    ext
    simp [permutationSign]
  map_mul' g h := by
    ext
    simp [permutationSign, mul_comm]

def transposeCellsType := ∀ {n : ℕ} (p : Partition n), Cell (transpose p) ≃ Cell p
def transposeTableauType := ∀ {n : ℕ} {p : Partition n}, Tableau p → Tableau (transpose p)
def signAutomorphismType := ∀ n : ℕ, GroupAlgebra n →ₗ[ℂ] GroupAlgebra n
def signRepresentationType := ∀ n : ℕ, Representation ℂ (SymmetricGroup n) ℂ

def transposeTableau_groupsType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    rowSubgroup (transposeTableau t) = columnSubgroup t ∧
    columnSubgroup (transposeTableau t) = rowSubgroup t

def signAutomorphism_singleType : Prop :=
  ∀ {n : ℕ} (g : SymmetricGroup n) (z : ℂ),
    signAutomorphism n (MonoidAlgebra.single g z) =
      MonoidAlgebra.single g (permutationSign g * z)

def signAutomorphism_mulType : Prop :=
  ∀ {n : ℕ} (x y : GroupAlgebra n),
    signAutomorphism n (x * y) = signAutomorphism n x * signAutomorphism n y

def signAutomorphism_involutiveType : Prop :=
  ∀ n : ℕ, Function.Involutive (signAutomorphism n)

/-- The linear sign map is an involutive complex algebra automorphism. -/
def signAutomorphism_algebraEquivType : Prop :=
  ∀ n : ℕ, ∃ θ : GroupAlgebra n ≃ₐ[ℂ] GroupAlgebra n,
    (∀ x, θ x = signAutomorphism n x) ∧ Function.Involutive θ

def signAutomorphism_youngType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    signAutomorphism n (columnAlternator t) = rowSymmetrizer (transposeTableau t) ∧
    signAutomorphism n (rowSymmetrizer t) = columnAlternator (transposeTableau t) ∧
    signAutomorphism n (youngSymmetrizer t) = reverseYoungSymmetrizer (transposeTableau t) ∧
    signAutomorphism n (reverseYoungSymmetrizer t) = youngSymmetrizer (transposeTableau t)

/-- The scalar-action version of the tensor isomorphism, on the same Specht spaces. -/
def transpose_sign_equivType : Prop :=
  ∀ {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule (transpose p))),
    InheritedSpechtAction p σ → InheritedSpechtAction (transpose p) τ →
    ∃ e : SpechtModule p ≃ₗ[ℂ] SpechtModule (transpose p),
      ∀ g v, e (σ g v) = permutationSign g • τ g (e v)

/-- Full equivariant isomorphism with the tensor product by the sign line. -/
def transpose_sign_tensorType : Prop :=
  ∀ {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule (transpose p))),
    InheritedSpechtAction p σ → InheritedSpechtAction (transpose p) τ →
    Nonempty (τ.Equiv (σ.tprod (signRepresentation n)))

end Specs.AdvancedFiniteGroupRepresentations
