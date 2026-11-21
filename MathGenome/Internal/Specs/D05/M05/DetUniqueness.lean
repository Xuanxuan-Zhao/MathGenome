import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-!
Independent statements for paper.tex:804–811, K05.05.det_uniqueness.
The scalars are any commutative ring with identity. Slots index columns:
`v j i` is the entry in row `i` of column `j`. All natural sizes, including
zero, are quantified without a nontriviality or characteristic assumption.
-/

namespace D05.Specs.DetUniqueness

/-- Every alternating form is its standard-basis value times the column
Leibniz determinant, without a normalization hypothesis. -/
def general_formula : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (f : AlternatingMap R (Fin n → R) R (Fin n))
    (v : Fin n → (Fin n → R)),
    f v = f (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) *
      D05.M05.determinant (Matrix.of (fun i j => v j i))

/-- The same assertion for an unbundled multilinear form with precisely the
paper's repeated-input vanishing condition. -/
def multilinear_formula : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => Fin n → R) R),
    D05.Specs.Alternating.IsAlternating f →
    ∀ (v : Fin n → (Fin n → R)),
    f v = f (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) *
      D05.M05.determinant (Matrix.of (fun i j => v j i))

/-- Existence of the determinant as a normalized alternating form, and
uniqueness among all normalized alternating forms. -/
def normalized_unique : Prop :=
  ∀ (R : Type*) [CommRing R] (n : ℕ),
    ∃ f : AlternatingMap R (Fin n → R) R (Fin n),
      (∀ v : Fin n → (Fin n → R),
        f v = D05.M05.determinant (Matrix.of (fun i j => v j i))) ∧
      f (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) = 1 ∧
      ∀ g : AlternatingMap R (Fin n → R) R (Fin n),
        g (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) = 1 → g = f

/-- At size zero every form is determined by its value on the unique empty
tuple, and the empty column determinant is one. -/
def empty_case : Prop :=
  ∀ {R : Type*} [CommRing R]
    (f : AlternatingMap R (Fin 0 → R) R (Fin 0))
    (v : Fin 0 → (Fin 0 → R)),
    f v = f (fun j i => (1 : Matrix (Fin 0) (Fin 0) R) i j) ∧
      D05.M05.determinant (Matrix.of (fun i j => v j i)) = 1

end D05.Specs.DetUniqueness
