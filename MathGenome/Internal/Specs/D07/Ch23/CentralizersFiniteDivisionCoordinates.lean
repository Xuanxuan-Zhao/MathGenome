import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

/-!
Independent specifications for the finite left-coordinate argument in
paper.tex:7370–7385 (K07.23.centralizers).

Despite its name, Mathlib's `Subfield D` for `[DivisionRing D]` is precisely
an inverse-closed unital subring; its definition does not require commutativity.
The canonical `Module E D` is the left action `a • x = (a : D) * x`.
An `Algebra F D` specifies the central field embedding; it is injective since
`F` is a field and `D` is nontrivial. No commutativity of `D` or `E` is assumed.
-/

universe u v

namespace Specs.D07.Ch23.CentralizersFiniteDivisionCoordinates

/-- Restrict the specified central embedding to a division subring containing it. -/
@[instance_reducible]
def centralSubfieldAlgebra (F : Type v) [Field F] (D : Type u) [DivisionRing D]
    [Algebra F D] (E : Subfield D) (hF : ∀ a : F, algebraMap F D a ∈ E) :
    Algebra F E :=
  ((algebraMap F D).codRestrict E.toSubring hF).toAlgebra'
    (fun a x => Subtype.ext (Algebra.commutes a (x : D)))

/-- A finite basis, unique left coordinates, and the cardinality formula.
The rank is positive because the ambient division ring is nonzero. -/
def LeftBasisAndCounting : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Finite D] (E : Subfield D),
    ∃ (r : ℕ) (b : Module.Basis (Fin r) E D),
      r = Module.finrank E D ∧ 0 < r ∧
      (∀ x : D, ∃! a : Fin r → E, x = ∑ i, (a i : D) * b i) ∧
      Nat.card D = Nat.card E ^ r

/-- Dimensions and counts for an arbitrary specified finite central field.
The restricted scalar action on `E` is fixed by the original embedding.
All three ranks are dimensions of finite spaces, never default values for
infinite dimensions. Properness means properness as an actual subring of `D`. -/
def CentralDimensions : Prop :=
  ∀ (F : Type v) [Field F] [Finite F]
    (D : Type u) [DivisionRing D] [Finite D] [Algebra F D]
    (E : Subfield D) (hF : ∀ a : F, algebraMap F D a ∈ E),
    letI := centralSubfieldAlgebra F D E hF
    let q := Nat.card F
    let d := Module.finrank F E
    let n := Module.finrank F D
    let r := Module.finrank E D
    1 < q ∧ 0 < d ∧ 0 < n ∧ 0 < r ∧
      Nat.card E = q ^ d ∧ Nat.card D = q ^ n ∧
      n = d * r ∧ d ∣ n ∧ (E ≠ ⊤ → d < n)

end Specs.D07.Ch23.CentralizersFiniteDivisionCoordinates
