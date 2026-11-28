import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SimpleReflections
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The sink numbering and the Coxeter matrix identity for a finite acyclic quiver. -/

open scoped Matrix

-- Vertex, arrow, and coefficient universes are independent.
set_option linter.checkUnivs false

universe u v r

namespace RepTheorySurvey.Quiver.SinkCycleSpec

abbrev IsSinkNumberingType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q], (Q ≃ Fin (Fintype.card Q)) → Prop

abbrev EndpointsAtType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q],
    (Q ≃ Fin (Fintype.card Q)) → ℕ → RM03.Arrow Q → Q × Q

abbrev ReverseIncidentType := ∀ {Q : Type u}, Q → Q × Q → Q × Q

abbrev QuiverAtType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q], (Q ≃ Fin (Fintype.card Q)) → ℕ → Quiver.{max u v} Q

abbrev CoxeterPrefixType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q], (Q ≃ Fin (Fintype.card Q)) →
    ∀ (R : Type r) [CommRing R], ℕ → (Q → R) ≃ₗ[R] (Q → R)

abbrev CoxeterType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q], (Q ≃ Fin (Fintype.card Q)) →
    ∀ (R : Type r) [CommRing R], (Q → R) ≃ₗ[R] (Q → R)

abbrev NumberedMatrixType :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q], (Q ≃ Fin (Fintype.card Q)) →
    ∀ (R : Type r) [CommRing R], Matrix Q Q R

section Orientation

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q]

/-- Rank zero represents the first numbered vertex. -/
def IsSinkNumbering (number : Q ≃ Fin (Fintype.card Q)) : Prop :=
  ∀ a : RM03.Arrow Q, number a.2.1 < number a.1

/-- The current source and target of an original arrow, after processing ranks below `m`.
An arrow is reversed exactly when one of its ends has been processed. -/
noncomputable def endpointsAt (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ)
    (a : RM03.Arrow Q) : Q × Q :=
  open Classical in
  if ((number a.1 : ℕ) < m) ↔ ((number a.2.1 : ℕ) < m) then
    (a.1, a.2.1)
  else
    (a.2.1, a.1)

/-- Interchange the endpoints of an arrow incident to the given vertex. -/
noncomputable def reverseIncident (i : Q) (ends : Q × Q) : Q × Q :=
  open Classical in
  if ends.1 = i ∨ ends.2 = i then ends.swap else ends

/-- The quiver at a given stage, with its arrows labelled by the original arrows. -/
noncomputable abbrev quiverAt (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) : Quiver Q :=
  RM03.quiverOfArrows
    (fun a : RM03.Arrow Q => (endpointsAt number m a).1)
    (fun a : RM03.Arrow Q => (endpointsAt number m a).2)

abbrev NumberingExists : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → ∃ number : Q ≃ Fin (Fintype.card Q), IsSinkNumbering number

abbrev InitialOrientation : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (a : RM03.Arrow Q), endpointsAt number 0 a = (a.1, a.2.1)

abbrev SinkAtEachStep : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {number : Q ≃ Fin (Fintype.card Q)},
    IsSinkNumbering number → ∀ (i : Fin (Fintype.card Q)) (j : Q),
      IsEmpty ((quiverAt number i.val).Hom (number.symm i) j)

abbrev ReverseAtEachStep : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] {number : Q ≃ Fin (Fintype.card Q)},
    IsSinkNumbering number → ∀ (i : Fin (Fintype.card Q)) (a : RM03.Arrow Q),
      endpointsAt number (i.val + 1) a =
        reverseIncident (number.symm i) (endpointsAt number i.val a)

abbrev RestoredOrientation : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (a : RM03.Arrow Q), endpointsAt number (Fintype.card Q) a = (a.1, a.2.1)

end Orientation

section Matrices

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
variable (R : Type r) [CommRing R]

/-- The first `m` reflections in the numbering, acting on the original vertex coordinates.
Once every vertex has been used, further stages keep the result. -/
noncomputable def coxeterPrefix : ℕ → (Q → R) ≃ₗ[R] (Q → R)
  | 0 => LinearEquiv.refl R _
  | m + 1 =>
    if h : m < Fintype.card Q then
      (coxeterPrefix m).trans (SimpleReflectionsSpec.simpleReflection R (number.symm ⟨m, h⟩))
    else
      coxeterPrefix m

/-- The operator applying the simple reflections in increasing rank order. -/
noncomputable def coxeter : (Q → R) ≃ₗ[R] (Q → R) :=
  coxeterPrefix number R (Fintype.card Q)

/-- The standard-coordinate matrix of the full Coxeter operator. -/
noncomputable def coxeterMatrix : Matrix Q Q R :=
  open Classical in
  LinearMap.toMatrix' (coxeter number R).toLinearMap

/-- The lower triangular Euler matrix in the numbering. -/
noncomputable def eulerMatrix : Matrix Q Q R :=
  open Classical in
  fun i j => if i = j then 1 else if number j < number i then
    -(FormsSpec.edgeMultiplicity i j : R) else 0

abbrev CoxeterPrefixStep : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (R : Type r) [CommRing R] (i : Fin (Fintype.card Q)) (x : Q → R),
    coxeterPrefix number R (i.val + 1) x =
      SimpleReflectionsSpec.simpleReflection R (number.symm i) (coxeterPrefix number R i.val x)

abbrev CoxeterPrefixIntCast : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (m : ℕ) (x : FormsSpec.DimensionVector Q),
    coxeterPrefix number ℝ m (fun i => (x i : ℝ)) =
      fun i => (coxeterPrefix number ℤ m x i : ℝ)

abbrev CoxeterMatrixActs : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (R : Type r) [CommRing R] (x : Q → R),
    coxeterMatrix number R *ᵥ x = coxeter number R x

abbrev EulerMatrixDet : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (R : Type r) [CommRing R],
    open Classical in (eulerMatrix number R).det = 1

abbrev EulerMatrixIsUnit : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (R : Type r) [CommRing R], open Classical in IsUnit (eulerMatrix number R)

abbrev EulerMatrixPolarization : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] (number : Q ≃ Fin (Fintype.card Q))
    (R : Type r) [CommRing R], eulerMatrix number R + (eulerMatrix number R)ᵀ =
      FormsSpec.polarizationMatrix R

abbrev CoxeterMatrixFormula : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q]
    (number : Q ≃ Fin (Fintype.card Q)) (R : Type r) [CommRing R] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → IsSinkNumbering number →
    open Classical in
      coxeterMatrix number R = -(eulerMatrix number R)⁻¹ * (eulerMatrix number R)ᵀ

end Matrices

end RepTheorySurvey.Quiver.SinkCycleSpec
