import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition

/-! Geometric constructibility from a finite initial set (paper.tex:4478).
The canonical geometry and finite-history constructors are shared in the Spec.
-/

namespace D07.Ch15.StraightedgeCompass

/-- The real subfield generated over Q by both coordinates of every initial
point.  Rational scalars use the canonical embedding into the real field. -/
noncomputable def coordinateField (P : InitialData) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Prod.fst '' P.points ∪ Prod.snd '' P.points)

/-- A point is constructible if it is available after finitely many permitted
line/line, line/circle, or circle/circle intersection selections. -/
def IsConstructible (P : InitialData) (p : Point) : Prop :=
  ∃ S : Set Point, Construction P S ∧ p ∈ S

/-- A constructible signed real coordinate is represented by (a,0). -/
def IsConstructibleReal (P : InitialData) (a : ℝ) : Prop :=
  IsConstructible P (a, 0)

/-- Every state reached by a construction is finite. -/
theorem Construction.finite {P : InitialData} {S : Set Point}
    (h : Construction P S) : S.Finite := by
  induction h with
  | initial => exact P.finite_points
  | step _ _ ih => exact ih.insert _

/-- Every initial point is already constructible (zero selections). -/
theorem isConstructible_of_mem {P : InitialData} {p : Point}
    (hp : p ∈ P.points) : IsConstructible P p :=
  ⟨P.points, Construction.initial, hp⟩

/-- Both coordinate projections, rather than only one encoding, lie in K. -/
theorem coordinates_mem_coordinateField {P : InitialData} {p : Point}
    (hp : p ∈ P.points) : p.1 ∈ coordinateField P ∧ p.2 ∈ coordinateField P := by
  constructor
  · exact IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨p, hp, rfl⟩)
  · exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨p, hp, rfl⟩)

end D07.Ch15.StraightedgeCompass
