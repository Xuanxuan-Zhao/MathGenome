import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Continuous

/-! K03.09.area_length, area assertion (paper.tex:2701–2724).
Rectangles have ordered finite real endpoints and may be degenerate. Inner
families are finite, contained in the set, and have disjoint open interiors;
outer families are arbitrary finite closed rectangle covers. Thus overlaps in
an outer cover are charged with multiplicity. Contents are real suprema/infima
of these genuinely geometric finite sums, not definitions by integral values.
The singleton interval is included. Length is allocated to a separate goal. -/
namespace SingleVariableAnalysis.RectangleArea

structure Rectangle where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  horizontal : left ≤ right
  vertical : bottom ≤ top

def Rectangle.closed (R : Rectangle) : Set (ℝ × ℝ) :=
  Set.Icc R.left R.right ×ˢ Set.Icc R.bottom R.top

def Rectangle.open (R : Rectangle) : Set (ℝ × ℝ) :=
  Set.Ioo R.left R.right ×ˢ Set.Ioo R.bottom R.top

def Rectangle.area (R : Rectangle) : ℝ :=
  (R.right - R.left) * (R.top - R.bottom)

def Rectangle.edge (R : Rectangle) : Set (ℝ × ℝ) := R.closed \ R.open

end SingleVariableAnalysis.RectangleArea

namespace Specs.SingleVariableAnalysis.Ch09.Area
open _root_.SingleVariableAnalysis.RectangleArea
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators

abbrev subgraphType := (ℝ → ℝ) → ℝ → ℝ → Set (ℝ × ℝ)
def subgraphValue : subgraphType := fun f a b =>
  {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc 0 (f p.1)}

abbrev innerFamilyType := Set (ℝ × ℝ) → {n : ℕ} → (Fin n → Rectangle) → Prop
def innerFamilyValue : innerFamilyType := fun S {_} R =>
  (∀ i, (R i).closed ⊆ S) ∧ Pairwise (fun i j => Disjoint (R i).open (R j).open)

abbrev outerFamilyType := Set (ℝ × ℝ) → {n : ℕ} → (Fin n → Rectangle) → Prop
def outerFamilyValue : outerFamilyType := fun S {_} R => S ⊆ ⋃ i, (R i).closed

abbrev sumsType := Set (ℝ × ℝ) → Set ℝ
def innerSumsValue : sumsType := fun S =>
  {v | ∃ (n : ℕ) (R : Fin n → Rectangle), innerFamilyValue S R ∧ v = ∑ i, (R i).area}
def outerSumsValue : sumsType := fun S =>
  {v | ∃ (n : ℕ) (R : Fin n → Rectangle), outerFamilyValue S R ∧ v = ∑ i, (R i).area}

abbrev contentType := Set (ℝ × ℝ) → ℝ
noncomputable def innerContentValue : contentType := fun S => sSup (innerSumsValue S)
noncomputable def outerContentValue : contentType := fun S => sInf (outerSumsValue S)

/-- Finite grid/overlap inequality, including touching edges and zero-area cells.
It applies to any disjoint-interior collection of cells and any finite cover. -/
def gridOverlap : Prop := ∀ {m n : ℕ} (R : Fin m → Rectangle) (Q : Fin n → Rectangle),
  Pairwise (fun i j => Disjoint (R i).open (R j).open) →
  (⋃ i, (R i).closed) ⊆ (⋃ j, (Q j).closed) →
  (∑ i, (R i).area) ≤ ∑ j, (Q j).area

/-- Every finite rectangle edge collection admits a finite cover by open
interiors of rectangles of arbitrarily small total area. -/
def boundaryCorrection : Prop := ∀ {n : ℕ} (R : Fin n → Rectangle)
  (ε : ℝ), 0 < ε → ∃ (m : ℕ) (Q : Fin m → Rectangle),
    (⋃ i, (R i).edge) ⊆ (⋃ j, (Q j).open) ∧ (∑ j, (Q j).area) < ε

/-- Columns have exactly the lower and upper Darboux areas. -/
def darbouxColumns : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (P : PartitionData a b)
  (hf : Ch08.DarbouxSums.boundedOnIntervalValue f a b),
  (∀ x ∈ Set.Icc a b, 0 ≤ f x) →
  Ch08.DarbouxSums.lowerSumValue f P hf ∈ innerSumsValue (subgraphValue f a b) ∧
  Ch08.DarbouxSums.upperSumValue f P hf ∈ outerSumsValue (subgraphValue f a b)

/-- Nonempty bounded families justify both real contents and identify the
geometric sup/inf with the actual Darboux integral, including a=b. -/
def subgraphArea : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Ch03.Continuity.relativeContinuousValue f (Set.Icc a b) →
  (∀ x ∈ Set.Icc a b, 0 ≤ f x) →
  ∃ h : Ch08.Integral.realIntegrableValue f a b,
    (innerSumsValue (subgraphValue f a b)).Nonempty ∧
    (outerSumsValue (subgraphValue f a b)).Nonempty ∧
    BddAbove (innerSumsValue (subgraphValue f a b)) ∧
    BddBelow (outerSumsValue (subgraphValue f a b)) ∧
    innerContentValue (subgraphValue f a b) = Ch08.Integral.realIntegralValue f h ∧
    outerContentValue (subgraphValue f a b) = Ch08.Integral.realIntegralValue f h

end Specs.SingleVariableAnalysis.Ch09.Area
