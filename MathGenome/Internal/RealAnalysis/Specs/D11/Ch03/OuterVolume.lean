import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.OuterCover
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent specification for paper.tex:798–842. Coordinates carry the
Euclidean norm. Endpoints are finite real numbers. `ofReal` gives length zero
for a reversed side; in particular all degenerate boxes are included. -/

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch03

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def openBox {d : ℕ} (a b : Fin d → ℝ) : Set (Point d) :=
  {x | ∀ j, a j < x j ∧ x j < b j}

def closedBox {d : ℕ} (a b : Fin d → ℝ) : Set (Point d) :=
  {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

/-- Endpoint choices are independent in every coordinate. `true` includes
the endpoint and `false` excludes it. -/
def endpointBox {d : ℕ} (a b : Fin d → ℝ) (lower upper : Fin d → Bool) :
    Set (Point d) :=
  {x | ∀ j, (if lower j then a j ≤ x j else a j < x j) ∧
    (if upper j then x j ≤ b j else x j < b j)}

noncomputable def boxContent {d : ℕ} (a b : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ j, ENNReal.ofReal (b j - a j)

/-- The infimum over representations makes the one-box cost intrinsic;
it is infinity off the family of bounded open boxes. -/
noncomputable def boxCost {d : ℕ} (s : Set (Point d)) : ℝ≥0∞ :=
  ⨅ (a : Fin d → ℝ) (b : Fin d → ℝ) (_ : s = openBox a b), boxContent a b

theorem boxCost_empty (d : ℕ) [NeZero d] : boxCost (∅ : Set (Point d)) = 0 := by
  have hbox : openBox (0 : Fin d → ℝ) 0 = ∅ := by
    ext x
    simp only [openBox, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hx
    have h := hx ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    exact (lt_trans h.1 h.2).false
  apply le_antisymm _ zero_le
  exact iInf_le_of_le 0 (iInf_le_of_le 0 (iInf_le_of_le hbox.symm (by
    simp [boxContent, Finset.prod_const, NeZero.ne d])))

end D11.Ch03

namespace Specs.D11.Ch03.OuterVolume

open _root_.D11.Ch03

def outerVolume_type := (d : ℕ) → [NeZero d] → OuterMeasure (Point d)

noncomputable def outerVolume_value : outerVolume_type :=
  fun d _ => OuterMeasure.ofFunction boxCost (boxCost_empty d)

def covering_formula : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    outerVolume_value d E =
      ⨅ (a : ℕ → Fin d → ℝ) (b : ℕ → Fin d → ℝ) (_ : E ⊆ ⋃ n, openBox (a n) (b n)),
        ∑' n, boxContent (a n) (b n)

/-- The displayed formula of the paper, with ordered endpoints so that the
real side lengths and their product are nonnegative. Empty boxes may pad a
finite cover. -/
def ordered_covering_formula : Prop :=
  ∀ (d : ℕ) [NeZero d] (E : Set (Point d)),
    outerVolume_value d E =
      ⨅ (a : ℕ → Fin d → ℝ) (b : ℕ → Fin d → ℝ)
        (_ : ∀ n j, a n j ≤ b n j) (_ : E ⊆ ⋃ n, openBox (a n) (b n)),
        ∑' n, ENNReal.ofReal (∏ j, (b n j - a n j))

def outerVolume_axioms : Prop :=
  ∀ (d : ℕ) [NeZero d],
    outerVolume_value d ∅ = 0 ∧ Monotone (fun E => outerVolume_value d E) ∧
    ∀ E : ℕ → Set (Point d),
      outerVolume_value d (⋃ n, E n) ≤ ∑' n, outerVolume_value d (E n)

def closedBox_volume : Prop :=
  ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ),
    outerVolume_value d (closedBox a b) = boxContent a b

def endpointBox_volume : Prop :=
  ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ) (lower upper : Fin d → Bool),
    outerVolume_value d (endpointBox a b lower upper) = boxContent a b

def side_length_product : Prop :=
  ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ) (_hab : ∀ j, a j ≤ b j)
    (lower upper : Fin d → Bool),
    outerVolume_value d (endpointBox a b lower upper) =
      ENNReal.ofReal (∏ j, (b j - a j))

def degenerate_box : Prop :=
  ∀ (d : ℕ) [NeZero d] (a b : Fin d → ℝ) (lower upper : Fin d → Bool),
    (∃ j, b j ≤ a j) → outerVolume_value d (endpointBox a b lower upper) = 0

end Specs.D11.Ch03.OuterVolume
