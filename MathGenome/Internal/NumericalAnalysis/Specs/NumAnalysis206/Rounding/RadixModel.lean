import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod

/-! Shared objects and independent statements for paper.tex, Definition W01.
Precision is a natural number constrained to be at least one, equivalently an
integer precision at least one. Exponent limits and the radix are integers.
All powers with possibly negative exponents are powers in the real field.
-/
namespace NumAnalysis206.Rounding

structure RadixFormat where
  β : ℤ
  p : ℕ
  emin : ℤ
  emax : ℤ
  gradual : Bool
  radix_ge_two : 2 ≤ β
  precision_pos : 1 ≤ p
  exponent_order : emin ≤ emax

namespace RadixFormat

noncomputable def positiveNormals (P : RadixFormat) : Finset ℝ := by
  classical
  exact ((Finset.Ico (P.β ^ (P.p - 1)) (P.β ^ P.p)).product
    (Finset.Icc P.emin P.emax)).image
      (fun me : ℤ × ℤ => (me.1 : ℝ) * (P.β : ℝ) ^ me.2)

noncomputable def positiveSubnormals (P : RadixFormat) : Finset ℝ := by
  classical
  exact (Finset.Ico (1 : ℤ) (P.β ^ (P.p - 1))).image
    (fun m : ℤ => (m : ℝ) * (P.β : ℝ) ^ P.emin)

noncomputable def positiveValues (P : RadixFormat) : Finset ℝ := by
  classical
  exact P.positiveNormals ∪ (if P.gradual then P.positiveSubnormals else ∅)

noncomputable def numbers (P : RadixFormat) : Finset ℝ := by
  classical
  exact insert 0 (P.positiveValues ∪ P.positiveValues.image (fun y => -y))

end RadixFormat

/-- Minimum distance, followed by the least real point having that distance.
The proof here only supplies the nonemptiness needed to form a finite minimum.
-/
noncomputable def finiteNearest (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) : ℝ := by
  classical
  let d := (s.image (fun y => |x - y|)).min' (hs.image _)
  exact (s.filter (fun y => |x - y| = d)).min' (by
    obtain ⟨y, hy, hdy⟩ := Finset.mem_image.mp
      (Finset.min'_mem (s.image (fun y => |x - y|)) (hs.image _))
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hdy⟩⟩)

namespace Specs

abbrev SetType := RadixFormat → Set ℝ
noncomputable def FValue : SetType := fun P => (P.numbers : Set ℝ)

abbrev RoundType := RadixFormat → ℝ → ℝ
noncomputable def flValue : RoundType := fun P x =>
  finiteNearest P.numbers (by classical exact ⟨0, by simp [RadixFormat.numbers]⟩) x

abbrev ConstantType := RadixFormat → ℝ
noncomputable def uValue : ConstantType := fun P => (P.β : ℝ) ^ (1 - (P.p : ℤ)) / 2
noncomputable def aminValue : ConstantType := fun P => (P.β : ℝ) ^ ((P.p : ℤ) - 1 + P.emin)
noncomputable def amaxValue : ConstantType := fun P => ((P.β : ℝ) ^ P.p - 1) * (P.β : ℝ) ^ P.emax

def safeDomainValue : SetType := fun P =>
  {x | x = 0 ∨ aminValue P ≤ |x| ∧ |x| ≤ amaxValue P}

/-- An explicit membership specification independent of the finite enumeration. -/
def membership : Prop := ∀ (P : RadixFormat) (x : ℝ),
  x ∈ FValue P ↔ x = 0 ∨
    (∃ m e : ℤ, P.β ^ (P.p - 1) ≤ m ∧ m < P.β ^ P.p ∧
      P.emin ≤ e ∧ e ≤ P.emax ∧
      (x = (m : ℝ) * (P.β : ℝ) ^ e ∨ x = -((m : ℝ) * (P.β : ℝ) ^ e))) ∨
    (P.gradual = true ∧ ∃ m : ℤ, 1 ≤ m ∧ m < P.β ^ (P.p - 1) ∧
      (x = (m : ℝ) * (P.β : ℝ) ^ P.emin ∨
       x = -((m : ℝ) * (P.β : ℝ) ^ P.emin)))

def finite : Prop := ∀ P : RadixFormat, (FValue P).Finite
def zero_mem : Prop := ∀ P : RadixFormat, (0 : ℝ) ∈ FValue P
def fl_mem : Prop := ∀ (P : RadixFormat) (x : ℝ), flValue P x ∈ FValue P

def fl_minimizes : Prop := ∀ (P : RadixFormat) (x y : ℝ),
  y ∈ FValue P → |flValue P x - x| ≤ |y - x|

/-- Among all distance minimizers the smaller real number is selected. -/
def fl_tie : Prop := ∀ (P : RadixFormat) (x y : ℝ),
  y ∈ FValue P → |y - x| = |flValue P x - x| → flValue P x ≤ y

def fl_fixes : Prop := ∀ (P : RadixFormat) (x : ℝ),
  x ∈ FValue P → flValue P x = x

end Specs
end NumAnalysis206.Rounding
