import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.Supercommutator
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.FinCases

namespace Specs.LieNotes.SuperRestricted.SuperMatrices

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.Supercommutator (MulGraded)

universe u

abbrev Mat (k : Type u) := Matrix (Fin 2) (Fin 2) k

variable (k : Type u) [Field k]

def elementType := ∀ (k : Type u) [Field k], Mat k

def zValue : Mat k := Matrix.single 0 0 1 + Matrix.single 1 1 1

def hValue : Mat k := Matrix.single 0 0 1

def eValue : Mat k := Matrix.single 0 1 1

def fValue : Mat k := Matrix.single 1 0 1

def pieceType := ∀ (k : Type u) [Field k], ZMod 2 → Submodule k (Mat k)

/-- Matrices of degree zero are diagonal. Matrices of degree one have zero diagonal. -/
def pieceValue (i : ZMod 2) : Submodule k (Mat k) :=
  if i = 0 then
    (Matrix.entryLinearMap k k 0 1).ker ⊓ (Matrix.entryLinearMap k k 1 0).ker
  else
    (Matrix.entryLinearMap k k 0 0).ker ⊓ (Matrix.entryLinearMap k k 1 1).ker

theorem mem_even {M : Mat k} : M ∈ pieceValue k 0 ↔ M 0 1 = 0 ∧ M 1 0 = 0 := by
  simp [pieceValue]

theorem mem_odd {M : Mat k} : M ∈ pieceValue k 1 ↔ M 0 0 = 0 ∧ M 1 1 = 0 := by
  have h : (1 : ZMod 2) ≠ 0 := by decide
  simp [pieceValue, h]

theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  exact (show ∀ j : ZMod 2, j = 0 ∨ j = 1 by decide) i

def gradingType := ∀ (k : Type u) [Field k], Grading k (Mat k)

/-- The even and odd components split a matrix into its diagonal and off-diagonal entries. -/
def gradingValue : Grading k (Mat k) where
  piece := pieceValue k
  isInternal := by
    have hall : (Set.univ : Set (ZMod 2)) = {0, 1} := by
      ext i
      simpa using parity_cases i
    apply (DirectSum.isInternal_submodule_iff_isCompl _
      (show (0 : ZMod 2) ≠ 1 by decide) hall).2
    refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
    · intro M he ho
      obtain ⟨h01, h10⟩ := (mem_even k).1 he
      obtain ⟨h00, h11⟩ := (mem_odd k).1 ho
      ext i j
      fin_cases i <;> fin_cases j
      exacts [h00, h01, h10, h11]
    · apply top_unique
      intro M _
      let D := Matrix.diagonal fun i => M i i
      have he : D ∈ pieceValue k 0 := by
        simp [mem_even, D]
      have ho : M - D ∈ pieceValue k 1 := by
        simp [mem_odd, D]
      rw [sup_comm]
      simpa only [sub_add_cancel] using Submodule.add_mem_sup ho he

def bracketType := ∀ (k : Type u) [Field k], Mat k →ₗ[k] Mat k →ₗ[k] Mat k

noncomputable def bracketValue : Mat k →ₗ[k] Mat k →ₗ[k] Mat k :=
  Supercommutator.bracketValue (gradingValue k)

def mulGradedType : Prop := ∀ (k : Type u) [Field k], MulGraded (gradingValue k)

def existsGlType : Prop :=
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    ∃ L : LieSuperalgebra k (Mat k), L.grading = gradingValue k ∧ L.bracket = bracketValue k

def generatorType := ∀ (k : Type u) [Field k], Fin 4 → Mat k

def generatorValue : Fin 4 → Mat k := ![zValue k, hValue k, eValue k, fValue k]

def existsBasisType : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ B : Module.Basis (Fin 4) k (Mat k), ∀ i, B i = generatorValue k i

def generatorMemType : Prop :=
  ∀ (k : Type u) [Field k] (i : Fin 4),
    generatorValue k i ∈ (gradingValue k).piece (if i < 2 then 0 else 1)

/-- The rows and columns are in the same order as the basis, namely z, h, e, f. -/
def bracketTable : Fin 4 → Fin 4 → Mat k :=
  ![![0, 0, 0, 0], ![0, 0, eValue k, -fValue k],
    ![0, -eValue k, 0, zValue k], ![0, fValue k, zValue k, 0]]

def bracketTableType : Prop :=
  ∀ (k : Type u) [Field k] (i j : Fin 4),
    bracketValue k (generatorValue k i) (generatorValue k j) = bracketTable k i j

def centralType : Prop :=
  ∀ (k : Type u) [Field k] (M : Mat k),
    bracketValue k (zValue k) M = 0 ∧ bracketValue k M (zValue k) = 0

def supertraceType := ∀ (k : Type u) [Field k], Mat k →ₗ[k] k

def supertraceValue : Mat k →ₗ[k] k :=
  Matrix.entryLinearMap k k 0 0 - Matrix.entryLinearMap k k 1 1

def supertraceBracketType : Prop :=
  ∀ (k : Type u) [Field k] (M N : Mat k),
    supertraceValue k (bracketValue k M N) = 0

def supertraceKerType : Prop :=
  ∀ (k : Type u) [Field k],
    (supertraceValue k).ker = Submodule.span k ({zValue k, eValue k, fValue k} : Set (Mat k))

end Specs.LieNotes.SuperRestricted.SuperMatrices
