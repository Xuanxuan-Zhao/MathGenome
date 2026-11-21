import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.Combinatorics.Matroid.Minor.Contract

/-! Independent statements for the complement-basis and minor assertions of
`paper.tex`, W67. All matroids have the same ambient type, and every complement
is relative to the current ground. The dual rank formula is allocated separately
to `matroid_dual_rank`. No nonemptiness assumptions are made on grounds or sets.
-/

namespace FiniteCombinatorics.Matroid.Expected

open Set
open scoped _root_.Matroid
universe u

def dualGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], M✶.E = M.E

def dualFinite : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], M✶.Finite

/-- The entire dual basis family is the family of relative complements. -/
def dualBases : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (D : Set α),
    M✶.IsBase D ↔ ∃ B, M.IsBase B ∧ D = relativeCompl M.E B

/-- The ground condition is essential when testing arbitrary ambient sets. -/
def dualBaseComplement : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (D : Set α),
    M✶.IsBase D ↔ D ⊆ M.E ∧ M.IsBase (relativeCompl M.E D)

def dualInvolution : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], M✶✶ = M

def deletionGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ＼ C).E = relativeCompl M.E C

/-- These are exactly the original independent sets in the retained ground. -/
def deletionIndependent : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C I : Set α),
    (M ＼ C).Indep I ↔ M.Indep I ∧ I ⊆ relativeCompl M.E C

def deletionFinite : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ＼ C).Finite

def contractionDefinition : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    M ／ C = (M✶ ＼ C)✶

def contractionGround : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ／ C).E = relativeCompl M.E C

def contractionFinite : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ／ C).Finite

def contractionDual : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ／ C)✶ = M✶ ＼ C

def deletionDual : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C : Set α),
    (M ＼ C)✶ = M✶ ／ C

end FiniteCombinatorics.Matroid.Expected
