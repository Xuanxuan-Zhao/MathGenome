import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
Independent specification for the reduced-word part of
`K07.01.free_group_universal_property` (paper.tex:377–396).

We use the canonical `FreeGroup S`, whose words are lists of `S × Bool`.
`true` denotes the positive sign and `false` the negative sign. The
`SignedLetters` obligation identifies these signs with generators and inverses.
`Reduced` explicitly forbids an adjacent inverse pair anywhere in the list.
`CancellationStep` identifies the library's single-step relation with deletion
of exactly such a pair; `FreeGroup.Red` is its reflexive transitive closure.
No decidable equality, finiteness or nonemptiness of `S` is assumed.
-/

namespace Specs.D07.Ch01.FreeGroupUniversalPropertyReducedWords

universe u

/-- No adjacent occurrences of the same generator with opposite signs. -/
def Reduced {S : Type u} (w : List (S × Bool)) : Prop :=
  ∀ (p q : List (S × Bool)) (s : S) (b : Bool),
    w ≠ p ++ (s, b) :: (s, !b) :: q

/-- Both signs represent the stipulated elements of the canonical free group. -/
def SignedLetters : Prop :=
  ∀ (S : Type u) (s : S),
    FreeGroup.mk [(s, true)] = FreeGroup.of s ∧
    FreeGroup.mk [(s, false)] = (FreeGroup.of s)⁻¹

/-- The library's notion of reducedness has the explicit source meaning. -/
def ReducedIff : Prop :=
  ∀ (S : Type u) (w : List (S × Bool)), FreeGroup.IsReduced w ↔ Reduced w

/-- A single cancellation deletes an adjacent inverse pair, in any context. -/
def CancellationStep : Prop :=
  ∀ (S : Type u) (v w : List (S × Bool)),
    FreeGroup.Red.Step v w ↔
      ∃ (p q : List (S × Bool)) (s : S) (b : Bool),
        v = p ++ (s, b) :: (s, !b) :: q ∧ w = p ++ q

/-- Every free-group element has exactly one reduced representative. -/
def UniqueReducedRepresentative : Prop :=
  ∀ (S : Type u) (x : FreeGroup S),
    ∃! w : List (S × Bool), Reduced w ∧ FreeGroup.mk w = x

/-- Every word can be reduced by finitely many adjacent cancellations.
Every reduced result of any such cancellation sequence is the same word. -/
def ReductionNormalForm : Prop :=
  ∀ (S : Type u) (w : List (S × Bool)),
    ∃ v : List (S × Bool), FreeGroup.Red w v ∧ Reduced v ∧
      FreeGroup.mk v = FreeGroup.mk w ∧
      ∀ z : List (S × Bool), FreeGroup.Red w z → Reduced z → z = v

/-- Multiplication concatenates representatives and cancels adjacent inverses. -/
def MultiplicationNormalForm : Prop :=
  ∀ (S : Type u) (x y : FreeGroup S) (v w : List (S × Bool)),
    Reduced v → FreeGroup.mk v = x → Reduced w → FreeGroup.mk w = y →
      ∃! r : List (S × Bool),
        Reduced r ∧ FreeGroup.mk r = x * y ∧ FreeGroup.Red (v ++ w) r

/-- The inverse reduced representative is obtained by reversing order and
changing every sign; no further cancellation is required. -/
def InverseNormalForm : Prop :=
  ∀ (S : Type u) (w : List (S × Bool)), Reduced w →
    Reduced ((w.map (fun a => (a.1, !a.2))).reverse) ∧
      FreeGroup.mk ((w.map (fun a => (a.1, !a.2))).reverse) = (FreeGroup.mk w)⁻¹

/-- The empty word is reduced and represents the identity. -/
def EmptyWord : Prop :=
  ∀ (S : Type u), Reduced ([] : List (S × Bool)) ∧
    FreeGroup.mk ([] : List (S × Bool)) = 1

/-- For an empty generator type, the empty word and the identity are the only
word and group element, respectively. -/
def EmptyGenerators : Prop :=
  ∀ (S : Type u) [IsEmpty S],
    (∀ w : List (S × Bool), w = []) ∧ (∀ x : FreeGroup S, x = 1)

end Specs.D07.Ch01.FreeGroupUniversalPropertyReducedWords
