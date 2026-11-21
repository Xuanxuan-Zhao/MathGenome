import MathGenome.Internal.Specs.D07.Ch01.FreeGroupUniversalPropertyReducedWords

/-!
Independent specification of `K07.01.free_group_universal_property`,
paper.tex:377–386. The canonical model is the same `FreeGroup S` as in the
upstream reduced-word specification. No finiteness, nonemptiness, or decidable
equality assumption is imposed on the generator type, and the target group may
live in a different universe.

`FreeGroupExists` also states the source's existential conclusion explicitly:
one group and one generator map work for every target group. Its word map
identifies both signs, the empty word, multiplication and inversion, and gives
each element a unique reduced representative in this very same group.
The preliminary normal-quotient lemma is allocated separately to
`support.group_normal_quotient`.
-/

namespace Specs.D07.Ch01.FreeGroupUniversalProperty

universe u v

/-- Every function on the generators extends uniquely to a homomorphism. -/
def UniversalProperty : Prop :=
  ∀ (S : Type u) (H : Type v) [Group H] (f : S → H),
    ∃! φ : FreeGroup S →* H, ∀ s : S, φ (FreeGroup.of s) = f s

/-- The extension evaluates a signed word as the ordered product of its letters. -/
def EvaluationOnWords : Prop :=
  ∀ (S : Type u) (H : Type v) [Group H] (f : S → H)
    (w : List (S × Bool)),
    FreeGroup.lift f (FreeGroup.mk w) =
      (w.map (fun a => if a.2 then f a.1 else (f a.1)⁻¹)).prod

/-- The canonical positive letters generate the whole free group. -/
def GeneratorsGenerate : Prop :=
  ∀ (S : Type u),
    Subgroup.closure (Set.range (FreeGroup.of : S → FreeGroup S)) = ⊤

/-- The existential theorem with universal mapping property and normal forms
on the same group. The Boolean signs are positive (`true`) and negative
(`false`), as in the upstream signed-word specification. -/
def FreeGroupExists : Prop :=
  ∀ (S : Type u),
    ∃ (F : Type u) (gF : Group F) (j : S → F) (word : List (S × Bool) → F),
      letI : Group F := gF
      (∀ (H : Type v) [Group H] (f : S → H),
        ∃! φ : F →* H, ∀ s : S, φ (j s) = f s) ∧
      (∀ s : S, word [(s, true)] = j s ∧ word [(s, false)] = (j s)⁻¹) ∧
      word [] = 1 ∧
      (∀ a b : List (S × Bool), word (a ++ b) = word a * word b) ∧
      (∀ a : List (S × Bool),
        word ((a.map (fun l => (l.1, !l.2))).reverse) = (word a)⁻¹) ∧
      (∀ x : F, ∃! w : List (S × Bool),
        FreeGroupUniversalPropertyReducedWords.Reduced w ∧ word w = x)

/-- The empty generator type is allowed; its free group has only the identity. -/
def EmptyGenerators : Prop :=
  ∀ (S : Type u) [IsEmpty S], ∀ x : FreeGroup S, x = 1

end Specs.D07.Ch01.FreeGroupUniversalProperty
