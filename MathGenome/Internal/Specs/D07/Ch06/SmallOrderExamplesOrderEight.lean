import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
Independent specification for the order-eight part of paper.tex:1078–1098.
`DihedralGroup 4` has eight elements; `QuaternionGroup 2` has eight elements.
The latter is identified with the source's matrices by the upstream model.
The cyclic factors use the additive residue groups with multiplicative tags.
-/
namespace Specs.D07.Ch06.SmallOrderExamplesOrderEight

abbrev C (n : ℕ) := Multiplicative (ZMod n)

/-- The five source models, with `C₂³` associated to the right. -/
def Model : Fin 5 → Type
  | 0 => C 8
  | 1 => C 4 × C 2
  | 2 => C 2 × (C 2 × C 2)
  | 3 => DihedralGroup 4
  | 4 => QuaternionGroup 2

instance modelGroup : (i : Fin 5) → Group (Model i)
  | 0 => inferInstanceAs (Group (C 8))
  | 1 => inferInstanceAs (Group (C 4 × C 2))
  | 2 => inferInstanceAs (Group (C 2 × (C 2 × C 2)))
  | 3 => inferInstanceAs (Group (DihedralGroup 4))
  | 4 => inferInstanceAs (Group (QuaternionGroup 2))

instance modelFintype : (i : Fin 5) → Fintype (Model i)
  | 0 => inferInstanceAs (Fintype (C 8))
  | 1 => inferInstanceAs (Fintype (C 4 × C 2))
  | 2 => inferInstanceAs (Fintype (C 2 × (C 2 × C 2)))
  | 3 => inferInstanceAs (Fintype (DihedralGroup 4))
  | 4 => inferInstanceAs (Fintype (QuaternionGroup 2))

instance modelDecidableEq : (i : Fin 5) → DecidableEq (Model i)
  | 0 => inferInstanceAs (DecidableEq (C 8))
  | 1 => inferInstanceAs (DecidableEq (C 4 × C 2))
  | 2 => inferInstanceAs (DecidableEq (C 2 × (C 2 × C 2)))
  | 3 => inferInstanceAs (DecidableEq (DihedralGroup 4))
  | 4 => inferInstanceAs (DecidableEq (QuaternionGroup 2))

/-- Realization of each of the five orders, using its actual group structure. -/
def ModelCardinalities : Prop := ∀ i : Fin 5, Nat.card (Model i) = 8

/-- Pairwise nonisomorphism, together with reflexive isomorphisms. -/
def PairwiseNonisomorphic : Prop :=
  ∀ i j : Fin 5, Nonempty (Model i ≃* Model j) ↔ i = j

/-- Exactly one of the five isomorphism classes, for every finite group of order eight. -/
def Classification : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], Nat.card G = 8 →
    ∃! i : Fin 5, Nonempty (G ≃* Model i)

/-- The source's `a^i b^ε`, with `ε` encoded by a Boolean. -/
def word {G : Type*} [Group G] (a b : G) (p : Fin 4 × Bool) : G :=
  if p.2 then a ^ p.1.val * b else a ^ p.1.val

/-- All relations and unique normal forms; no normal form or cardinality is assumed
in the classification. `q = true` is the quaternion case. -/
def NormalForm {G : Type*} [Group G] (a b : G) (q : Bool) : Prop :=
  orderOf a = 4 ∧ b * a * b⁻¹ = a⁻¹ ∧
  b ^ 2 = (if q then a ^ 2 else 1) ∧
  (∀ g : G, ∃! p : Fin 4 × Bool, g = word a b p)

/-- Both concrete nonabelian models realize precisely the specified relations. -/
def ModelNormalForms : Prop :=
  NormalForm (DihedralGroup.r 1 : DihedralGroup 4) (.sr 0) false ∧
  NormalForm (QuaternionGroup.a 1 : QuaternionGroup 2) (.xa 0) true

/-- Identification from the source normal forms, with both generator images fixed. -/
def NormalFormRecognition : Prop :=
  ∀ (G : Type*) [Group G] (a b : G) (q : Bool), NormalForm a b q →
    if q then
      ∃ e : QuaternionGroup 2 ≃* G, e (.a 1) = a ∧ e (.xa 0) = b
    else
      ∃ e : DihedralGroup 4 ≃* G, e (.r 1) = a ∧ e (.sr 0) = b

/-- The nonabelian case of the exhaustive reduction, including its generators. -/
def NonabelianReduction : Prop :=
  ∀ (G : Type*) [Group G] [Finite G], Nat.card G = 8 →
    (∃ x y : G, x * y ≠ y * x) →
      ∃ (a b : G) (q : Bool), NormalForm a b q

end Specs.D07.Ch06.SmallOrderExamplesOrderEight
