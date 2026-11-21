import MathGenome.Internal.Specs.D07.Ch18.FiniteNilpotentNormalSylowMultiplication
import MathGenome.Internal.Specs.D07.Ch18.NormalizerCondition
import MathGenome.Internal.Specs.D07.Ch18.SylowNormalizer
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceClosure
import MathGenome.Internal.Specs.D07.Ch18.PgroupNilpotent

/-!
Independent specification of K07.18.finite_nilpotent, paper.tex:5103–5136.

Nilpotence is termination of the upper central series (`Group.IsNilpotent`),
and the normalizer condition uses strict subgroup inclusion. We reuse the
canonical prime-divisor index and normal-Sylow predicate of the multiplication
prerequisite. The fourth condition specifies multiplication itself: for a
chosen Sylow at each prime divisor, the isomorphism evaluates to the ordered
product in every enumeration and restricts to the given subgroup inclusions.
No normality premise is built into this condition.

The main equivalence uses existence of a choice of Sylow factors. A second
version works for every prescribed choice, showing independence of that
choice. Finiteness is a premise throughout the equivalences. In particular,
the trivial group is included, with an empty prime-divisor index.
-/

namespace Specs.D07.Ch18.FiniteNilpotent

open Specs.D07.Ch18.FiniteNilpotentNormalSylowMultiplication

universe u

def normalizerConditionValue (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, H < ⊤ → H < Subgroup.normalizer (H : Set G)

def sylowMultiplicationValue (G : Type u) [Group G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) : Prop :=
  ∃ e : (∀ p, P p) ≃* G,
    (∀ (x : ∀ p, P p) (l : List (PrimeDivisors G)),
      l.Nodup → l.toFinset = Finset.univ →
      e x = (l.map (fun p => (x p : G))).prod) ∧
    (∀ (p : PrimeDivisors G) (y : P p),
      e (Pi.mulSingle p y) = (y : G))

def NormalizerImpliesNormalSylow : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    normalizerConditionValue G → AllSylowNormal G

def NormalSylowImpliesMultiplication : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G),
    AllSylowNormal G → sylowMultiplicationValue G P

def MultiplicationImpliesNilpotent : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G),
    sylowMultiplicationValue G P → Group.IsNilpotent G

def ChosenFamilyEquivalences : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G),
    List.TFAE [Group.IsNilpotent G, normalizerConditionValue G,
      AllSylowNormal G, sylowMultiplicationValue G P]

def EquivalentConditions : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    List.TFAE [Group.IsNilpotent G, normalizerConditionValue G,
      AllSylowNormal G,
      ∃ P : ∀ p : PrimeDivisors G, Sylow p.val G, sylowMultiplicationValue G P]

def TrivialCase : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Subsingleton G],
    Group.IsNilpotent G ∧ normalizerConditionValue G ∧ AllSylowNormal G ∧
      IsEmpty (PrimeDivisors G) ∧
      ∀ P : ∀ p : PrimeDivisors G, Sylow p.val G, sylowMultiplicationValue G P

end Specs.D07.Ch18.FiniteNilpotent
