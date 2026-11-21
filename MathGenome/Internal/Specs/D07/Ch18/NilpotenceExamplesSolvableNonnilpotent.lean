import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria
import MathGenome.Internal.Specs.D07.Ch15.SolvableClosure
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
Independent specification of the S₃ paragraph of `K07.18.nilpotence_examples`,
paper.tex:5205–5212. S₃ is the full permutation group on three elements and A₃
is its actual alternating subgroup. The lower terms use the shared source
indexing γ₁ = G. The class predicate means upper termination, including c = 0.
-/
namespace Specs.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent

/-- The commutator subgroup of S₃ is A₃, as subgroups of S₃. -/
def DerivedSubgroup : Prop :=
  commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3)

def FirstDerivedTerm : Prop :=
  derivedSeries (Equiv.Perm (Fin 3)) 1 = alternatingGroup (Fin 3)

def SecondDerivedTerm : Prop :=
  derivedSeries (Equiv.Perm (Fin 3)) 2 = ⊥

/-- The lower recurrence, unlike the derived recurrence, remains at A₃. -/
def MixedCommutator : Prop :=
  ⁅alternatingGroup (Fin 3), (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ =
    alternatingGroup (Fin 3)

def LowerCentralTerms : Prop :=
  ∀ i : ℕ, 2 ≤ i →
    CentralSeries.lowerValue (Equiv.Perm (Fin 3)) i = alternatingGroup (Fin 3)

def Solvable : Prop := Group.IsSolvable (Equiv.Perm (Fin 3))

def NotNilpotent : Prop := ¬ Group.IsNilpotent (Equiv.Perm (Fin 3))

/-- No upper central term reaches S₃; no default numerical class is used. -/
def NoClassBound : Prop :=
  ∀ c : ℕ, ¬ NilpotenceCriteria.classAtMostValue (Equiv.Perm (Fin 3)) c

end Specs.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
