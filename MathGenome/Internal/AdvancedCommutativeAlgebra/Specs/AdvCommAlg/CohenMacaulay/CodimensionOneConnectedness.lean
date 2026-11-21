import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! Independent CM-16 statements, paper.tex:3836–3886.
The two radical noncontainments express incomparability. Nilpotence is
ideal nilpotence, and no reducedness assumption is made. The final statement
uses arbitrary nonempty disjoint families covering the minimal primes;
Noetherianity makes these families finite. Their intersections define the
unions of the corresponding irreducible components, and the sum defines
the intersection of those unions. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def grade_sup_le_oneType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R), I ≠ ⊤ → J ≠ ⊤ →
    (¬ I.radical ≤ J.radical) → (¬ J.radical ≤ I.radical) →
    IsNilpotent (I ⊓ J) → AdvCommAlg.Depth.Specs.gradeValue (I ⊔ J) R ≤ 1

def height_sup_le_oneType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R), I ≠ ⊤ → J ≠ ⊤ →
    (¬ I.radical ≤ J.radical) → (¬ J.radical ≤ I.radical) →
    IsNilpotent (I ⊓ J) → RingSerreConditionValue R 2 → (I ⊔ J).height ≤ 1

def height_sup_le_one_of_cohenMacaulayRingType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R), I ≠ ⊤ → J ≠ ⊤ →
    (¬ I.radical ≤ J.radical) → (¬ J.radical ≤ I.radical) →
    IsNilpotent (I ⊓ J) → CohenMacaulayRingValue R → (I ⊔ J).height ≤ 1

def height_partition_minimalPrimes_le_oneType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (s t : Set (Ideal R)), s.Nonempty → t.Nonempty → Disjoint s t →
    s ∪ t = minimalPrimes R → RingSerreConditionValue R 2 →
      (sInf s ⊔ sInf t).height ≤ 1

end AdvCommAlg.CohenMacaulay.Specs
