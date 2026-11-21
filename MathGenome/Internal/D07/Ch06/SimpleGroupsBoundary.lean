import MathGenome.Internal.Specs.D07.Ch06.SimpleGroupsBoundary
import MathGenome.Internal.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! Elementary simple groups, including the four-letter boundary.

The library's simple-group class has exactly the definition in the source.
For the abelian classification, we apply the cyclicity and prime-cardinality
theorems for commutative simple groups, and the prime-order simplicity theorem
in the converse direction. The alternating simplicity assertions reuse the
assigned upstream result. At four letters the canonical Klein four subgroup
is normal and has order four, whereas the alternating group has order twelve.
-/

namespace D07.Ch06.SimpleGroupsBoundary

universe u

theorem simple_group_characterization :
    Specs.D07.Ch06.SimpleGroupsBoundary.SimpleGroupCharacterization.{u} := by
  intro G _
  exact isSimpleGroup_iff G

theorem trivial_not_simple :
    Specs.D07.Ch06.SimpleGroupsBoundary.TrivialNotSimple.{u} := by
  intro G _ _ h
  haveI : IsSimpleGroup G := h
  exact not_nontrivial G inferInstance

theorem finite_simple_abelian_classification :
    Specs.D07.Ch06.SimpleGroupsBoundary.FiniteSimpleAbelianClassification.{u} := by
  intro G _ _
  constructor
  · rintro ⟨hsimple, hcomm⟩
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    haveI : IsSimpleGroup G := hsimple
    exact ⟨IsSimpleGroup.isCyclic, IsSimpleGroup.prime_card⟩
  · rintro ⟨hcyclic, hprime⟩
    haveI : IsCyclic G := hcyclic
    haveI : Fact (Nat.card G).Prime := ⟨hprime⟩
    exact ⟨isSimpleGroup_of_prime_card rfl,
      fun x y => (IsCyclic.isMulCommutative (α := G)).is_comm.comm x y⟩

theorem prime_order_simple :
    Specs.D07.Ch06.SimpleGroupsBoundary.PrimeOrderSimple.{u} := by
  intro G _ _ p hp hcard
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSimpleGroup_of_prime_card hcard

theorem alternating_simple :
    Specs.D07.Ch06.SimpleGroupsBoundary.AlternatingSimple.{u} :=
  D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity.alternating_simple

theorem alternating_nonabelian :
    Specs.D07.Ch06.SimpleGroupsBoundary.AlternatingNonabelian.{u} :=
  D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity.alternating_nonabelian

theorem alternating_four_normal_witness :
    Specs.D07.Ch06.SimpleGroupsBoundary.AlternatingFourNormalWitness.{u} := by
  classical
  intro X _ hcard
  have hVcard := alternatingGroup.kleinFour_card_of_card_eq_four hcard
  refine ⟨alternatingGroup.kleinFour X, alternatingGroup.normal_kleinFour hcard,
    ?_, ?_, hVcard⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hVcard
    norm_num at hVcard
  · intro htop
    rw [htop, Subgroup.card_top, alternatingGroup.card_of_card_eq_four hcard] at hVcard
    norm_num at hVcard

theorem alternating_four_not_simple :
    Specs.D07.Ch06.SimpleGroupsBoundary.AlternatingFourNotSimple.{u} := by
  classical
  intro X _ hcard hsimple
  haveI : IsSimpleGroup (alternatingGroup X) := hsimple
  obtain ⟨V, hnormal, hbot, htop, _⟩ := alternating_four_normal_witness X hcard
  haveI : V.Normal := hnormal
  exact (Subgroup.Normal.eq_bot_or_eq_top V).elim hbot htop

end D07.Ch06.SimpleGroupsBoundary
