import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions

/-! Independent statements for the products and positive powers assertions of RK-09.
The list order is fixed. The exponent at each position is arbitrary and positive;
choosing exponent one leaves any desired entries unchanged. No finiteness, local,
Noetherian, or nonzero assumption is imposed on the ring or coefficient module. -/
universe u v
namespace AdvCommAlg.RegularSequence.Specs

open RingTheory.Sequence

def weaklyRegular_mulType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p s : List R) (a b : R),
    IsWeaklyRegular M (p ++ a :: s) → IsWeaklyRegular M (p ++ b :: s) →
    IsWeaklyRegular M (p ++ (a * b) :: s)

def regular_mulType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p s : List R) (a b : R),
    IsRegular M (p ++ a :: s) → IsRegular M (p ++ b :: s) →
    IsRegular M (p ++ (a * b) :: s)

def weaklyRegular_powersType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (n : ℕ → ℕ),
    (∀ i, i < x.length → 0 < n i) → IsWeaklyRegular M x →
    IsWeaklyRegular M (x.mapIdx fun i a => a ^ n i)

def regular_powersType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (n : ℕ → ℕ),
    (∀ i, i < x.length → 0 < n i) → IsRegular M x →
    IsRegular M (x.mapIdx fun i a => a ^ n i)

end AdvCommAlg.RegularSequence.Specs
