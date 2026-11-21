import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.RegularQuotient
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Independent statements for CM-08b, paper.tex:3422–3443.
The generating-list hypothesis includes any ordered minimal generating list
of the maximal ideal in dimension `d`. No regularity of that list is assumed.
All prefixes, including zero and the full length, are covered. The second
statement includes the empty regular list. In the last statement the
uniformizer is specified by its defining ideal equality, rather than an
extra assumption about its square or the quotient. -/

universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def regularLocal_prefix_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (x : List R), ringKrullDim R = (d : WithBot ℕ∞) →
    x.length = d → Ideal.ofList x = IsLocalRing.maximalIdeal R →
    ∀ c : ℕ, c ≤ d →
      IsRegularLocalRing (R ⧸ Ideal.ofList (x.take c)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (x.take c)) = ((d - c : ℕ) : WithBot ℕ∞)

def regularLocal_regular_quotient_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (x : List R),
    RingTheory.Sequence.IsRegular R x →
    ∀ hmem : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R,
    letI := AdvCommAlg.Depth.regularQuotientLocalRing x hmem
    LocalCohenMacaulayValue (R ⧸ Ideal.ofList x) (R ⧸ Ideal.ofList x)

def dvr_uniformizer_square_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (t : R), IsLocalRing.maximalIdeal R = Ideal.span {t} →
    RingTheory.Sequence.IsRegular R [t ^ 2] ∧
    ∃ hlocal : IsLocalRing (R ⧸ Ideal.ofList [t ^ 2]),
      ringKrullDim (R ⧸ Ideal.ofList [t ^ 2]) = 0 ∧
      @IsLocalRing.maximalIdeal (R ⧸ Ideal.ofList [t ^ 2]) _ hlocal ≠ ⊥ ∧
      ¬ IsRegularLocalRing (R ⧸ Ideal.ofList [t ^ 2])

end AdvCommAlg.CohenMacaulay.Specs
