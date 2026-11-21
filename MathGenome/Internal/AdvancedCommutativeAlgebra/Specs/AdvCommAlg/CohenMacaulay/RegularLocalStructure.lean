import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Independent statements for the regular-local structure part of CM-08,
paper.tex:3422–3437. A generating list of length equal to dimension is
sufficient; thus the first statement includes every ordered minimal list
in the source, without assuming any regularity of its elements.
The local-ring instance excludes the zero ring. Dimension zero and empty
lists are included. Prefix quotients and the contrasting example are CM-08b.
-/

universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def regular_generatingListType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (x : List R), ringKrullDim R = (d : WithBot ℕ∞) →
    x.length = d → Ideal.ofList x = IsLocalRing.maximalIdeal R →
    RingTheory.Sequence.IsRegular R x

def exists_regular_generatorsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ∃ x : List R, Ideal.ofList x = IsLocalRing.maximalIdeal R ∧
      ringKrullDim R = (x.length : WithBot ℕ∞) ∧
      RingTheory.Sequence.IsRegular R x

def regularLocal_dimension_zero_isFieldType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = 0 → IsField R

def regularLocal_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    LocalCohenMacaulayValue R R

end AdvCommAlg.CohenMacaulay.Specs
