import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.KummerObstructions
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitPlaces
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace LinearAlgebraicGroups.Arithmetic.FiniteKummerSplittingSpec

universe u v w

/-- One finite place outside the prescribed set admits an embedding of the
extension under which all the prescribed Kummer classes vanish. The completion
contains a primitive root of the given order, which is prime to the residue
characteristic. -/
def ExistsPlace : Prop :=
  ∀ {K : Type u} {E : Type w} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (D : GlobalFieldData.{u, v} K) (S : Finset D.FinitePlace)
    (n : ℕ), 1 < n → (n : K) ≠ 0 →
    ∀ P : Set (Kummer.Classes E n), P.Finite →
      ∃ v : D.FinitePlace, v ∉ S ∧
        ∃ e : E →+* D.FiniteCompletion v,
          e.comp (algebraMap K E) = D.embedding (.inl v) ∧
          (∀ c ∈ P, Kummer.map e n c = 1) ∧
          (∃ ζ : D.FiniteCompletion v, IsPrimitiveRoot ζ n) ∧
          (n : IsLocalRing.ResidueField (D.integers v)) ≠ 0

end LinearAlgebraicGroups.Arithmetic.FiniteKummerSplittingSpec
