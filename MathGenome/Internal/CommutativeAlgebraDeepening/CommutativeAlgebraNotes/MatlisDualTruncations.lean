import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveHullTruncations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteLengthMatlisDuality

namespace CommutativeAlgebraNotes

universe u v w

/-- The residue-field hull is the union of its positive-power truncations, each of which
is the residue-field hull over the corresponding quotient. Matlis duality preserves finite
length, and evaluation gives natural biduality on finite-length modules. -/
theorem matlisDual_finiteLengthTruncations {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (E : ResidueFieldEnvelope R) :
    (⋃ n : {n : ℕ // 1 ≤ n}, (hullTruncation E n.val : Set E.carrier)) = Set.univ ∧
    (∀ (n : ℕ) (hn : 1 ≤ n),
      letI := truncationResidueModule (R := R) n hn
      AdvCommAlg.Gorenstein.IsInjectiveEnvelope (truncationResidueInclusion E n hn)) ∧
    (∀ (X : Type v) [AddCommGroup X] [Module R X], IsFiniteLength R X →
      Module.length R (MatlisDualModule E X) = Module.length R X ∧
      IsFiniteLength R (MatlisDualModule E X) ∧
      ∃ e : X ≃ₗ[R] MatlisDualModule E (MatlisDualModule E X),
        e.toLinearMap = matlisEvaluation E X) ∧
    (∀ {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
      [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y),
      (matlisDualMap E (matlisDualMap E f)).comp (matlisEvaluation E X) =
        (matlisEvaluation E Y).comp f) := by
  refine ⟨Set.eq_univ_of_forall ?_, hullTruncation_isEnvelope E, ?_, ?_⟩
  · intro x
    obtain ⟨n, hn, hx⟩ := exists_mem_hullTruncation E x
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hx⟩
  · intro X _ _ hX
    exact ⟨matlisDual_length E X hX, matlisDual_isFiniteLength E X hX,
      matlisEvaluation_equiv E X hX⟩
  · intro X Y _ _ _ _ f
    exact matlisEvaluation_naturality E f

end CommutativeAlgebraNotes
