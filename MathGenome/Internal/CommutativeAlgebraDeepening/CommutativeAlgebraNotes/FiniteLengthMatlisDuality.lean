import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Type
import Mathlib.RingTheory.Length

/-! The finite-length part of Proposition M02. -/

namespace CommutativeAlgebraNotes

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] (E : ResidueFieldEnvelope R)
variable (X : Type v) [AddCommGroup X] [Module R X]

private theorem matlisDual_length_of_simple [IsSimpleModule R X] :
    Module.length R (MatlisDualModule E X) = Module.length R X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule R X)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  obtain ⟨toSocle, _⟩ := AdvCommAlg.Depth.homSocleEquiv R E.carrier
  obtain ⟨fromResidue, _⟩ := residueFieldEnvelope_socle_equiv E
  let toResidue := (toSocle.trans fromResidue.symm).restrictScalars R
  exact (LinearEquiv.congrLeft E.carrier R e).length_eq.trans
    (toResidue.length_eq.trans e.length_eq.symm)

/-- The Matlis dual preserves composition length on finite-length modules. -/
theorem matlisDual_length (hX : IsFiniteLength R X) :
    Module.length R (MatlisDualModule E X) = Module.length R X := by
  induction hX with
  | of_subsingleton => simp [MatlisDualModule]
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨hinj, hexact, hsurj⟩ := matlisDualMap_shortExact E N.subtype N.mkQ
      N.subtype_injective (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
    calc
      Module.length R (MatlisDualModule E M) =
          Module.length R (MatlisDualModule E (M ⧸ N)) +
            Module.length R (MatlisDualModule E N) :=
        Module.length_eq_add_of_exact _ _ hinj hsurj hexact
      _ = Module.length R (M ⧸ N) + Module.length R N := by
        rw [matlisDual_length_of_simple E, ih]
      _ = Module.length R M :=
        (add_comm _ _).trans (Module.length_eq_add_of_exact N.subtype N.mkQ
          N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)).symm

/-- The Matlis dual of a finite-length module again has finite length. -/
theorem matlisDual_isFiniteLength (hX : IsFiniteLength R X) :
    IsFiniteLength R (MatlisDualModule E X) := by
  apply Module.length_ne_top_iff.mp
  rw [matlisDual_length E X hX]
  exact Module.length_ne_top_iff.mpr hX

/-- The canonical evaluation map of a finite-length module is an isomorphism. -/
theorem matlisEvaluation_equiv (hX : IsFiniteLength R X) :
    ∃ e : X ≃ₗ[R] MatlisDualModule E (MatlisDualModule E X),
      e.toLinearMap = matlisEvaluation E X := by
  have hd := matlisDual_isFiniteLength E X hX
  have ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (matlisDual_isFiniteLength E _ hd)
  have hinj := matlisEvaluation_injective E X
  have hsurj : Function.Surjective (matlisEvaluation E X) := by
    apply LinearMap.range_eq_top.mp
    by_contra hproper
    have hlt := Submodule.length_lt hproper
    rw [← (LinearEquiv.ofInjective _ hinj).length_eq, matlisDual_length E _ hd,
      matlisDual_length E X hX] at hlt
    exact (lt_irrefl _) hlt
  exact ⟨LinearEquiv.ofBijective (matlisEvaluation E X) ⟨hinj, hsurj⟩, rfl⟩

/-- Evaluation commutes with every linear map, including those of finite-length modules. -/
theorem matlisEvaluation_naturality {X : Type v} {Y : Type w}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    (matlisDualMap E (matlisDualMap E f)).comp (matlisEvaluation E X) =
      (matlisEvaluation E Y).comp f :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

end CommutativeAlgebraNotes
