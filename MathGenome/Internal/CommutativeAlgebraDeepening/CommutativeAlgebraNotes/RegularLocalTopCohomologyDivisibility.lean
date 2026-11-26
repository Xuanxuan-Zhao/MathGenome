import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckVanishing
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularDomain
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open Specs.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility

open private localCohomology_map_smul_id from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckVanishing

namespace CommutativeAlgebraNotes

universe u

/-- Multiplication by a nonzero element is surjective on top local cohomology
with support in the maximal ideal of a regular local ring. -/
theorem regularLocalTopCohomology_mul_surjective : mulSurjectiveType.{u} := by
  intro R _ _ d hd c hc
  let : IsDomain R :=
    P103.RegularDomain.domain R ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance)
  let M := ModuleCat.of R R
  let S := M.smulShortComplex c
  let I := IsLocalRing.maximalIdeal R
  have hreg : IsSMulRegular R c := IsSMulRegular.of_ne_zero hc
  have hS : S.ShortExact := hreg.smulShortComplex_shortExact
  -- The support dimension drops along the quotient by a nonzerodivisor.
  have hdrop : Module.supportDim R (QuotSMulTop c R) + 1 ≤ (d : WithBot ℕ∞) := by
    rw [← hd, ← Module.supportDim_self_eq_ringKrullDim]
    exact Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (fun p hp => hreg.notMem_of_mem_minimalPrimes hp)
  have hlt := ENat.WithBot.add_one_le_natCast_iff.mp hdrop
  have hz : IsZero ((localCohomology I (d : ℤ)).obj S.X₃) := by
    change IsZero ((localCohomology I (d : ℤ)).obj (ModuleCat.of R (QuotSMulTop c R)))
    apply grothendieckVanishing I _ (d : ℤ)
    cases d with
    | zero =>
      exact Or.inl ((WithBot.lt_zero_iff_eq_bot _).mp hlt)
    | succ n =>
      have hlt' : Module.supportDim R (QuotSMulTop c R) < (n : WithBot ℕ∞) + 1 := by
        simpa only [Nat.cast_succ] using hlt
      exact Or.inr ⟨n, ENat.WithBot.lt_add_one_iff.mp hlt', by omega⟩
  have he := (localCohomology_exact I hS (d : ℤ)).1
  have hsurj := (ModuleCat.epi_iff_surjective _).mp
    ((ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)).mp he.exact)
  change Function.Surjective ((localCohomology I (d : ℤ)).map (c • 𝟙 M)) at hsurj
  rw [localCohomology_map_smul_id] at hsurj
  exact hsurj

end CommutativeAlgebraNotes
