import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GradeFromLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckVanishing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckNonvanishing

/-! The Cohen–Macaulay criterion via maximal-ideal local cohomology. -/

open CategoryTheory.Limits

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology

universe u

/-- Top local cohomology is nonzero, and the other degrees vanish precisely for
Cohen–Macaulay modules. -/
theorem cohenMacaulay_iff_localCohomology_concentrated : moduleCriterionType.{u} := by
  intro R _ _ _ M _ _
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨d, hd, htop⟩ := grothendieckNonvanishing M
  refine ⟨d, hd, htop, ?_⟩
  have hdepth : AdvCommAlg.Depth.depth R M =
      ⨅ q : {q : ℕ // Nontrivial ((localCohomology m (q : ℤ)).obj M)}, (q.val : ℕ∞) :=
    grade_eq_inf_localCohomology m M
  rw [AdvCommAlg.CohenMacaulay.localCohenMacaulay_iff_sourceDepth,
    AdvCommAlg.CohenMacaulay.dimension, hd]
  change (↑(AdvCommAlg.Depth.depth R M) : WithBot ℕ∞) = ↑(d : ℕ∞) ↔ _
  rw [WithBot.coe_eq_coe, hdepth, ENat.iInf_eq_natCast_iff]
  constructor
  · rintro ⟨_, hleast⟩ q hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · cases q with
      | negSucc _ => exact CategoryTheory.Functor.zero_obj (D := ModuleCat.{u} R) M
      | ofNat n =>
        apply ModuleCat.isZero_iff_subsingleton.mpr
        apply not_nontrivial_iff_subsingleton.mp
        intro hn
        exact (not_le_of_gt (ENat.natCast_lt_natCast.mpr (Int.ofNat_lt.mp hlt)))
          (hleast ⟨n, hn⟩)
    · exact grothendieckVanishing m M q (Or.inr ⟨d, hd.le, hgt⟩)
  · intro hvanish
    refine ⟨⟨⟨d, htop⟩, rfl⟩, fun q => ?_⟩
    have hqd : q.val = d := by
      by_contra hne
      have hz := hvanish (q.val : ℤ) (fun h => hne (Int.ofNat_inj.mp h))
      exact (not_nontrivial_iff_subsingleton.mpr
        (ModuleCat.isZero_iff_subsingleton.mp hz)) q.property
    simp [hqd]

/-- The Cohen–Macaulay criterion for the ring with its own module structure. -/
theorem cohenMacaulayRing_iff_localCohomology_concentrated : ringCriterionType.{u} := by
  intro R _ _ _
  obtain ⟨d, hd, htop, hcriterion⟩ :=
    cohenMacaulay_iff_localCohomology_concentrated (ModuleCat.of R R)
  exact ⟨d, (Module.supportDim_self_eq_ringKrullDim R).symm.trans hd, htop, hcriterion⟩

end CommutativeAlgebraNotes
