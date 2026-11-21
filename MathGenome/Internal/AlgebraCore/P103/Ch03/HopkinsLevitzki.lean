import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.HopkinsLevitzki
import MathGenome.Internal.AlgebraCore.P103.Ch03.ArtinianRadical
import Mathlib.RingTheory.HopkinsLevitzki

/-!
The finite-length assertions of paper.tex, Theorem 3.3.

Mathlib's semiprimary induction uses the finite radical filtration:
for a module killed by J, descend scalars to R/J to obtain semisimplicity;
then extend across J M and M/J M, decreasing the nilpotence exponent.
Its chain-condition equivalence therefore needs exactly nilpotence of J
and semisimplicity of R/J, with no commutativity or finite-generation
assumption on J. The upstream Artinian-radical assertions provide those
hypotheses for the regular module.
-/

universe u v

namespace P103.Ch03.HopkinsLevitzki

open P103.Specs.Ch03.HopkinsLevitzki

theorem all_modules_semisimple : all_modules_semisimpleType.{u, v} := by
  intro R M _ _ _ _
  exact IsSemisimpleRing.isSemisimpleModule

theorem semisimple_finite_decomposition : semisimple_finite_decompositionType.{u, v} := by
  intro R M _ _ _ _ h
  have hfin : Module.Finite R M := by
    rcases h with h | h
    · exact ((IsSemisimpleModule.finite_tfae (R := R) (M := M)).out 3 1).mp h
    · exact ((IsSemisimpleModule.finite_tfae (R := R) (M := M)).out 2 1).mp h
  exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M

theorem noetherian_finite_length : noetherian_finite_lengthType.{u, v} := by
  intro R M _ _ _ hn hs hM
  let : IsSemiprimaryRing R := ⟨hs, hn⟩
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨hM, IsSemiprimaryRing.isNoetherian_iff_isArtinian.mp hM⟩

theorem left_regular_finite_length : left_regular_finite_lengthType.{u} := by
  intro R _ _
  let : IsSemiprimaryRing R :=
    ⟨P103.Ch03.ArtinianRadical.quotient_semisimple R,
      P103.Ch03.ArtinianRadical.nilpotent R⟩
  have hN : IsNoetherian R R :=
    IsSemiprimaryRing.isNoetherian_iff_isArtinian.mpr inferInstance
  exact noetherian_finite_length R R
    (P103.Ch03.ArtinianRadical.nilpotent R)
    (P103.Ch03.ArtinianRadical.quotient_semisimple R) hN

theorem left_noetherian : left_noetherianType.{u} := by
  intro R _ _
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp (left_regular_finite_length R)).1

theorem right_regular_finite_length : right_regular_finite_lengthType.{u} := by
  intro R _ _
  exact left_regular_finite_length Rᵐᵒᵖ

theorem right_noetherian : right_noetherianType.{u} := by
  intro R _ _
  exact left_noetherian Rᵐᵒᵖ

end P103.Ch03.HopkinsLevitzki
