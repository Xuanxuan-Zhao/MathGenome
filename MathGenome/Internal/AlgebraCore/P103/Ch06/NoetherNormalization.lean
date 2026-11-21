import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.NoetherNormalization
import Mathlib.RingTheory.NoetherNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.PolynomialDimension
import MathGenome.Internal.AlgebraCore.P103.Ch04.IntegralDimension

/-! Noether normalization over arbitrary fields, including the dimension identity.
The library normalization theorem supplies the finite injective map without
any reducedness, domain, or infinite-field assumption. Integral dimension
invariance and polynomial dimension identify the number of variables. -/
namespace P103.Ch06.NoetherNormalization

open P103.Specs.Ch06.NoetherNormalization

universe u v

theorem normalization_map : normalization_mapType.{u,v} := by
  intro k A _ _ _ _ _
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  refine ⟨d, g, hinj, hfin, ?_⟩
  have hdim := P103.Ch04.IntegralDimension.dimension_eq
    (MvPolynomial (Fin d) k) A g.toRingHom hfin.to_isIntegral
  rw [(RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hinj] at hdim
  exact hdim.trans ((ringKrullDim_eq_of_ringEquiv
    (RingEquiv.quotientBot (MvPolynomial (Fin d) k))).trans
    (P103.Ch06.PolynomialDimension.polynomial_dimension k d))

theorem normalization_elements : normalization_elementsType.{u,v} := by
  intro k A _ _ _ _ _
  obtain ⟨d, g, hinj, hfin, hdim⟩ := normalization_map k A
  refine ⟨d, g ∘ MvPolynomial.X, ?_, ?_, hdim⟩
  · rw [algebraicIndependent_iff_injective_aeval, ← MvPolynomial.aeval_unique g]
    exact hinj
  · have hrange : g.range.val.Finite :=
      AlgHom.Finite.of_comp_finite (f := g.rangeRestrict) (g := g.range.val)
        (by simpa using hfin)
    have hfg : Module.Finite g.range A := hrange
    rwa [MvPolynomial.aeval_unique g, MvPolynomial.aeval_range] at hfg

end P103.Ch06.NoetherNormalization
