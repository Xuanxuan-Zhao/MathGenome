import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationData

/-!
# The specialization field and its residue data

These declarations use the canonical definitions in the independent Specs.
-/

open scoped Polynomial

open Specs.GaloisFormalization.IG.SpecializationData

namespace GaloisFormalization.IG.SpecializationData

noncomputable section

abbrev RegularAt := @Specs.GaloisFormalization.IG.SpecializationData.RegularAt

abbrev PolynomialRegularAt := @Specs.GaloisFormalization.IG.SpecializationData.PolynomialRegularAt

abbrev regularCoefficients := @Specs.GaloisFormalization.IG.SpecializationData.regularCoefficients

abbrev evalRegular := @Specs.GaloisFormalization.IG.SpecializationData.evalRegular

abbrev regularPolynomial := @Specs.GaloisFormalization.IG.SpecializationData.regularPolynomial

abbrev specialize := @Specs.GaloisFormalization.IG.SpecializationData.specialize

abbrev uniformizer := @Specs.GaloisFormalization.IG.SpecializationData.uniformizer

abbrev powerToLaurent := @Specs.GaloisFormalization.IG.SpecializationData.powerToLaurent

abbrev polynomialSeries := @Specs.GaloisFormalization.IG.SpecializationData.polynomialSeries

abbrev polynomialLaurent := @Specs.GaloisFormalization.IG.SpecializationData.polynomialLaurent

abbrev substitution := @Specs.GaloisFormalization.IG.SpecializationData.substitution

abbrev substitutionAlgebra := @Specs.GaloisFormalization.IG.SpecializationData.substitutionAlgebra

abbrev seriesOrder := @Specs.GaloisFormalization.IG.SpecializationData.seriesOrder

abbrev inducedOrder := @Specs.GaloisFormalization.IG.SpecializationData.inducedOrder

abbrev valuationRing := @Specs.GaloisFormalization.IG.SpecializationData.valuationRing

abbrev positiveIdeal := @Specs.GaloisFormalization.IG.SpecializationData.positiveIdeal

abbrev residueField := @Specs.GaloisFormalization.IG.SpecializationData.residueField

abbrev integralSeries := @Specs.GaloisFormalization.IG.SpecializationData.integralSeries

abbrev reduction := @Specs.GaloisFormalization.IG.SpecializationData.reduction

abbrev residueEmbedding := @Specs.GaloisFormalization.IG.SpecializationData.residueEmbedding

abbrev PointEmbedding := @Specs.GaloisFormalization.IG.SpecializationData.PointEmbedding

abbrev decompositionGroup := @Specs.GaloisFormalization.IG.SpecializationData.decompositionGroup

abbrev MatchesRoots := @Specs.GaloisFormalization.IG.SpecializationData.MatchesRoots

/-- The underlying ring homomorphism of the point embedding. -/
abbrev PointEmbedding.toRingHom {k : Type*} [Field k] {ℓ : Type*} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type*} [Field L] [Algebra (RatFunc k) L]
    (i : PointEmbedding (ℓ := ℓ) a L) : L →+* LaurentSeries ℓ :=
  Specs.GaloisFormalization.IG.SpecializationData.PointEmbedding.toRingHom i

@[simp]
theorem powerToLaurent_X : PowerToLaurentX := by
  intro ℓ _
  exact HahnSeries.ofPowerSeries_X

theorem specialize_coeff : SpecializeCoeff := by
  intro k _ a f hf n
  change ((regularPolynomial a f hf).map (evalRegular a)).coeff n = _
  rw [Polynomial.coeff_map]
  change RatFunc.eval (RingHom.id k) a (↑((regularPolynomial a f hf).coeff n)) = _
  have h : (↑((regularPolynomial a f hf).coeff n) : RatFunc k) = f.coeff n :=
    Polynomial.coeff_toSubring f (regularCoefficients a) _
  rw [h]

theorem mem_valuationRing : ValuationRingMembership := by
  intro ℓ _ L _ i x
  rfl

theorem nonnegative_iff_powerSeries : NonnegativeIffPowerSeries :=
  Specs.GaloisFormalization.IG.SpecializationData.nonnegative_iff_powerSeries

theorem powerToLaurent_integralSeries : PowerToLaurentIntegralSeries :=
  Specs.GaloisFormalization.IG.SpecializationData.powerToLaurent_integralSeries

theorem mem_positiveIdeal : PositiveIdealMembership := by
  intro ℓ _ L _ i x
  exact (AddValuation.toValuation (inducedOrder i)).mem_maximalIdeal_iff

theorem reduction_apply : ReductionApply :=
  Specs.GaloisFormalization.IG.SpecializationData.reduction_apply

theorem residueEmbedding_residue : ResidueEmbeddingApply := by
  intro ℓ _ L _ i x
  exact Specs.GaloisFormalization.IG.SpecializationData.reduction_apply i x

end

end GaloisFormalization.IG.SpecializationData
