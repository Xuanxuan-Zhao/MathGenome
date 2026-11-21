import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.RegularLocalLowDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.DimensionOneDVR
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularDomain

/-!
The regular-local domain step used in SN-09, paper.tex:4273–4276.

The mounted P103 domain theorem is available as a proved library result.
It proves the stronger, unrestricted regular-local domain assertion, using
Krull intersection and the polynomial description of the associated graded
ring. Its regularity hypothesis is exactly cotangent-space dimension equal
to Krull dimension; the first theorem explicitly bridges that hypothesis.
Thus the domain property is proved before the domain-dependent SN-06
equivalence is applied. Dimension zero uses CM-08's field boundary.
-/

universe u
namespace AdvCommAlg.Normality

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Regular local rings are domains, with no domain assumption as input. -/
theorem regularLocal_isDomain : IsDomain R := by
  apply P103.RegularDomain.domain R
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance

/-- The dimension-zero boundary is a field. -/
theorem regularLocal_dimension_zero_isField (hd : ringKrullDim R = 0) : IsField R :=
  CohenMacaulay.regularLocal_dimension_zero_isField R hd

/-- In dimension one both the domain structure and the DVR property follow. -/
theorem regularLocal_dimension_one_isDVR (hd : ringKrullDim R = 1) :
    ∃ h : IsDomain R, @IsDiscreteValuationRing R _ h := by
  let h : IsDomain R := regularLocal_isDomain R
  exact ⟨h, (dimension_one_dvr_equivalences R hd).2.mp inferInstance⟩

/-- Every regular local ring of dimension at most one is an integrally closed domain. -/
theorem regularLocal_low_dimension_integrallyClosed (hd : ringKrullDim R ≤ 1) :
    IsDomain R ∧ IsIntegrallyClosed R := by
  let : IsDomain R := regularLocal_isDomain R
  refine ⟨inferInstance, ?_⟩
  by_cases hzero : ringKrullDim R = 0
  · let : Field R := (regularLocal_dimension_zero_isField R hzero).toField
    infer_instance
  · have hone : ringKrullDim R = 1 := by
      apply le_antisymm hd
      apply le_of_not_gt
      intro hlt
      apply hzero
      apply le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial (R := R))
      have hlt' : ringKrullDim R < (0 : WithBot ℕ∞) + 1 := by simpa using hlt
      exact ENat.WithBot.lt_add_one_iff.mp hlt'
    exact (dimension_one_dvr_equivalences R hone).1.mpr inferInstance

end AdvCommAlg.Normality
