import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.HypersurfaceExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularAndCompleteIntersection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CanonicalQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars

/-! The hypersurface in GC-14. Dimension drop identifies the GC-10 degree;
the two-term resolution identifies its actual Ext coefficient over S/(f). -/
noncomputable section
universe u

namespace AdvCommAlg.Gorenstein
namespace HypersurfaceExample

open CanonicalQuotient ConcentratedChangeOfRings

theorem dimensionDrop : HypersurfaceExampleSpecs.dimensionDropType.{u} := by
  intro S _ _ f hf hreg
  letI := RegularReduction.quotientLocalRing f hf
  let Q := S ⧸ Ideal.span {f}
  have hdim := (CohenMacaulay.dimension_quotient_regular S S f hf hreg).2
  change Module.supportDim S (QuotSMulTop f S) + 1 = Module.supportDim S S at hdim
  rw [Module.supportDim_eq_of_equiv ((principalRingModuleEquiv f).restrictScalars S)] at hdim
  have hsc := CohenMacaulay.dimension_of_surjective (R := S) (S := Q) Q
    Ideal.Quotient.mk_surjective
  change Module.supportDim S Q = Module.supportDim Q Q at hsc
  rw [hsc, Module.supportDim_self_eq_ringKrullDim,
    Module.supportDim_self_eq_ringKrullDim] at hdim
  exact hdim

theorem gorenstein : HypersurfaceExampleSpecs.gorensteinType.{u} := by
  intro S _ _ f hf hreg
  exact (RegularReduction.localGorenstein_quotient_iff S f hf hreg).mp
    (regularLocal_gorenstein S)

theorem extOne : HypersurfaceExampleSpecs.extOneType.{u} := by
  intro S _ _ f _ hreg
  exact ⟨(RegularQuotientExt.quotientBoundaryEquiv f hreg (ModuleCat.of S S)).symm.trans
    (RegularReduction.quotientRegularModuleEquiv (Ideal.span {f}))⟩

theorem canonical : HypersurfaceExampleSpecs.canonicalType.{u} := by
  intro S _ _ f hf hreg
  letI := RegularReduction.quotientLocalRing f hf
  let Q := S ⧸ Ideal.span {f}
  obtain ⟨s, hs, _⟩ := CohenMacaulay.isLeast_parameter_length S S
  obtain ⟨d, hd, _⟩ := CohenMacaulay.isLeast_parameter_length Q Q
  rw [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim] at hs hd
  have hdrop := dimensionDrop S f hf hreg
  rw [hs, hd] at hdrop
  have hsd : s = d + 1 := by exact_mod_cast hdrop.symm
  have hc : s - d = 1 := by omega
  have hG := regularLocal_gorenstein S
  have hQ := localGorenstein_cohenMacaulay Q (gorenstein S f hf hreg)
  obtain ⟨hfin, hcan, _⟩ := canonicalQuotient_properties S Q
    Ideal.Quotient.mk_surjective hG hQ s d hs hd
  refine ⟨s, d, hs, hd, hsd, hc, hfin, hcan, ?_, ?_⟩
  · change Nonempty (coefficient (algebraMap S Q) (ModuleCat.of S S) (s - d) ≃ₗ[Q]
      coefficient (Ideal.Quotient.mk (Ideal.span {f})) (ModuleCat.of S S) 1)
    rw [hc]
    exact ⟨LinearEquiv.refl Q _⟩
  · change Nonempty (coefficient (algebraMap S Q) (ModuleCat.of S S) (s - d) ≃ₗ[Q] Q)
    rw [hc]
    exact extOne S f hf hreg

end HypersurfaceExample
end AdvCommAlg.Gorenstein
