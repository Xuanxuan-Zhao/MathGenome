import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FlatBaseChangeLocus
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.OpenLocus
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.FlatBaseChangeLocus
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.BaseChange

/-! ET-14: flat pullback of the étale locus. ET-04 expresses it as the
smooth locus minus the support of Ω. SM-13 gives the smooth-locus comparison;
KD-17 and faithful flatness of the local map at a prime give the support comparison. -/
namespace AdvCommAlg.Etale

universe u v w
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Equality of the principal-neighborhood étale loci under any flat base extension. -/
theorem etaleLocus_flat_base_change :
    Specs.AdvCommAlg.Etale.FlatBaseChangeLocus.locus.{u,v,w} := by
  intro A B A' _ _ _ _ _ _ _
  have : Module.Flat B (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight A B A').symm.toLinearEquiv
  rw [etaleLocus_eq_smoothLocus_diff_support A' (A' ⊗[A] B),
    etaleLocus_eq_smoothLocus_diff_support A B,
    Smooth.smoothLocus_flat_base_change A B A']
  ext q'
  simp only [Set.mem_sdiff, Set.mem_preimage]
  rw [← (Differentials.baseChangeEquiv A A' B (A' ⊗[A] B)).support_eq,
    Smooth.notMem_support_baseChange B (A' ⊗[A] B) (KaehlerDifferential A B) q']

/-- The equivalent pointwise assertion uses exactly the ET-06 neighborhood predicate. -/
theorem isEtaleAt_flat_base_change :
    Specs.AdvCommAlg.Etale.FlatBaseChangeLocus.pointwise.{u,v,w} := by
  intro A B A' _ _ _ _ _ _ _ q'
  exact Set.ext_iff.mp (etaleLocus_flat_base_change A B A') q'

end AdvCommAlg.Etale
