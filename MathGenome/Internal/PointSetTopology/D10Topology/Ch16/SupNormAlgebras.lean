import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.TopologyComparison

/-! Supremum norms, function algebras and uniform closure for chapter 16.
The canonical metric is the untruncated supremum metric on compact-domain
continuous maps; its agreement with chapter 13 is established below. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v w
namespace D10Topology.Ch16

abbrev supNorm := @Specs.D10Topology.Ch16.SupNormAlgebras.supNorm
abbrev supNormTopology := @Specs.D10Topology.Ch16.SupNormAlgebras.supNormTopology
abbrev FunctionSubalgebra := @Specs.D10Topology.Ch16.SupNormAlgebras.FunctionSubalgebra
abbrev RealFunctionAlgebra := @Specs.D10Topology.Ch16.SupNormAlgebras.RealFunctionAlgebra
abbrev ComplexFunctionAlgebra := @Specs.D10Topology.Ch16.SupNormAlgebras.ComplexFunctionAlgebra
abbrev IsUnital := @Specs.D10Topology.Ch16.SupNormAlgebras.IsUnital
abbrev SeparatesPoints := @Specs.D10Topology.Ch16.SupNormAlgebras.SeparatesPoints
abbrev ConjugationInvariant := @Specs.D10Topology.Ch16.SupNormAlgebras.ConjugationInvariant
abbrev uniformClosure := @Specs.D10Topology.Ch16.SupNormAlgebras.uniformClosure

theorem supNorm_eq_iSup : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_eq_iSup := by
  intro X 𝕜 _ _ _ f
  exact ContinuousMap.norm_eq_iSup_norm f

theorem realSupNorm_eq_iSup_abs : Specs.D10Topology.Ch16.SupNormAlgebras.realSupNorm_eq_iSup_abs := by
  intro X _ _ f
  simpa only [Real.norm_eq_abs] using supNorm_eq_iSup f

theorem complexSupNorm_eq_iSup : Specs.D10Topology.Ch16.SupNormAlgebras.complexSupNorm_eq_iSup := by
  intro X _ _ f
  exact supNorm_eq_iSup f

theorem supNorm_bounded : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_bounded := by
  intro X 𝕜 _ _ _ f
  exact ⟨‖f‖, norm_nonneg f, f.norm_coe_le_norm⟩

theorem supNorm_nonneg : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_nonneg := by
  intro X 𝕜 _ _ _ f
  exact norm_nonneg f

theorem supNorm_eq_zero : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_eq_zero := by
  intro X 𝕜 _ _ _ f
  exact norm_eq_zero

theorem supNorm_add_le : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_add_le := by
  intro X 𝕜 _ _ _ f g
  exact norm_add_le f g

theorem supNorm_smul : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_smul := by
  intro X 𝕜 _ _ _ c f
  exact norm_smul c f

theorem supNorm_mul_le : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_mul_le := by
  intro X 𝕜 _ _ _ f g
  exact norm_mul_le f g

theorem supNorm_empty : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_empty := by
  intro X 𝕜 _ _ _ _ f
  have h : f = 0 := Subsingleton.elim _ _
  change ‖f‖ = 0
  rw [h, norm_zero]

theorem supNorm_const : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_const := by
  intro X 𝕜 _ _ _ _ c
  rw [supNorm_eq_iSup]
  simp

theorem supNorm_dist : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_dist := by
  intro X 𝕜 _ _ _ f g
  exact dist_eq_norm f g

theorem supNorm_lt_iff : Specs.D10Topology.Ch16.SupNormAlgebras.supNorm_lt_iff := by
  intro X 𝕜 _ _ _ f ε hε
  exact f.norm_lt_iff hε

theorem supNormTopology_eq_uniform : Specs.D10Topology.Ch16.SupNormAlgebras.supNormTopology_eq_uniform := by
  intro X 𝕜 _ _ _
  change ContinuousMap.compactOpen = _
  exact (Ch13.compactOpenContinuousTopology_eq_mathlib (X := X) (Y := 𝕜)).symm.trans
    (Ch13.compactDomain_continuousTopologies_eq (X := X) (Y := 𝕜)).2

theorem tendsto_iff_uniform : Specs.D10Topology.Ch16.SupNormAlgebras.tendsto_iff_uniform := by
  intro X 𝕜 _ _ _ ι F f l
  rw [(ContinuousMap.isUniformEmbedding_equivBoundedOfCompact X 𝕜).isEmbedding.tendsto_nhds_iff]
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly

theorem functionSubalgebra_iff : Specs.D10Topology.Ch16.SupNormAlgebras.functionSubalgebra_iff := by
  intro X 𝕜 _ _ S
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.zero_mem, fun _ hf _ hg => A.add_mem hf hg,
      fun _ hf _ hg => A.mul_mem hf hg, fun c _ hf => A.smul_mem c hf⟩
  · rintro ⟨hz, ha, hm, hs⟩
    exact ⟨{
      carrier := S
      zero_mem' := hz
      add_mem' := fun hf hg => ha _ hf _ hg
      mul_mem' := fun hf hg => hm _ hf _ hg
      smul_mem' := fun c _ hf => hs c _ hf }, rfl⟩

theorem unital_iff_contains_constants : Specs.D10Topology.Ch16.SupNormAlgebras.unital_iff_contains_constants := by
  intro X 𝕜 _ _ A
  constructor
  · intro h c
    have hc : c • (1 : C(X, 𝕜)) = ContinuousMap.const X c := by
      ext x
      simp
    rw [← hc]
    exact A.smul_mem c h
  · intro h
    change (1 : C(X, 𝕜)) ∈ A
    simpa only [ContinuousMap.const_one] using h 1

theorem empty_domain_collapse : Specs.D10Topology.Ch16.SupNormAlgebras.empty_domain_collapse := by
  intro X 𝕜 _ _ _ f g
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem empty_domain_algebra : Specs.D10Topology.Ch16.SupNormAlgebras.empty_domain_algebra := by
  intro X 𝕜 _ _ _ A
  have h (f : C(X, 𝕜)) : f ∈ A := by
    have he : f = 0 := Subsingleton.elim _ _
    rw [he]
    exact A.zero_mem
  exact ⟨h 1, Set.eq_univ_of_forall h⟩

theorem conjugate_apply : Specs.D10Topology.Ch16.SupNormAlgebras.conjugate_apply := by
  intro X _ f x
  rfl

theorem conjugationInvariant_iff : Specs.D10Topology.Ch16.SupNormAlgebras.conjugationInvariant_iff := by
  intro X _ A
  constructor
  · intro h f hf
    exact ⟨star f, h f hf, fun _ => rfl⟩
  · intro h f hf
    obtain ⟨g, hg, he⟩ := h f hf
    have heq : g = star f := ContinuousMap.ext he
    simpa only [← heq] using hg

theorem uniformClosure_eq_norm_closure : Specs.D10Topology.Ch16.SupNormAlgebras.uniformClosure_eq_norm_closure := by
  intro X 𝕜 _ _ _ A
  change @closure _ (Specs.D10Topology.Ch13.FunctionTopologies.uniformContinuousTopology) A = _
  rw [← supNormTopology_eq_uniform (X := X) (𝕜 := 𝕜)]
  rfl

theorem mem_uniformClosure_iff : Specs.D10Topology.Ch16.SupNormAlgebras.mem_uniformClosure_iff := by
  intro X 𝕜 _ _ _ A f
  rw [uniformClosure_eq_norm_closure, Metric.mem_closure_iff]
  simp only [Specs.D10Topology.Ch16.SupNormAlgebras.supNorm, dist_eq_norm]

theorem mem_uniformClosure_iff_pointwise_error : Specs.D10Topology.Ch16.SupNormAlgebras.mem_uniformClosure_iff_pointwise_error := by
  intro X 𝕜 _ _ _ A f
  rw [mem_uniformClosure_iff]
  exact forall_congr' fun ε => forall_congr' fun hε =>
    exists_congr fun g => and_congr_right fun _ => (supNorm_lt_iff (f - g) ε hε)

end D10Topology.Ch16
