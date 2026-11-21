import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.EllipticFredholm
import MathGenome.Internal.LinearPDE.P201.Elliptic.NonsymmetricResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.SchauderAdjoints

noncomputable section
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexConjugate
open P201Specs.Fredholm
namespace P201.Elliptic.Fredholm
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Schauder's transpose theorem transported through the actual Riesz maps. -/
theorem compact_adjoint (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  have hc := ExpandedFA.Compactness.SchauderAdjoints.compact_banachTranspose ℂ H H T
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr hT)
  have hn := (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mp hc
  have hcomp := (hn.comp_clm (InnerProductSpace.toDual ℂ H).toLinearIsometry.toContinuousLinearMap).clm_comp
    (InnerProductSpace.toDual ℂ H).symm.toLinearIsometry.toContinuousLinearMap
  convert hcomp using 1
  ext x
  apply (InnerProductSpace.toDual ℂ H).injective
  ext y
  change InnerProductSpace.toDual ℂ H (T.adjoint x) y =
    InnerProductSpace.toDual ℂ H ((InnerProductSpace.toDual ℂ H).symm
      (ExpandedFA.P1.C04Annihilators.banachTranspose ℂ H H T
        (InnerProductSpace.toDual ℂ H x))) y
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact T.adjoint_inner_left y x

/-- The bounded defect, defined without dividing by the spectral parameter. -/
def defect (T : H →L[ℂ] H) (c : ℂ) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - c • T

omit [CompleteSpace H] in
lemma eigenKernel_eq_defect (L : ExpandedFA.Unbounded.Operator ℂ H H)
    (T : H →L[ℂ] H) (μ : ℝ)
    (hT : ∀ u f, (u, f - (μ : ℂ) • u) ∈ L.graph ↔ T f = u) (z : ℂ) :
    eigenKernel L z = (defect T (z + (μ : ℂ))).ker := by
  ext u
  have he : (z + (μ : ℂ)) • u - (μ : ℂ) • u = z • u := by
    simp [add_smul]
  change (u, z • u) ∈ L.graph ↔ u - (z + (μ : ℂ)) • T u = 0
  rw [← he, hT, map_smul, sub_eq_zero, eq_comm]

omit [CompleteSpace H] in
lemma solves_iff_defect (L : ExpandedFA.Unbounded.Operator ℂ H H)
    (T : H →L[ℂ] H) (μ : ℝ)
    (hT : ∀ u f, (u, f - (μ : ℂ) • u) ∈ L.graph ↔ T f = u) (z : ℂ) (f : H) :
    (∃ u, Solves L z f u) ↔ ∃ x, defect T (z + (μ : ℂ)) x = f := by
  constructor
  · rintro ⟨u, hu⟩
    have he : f + (z + (μ : ℂ)) • u - (μ : ℂ) • u = f + z • u := by
      simp only [add_smul]
      module
    have ht := (hT u (f + (z + (μ : ℂ)) • u)).mp (he ▸ hu)
    refine ⟨f + (z + (μ : ℂ)) • u, ?_⟩
    change f + (z + (μ : ℂ)) • u - (z + (μ : ℂ)) • T (f + (z + (μ : ℂ)) • u) = f
    rw [ht, add_sub_cancel_right]
  · rintro ⟨x, hx⟩
    refine ⟨T x, ?_⟩
    have he : f + z • T x = x - (μ : ℂ) • T x := by
      change x - (z + (μ : ℂ)) • T x = f at hx
      rw [← hx, add_smul]
      module
    change (T x, f + z • T x) ∈ L.graph
    rw [he]
    exact (hT (T x) x).mpr rfl

omit [CompleteSpace H] in
lemma affine_solutions (L : ExpandedFA.Unbounded.Operator ℂ H H) (z : ℂ)
    (f u₀ : H) (h₀ : Solves L z f u₀) (u : H) :
    Solves L z f u ↔ ∃ v ∈ eigenKernel L z, u = u₀ + v := by
  constructor
  · intro hu
    refine ⟨u - u₀, ?_, by abel⟩
    have h := L.graph.sub_mem hu h₀
    change (u - u₀, z • (u - u₀)) ∈ L.graph
    convert h using 1; simp [smul_sub]
  · rintro ⟨v, hv, rfl⟩
    have h := L.graph.add_mem h₀ hv
    change (u₀ + v, f + z • (u₀ + v)) ∈ L.graph
    convert h using 1; simp [smul_add, add_assoc]



lemma adjoint_defect (T : H →L[ℂ] H) (c : ℂ) :
    (defect T c).adjoint = defect T.adjoint (conj c) := by
  simp only [defect, map_sub, ContinuousLinearMap.adjoint_id, map_smulₛₗ]

/-- Closed range is used for exact compatibility, rather than just density.
Finite kernels are established for both compact defects. -/
theorem bounded_defect_facts (T : H →L[ℂ] H) (hT : IsCompactOperator T) (c : ℂ) :
    FiniteDimensional ℂ (defect T c).ker ∧
    FiniteDimensional ℂ (defect T c).adjoint.ker ∧
    (defect T c).range = (defect T c).adjoint.kerᗮ ∧
    (Function.Injective (defect T c) → Function.Surjective (defect T c)) := by
  have hK := (ExpandedFA.Compactness.compact_iff_isCompactOperator (c • T).toLinearMap).mpr (hT.smul c)
  have hK' := (ExpandedFA.Compactness.compact_iff_isCompactOperator
    ((conj c) • T.adjoint).toLinearMap).mpr
    ((compact_adjoint T hT).smul (conj c))
  have hfin := (ExpandedFA.Fredholm.identity_sub_compact_kernel_closed_finite_dimensional
    (c • T) hK).2
  have hfin' := (ExpandedFA.Fredholm.identity_sub_compact_kernel_closed_finite_dimensional
    ((conj c) • T.adjoint) hK').2
  have hclosed := ExpandedFA.Fredholm.identity_sub_compact_closed_range (c • T) hK
  refine ⟨hfin, ?_, ?_, (ExpandedFA.Fredholm.riesz_schauder_alternative (c • T) hK).mp⟩
  · rw [adjoint_defect]
    exact hfin'
  · calc
      (defect T c).range = (defect T c).range.topologicalClosure :=
        hclosed.submodule_topologicalClosure_eq.symm
      _ = (defect T c).rangeᗮᗮ := ((defect T c).range.orthogonal_orthogonal_eq_closure).symm
      _ = (defect T c).adjoint.kerᗮ := by rw [ContinuousLinearMap.orthogonal_range]

/-- A compact shifted inverse implies the complete alternative. No inverse
of `z+μ` is taken: all identities also cover its zero value. -/
theorem alternative_of_inverse (L : ExpandedFA.Unbounded.Operator ℂ H H)
    (T : H →L[ℂ] H) (μ : ℝ) (hc : IsCompactOperator T)
    (hT : ∀ u f, (u, f - (μ : ℂ) • u) ∈ L.graph ↔ T f = u)
    (hA : ∀ u f, (u, f - (μ : ℂ) • u) ∈ L.adjoint.graph ↔ T.adjoint f = u) :
    Alternative L := by
  intro z
  let A := defect T (z + (μ : ℂ))
  have hk : eigenKernel L z = A.ker := eigenKernel_eq_defect L T μ hT z
  have hka : eigenKernel L.adjoint (conj z) = A.adjoint.ker := by
    rw [eigenKernel_eq_defect L.adjoint T.adjoint μ hA, show A.adjoint =
      defect T.adjoint (conj z + (μ : ℂ)) by
        simp only [A, adjoint_defect, map_add, Complex.conj_ofReal]]
  obtain ⟨hfin, hfina, hrange, hsurj⟩ := bounded_defect_facts T hc (z + (μ : ℂ))
  have hs (f : H) : (∃ u, Solves L z f u) ↔ f ∈ A.range :=
    solves_iff_defect L T μ hT z f
  refine ⟨hk ▸ hfin, hka ▸ hfina, ?_, affine_solutions L z, ?_⟩
  · intro f
    rw [hs, hrange, Submodule.mem_orthogonal, ← hka]
  · intro hbot f
    have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp (hk ▸ hbot)
    obtain ⟨u, hu⟩ := (hs f).mpr (hsurj hinj f)
    refine ⟨u, hu, ?_⟩
    intro v hv
    obtain ⟨w, hw, hvw⟩ := (affine_solutions L z f u hu v).mp hv
    have hw0 : w = 0 := by simpa only [hbot, Submodule.mem_bot] using hw
    simpa only [hw0, add_zero] using hvw

set_option backward.isDefEq.respectTransparency true in
/-- Assembly on the concrete four-term Dirichlet form. The large-shift and
all-parameter conclusions refer to a single canonical associated graph. -/
theorem pde_fredholm : P201Specs.Fredholm.PDE := by
  intro m Ω hΩ q hq lam hlam hell
  obtain ⟨B, C, hi, hd, hC, hB, hG, hjc, hR⟩ :=
    Nonsymmetric.pde_resolvent m Ω hΩ ℂ q hq lam hlam hell
  let a := NonsymmetricExpected.embeddedForm
    (𝕜 := ℂ) (H := P201Specs.Lp ℂ Ω 2) (V := P201Specs.H10 ℂ Ω)
    (P201Specs.hZeroUnderlying (𝕜 := ℂ) Ω) hi hd B
  have hμ : C < C + 1 := by linarith
  obtain ⟨_, S, hsol, huniq, hTi, hTd, hdense, hclosed, hdom, hgraph, hadj, hcompact⟩ :=
    hR (C + 1) hμ
  refine ⟨B, hi, hd, hB, ?_⟩
  change Full a.associatedOperator
  refine ⟨hdense, hclosed, ⟨C, ?_⟩, ?_⟩
  · intro μ hμ
    obtain ⟨_, Sμ, _, _, _, _, _, _, _, hgμ, _, hcμ⟩ := hR μ hμ
    exact ⟨(P201Specs.hZeroUnderlying Ω).comp Sμ, hcμ hjc, hgμ⟩
  · exact alternative_of_inverse a.associatedOperator
      ((P201Specs.hZeroUnderlying Ω).comp S) (C + 1) (hcompact hjc) hgraph hadj

end P201.Elliptic.Fredholm
