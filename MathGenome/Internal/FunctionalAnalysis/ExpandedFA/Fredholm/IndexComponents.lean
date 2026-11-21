import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.IndexComponents
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.IndexStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.HilbertTwoExponentials
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Tactic.Linarith

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u v

section Banach
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- An index-zero Fredholm operator can be completed to an isomorphism by
mapping its finite-dimensional kernel onto a complement of its range. -/
theorem exists_finite_rank_correction (T : X →L[𝕜] X) (hT : IsFredholm T)
    (hzero : fredholmIndex T hT = 0) :
    ∃ F : X →L[𝕜] X, FiniteDimensional 𝕜 F.range ∧ IsUnit (T + F) := by
  obtain ⟨pkg⟩ := hT.to_native.nonempty_fredholmPackage
  let := pkg.decDom.finite_X₀
  let := pkg.decCodom.finite_X₀
  have hdim : Module.finrank 𝕜 pkg.decDom.X₀ =
      Module.finrank 𝕜 pkg.decCodom.X₀ := by
    have hquot := (pkg.decCodom.X₁.quotientEquivOfIsTopCompl
      pkg.decCodom.X₀ pkg.decCodom.isTopCompl).toLinearEquiv.finrank_eq
    change (Module.finrank 𝕜 T.ker : ℤ) -
      (Module.finrank 𝕜 (X ⧸ T.range) : ℤ) = 0 at hzero
    rw [pkg.ker_eq, pkg.range_eq, hquot] at hzero
    exact_mod_cast (sub_eq_zero.mp hzero)
  let e₀ : pkg.decDom.X₀ ≃L[𝕜] pkg.decCodom.X₀ :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  let d := pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl
  let c := pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl
  let e : X ≃L[𝕜] X := (d.symm.trans (pkg.equiv.prodCongr e₀)).trans c
  let f : X →L[𝕜] pkg.decCodom.X₀ :=
    e₀.toContinuousLinearMap.comp
      (pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm)
  let F : X →L[𝕜] X := pkg.decCodom.X₀.subtypeL.comp f
  have hF : FiniteDimensional 𝕜 F.range := by
    apply FiniteDimensional.of_injective
      (Submodule.inclusion (show F.range ≤ pkg.decCodom.X₀ from by
        rintro _ ⟨x, rfl⟩
        exact (f x).property))
    exact Submodule.inclusion_injective _
  refine ⟨F, hF, ?_⟩
  have he : T + F = e.toContinuousLinearMap := by
    ext x
    simp only [add_apply, pkg.eq_equiv,
      ContinuousLinearMap.comp_apply, F, f, e, d, c,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodCongr_apply,
      Submodule.prodEquivOfIsTopCompl_apply, Submodule.prodEquivOfIsTopCompl_symm_apply]
    rfl
  rw [he]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective

/-- Every affine compact-perturbation segment remains Fredholm. -/
theorem joinedIn_compact_perturbation (T K : X →L[𝕜] X) (hT : IsFredholm T)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    JoinedIn {S : X →L[𝕜] X | IsFredholm S} T (T + K) := by
  let f : ℝ → (X →L[𝕜] X) := fun t => T + (RCLike.ofReal t : 𝕜) • K
  apply JoinedIn.ofLine (f := f)
  · exact (continuous_const.add
      ((RCLike.continuous_ofReal : Continuous (RCLike.ofReal : ℝ → 𝕜)).smul
        continuous_const)).continuousOn
  · simp [f]
  · simp [f]
  · rintro _ ⟨t, _, rfl⟩
    exact hT.add_compact (Compactness.compact_smul _ K.toLinearMap hK)

end Banach

section Hilbert
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem isFredholm_of_isUnit {T : H →L[ℂ] H} (hT : IsUnit T) : IsFredholm T :=
  isFredholm_of_native (ContinuousLinearMap.IsInvertible.of_isHomeomorph
    (ContinuousLinearMap.isHomeomorph_of_isUnit hT)).isFredholm

/-- The upstream two-exponential path is a path in the Fredholm set. -/
theorem joinedIn_invertibles (A B : H →L[ℂ] H) (hA : IsUnit A) (hB : IsUnit B) :
    JoinedIn {T : H →L[ℂ] H | IsFredholm T} A B := by
  let := BanachAlgebra.HilbertTwoExponentials.invertibles_path_connected H
  obtain ⟨p⟩ := PathConnectedSpace.joined hA.unit hB.unit
  have hp : JoinedIn {T : H →L[ℂ] H | IsFredholm T}
      (hA.unit : H →L[ℂ] H) (hB.unit : H →L[ℂ] H) := by
    refine ⟨p.map Units.continuous_val, ?_⟩
    intro t
    exact isFredholm_of_isUnit (p t).isUnit
  simpa only [hA.unit_spec, hB.unit_spec] using hp

/-- All index-zero operators lie in the identity's norm-path component. -/
theorem joinedIn_identity_of_index_zero (T : H →L[ℂ] H) (hT : IsFredholm T)
    (hzero : fredholmIndex T hT = 0) :
    JoinedIn {S : H →L[ℂ] H | IsFredholm S} T (ContinuousLinearMap.id ℂ H) := by
  obtain ⟨F, hF, hU⟩ := exists_finite_rank_correction T hT hzero
  let := hF
  exact (joinedIn_compact_perturbation T F hT (compact_of_finiteDimensional_range F)).trans
    (joinedIn_invertibles _ _ hU isUnit_one)

/-- Local constancy of the integer index gives necessity along an actual
operator-norm continuous path. -/
theorem index_eq_of_joinedIn (A B : H →L[ℂ] H) (hA : IsFredholm A) (hB : IsFredholm B)
    (hpath : JoinedIn {T : H →L[ℂ] H | IsFredholm T} A B) :
    fredholmIndex A hA = fredholmIndex B hB := by
  obtain ⟨p, hp⟩ := hpath
  have hi : Continuous (fun t : unitInterval => (p t).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hp t).to_native.index_continuousAt.comp p.continuous.continuousAt
  have he := isPreconnected_univ.constant hi.continuousOn
    (x := (0 : unitInterval)) (y := (1 : unitInterval)) (Set.mem_univ _) (Set.mem_univ _)
  rw [fredholmIndex_eq_native, fredholmIndex_eq_native]
  simpa only [Path.source, Path.target] using he

/-- Equal indices reduce to the zero-index component by a bounded parametrix.
The remaining error is compact and is removed by a straight segment. -/
theorem joinedIn_of_index_eq (A B : H →L[ℂ] H) (hA : IsFredholm A) (hB : IsFredholm B)
    (hindex : fredholmIndex A hA = fredholmIndex B hB) :
    JoinedIn {T : H →L[ℂ] H | IsFredholm T} A B := by
  obtain ⟨C, hK, hL⟩ := (atkinson_compact B).mp hB
  have hC : IsFredholm C := isFredholm_of_compact_parametrix C B hL hK
  let K := C.comp B - ContinuousLinearMap.id ℂ H
  have hI : IsFredholm (ContinuousLinearMap.id ℂ H) :=
    isFredholm_of_native ContinuousLinearMap.IsFredholm.id
  have hCB : IsFredholm (C.comp B) := isFredholm_comp B C hB hC
  have hAC : IsFredholm (A.comp C) := isFredholm_comp C A hC hA
  have hCBzero : fredholmIndex (C.comp B) hCB = 0 := by
    have hz := fredholmIndex_add_compact (ContinuousLinearMap.id ℂ H) K hK hI
      (hI.add_compact hK)
    have hid : fredholmIndex (ContinuousLinearMap.id ℂ H) hI = 0 :=
      LinearMap.index_id
    simpa only [K, add_sub_cancel, hid] using hz
  have hACzero : fredholmIndex (A.comp C) hAC = 0 := by
    have h₁ := fredholmIndex_comp B C hB hC hCB
    have h₂ := fredholmIndex_comp C A hC hA hAC
    linarith
  obtain ⟨p, hp⟩ := joinedIn_identity_of_index_zero (A.comp C) hAC hACzero
  have hprod : JoinedIn {T : H →L[ℂ] H | IsFredholm T} ((A.comp C).comp B) B := by
    let q : Path ((A.comp C).comp B) B :=
      { toFun := fun t => (p t).comp B
        continuous_toFun := p.continuous.clm_comp continuous_const
        source' := by simp
        target' := by simp }
    exact ⟨q, fun t => isFredholm_comp B (p t) hB (hp t)⟩
  have hAK := Compactness.compact_postcomp K.toLinearMap A hK
  have heq : A + A.comp K = (A.comp C).comp B := by
    ext x
    simp only [K, add_apply, ContinuousLinearMap.comp_apply,
      sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  exact (heq ▸ joinedIn_compact_perturbation A (A.comp K) hA hAK).trans hprod

end Hilbert

/-- Norm-path components of all Fredholm endomorphisms of any complex
Hilbert space are exactly the fibers of the integer index. -/
theorem index_components : IndexComponentsSpec.IndexComponents.{u} := by
  intro H _ _ _ A B hA hB
  exact ⟨index_eq_of_joinedIn A B hA hB, joinedIn_of_index_eq A B hA hB⟩

end ExpandedFA.Fredholm
