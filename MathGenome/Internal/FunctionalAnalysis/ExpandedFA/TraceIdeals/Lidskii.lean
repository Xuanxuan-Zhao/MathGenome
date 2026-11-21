import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.Lidskii
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.QuasinilpotentTraceZero
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.Lidskii
open TraceClassDefinitions
open scoped BigOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An injective finite choice of algebraic occurrences never exceeds the
full algebraic multiplicity at any scalar. -/
lemma selection_of_injective {n : ℕ} (T : H →L[ℂ] H)
    (f : Fin n → Spec.EigenvalueIndex T) (hf : Function.Injective f) :
    WeylProducts.Spec.PaddedEigenvalueSelection T (fun i => Spec.eigenvalue T (f i)) := by
  classical
  refine ⟨fun i _ => (f i).1.property.2, ?_⟩
  intro z hz
  let s : Finset (Fin n) := Finset.univ.filter (fun i => Spec.eigenvalue T (f i) = z)
  have hs (i : s) : (f i.val).1.val = z := (Finset.mem_filter.mp i.property).2
  let g : s → Fin (WeylProducts.Spec.algebraicMultiplicity T z) := fun i =>
    ⟨(f i.val).2.val, by simpa only [← hs i] using (f i.val).2.isLt⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply hf
    have hz : (f i.val).1 = (f j.val).1 :=
      Subtype.ext ((hs i).trans (hs j).symm)
    exact Sigma.ext hz ((Fin.heq_ext_iff (congrArg
      (fun z : Spec.NonzeroEigenvalues T => WeylProducts.Spec.algebraicMultiplicity T z.val) hz)).mpr
        (congrArg Fin.val hij))
  have hcard := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

variable [CompleteSpace H]

/-- Weyl's inequality bounds every finite subsum of the COMPLETE algebraic
spectrum. In particular no enumeration or exhaustion is assumed. -/
lemma finite_eigenvalue_sum_le (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (s : Finset (Spec.EigenvalueIndex T)) :
    (∑ i ∈ s, ‖Spec.eigenvalue T i‖) ≤ traceNorm T := by
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  let f : Fin s.card → Spec.EigenvalueIndex T := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have h := (QuasinilpotentTraceZero.finite_selection_weyl_bounds T hT
    (fun i => Spec.eigenvalue T (f i)) (selection_of_injective T f hf)).1
  calc
    _ = ∑ i : s, ‖Spec.eigenvalue T i.val‖ := (Finset.sum_coe_sort s _).symm
    _ = ∑ i : Fin s.card, ‖Spec.eigenvalue T (f i)‖ := (e.sum_comp _).symm
    _ ≤ _ := h

/-- Absolute convergence for the full eigenvalue multiset, with algebraic
multiplicity, on every complex Hilbert space. -/
theorem absolute_eigenvalue_sum : Spec.AbsoluteEigenvalueSum.{u} := by
  intro H _ _ _ T hT
  have hb := finite_eigenvalue_sum_le T hT
  exact ⟨summable_of_sum_le (fun i => norm_nonneg _) hb,
    Real.tsum_le_of_sum_le (fun i => norm_nonneg _) hb⟩

/-- A nonzero adjoint eigenvector cannot annihilate the corresponding full
root space. The proof uses the compact Fredholm kernel/range decomposition,
so it does not require identifying an analytic Riesz projection. -/
lemma adjoint_eigenvector_eq_zero_of_orthogonal (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (z : ℂ) (hz : z ≠ 0) (u : H)
    (hu : T.adjoint u = star z • u)
    (horth : ∀ x ∈ Module.End.maxGenEigenspace T.toLinearMap z, inner ℂ u x = 0) :
    u = 0 := by
  let L : H →L[ℂ] H := z⁻¹ • T
  have hL := Fredholm.compact_smul T hT z⁻¹
  obtain ⟨q, hq, hdec⟩ := Fredholm.riesz_decomposition L hL
  have hd := (hdec q le_rfl).2.2
  have hcompl := hd.1.isCompl
  have hroot : Fredholm.CompactDefectStabilizationSpec.kernelChain L q ≤
      Module.End.maxGenEigenspace T.toLinearMap z := by
    rw [← Fredholm.nonzero_spectral_shift_power_kernel T z hz q,
      WeylProducts.shift_power_kernel]
    exact Module.End.genEigenspace_le_maximal T.toLinearMap z q
  let A : Module.End ℂ H := (ContinuousLinearMap.id ℂ H - L).toLinearMap
  have hA (x : H) : inner ℂ u (A x) = 0 := by
    simp only [A, L, ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.id_apply,
      smul_apply, inner_sub_right, inner_smul_right]
    rw [← T.adjoint_inner_left, hu, inner_smul_left]
    change inner ℂ u x - z⁻¹ * (star (star z) * inner ℂ u x) = 0
    simp [hz]
  have hrange (x : H)
      (hx : x ∈ Fredholm.CompactDefectStabilizationSpec.rangeChain L q) :
      inner ℂ u x = 0 := by
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    simpa only [pow_succ', Module.End.mul_apply] using hA ((A ^ p) y)
  have hsum : u ∈ (Fredholm.CompactDefectStabilizationSpec.kernelChain L q) ⊔
      (Fredholm.CompactDefectStabilizationSpec.rangeChain L q) := by
    rw [hcompl.sup_eq_top]
    trivial
  obtain ⟨n, hn, r, hr, heq⟩ := Submodule.mem_sup.mp hsum
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    inner ℂ u u = inner ℂ u (n+r) := congrArg (inner ℂ u) heq.symm
    _ = 0 := by rw [inner_add_right, horth n (hroot hn), hrange r hr, add_zero]

/-- Closed span of all nonzero generalized eigenspaces. -/
def rootSpace (T : H →L[ℂ] H) : Submodule ℂ H :=
  (⨆ z : Spec.NonzeroEigenvalues T,
    Module.End.maxGenEigenspace T.toLinearMap z.val).topologicalClosure

instance rootSpace_completeSpace (T : H →L[ℂ] H) : CompleteSpace (rootSpace T) := by
  unfold rootSpace
  infer_instance

lemma rootSpace_invariant (T : H →L[ℂ] H) :
    rootSpace T ∈ Module.End.invtSubmodule T.toLinearMap := by
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
  apply iSup_le
  intro z
  exact ((Module.End.mem_invtSubmodule_iff_map_le _).mp
    (Module.End.genEigenspace_mem_invtSubmodule T.toLinearMap z.val ⊤)).trans
      (le_iSup (fun z : Spec.NonzeroEigenvalues T =>
        Module.End.maxGenEigenspace T.toLinearMap z.val) z)

/-- Compactness of the adjoint follows from finite-rank approximation.
This proof uses the established trace-norm density and the isometry of adjoint. -/
lemma compact_adjoint_of_traceClass (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.adjoint.toLinearMap := by
  obtain ⟨F, hfr, hF, hlim, _⟩ :=
    QuasinilpotentTraceZero.exists_finite_rank_singular_approximants T hT
  have hconv := QuasinilpotentTraceZero.tendsto_of_traceNorm hT hF hlim
  apply (TraceNormIdeal.compact_iff_native T.adjoint).mpr
  apply isCompactOperator_of_tendsto (ContinuousLinearMap.adjoint.continuous.tendsto T |>.comp hconv)
  apply Filter.Eventually.of_forall
  intro n
  letI : FiniteDimensional ℂ (F n).range := hfr n
  have heq : (F n).adjoint = (F n).rangeRestrict.adjoint.comp (F n).range.subtypeL.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp]
    rfl
  change IsCompactOperator (F n).adjoint
  rw [heq]
  exact (isCompactOperator_of_locallyCompactSpace_rng (F n).rangeRestrict.adjoint).comp_clm _

lemma rootSpace_orthogonal_invariant_adjoint (T : H →L[ℂ] H) :
    (rootSpace T)ᗮ ∈ Module.End.invtSubmodule T.adjoint.toLinearMap := by
  apply ContinuousLinearMap.orthogonal_mem_invtSubmodule (T := T.adjoint)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using rootSpace_invariant T

/-- Quasinilpotence of the orthogonal compression to the complement of all
nonzero root spaces. It is essential to compress rather than to assume this
complement is invariant for T. -/
lemma residual_spectrum_subset_zero (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    let P := (rootSpace T)ᗮ.starProjection
    spectrum ℂ (P.comp (T.comp P)) ⊆ {0} := by
  classical
  let K := (rootSpace T)ᗮ
  let P : H →L[ℂ] H := K.starProjection
  let Q : H →L[ℂ] H := P.comp (T.comp P)
  change spectrum ℂ Q ⊆ {0}
  have hP : P.adjoint = P := (isSelfAdjoint_starProjection K).adjoint_eq
  have hQ : Q.adjoint = P.comp (T.adjoint.comp P) := by
    simp only [Q, ContinuousLinearMap.adjoint_comp, hP, ContinuousLinearMap.comp_assoc]
  have hc := (TraceNormIdeal.compact_iff_native T.adjoint).mp
    (compact_adjoint_of_traceClass T hT)
  have hcQ : Compactness.DefinitionsSpec.IsCompactLinearMapValue Q.adjoint.toLinearMap := by
    apply (TraceNormIdeal.compact_iff_native Q.adjoint).mpr
    rw [hQ]
    exact (hc.comp_clm P).clm_comp P
  have hspec : spectrum ℂ Q.adjoint ⊆ {0} := by
    intro w hw
    by_contra hwzero
    have hw0 : w ≠ 0 := hwzero
    obtain ⟨u, hu0, hu⟩ :=
      (Fredholm.compact_nonzero_spectrum_iff_eigenvalue Q.adjoint hcQ w hw0).mp hw
    have huK : u ∈ K := by
      have heq : w⁻¹ • Q.adjoint u = u := by simp [hu, hw0]
      rw [← heq]
      apply K.smul_mem
      rw [hQ]
      exact (K.orthogonalProjectionOnto _).property
    have hPu : P u = u := K.starProjection_eq_self_iff.mpr huK
    have hPT : P (T.adjoint u) = T.adjoint u :=
      K.starProjection_eq_self_iff.mpr (rootSpace_orthogonal_invariant_adjoint T huK)
    have huT : T.adjoint u = w • u := by
      simpa only [hQ, ContinuousLinearMap.comp_apply, hPu, hPT] using hu
    have hwspec : w ∈ spectrum ℂ T.adjoint := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr huT, hu0⟩).mem_spectrum
    have hzspec : star w ∈ spectrum ℂ T := by
      rw [← ContinuousLinearMap.star_eq_adjoint, spectrum.map_star] at hwspec
      exact hwspec
    have hz0 : star w ≠ 0 := star_ne_zero.mpr hw0
    obtain ⟨v, hv0, hv⟩ :=
      (Fredholm.compact_nonzero_spectrum_iff_eigenvalue T hT.1 (star w) hz0).mp hzspec
    let z : Spec.NonzeroEigenvalues T := ⟨star w, hz0,
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩⟩
    have hroot : Module.End.maxGenEigenspace T.toLinearMap z.val ≤ rootSpace T :=
      (le_iSup (fun z : Spec.NonzeroEigenvalues T =>
        Module.End.maxGenEigenspace T.toLinearMap z.val) z).trans
        (Submodule.le_topologicalClosure _)
    have huorth : ∀ x ∈ Module.End.maxGenEigenspace T.toLinearMap (star w),
        inner ℂ u x = 0 := by
      intro x hx
      exact ((rootSpace T).mem_orthogonal' u |>.mp huK) x (hroot hx)
    exact hu0 (adjoint_eigenvector_eq_zero_of_orthogonal T hT.1 (star w) hz0 u
      (by simpa only [star_star] using huT) huorth)
  intro z hz
  have hz' : star z ∈ spectrum ℂ Q.adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint, spectrum.map_star]
    simpa only [Set.mem_star, star_star] using hz
  have hzero : star z = 0 := Set.mem_singleton_iff.mp (hspec hz')
  simpa only [Set.mem_singleton_iff, star_eq_zero] using hzero

/-- Cyclicity removes the second projection after the quasinilpotent
compression has been shown to have zero trace. -/
lemma residual_trace_zero (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    trace (T.comp (rootSpace T)ᗮ.starProjection) = 0 := by
  let P : H →L[ℂ] H := (rootSpace T)ᗮ.starProjection
  have hTP : IsTraceClass (T.comp P) := by
    simpa only [ContinuousLinearMap.id_comp] using
      (TraceNormIdeal.two_sided_ideal ℂ H H H H T (ContinuousLinearMap.id ℂ H) P hT).1
  have hQ : IsTraceClass (P.comp (T.comp P)) := by
    simpa only [ContinuousLinearMap.comp_id] using
      (TraceNormIdeal.two_sided_ideal ℂ H H H H (T.comp P) P
        (ContinuousLinearMap.id ℂ H) hTP).1
  have hz := QuasinilpotentTraceZero.quasinilpotent_trace_zero H _ hQ
    (residual_spectrum_subset_zero T hT)
  have hcyc := TraceBasisCyclicity.trace_comp_comm (T.comp P) P hTP
  have hPP : P.comp P = P := (rootSpace T)ᗮ.isIdempotentElem_starProjection
  rw [ContinuousLinearMap.comp_assoc, hPP] at hcyc
  exact hcyc.symm.trans hz

/-- Finite sums of full nonzero root spaces, retaining all algebraic
multiplicities rather than just ordinary eigenvectors. -/
def finiteRootSpace (T : H →L[ℂ] H) (s : Finset (Spec.NonzeroEigenvalues T)) : Submodule ℂ H :=
  ⨆ z ∈ s, Module.End.maxGenEigenspace T.toLinearMap z.val

lemma finiteRootSpace_finiteDimensional (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (s : Finset (Spec.NonzeroEigenvalues T)) : FiniteDimensional ℂ (finiteRootSpace T s) := by
  letI (z : Spec.NonzeroEigenvalues T) :
      FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z.val) :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hT.1 z.property.1
  unfold finiteRootSpace
  rw [iSup_subtype']
  infer_instance

lemma finiteRootSpace_invariant (T : H →L[ℂ] H) (s : Finset (Spec.NonzeroEigenvalues T)) :
    ∀ x ∈ finiteRootSpace T s, T x ∈ finiteRootSpace T s :=
  LinearMap.mapsTo_biSup_of_mapsTo (s : Set (Spec.NonzeroEigenvalues T))
    (fun z => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val)

/-- A finite-dimensional nilpotent shift has exactly the expected trace. -/
lemma root_restriction_trace (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (z : Spec.NonzeroEigenvalues T) :
    let hE := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val
    LinearMap.trace ℂ _ (T.toLinearMap.restrict hE) =
      (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val := by
  let E := Module.End.maxGenEigenspace T.toLinearMap z.val
  letI : FiniteDimensional ℂ E :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hT.1 z.property.1
  let hE : ∀ x ∈ E, T.toLinearMap x ∈ E :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val
  let g : Module.End ℂ E := T.toLinearMap.restrict hE
  have hg : g.maxGenEigenspace z.val = ⊤ := by
    rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
    exact Submodule.comap_subtype_self E
  have hN : IsNilpotent (g - z.val • 1) := by
    apply ((LinearMap.charpoly_nilpotent_tfae (g - z.val • 1)).out 3 1).mp
    intro x
    exact (Module.End.mem_maxGenEigenspace g z.val x).mp (by rw [hg]; trivial)
  have ht : LinearMap.trace ℂ E (g - z.val • 1) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [map_sub, map_smul, LinearMap.trace_one] at ht
  change LinearMap.trace ℂ E g = _
  simpa only [WeylProducts.Spec.algebraicMultiplicity, smul_eq_mul, mul_comm] using sub_eq_zero.mp ht

/-- The trace of a finite invariant compression is the ordinary algebraic
trace of the actual restriction. Cyclicity avoids choosing an adapted basis. -/
lemma trace_finite_compression (T : H →L[ℂ] H) (M : Submodule ℂ H)
    [FiniteDimensional ℂ M] (hM : ∀ x ∈ M, T x ∈ M) :
    trace (T.comp M.starProjection) = LinearMap.trace ℂ M (T.toLinearMap.restrict hM) := by
  let g : H →L[ℂ] M := M.orthogonalProjectionOnto
  let A : M →L[ℂ] H := T.comp M.subtypeL
  have hg : IsTraceClass g := TraceNormIdeal.finite_rank_traceClass g
  have hleft : A.comp g = T.comp M.starProjection := rfl
  have hright : g.comp A = T.restrict hM := by
    apply ContinuousLinearMap.ext
    intro x
    exact M.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hM x x.property⟩
  have ht := TraceBasisCyclicity.trace_comp_comm g A hg
  rw [hleft, hright, QuasinilpotentTraceZero.trace_eq_linearMap_trace (T.restrict hM)] at ht
  exact ht

/-- Finite spectral traces include every Jordan multiplicity. -/
lemma finite_root_trace (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (s : Finset (Spec.NonzeroEigenvalues T)) :
    letI := finiteRootSpace_finiteDimensional T hT s
    trace (T.comp (finiteRootSpace T s).starProjection) =
      ∑ z ∈ s, (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val := by
  classical
  letI := finiteRootSpace_finiteDimensional T hT s
  letI (z : Spec.NonzeroEigenvalues T) :
      FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z.val) :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hT.1 z.property.1
  rw [trace_finite_compression T _ (finiteRootSpace_invariant T s)]
  have hind : iSupIndep (fun z : s => Module.End.maxGenEigenspace T.toLinearMap z.val.val) :=
    (Module.End.independent_maxGenEigenspace T.toLinearMap).comp
      (Subtype.val_injective.comp Subtype.val_injective)
  rw [LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup s hind
    (fun z : Spec.NonzeroEigenvalues T =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val)
    (finiteRootSpace T s) rfl (finiteRootSpace_invariant T s)]
  apply Finset.sum_congr rfl
  intro z _
  exact root_restriction_trace T hT z

/-- A trace-class expansion computes the trace against a contraction. -/
lemma trace_comp_contraction_expansion (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H H T)
    (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) :
    trace (T.comp A) = ∑' j, (S.sigma j : ℂ) * inner ℂ (S.rightVector j) (A (S.leftVector j)) := by
  have hs := (singularSystem_sum ℂ H H T hT S).1
  have ht : trace (A.comp T) =
      ∑' j, (S.sigma j : ℂ) * inner ℂ (S.rightVector j) (A (S.leftVector j)) := by
    apply TraceBasisCyclicity.trace_of_expansion (A.comp T) S.sigma
      (fun j => A (S.leftVector j)) S.rightVector (fun j => (S.positive j).le) hs 1
    · intro j
      have hb := A.le_opNorm (S.leftVector j)
      rw [S.left_orthonormal.norm_eq_one, mul_one] at hb
      have hnorm : ‖A (S.leftVector j)‖ ≤ 1 := hb.trans hA
      rw [S.right_orthonormal.norm_eq_one]
      nlinarith [norm_nonneg (A (S.leftVector j))]
    · intro x
      simpa only [ContinuousLinearMap.comp_apply, map_smul] using (S.expansion x).mapL A
  exact (TraceBasisCyclicity.trace_comp_comm T A hT).symm.trans ht

/-- Strong convergence of uniformly contractive operators can be tested by
any trace-class operator, even when the ambient Hilbert space is nonseparable. -/
lemma trace_comp_tendsto_of_strong_contractions {ι : Type*} {l : Filter ι}
    (T : H →L[ℂ] H) (hT : IsTraceClass T) (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hpoint : ∀ x, Filter.Tendsto (fun i => A i x) l (nhds (B x))) :
    Filter.Tendsto (fun i => trace (T.comp (A i))) l (nhds (trace (T.comp B))) := by
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ H H T hT.1
  have hs := (singularSystem_sum ℂ H H T hT S).1
  simp_rw [trace_comp_contraction_expansion T hT S B hB,
    trace_comp_contraction_expansion T hT S _ (hA _)]
  apply tendsto_tsum_of_dominated_convergence hs
  · intro j
    exact (((innerSL ℂ (S.rightVector j)).continuous.tendsto (B (S.leftVector j))).comp
      (hpoint (S.leftVector j))).const_mul (S.sigma j : ℂ)
  · apply Filter.Eventually.of_forall
    intro i j
    have hnorm : ‖A i (S.leftVector j)‖ ≤ 1 := by
      have hb := (A i).le_opNorm (S.leftVector j)
      rw [S.left_orthonormal.norm_eq_one, mul_one] at hb
      exact hb.trans (hA i)
    have hin : ‖inner ℂ (S.rightVector j) (A i (S.leftVector j))‖ ≤ 1 := by
      simpa only [S.right_orthonormal.norm_eq_one, one_mul] using
        (norm_inner_le_norm (S.rightVector j) (A i (S.leftVector j))).trans
          (by simpa only [S.right_orthonormal.norm_eq_one, one_mul] using hnorm)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.positive j)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hin (S.positive j).le

lemma finiteRootSpace_mono (T : H →L[ℂ] H) : Monotone (finiteRootSpace T) := by
  intro s t hst
  apply iSup₂_le
  intro z hz
  exact le_biSup (fun z : Spec.NonzeroEigenvalues T =>
    Module.End.maxGenEigenspace T.toLinearMap z.val) (hst hz)

lemma iSup_finiteRootSpace (T : H →L[ℂ] H) :
    (⨆ s : Finset (Spec.NonzeroEigenvalues T), finiteRootSpace T s) =
      ⨆ z : Spec.NonzeroEigenvalues T, Module.End.maxGenEigenspace T.toLinearMap z.val := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro s
    exact iSup₂_le (fun z _ => le_iSup
      (fun z : Spec.NonzeroEigenvalues T => Module.End.maxGenEigenspace T.toLinearMap z.val) z)
  · apply iSup_le
    intro z
    exact le_iSup_of_le {z} (le_biSup
      (fun z : Spec.NonzeroEigenvalues T => Module.End.maxGenEigenspace T.toLinearMap z.val)
      (Finset.mem_singleton_self z))

set_option backward.isDefEq.respectTransparency false in
/-- Finite algebraic spectral traces converge to the trace on the closed
root space. Completeness and convergence here come from orthogonal projection,
not from any claim that algebraic Riesz projections are uniformly bounded. -/
lemma root_trace_hasSum (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    HasSum (fun z : Spec.NonzeroEigenvalues T =>
      (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val)
      (trace (T.comp (rootSpace T).starProjection)) := by
  classical
  letI : (rootSpace T).HasOrthogonalProjection := inferInstance
  letI : (⨆ s : Finset (Spec.NonzeroEigenvalues T),
      finiteRootSpace T s).topologicalClosure.HasOrthogonalProjection := inferInstance
  letI (s : Finset (Spec.NonzeroEigenvalues T)) : FiniteDimensional ℂ (finiteRootSpace T s) :=
    finiteRootSpace_finiteDimensional T hT s
  have hpoint (x : H) :
      Filter.Tendsto (fun s => (finiteRootSpace T s).starProjection x) Filter.atTop
        (nhds ((rootSpace T).starProjection x)) := by
    have h := Submodule.starProjection_tendsto_closure_iSup (finiteRootSpace T)
      (finiteRootSpace_mono T) x
    simpa only [iSup_finiteRootSpace, rootSpace] using h
  have ht := trace_comp_tendsto_of_strong_contractions T hT
    (fun s => (finiteRootSpace T s).starProjection) (rootSpace T).starProjection
    (fun s => (finiteRootSpace T s).starProjection_norm_le) (rootSpace T).starProjection_norm_le hpoint
  exact ht.congr' (Filter.Eventually.of_forall
    (fun s : Finset (Spec.NonzeroEigenvalues T) => finite_root_trace T hT s))

/-- The complement contributes zero, so the closed root-space trace is the
entire trace even when the root vectors are not complete in the Hilbert space. -/
lemma trace_rootSpace_eq_trace (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    trace (T.comp (rootSpace T).starProjection) = trace T := by
  have hTP : IsTraceClass (T.comp (rootSpace T)ᗮ.starProjection) := by
    simpa only [ContinuousLinearMap.id_comp] using
      (TraceNormIdeal.two_sided_ideal ℂ H H H H T (ContinuousLinearMap.id ℂ H)
        (rootSpace T)ᗮ.starProjection hT).1
  have heq : T.comp (rootSpace T).starProjection = T - T.comp (rootSpace T)ᗮ.starProjection := by
    ext x
    simp only [Submodule.starProjection_orthogonal, ContinuousLinearMap.comp_apply,
      sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [heq, QuasinilpotentTraceZero.trace_sub H _ _ hT hTP, residual_trace_zero T hT, sub_zero]

/-- Lidskii's trace formula, with the full algebraic multiset and absolute
convergence, for arbitrary complex Hilbert spaces. No normality or separability
is assumed. -/
theorem lidskii : Spec.Lidskii.{u} := by
  intro H _ _ _ T hT
  have habs := (absolute_eigenvalue_sum H T hT).1
  have hs := habs.of_norm
  refine ⟨habs, ?_⟩
  have hfinite (z : Spec.NonzeroEigenvalues T) :
      HasSum (fun i : Fin (WeylProducts.Spec.algebraicMultiplicity T z.val) =>
        Spec.eigenvalue T ⟨z, i⟩)
        ((WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val) := by
    simpa only [Spec.eigenvalue, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using
      (hasSum_fintype (fun _ : Fin (WeylProducts.Spec.algebraicMultiplicity T z.val) => z.val))
  have heq := (hs.hasSum.sigma hfinite).unique (root_trace_hasSum T hT)
  have hsum := hs.hasSum
  rw [heq.trans (trace_rootSpace_eq_trace T hT)] at hsum
  exact hsum

end ExpandedFA.TraceIdeals.Lidskii
