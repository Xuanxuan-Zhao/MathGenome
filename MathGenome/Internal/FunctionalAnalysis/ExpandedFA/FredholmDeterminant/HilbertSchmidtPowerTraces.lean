import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.Lidskii

noncomputable section
set_option maxHeartbeats 800000
universe u
namespace ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces
open TraceIdeals
open TraceClassDefinitions HilbertSchmidtDefinitions
open scoped BigOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The square sum on any finite orthonormal family is bounded by the
canonical Hilbert–Schmidt square, with no countability restriction. -/
lemma finite_orthonormal_square_le (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T)
    {ι : Type*} [Fintype ι] (e : ι → H) (he : Orthonormal ℂ e) :
    ∑ i, ‖T (e i)‖ ^ 2 ≤ (hilbertSchmidtSquare T).toReal := by
  classical
  obtain ⟨w, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let f : ι → w := fun i => ⟨e i, hsub ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun i j hij => he.linearIndependent.injective (congrArg Subtype.val hij)
  have heq (i : ι) : b (f i) = e i := congrFun hb (f i)
  have hbase := HilbertSchmidtBasis.hilbertBasis_isBasis b
  have hs := (finiteness_in_basis T b hbase).mp hT
  have hn := (normSquare_in_basis ⟨T, hT⟩ b hbase).2
  rw [HilbertSchmidtBasis.square_of_norm] at hn
  rw [hn]
  calc
    ∑ i, ‖T (e i)‖ ^ 2 = ∑ j ∈ Finset.univ.map ⟨f, hf⟩, ‖T (b j)‖ ^ 2 := by
      simp only [Finset.sum_map, Function.Embedding.coeFn_mk, heq]
    _ ≤ ∑' j, ‖T (b j)‖ ^ 2 := hs.sum_le_tsum _ (fun j _ => sq_nonneg _)

/-- A finite-family proof of S₂ S₂ ⊆ S₁. A coarse square bound suffices
for membership; no unit-vector normalization or nonzero-space assumption. -/
lemma hilbertSchmidt_comp_traceClass (A B : H →L[ℂ] H)
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) : IsTraceClass (A.comp B) := by
  have hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue (A.comp B).toLinearMap := by
    apply (TraceNormIdeal.compact_iff_native _).mpr
    exact ((TraceNormIdeal.compact_iff_native A).mp
      (HilbertSchmidtBasis.compactness A hA)).comp_clm B
  apply (TraceNormIdeal.traceClass_of_finite_family_bound (A.comp B) hc
    ((hilbertSchmidtSquare A.adjoint).toReal + (hilbertSchmidtSquare B).toReal) ?_).1
  intro n a b ha hb
  calc
    ∑ i, ‖inner ℂ (a i) ((A.comp B) (b i))‖ ≤
        ∑ i, (‖A.adjoint (a i)‖ ^ 2 + ‖B (b i)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [ContinuousLinearMap.comp_apply, ← A.adjoint_inner_left]
      apply (norm_inner_le_norm _ _).trans
      have hx := sq_nonneg (‖A.adjoint (a i)‖ - ‖B (b i)‖)
      have hy := sq_nonneg ‖A.adjoint (a i)‖
      have hz := sq_nonneg ‖B (b i)‖
      nlinarith only [hx, hy, hz]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (finite_orthonormal_square_le A.adjoint
        ((HilbertSchmidtBasis.adjoint_finiteness A).mpr hA) a ha)
        (finite_orthonormal_square_le B hB b hb)

theorem traceClass_powers : Spec.TraceClassPowers.{u} := by
  intro H _ _ _ T hT n
  induction n with
  | zero => simpa only [zero_add, pow_two, ContinuousLinearMap.mul_def] using
      hilbertSchmidt_comp_traceClass T T hT hT
  | succ n ih =>
      have h := (TraceNormIdeal.two_sided_ideal ℂ H H H H (T ^ (n + 2)) T
        (ContinuousLinearMap.id ℂ H) ih).1
      simp only [ContinuousLinearMap.comp_id] at h
      change IsTraceClass (T * T ^ (n + 2)) at h
      simpa only [← pow_succ', Nat.succ_add] using h

/-- Invariance passes to every power, expressed for the actual continuous map. -/
lemma power_invariant (T : H →L[ℂ] H) (M : Submodule ℂ H)
    (hM : ∀ x ∈ M, T x ∈ M) (p : ℕ) : ∀ x ∈ M, (T ^ p) x ∈ M := by
  simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe] using
    Module.End.pow_apply_mem_of_forall_mem p hM

/-- Nonzero generalized eigenspaces of a compact map have finite dimension. -/
lemma finiteRootSpace_finiteDimensional (T : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (s : Finset (Lidskii.Spec.NonzeroEigenvalues T)) :
    FiniteDimensional ℂ (Lidskii.finiteRootSpace T s) := by
  letI (z : Lidskii.Spec.NonzeroEigenvalues T) :
      FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z.val) :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hc z.property.1
  unfold Lidskii.finiteRootSpace
  rw [iSup_subtype']
  infer_instance

/-- On a finite-dimensional root space the nilpotent part contributes zero
to the trace of every power, including its full algebraic multiplicity. -/
lemma root_restriction_power_trace (T : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (z : Lidskii.Spec.NonzeroEigenvalues T) (p : ℕ) :
    let hE := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val
    LinearMap.trace ℂ _ ((T.toLinearMap.restrict hE) ^ p) =
      (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val ^ p := by
  let E := Module.End.maxGenEigenspace T.toLinearMap z.val
  letI : FiniteDimensional ℂ E :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hc z.property.1
  let hE : ∀ x ∈ E, T.toLinearMap x ∈ E :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val
  let g : Module.End ℂ E := T.toLinearMap.restrict hE
  have hg : g.maxGenEigenspace z.val = ⊤ := by
    rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
    exact Submodule.comap_subtype_self E
  have hN : IsNilpotent (g - algebraMap ℂ (Module.End ℂ E) z.val) := by
    apply ((LinearMap.charpoly_nilpotent_tfae
      (g - algebraMap ℂ (Module.End ℂ E) z.val)).out 3 1).mp
    intro x
    exact (Module.End.mem_maxGenEigenspace g z.val x).mp (by rw [hg]; trivial)
  change LinearMap.trace ℂ E (g ^ p) = _
  induction p with
  | zero => simp [WeylProducts.Spec.algebraicMultiplicity, E]
  | succ p ih =>
      rw [pow_succ]
      change LinearMap.trace ℂ E ((g ^ p).comp g) = _
      rw [LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent z.val
        (Commute.refl g |>.pow_left p) hN, ih, pow_succ]
      ring

set_option backward.isDefEq.respectTransparency false in
lemma finite_root_power_trace (T : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (s : Finset (Lidskii.Spec.NonzeroEigenvalues T)) (p : ℕ) :
    letI := finiteRootSpace_finiteDimensional T hc s
    trace ((T ^ p).comp (Lidskii.finiteRootSpace T s).starProjection) =
      ∑ z ∈ s, (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val ^ p := by
  classical
  letI := finiteRootSpace_finiteDimensional T hc s
  letI (z : Lidskii.Spec.NonzeroEigenvalues T) :
      FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z.val) :=
    WeylProducts.compact_maxGenEigenspace_finiteDimensional T hc z.property.1
  rw [Lidskii.trace_finite_compression (T ^ p) _
    (power_invariant T _ (Lidskii.finiteRootSpace_invariant T s) p)]
  have hind : iSupIndep (fun z : s => Module.End.maxGenEigenspace T.toLinearMap z.val.val) :=
    (Module.End.independent_maxGenEigenspace T.toLinearMap).comp
      (Subtype.val_injective.comp Subtype.val_injective)
  rw [LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup s hind
    (fun z : Lidskii.Spec.NonzeroEigenvalues T => power_invariant T _
      (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val) p)
    (Lidskii.finiteRootSpace T s) rfl
    (power_invariant T _ (Lidskii.finiteRootSpace_invariant T s) p)]
  apply Finset.sum_congr rfl
  intro z _
  let E := Module.End.maxGenEigenspace T.toLinearMap z.val
  let hE : ∀ x ∈ E, T.toLinearMap x ∈ E :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl T.toLinearMap) z.val
  have hpow : (T.toLinearMap.restrict hE) ^ p =
      (T ^ p).toLinearMap.restrict (power_invariant T E hE p) := by
    simpa only [ContinuousLinearMap.toLinearMap_pow] using
      (Module.End.pow_restrict (f' := T.toLinearMap) p hE)
  have ht := root_restriction_power_trace T hc z p
  change LinearMap.trace ℂ E ((T.toLinearMap.restrict hE) ^ p) = _ at ht
  rw [hpow] at ht
  exact ht

open Lidskii (rootSpace)

/-- The residual compression is quasinilpotent already for compact T.
Trace class of T itself is unnecessary. -/
lemma residual_spectrum_subset_zero (T : H →L[ℂ] H)
    (hcT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (hcAdj : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.adjoint.toLinearMap) :
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
    hcAdj
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
      K.starProjection_eq_self_iff.mpr (Lidskii.rootSpace_orthogonal_invariant_adjoint T huK)
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
      (Fredholm.compact_nonzero_spectrum_iff_eigenvalue T hcT (star w) hz0).mp hzspec
    let z : Lidskii.Spec.NonzeroEigenvalues T := ⟨star w, hz0,
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩⟩
    have hroot : Module.End.maxGenEigenspace T.toLinearMap z.val ≤ rootSpace T :=
      (le_iSup (fun z : Lidskii.Spec.NonzeroEigenvalues T =>
        Module.End.maxGenEigenspace T.toLinearMap z.val) z).trans
        (Submodule.le_topologicalClosure _)
    have huorth : ∀ x ∈ Module.End.maxGenEigenspace T.toLinearMap (star w),
        inner ℂ u x = 0 := by
      intro x hx
      exact ((rootSpace T).mem_orthogonal' u |>.mp huK) x (hroot hx)
    exact hu0 (Lidskii.adjoint_eigenvector_eq_zero_of_orthogonal T hcT (star w) hz0 u
      (by simpa only [star_star] using huT) huorth)
  intro z hz
  have hz' : star z ∈ spectrum ℂ Q.adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint, spectrum.map_star]
    simpa only [Set.mem_star, star_star] using hz
  have hzero : star z = 0 := Set.mem_singleton_iff.mp (hspec hz')
  simpa only [Set.mem_singleton_iff, star_eq_zero] using hzero


/-- Compression to the orthogonal complement of an invariant subspace is
multiplicative on positive powers. -/
lemma residual_power (T : H →L[ℂ] H) :
    let P := (rootSpace T)ᗮ.starProjection
    ∀ p : ℕ, (P.comp (T.comp P)) ^ (p + 1) = P.comp (T ^ (p + 1)) := by
  let M := rootSpace T
  let P : H →L[ℂ] H := Mᗮ.starProjection
  have hinv : ∀ x ∈ M, T x ∈ M := Lidskii.rootSpace_invariant T
  have hzero : P.comp (T.comp M.starProjection) = 0 := by
    ext x
    exact M.starProjection_orthogonal_apply_eq_zero
      (hinv _ ((M.orthogonalProjectionOnto x).property))
  have hPTP : P.comp (T.comp P) = P.comp T := by
    have hP : P = ContinuousLinearMap.id ℂ H - M.starProjection :=
      M.starProjection_orthogonal
    nth_rw 2 [hP]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.comp_sub, hzero, sub_zero]
  change ∀ p : ℕ, (P.comp (T.comp P)) ^ (p + 1) = P.comp (T ^ (p + 1))
  intro p
  induction p with
  | zero => simpa only [zero_add, pow_one] using hPTP
  | succ p ih =>
      rw [pow_succ', ih]
      change (P.comp (T.comp P)).comp (P.comp (T ^ (p+1))) = _
      rw [hPTP, ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc P T P,
        hPTP, ContinuousLinearMap.comp_assoc]
      exact congrArg (fun A : H →L[ℂ] H => P.comp A) (pow_succ' T (p+1)).symm

/-- Every trace-class positive power has zero trace on the residual space.
T itself is only required to be Hilbert–Schmidt. -/
lemma residual_power_trace_zero (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T)
    (p : ℕ) (hpower : IsTraceClass (T ^ (p + 1))) :
    trace ((T ^ (p + 1)).comp (rootSpace T)ᗮ.starProjection) = 0 := by
  let P : H →L[ℂ] H := (rootSpace T)ᗮ.starProjection
  let Q : H →L[ℂ] H := P.comp (T.comp P)
  have hTC : IsTraceClass (Q ^ (p + 1)) := by
    rw [residual_power T p]
    simpa only [ContinuousLinearMap.comp_id] using
      (TraceNormIdeal.two_sided_ideal ℂ H H H H (T ^ (p+1)) P
        (ContinuousLinearMap.id ℂ H) hpower).1
  have hspec : spectrum ℂ (Q ^ (p + 1)) ⊆ {0} := by
    rw [spectrum.map_pow_of_pos Q (by omega)]
    rintro z ⟨w, hw, rfl⟩
    have hz := residual_spectrum_subset_zero T (HilbertSchmidtBasis.compactness T hT)
      (HilbertSchmidtBasis.compactness T.adjoint
        ((HilbertSchmidtBasis.adjoint_finiteness T).mpr hT)) hw
    simpa only [Set.mem_singleton_iff.mp hz, zero_pow (by omega : p + 1 ≠ 0)] using
      (Set.mem_singleton (0 : ℂ))
  have hzero := QuasinilpotentTraceZero.quasinilpotent_trace_zero H _ hTC hspec
  rw [residual_power T p] at hzero
  exact (TraceBasisCyclicity.trace_comp_comm (T ^ (p+1)) P hpower).symm.trans hzero

set_option backward.isDefEq.respectTransparency false in
/-- The net of finite full root spaces computes spectral power traces. -/
lemma root_power_trace_hasSum (T : H →L[ℂ] H)
    (hc : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (p : ℕ) (hpower : IsTraceClass (T ^ p)) :
    HasSum (fun z : Lidskii.Spec.NonzeroEigenvalues T =>
      (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val ^ p)
      (trace ((T ^ p).comp (rootSpace T).starProjection)) := by
  classical
  letI : (rootSpace T).HasOrthogonalProjection := inferInstance
  letI : (⨆ s : Finset (Lidskii.Spec.NonzeroEigenvalues T),
      Lidskii.finiteRootSpace T s).topologicalClosure.HasOrthogonalProjection := inferInstance
  letI (s : Finset (Lidskii.Spec.NonzeroEigenvalues T)) :
      FiniteDimensional ℂ (Lidskii.finiteRootSpace T s) :=
    finiteRootSpace_finiteDimensional T hc s
  have hpoint (x : H) :
      Filter.Tendsto (fun s => (Lidskii.finiteRootSpace T s).starProjection x) Filter.atTop
        (nhds ((rootSpace T).starProjection x)) := by
    have h := Submodule.starProjection_tendsto_closure_iSup (Lidskii.finiteRootSpace T)
      (Lidskii.finiteRootSpace_mono T) x
    simpa only [Lidskii.iSup_finiteRootSpace, rootSpace] using h
  have ht := Lidskii.trace_comp_tendsto_of_strong_contractions (T ^ p) hpower
    (fun s => (Lidskii.finiteRootSpace T s).starProjection) (rootSpace T).starProjection
    (fun s => (Lidskii.finiteRootSpace T s).starProjection_norm_le)
    (rootSpace T).starProjection_norm_le hpoint
  exact ht.congr' (Filter.Eventually.of_forall
    (fun s : Finset (Lidskii.Spec.NonzeroEigenvalues T) => finite_root_power_trace T hc s p))

lemma power_trace_rootSpace_eq_trace (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T)
    (p : ℕ) (hpower : IsTraceClass (T ^ (p + 1))) :
    trace ((T ^ (p + 1)).comp (rootSpace T).starProjection) = trace (T ^ (p + 1)) := by
  have hTP : IsTraceClass ((T ^ (p + 1)).comp (rootSpace T)ᗮ.starProjection) := by
    simpa only [ContinuousLinearMap.id_comp] using
      (TraceNormIdeal.two_sided_ideal ℂ H H H H (T ^ (p+1)) (ContinuousLinearMap.id ℂ H)
        (rootSpace T)ᗮ.starProjection hpower).1
  have heq : (T ^ (p+1)).comp (rootSpace T).starProjection =
      (T ^ (p+1)) - (T ^ (p+1)).comp (rootSpace T)ᗮ.starProjection := by
    ext x
    simp only [Submodule.starProjection_orthogonal, ContinuousLinearMap.comp_apply,
      sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [heq, QuasinilpotentTraceZero.trace_sub H _ _ hpower hTP,
    residual_power_trace_zero T hT p hpower, sub_zero]

/-- Unordered scalar summability is absolute. Splitting each finite
multiplicity fiber therefore gives the full algebraic eigenvalue multiset. -/
lemma split_multiplicities (T : H →L[ℂ] H) (p : ℕ) (a : ℂ)
    (hs : HasSum (fun z : Lidskii.Spec.NonzeroEigenvalues T =>
      (WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val ^ p) a) :
    Summable (fun i : Lidskii.Spec.EigenvalueIndex T => ‖Lidskii.Spec.eigenvalue T i ^ p‖) ∧
    HasSum (fun i : Lidskii.Spec.EigenvalueIndex T => Lidskii.Spec.eigenvalue T i ^ p) a := by
  classical
  have habs := hs.summable.norm
  have hsum : Summable (fun i : Lidskii.Spec.EigenvalueIndex T =>
      ‖Lidskii.Spec.eigenvalue T i ^ p‖) := by
    apply (summable_sigma_of_nonneg (fun i => norm_nonneg
      (Lidskii.Spec.eigenvalue T i ^ p))).mpr
    refine ⟨fun z => (hasSum_fintype _).summable, ?_⟩
    convert habs using 1
    ext z
    simp only [Lidskii.Spec.eigenvalue, tsum_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_mul,
      Complex.norm_natCast]
  refine ⟨hsum, ?_⟩
  have htotal := hsum.of_norm.hasSum
  have hfiber (z : Lidskii.Spec.NonzeroEigenvalues T) :
      HasSum (fun i : Fin (WeylProducts.Spec.algebraicMultiplicity T z.val) =>
        Lidskii.Spec.eigenvalue T ⟨z, i⟩ ^ p)
        ((WeylProducts.Spec.algebraicMultiplicity T z.val : ℂ) * z.val ^ p) := by
    simpa only [Lidskii.Spec.eigenvalue, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
      hasSum_fintype (fun _ : Fin (WeylProducts.Spec.algebraicMultiplicity T z.val) => z.val ^ p)
  have heq := (htotal.sigma hfiber).unique hs
  exact heq ▸ htotal

theorem power_traces : Spec.PowerTraces.{u} := by
  intro H _ _ _ T hT n
  have hTC := traceClass_powers H T hT n
  have hs := root_power_trace_hasSum T (HilbertSchmidtBasis.compactness T hT) (n+2) hTC
  rw [power_trace_rootSpace_eq_trace T hT (n+1) hTC] at hs
  exact split_multiplicities T (n+2) _ hs

theorem full_conclusion : Spec.FullConclusion.{u} := ⟨traceClass_powers, power_traces⟩

end ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces
