import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.Multipliers
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.Liouville
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.Monodromy

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Operator

namespace D13Unified.Ch14.Multipliers
open Ch06.StateDerivative Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch14.Multipliers
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinates are a continuous linear map on the finite-dimensional operator space. -/
def coordinates [FiniteDimensional ℝ E] {n : ℕ} (b : Module.Basis (Fin n) ℝ E) :
    (E →L[ℝ] E) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ))

@[simp] lemma coordinates_apply [FiniteDimensional ℝ E] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (L : E →L[ℝ] E) :
    coordinates b L = inBasis b L := rfl

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma complete_time {p : E} (F : AutonomousODE E) (hc : Ch11.Orbits.IsComplete F p) (t : ℝ) :
    t ∈ (flowInterval F p).carrier := by
  rw [hc]
  exact mem_univ t

/-- Normalized variation and the upstream canonical principal matrix agree by
uniqueness of the matrix IVP, in every basis. -/
theorem variation_conclusions (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (p : E) (hp : p ∈ F.domain) (T : ℝ)
    (hc : Ch11.Orbits.IsComplete F p)
    (hper : Function.Periodic (fun t => flow F t p) T) :
    VariationConclusions F p T := by
  have hx := flow_ivp F hF hp
  have htime := complete_time F hc
  have hA : Continuous (coefficient F p) := by
    have hco : ContinuousOn (coefficient F p) (flowInterval F p).carrier :=
      (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
        hx.1.1.continuousOn (fun t ht => hx.1.2.1 t ht)
    rw [hc] at hco
    exact continuousOn_univ.mp hco
  have hV := (Ch06.StateDerivative.maximal_domain_derivative F hF).2.2 p hp
  have hVd (t : ℝ) : HasDerivAt (orbitVariation F p)
      ((coefficient F p t).comp (orbitVariation F p t)) t := hV.2.1 t (htime t)
  refine ⟨hA, (fun t => by simp only [coefficient, hper t]), hV.1, hVd, ?_, ?_⟩
  · intro n b t
    have hAc : Continuous (fun t => inBasis b (coefficient F p t)) :=
      (coordinates b).continuous.comp hA
    have hYc : Continuous (fun t => inBasis b (orbitVariation F p t)) :=
      (coordinates b).continuous.comp (continuous_iff_continuousAt.mpr
        (fun t => (hVd t).continuousAt))
    have hY0 : inBasis b (orbitVariation F p 0) = 1 := by
      simp [inBasis, hV.1]
    have hYd (t : ℝ) : HasDerivAt (fun r => inBasis b (orbitVariation F p r))
        (inBasis b (coefficient F p t) * inBasis b (orbitVariation F p t)) t := by
      convert! (coordinates b).hasFDerivAt.comp_hasDerivAt t (hVd t) using 1
      exact (LinearMap.toMatrix_comp b b b _ _).symm
    exact (Ch07.EvolutionMatrix.evolution ℝ n Ch08.Monodromy.wholeTime
      (fun r => inBasis b (coefficient F p r)) 0 (mem_univ 0) hAc.continuousOn).2.2.2.2.2
      _ hYc.continuousOn hY0 (fun r _ => (hYd r).hasDerivWithinAt) (mem_univ t)
  · have hret : flow F T p = p := by
      simpa only [zero_add, hx.2.2] using hper 0
    simpa only [hret] using Ch11.Flow.flow_pushforward F hF (T,p) ⟨hp,htime T⟩

/-- Split a vector into its velocity coordinate and its transverse projection. -/
def sectionSplit (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) :
    E ≃ₗ[ℝ] (ℝ × ℓ.ker) where
  toFun x := (ℓ x / ℓ a, ReturnBranch.transverseProjection ℓ a ha x)
  invFun x := x.1 • a + (x.2 : E)
  left_inv x := by
    dsimp
    rw [ReturnBranch.transverseProjection_apply]
    abel
  right_inv x := by
    rcases x with ⟨c,v⟩
    apply Prod.ext
    · simp [map_add, map_smul, show ℓ (v : E) = 0 from v.property, ha]
    · apply Subtype.ext
      simp [map_add, map_smul]
  map_add' x y := by
    apply Prod.ext <;> simp [add_div]
  map_smul' c x := by
    apply Prod.ext <;> simp [mul_div_assoc]

lemma section_dimension (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) :
    Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E := by
  have h := (sectionSplit ℓ a ha).finrank_eq
  simpa [add_comm] using h.symm

omit [FiniteDimensional ℝ E] in
/-- Invariance of the genuine velocity line. -/
lemma velocityLine_invariant (a : E) (M : E →ₗ[ℝ] E) (hMa : M a = a) :
    Submodule.span ℝ {a} ≤ (Submodule.span ℝ {a}).comap M := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  simp [hMa]

/-- The class map restricted to the section is bijective. Surjectivity uses
subtracting the velocity component, and injectivity uses transversality. -/
def sectionQuotientEquiv (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0) :
    ℓ.ker ≃ₗ[ℝ] (E ⧸ Submodule.span ℝ {a}) := by
  let N := Submodule.span ℝ {a}
  let q : ℓ.ker →ₗ[ℝ] E ⧸ N := N.mkQ.comp ℓ.ker.subtype
  apply LinearEquiv.ofBijective q
  constructor
  · apply (injective_iff_map_eq_zero q).mpr
    intro v hv
    have hvN : (v : E) ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hv
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hvN
    have hc0 : c = 0 := by
      have h := congrArg ℓ hc
      rw [map_smul, show ℓ (v : E) = 0 from v.property, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right ha
    apply Subtype.ext
    simpa [hc0] using hc.symm
  · intro z
    obtain ⟨x,rfl⟩ := N.mkQ_surjective z
    refine ⟨ReturnBranch.transverseProjection ℓ a ha x, ?_⟩
    change N.mkQ _ = N.mkQ x
    apply (Submodule.Quotient.eq N).mpr
    change ((ReturnBranch.transverseProjection ℓ a ha x : E) - x) ∈ N
    rw [ReturnBranch.transverseProjection_apply]
    have he : x - (ℓ x / ℓ a) • a - x = -(ℓ x / ℓ a) • a := by module
    rw [he]
    exact Submodule.smul_mem N _ (Submodule.mem_span_singleton_self a)

omit [FiniteDimensional ℝ E] in
@[simp] lemma sectionQuotientEquiv_apply (ℓ : E →L[ℝ] ℝ) (a : E)
    (ha : ℓ a ≠ 0) (v : ℓ.ker) :
    sectionQuotientEquiv ℓ a ha v = (Submodule.span ℝ {a}).mkQ (v : E) := rfl

omit [FiniteDimensional ℝ E] in
/-- Quotient conjugacy follows from the actual return derivative formula. -/
lemma quotient_conjugacy (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0)
    (M : E →L[ℝ] E) (hMa : M a = a) (B : ℓ.ker →L[ℝ] ℓ.ker)
    (hB : ∀ v : ℓ.ker, (B v : E) = M (v : E) - (ℓ (M (v : E)) / ℓ a) • a) :
    (sectionQuotientEquiv ℓ a ha).conj B.toLinearMap =
      (Submodule.span ℝ {a}).mapQ (Submodule.span ℝ {a}) M.toLinearMap
        (velocityLine_invariant a M.toLinearMap hMa) := by
  let e := sectionQuotientEquiv ℓ a ha
  apply LinearMap.ext
  intro z
  obtain ⟨v,rfl⟩ := e.surjective z
  rw [LinearEquiv.conj_apply_apply]
  change e (B (e.symm (e v))) = _
  rw [e.symm_apply_apply]
  simp only [e, sectionQuotientEquiv_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
  apply (Submodule.Quotient.eq _).mpr
  rw [hB]
  have he : M (v : E) - (ℓ (M (v : E)) / ℓ a) • a - M (v : E) =
      -(ℓ (M (v : E)) / ℓ a) • a := by module
  change M (v : E) - (ℓ (M (v : E)) / ℓ a) • a - M (v : E) ∈ _
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)

/-- A block triangular operator with a fixed one-dimensional first block.
This is a polynomial identity and therefore retains every multiplicity. -/
lemma triangular_invariants {K : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] (L : (ℝ × K) →ₗ[ℝ] (ℝ × K)) (B : K →ₗ[ℝ] K)
    (hfirst : ∀ c : ℝ, L (c,0) = (c,0))
    (hsecond : ∀ v : K, (L (0,v)).2 = B v) :
    L.charpoly = (Polynomial.X - 1) * B.charpoly ∧ LinearMap.det L = LinearMap.det B := by
  classical
  let b₁ := Module.Basis.singleton Unit ℝ
  let b₂ := Module.finBasis ℝ K
  let b := b₁.prod b₂
  let A := LinearMap.toMatrix b b L
  let C : Matrix Unit (Fin (Module.finrank ℝ K)) ℝ := A.submatrix Sum.inl Sum.inr
  have hA : A = Matrix.fromBlocks 1 C 0 (LinearMap.toMatrix b₂ b₂ B) := by
    ext (i | i) (j | j)
    · simp [A, b, LinearMap.toMatrix_apply, Module.Basis.prod_apply, hfirst,
        b₁]
    · rfl
    · simp [A, b, LinearMap.toMatrix_apply, Module.Basis.prod_apply, hfirst]
    · simpa [A, b, LinearMap.toMatrix_apply, Module.Basis.prod_apply] using
        congrArg (fun v => b₂.repr v i) (hsecond (b₂ j))
  constructor
  · rw [← LinearMap.charpoly_toMatrix L b, show LinearMap.toMatrix b b L = _ from hA, Matrix.charpoly_fromBlocks_zero₂₁,
      LinearMap.charpoly_toMatrix]
    simp [Matrix.charpoly_one]
  · rw [← LinearMap.det_toMatrix b L, show LinearMap.toMatrix b b L = _ from hA, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul, LinearMap.det_toMatrix]

/-- The derivative formula realizes M as precisely this block triangular operator. -/
lemma transverse_invariants (ℓ : E →L[ℝ] ℝ) (a : E) (ha : ℓ a ≠ 0)
    (M : E →L[ℝ] E) (hMa : M a = a) (B : ℓ.ker →L[ℝ] ℓ.ker)
    (hB : ∀ v : ℓ.ker, (B v : E) = M (v : E) - (ℓ (M (v : E)) / ℓ a) • a) :
    M.toLinearMap.charpoly = (Polynomial.X - 1) * B.toLinearMap.charpoly ∧
      LinearMap.det M.toLinearMap = LinearMap.det B.toLinearMap := by
  let e := sectionSplit ℓ a ha
  let L := e.conj M.toLinearMap
  have hf (c : ℝ) : L (c,0) = (c,0) := by
    rw [LinearEquiv.conj_apply_apply]
    change sectionSplit ℓ a ha (M (c • a + (0 : ℓ.ker))) = (c,0)
    simp [sectionSplit, hMa, ha, map_smul]
  have hs (v : ℓ.ker) : (L (0,v)).2 = B v := by
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    dsimp only [e, sectionSplit, LinearEquiv.coe_mk, LinearEquiv.coe_symm_mk]
    change (ReturnBranch.transverseProjection ℓ a ha (M (0 • a + (v : E))) : E) = _
    simpa only [zero_smul, zero_add, ReturnBranch.transverseProjection_apply] using (hB v).symm
  have h := triangular_invariants L B.toLinearMap hf hs
  refine ⟨?_, ?_⟩
  · simpa only [L, LinearEquiv.charpoly_conj] using h.1
  · simpa only [L, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj] using h.2

/-- Liouville on the actual variational solution, transported through a basis.
The integrand trace is exactly the divergence of the original field. -/
lemma variation_determinant (F : AutonomousODE E) (p : E) (T : ℝ)
    (hV : VariationConclusions F p T) :
    LinearMap.det (orbitVariation F p T).toLinearMap =
      Real.exp (∫ t in (0 : ℝ)..T, divergence F (flow F t p)) := by
  let n := Module.finrank ℝ E
  let b := Module.finBasis ℝ E
  let A := fun r => inBasis b (coefficient F p r)
  let Y := fun r => Ch07.EvolutionMatrix.U Ch08.Monodromy.wholeTime A r 0
  have hA : Continuous A := (coordinates b).continuous.comp hV.1
  have hYc : ContinuousOn Y Ch08.Monodromy.wholeTime.carrier :=
    Ch07.EvolutionMatrix.continuousOn_U _ A 0 (mem_univ 0) hA.continuousOn
  have hYd := Ch07.EvolutionMatrix.hasDerivWithinAt_U
    Ch08.Monodromy.wholeTime A 0 (mem_univ 0) hA.continuousOn
  have hdet := Ch07.Liouville.det_eq_exp_trace_integral Ch08.Monodromy.wholeTime
    A Y hA.continuousOn hYc hYd (mem_univ 0) (mem_univ T)
  have hY0 : Y 0 = 1 := Ch07.EvolutionMatrix.U_self _ A 0 (mem_univ 0) hA.continuousOn
  have hYT : inBasis b (orbitVariation F p T) = Y T := hV.2.2.2.2.1 n b T
  have htrace (t : ℝ) : (A t).trace = divergence F (flow F t p) :=
    (LinearMap.trace_eq_matrix_trace ℝ b (coefficient F p t).toLinearMap).symm
  rw [hY0, Matrix.det_one, one_mul, ← Real.exp_eq_exp_ℝ] at hdet
  simp_rw [htrace] at hdet
  rw [← LinearMap.det_toMatrix b]
  change (inBasis b (orbitVariation F p T)).det = _
  rw [hYT]
  exact hdet

/-- Every endomorphism of a real line is multiplication by its determinant. -/
lemma line_operator {K : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] (hK : Module.finrank ℝ K = 1) (B : K →ₗ[ℝ] K) :
    ∃ μ : ℝ, B = μ • LinearMap.id ∧ LinearMap.det B = μ ∧
      B.charpoly = Polynomial.X - Polynomial.C μ := by
  classical
  let b := Module.finBasisOfFinrankEq ℝ K hK
  let μ := LinearMap.toMatrix b b B 0 0
  have hB : B = μ • LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hi, hj, μ]
  refine ⟨μ, hB, ?_, ?_⟩
  · rw [hB, LinearMap.det_smul, hK]
    simp
  · rw [← LinearMap.charpoly_toMatrix B b]
    have hm : LinearMap.toMatrix b b B = Matrix.diagonal (fun _ => μ) := by
      rw [hB]
      simp [Matrix.smul_one_eq_diagonal]
    rw [hm, Matrix.charpoly_diagonal]
    simp

/-- Assemble the quotient isomorphism, exact characteristic polynomial,
Liouville identity and the positive single planar multiplier. -/
theorem multipliers : MultipliersExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T _hT hc hper _hleast _hnc ℓ ha d
  have hF1 : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain :=
    hF.of_le (by exact_mod_cast hk)
  have hV := variation_conclusions F hF1 p hp T hc hper
  refine ⟨hV, ?_⟩
  let a := autonomousEvalValue F p
  let M := orbitVariation F p T
  let B := fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0
  have hMa : M a = a := hV.2.2.2.2.2
  have hB : ∀ v : ℓ.ker, (B v : E) = M (v : E) - (ℓ (M (v : E)) / ℓ a) • a :=
    d.map_derivative
  have hinv := transverse_invariants ℓ a ha M hMa B hB
  have hdim := section_dimension ℓ a ha
  have hdet : LinearMap.det B.toLinearMap =
      Real.exp (∫ t in (0 : ℝ)..T, divergence F (flow F t p)) :=
    hinv.2.symm.trans (variation_determinant F p T hV)
  refine ⟨?_, hdim, hinv.1, hdet, ?_⟩
  · exact ⟨velocityLine_invariant a M.toLinearMap hMa,
      sectionQuotientEquiv ℓ a ha, sectionQuotientEquiv_apply ℓ a ha,
      quotient_conjugacy ℓ a ha M hMa B hB⟩
  · intro hplane
    have hline : Module.finrank ℝ ℓ.ker = 1 := by omega
    obtain ⟨μ, hμ, hdetμ, hpoly⟩ := line_operator hline B.toLinearMap
    refine ⟨μ, ?_, hμ, hpoly⟩
    rw [← hdetμ, hdet]
    exact Real.exp_pos _

/-- Construct the return map from the original orbit hypotheses, then apply
the theorem above. This also retains arbitrary section and time shrinkings. -/
theorem periodic_orbit_multipliers : PeriodicOrbitMultipliersExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T hT hc hper hleast hnc ℓ ha S₀ hS₀ h0 ε hε
  obtain ⟨d, hS, hδ⟩ := ReturnMap.return_map k hk F hF p hp T hT hc hper
    hleast hnc ℓ ha S₀ hS₀ h0 ε hε
  exact ⟨d, hS, hδ, multipliers k hk F hF p hp T hT hc hper hleast hnc ℓ ha d⟩

end D13Unified.Ch14.Multipliers
