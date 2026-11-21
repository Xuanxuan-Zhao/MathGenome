import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletMinMax
import MathGenome.Internal.LinearPDE.P201.Elliptic.DirichletEigenbasis
import Mathlib.Topology.Order.Compact

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace P201.DirichletMinMax
open P201Specs.Dirichlet P201Specs.DirichletEigenbasis P201Specs.DirichletMinMax

/-- Parseval with the coefficient orientation used by the spectral form data. -/
theorem hasSum_sq_coefficients {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e : HilbertBasis ℕ ℝ H) (u : H) :
    HasSum (fun i => (inner ℝ (e i) u) ^ 2) (‖u‖ ^ 2) := by
  simpa only [real_inner_comm u, ← pow_two, real_inner_self_eq_norm_sq] using
    e.hasSum_inner_mul_inner u u

/-- On the span of the first k+1 lifted eigenvectors, all later coefficients vanish. -/
theorem coefficient_eq_zero_of_mem_firstSpace {V H : Type*}
    [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →ₗ[ℝ] H) (e : HilbertBasis ℕ ℝ H) (v : ℕ → V)
    (hv : ∀ i, J (v i) = e i) (k : ℕ) (u : V) (hu : u ∈ firstSpace v k)
    (i : ℕ) (hi : k < i) : inner ℝ (e i) (J u) = 0 := by
  let f : V →ₗ[ℝ] ℝ := (innerSL ℝ (e i)).toLinearMap.comp J
  have hsub : firstSpace v k ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change inner ℝ (e i) (J (v j)) = 0
    rw [hv]
    exact e.orthonormal.inner_eq_zero (by omega)
  exact hsub hu

/-- k homogeneous linear coefficient constraints cannot be injective on a
(k+1)-dimensional space. This includes k=0. -/
theorem exists_orthogonal_vector {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →ₗ[ℝ] H) (e : HilbertBasis ℕ ℝ H) (k : ℕ)
    (W : Submodule ℝ V) (hdim : Module.finrank ℝ W = k + 1) :
    ∃ u ∈ W, u ≠ 0 ∧ ∀ i < k, inner ℝ (e i) (J u) = 0 := by
  let f : W →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi (fun i => ((innerSL ℝ (e i)).toLinearMap.comp J).comp W.subtype)
  have hn : ¬Function.Injective f := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hdim, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    omega
  have hker : f.ker ≠ ⊥ := fun h => hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨u, hu, hnzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨u, u.property, fun hz => hnzero (Subtype.ext hz), ?_⟩
  intro i hi
  exact congrFun hu ⟨i, hi⟩
/-- The initial lifted family has exactly the asserted dimension. -/
theorem finrank_firstSpace {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →ₗ[ℝ] H) (e : HilbertBasis ℕ ℝ H) (v : ℕ → V)
    (hv : ∀ i, J (v i) = e i) (k : ℕ) :
    Module.finrank ℝ (firstSpace v k) = k + 1 := by
  have hli : LinearIndependent ℝ (fun i : Fin (k + 1) => v i) := by
    apply LinearIndependent.of_comp J
    simpa only [Function.comp_def, hv] using
      e.orthonormal.linearIndependent.comp (fun i : Fin (k + 1) => (i : ℕ)) Fin.val_injective
  simpa only [firstSpace, Fintype.card_fin] using finrank_span_eq_card hli

/-- Comparison of the spectral energy sum with Parseval. -/
theorem spectral_upper_bound {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →ₗ[ℝ] H) (e : HilbertBasis ℕ ℝ H) (v : ℕ → V)
    (hv : ∀ i, J (v i) = e i) (ev : ℕ → ℝ) (hm : Monotone ev)
    (q : V → ℝ) (hq : ∀ u, HasSum (fun i => ev i * (inner ℝ (e i) (J u)) ^ 2) (q u))
    (k : ℕ) (u : V) (hu : u ∈ firstSpace v k) : q u ≤ ev k * ‖J u‖ ^ 2 := by
  apply hasSum_le (g := fun i => ev k * (inner ℝ (e i) (J u)) ^ 2) _ (hq u)
    ((hasSum_sq_coefficients e (J u)).mul_left (ev k))
  intro i
  by_cases hi : i ≤ k
  · exact mul_le_mul_of_nonneg_right (hm hi) (sq_nonneg _)
  · rw [coefficient_eq_zero_of_mem_firstSpace J e v hv k u hu i (by omega)]
    simp

/-- The spectral sum gives the opposite bound on the orthogonal complement
of the first k eigenvectors. -/
theorem spectral_lower_bound {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →ₗ[ℝ] H) (e : HilbertBasis ℕ ℝ H) (ev : ℕ → ℝ) (hm : Monotone ev)
    (q : V → ℝ) (hq : ∀ u, HasSum (fun i => ev i * (inner ℝ (e i) (J u)) ^ 2) (q u))
    (k : ℕ) (u : V) (hu : ∀ i < k, inner ℝ (e i) (J u) = 0) :
    ev k * ‖J u‖ ^ 2 ≤ q u := by
  apply hasSum_le (f := fun i => ev k * (inner ℝ (e i) (J u)) ^ 2) _
    ((hasSum_sq_coefficients e (J u)).mul_left (ev k)) (hq u)
  intro i
  by_cases hi : k ≤ i
  · exact mul_le_mul_of_nonneg_right (hm hi) (sq_nonneg _)
  · rw [hu i (by omega)]
    simp

/-- Homogeneity allows maximization on any unit sphere in a finite dimensional
subspace, while retaining the L² denominator. -/
theorem quotient_smul {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (u : V) (c : ℝ) (hc : c ≠ 0) :
    B (c • u) (c • u) / ‖J (c • u)‖ ^ 2 = B u u / ‖J u‖ ^ 2 := by
  simp only [map_smul, smul_apply, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_assoc, ← pow_two, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- Every nontrivial finite dimensional subspace has an attained Rayleigh
maximum. No compactness in the infinite dimensional form domain is asserted. -/
theorem finite_rayleigh_maximum {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (W : Submodule ℝ V) [FiniteDimensional ℝ W] [Nontrivial W] :
    ∃ u ∈ W, u ≠ 0 ∧ ∀ z ∈ W, z ≠ 0 → B z z / ‖J z‖ ^ 2 ≤ B u u / ‖J u‖ ^ 2 := by
  let R : W → ℝ := fun u => B u.val u.val / ‖J u.val‖ ^ 2
  have hnonzero (u : W) (hu : u ∈ Metric.sphere (0 : W) 1) : (u : V) ≠ 0 := by
    intro hz
    have he : u = 0 := Subtype.ext hz
    simp [he] at hu
  have hcont : ContinuousOn R (Metric.sphere (0 : W) 1) := by
    apply ContinuousOn.div
      (((B.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val).continuousOn)
      (((J.continuous.comp continuous_subtype_val).norm.pow 2).continuousOn)
    intro u hu
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (fun hz =>
      hnonzero u hu (hJ (hz.trans (map_zero J).symm))))
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : W) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num)) hcont
  refine ⟨u, u.property, hnonzero u hu, ?_⟩
  intro z hz hnz
  let w : W := ⟨z, hz⟩
  have hnw : w ≠ 0 := fun h => hnz (congrArg Subtype.val h)
  have hn : (‖w‖⁻¹ • w) ∈ Metric.sphere (0 : W) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hnw
  have hle := hmax hn
  change B ((‖w‖⁻¹ : ℝ) • z) ((‖w‖⁻¹ : ℝ) • z) /
    ‖J ((‖w‖⁻¹ : ℝ) • z)‖ ^ 2 ≤ _ at hle
  rwa [quotient_smul B J z _ (inv_ne_zero (norm_ne_zero_iff.mpr hnw))] at hle
/-- The attained variational formula for any full resolution of the concrete
coefficient form. The final theorem constructs this resolution. -/
theorem minmax_of_resolution {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω))
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2))
    (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω)
    (hd : OperatorData Ω a e ev v) (hf : FormData Ω A e ev v) :
    MinMaxData Ω A ev v := by
  let J : H10 ℝ Ω →L[ℝ] Lp ℝ Ω 2 := hZeroUnderlying Ω
  let q : H10 ℝ Ω → ℝ := fun u => ellipticEnergyForm Ω A u.val u.val
  have hJ : Function.Injective J := DirichletResolvent.inclusion_injective Ω
  have hv (i : ℕ) : J (v i) = e i := (hd.2.2.2.1 i).1
  have hs (u : H10 ℝ Ω) :
      HasSum (fun i => ev i * (inner ℝ (e i) (J u)) ^ 2) (q u) := hf.2.1 u
  have hden (u : H10 ℝ Ω) (hu : u ≠ 0) : 0 < ‖J u‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (fun hz => hu (hJ (hz.trans (map_zero J).symm)))
  have hqev (j : ℕ) : q (v j) = ev j := by
    apply (hs (v j)).unique
    convert hasSum_ite_eq j (ev j) using 1
    funext i
    rw [hv]
    by_cases hij : i = j
    · subst i
      simp [e.orthonormal.norm_eq_one]
    · simp [hij, e.orthonormal.inner_eq_zero hij]
  have hvev (j : ℕ) : rayleigh Ω A (v j) = ev j := by
    change q (v j) / ‖J (v j)‖ ^ 2 = ev j
    rw [hqev, hv, e.orthonormal.norm_eq_one]
    simp
  intro k
  refine ⟨finrank_firstSpace J.toLinearMap e v hv k, ?_, ?_⟩
  · constructor
    · refine ⟨v k, Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩, ?_, hvev k⟩
      intro hz
      exact e.orthonormal.ne_zero k (by rw [← hv k, hz, map_zero])
    · intro u hu hne
      apply (div_le_iff₀ (hden u hne)).mpr
      exact spectral_upper_bound J.toLinearMap e v hv ev hd.2.1 q hs k u hu
  · intro W hdim
    have hdimpos : 0 < Module.finrank ℝ W := by omega
    letI : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos hdimpos
    letI : Nontrivial W := Module.finrank_pos_iff.mp hdimpos
    let B : H10 ℝ Ω →L[ℝ] H10 ℝ Ω →L[ℝ] ℝ :=
      (Dirichlet.form Ω A hA).bilinearComp (zeroInclusion Ω) (zeroInclusion Ω)
    have hB (u w : H10 ℝ Ω) : B u w = ellipticEnergyForm Ω A u.val w.val :=
      Dirichlet.form_apply Ω A hA u.val w.val
    obtain ⟨u, hu, hune, hmax⟩ := finite_rayleigh_maximum B J hJ W
    refine ⟨rayleigh Ω A u, ⟨⟨u, hu, hune, rfl⟩, ?_⟩, ?_⟩
    · intro z hz hzne
      simpa only [hB, rayleigh, J] using hmax z hz hzne
    · obtain ⟨z, hz, hzne, horth⟩ := exists_orthogonal_vector J.toLinearMap e k W hdim
      have hlo : ev k ≤ rayleigh Ω A z := by
        apply (le_div_iff₀ (hden z hzne)).mpr
        exact spectral_lower_bound J.toLinearMap e ev hd.2.1 q hs k z horth
      exact hlo.trans (by simpa only [hB, rayleigh, J] using hmax z hz hzne)

/-- The extremal inequalities and attainment imply the literal infimum
formula; thus the representation of min–max has no empty-set convention. -/
theorem infimum_formula_of_minmax {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω) (h : MinMaxData Ω A ev v) :
    InfimumFormula Ω A ev := by
  intro k
  obtain ⟨hdim, hfirst, hall⟩ := h k
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨firstSpace v k, hdim, hfirst⟩, ?_⟩
  rintro r ⟨W, hW, hr⟩
  obtain ⟨r', ⟨⟨u, hu, hne, heq⟩, _⟩, hlo⟩ := hall W hW
  have hle := hr.2 u hu hne
  rw [heq] at hle
  exact hlo.trans hle

/-- The entire theorem `pde:elliptic-dirichlet-spectrum`, including its
compact positive self-adjoint inverse, multiplicities, and attained min–max. -/
theorem dirichlet_spectrum_minmax : P201Specs.DirichletMinMax.Statement := by
  intro m Ω hΩ hne A hA lam hlam hEll hsym
  obtain ⟨a, T, hadom, haform, _hgraph, _, _, _, _, _, hright, hleft,
    _, hcompact, hself, hpos, hinj, hdense⟩ :=
    DirichletResolvent.realization m Ω hΩ hne A hA lam hlam hEll hsym
  have ha : IsCoefficientForm Ω A a := ⟨hadom, haform⟩
  obtain ⟨e, ev, v, hd, hf⟩ :=
    DirichletEigenbasis.dirichlet_eigenbasis m Ω hΩ hne A hA lam hlam hEll hsym a ha
  have hmm := minmax_of_resolution Ω A hA a e ev v hd hf
  refine ⟨a, T, e, ev, v, ha, ?_, hd, hf, hmm,
    infimum_formula_of_minmax Ω A ev v hmm⟩
  refine ⟨?_, hcompact, hself, hpos, hinj, hdense⟩
  intro u f
  constructor
  · intro huf
    have hu : u ∈ a.associatedOperator.domain := LinearPMap.mem_domain_iff.mpr ⟨f, huf⟩
    have he := a.associatedOperator.mem_graph ⟨u, hu⟩
    have hval : a.associatedOperator ⟨u, hu⟩ = f :=
      a.associatedOperator.mem_graph_snd_inj he huf rfl
    simpa only [hval] using hleft ⟨u, hu⟩
  · intro hu
    simpa only [hu] using hright f

end P201.DirichletMinMax
