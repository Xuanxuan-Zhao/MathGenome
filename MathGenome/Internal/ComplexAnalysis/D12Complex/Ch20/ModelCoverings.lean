import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.ModelCoverings
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.CoveringPaths
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
open Set Topology

namespace D12Complex.Ch20.ModelCoverings

/-- Recover the project's open-sheet predicate from a Mathlib covering.
The continuous inverse sections of a local homeomorphism are open embeddings. -/
theorem covering_of_isCoveringMap {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) (hp : IsCoveringMap p) : IsCovering p := by
  classical
  intro b
  obtain ⟨hd, U, hb, hU, hpU, H, hH⟩ := hp b
  let F := p ⁻¹' {b}
  let g (i : F) (y : U) : E := (H.symm (y, i) : E)
  have hcont (i : F) : Continuous (g i) := by dsimp [g]; fun_prop
  have hpg (i : F) (y : U) : p (g i y) = y := by
    simpa only [g, H.apply_symm_apply] using (hH (H.symm (y, i))).symm
  have hemb (i : F) : IsOpenEmbedding (g i) := by
    apply hp.isLocalHomeomorph.isOpenEmbedding_of_comp
    · have heq : p ∘ g i = (Subtype.val : U → B) := funext (hpg i)
      rw [heq]
      exact hU.isOpenEmbedding_subtypeVal
    · exact hcont i
  let V (i : F) : Set E := Set.range (g i)
  refine ⟨U, hb, hU, Set.range V, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (hemb i).isOpen_range
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
    have hyz : H.symm (z, j) = H.symm (y, i) := Subtype.ext hz
    have hji : j = i := congrArg Prod.snd (H.symm.injective hyz)
    exact hij (congrArg V hji.symm)
  · ext e
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, y, rfl⟩
      change p (g i y) ∈ U
      rw [hpg]
      exact y.property
    · intro he
      refine Set.mem_sUnion.mpr ⟨V (H ⟨e, he⟩).2, ⟨_, rfl⟩, ?_⟩
      exact ⟨(H ⟨e, he⟩).1, congrArg Subtype.val (H.symm_apply_apply ⟨e, he⟩)⟩
  · rintro _ ⟨i, rfl⟩
    let h : U ≃ₜ V i := (hemb i).toIsEmbedding.toHomeomorph
    refine ⟨h.symm, ?_⟩
    intro e
    have hh : g i (h.symm e) = e := congrArg Subtype.val (h.apply_symm_apply e)
    exact (hpg i (h.symm e)).symm.trans (congrArg p hh)

/-- The series exponential fixed upstream is the exponential used in these models. -/
theorem model_exp_eq_E : Complex.exp = D12Complex.E := Exponential.E_eq_exp.symm

theorem exponential_covering : Specs.D12Complex.Ch20.ModelCoverings.exponential_covering := by
  refine ⟨?_, covering_of_isCoveringMap _ Complex.isCoveringMap_exp, ?_⟩
  · intro z
    exact ⟨Complex.log z, Subtype.ext (Complex.exp_log z.property)⟩
  · exact ⟨isOpen_univ, fun z _ => Complex.differentiableAt_exp⟩

/-- A logarithm on an actual positive-radius disk, with its derivative. -/
theorem logarithm_disk (b : ℂ) (hb : b ≠ 0) :
    ∃ (r : ℝ) (L : ℂ → ℂ), 0 < r ∧
      (∀ z ∈ Metric.ball b r, z ≠ 0) ∧ HolomorphicOn (Metric.ball b r) L ∧
      (∀ z ∈ Metric.ball b r, Complex.exp (L z) = z) ∧
      ∀ z ∈ Metric.ball b r, HasDerivAt L (1 / z) z := by
  have hc : D12Complex.E (Complex.log b) = b := by
    rw [Exponential.E_eq_exp, Complex.exp_log hb]
  obtain ⟨U, L, hbU, _, hL, _, he, hd⟩ := LocalLogarithmsRoots.local_logarithm
    Set.univ (fun z : ℂ => z) b (Complex.log b)
    ⟨isOpen_univ, fun _ _ => differentiableAt_id⟩ (Set.mem_univ _) hb hc
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hL.1 b hbU
  refine ⟨r, L, hr, ?_, ⟨Metric.isOpen_ball, fun z hz => hL.2 z (hsub hz)⟩, ?_, ?_⟩
  · intro z hz
    rw [← he z (hsub hz)]
    exact Exponential.E_ne_zero _
  · intro z hz
    rw [model_exp_eq_E]
    exact he z (hsub hz)
  · intro z hz
    simpa only [deriv_id''] using hd z (hsub hz)

/-- Noncritical holomorphic maps send open sets to open sets, directly from
 the already proved local inverse theorem. -/
theorem image_open_of_noncritical (U : Set ℂ) (g : ℂ → ℂ)
    (hg : HolomorphicOn U g) (hne : ∀ z ∈ U, deriv g z ≠ 0) : IsOpen (g '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨S, T, q, hzS, hgzT, hSU, hpair, _, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse U g z hg hz (hne z hz)
  apply Filter.mem_of_superset (hpair.2.1.1.mem_nhds hgzT)
  intro w hw
  exact ⟨q w, hSU (hpair.2.2.2.1 hw), hpair.2.2.2.2.2 hw⟩

/-- A noncritical holomorphic right inverse parametrizes one open inverse sheet. -/
theorem inverse_sheet (f g : ℂ → ℂ) (U : Set ℂ)
    (hf : HolomorphicOn Set.univ f) (hg : HolomorphicOn U g)
    (hne : ∀ z ∈ U, deriv g z ≠ 0) (hr : ∀ z ∈ U, f (g z) = z) :
    BiholomorphicPair (g '' U) U f g := by
  refine ⟨⟨image_open_of_noncritical U g hg hne, fun z _ => hf.2 z trivial⟩,
    hg, ?_, ?_, ?_, hr⟩
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [hr z hz] using hz
  · intro z hz
    exact ⟨z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hr z hz]

private theorem period_ne_zero : period ≠ 0 := by
  simp [period, Real.pi_ne_zero, Complex.I_ne_zero]

private theorem exp_period_shift (z : ℂ) (k : ℤ) :
    Complex.exp (z + k * period) = Complex.exp z := by
  exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩

theorem exponential_sheets : Specs.D12Complex.Ch20.ModelCoverings.exponential_sheets := by
  intro b hb
  obtain ⟨r, L, hr, hn, hL, he, hd⟩ := logarithm_disk b hb
  have hshift (k : ℤ) (z : ℂ) (hz : z ∈ Metric.ball b r) :
      Complex.exp (expBranch L k z) = z := (exp_period_shift _ k).trans (he z hz)
  refine ⟨r, L, hr, hn, hL, he, ?_, ?_, ?_⟩
  · intro j k hjk
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hwz : w = z := (hshift k w hw).symm.trans
      ((congrArg Complex.exp hzw).trans (hshift j z hz))
    subst w
    have hkj : (k : ℂ) = (j : ℂ) :=
      mul_right_cancel₀ period_ne_zero (add_left_cancel hzw)
    exact hjk (Int.cast_injective hkj).symm
  · ext z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨k, w, hw, rfl⟩
      simpa only [hshift k w hw] using hw
    · intro hz
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he (Complex.exp z) hz).symm
      exact ⟨k, Complex.exp z, hz, hk.symm⟩
  · intro k
    apply inverse_sheet Complex.exp (expBranch L k) (Metric.ball b r)
      ⟨isOpen_univ, fun _ _ => Complex.differentiableAt_exp⟩
      ⟨Metric.isOpen_ball, fun z hz => ((hd z hz).add_const _).differentiableAt⟩
    · intro z hz
      rw [show deriv (expBranch L k) z = 1 / z from ((hd z hz).add_const _).deriv]
      exact one_div_ne_zero (hn z hz)
    · exact hshift k

private theorem powerBranch_factor (L : ℂ → ℂ) (n : ℕ) (k : Fin n) (z : ℂ) :
    powerBranch L n k z = Complex.exp (L z / n) * Complex.exp (period / n) ^ k.val := by
  unfold powerBranch
  rw [show (L z + (k.val : ℂ) * period) / n =
    L z / n + (k.val : ℂ) * (period / n) by ring,
    Complex.exp_add, Complex.exp_nat_mul]

private theorem root_pow (w : ℂ) (n : ℕ) (hn : 0 < n) :
    Complex.exp (w / n) ^ n = Complex.exp w := by
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

private theorem powerBranch_pow (L : ℂ → ℂ) (n : ℕ) (hn : 0 < n)
    (k : Fin n) (z : ℂ) : (powerBranch L n k z) ^ n = Complex.exp (L z) := by
  unfold powerBranch
  rw [root_pow _ n hn]
  exact exp_period_shift (L z) (k.val : ℤ)

private theorem powerBranch_injective (L : ℂ → ℂ) (n : ℕ) (hn : 0 < n) (z : ℂ) :
    Function.Injective (fun k : Fin n => powerBranch L n k z) := by
  intro j k h
  dsimp only at h
  rw [powerBranch_factor, powerBranch_factor] at h
  apply Fin.ext
  exact (Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)).pow_inj j.isLt k.isLt
    (mul_left_cancel₀ (Complex.exp_ne_zero _) h)

private theorem powerBranch_exhausts (L : ℂ → ℂ) (n : ℕ) (hn : 0 < n)
    (w z : ℂ) (h : z ^ n = Complex.exp (L w)) :
    ∃ k : Fin n, powerBranch L n k w = z := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let ξ := Complex.exp (L w / n)
  have hξ : ξ ^ n = Complex.exp (L w) := root_pow _ _ hn
  have hquot : (z / ξ) ^ n = 1 := by
    rw [div_pow, h, hξ, div_self (Complex.exp_ne_zero _)]
  obtain ⟨k, hk, heq⟩ := (Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)).eq_pow_of_pow_eq_one hquot
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [powerBranch_factor]
  change ξ * Complex.exp (period / n) ^ k = z
  unfold period
  rw [heq]
  exact mul_div_cancel₀ z (Complex.exp_ne_zero _)

theorem power_covering : Specs.D12Complex.Ch20.ModelCoverings.power_covering := by
  intro n hn
  refine ⟨?_, covering_of_isCoveringMap _
    (isCoveringMap_npow n (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))), ?_⟩
  · intro z
    refine ⟨⟨Complex.exp (Complex.log z / n), Complex.exp_ne_zero _⟩, ?_⟩
    apply Subtype.ext
    exact (root_pow _ _ hn).trans (Complex.exp_log z.property)
  · exact ⟨isClosed_singleton.isOpen_compl, fun z _ => (hasDerivAt_pow n z).differentiableAt⟩

theorem power_fiber_card : Specs.D12Complex.Ch20.ModelCoverings.power_fiber_card := by
  intro n hn b
  let L : ℂ → ℂ := fun _ => Complex.log b
  let f : Fin n → {z : PuncturedPlane // powerProjection n z = b} := fun k =>
    ⟨⟨powerBranch L n k b, Complex.exp_ne_zero _⟩,
      Subtype.ext ((powerBranch_pow L n hn k b).trans (Complex.exp_log b.property))⟩
  have hinj : Function.Injective f := by
    intro j k h
    exact powerBranch_injective L n hn b (congrArg (fun z => (z.val : ℂ)) h)
  have hsurj : Function.Surjective f := by
    intro z
    have hz : (z.val : ℂ) ^ n = Complex.exp (L b) := by
      change (z.val : ℂ) ^ n = Complex.exp (Complex.log b)
      rw [Complex.exp_log b.property]
      exact congrArg Subtype.val z.property
    obtain ⟨k, hk⟩ := powerBranch_exhausts L n hn b z.val hz
    refine ⟨k, ?_⟩
    exact Subtype.ext (Subtype.ext hk)
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm.trans (Nat.card_fin n)

theorem power_sheets : Specs.D12Complex.Ch20.ModelCoverings.power_sheets := by
  intro b n hb hn
  obtain ⟨r, L, hr, hnz, hL, he, hd⟩ := logarithm_disk b hb
  have hp (k : Fin n) (z : ℂ) (hz : z ∈ Metric.ball b r) :
      (powerBranch L n k z) ^ n = z := (powerBranch_pow L n hn k z).trans (he z hz)
  have hder (k : Fin n) (z : ℂ) (hz : z ∈ Metric.ball b r) :
      HasDerivAt (powerBranch L n k)
        (Complex.exp ((L z + (k.val : ℂ) * period) / n) * ((1 / z) / n)) z :=
    (Complex.hasDerivAt_exp _).comp z (((hd z hz).add_const _).div_const _)
  refine ⟨r, L, hr, hnz, hL, he, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨powerBranch L n k b, b, Metric.mem_ball_self hr, rfl⟩
  · intro j k hjk
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hwz : w = z := (hp k w hw).symm.trans
      ((congrArg (fun q : ℂ => q ^ n) hzw).trans (hp j z hz))
    subst w
    exact hjk ((powerBranch_injective L n hn z hzw).symm)
  · ext z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨k, w, hw, rfl⟩
      simpa only [hp k w hw] using hw
    · intro hz
      obtain ⟨k, hk⟩ := powerBranch_exhausts L n hn (z ^ n) z (he (z ^ n) hz).symm
      exact ⟨k, z ^ n, hz, hk⟩
  · intro k
    apply inverse_sheet (fun z => z ^ n) (powerBranch L n k) (Metric.ball b r)
      ⟨isOpen_univ, fun z _ => (hasDerivAt_pow n z).differentiableAt⟩
      ⟨Metric.isOpen_ball, fun z hz => (hder k z hz).differentiableAt⟩
    · intro z hz
      rw [(hder k z hz).deriv]
      exact mul_ne_zero (Complex.exp_ne_zero _) (div_ne_zero (one_div_ne_zero (hnz z hz))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))
    · exact hp k

theorem restricted_exponential_local :
    Specs.D12Complex.Ch20.ModelCoverings.restricted_exponential_local := by
  have hhol : HolomorphicOn {z : ℂ | z ≠ 0} Complex.exp :=
    ⟨isClosed_singleton.isOpen_compl, fun _ _ => Complex.differentiableAt_exp⟩
  refine ⟨?_, hhol, ?_⟩
  · intro b
    obtain ⟨c, hc⟩ := exponential_covering.1 b
    by_cases hcz : c = 0
    · refine ⟨⟨period, period_ne_zero⟩, ?_⟩
      apply Subtype.ext
      have hc' := congrArg Subtype.val hc
      change Complex.exp c = (b : ℂ) at hc'
      rw [hcz] at hc'
      change Complex.exp period = (b : ℂ)
      rw [← hc']
      simpa using exp_period_shift 0 1
    · exact ⟨⟨c, hcz⟩, hc⟩
  · intro a ha
    obtain ⟨U, V, L, haU, heaV, hU, hp, _, _⟩ :=
      LocalHolomorphicInverse.local_holomorphic_inverse {z : ℂ | z ≠ 0} Complex.exp a
        hhol ha (by rw [Complex.deriv_exp]; exact Complex.exp_ne_zero a)
    refine ⟨U, V, L, haU, heaV, hU, ?_, hp⟩
    intro z hz
    rw [← hp.2.2.2.2.2 hz]
    exact Complex.exp_ne_zero _

private theorem continuous_intervalParameter (ε : ℝ) : Continuous (intervalParameter ε) := by
  unfold intervalParameter
  fun_prop

theorem restricted_exponential_no_lift :
    Specs.D12Complex.Ch20.ModelCoverings.restricted_exponential_no_lift := by
  intro ε _
  have hc : Continuous (terminalPath ε) := by
    unfold terminalPath expProjection
    exact (Complex.continuous_exp.comp (continuous_intervalParameter ε)).subtype_mk _
  refine ⟨hc, ?_⟩
  rintro ⟨Γ, hΓ, hΓ0, hproj⟩
  have hfull : (fun s => (Γ s : ℂ)) = intervalParameter ε := by
    apply Complex.isCoveringMap_exp.eq_of_comp_eq
      (continuous_subtype_val.comp hΓ) (continuous_intervalParameter ε) _ (0 : unitInterval)
    · simpa [intervalParameter] using hΓ0
    · exact hproj
  have hz : (Γ 1 : ℂ) = 0 := by
    simpa [intervalParameter] using congrFun hfull 1
  exact (Γ 1).property hz

theorem restricted_exponential_not_covering :
    Specs.D12Complex.Ch20.ModelCoverings.restricted_exponential_not_covering := by
  intro hcov
  let a : PuncturedPlane := ⟨(-1 : ℂ), neg_ne_zero.mpr one_ne_zero⟩
  have ha : restrictedExp a = terminalPath 1 0 := by
    apply Subtype.ext
    simp [restrictedExp, terminalPath, expProjection, intervalParameter, a]
  obtain ⟨Γ, hΓ, _⟩ := CoveringPaths.path_lifting restrictedExp hcov (terminalPath 1)
    (restricted_exponential_no_lift 1 zero_lt_one).1 a ha
  apply (restricted_exponential_no_lift 1 zero_lt_one).2
  exact ⟨Γ, hΓ.1, congrArg Subtype.val hΓ.2.1, hΓ.2.2⟩

end D12Complex.Ch20.ModelCoverings
