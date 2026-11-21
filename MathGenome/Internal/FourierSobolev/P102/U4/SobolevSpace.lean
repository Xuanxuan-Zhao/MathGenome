import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions ENNReal
namespace P102.U4

abbrev sobolevSpace : SobolevExpected.SpaceType := @Sobolev
abbrev weakDerivative : SobolevExpected.DerivativeType := @sobolevDerivative
abbrev underlyingLp : SobolevExpected.UnderlyingType := @sobolevUnderlying

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The bundled pairing is the source's bilinear integral on Ω. -/
theorem lpTestPairing_eq_integral (φ : TestSpace 𝕜 Ω) (u : DomainLp 𝕜 Ω p) :
    lpTestPairing Ω p φ u = ∫ x in Ω, u x * φ x := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing _ p (ENNReal.conjExponent p) u _ = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  have hφ : MemLp φ (ENNReal.conjExponent p) (volume.restrict (Ω : Set (Space d))) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  filter_upwards [hφ.coeFn_toLp] with x hx
  exact congrArg (fun z : 𝕜 => u x * z) hx

/-- Every Lp representative in the required exponent range is locally integrable on Ω. -/
theorem domainLp_locallyIntegrable (u : DomainLp 𝕜 Ω p) :
    LocallyIntegrableOn (⇑u) Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp u).locallyIntegrable (Fact.out : 1 ≤ p))

theorem regularLp_pairing (u : DomainLp 𝕜 Ω p) (φ : TestSpace 𝕜 Ω) :
    regularDistribution Ω u φ = lpTestPairing Ω p φ u := by
  rw [lpTestPairing_eq_integral, regular_pairing d 𝕜 Ω u (domainLp_locallyIntegrable Ω p u)]

/-- Uniqueness uses the established injection of regular distributions, on the restricted measure. -/
theorem regularLp_injective : Function.Injective
    (fun u : DomainLp 𝕜 Ω p => regularDistribution Ω u) := by
  intro u v h
  apply Lp.ext
  exact (regular_injectivity d 𝕜 Ω u v (domainLp_locallyIntegrable Ω p u)
    (domainLp_locallyIntegrable Ω p v)).mp h

/-- Equivalence between the distribution equation and all its test integral equations. -/
theorem distributionPartial_eq_regularLp_iff (α : MultiIndex d)
    (u v : DomainLp 𝕜 Ω p) :
    distributionPartial α (regularDistribution Ω u) = regularDistribution Ω v ↔
      ∀ φ : TestSpace 𝕜 Ω, lpTestPairing Ω p φ v =
        (-1 : 𝕜) ^ α.card *
          lpTestPairing Ω p (testPartialWord Ω (α.sort (· ≤ ·)) φ) u := by
  constructor
  · intro h φ
    have he := congrArg (fun T : DistributionSpace 𝕜 Ω => T φ) h
    simpa only [distributionPartial, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, regularLp_pairing Ω p] using he.symm
  · intro h
    ext φ
    simpa only [distributionPartial, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, regularLp_pairing Ω p] using (h φ).symm

/-- Membership is exactly the family of weak-derivative equations. -/
theorem mem_sobolevSubmodule_iff (v : SobolevTuple 𝕜 Ω m p) :
    v ∈ sobolevSubmodule 𝕜 Ω m p ↔
      ∀ (α : SobolevIndex d m) (φ : TestSpace 𝕜 Ω),
        lpTestPairing Ω p φ (v α) = (-1 : 𝕜) ^ α.val.card *
          lpTestPairing Ω p (testPartialWord Ω (α.val.sort (· ≤ ·)) φ)
            (v (zeroSobolevIndex d m)) := by
  simp only [sobolevSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    sobolevEquation, ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, smul_apply, smul_eq_mul, sub_eq_zero]

/-- An arbitrary intersection of kernels of continuous maps is closed. -/
theorem sobolevSubmodule_isClosed :
    IsClosed (sobolevSubmodule 𝕜 Ω m p : Set (SobolevTuple 𝕜 Ω m p)) := by
  simp only [sobolevSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun α => isClosed_iInter fun φ =>
    (sobolevEquation Ω m p α φ).isClosed_ker

/-- The exact source norm, with the zero-order term included. -/
theorem sobolev_norm (u : Sobolev 𝕜 Ω m p) :
    ‖u‖ = ∑ α : SobolevIndex d m, ‖sobolevDerivative u α‖ :=
  PiLp.norm_eq_of_L1 u.val

/-- Banachness holds for all p≥1 including infinity, and all d,m,Ω. -/
instance sobolevCompleteSpace : CompleteSpace (Sobolev 𝕜 Ω m p) :=
  (sobolevSubmodule_isClosed Ω m p).completeSpace_coe

theorem sobolev_complete : CompleteSpace (Sobolev 𝕜 Ω m p) := inferInstance

/-- The retained tuple entries really are distribution derivative representatives. -/
theorem sobolev_derivative_distribution (u : Sobolev 𝕜 Ω m p) (α : SobolevIndex d m) :
    distributionPartial α.val (regularDistribution Ω (sobolevUnderlying u)) =
      regularDistribution Ω (sobolevDerivative u α) := by
  apply (distributionPartial_eq_regularLp_iff Ω p _ _ _).mpr
  exact (mem_sobolevSubmodule_iff Ω m p u.val).mp u.property α

/-- The zeroth derivative is the underlying Lp class. -/
theorem sobolev_derivative_zero (u : Sobolev 𝕜 Ω m p) :
    sobolevDerivative u (zeroSobolevIndex d m) = sobolevUnderlying u := rfl

/-- Equality as functions is determined by the zero-order class. -/
theorem sobolevUnderlying_injective :
    Function.Injective (@sobolevUnderlying d 𝕜 _ Ω m p _) := by
  intro u v h
  apply Subtype.ext
  apply PiLp.ext
  intro α
  change sobolevDerivative u α = sobolevDerivative v α
  apply regularLp_injective Ω p
  change regularDistribution Ω (sobolevDerivative u α) =
    regularDistribution Ω (sobolevDerivative v α)
  rw [← sobolev_derivative_distribution Ω m p u α,
    ← sobolev_derivative_distribution Ω m p v α, h]

/-- There is at most one Lp representative of any specified distribution derivative. -/
theorem sobolev_derivative_unique (u : Sobolev 𝕜 Ω m p) (α : SobolevIndex d m)
    (v : DomainLp 𝕜 Ω p)
    (hv : distributionPartial α.val (regularDistribution Ω (sobolevUnderlying u)) =
      regularDistribution Ω v) : v = sobolevDerivative u α := by
  apply regularLp_injective Ω p
  change regularDistribution Ω v = regularDistribution Ω (sobolevDerivative u α)
  rw [← hv, sobolev_derivative_distribution Ω m p]

/-- Precisely the Lp classes in the source definition occur as zeroth coordinates. -/
theorem sobolev_range :
    Set.range (@sobolevUnderlying d 𝕜 _ Ω m p _) =
      {u | HasSobolevDerivatives Ω m p u} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩ α hα
    exact ⟨sobolevDerivative v ⟨α, hα⟩, sobolev_derivative_distribution Ω m p v ⟨α, hα⟩⟩
  · intro h
    let v : SobolevIndex d m → DomainLp 𝕜 Ω p :=
      fun α => (h α.val α.property).choose
    have hv (α : SobolevIndex d m) :
        distributionPartial α.val (regularDistribution Ω u) = regularDistribution Ω (v α) :=
      (h α.val α.property).choose_spec
    have hv0 : v (zeroSobolevIndex d m) = u := by
      apply regularLp_injective Ω p
      change regularDistribution Ω (v (zeroSobolevIndex d m)) = regularDistribution Ω u
      rw [← hv (zeroSobolevIndex d m)]
      exact derivative_zero d 𝕜 Ω _
    have hmem : WithLp.toLp 1 v ∈ sobolevSubmodule 𝕜 Ω m p := by
      apply (mem_sobolevSubmodule_iff Ω m p _).mpr
      intro α φ
      change lpTestPairing Ω p φ (v α) = _ * lpTestPairing Ω p _ (v _)
      rw [hv0]
      exact (distributionPartial_eq_regularLp_iff Ω p α.val u (v α)).mp (hv α) φ
    exact ⟨⟨WithLp.toLp 1 v, hmem⟩, hv0⟩

/-- Integral form of the closed equations, using the actual coordinate partials of tests. -/
theorem sobolev_tuple_image :
    Set.range (fun u : Sobolev 𝕜 Ω m p => u.val) =
      {v : SobolevTuple 𝕜 Ω m p | ∀ (α : SobolevIndex d m) (φ : TestSpace 𝕜 Ω),
        (∫ x in Ω, v α x * φ x) = (-1 : 𝕜) ^ α.val.card *
          ∫ x in Ω, v (zeroSobolevIndex d m) x * multiPartial φ α.val x} := by
  ext v
  rw [Subtype.range_coe_subtype]
  change v ∈ sobolevSubmodule 𝕜 Ω m p ↔ _
  rw [mem_sobolevSubmodule_iff Ω m p]
  simp_rw [lpTestPairing_eq_integral Ω p]
  simp only [testPartialWord_coe, multiPartial, Set.mem_ofPred_eq]

theorem sobolev_tuple_image_closed :
    IsClosed (Set.range (fun u : Sobolev 𝕜 Ω m p => u.val)) := by
  have hr : Set.range (fun u : Sobolev 𝕜 Ω m p => u.val) =
      (sobolevSubmodule 𝕜 Ω m p : Set (SobolevTuple 𝕜 Ω m p)) := by
    ext v
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.property, fun hv => ⟨⟨v, hv⟩, rfl⟩⟩
  rw [hr]
  exact sobolevSubmodule_isClosed Ω m p

/-- Restricting any other finite Lq product norm gives exactly the Sobolev topology. -/
theorem sobolev_product_norm_equivalence (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Topology.IsEmbedding (fun u : Sobolev 𝕜 Ω m p =>
      (WithLp.toLp q u.val.ofLp : PiLp q (fun _ : SobolevIndex d m => DomainLp 𝕜 Ω p))) :=
  (PiLp.homeomorph q _).symm.isEmbedding.comp
    ((PiLp.homeomorph 1 _).isEmbedding.comp Topology.IsEmbedding.subtypeVal)

/-- When zero is the only available multi-index, the underlying map is an isometry onto Lp. -/
theorem sobolev_isometry_of_only_zero
    (hidx : ∀ α : SobolevIndex d m, α = zeroSobolevIndex d m) :
    ∃ e : Sobolev 𝕜 Ω m p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
      ∀ u, e u = sobolevUnderlying u := by
  have hs : Function.Surjective (@sobolevUnderlying d 𝕜 _ Ω m p _) := by
    intro u
    have hu : HasSobolevDerivatives Ω m p u := by
      intro α hα
      have ha : α = 0 := congrArg Subtype.val (hidx ⟨α, hα⟩)
      exact ⟨u, ha ▸ derivative_zero d 𝕜 Ω _⟩
    exact (Set.ext_iff.mp (sobolev_range Ω m p) u).mpr hu
  let e : Sobolev 𝕜 Ω m p ≃ₗ[𝕜] DomainLp 𝕜 Ω p :=
    LinearEquiv.ofBijective (sobolevUnderlyingCLM Ω m p).toLinearMap
      ⟨sobolevUnderlying_injective Ω m p, hs⟩
  have hn (u : Sobolev 𝕜 Ω m p) : ‖e u‖ = ‖u‖ := by
    change ‖sobolevUnderlying u‖ = ‖u‖
    rw [sobolev_norm Ω m p]
    symm
    apply Finset.sum_eq_single (zeroSobolevIndex d m)
    · intro α _ hα
      exact (hα (hidx α)).elim
    · simp
  exact ⟨{ toLinearEquiv := e, norm_map' := hn }, fun _ => rfl⟩

/-- W^{0,p} is canonically linearly isometric to the original Lp space. -/
theorem sobolev_zeroOrder_isometry :
    ∃ e : Sobolev 𝕜 Ω 0 p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
      ∀ u, e u = sobolevUnderlying u := by
  apply sobolev_isometry_of_only_zero Ω 0 p
  intro α
  apply Subtype.ext
  exact Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero α.property)

/-- In dimension zero there are no positive-order coordinate derivatives. -/
theorem sobolev_zeroDimension_isometry (Ω₀ : Opens (Space 0)) :
    ∃ e : Sobolev 𝕜 Ω₀ m p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω₀ p,
      ∀ u, e u = sobolevUnderlying u := by
  apply sobolev_isometry_of_only_zero Ω₀ m p
  intro α
  apply Subtype.ext
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro i
  exact Fin.elim0 i

/-- The empty-domain space contains only zero, for every order and exponent. -/
theorem sobolev_empty (u : Sobolev 𝕜 (⊥ : Opens (Space d)) m p) : u = 0 := by
  apply sobolevUnderlying_injective (⊥ : Opens (Space d)) m p
  apply Lp.ext
  simp only [Opens.coe_bot, Measure.restrict_empty, ae_zero]
  exact Filter.eventually_bot

end P102.U4
