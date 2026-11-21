import MathGenome.Internal.FourierSobolev.Specs.P102.U4.MeyersSerrin
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionOperations
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! Meyers–Serrin approximation on arbitrary open sets.
The whole-space and zero-extension clauses reuse the independently proved prerequisites. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology Pointwise
namespace P102.U4

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coordinate sum error is exactly the Sobolev distance. -/
theorem domainSobolevSumError_eq_norm (u v : Sobolev 𝕜 Ω m p) :
    domainSobolevSumError u v = ‖u - v‖ := by
  rw [sobolev_norm Ω m p]
  rfl

/-- On the whole space the new domain notation agrees with the frozen interface. -/
theorem representsSobolevOn_top_iff (f : Space d → 𝕜)
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) :
    RepresentsSobolevOn f u ↔ RepresentsSobolev f u := by
  simp only [RepresentsSobolevOn, RepresentsSobolev, Opens.coe_top, Measure.restrict_univ]

/-- Smooth compactly supported density, conditional on the supplied whole-space
results. All six premises remain explicit and in their required order. -/
theorem meyersSerrin_wholeSpaceDensity_conditional
    (_hCutoff : WholeSpaceDensityExpected.Cutoff)
    (hDensity : WholeSpaceDensityExpected.Density)
    (_hMollification : WholeSpaceDensityExpected.Mollification)
    (_hMollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_hSmoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_hWeakMollification : WholeSpaceDensityExpected.WeakMollification) :
    MeyersSerrinExpected.WholeSpaceDensity :=
  hDensity

/-- The independently available zero-extension theorem supplies the source's
closure, isometry, and every derivative identity. -/
theorem meyersSerrin_zeroExtension_conditional
    (_hCutoff : WholeSpaceDensityExpected.Cutoff)
    (_hDensity : WholeSpaceDensityExpected.Density)
    (_hMollification : WholeSpaceDensityExpected.Mollification)
    (_hMollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_hSmoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_hWeakMollification : WholeSpaceDensityExpected.WeakMollification) :
    MeyersSerrinExpected.ZeroExtension :=
  ⟨zeroExtension_closure, zeroExtension_operator⟩

/-- The smooth-density conclusion on the whole open space, obtained without
assuming any arbitrary-domain extension theorem. -/
theorem smoothDensity_top_of_wholeSpace
    (hDensity : WholeSpaceDensityExpected.Density)
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev (d := d) 𝕜 (⊤ : Opens (Space d)) m p) :
    ∃ (f : ℕ → Space d → 𝕜) (v : ℕ → Sobolev 𝕜 (⊤ : Opens (Space d)) m p),
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) ⊤ ∧ RepresentsSobolevOn (f n) (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      Tendsto (fun n => domainSobolevSumError (v n) u) atTop (𝓝 0) := by
  obtain ⟨φ, v, hv, ht, he⟩ := hDensity m p hp u
  refine ⟨fun n => φ n, v, fun n => ⟨(φ n).contDiff.contDiffOn, ?_⟩, ht, he⟩
  exact (representsSobolevOn_top_iff _ _).mpr (hv n)

/-- Empty domains need no regularity or positive dimension, even at p = ∞. -/
theorem smoothDensity_empty (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev (d := d) 𝕜 (⊥ : Opens (Space d)) m p) :
    ∃ (f : ℕ → Space d → 𝕜) (v : ℕ → Sobolev 𝕜 (⊥ : Opens (Space d)) m p),
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) ⊥ ∧ RepresentsSobolevOn (f n) (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      Tendsto (fun n => domainSobolevSumError (v n) u) atTop (𝓝 0) := by
  have hu : u = 0 := sobolev_empty m p u
  subst u
  refine ⟨fun _ => 0, fun _ => 0, ?_, tendsto_const_nhds, ?_⟩
  · intro n
    refine ⟨contDiff_const.contDiffOn, ?_⟩
    intro α
    simp only [Opens.coe_bot, Measure.restrict_empty]
    simp only [MeasureTheory.ae_zero]
    exact Filter.eventually_bot
  · simpa only [domainSobolevSumError_eq_norm, sub_self, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- A countable smooth partition on an arbitrary open set. Each member has
ambient compact support inside Ω. Local finiteness is asserted on Ω, which is
essential when the domain has a boundary. -/
theorem exists_testPartition_partialSums (Ω : Opens (Space d)) :
    ∃ θ : ℕ → TestSpace ℝ Ω,
      (∀ n x, 0 ≤ θ n x) ∧
      LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (θ n)}) ∧
      (∀ x : Ω, ∃ N : ℕ, ∀ n ≥ N, ∑ j ∈ Finset.range (n + 1), θ j x = 1) := by
  classical
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let e := CompactExhaustion.choice Ω
  let K : ℕ → Compacts (Space d) := fun n =>
    ⟨Subtype.val '' e n, (e.isCompact n).image continuous_subtype_val⟩
  let V : ℕ → Opens (Space d) := fun n =>
    ⟨Subtype.val '' interior (e (n + 1)), Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior⟩
  have hKV (n : ℕ) : (K n : Set (Space d)) ⊆ V n := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, e.subset_interior_succ n hy, rfl⟩
  have hVΩ (n : ℕ) : V n ≤ Ω := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hVK (n : ℕ) : (V n : Set (Space d)) ⊆ K (n + 1) := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, interior_subset hy, rfl⟩
  choose χ hχ01 U hKU hUV hχ1 using fun n => cutoff d (V n) (K n) (hKV n)
  let η : ℕ → TestSpace ℝ Ω := fun n => zeroExtension ℝ (hVΩ n) (χ n)
  have hηcoe (n : ℕ) : (η n : Space d → ℝ) = χ n := by
    ext x
    simp [η, zeroExtension, TestFunction.monoCLM_apply, hVΩ n]
  have hη01 (n : ℕ) (x : Space d) : 0 ≤ η n x ∧ η n x ≤ 1 := by
    rw [hηcoe]
    exact hχ01 n x
  have hη1 (n : ℕ) (x : Space d) (hx : x ∈ K n) : η n x = 1 := by
    rw [hηcoe]
    exact hχ1 n x (hKU n hx)
  have hηsupport (n : ℕ) : tsupport (η n) ⊆ K (n + 1) := by
    rw [hηcoe]
    exact (χ n).tsupport_subset.trans (hVK n)
  let θ : ℕ → TestSpace ℝ Ω
    | 0 => η 0
    | n + 1 => η (n + 1) - η n
  have hθsum (n : ℕ) (x : Space d) :
      ∑ j ∈ Finset.range (n + 1), θ j x = η n x := by
    induction n with
    | zero => simp [θ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      change η n x + (η (n + 1) x - η n x) = η (n + 1) x
      ring
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro n x
    cases n with
    | zero => exact (hη01 0 x).1
    | succ n =>
      change 0 ≤ η (n + 1) x - η n x
      by_cases hx : x ∈ tsupport (η n)
      · rw [hη1 (n + 1) x (hηsupport n hx)]
        exact sub_nonneg.mpr (hη01 n x).2
      · rw [image_eq_zero_of_notMem_tsupport hx, sub_zero]
        exact (hη01 (n + 1) x).1
  · intro x
    obtain ⟨N, hN⟩ := e.exists_mem_nhds x
    let W : Set (Space d) := Subtype.val '' interior (e N)
    have hWo : IsOpen W := Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior
    have hxW : (x : Space d) ∈ W := ⟨x, mem_interior_iff_mem_nhds.mpr hN, rfl⟩
    refine ⟨Subtype.val ⁻¹' W, continuous_subtype_val.continuousAt (hWo.mem_nhds hxW),
      (Set.finite_le_nat N).subset ?_⟩
    rintro n ⟨y, hyn, hyW⟩
    by_contra hn
    have hnN : N < n := Nat.lt_of_not_ge hn
    have hz : (θ n : Space d → ℝ) =ᶠ[𝓝 (y : Space d)] 0 := by
      filter_upwards [hWo.mem_nhds hyW] with z hz
      obtain ⟨w, hw, rfl⟩ := hz
      cases n with
      | zero => omega
      | succ n =>
        have hNn : N ≤ n := by omega
        change η (n + 1) w - η n w = 0
        rw [hη1 (n + 1) w ⟨w, e.subset (by omega) (interior_subset hw), rfl⟩,
          hη1 n w ⟨w, e.subset hNn (interior_subset hw), rfl⟩, sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hyn
  · intro x
    obtain ⟨N, hN⟩ := e.exists_mem x
    refine ⟨N, fun n hn => ?_⟩
    rw [hθsum]
    exact hη1 n x ⟨x, e.subset hn hN, rfl⟩

/-- The partition identity in the usual finitely supported sum notation. -/
theorem exists_testPartition (Ω : Opens (Space d)) :
    ∃ θ : ℕ → TestSpace ℝ Ω,
      (∀ n x, 0 ≤ θ n x) ∧
      LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (θ n)}) ∧
      (∀ x : Ω, ∑ᶠ n, θ n x = 1) := by
  classical
  obtain ⟨θ, hθ, hlf, hs⟩ := exists_testPartition_partialSums Ω
  refine ⟨θ, hθ, hlf, fun x => ?_⟩
  obtain ⟨N, hN⟩ := hs x
  have hfin := hlf.point_finite x
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hsupp : Function.support (fun n => θ n x) ⊆
      (Finset.range (max N M + 1) : Set ℕ) := by
    intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((hM (subset_tsupport (θ n) hn)).trans (le_max_right N M))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  exact hN _ (le_max_left N M)

/-- A locally finite family reduces to one fixed finite sum on a neighborhood
of any point of Ω. The neighborhood is ambient, because Ω is open. -/
theorem locallyFinite_finsum_eventuallyEq {f : ℕ → Space d → 𝕜}
    (hlf : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (f n)}))
    {x : Space d} (hx : x ∈ Ω) :
    ∃ s : Finset ℕ, (fun y => ∑ᶠ n, f n y) =ᶠ[𝓝 x] fun y => ∑ n ∈ s, f n y := by
  classical
  obtain ⟨U, hU, hfin⟩ := hlf ⟨x, hx⟩
  refine ⟨hfin.toFinset, ?_⟩
  have he : ∀ᶠ y : Ω in 𝓝 (⟨x, hx⟩ : Ω),
      (∑ᶠ n, f n y) = ∑ n ∈ hfin.toFinset, f n y := by
    filter_upwards [hU] with y hy
    apply finsum_eq_sum_of_support_subset
    intro n hn
    apply hfin.mem_toFinset.mpr
    exact ⟨y, subset_tsupport (f n) hn, hy⟩
  have hmap := map_nhds_subtype_coe_eq_nhds hx (Ω.isOpen.mem_nhds hx)
  rw [← hmap]
  exact he

/-- The locally finite smooth sum used by the localization argument is smooth
on Ω without any assertion of smoothness across its boundary. -/
theorem contDiffOn_finsum_of_locallyFinite {f : ℕ → Space d → 𝕜}
    (hf : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) Ω)
    (hlf : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (f n)})) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ᶠ n, f n x) Ω := by
  intro x hx
  obtain ⟨s, hs⟩ := locallyFinite_finsum_eventuallyEq hlf hx
  exact ((ContDiffAt.sum fun n (_ : n ∈ s) =>
    (hf n).contDiffAt (Ω.isOpen.mem_nhds hx)).congr_of_eventuallyEq hs).contDiffWithinAt

/-- Norm convergence is exactly convergence of the finite derivative sum. -/
theorem tendsto_iff_domainSobolevSumError {ι : Type*} {l : Filter ι}
    {v : ι → Sobolev 𝕜 Ω m p} {u : Sobolev 𝕜 Ω m p} :
    Tendsto v l (𝓝 u) ↔
      Tendsto (fun i => domainSobolevSumError (v i) u) l (𝓝 0) := by
  simp only [domainSobolevSumError_eq_norm]
  exact tendsto_iff_norm_sub_tendsto_zero

/-- In dimension zero every open set is either empty or the whole singleton.
Thus the entire smooth-density conclusion follows from the whole-space premise. -/
theorem smoothDensity_zeroDimension_of_wholeSpace
    (hDensity : WholeSpaceDensityExpected.Density)
    (Ω : Opens (Space 0)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω m p) :
    ∃ (f : ℕ → Space 0 → 𝕜) (v : ℕ → Sobolev 𝕜 Ω m p),
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) Ω ∧ RepresentsSobolevOn (f n) (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      Tendsto (fun n => domainSobolevSumError (v n) u) atTop (𝓝 0) := by
  have hΩ : Ω = ⊥ ∨ Ω = ⊤ := by
    by_cases he : (Ω : Set (Space 0)).Nonempty
    · right
      obtain ⟨x, hx⟩ := he
      apply top_unique
      intro y _
      have hyx : y = x := Subsingleton.elim _ _
      rw [hyx]
      exact hx
    · left
      apply bot_unique
      intro x hx
      exact False.elim (he ⟨x, hx⟩)
  rcases hΩ with rfl | rfl
  · exact smoothDensity_empty m p u
  · exact smoothDensity_top_of_wholeSpace hDensity m p hp u

/-- A test represents all of the weak derivative coordinates of its Sobolev
class, not merely the zeroth coordinate used in the definition of W₀. -/
theorem test_representsSobolevOn (φ : TestSpace 𝕜 Ω) (u : Sobolev 𝕜 Ω m p)
    (hu : sobolevUnderlying u = testToDomainLp Ω p φ) : RepresentsSobolevOn φ u := by
  intro α
  let ψ := testPartialWord Ω (α.val.sort (· ≤ ·)) φ
  have he : regularDistribution Ω (sobolevDerivative u α) =
      regularDistribution Ω (testToDomainLp Ω p ψ) := by
    rw [← sobolev_derivative_distribution Ω m p u α, hu,
      regular_testToDomainLp Ω p, regular_testToDomainLp Ω p]
    rw [derivative_classicalCompatibility d 𝕜 Ω α.val φ
      (φ.contDiff.of_le (by simp)).contDiffOn]
    congr 1
    exact (testPartialWord_coe Ω _ φ).symm
  have hv := regularLp_injective Ω p he
  rw [hv]
  exact (testToDomainLp_ae Ω p ψ).trans (Filter.Eventually.of_forall
    (congrFun (testPartialWord_coe Ω _ φ)))

/-- Smooth density on the closed zero-boundary subspace follows directly from
its definition. This is a partial domain result and does not identify W₀ with W. -/
theorem smoothDensity_on_sobolevZero (u : SobolevZero 𝕜 Ω m p) :
    ∃ (φ : ℕ → TestSpace 𝕜 Ω) (v : ℕ → Sobolev 𝕜 Ω m p),
      (∀ n, RepresentsSobolevOn (φ n) (v n)) ∧
      Tendsto v atTop (𝓝 u.val) ∧
      Tendsto (fun n => domainSobolevSumError (v n) u.val) atTop (𝓝 0) := by
  classical
  have hmem : u.val ∈ closure {v : Sobolev 𝕜 Ω m p |
      ∃ φ : TestSpace 𝕜 Ω, sobolevUnderlying v = testToDomainLp Ω p φ} := by
    rw [← zeroExtension_closure Ω m p]
    exact u.property
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hmem
  choose φ hφ using hv
  exact ⟨φ, v, fun n => test_representsSobolevOn (φ n) (v n) (hφ n), ht,
    tendsto_iff_domainSobolevSumError.mp ht⟩

/-- Multiplying an Lp class by a test is again Lp, and its regular distribution
is precisely the canonical distribution product. -/
theorem exists_regular_testProduct (φ : TestSpace 𝕜 Ω) (v : DomainLp 𝕜 Ω p) :
    ∃ w : DomainLp 𝕜 Ω p,
      regularDistribution Ω w = distributionMultiplier
        ⟨φ, φ.contDiff.contDiffOn⟩ (regularDistribution Ω v) ∧
      (w : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
        fun x => φ x * v x := by
  have hm : MemLp (fun x => φ x * v x) p (volume.restrict (Ω : Set (Space d))) :=
    (φ.continuous.memLp_of_hasCompactSupport (p := ∞) φ.hasCompactSupport).mul (Lp.memLp v)
  refine ⟨hm.toLp _, ?_, hm.coeFn_toLp⟩
  ext ψ
  change regularDistribution Ω (hm.toLp _) ψ =
    regularDistribution Ω v (coefficientTestProduct ⟨φ, φ.contDiff.contDiffOn⟩ ψ)
  rw [regular_pairing d 𝕜 Ω _ (domainLp_locallyIntegrable Ω p _),
    regular_pairing d 𝕜 Ω _ (domainLp_locallyIntegrable Ω p _)]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]
  change φ x * v x * ψ x = v x * (φ x * ψ x)
  ring

/-- Every term of the iterated product rule has an Lp representative. The
cardinality bound records exactly the remaining derivative order. -/
theorem leibnizExpansion_hasLp (u : Sobolev 𝕜 Ω m p) (l : List (Fin d)) :
    ∀ (φ : TestSpace 𝕜 Ω) (β : MultiIndex d), β.card + l.length ≤ m →
    ∃ w : DomainLp 𝕜 Ω p, regularDistribution Ω w =
      leibnizExpansion testMultiplier l ⟨φ, φ.contDiff.contDiffOn⟩
        (distributionPartial β (regularDistribution Ω (sobolevUnderlying u))) := by
  induction l with
  | nil =>
    intro φ β hβ
    have hβm : β.card ≤ m := by simpa using hβ
    obtain ⟨w, hw, _⟩ := exists_regular_testProduct φ (sobolevDerivative u ⟨β, hβm⟩)
    refine ⟨w, ?_⟩
    rw [sobolev_derivative_distribution Ω m p u ⟨β, hβm⟩]
    exact hw
  | cons i l ih =>
    intro φ β hβ
    have hleft : β.card + l.length ≤ m := by
      simp only [List.length_cons] at hβ
      omega
    have hright : ({i} + β).card + l.length ≤ m := by
      simp only [Multiset.card_add, Multiset.card_singleton]
      simp only [List.length_cons] at hβ
      omega
    obtain ⟨w₁, hw₁⟩ := ih (testPartialWord Ω [i] φ) β hleft
    obtain ⟨w₂, hw₂⟩ := ih φ ({i} + β) hright
    refine ⟨w₁ + w₂, ?_⟩
    have hadd : regularDistribution Ω (w₁ + w₂) =
        regularDistribution Ω w₁ + regularDistribution Ω w₂ := by
      ext ψ
      simp only [add_apply, regularLp_pairing Ω p]
      exact map_add (lpTestPairing Ω p ψ) w₁ w₂
    rw [hadd, hw₁, hw₂]
    change _ = leibnizExpansion testMultiplier l
        (coefficientPartial i ⟨φ, φ.contDiff.contDiffOn⟩)
        (distributionPartial β (regularDistribution Ω (sobolevUnderlying u))) +
      leibnizExpansion testMultiplier l ⟨φ, φ.contDiff.contDiffOn⟩
        (distributionPartial {i} (distributionPartial β
          (regularDistribution Ω (sobolevUnderlying u))))
    rw [← derivative_add d 𝕜 Ω {i} β]
    congr 2

/-- A compactly supported smooth localization of an arbitrary Sobolev class has
the full Sobolev regularity. No boundary assumption on Ω enters this statement. -/
theorem exists_sobolev_testProduct (φ : TestSpace 𝕜 Ω) (u : Sobolev 𝕜 Ω m p) :
    ∃ v : Sobolev 𝕜 Ω m p,
      (sobolevUnderlying v : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => φ x * sobolevUnderlying u x) ∧
      HasCompactSupportIn (sobolevUnderlying v) := by
  obtain ⟨w, hw, hwae⟩ := exists_regular_testProduct φ (sobolevUnderlying u)
  have hwreg : HasSobolevDerivatives Ω m p w := by
    intro α hα
    obtain ⟨z, hz⟩ := leibnizExpansion_hasLp u (α.sort (· ≤ ·)) φ 0 (by simpa using hα)
    refine ⟨z, ?_⟩
    rw [hw, distributionMultiplier_iteratedProductRule]
    rw [derivative_zero] at hz
    exact hz.symm
  have hwrange : w ∈ Set.range (@sobolevUnderlying d 𝕜 _ Ω m p _) := by
    rw [sobolev_range Ω m p]
    exact hwreg
  obtain ⟨v, hv⟩ := hwrange
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact hwae
  · refine ⟨⟨tsupport φ, φ.hasCompactSupport⟩, φ.tsupport_subset, ?_⟩
    rw [hv]
    filter_upwards [hwae] with x hx hxφ
    rw [hx, image_eq_zero_of_notMem_tsupport hxφ, zero_mul]

/-- Each localized piece extends to a whole-space Sobolev class, with every
derivative extended by zero and exactly the same derivative sum norm. -/
theorem exists_localized_wholeSpace (hp : p ≠ ⊤)
    (φ : TestSpace 𝕜 Ω) (u : Sobolev 𝕜 Ω m p) :
    ∃ (v : Sobolev 𝕜 Ω m p) (w : Sobolev (d := d) 𝕜 ⊤ m p),
      (sobolevUnderlying v : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => φ x * sobolevUnderlying u x) ∧
      HasCompactSupportIn (sobolevUnderlying v) ∧
      sobolevUnderlying w = lpZeroExtension Ω p (sobolevUnderlying v) ∧
      (∀ α, sobolevDerivative w α = lpZeroExtension Ω p (sobolevDerivative v α)) ∧
      ‖w‖ = ‖v‖ := by
  obtain ⟨v, hv, hvc⟩ := exists_sobolev_testProduct φ u
  obtain ⟨w, hw, hwd, hwn⟩ := zeroExtension_compact Ω m p hp v hvc
  exact ⟨v, w, hv, hvc, hw, hwd, hwn⟩

/-- The compactly supported whole-space clause of AN-11-C04-R03. -/
theorem meyersSerrin_wholeSpaceDensity : MeyersSerrinExpected.WholeSpaceDensity :=
  wholeSpace_density

/-- The closure and derivative-commuting isometric zero-extension clause. -/
theorem meyersSerrin_zeroExtension : MeyersSerrinExpected.ZeroExtension :=
  ⟨zeroExtension_closure, zeroExtension_operator⟩

/-- Restriction of an Lp class to an open set. -/
def domainLpRestrict (Ω : Opens (Space d)) (u : DomainLp (d := d) 𝕜 ⊤ p) : DomainLp 𝕜 Ω p :=
  (show MemLp (u : Space d → 𝕜) p (volume.restrict (Ω : Set (Space d))) from
    (show MemLp (u : Space d → 𝕜) p volume by simpa using Lp.memLp u).restrict Ω).toLp u

theorem domainLpRestrict_ae (Ω : Opens (Space d)) (u : DomainLp (d := d) 𝕜 ⊤ p) :
    (domainLpRestrict Ω u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] u :=
  MemLp.coeFn_toLp _

theorem domainLpRestrict_norm_le (Ω : Opens (Space d)) (u : DomainLp (d := d) 𝕜 ⊤ p) :
    ‖domainLpRestrict Ω u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (domainLpRestrict_ae Ω u)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  exact ENNReal.toReal_mono (by simpa using (Lp.memLp u).eLpNorm_ne_top)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Restriction is a contraction; its bound is independent of the domain. -/
def domainLpRestrictCLM (Ω : Opens (Space d)) : DomainLp (d := d) 𝕜 ⊤ p →L[𝕜] DomainLp 𝕜 Ω p :=
  LinearMap.mkContinuous
    { toFun := domainLpRestrict Ω
      map_add' := by
        intro u v
        have hadd := Lp.coeFn_add u v
        simp only [Opens.coe_top, Measure.restrict_univ] at hadd
        apply Lp.ext
        filter_upwards [domainLpRestrict_ae Ω (u + v), domainLpRestrict_ae Ω u,
          domainLpRestrict_ae Ω v, Lp.coeFn_add (domainLpRestrict Ω u) (domainLpRestrict Ω v),
          ae_restrict_of_ae hadd] with x huv hu hv hsum hsum'
        simp only [Pi.add_apply] at hsum hsum'
        rw [huv, hsum', hsum, hu, hv]
      map_smul' := by
        intro c u
        have hsmul := Lp.coeFn_smul c u
        simp only [Opens.coe_top, Measure.restrict_univ] at hsmul
        apply Lp.ext
        filter_upwards [domainLpRestrict_ae Ω (c • u), domainLpRestrict_ae Ω u,
          Lp.coeFn_smul c (domainLpRestrict Ω u),
          ae_restrict_of_ae hsmul] with x hcu hu hsm hsm'
        simp only [Pi.smul_apply] at hsm hsm'
        simpa only [RingHom.id_apply] using hcu.trans (hsm'.trans (by rw [hsm, hu])) }
    1 (by intro u; simpa using domainLpRestrict_norm_le Ω u)

/-- The pairing after restriction is the original pairing with the same
ambient test, viewed as a whole-space test by zero extension. -/
theorem lpTestPairing_restrict (Ω : Opens (Space d)) (φ : TestSpace 𝕜 Ω)
    (u : DomainLp (d := d) 𝕜 ⊤ p) :
    lpTestPairing Ω p φ (domainLpRestrict Ω u) =
      lpTestPairing ⊤ p (zeroExtension 𝕜 le_top φ) u := by
  rw [lpTestPairing_eq_integral, lpTestPairing_eq_integral]
  simp only [Opens.coe_top, Measure.restrict_univ, zeroExtension, TestFunction.monoCLM_apply,
    le_top, and_self, ↓reduceIte]
  rw [← setIntegral_mul_test Ω (u : Space d → 𝕜) φ]
  apply integral_congr_ae
  filter_upwards [domainLpRestrict_ae Ω u] with x hx
  simpa only [zeroExtension, TestFunction.monoCLM_apply] using congrArg (fun z => z * φ x) hx

/-- Sobolev restriction retains every derivative coordinate. -/
def sobolevRestrict (Ω : Opens (Space d)) (u : Sobolev (d := d) 𝕜 ⊤ m p) : Sobolev 𝕜 Ω m p :=
  ⟨WithLp.toLp 1 (fun α => domainLpRestrict Ω (sobolevDerivative u α)), by
    apply (mem_sobolevSubmodule_iff Ω m p _).mpr
    intro α φ
    change lpTestPairing Ω p φ (domainLpRestrict Ω (sobolevDerivative u α)) = _
    rw [lpTestPairing_restrict]
    have he := (mem_sobolevSubmodule_iff ⊤ m p u.val).mp u.property α
      (zeroExtension 𝕜 le_top φ)
    change lpTestPairing _ _ _ (sobolevDerivative u α) = _ at he
    rw [he]
    congr 1
    rw [lpTestPairing_restrict]
    congr 2
    apply TestFunction.ext
    intro x
    simp only [testPartialWord_coe, zeroExtension, TestFunction.monoCLM_apply,
      le_top, and_self, ↓reduceIte]⟩

theorem sobolevRestrict_derivative (Ω : Opens (Space d)) (u : Sobolev (d := d) 𝕜 ⊤ m p)
    (α : SobolevIndex d m) :
    sobolevDerivative (sobolevRestrict Ω u) α = domainLpRestrict Ω (sobolevDerivative u α) := rfl

theorem sobolevRestrict_norm_le (Ω : Opens (Space d)) (u : Sobolev (d := d) 𝕜 ⊤ m p) :
    ‖sobolevRestrict Ω u‖ ≤ ‖u‖ := by
  rw [sobolev_norm, sobolev_norm]
  exact Finset.sum_le_sum fun α _ => domainLpRestrict_norm_le Ω _

/-- Shrinking enlargements of a locally finite family remain locally finite
on the open domain. The sets themselves may accumulate at the boundary. -/
theorem locallyFinite_add_closedBall {K : ℕ → Set (Space d)}
    (hKΩ : ∀ n, K n ⊆ Ω)
    (hK : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ K n}))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ K n + Metric.closedBall 0 (r n)}) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hK x
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hU
  have hev : ∀ᶠ n in atTop, r n < R / 2 :=
    hr.eventually (eventually_lt_nhds (half_pos hR))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨Metric.ball x (R / 2), Metric.ball_mem_nhds _ (half_pos hR),
    (hfin.union (Set.finite_Iio N)).subset ?_⟩
  rintro n ⟨y, hy, hyball⟩
  by_cases hn : n < N
  · exact Or.inr hn
  · left
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    refine ⟨⟨a, hKΩ n ha⟩, ha, hRU ?_⟩
    have hb' : ‖b‖ ≤ r n := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
    have hdist : dist a (y : Space d) = ‖b‖ := by
      rw [← hab, dist_eq_norm]
      simp only [sub_add_cancel_left, norm_neg]
    change dist a (x : Space d) < R
    have hy' : dist (y : Space d) (x : Space d) < R / 2 := hyball
    calc
      dist a (x : Space d) ≤ dist a (y : Space d) + dist (y : Space d) (x : Space d) :=
        dist_triangle _ _ _
      _ < R / 2 + R / 2 := add_lt_add (by rw [hdist]; exact hb'.trans_lt (hN n (Nat.le_of_not_gt hn))) hy'
      _ = R := add_halves R

/-- An essential-support bound gives the expected Minkowski-sum bound for the
actual smooth convolution representative, rather than just compactness. -/
theorem tsupport_localConvolution_subset {f : Space d → 𝕜}
    (hf : LocallyIntegrable f volume) (K : Compacts (Space d))
    (hK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) (ρ : WholeTests d 𝕜) :
    tsupport (localConvolution (regularDistribution ⊤ f) ρ) ⊆
      (K : Set (Space d)) + tsupport ρ := by
  apply closure_minimal _ (K.isCompact.add ρ.hasCompactSupport).isClosed
  intro x hx
  by_contra hxsum
  apply hx
  rw [localConvolution_regular_whole hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hK] with y hy
  by_cases hyK : y ∈ K
  · have hz : ρ (x - y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hxsum ⟨y, hyK, x - y, hz, by abel_nf⟩
    simp [hz]
  · simp [hy hyK]

/-- The Sobolev restriction operator is linear and contractive in the full
sum norm, so it can be applied to convergent series of errors. -/
def sobolevRestrictCLM (Ω : Opens (Space d)) :
    Sobolev (d := d) 𝕜 ⊤ m p →L[𝕜] Sobolev 𝕜 Ω m p :=
  LinearMap.mkContinuous
    { toFun := sobolevRestrict Ω
      map_add' := by
        intro u v
        apply Subtype.ext
        apply PiLp.ext
        intro α
        change domainLpRestrict Ω (sobolevDerivative u α + sobolevDerivative v α) =
          domainLpRestrict Ω (sobolevDerivative u α) + domainLpRestrict Ω (sobolevDerivative v α)
        exact map_add (domainLpRestrictCLM Ω) _ _
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply PiLp.ext
        intro α
        change domainLpRestrict Ω (c • sobolevDerivative u α) =
          c • domainLpRestrict Ω (sobolevDerivative u α)
        exact map_smul (domainLpRestrictCLM Ω) _ _ }
    1 (by intro u; simpa using sobolevRestrict_norm_le Ω u)

/-- Restricting a zero extension gives the original Lp class. -/
theorem domainLpRestrict_zeroExtension (Ω : Opens (Space d)) (u : DomainLp 𝕜 Ω p) :
    domainLpRestrict Ω (lpZeroExtension Ω p u) = u := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_ae Ω (lpZeroExtension Ω p u),
    ae_restrict_of_ae (lpZeroExtension_ae Ω p u), ae_restrict_mem Ω.isOpen.measurableSet]
    with x hx he hxΩ
  rw [hx, he, Set.indicator_of_mem hxΩ]

/-- The full weak-derivative representation follows from a smooth underlying
representative. This imposes no smoothness across the boundary. -/
theorem representsSobolevOn_of_underlying {f : Space d → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (u : Sobolev 𝕜 Ω m p)
    (hu : (sobolevUnderlying u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] f) :
    RepresentsSobolevOn f u := by
  have hfl : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have he := (regular_injectivity d 𝕜 Ω _ _ (domainLp_locallyIntegrable Ω p _) hfl).mpr hu
  intro α
  have hfd : ContDiffOn ℝ (α.val.card : ℕ) f Ω := hf.of_le (by simp)
  have hd : LocallyIntegrableOn (multiPartial f α.val) Ω volume :=
    (partialWord_contDiffOn Ω hfd (α.val.sort (· ≤ ·)) 0 (by simp)).continuousOn.locallyIntegrableOn
      Ω.isOpen.measurableSet
  apply (regular_injectivity d 𝕜 Ω _ _ (domainLp_locallyIntegrable Ω p _) hd).mp
  rw [← sobolev_derivative_distribution Ω m p, he,
    derivative_classicalCompatibility d 𝕜 Ω α.val f hfd]

/-- Mollification can satisfy an arbitrary sum-norm tolerance and an arbitrary
positive support radius simultaneously. All derivatives are included in the error. -/
theorem exists_mollified_approximation (hp : p ≠ ⊤)
    (u : Sobolev (d := d) 𝕜 ⊤ m p) (K : Compacts (Space d))
    (hK : ∀ᵐ x ∂volume, x ∉ K → sobolevUnderlying u x = 0)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (φ : WholeTests d 𝕜) (v : Sobolev (d := d) 𝕜 ⊤ m p),
      RepresentsSobolev φ v ∧ ‖v - u‖ < ε ∧
      tsupport φ ⊆ (K : Set (Space d)) + Metric.closedBall 0 δ := by
  obtain ⟨ρ, hρ⟩ := wholeSpace_mollifierExistence d 𝕜
  obtain ⟨v, hv, _, ht⟩ := wholeSpace_mollification m p hp ρ hρ u ⟨K, hK⟩
  have hsmall := ht.eventually (eventually_lt_nhds hε)
  have hless : ∀ᶠ t : ℝ in 𝓝[>] 0, t < δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  obtain ⟨t, htε, htδ, htpos⟩ := (hsmall.and (hless.and self_mem_nhdsWithin)).exists
  let φ : WholeTests d 𝕜 :=
    ⟨localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ t),
      (hv t htpos).1, (hv t htpos).2.1, subset_univ _⟩
  refine ⟨φ, v t, (hv t htpos).2.2.1, ?_, ?_⟩
  · simpa only [sobolevSumError_eq_norm] using htε
  · have hli : LocallyIntegrable (sobolevUnderlying u : Space d → 𝕜) volume := by
      simpa using (Lp.memLp (sobolevUnderlying u)).locallyIntegrable (Fact.out : 1 ≤ p)
    exact (tsupport_localConvolution_subset hli K hK (ρ t)).trans
      (Set.add_subset_add_left ((hρ.2 t htpos).trans
        (Metric.closedBall_subset_closedBall htδ.le)))

/-- A compact set inside Ω has a positive allowed convolution radius. -/
theorem exists_supportRadius (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      (K : Set (Space d)) + Metric.closedBall (0 : Space d) δ ⊆ (Ω : Set (Space d)) := by
  obtain ⟨δ, hδ, hsub⟩ := K.isCompact.exists_cthickening_subset_open Ω.isOpen hK
  refine ⟨min δ r, lt_min hδ hr, min_le_right _ _, ?_⟩
  rintro x ⟨a, ha, b, hb, rfl⟩
  apply hsub
  apply Metric.mem_cthickening_of_dist_le (a + b) a δ (K : Set (Space d)) ha
  have hb' : ‖b‖ ≤ min δ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb'.trans (min_le_left δ r)

/-- The real partition is available over either scalar field, using precisely
the same compact supports. -/
theorem exists_scalarTestPartition (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :
    ∃ θ : ℕ → TestSpace 𝕜 Ω,
      LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (θ n)}) ∧
      (∀ x : Ω, ∑ᶠ n, θ n x = 1) := by
  obtain ⟨η, _, hlf, hs⟩ := exists_testPartition Ω
  let θ : ℕ → TestSpace 𝕜 Ω := fun n => TestFunction.postcompCLM RCLike.ofRealCLM (η n)
  have hsub (n : ℕ) : tsupport (θ n) ⊆ tsupport (η n) :=
    tsupport_comp_subset (map_zero RCLike.ofRealCLM) _
  refine ⟨θ, hlf.subset (fun n x hx => hsub n hx), fun x => ?_⟩
  have hfin : Function.HasFiniteSupport (fun n => η n x) :=
    (hlf.point_finite x).subset fun n hn => subset_tsupport (η n) hn
  have he := (algebraMap ℝ 𝕜).toAddMonoidHom.map_finsum hfin
  change ((∑ᶠ n, η n x : ℝ) : 𝕜) = ∑ᶠ n, (η n x : 𝕜) at he
  rw [hs x, RCLike.ofReal_one] at he
  exact he.symm

/-- A localized zero extension has the specific compact essential support
needed to control the supports of its mollifications. -/
theorem localized_zeroExtension_support (φ : TestSpace 𝕜 Ω)
    (u v : Sobolev 𝕜 Ω m p) (w : Sobolev (d := d) 𝕜 ⊤ m p)
    (hv : (sobolevUnderlying v : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
      fun x => φ x * sobolevUnderlying u x)
    (hw : sobolevUnderlying w = lpZeroExtension Ω p (sobolevUnderlying v)) :
    ∀ᵐ x ∂volume, x ∉ tsupport φ → sobolevUnderlying w x = 0 := by
  rw [hw]
  have hv' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hv
  filter_upwards [lpZeroExtension_ae Ω p (sobolevUnderlying v), hv'] with x hx hprod hnot
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, hprod hxΩ,
      image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  · exact Set.indicator_of_notMem hxΩ _

/-- Each localized Sobolev piece admits an arbitrarily accurate smooth
approximation whose support stays in its prescribed compact enlargement. -/
theorem exists_localized_approximation (hp : p ≠ ⊤)
    (φ : TestSpace 𝕜 Ω) (u : Sobolev 𝕜 Ω m p) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hΩ : tsupport φ + Metric.closedBall (0 : Space d) r ⊆ (Ω : Set (Space d))) :
    ∃ (v w : Sobolev 𝕜 Ω m p) (ψ : TestSpace 𝕜 Ω),
      ((sobolevUnderlying v : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
        fun x => φ x * sobolevUnderlying u x) ∧
      ((sobolevUnderlying w : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] ψ) ∧
      ‖w - v‖ < ε ∧ tsupport ψ ⊆ tsupport φ + Metric.closedBall 0 r := by
  obtain ⟨v, z, hv, _, hz, _, _⟩ := exists_localized_wholeSpace hp φ u
  have hK := localized_zeroExtension_support φ u v z hv hz
  obtain ⟨ψ, w, hw, herr, hs⟩ := exists_mollified_approximation hp z
    ⟨tsupport φ, φ.hasCompactSupport⟩ hK hr hε
  let ψΩ : TestSpace 𝕜 Ω := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hs.trans hΩ⟩
  have hvback : sobolevRestrict Ω z = v := by
    apply sobolevUnderlying_injective Ω m p
    change domainLpRestrict Ω (sobolevUnderlying z) = _
    rw [hz, domainLpRestrict_zeroExtension]
  refine ⟨v, sobolevRestrict Ω w, ψΩ, hv, ?_, ?_, hs⟩
  · have hwae := hw (zeroSobolevIndex d m)
    simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hwae
    exact (domainLpRestrict_ae Ω (sobolevUnderlying w)).trans (ae_restrict_of_ae hwae)
  · calc
      ‖sobolevRestrict Ω w - v‖ = ‖sobolevRestrict Ω (w - z)‖ := by
        rw [← hvback]
        exact congrArg norm ((sobolevRestrictCLM Ω).map_sub w z).symm
      _ ≤ ‖w - z‖ := sobolevRestrict_norm_le Ω _
      _ < ε := herr

/-- The zeroth coordinate is bounded by the full derivative sum norm. -/
theorem sobolevUnderlying_norm_le (u : Sobolev 𝕜 Ω m p) :
    ‖sobolevUnderlying u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u.val (zeroSobolevIndex d m)

/-- Gluing summable Sobolev errors identifies the limit with the locally finite
smooth sum. The original localized pieces need not be norm-summable. -/
theorem sobolev_glue_localized_errors (u : Sobolev 𝕜 Ω m p)
    (θ φ : ℕ → TestSpace 𝕜 Ω)
    (hθ : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (θ n)}))
    (hθsum : ∀ x : Ω, ∑ᶠ n, θ n x = 1)
    (hφ : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (φ n)}))
    (v w : ℕ → Sobolev 𝕜 Ω m p)
    (hv : ∀ n, (sobolevUnderlying (v n) : Space d → 𝕜)
      =ᵐ[volume.restrict (Ω : Set (Space d))] fun x => θ n x * sobolevUnderlying u x)
    (hw : ∀ n, (sobolevUnderlying (w n) : Space d → 𝕜)
      =ᵐ[volume.restrict (Ω : Set (Space d))] φ n)
    (he : Summable (fun n => ‖w n - v n‖)) :
    ∃ (f : Space d → 𝕜) (z : Sobolev 𝕜 Ω m p),
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ RepresentsSobolevOn f z ∧
      ‖z - u‖ ≤ ∑' n, ‖w n - v n‖ := by
  let e : ℕ → Sobolev 𝕜 Ω m p := fun n => w n - v n
  have hes : Summable e := he.of_norm
  have hep : Summable (fun n => ‖sobolevUnderlying (e n)‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => sobolevUnderlying_norm_le _) he
  have hco : (sobolevUnderlying (∑' n, e n) : Space d → 𝕜)
      =ᵐ[volume.restrict (Ω : Set (Space d))] fun x => ∑' n, sobolevUnderlying (e n) x := by
    have hmap := (sobolevUnderlyingCLM Ω m p).map_tsum hes
    change sobolevUnderlying (∑' n, e n) = ∑' n, sobolevUnderlying (e n) at hmap
    rw [hmap]
    exact Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hep)
  have hpoint : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      ∀ n, sobolevUnderlying (e n) x = φ n x - θ n x * sobolevUnderlying u x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_sub (sobolevUnderlying (w n)) (sobolevUnderlying (v n)),
      hw n, hv n] with x hx hwx hvx
    change (sobolevUnderlying (w n) - sobolevUnderlying (v n)) x = _
    simpa only [Pi.sub_apply, hwx, hvx] using hx
  let f : Space d → 𝕜 := fun x => ∑ᶠ n, φ n x
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω :=
    contDiffOn_finsum_of_locallyFinite (fun n => (φ n).contDiff.contDiffOn) hφ
  have hrep : (sobolevUnderlying (u + ∑' n, e n) : Space d → 𝕜)
      =ᵐ[volume.restrict (Ω : Set (Space d))] f := by
    filter_upwards [hco, hpoint,
      Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying (∑' n, e n)),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hcox hpx hadd hxΩ
    have hθfin : Function.HasFiniteSupport (fun n => θ n x) :=
      (hθ.point_finite ⟨x, hxΩ⟩).subset fun n hn => subset_tsupport (θ n) hn
    have hφfin : Function.HasFiniteSupport (fun n => φ n x) :=
      (hφ.point_finite ⟨x, hxΩ⟩).subset fun n hn => subset_tsupport (φ n) hn
    have hprod : Function.HasFiniteSupport (fun n => θ n x * sobolevUnderlying u x) :=
      hθfin.mul_left _
    have hdiff : Function.HasFiniteSupport (fun n => φ n x - θ n x * sobolevUnderlying u x) :=
      hφfin.sub hprod
    change (sobolevUnderlying u + sobolevUnderlying (∑' n, e n)) x = _
    rw [hadd, Pi.add_apply, hcox, tsum_congr hpx, tsum_eq_finsum hdiff,
      finsum_sub_distrib hφfin hprod, ← finsum_mul', hθsum ⟨x, hxΩ⟩, one_mul]
    · exact add_sub_cancel _ _
    · exact hθfin
  refine ⟨f, u + ∑' n, e n, hf,
    representsSobolevOn_of_underlying hf _ hrep, ?_⟩
  simpa only [add_sub_cancel_left] using norm_tsum_le_tsum_norm he

/-- Smooth approximation on an arbitrary open set with any positive full
Sobolev sum-norm tolerance. There are no boundary or boundedness hypotheses. -/
theorem exists_smoothSobolev_approximation (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω m p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Space d → 𝕜) (z : Sobolev 𝕜 Ω m p),
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ RepresentsSobolevOn f z ∧ ‖z - u‖ ≤ ε := by
  obtain ⟨θ, hθ, hθsum⟩ := exists_scalarTestPartition 𝕜 Ω
  let K (n : ℕ) : Compacts (Space d) := ⟨tsupport (θ n), (θ n).hasCompactSupport⟩
  have hinvpos (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  choose r hr hrle hrΩ using fun n => exists_supportRadius (K n) (θ n).tsupport_subset (hinvpos n)
  have hrt : Tendsto r atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero (fun n => (hr n).le) hrle hi
  have hbudget (n : ℕ) : 0 < ε / 2 / 2 ^ n := by positivity
  choose v w φ hv hw herr hs using fun n =>
    exists_localized_approximation hp (θ n) u (hr n) (hbudget n) (hrΩ n)
  have hφ : LocallyFinite (fun n => {x : Ω | (x : Space d) ∈ tsupport (φ n)}) :=
    (locallyFinite_add_closedBall (fun n => (θ n).tsupport_subset) hθ hrt).subset
      (fun n x hx => hs n hx)
  have he : Summable (fun n => ‖w n - v n‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (herr n).le)
      (summable_geometric_two' ε)
  obtain ⟨f, z, hf, hrep, hbound⟩ :=
    sobolev_glue_localized_errors u θ φ hθ hθsum hφ v w hv hw he
  refine ⟨f, z, hf, hrep, hbound.trans ?_⟩
  calc
    ∑' n, ‖w n - v n‖ ≤ ∑' n : ℕ, ε / 2 / 2 ^ n :=
      he.tsum_le_tsum (fun n => (herr n).le) (summable_geometric_two' ε)
    _ = ε := tsum_geometric_two' ε

/-- Meyers–Serrin density in the full derivative sum norm, for every open set
and either scalar field, also in dimension and derivative order zero. -/
theorem meyersSerrin_smoothDensity : MeyersSerrinExpected.SmoothDensity := by
  intro d 𝕜 _ Ω m p _ hp u
  have hpos (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  choose f v hf hrep hnorm using fun n => exists_smoothSobolev_approximation hp u (hpos n)
  have herror : Tendsto (fun n => ‖v n - u‖) atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero (fun n => norm_nonneg _) hnorm hi
  exact ⟨f, v, fun n => ⟨hf n, hrep n⟩,
    tendsto_iff_norm_sub_tendsto_zero.mpr herror,
    by simpa only [domainSobolevSumError_eq_norm] using herror⟩

end P102.U4
