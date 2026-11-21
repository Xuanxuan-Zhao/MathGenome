import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.SymmetricCoefficients
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereRationality
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace D12Complex.SymmetricCoefficients
open SymmetricCoefficientData

abbrev parameter : Specs.D12Complex.Ch21.SymmetricCoefficients.parameter_type :=
  SymmetricCoefficientData.parameter
abbrev coefficient : Specs.D12Complex.Ch21.SymmetricCoefficients.coefficient_type :=
  SymmetricCoefficientData.coefficient
abbrev LocallyEnumerated : Specs.D12Complex.Ch21.SymmetricCoefficients.LocallyEnumerated_type :=
  SymmetricCoefficientData.LocallyEnumerated
abbrev AnalyticMultiset : Specs.D12Complex.Ch21.SymmetricCoefficients.AnalyticMultiset_type :=
  SymmetricCoefficientData.AnalyticMultiset
abbrev CyclicPowerGrowth : Specs.D12Complex.Ch21.SymmetricCoefficients.CyclicPowerGrowth_type :=
  SymmetricCoefficientData.CyclicPowerGrowth

@[simp] theorem parameter_finite (a u : ℂ) :
    parameter (sphereFinite a) u = sphereFinite (a + u) := by
  simp [parameter, SymmetricCoefficientData.parameter, sphereFinite, sphereInfty,
    finiteCoordinate]

@[simp] theorem parameter_infty (u : ℂ) :
    parameter sphereInfty u = infinityParametrization u := by
  simp [parameter, SymmetricCoefficientData.parameter]

@[simp] theorem parameter_zero (p : RiemannSphere) : parameter p 0 = p := by
  induction p using OnePoint.rec with
  | infty => change parameter sphereInfty 0 = sphereInfty
             simp [infinityParametrization]
  | coe a => simpa [sphereFinite] using parameter_finite a 0

theorem product_expansion : Specs.D12Complex.Ch21.SymmetricCoefficients.product_expansion_type := by
  intro B p
  convert Multiset.prod_X_sub_X_eq_sum_esymm (B p) using 1
  apply Finset.sum_congr rfl
  intro k hk
  simp [SymmetricCoefficientData.coefficient, Polynomial.C_mul,
    Polynomial.C_pow, mul_assoc]

/-- Finite sums and products of the local branches are weakly holomorphic. -/
theorem enumeration_holomorphic {d : ℕ} {U : Set ℂ} {f : Fin d → ℂ → ℂ}
    (hf : ∀ i, HolomorphicOn U (f i)) (hU : IsOpen U) (k : ℕ) :
    HolomorphicOn U (fun u => (-1 : ℂ)^k *
      (Finset.univ.val.map (fun i => f i u)).esymm k) := by
  classical
  simp_rw [Finset.esymm_map_val]
  refine ⟨hU, fun a ha => ?_⟩
  apply DifferentiableAt.const_mul
  exact DifferentiableAt.fun_sum fun s hs =>
    DifferentiableAt.fun_finsetProd fun i hi => (hf i).2 a ha

theorem holomorphic_coefficients :
    Specs.D12Complex.Ch21.SymmetricCoefficients.holomorphic_coefficients_type := by
  intro d B p hp k
  obtain ⟨r, hr, f, hf, he⟩ := hp
  refine ⟨r, hr, isOpen_ball, fun a ha => ?_⟩
  apply ((enumeration_holomorphic hf isOpen_ball k).2 a ha).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ha] with u hu
  simp only [SymmetricCoefficientData.coefficient, he u hu]

/-- A safe integer exponent avoids any use of fractional powers: for |t|≤1
and h≥1, |t^h|≤|t|. -/
theorem cyclic_value_bound {t u v : ℂ} {h n : ℕ} {C : ℝ}
    (hh : 1 ≤ h) (ht : ‖t‖ ≤ 1) (htu : t^h = u)
    (hu : 0 < ‖u‖) (hC : 0 ≤ C)
    (hv : ‖v‖ ≤ C * (‖t‖^n)⁻¹) :
    ‖v‖ ≤ C * (‖u‖^n)⁻¹ := by
  have hnorm : ‖u‖ ≤ ‖t‖ := by
    rw [← htu, norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) ht (by omega)
  exact hv.trans (mul_le_mul_of_nonneg_left
    (inv_anti₀ (pow_pos hu _) (pow_le_pow_left₀ (norm_nonneg _) hnorm _)) hC)

theorem common_power_bound :
    Specs.D12Complex.Ch21.SymmetricCoefficients.common_power_bound_type := by
  classical
  intro B p hp
  obtain ⟨m, h, W, C, N, δ, ρ, hδ, hδ1, hρ, hdata, hcover⟩ := hp
  let A : ℝ := 1 + ∑ i, C i
  let M : ℕ := ∑ i, N i
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hdata i).2.1.le
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨A, M, min ρ 1, hA, lt_min hρ zero_lt_one, min_le_right _ _, ?_⟩
  intro u hu v hv
  have hu0 : 0 < ‖u‖ := by simpa only [sub_zero] using hu.1
  have huρ : ‖u‖ < ρ := lt_of_lt_of_le (by simpa only [sub_zero] using hu.2) (min_le_left _ _)
  have hu1 : ‖u‖ ≤ 1 := le_of_lt (lt_of_lt_of_le
    (by simpa only [sub_zero] using hu.2) (min_le_right _ _))
  obtain ⟨i, t, ht, htu, htv⟩ := hcover u ⟨by simpa using hu0, by simpa using huρ⟩ v hv
  have hti : ‖t‖ ≤ 1 := le_trans (le_of_lt (by simpa only [sub_zero] using ht.2)) hδ1
  have hv' : ‖v‖ ≤ C i * (‖u‖ ^ N i)⁻¹ :=
    cyclic_value_bound (hdata i).1 hti htu hu0 (hdata i).2.1.le
      (by simpa [htv] using (hdata i).2.2.2 t ht)
  have hNi : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have hCi : C i ≤ A := by
    have hi : C i ≤ ∑ j, C j :=
      Finset.single_le_sum (fun j _ => (hdata j).2.1.le) (Finset.mem_univ i)
    dsimp [A]; linarith
  apply hv'.trans
  apply mul_le_mul hCi _ (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)) hA.le
  exact inv_anti₀ (pow_pos hu0 _) (pow_le_pow_of_le_one (norm_nonneg _) hu1 hNi)

/-- A quantitative estimate for each elementary symmetric function. -/
theorem norm_esymm_le {s : Multiset ℂ} {M : ℝ} (_hM : 0 ≤ M)
    (hs : ∀ v ∈ s, ‖v‖ ≤ M) (k : ℕ) :
    ‖s.esymm k‖ ≤ (s.card.choose k : ℝ) * M^k := by
  have ht (t : Multiset ℂ) (ht : t ∈ s.powersetCard k) : ‖t.prod‖ ≤ M^k := by
    rw [Multiset.norm_prod]
    calc
      (t.map norm).prod ≤ (t.map fun _ => M).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => norm_nonneg v)
          (fun v hv => hs v (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hv))
      _ = M^k := by simp [(Multiset.mem_powersetCard.mp ht).2]
  unfold Multiset.esymm
  apply (norm_multiset_sum_le _).trans
  have hb := Multiset.sum_le_card_nsmul
    (((s.powersetCard k).map Multiset.prod).map norm) (M^k) (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨t, ht', rfl⟩ := Multiset.mem_map.mp hv
      exact ht t ht')
  simpa only [Multiset.card_map, Multiset.card_powersetCard, nsmul_eq_mul] using hb

theorem norm_coefficient_le {B : RiemannSphere → Multiset ℂ} {p : RiemannSphere}
    {d : ℕ} (hd : (B p).card = d) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ v ∈ B p, ‖v‖ ≤ M) (k : ℕ) :
    ‖coefficient B k p‖ ≤ (d.choose k : ℝ) * M^k := by
  simpa [coefficient, SymmetricCoefficientData.coefficient, norm_mul, norm_pow, hd]
    using norm_esymm_le hM hs k

/-- Every centered coordinate is injective, including the reciprocal chart. -/
theorem parameter_injective (p : RiemannSphere) : Function.Injective (parameter p) := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · apply Function.LeftInverse.injective (g := infinityCoordinate)
    intro u
    rw [parameter_infty]
    change infinityChart (infinityChart.symm u) = u
    exact infinityChart.right_inv (mem_univ u)
  · intro u v huv
    simp only [parameter_finite] at huv
    exact add_left_cancel (sphereFinite_injective huv)

/-- Finite exceptional sets leave a punctured ordinary neighborhood in every chart. -/
theorem eventually_regular (E : Finset RiemannSphere) (p : RiemannSphere) :
    ∀ᶠ u in 𝓝[≠] (0 : ℂ), parameter p u ∉ E :=
  ((parameter_injective p).tendsto_cofinite.eventually E.eventually_cofinite_notMem).filter_mono
    (nhdsNE_le_cofinite 0)

/-- Translate ordinary local holomorphy from the centered chart to z itself. -/
theorem differentiable_finite {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (k : ℕ) {a : ℂ} (ha : sphereFinite a ∉ E) :
    DifferentiableAt ℂ (fun z => coefficient B k (sphereFinite z)) a := by
  obtain ⟨r, hr, hf⟩ := holomorphic_coefficients d B (sphereFinite a) (hB.2 _ ha).2 k
  have h0 : DifferentiableAt ℂ (fun u => coefficient B k (parameter (sphereFinite a) u))
      (a-a) := by simpa using hf.2 0 (mem_ball_self hr)
  have h := h0.comp a (f := fun z : ℂ => z-a) (differentiableAt_id.sub_const a)
  convert! h using 1; simp [Function.comp_def, parameter_finite]

/-- Away from the center, source coordinates reduce to ordinary plane maps. -/
theorem differentiable_parameter {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (k : ℕ) (p : RiemannSphere) {u : ℂ} (hu : u ≠ 0)
    (hpu : parameter p u ∉ E) :
    DifferentiableAt ℂ (fun v => coefficient B k (parameter p v)) u := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · have hfu := differentiable_finite hB k (a := u⁻¹) (by
      simpa only [parameter_infty, infinityParametrization_ne_zero _ hu] using hpu)
    apply (hfu.comp u (differentiableAt_id.inv hu)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hu] with v hv
    simp only [parameter_infty, infinityParametrization_ne_zero _ hv, Function.comp_apply]
  · have hfa := differentiable_finite hB k (a := a+u)
      (by simpa only [parameter_finite] using hpu)
    have ht : DifferentiableAt ℂ (fun v : ℂ => a+v) u :=
      (differentiableAt_const a).add differentiableAt_id
    convert! hfa.comp u ht using 1; simp [Function.comp_def, parameter_finite]


/-- The only possible nonordinary point of a sufficiently small chart is its center. -/
theorem isolated_coefficient {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (k : ℕ) (p : RiemannSphere) :
    IsolatedSingularityAt (fun u => coefficient B k (parameter p u)) 0 := by
  apply SingularityGrowth.isolated_of_eventually_differentiable
  filter_upwards [eventually_regular E p, self_mem_nhdsWithin] with u hu hu0
  exact differentiable_parameter hB k p hu0 hu

/-- Growth of the branches bounds every symmetric coefficient. -/
theorem meromorphic_coefficient {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (hg : ∀ p ∈ E, CyclicPowerGrowth B p) (k : ℕ) (p : RiemannSphere) :
    MeromorphicAt (fun u => coefficient B k (parameter p u)) 0 := by
  classical
  by_cases hp : p ∈ E
  · obtain ⟨C, N, r, hC, hr, hr1, hb⟩ := common_power_bound B p (hg p hp)
    have hi := isolated_coefficient hB k p
    have ho : (fun u => coefficient B k (parameter p u)) =O[𝓝[≠] (0 : ℂ)]
        (fun u => ((u-0)^(N*k))⁻¹) := by
      apply Asymptotics.IsBigO.of_bound ((d.choose k : ℝ) * C^k)
      filter_upwards [SingularityGrowth.puncturedDisk_mem hr, eventually_regular E p] with u hu hreg
      have hbound := norm_coefficient_le (hB.2 _ hreg).1
        (mul_nonneg hC.le (inv_nonneg.mpr (pow_nonneg (norm_nonneg u) N))) (hb u hu) k
      simpa only [sub_zero, norm_inv, norm_pow, mul_pow, inv_pow, ← pow_mul, mul_assoc]
        using hbound
    exact ((SingularityGrowth.atMost_iff_order hi (N*k)).mp
      ((SingularityGrowth.bigO_iff _ _ hi (N*k)).mp ho)).1
  · obtain ⟨r, hr, hf⟩ := holomorphic_coefficients d B p (hB.2 _ hp).2 k
    exact ((LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
      ⟨ball 0 r, mem_ball_self hr, hf⟩).meromorphicAt

/-- The plane expression is holomorphic away from the given exceptional set. -/
theorem analytic_finite {E : Finset RiemannSphere} {d : ℕ}
    {B : RiemannSphere → Multiset ℂ} (hB : AnalyticMultiset E d B)
    (k : ℕ) {a : ℂ} (ha : sphereFinite a ∉ E) :
    AnalyticAt ℂ (fun z => coefficient B k (sphereFinite z)) a := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he : ∀ᶠ z in 𝓝 a, sphereFinite z ∉ E := by
    apply (E.finite_toSet.isClosed.preimage continuous_sphereFinite).isOpen_compl.mem_nhds
    exact ha
  filter_upwards [he] with z hz
  exact differentiable_finite hB k hz

/-- A raw plane meromorphic expression with finitely many exceptional ordinary
points and a meromorphic reciprocal germ is rational, with all cancellations
restored. This uses the accepted pole-clearing and entire-at-infinity results. -/
theorem rational_of_meromorphic (f : ℂ → ℂ) (hf : MeromorphicOn f univ)
    (hbad : Set.Finite {a | ¬ AnalyticAt ℂ f a})
    (hI : MeromorphicAt (reciprocalPullback f) 0) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ a : ℂ, LocalQuotientsArithmetic.fill f a =
        LocalQuotientsArithmetic.fill (fun z => P.eval z / Q.eval z) a) ∧
      LocalQuotientsArithmetic.fill (reciprocalPullback f) 0 =
        LocalQuotientsArithmetic.fill (fun u => P.eval u⁻¹ / Q.eval u⁻¹) 0 := by
  let F := LocalQuotientsArithmetic.fill f
  have hF : ScalarMeromorphicOn univ F :=
    LocalQuotientsArithmetic.scalarMeromorphicOn_fill univ isOpen_univ f hf
  have hpoles : Set.Finite {a | F a = sphereInfty} := by
    apply hbad.subset
    intro a ha han
    have he := LocalQuotientsArithmetic.fill_of_analyticAt han
    exact (OnePoint.coe_ne_infty (f a)) (he.symm.trans ha)
  obtain ⟨Q, hQ, hg⟩ := SphereRationality.clear_finite_poles F hF hpoles
  have hrec : reciprocalPullback (scalarFinitePart F) =ᶠ[𝓝[≠] (0 : ℂ)]
      reciprocalPullback f := by
    have hgood : ∀ᶠ z in (cofinite : Filter ℂ), AnalyticAt ℂ f z := by
      simpa only [Set.mem_ofPred_eq, not_not] using hbad.eventually_cofinite_notMem
    have he : ∀ᶠ u in (cofinite : Filter ℂ), AnalyticAt ℂ f u⁻¹ :=
      inv_injective.tendsto_cofinite.eventually hgood
    filter_upwards [he.filter_mono (nhdsNE_le_cofinite (0 : ℂ))] with u hu
    simp only [reciprocalPullback, scalarFinitePart, F,
      LocalQuotientsArithmetic.fill_of_analyticAt hu, finiteCoordinate_sphereFinite]
  have hgm : MeromorphicAt (reciprocalPullback
      (fun z => Q.eval z * scalarFinitePart F z)) 0 := by
    exact (SphereRationality.polynomial_reciprocal_meromorphic Q).fun_mul (hI.congr hrec.symm)
  obtain ⟨P, hP⟩ := SphereRationality.polynomial_of_entire_reciprocal_meromorphic _ hg hgm
  have heq (z : ℂ) (hz : Q.eval z ≠ 0) :
      scalarFinitePart F z = P.eval z / Q.eval z := by
    apply (eq_div_iff hz).mpr
    rw [mul_comm]
    exact hP z
  refine ⟨P, Q, hQ, ?_, ?_⟩
  · intro a
    calc
      LocalQuotientsArithmetic.fill f a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a :=
        LocalQuotientsArithmetic.scalar_eq_fill univ F hF (mem_univ a)
      _ = _ := LocalQuotientsArithmetic.fill_congr _ _ a (by
        filter_upwards [(Polynomial.eventually_eval_ne_zero_cofinite hQ).filter_mono
          (nhdsNE_le_cofinite a)] with z hz
        exact heq z hz)
  · apply LocalQuotientsArithmetic.fill_congr
    apply hrec.symm.trans
    have hne : ∀ᶠ u in (cofinite : Filter ℂ), Q.eval u⁻¹ ≠ 0 :=
      inv_injective.tendsto_cofinite.eventually (Polynomial.eventually_eval_ne_zero_cofinite hQ)
    filter_upwards [hne.filter_mono (nhdsNE_le_cofinite (0 : ℂ))] with u hu
    exact heq u⁻¹ hu

/-- Each symmetric coefficient is holomorphic off E, meromorphic at every
missing point (also infinity), and the germ of one rational function. -/
theorem rational_coefficients :
    Specs.D12Complex.Ch21.SymmetricCoefficients.rational_coefficients_type := by
  classical
  intro E d B hB hg k
  refine ⟨fun p hp => holomorphic_coefficients d B p (hB.2 p hp).2 k,
    meromorphic_coefficient hB hg k, ?_⟩
  let f : ℂ → ℂ := fun z => coefficient B k (sphereFinite z)
  have hf : MeromorphicOn f univ := by
    intro a _
    have hm := meromorphic_coefficient hB hg k (sphereFinite a)
    have ht : MeromorphicAt (fun u : ℂ => f (u+a)) 0 := by
      simpa only [parameter_finite, add_comm, f] using hm
    simpa only [zero_add] using meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mp ht
  have hbad : Set.Finite {a | ¬ AnalyticAt ℂ f a} := by
    apply (E.finite_toSet.preimage sphereFinite_injective.injOn).subset
    intro a ha
    by_contra hn
    exact ha (analytic_finite hB k hn)
  have hrec : (fun u => coefficient B k (parameter sphereInfty u)) =ᶠ[𝓝[≠] (0 : ℂ)]
      reciprocalPullback f := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [parameter_infty, infinityParametrization_ne_zero _ hu, reciprocalPullback, f]
  have hI := (meromorphic_coefficient hB hg k sphereInfty).congr hrec
  obtain ⟨P, Q, hQ, he, hi⟩ := rational_of_meromorphic f hf hbad hI
  exact ⟨P, Q, hQ, he, (LocalQuotientsArithmetic.fill_congr _ _ 0 hrec).trans hi⟩

/-- The rational functions agree with the actual regular coefficient values;
the filling operation in the main theorem does not lose those values. -/
theorem rational_values :
    Specs.D12Complex.Ch21.SymmetricCoefficients.rational_values_type := by
  intro E d B hB hg k
  obtain ⟨_, _, P, Q, hQ, he, hi⟩ := rational_coefficients E d B hB hg k
  refine ⟨P, Q, hQ, fun a ha => ?_, fun hInfinity => ?_⟩
  · exact (LocalQuotientsArithmetic.fill_of_analyticAt (analytic_finite hB k ha)).symm.trans (he a)
  · obtain ⟨r, hr, hf⟩ := holomorphic_coefficients d B sphereInfty (hB.2 _ hInfinity).2 k
    have han := (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
      ⟨ball 0 r, mem_ball_self hr, hf⟩
    have hv := LocalQuotientsArithmetic.fill_of_analyticAt han
    calc
      sphereFinite (coefficient B k sphereInfty) =
          LocalQuotientsArithmetic.fill (fun u => coefficient B k (parameter sphereInfty u)) 0 := by
        simpa only [parameter_zero] using hv.symm
      _ = _ := hi

end D12Complex.SymmetricCoefficients
