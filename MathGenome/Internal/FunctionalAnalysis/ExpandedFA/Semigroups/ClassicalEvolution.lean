import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ClassicalEvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel

noncomputable section
open Filter Topology Set
open scoped NNReal ContDiff
namespace ExpandedFA.Semigroups.ClassicalEvolution
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
open ClassicalEvolutionSpec

/-- Lower powers have larger domains, with no assumption on the operator. -/
theorem power_domain_mono (B : Unbounded.Operator 𝕜 X X) {j k : ℕ}
    (hjk : j ≤ k) :
    (Unbounded.power B k).domain ≤ (Unbounded.power B j).domain := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    intro x hx
    exact ih hx.choose

/-- Moving the first application to the right retains the exact domain. -/
theorem power_shift (B : Unbounded.Operator 𝕜 X X) (n : ℕ)
    (x : (Unbounded.power B (n + 1)).domain) :
    ∃ hx : (x : X) ∈ B.domain,
      ∃ hy : B ⟨x, hx⟩ ∈ (Unbounded.power B n).domain,
        Unbounded.power B n ⟨B ⟨x, hx⟩, hy⟩ = Unbounded.power B (n + 1) x := by
  induction n with
  | zero =>
    exact ⟨x.2.choose_spec, Submodule.mem_top, rfl⟩
  | succ n ih =>
    let z : (Unbounded.power B (n + 1)).domain := ⟨x, x.2.choose⟩
    obtain ⟨hx, hy, he⟩ := ih z
    have hz : Unbounded.power B (n + 1) z ∈ B.domain := x.2.choose_spec
    have hy' : B ⟨x, hx⟩ ∈ (Unbounded.power B (n + 1)).domain :=
      ⟨hy, he.symm ▸ hz⟩
    refine ⟨hx, hy', ?_⟩
    change B ⟨Unbounded.power B n ⟨B ⟨x, hx⟩, _⟩, _⟩ =
      B ⟨Unbounded.power B (n + 1) z, _⟩
    congr 1
    exact Subtype.ext he

/-- All powers commute with the semigroup on their full domains. -/
theorem power_invariant_commutes (T : C0Semigroup 𝕜 X) (n : ℕ)
    (t : ℝ≥0) (x : (power T n).domain) :
    ∃ hx : T.operators t x ∈ (power T n).domain,
      power T n ⟨T.operators t x, hx⟩ = T.operators t (power T n x) := by
  induction n with
  | zero => exact ⟨Submodule.mem_top, rfl⟩
  | succ n ih =>
    let z : (power T n).domain := ⟨x, x.2.choose⟩
    obtain ⟨hz, he⟩ := ih z
    have hAx : power T n z ∈ (A T).domain := x.2.choose_spec
    have htAx := SemigroupGrowthAndGenerator.domain_invariant T t _ hAx
    have hx : T.operators t x ∈ (power T (n + 1)).domain :=
      ⟨hz, he.symm ▸ htAx⟩
    refine ⟨hx, ?_⟩
    change A T ⟨power T n ⟨T.operators t x, _⟩, _⟩ =
      T.operators t (A T ⟨power T n z, hAx⟩)
    have hsub : (⟨power T n ⟨T.operators t x, hz⟩, hx.choose_spec⟩ : (A T).domain) =
        ⟨T.operators t (power T n z), htAx⟩ := Subtype.ext he
    rw [hsub]
    exact SemigroupGrowthAndGenerator.generator_commutes T t ⟨power T n z, hAx⟩ htAx

/-- The orbit in the canonical graph norm of the j-th power. -/
def graphOrbit (T : C0Semigroup 𝕜 X) (j : ℕ) (x : (power T j).domain)
    (t : ℝ) : Unbounded.GraphDomain (power T j) :=
  (⟨T.operators t.toNNReal x, (power_invariant_commutes T j t.toNNReal x).choose⟩ :
    (power T j).domain)

@[simp] theorem graphOrbit_coe (T : C0Semigroup 𝕜 X) (j : ℕ)
    (x : (power T j).domain) (t : ℝ) :
    (Unbounded.GraphDomain.toDomain _ (graphOrbit T j x t) : X) =
      T.operators t.toNNReal x := rfl

@[simp] theorem graphOrbit_apply (T : C0Semigroup 𝕜 X) (j : ℕ)
    (x : (power T j).domain) (t : ℝ) :
    power T j (Unbounded.GraphDomain.toDomain _ (graphOrbit T j x t)) =
      T.operators t.toNNReal (power T j x) :=
  (power_invariant_commutes T j t.toNNReal x).choose_spec

/-- Convergence in the sum graph norm is exactly convergence of both graph
coordinates. Completeness or closedness of the operator is not needed. -/
theorem tendsto_graph_iff (B : Unbounded.Operator 𝕜 X X)
    {ι : Type*} {l : Filter ι} {f : ι → Unbounded.GraphDomain B}
    {y : Unbounded.GraphDomain B} :
    Tendsto f l (𝓝 y) ↔
      Tendsto (fun i => (Unbounded.GraphDomain.toDomain B (f i) : X)) l
        (𝓝 (Unbounded.GraphDomain.toDomain B y : X)) ∧
      Tendsto (fun i => B (Unbounded.GraphDomain.toDomain B (f i))) l
        (𝓝 (B (Unbounded.GraphDomain.toDomain B y))) := by
  have hnorm (z w : Unbounded.GraphDomain B) :
      dist z w = dist (Unbounded.GraphDomain.toDomain B z : X)
        (Unbounded.GraphDomain.toDomain B w : X) +
        dist (B (Unbounded.GraphDomain.toDomain B z))
          (B (Unbounded.GraphDomain.toDomain B w)) := by
    rw [dist_eq_norm, Unbounded.GraphDomain.norm_eq]
    simp only [dist_eq_norm, ← B.map_sub]
    rfl
  constructor
  · intro h
    constructor
    · apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.mp h ε hε] with i hi
      rw [hnorm] at hi
      exact lt_of_le_of_lt (le_add_of_nonneg_right dist_nonneg) hi
    · apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.mp h ε hε] with i hi
      rw [hnorm] at hi
      exact lt_of_le_of_lt (le_add_of_nonneg_left dist_nonneg) hi
  · rintro ⟨h₁, h₂⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp h₁ (ε / 2) (by positivity),
      Metric.tendsto_nhds.mp h₂ (ε / 2) (by positivity)] with i h₁ h₂
    rw [hnorm]
    linarith

local instance (B : Unbounded.Operator 𝕜 X X) :
    NormedSpace ℝ (Unbounded.GraphDomain B) := NormedSpace.restrictScalars ℝ 𝕜 _
local instance (B : Unbounded.Operator 𝕜 X X) :
    IsScalarTower ℝ 𝕜 (Unbounded.GraphDomain B) :=
  IsScalarTower.restrictScalars ℝ 𝕜 _

def graphFst (B : Unbounded.Operator 𝕜 X X) : Unbounded.GraphDomain B →ₗ[𝕜] X where
  toFun x := (Unbounded.GraphDomain.toDomain B x : X)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def graphSnd (B : Unbounded.Operator 𝕜 X X) : Unbounded.GraphDomain B →ₗ[𝕜] X where
  toFun x := B (Unbounded.GraphDomain.toDomain B x)
  map_add' _ _ := B.map_add _ _
  map_smul' _ _ := B.map_smul _ _

/-- Coordinate derivatives imply a derivative in the actual graph norm. -/
theorem hasDerivWithinAt_graph (B : Unbounded.Operator 𝕜 X X)
    {f : ℝ → Unbounded.GraphDomain B} {v : Unbounded.GraphDomain B}
    {s : Set ℝ} {t : ℝ}
    (h₁ : HasDerivWithinAt (fun r =>
      (Unbounded.GraphDomain.toDomain B (f r) : X))
      (Unbounded.GraphDomain.toDomain B v : X) s t)
    (h₂ : HasDerivWithinAt (fun r => B (Unbounded.GraphDomain.toDomain B (f r)))
      (B (Unbounded.GraphDomain.toDomain B v)) s t) :
    HasDerivWithinAt f v s t := by
  have hmap (L : Unbounded.GraphDomain B →ₗ[𝕜] X) (r : ℝ) :
      L (slope f t r) = slope (fun r => L (f r)) t r := by
    simp only [slope_def_module]
    rw [L.map_smul_of_tower, L.map_sub]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply (tendsto_graph_iff B).mpr
  constructor
  · change Tendsto (fun r => graphFst B (slope f t r)) _ _
    apply (hasDerivWithinAt_iff_tendsto_slope.mp h₁).congr'
    exact Eventually.of_forall (fun r => (hmap (graphFst B) r).symm)
  · change Tendsto (fun r => graphSnd B (slope f t r)) _ _
    apply (hasDerivWithinAt_iff_tendsto_slope.mp h₂).congr'
    exact Eventually.of_forall (fun r => (hmap (graphSnd B) r).symm)

theorem continuous_graphOrbit (T : C0Semigroup 𝕜 X) (j : ℕ)
    (x : (power T j).domain) : Continuous (graphOrbit T j x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (tendsto_graph_iff _).mpr
  simp only [graphOrbit_coe, graphOrbit_apply]
  exact ⟨(T.continuous_real_orbit x).continuousAt,
    (T.continuous_real_orbit (power T j x)).continuousAt⟩

/-- One derivative in D(A^j) uses exactly one additional power of A. -/
theorem graphOrbit_hasDeriv (T : C0Semigroup 𝕜 X) (j : ℕ)
    (x : (power T j).domain) (hx : (x : X) ∈ (A T).domain)
    (hy : A T ⟨x, hx⟩ ∈ (power T j).domain)
    (hz : power T j x ∈ (A T).domain)
    (hcomm : power T j ⟨A T ⟨x, hx⟩, hy⟩ = A T ⟨power T j x, hz⟩)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (graphOrbit T j x)
      (graphOrbit T j ⟨A T ⟨x, hx⟩, hy⟩ t) (Ici 0) t := by
  apply hasDerivWithinAt_graph
  · simpa only [graphOrbit_coe, generator] using T.hasDerivWithinAt_orbit ⟨x, hx⟩ t ht
  · simpa only [graphOrbit_apply, hcomm, generator] using
      T.hasDerivWithinAt_orbit ⟨power T j x, hz⟩ t ht

/-- Smoothness with an explicit number of spare generator powers. -/
theorem graphOrbit_contDiff (T : C0Semigroup 𝕜 X) (j m : ℕ)
    (x : (power T (j + m)).domain) :
    ContDiffOn ℝ m (graphOrbit T j
      ⟨x, power_domain_mono (A T) (Nat.le_add_right j m) x.2⟩) (Ici 0) := by
  induction m with
  | zero =>
    exact contDiffOn_zero.mpr (continuous_graphOrbit T j _).continuousOn
  | succ m ih =>
    let xbig : (power T (j + m + 1)).domain := ⟨x, by simpa only [Nat.add_assoc] using x.2⟩
    obtain ⟨hx, hy, _⟩ := power_shift (A T) (j + m) xbig
    let y : (power T (j + m)).domain := ⟨A T ⟨x, hx⟩, hy⟩
    let xsmall : (power T (j + 1)).domain :=
      ⟨x, power_domain_mono (A T) (by omega : j + 1 ≤ j + (m + 1)) x.2⟩
    obtain ⟨hx', hy', he⟩ := power_shift (A T) j xsmall
    have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
        (graphOrbit T j ⟨x, power_domain_mono (A T) (Nat.le_add_right j (m + 1)) x.2⟩)
        (graphOrbit T j ⟨y, power_domain_mono (A T) (Nat.le_add_right j m) y.2⟩ t)
        (Ici 0) t := by
      intro t ht
      exact graphOrbit_hasDeriv T j ⟨x, xsmall.2.choose⟩ hx' hy'
        xsmall.2.choose_spec he t ht
    rw [show (↑(m + 1) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
    refine ⟨fun t ht => (hd t ht).differentiableWithinAt, ?_, ?_⟩
    · simp
    · apply (ih y).congr
      intro t ht
      exact (hd t ht).derivWithin ((uniqueDiffOn_Ici 0) t ht)

/-- The homogeneous orbit is a classical solution, including its derivative at 0. -/
theorem classical_existence : ClassicalExistence (𝕜 := 𝕜) (X := X) := by
  intro T x
  refine ⟨by simp, ?_⟩
  let hu : ∀ t : Ici (0 : ℝ), T.operators (t : ℝ).toNNReal x ∈ (A T).domain :=
    fun t => SemigroupGrowthAndGenerator.domain_invariant T _ x x.2
  refine ⟨hu, ?_, ?_⟩
  · apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
    refine ⟨fun t ht => (T.hasDerivWithinAt_orbit x t ht).differentiableWithinAt, ?_⟩
    exact (T.continuous_real_orbit (A T x)).continuousOn.congr
      (fun t ht => (T.hasDerivWithinAt_orbit x t ht).derivWithin
        ((uniqueDiffOn_Ici 0) t ht))
  · intro t
    rw [SemigroupGrowthAndGenerator.generator_commutes T _ x _]
    exact T.hasDerivWithinAt_orbit x t t.2

/-- Full source regularity, including k = j and j = 0. -/
theorem higher_graph_regularity : HigherGraphRegularity (𝕜 := 𝕜) (X := X) := by
  intro T k j hjk x
  have he : j + (k - j) = k := Nat.add_sub_of_le hjk
  let y : (power T (j + (k - j))).domain := ⟨x, he.symm ▸ x.2⟩
  exact ⟨_, fun _ _ => rfl, graphOrbit_contDiff T j (k - j) y⟩

/-- Comparison with an arbitrary classical solution uses strong continuity and
local bounds, rather than differentiability in operator norm. -/
theorem solution_comparison_right (T : C0Semigroup 𝕜 X) (u : ℝ → X)
    (hu : ∀ s : Ici (0 : ℝ), u s ∈ (A T).domain)
    (hd : ∀ s : Ici (0 : ℝ),
      HasDerivWithinAt u (A T ⟨u s, hu s⟩) (Ici 0) s)
    (t : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) (hst : s < (t : ℝ)) :
    HasDerivWithinAt (fun r : ℝ => T.operators ((t : ℝ) - r).toNNReal (u r))
      0 (Ici s) s := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  let y : (A T).domain := ⟨u s, hu ⟨s, hs⟩⟩
  have hshift : Tendsto (fun r : ℝ => r - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert! ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => r) (𝓝[>] s) (𝓝 s)).sub_const s) using 1
      simp
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show s < r from hr)
  have hdu : HasDerivWithinAt u (A T y) (Ioi s) s :=
    (hd ⟨s, hs⟩).mono (fun r hr => hs.trans hr.le)
  have hlimu := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hdu
  have hlimT := (generator_has_limit T y).comp hshift
  have hz : Tendsto (fun r : ℝ => slope u s r - differenceQuotient T (r - s) (u s))
      (𝓝[>] s) (𝓝 0) := by
    simpa only [sub_self, Function.comp_def, differenceQuotient, y] using hlimu.sub hlimT
  obtain ⟨C, _, hC⟩ := T.bounded_on_interval t
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] s,
      ‖T.operators ((t : ℝ) - r).toNNReal‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply hC
    have hr0 : 0 ≤ r := hs.trans (show s ≤ r from hr.le)
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (show (t : ℝ) - r ≤ (t : ℝ) by linarith)
  have hzero := GeneratorDeterminesSemigroup.tendsto_apply_zero_of_bounded T
    (fun r : ℝ => ((t : ℝ) - r).toNNReal) hbound hz
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds] with r hrs hrt
  rw [slope_def_module, slope_def_module, T.differenceQuotient_real]
  rw [← smul_sub, (T.operators ((t : ℝ) - r).toNNReal).map_smul_of_tower]
  congr 1
  simp only [map_sub]
  have htime : ((t : ℝ) - r).toNNReal + (r - s).toNNReal =
      ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hrt.le),
      Real.coe_toNNReal _ (sub_nonneg.mpr hrs.le),
      Real.coe_toNNReal _ (sub_nonneg.mpr hst.le)]
    ring
  rw [← T.add_apply, htime]
  abel

/-- Every classical solution agrees with the orbit on the entire time axis. -/
theorem classical_uniqueness : ClassicalUniqueness (𝕜 := 𝕜) (X := X) := by
  intro T x u hsol t ht
  obtain ⟨h0, hu, hc, hd⟩ := hsol
  let τ : ℝ≥0 := ⟨t, ht⟩
  have hcont : ContinuousOn (fun s : ℝ =>
      T.operators ((τ : ℝ) - s).toNNReal (u s)) (Icc 0 t) := by
    intro s hs
    apply GeneratorDeterminesSemigroup.tendsto_apply T
    · exact (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · exact (hc.continuousOn s hs.1).mono (fun r hr => hr.1)
  have hder : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt
      (fun r : ℝ => T.operators ((τ : ℝ) - r).toNNReal (u r)) 0 (Ici s) s := by
    intro s hs
    exact solution_comparison_right T u hu hd τ s hs.1 hs.2
  have heq := constant_of_has_deriv_right_zero hcont hder t ⟨ht, le_rfl⟩
  change T.operators (t - t).toNNReal (u t) =
    T.operators (t - 0).toNNReal (u 0) at heq
  simpa only [sub_self, Real.toNNReal_zero, C0Semigroup.zero_apply,
    sub_zero, h0] using heq

end ExpandedFA.Semigroups.ClassicalEvolution
