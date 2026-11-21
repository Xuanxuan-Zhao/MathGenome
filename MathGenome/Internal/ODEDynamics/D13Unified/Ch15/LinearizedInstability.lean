import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LinearizedInstability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.AdaptedNorm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Module Set Filter
open scoped Topology
namespace D13Unified.Ch15.LinearizedInstability

/-- Expansion in an invariant cone forces a finite first exit from a ball.
The hypotheses concern only points inside that ball. -/
lemma firstExit_of_cone {E : Type} [NormedAddCommGroup E]
    (G : E → E) (U S : E → ℝ) (r c D : ℝ)
    (hc : 1 < c) (hD : 0 < D)
    (hbound : ∀ v, U v ≤ D * ‖v‖)
    (hstep : ∀ v, ‖v‖ < r → S v ≤ U v →
      S (G v) ≤ U (G v) ∧ c * U v ≤ U (G v))
    (x : E) (hx : ‖x‖ < r) (hcone : S x ≤ U x) (hpos : 0 < U x) :
    ∃ N : ℕ, 0 < N ∧ r ≤ ‖G^[N] x‖ ∧ ∀ n < N, ‖G^[n] x‖ < r := by
  have hexit : ∃ n : ℕ, r ≤ ‖G^[n] x‖ := by
    by_contra! hstay
    have hiter : ∀ n : ℕ, S (G^[n] x) ≤ U (G^[n] x) ∧
        c ^ n * U x ≤ U (G^[n] x) := by
      intro n
      induction n with
      | zero => simpa using And.intro hcone (le_refl (U x))
      | succ n ih =>
        obtain ⟨hcone', hgrow⟩ := hstep (G^[n] x) (hstay n) ih.1
        rw [Function.iterate_succ_apply']
        refine ⟨hcone', ?_⟩
        calc
          c ^ (n + 1) * U x = c * (c ^ n * U x) := by ring
          _ ≤ c * U (G^[n] x) := mul_le_mul_of_nonneg_left ih.2 (by linarith)
          _ ≤ U (G (G^[n] x)) := hgrow
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D * r / U x) hc
    have hlarge : D * r < c ^ n * U x := (div_lt_iff₀ hpos).mp hn
    have hsmall := (hiter n).2.trans (hbound (G^[n] x))
    have := mul_lt_mul_of_pos_left (hstay n) hD
    linarith
  let N := Nat.find hexit
  have hN : r ≤ ‖G^[N] x‖ := Nat.find_spec hexit
  have hprior : ∀ n < N, ‖G^[n] x‖ < r := by
    intro n hn
    exact lt_of_not_ge (Nat.find_min hexit hn)
  refine ⟨N, ?_, hN, hprior⟩
  by_contra! hzero
  have : N = 0 := Nat.eq_zero_of_le_zero hzero
  have hN0 : r ≤ ‖x‖ := by simpa [this] using hN
  exact hx.not_ge hN0

/-- The two error coordinates preserve the cone and expand its first
coordinate when the nonlinear remainder is sufficiently small. -/
lemma cone_step {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (data : ConeData A) (G : E → E) (η : ℝ)
    (hη : 0 ≤ η) (hgap : data.b + 2 * η ≤ data.a - 2 * η)
    (v : E) (hcone : data.complementary v ≤ data.unstable v)
    (hu : data.unstable (G v - A v) ≤ η * (data.unstable v + data.complementary v))
    (hs : data.complementary (G v - A v) ≤ η * (data.unstable v + data.complementary v)) :
    data.complementary (G v) ≤ data.unstable (G v) ∧
      (data.a - 2 * η) * data.unstable v ≤ data.unstable (G v) := by
  have herru : data.unstable (G v - A v) ≤ 2 * η * data.unstable v := by
    nlinarith
  have herrs : data.complementary (G v - A v) ≤ 2 * η * data.unstable v := by
    nlinarith
  have htriangle : data.unstable (A v) ≤
      data.unstable (G v) + data.unstable (G v - A v) := by
    have heq : G v - (G v - A v) = A v := by abel
    simpa only [heq] using
      (map_sub_le_add data.unstable (G v) (G v - A v))
  have hexpand := data.expands v
  have hgrow : (data.a - 2 * η) * data.unstable v ≤ data.unstable (G v) := by
    nlinarith
  have hcomp : data.complementary (G v) ≤
      data.complementary (A v) + data.complementary (G v - A v) := by
    simpa using (map_add_le_add data.complementary (A v) (G v - A v))
  have hcontrol := data.controls v
  have hupper : data.complementary (G v) ≤
      (data.b + 2 * η) * data.unstable v := by
    nlinarith [mul_le_mul_of_nonneg_left hcone data.b_nonneg]
  exact ⟨hupper.trans ((mul_le_mul_of_nonneg_right hgap
    (apply_nonneg data.unstable v)).trans hgrow), hgrow⟩

/-- Differentiability controls both projected remainder coordinates, in the
sum of the two projected norms. -/
lemma remainder_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (data : ConeData A) (F : E → E) (p : E)
    (hfix : F p = p) (hF : HasFDerivAt F A p) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : E, ‖v‖ < r →
      data.unstable (F (p + v) - p - A v) ≤
        η * (data.unstable v + data.complementary v) ∧
      data.complementary (F (p + v) - p - A v) ≤
        η * (data.unstable v + data.complementary v) := by
  have hk : 0 < η / (data.D * data.C) := div_pos hη (mul_pos data.D_pos data.C_pos)
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp (hF.isLittleO.bound hk)
  refine ⟨r, hr, fun v hv => ?_⟩
  have hd : dist (p + v) p < r := by simpa [dist_eq_norm] using hv
  have he : ‖F (p + v) - p - A v‖ ≤ η / (data.D * data.C) * ‖v‖ := by
    simpa [hfix] using hrem hd
  have hb := data.upper (F (p + v) - p - A v)
  have hl := data.lower v
  have he' := mul_le_mul_of_nonneg_left he data.D_pos.le
  have hl' := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ η / (data.D * data.C))
  have hsum : data.unstable (F (p + v) - p - A v) +
      data.complementary (F (p + v) - p - A v) ≤
      η * (data.unstable v + data.complementary v) := by
    calc
      _ ≤ data.D * ‖F (p + v) - p - A v‖ := hb
      _ ≤ data.D * (η / (data.D * data.C) * ‖v‖) := he'
      _ ≤ data.D * (η / (data.D * data.C) *
          (data.C * (data.unstable v + data.complementary v))) :=
        mul_le_mul_of_nonneg_left hl' data.D_pos.le
      _ = _ := by field_simp [data.C_pos.ne', data.D_pos.ne']
  constructor <;> linarith [apply_nonneg data.unstable (F (p + v) - p - A v),
    apply_nonneg data.complementary (F (p + v) - p - A v)]

/-- The pure expanding direction has arbitrarily small nonzero multiples. -/
lemma small_cone_point {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (data : ConeData A) (r : ℝ) (hr : 0 < r) :
    ∃ v : E, ‖v‖ < r ∧ data.complementary v ≤ data.unstable v ∧
      0 < data.unstable v := by
  let t : ℝ := r / (2 * (‖data.direction‖ + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htnorm : t * ‖data.direction‖ < r := by
    have ht' : t * (2 * (‖data.direction‖ + 1)) = r :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg data.direction]
  refine ⟨t • data.direction, ?_, ?_, ?_⟩
  · simpa [norm_smul, Real.norm_of_nonneg ht.le] using htnorm
  · simp only [map_smul_eq_mul, data.direction_complementary, mul_zero]
    exact mul_nonneg (norm_nonneg t) (apply_nonneg data.unstable _)
  · simp only [map_smul_eq_mul, Real.norm_of_nonneg ht.le]
    exact mul_pos ht data.direction_pos

/-- Translation of all natural iterates, without any domain or invariance
assumption. Its later use is limited to the finite first-exit segment. -/
lemma translated_iterate {E : Type} [AddCommGroup E] (F : E → E)
    (p v : E) (n : ℕ) :
    (fun w => F (p + w) - p)^[n] v = F^[n] (p + v) - p := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]

/-- The dynamical part of the instability proof. Only differentiability at
the fixed point is needed after the linear cone data have been established. -/
theorem instability_of_coneData {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (data : ConeData A) (F : E → E) (V : Set E) (p : E)
    (hV : IsOpen V) (hp : p ∈ V) (hfix : F p = p) (hF : HasFDerivAt F A p) :
    LocallyUnstable F V p := by
  let η := min ((data.a - 1) / 4) ((data.a - data.b) / 8)
  have hη : 0 < η := lt_min (by linarith [data.a_gt_one]) (by linarith [data.gap])
  have hηa : η ≤ (data.a - 1) / 4 := min_le_left _ _
  have hηb : η ≤ (data.a - data.b) / 8 := min_le_right _ _
  have hc : 1 < data.a - 2 * η := by linarith [data.a_gt_one]
  have hgap : data.b + 2 * η ≤ data.a - 2 * η := by linarith [data.gap]
  obtain ⟨r₀, hr₀, hrem⟩ := remainder_small data F p hfix hF η hη
  obtain ⟨rV, hrV, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
  let ε := min r₀ rV
  have hε : 0 < ε := lt_min hr₀ hrV
  have hε₀ : ε ≤ r₀ := min_le_left _ _
  have hεV : ε ≤ rV := min_le_right _ _
  have hsub : Metric.ball p ε ⊆ V := (Metric.ball_subset_ball hεV).trans hball
  refine ⟨ε, hε, hsub, fun δ hδ => ?_⟩
  obtain ⟨v, hv, hcone, hpos⟩ := small_cone_point data (min δ ε) (lt_min hδ hε)
  have hvδ := lt_of_lt_of_le hv (min_le_left δ ε)
  have hvε := lt_of_lt_of_le hv (min_le_right δ ε)
  let G := fun w => F (p + w) - p
  have hstep : ∀ w, ‖w‖ < ε → data.complementary w ≤ data.unstable w →
      data.complementary (G w) ≤ data.unstable (G w) ∧
        (data.a - 2 * η) * data.unstable w ≤ data.unstable (G w) := by
    intro w hw hcw
    obtain ⟨hu, hs⟩ := hrem w (hw.trans_le hε₀)
    exact cone_step data G η hη.le hgap w hcw hu hs
  have hbound : ∀ w, data.unstable w ≤ data.D * ‖w‖ := by
    intro w
    exact (le_add_of_nonneg_right (apply_nonneg data.complementary w)).trans (data.upper w)
  obtain ⟨N, hN, hexit, hprior⟩ := firstExit_of_cone G data.unstable data.complementary
    ε (data.a - 2 * η) data.D hc data.D_pos hbound hstep v hvε hcone hpos
  have hmem : p + v ∈ Metric.ball p ε := by simpa [Metric.mem_ball, dist_eq_norm] using hvε
  refine ⟨p + v, hsub hmem, by simpa using hvδ, N, hN, ?_, ?_⟩
  · simpa only [G, translated_iterate] using hexit
  · intro n hn
    have hnorm : ‖F^[n] (p + v) - p‖ < ε := by
      simpa only [G, translated_iterate] using hprior n hn
    exact ⟨hnorm, hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hnorm)⟩

/-- The first-exit segment depends only on values of the map on its domain.
This justifies using an arbitrary total representative of a local map. -/
lemma FirstExit.congr {E : Type} [NormedAddCommGroup E]
    {F G : E → E} {V : Set E} {p x : E} {ε : ℝ} {N : ℕ}
    (h : FirstExit F V p x ε N) (hFG : Set.EqOn F G V) :
    FirstExit G V p x ε N := by
  obtain ⟨hN, hexit, hprior⟩ := h
  have heq : ∀ n : ℕ, n ≤ N → F^[n] x = G^[n] x := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [hFG (hprior n (Nat.lt_of_succ_le hn)).2, ih (Nat.le_of_succ_le hn)]
  refine ⟨hN, ?_, fun n hn => ?_⟩
  · rw [← heq N le_rfl]
    exact hexit
  · rw [← heq n hn.le]
    exact hprior n hn

lemma LocallyUnstable.congr {E : Type} [NormedAddCommGroup E]
    {F G : E → E} {V : Set E} {p : E}
    (h : LocallyUnstable F V p) (hFG : Set.EqOn F G V) :
    LocallyUnstable G V p := by
  obtain ⟨ε, hε, hball, hperturb⟩ := h
  refine ⟨ε, hε, hball, fun δ hδ => ?_⟩
  obtain ⟨x, hxV, hxδ, N, hN⟩ := hperturb δ hδ
  exact ⟨x, hxV, hxδ, N, hN.congr hFG⟩

/-- Compatibility with the canonical metric definition of Lyapunov stability. -/
lemma LocallyUnstable.not_lyapunovStable {E : Type} [NormedAddCommGroup E]
    {F : E → E} {V : Set E} {p : E} (h : LocallyUnstable F V p) :
    ¬ DiscreteDefinitions.LyapunovStable F p := by
  intro hstable
  obtain ⟨ε, hε, _, hperturb⟩ := h
  obtain ⟨δ, hδ, hstay⟩ := hstable ε hε
  obtain ⟨x, _, hxδ, N, hN⟩ := hperturb δ hδ
  have hnear : dist x p < δ := by simpa only [dist_eq_norm] using hxδ
  have hsmall : ‖F^[N] x - p‖ < ε := by
    simpa only [dist_eq_norm] using hstay x hnear N
  exact (not_lt_of_ge hN.2.1) hsmall

/-- Sum of the full generalized eigenspaces selected by a set of eigenvalues. -/
def spectralSubspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (s : Set ℂ) : Submodule ℂ V :=
  ⨆ z ∈ s, T.maxGenEigenspace z

lemma spectralSubspace_invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (s : Set ℂ) :
    ∀ x ∈ spectralSubspace T s, T x ∈ spectralSubspace T s := by
  change spectralSubspace T s ≤ (spectralSubspace T s).comap T
  apply iSup_le
  intro z
  apply iSup_le
  intro hz x hx
  exact Submodule.mem_iSup_of_mem z (Submodule.mem_iSup_of_mem hz
    (T.genEigenspace_mem_invtSubmodule z ⊤ hx))

lemma spectralSubspace_isCompl {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (s : Set ℂ) :
    IsCompl (spectralSubspace T s) (spectralSubspace T sᶜ) := by
  refine ⟨T.independent_maxGenEigenspace.disjoint_biSup_biSup disjoint_compl_right, ?_⟩
  rw [codisjoint_iff, spectralSubspace, spectralSubspace, ← iSup_union, Set.union_compl_self,
    iSup_univ, T.iSup_maxGenEigenspace_eq_top]

lemma eigenvalue_restrict_spectralSubspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (s : Set ℂ) (z : ℂ)
    (hz : Module.End.HasEigenvalue (T.restrict (spectralSubspace_invariant T s)) z) : z ∈ s := by
  by_contra hzs
  have hd : Disjoint (T.eigenspace z) (spectralSubspace T s) :=
    (T.independent_maxGenEigenspace.disjoint_biSup hzs).mono_left
      Module.End.eigenspace_le_maxGenEigenspace
  exact hz (Module.End.eigenspace_restrict_eq_bot (spectralSubspace_invariant T s) hd)

lemma finite_spectral_gap (s : Set ℂ) (hs : s.Finite)
    (h : ∀ z ∈ s, 1 < ‖z‖) : ∃ a : ℝ, 1 < a ∧ ∀ z ∈ s, a < ‖z‖ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨2, by norm_num, by simp⟩
  | @insert z s hz hs ih =>
    obtain ⟨a, ha, hbound⟩ := ih (fun w hw => h w (Set.mem_insert_of_mem z hw))
    have hz' := h z (Set.mem_insert z s)
    refine ⟨min a ((1 + ‖z‖) / 2), lt_min ha (by linarith), ?_⟩
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (hbound w hw)

/-- Adapted norms on both complex spectral summands; zero summands are allowed. -/
lemma spectralSubspace_adaptedNorms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) :
    let U := spectralSubspace T {z | 1 < ‖z‖}
    let W := spectralSubspace T {z | 1 < ‖z‖}ᶜ
    ∃ (a b : ℝ) (p : Seminorm ℂ U) (q : Seminorm ℂ W),
      1 < a ∧ 0 ≤ b ∧ b < a ∧ AdaptedNorm.Equivalent p ∧ AdaptedNorm.Equivalent q ∧
      (∀ u, a * p u ≤ p (T.restrict (spectralSubspace_invariant T _) u)) ∧
      (∀ w, q (T.restrict (spectralSubspace_invariant T _) w) ≤ b * q w) := by
  classical
  intro U W
  let Tu : Module.End ℂ U := T.restrict (spectralSubspace_invariant T _)
  let Tw : Module.End ℂ W := T.restrict (spectralSubspace_invariant T _)
  have hu : ∀ z ∈ spectrum ℂ Tu, 1 < ‖z‖ := by
    intro z hz
    exact eigenvalue_restrict_spectralSubspace T _ z
      (Module.End.HasEigenvalue.of_mem_spectrum hz)
  obtain ⟨a, ha, hagap⟩ := finite_spectral_gap _ (Module.End.finite_spectrum Tu) hu
  have hunit : IsUnit Tu := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    have hzero : ¬ Tu.HasEigenvalue 0 := by
      intro hz
      have := hu 0 hz.mem_spectrum
      norm_num at this
    simpa only [Module.End.HasEigenvalue, Module.End.eigenspace_zero] using not_ne_iff.mp hzero
  obtain ⟨unit, hunit⟩ := hunit
  let bu := Module.finBasis ℂ U
  let bw := Module.finBasis ℂ W
  have hspecu : ∀ z ∈ spectrum ℂ (LinearMap.toMatrix bu bu (unit : Module.End ℂ U)),
      a < ‖z‖ := by
    intro z hz
    change z ∈ spectrum ℂ ((LinearMap.toMatrixAlgEquiv bu) (unit : Module.End ℂ U)) at hz
    rw [AlgEquiv.spectrum_eq, hunit] at hz
    exact hagap z hz
  obtain ⟨p, hp, hlow⟩ := AdaptedNorm.lowerComplex bu unit a (by linarith) hspecu
  let b := (1 + a) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hspecw : spectralRadius ℂ (LinearMap.toMatrix bw bw Tw) < ENNReal.ofReal b := by
    have hrad : spectralRadius ℂ (LinearMap.toMatrix bw bw Tw) ≤ 1 := by
      rw [spectralRadius_eq_of_unital]
      apply iSup₂_le
      intro z hz
      have hzs : z ∈ spectrum ℂ Tw := by
        change z ∈ spectrum ℂ ((LinearMap.toMatrixAlgEquiv bw) Tw) at hz
        rwa [AlgEquiv.spectrum_eq] at hz
      have hle : ‖z‖ ≤ 1 := not_lt.mp (eigenvalue_restrict_spectralSubspace T _ z
        (Module.End.HasEigenvalue.of_mem_spectrum hzs))
      exact_mod_cast hle
    exact hrad.trans_lt (by simpa only [← ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < b)).mpr hb)
  obtain ⟨q, hq, hupp, _⟩ := AdaptedNorm.upperComplex bw Tw b hspecw
  refine ⟨a, b, p, q, ha, by linarith, by dsimp [b]; linarith, hp, hq, ?_, hupp⟩
  simpa only [hunit] using hlow

lemma projectionOnto_commutes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (U W : Submodule ℂ V) (h : IsCompl U W)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) (v : V) :
    U.projectionOnto W h (T v) = T.restrict hU (U.projectionOnto W h v) := by
  have hv : (U.projectionOnto W h v : V) + (W.projectionOnto U h.symm v : V) = v :=
    Submodule.projection_add_projection_eq_self h v
  conv_lhs => rw [← hv, map_add, map_add]
  rw [Submodule.projectionOnto_apply_of_mem_left h (hU _ (Subtype.coe_prop _)),
    Submodule.projectionOnto_apply_of_mem_right h (hW _ (Subtype.coe_prop _)), add_zero]
  rfl

/-- Pull the two adapted norms back to a real space embedded in the complexification. -/
lemma coneData_of_complexNorms {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (A : E →L[ℝ] E) (T : Module.End ℂ V)
    (U W : Submodule ℂ V) (h : IsCompl U W)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W)
    (p : Seminorm ℂ U) (q : Seminorm ℂ W)
    (hp : AdaptedNorm.Equivalent p) (hq : AdaptedNorm.Equivalent q)
    (a b : ℝ) (ha : 1 < a) (hb : 0 ≤ b) (hba : b < a)
    (hpa : ∀ u, a * p u ≤ p (T.restrict hU u))
    (hqb : ∀ w, q (T.restrict hW w) ≤ b * q w)
    (J : E →L[ℝ] V) (hJA : ∀ v, J (A v) = T (J v))
    (K : ℝ) (hK : 0 < K) (hJ : ∀ v, ‖v‖ ≤ K * ‖J v‖)
    (w : E) (hw : w ≠ 0) (hwU : J w ∈ U) : Nonempty (ConeData A) := by
  let fu : E →L[ℝ] U :=
    ((U.projectionOnto W h).toContinuousLinearMap.restrictScalars ℝ).comp J
  let fw : E →L[ℝ] W :=
    ((W.projectionOnto U h.symm).toContinuousLinearMap.restrictScalars ℝ).comp J
  let P : Seminorm ℝ E := (p.restrictScalars ℝ).comp fu.toLinearMap
  let Q : Seminorm ℝ E := (q.restrictScalars ℝ).comp fw.toLinearMap
  obtain ⟨Cu, hCu, Du, hDu, hpu⟩ := hp
  obtain ⟨Cw, hCw, Dw, hDw, hqw⟩ := hq
  let C := K * (Cu + Cw)
  let D := Du * (‖fu‖ + 1) + Dw * (‖fw‖ + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum (v : E) : (fu v : V) + (fw v : V) = J v :=
    Submodule.projection_add_projection_eq_self h (J v)
  have hlower (v : E) : ‖v‖ ≤ C * (P v + Q v) := by
    have hnorm : ‖J v‖ ≤ ‖fu v‖ + ‖fw v‖ := by
      rw [← hsum v]
      exact norm_add_le _ _
    have hpu' := (hpu (fu v)).1
    have hqw' := (hqw (fw v)).1
    change ‖fu v‖ ≤ Cu * P v at hpu'
    change ‖fw v‖ ≤ Cw * Q v at hqw'
    have hcomp : ‖J v‖ ≤ (Cu + Cw) * (P v + Q v) := by
      nlinarith [apply_nonneg P v, apply_nonneg Q v]
    exact (hJ v).trans (by simpa only [C, mul_assoc] using
      mul_le_mul_of_nonneg_left hcomp hK.le)
  have hupper (v : E) : P v + Q v ≤ D * ‖v‖ := by
    have hpu' := (hpu (fu v)).2
    have hqw' := (hqw (fw v)).2
    change P v ≤ Du * ‖fu v‖ at hpu'
    change Q v ≤ Dw * ‖fw v‖ at hqw'
    have hu := fu.le_opNorm v
    have hw := fw.le_opNorm v
    dsimp [D]
    nlinarith [norm_nonneg v]
  have hfu (v : E) : fu (A v) = T.restrict hU (fu v) := by
    change U.projectionOnto W h (J (A v)) = _
    rw [hJA]
    exact projectionOnto_commutes T U W h hU hW (J v)
  have hfw (v : E) : fw (A v) = T.restrict hW (fw v) := by
    change W.projectionOnto U h.symm (J (A v)) = _
    rw [hJA]
    exact projectionOnto_commutes T W U h.symm hW hU (J v)
  have hwQ : Q w = 0 := by
    change q (W.projectionOnto U h.symm (J w)) = 0
    rw [Submodule.projectionOnto_apply_of_mem_right h.symm hwU, map_zero]
  have hwP : 0 < P w := by
    have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hl := hlower w
    rw [hwQ, add_zero] at hl
    nlinarith [apply_nonneg P w]
  refine ⟨⟨P, Q, a, b, ha, hb, hba, C, D, hC, hD, hlower, hupper,
    ?_, ?_, w, hwP, hwQ⟩⟩
  · intro v
    change a * p (fu v) ≤ p (fu (A v))
    rw [hfu]
    exact hpa (fu v)
  · intro v
    change q (fw (A v)) ≤ b * q (fw v)
    rw [hfw]
    exact hqb (fw v)

lemma complexify_mulVec_star {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℂ) :
    (Ch08.MatrixPowerCriteria.complexify M).mulVec (star v) =
      star ((Ch08.MatrixPowerCriteria.complexify M).mulVec v) := by
  ext i
  simp [Ch08.MatrixPowerCriteria.complexify, Matrix.mulVec, dotProduct,
    star_sum, star_mul, mul_comm]

lemma star_mem_maxGenEigenspace {d : ℕ} (T : Module.End ℂ (Fin d → ℂ))
    (hT : ∀ v, T (star v) = star (T v)) {z : ℂ} {v : Fin d → ℂ}
    (hv : v ∈ T.maxGenEigenspace z) : star v ∈ T.maxGenEigenspace (star z) := by
  obtain ⟨k, hk⟩ := (T.mem_maxGenEigenspace z v).mp hv
  apply (T.mem_maxGenEigenspace (star z) (star v)).mpr
  have hpow : ∀ n : ℕ, ∀ x : Fin d → ℂ,
      ((T - star z • 1) ^ n) (star x) = star (((T - z • 1) ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hT]
      ext i
      simp [star_sub, star_mul, mul_comm]
  refine ⟨k, ?_⟩
  rw [hpow, hk, star_zero]

lemma star_mem_unstableSubspace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    {v : Fin d → ℂ}
    (hv : v ∈ spectralSubspace (Ch08.MatrixPowerCriteria.complexify M).toLin' {z | 1 < ‖z‖}) :
    star v ∈ spectralSubspace (Ch08.MatrixPowerCriteria.complexify M).toLin' {z | 1 < ‖z‖} := by
  let T : Module.End ℂ (Fin d → ℂ) := (Ch08.MatrixPowerCriteria.complexify M).toLin'
  change v ∈ ⨆ z ∈ {z : ℂ | 1 < ‖z‖}, T.maxGenEigenspace z at hv
  refine Submodule.iSup_induction _ (motive := fun x => star x ∈ spectralSubspace T {z | 1 < ‖z‖}) hv ?_ ?_ ?_
  · intro z x hx
    refine Submodule.iSup_induction _ (motive := fun x => star x ∈ spectralSubspace T {z | 1 < ‖z‖}) hx ?_ ?_ ?_
    · intro hz x hx
      have hstar := star_mem_maxGenEigenspace T (complexify_mulVec_star M) hx
      exact Submodule.mem_iSup_of_mem (star z) (Submodule.mem_iSup_of_mem
        (by simpa using hz : star z ∈ {z : ℂ | 1 < ‖z‖}) hstar)
    · simpa only [star_zero] using (spectralSubspace T _).zero_mem
    · intro x y hx hy
      simpa only [star_add] using (spectralSubspace T _).add_mem hx hy
  · simpa only [star_zero] using (spectralSubspace T _).zero_mem
  · intro x y hx hy
    simpa only [star_add] using (spectralSubspace T _).add_mem hx hy

/-- A nonzero conjugation-stable unstable space contains a nonzero real vector. -/
lemma real_unstable_direction {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hspec : ∃ z : ℂ, Module.End.HasEigenvalue
      (Ch08.MatrixPowerCriteria.complexify M).toLin' z ∧ 1 < ‖z‖) :
    ∃ w : Fin d → ℝ, w ≠ 0 ∧
      (fun i => (w i : ℂ)) ∈
        spectralSubspace (Ch08.MatrixPowerCriteria.complexify M).toLin' {z | 1 < ‖z‖} := by
  obtain ⟨z, hz, hznorm⟩ := hspec
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  let U := spectralSubspace (Ch08.MatrixPowerCriteria.complexify M).toLin' {z | 1 < ‖z‖}
  have hvU : v ∈ U := Submodule.mem_iSup_of_mem z (Submodule.mem_iSup_of_mem hznorm
    (Module.End.eigenspace_le_maxGenEigenspace hv.1))
  have hstar : star v ∈ U := star_mem_unstableSubspace M hvU
  have hre : (fun i => ((v i).re : ℂ)) ∈ U := by
    have h := U.smul_mem (1 / 2 : ℂ) (U.add_mem hvU hstar)
    convert h using 1
    ext i
    apply Complex.ext <;> simp; ring
  have him : (fun i => ((v i).im : ℂ)) ∈ U := by
    have h := U.smul_mem (-Complex.I / 2) (U.sub_mem hvU hstar)
    convert h using 1
    ext i
    apply Complex.ext <;> simp; ring
  by_cases hreal : (fun i => (v i).re) = 0
  · refine ⟨fun i => (v i).im, ?_, him⟩
    intro hi
    apply hv.2
    ext i
    apply Complex.ext
    · exact congrFun hreal i
    · exact congrFun hi i
  · exact ⟨_, hreal, hre⟩

/-- Construct projected adapted norms from the complexified spectral condition.
The generalized eigenspaces include all Jordan blocks, and conjugation produces
a nonzero real expanding direction. No spectral conditions are placed on the
complement beyond its defining modulus cutoff. -/
lemma spectralCone_exists {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (basis : Basis (Fin d) ℝ E)
    (A : E →L[ℝ] E)
    (hspec : ∃ z : ℂ, Module.End.HasEigenvalue
      (Ch08.MatrixPowerCriteria.complexify
        (LinearMap.toMatrix basis basis A.toLinearMap)).toLin' z ∧ 1 < ‖z‖) :
    Nonempty (ConeData A) := by
  let M := LinearMap.toMatrix basis basis A.toLinearMap
  let T : Module.End ℂ (Fin d → ℂ) := (Ch08.MatrixPowerCriteria.complexify M).toLin'
  let U := spectralSubspace T {z | 1 < ‖z‖}
  let W := spectralSubspace T {z | 1 < ‖z‖}ᶜ
  obtain ⟨a, b, p, q, ha, hb, hba, hp, hq, hpa, hqb⟩ := spectralSubspace_adaptedNorms T
  let I : (Fin d → ℝ) →L[ℝ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))
  have hInorm (v : Fin d → ℝ) : ‖I v‖ = ‖v‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      intro i
      simpa only [I, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.norm_real,
        Real.norm_eq_abs] using norm_le_pi_norm v i
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (I v))).mpr
      intro i
      have h := norm_le_pi_norm (I v) i
      simpa only [I, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.norm_real,
        Real.norm_eq_abs] using h
  let e := basis.equivFunL
  let J : E →L[ℝ] (Fin d → ℂ) := I.comp e.toContinuousLinearMap
  have hJA (v : E) : J (A v) = T (J v) := by
    change (fun i => ((basis.repr (A v) i : ℝ) : ℂ)) =
      (Ch08.MatrixPowerCriteria.complexify M).mulVec
        (fun i => ((basis.repr v i : ℝ) : ℂ))
    have hm := LinearMap.toMatrix_mulVec_repr basis basis A.toLinearMap v
    change M.mulVec (basis.repr v) = basis.repr (A v) at hm
    rw [← hm]
    ext i
    simp [Ch08.MatrixPowerCriteria.complexify, Matrix.mulVec, dotProduct]
  let K := ‖e.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hJ (v : E) : ‖v‖ ≤ K * ‖J v‖ := by
    have hv : ‖v‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
        e.symm.toContinuousLinearMap.le_opNorm (e v)
    have hnorm : ‖J v‖ = ‖e v‖ := hInorm (e v)
    rw [hnorm]
    dsimp [K]
    nlinarith [norm_nonneg (e v)]
  obtain ⟨w, hw, hwU⟩ := real_unstable_direction M hspec
  apply coneData_of_complexNorms A T U W (spectralSubspace_isCompl T _)
    (spectralSubspace_invariant T _) (spectralSubspace_invariant T _)
    p q hp hq a b ha hb hba hpa hqb J hJA K hK hJ (e.symm w)
  · exact fun h => hw (by simpa using congrArg e h)
  · change (fun i => ((e (e.symm w)) i : ℂ)) ∈ U
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hwU

theorem linearizedInstability :
    Specs.D13Unified.Ch15.LinearizedInstability.linearizedInstability := by
  intro E _ _ _ d basis F V p A hV hp hfix _ hF hspec
  obtain ⟨data⟩ := spectralCone_exists basis A hspec
  exact instability_of_coneData data F V p hV hp hfix hF

end D13Unified.Ch15.LinearizedInstability
