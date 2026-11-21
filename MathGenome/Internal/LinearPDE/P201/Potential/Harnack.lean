import MathGenome.Internal.LinearPDE.P201Specs.Potential.Harnack
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Ring
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
namespace P201.Harnack
open P201Specs

/-- Scalar form of the sharp Poisson-kernel estimate. -/
theorem normalized_kernel_bounds (k : ℕ) {ρ t d : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (_ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hlo : 1 - t ≤ d) (hhi : d ≤ 1 + t) :
    (1 - ρ) / (1 + ρ) ^ k ≤ (1 - t ^ 2) / d ^ (k + 1) ∧
    (1 - t ^ 2) / d ^ (k + 1) ≤ (1 + ρ) / (1 - ρ) ^ k := by
  have ht1 : t < 1 := htρ.trans_lt hρ1
  have hd : 0 < d := lt_of_lt_of_le (by linarith) hlo
  have hp : 0 < 1 + ρ := by linarith
  have hm : 0 < 1 - ρ := by linarith
  have hdp : d ^ k ≤ (1 + ρ) ^ k := pow_le_pow_left₀ hd.le (by linarith) k
  have hdm : (1 - ρ) ^ k ≤ d ^ k := pow_le_pow_left₀ hm.le (by linarith) k
  constructor
  · apply (div_le_div_iff₀ (pow_pos hp k) (pow_pos hd (k + 1))).mpr
    rw [pow_succ]
    calc
      (1 - ρ) * (d ^ k * d) ≤ (1 - t) * ((1 + ρ) ^ k * d) := by
        exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hdp hd.le)
          (mul_nonneg (pow_nonneg hd.le k) hd.le) (by linarith)
      _ ≤ (1 - t) * ((1 + ρ) ^ k * (1 + t)) := by
        gcongr
      _ = (1 - t ^ 2) * (1 + ρ) ^ k := by ring
  · apply (div_le_div_iff₀ (pow_pos hd (k + 1)) (pow_pos hm k)).mpr
    rw [pow_succ]
    calc
      (1 - t ^ 2) * (1 - ρ) ^ k = (1 + t) * ((1 - t) * (1 - ρ) ^ k) := by ring
      _ ≤ (1 + ρ) * (d * d ^ k) := by
        exact mul_le_mul (by linarith)
          (mul_le_mul hlo hdm (pow_nonneg hm.le k) hd.le)
          (mul_nonneg (by linarith) (pow_nonneg hm.le k)) (by linarith)
      _ = (1 + ρ) * (d ^ k * d) := by ring

/-- The specified surface measure is supported on the sphere. -/
theorem sphereSurface_ae_mem {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ζ ∂sphereSurface a r, ζ ∈ sphere a r := by
  exact P201.BallPoisson.sphereSurface_ae_mem a hr

/-- Comparison with the value of the kernel at the center. -/
theorem kernel_bounds {n : ℕ} (hn : 2 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {x ζ : Space n} (hx : ‖x - a‖ ≤ ρ * r) (hζ : ζ ∈ sphere a r) :
    ((1 - ρ) / (1 + ρ) ^ (n - 1)) * BallPoisson.kernel a r a ζ ≤
      BallPoisson.kernel a r x ζ ∧
    BallPoisson.kernel a r x ζ ≤
      ((1 + ρ) / (1 - ρ) ^ (n - 1)) * BallPoisson.kernel a r a ζ := by
  have hζr : ‖a - ζ‖ = r := by
    rw [norm_sub_rev]; exact mem_sphere_iff_norm.mp hζ
  have htri : ‖x - ζ‖ ≤ r + ‖x - a‖ := by
    calc
      ‖x - ζ‖ = ‖(x - a) + (a - ζ)‖ := by congr 1; abel
      _ ≤ ‖x - a‖ + ‖a - ζ‖ := norm_add_le _ _
      _ = r + ‖x - a‖ := by rw [hζr]; ring
  have hrev : r - ‖x - a‖ ≤ ‖x - ζ‖ := by
    have : r ≤ ‖x - a‖ + ‖x - ζ‖ := by
      calc
        r = ‖(a - x) + (x - ζ)‖ := by rw [sub_add_sub_cancel, hζr]
        _ ≤ ‖a - x‖ + ‖x - ζ‖ := norm_add_le _ _
        _ = ‖x - a‖ + ‖x - ζ‖ := by rw [norm_sub_rev a x]
    linarith
  have hxlt : ‖x - a‖ < r := hx.trans_lt (by nlinarith)
  have hd : 0 < ‖x - ζ‖ := lt_of_lt_of_le (by linarith) hrev
  have hh := normalized_kernel_bounds (n - 1) (d := ‖x - ζ‖ / r) hρ hρ1
    (div_nonneg (norm_nonneg _) hr.le) ((div_le_iff₀ hr).mpr hx)
    ((le_div_iff₀ hr).mpr (by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hr.ne']
      exact hrev))
    ((div_le_iff₀ hr).mpr (by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hr.ne']
      exact htri))
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hh
  have ho : 0 < omega n := P201.MeanValues.omega_pos (by omega)
  have hc : 0 < BallPoisson.kernel a r a ζ := by
    unfold BallPoisson.kernel P201Specs.BallPoisson.kernel
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, hζr]
    exact div_pos (sq_pos_of_pos hr) (mul_pos (mul_pos hr ho) (pow_pos hr n))
  have he : BallPoisson.kernel a r x ζ =
      ((1 - (‖x - a‖ / r) ^ 2) / (‖x - ζ‖ / r) ^ n) *
        BallPoisson.kernel a r a ζ := by
    unfold BallPoisson.kernel P201Specs.BallPoisson.kernel
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, hζr, div_pow]
    field_simp
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right hh.1 hc.le, mul_le_mul_of_nonneg_right hh.2 hc.le⟩

/-- The ball estimate in dimensions covered by the Poisson interfaces. -/
theorem ball_bounds_of_poisson
    (hph : P201Specs.BallPoisson.PoissonHarmonicStatement)
    (hrep : P201Specs.BallPoisson.RepresentationStatement)
    {n : ℕ} (hn : 2 ≤ n) (Ω : Domain n) (u : Space n → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (hu0 : ∀ y ∈ Ω, 0 ≤ u y)
    (a : Space n) (r : ℝ) (hr : 0 < r) (hb : closedBall a r ⊆ (Ω : Set _))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (x : Space n) (hx : ‖x - a‖ ≤ ρ * r) :
    ((1 - ρ) / (1 + ρ) ^ (n - 1)) * u a ≤ u x ∧
    u x ≤ ((1 + ρ) / (1 - ρ) ^ (n - 1)) * u a := by
  obtain ⟨g, hg, heq, _⟩ := hrep hn a r hr Ω u hb hu
  have ha : a ∈ ball a r := mem_ball_self hr
  have hxi : x ∈ ball a r := by
    rw [mem_ball_iff_norm]
    exact hx.trans_lt (by nlinarith)
  have hi := (hph hn a r hr g).1
  let f : Space n → Space n → ℝ := fun y ζ =>
    BallPoisson.kernel a r y ζ * BallPoisson.boundaryValue a r g ζ
  have hia : Integrable (f a) (sphereSurface a r) := by
    simpa only [f, smul_eq_mul] using hi a ha
  have hix : Integrable (f x) (sphereSurface a r) := by
    simpa only [f, smul_eq_mul] using hi x hxi
  have hea : (∫ ζ, f a ζ ∂sphereSurface a r) = u a := (heq ha).symm
  have hex : (∫ ζ, f x ζ ∂sphereSurface a r) = u x := (heq hxi).symm
  have hbnd : ∀ᵐ ζ ∂sphereSurface a r,
      ((1 - ρ) / (1 + ρ) ^ (n - 1)) * f a ζ ≤ f x ζ ∧
      f x ζ ≤ ((1 + ρ) / (1 - ρ) ^ (n - 1)) * f a ζ := by
    filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
    have hg0 : 0 ≤ BallPoisson.boundaryValue a r g ζ := by
      rw [show BallPoisson.boundaryValue a r g ζ = g ⟨ζ, hζ⟩ from
        P201.BallPoisson.boundaryValue_coe a r g ⟨ζ, hζ⟩, hg ⟨ζ, hζ⟩]
      exact hu0 ζ (hb (sphere_subset_closedBall hζ))
    obtain ⟨hl, hh⟩ := kernel_bounds hn a hr hρ hρ1 hx hζ
    constructor
    · simpa only [f, mul_assoc] using mul_le_mul_of_nonneg_right hl hg0
    · simpa only [f, mul_assoc] using mul_le_mul_of_nonneg_right hh hg0
  constructor
  · have h := integral_mono_ae (hia.const_mul _) hix (hbnd.mono fun _ h => h.1)
    rwa [integral_const_mul, hea, hex] at h
  · have h := integral_mono_ae hix (hia.const_mul _) (hbnd.mono fun _ h => h.2)
    rwa [integral_const_mul, hea, hex] at h

/-- In the fixed one-dimensional frame every vector is a scalar multiple
of the unit coordinate. -/
theorem vector_one (v : Space 1) : v = (v 0) • coordinate 1 0 := by
  ext i
  fin_cases i
  simp [coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single]

/-- One-dimensional harmonic functions agree with their affine tangent
on every closed interval compactly contained in their domain. -/
theorem affine_on_ball_one (Ω : Domain 1) (u : Space 1 → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic Ω u)
    (a : Space 1) {r : ℝ} (hr : 0 < r) (hb : closedBall a r ⊆ (Ω : Set _)) :
    ∀ x ∈ closedBall a r, u x = u a + (x 0 - a 0) *
      fderiv ℝ u a (coordinate 1 0) := by
  let e := coordinate 1 0
  let D : Space 1 → ℝ := fun y => fderiv ℝ u y e
  have hD : ContDiffOn ℝ 1 D Ω :=
    (hu.1.fderiv_of_isOpen Ω.isOpen (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffOn_const
  have hd : ∀ y ∈ closedBall a r, DifferentiableAt ℝ D y := fun y hy =>
    (hD.contDiffAt (Ω.isOpen.mem_nhds (hb hy))).differentiableAt one_ne_zero
  have hdz : ∀ y ∈ closedBall a r, fderiv ℝ D y = 0 := by
    intro y hy
    have hl : fderiv ℝ D y e = 0 := by
      have hs : ({(0 : Fin 1), 0} : Multiset (Fin 1)).sort (· ≤ ·) = [0, 0] := by
        rw [Multiset.insert_eq_cons, Multiset.sort_cons 0 {0} (· ≤ ·) (by simp),
          Multiset.sort_singleton]
      simpa only [laplacian, Fin.sum_univ_one, multiPartial, P102.U4.multiPartial,
        hs, P102.U4.partialWord, D, e] using hu.2 y (hb hy)
    ext v
    rw [vector_one v, map_smul]
    change (v 0) • fderiv ℝ D y e = 0
    rw [hl, smul_zero]
  have ha : a ∈ closedBall a r := mem_closedBall_self hr.le
  have hc : ∀ y ∈ closedBall a r, D y = D a := by
    intro y hy
    have h := (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le'
      hd (φ := 0) (C := 0) (fun z hz => by simp [hdz z hz]) ha hy
    simpa only [zero_apply, sub_zero, zero_mul, norm_le_zero_iff,
      sub_eq_zero] using h
  have hdu : ∀ y ∈ closedBall a r, DifferentiableAt ℝ u y := fun y hy =>
    (hu.1.contDiffAt (Ω.isOpen.mem_nhds (hb hy))).differentiableAt (by norm_num)
  have he : ∀ y ∈ closedBall a r, fderiv ℝ u y = fderiv ℝ u a := by
    intro y hy
    ext v
    rw [vector_one v, map_smul, map_smul]
    exact congrArg (fun t : ℝ => (v 0) • t) (hc y hy)
  intro x hx
  have h := (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le'
    hdu (φ := fderiv ℝ u a) (C := 0) (fun z hz => by simp [he z hz]) ha hx
  have hh : u x - u a - fderiv ℝ u a (x - a) = 0 := by simpa using h
  rw [vector_one (x - a), map_smul] at hh
  change u x - u a - (x 0 - a 0) * D a = 0 at hh
  change u x = u a + (x 0 - a 0) * D a
  linarith

/-- Sharp interval bounds follow from affinity and nonnegativity of the
two endpoint values; no Poisson formula in dimension one is assumed. -/
theorem ball_bounds_one (Ω : Domain 1) (u : Space 1 → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic Ω u) (hu0 : ∀ y ∈ Ω, 0 ≤ u y)
    (a : Space 1) (r : ℝ) (hr : 0 < r) (hb : closedBall a r ⊆ (Ω : Set _))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (x : Space 1) (hx : ‖x - a‖ ≤ ρ * r) :
    (1 - ρ) * u a ≤ u x ∧ u x ≤ (1 + ρ) * u a := by
  let e := coordinate 1 0
  let D := fderiv ℝ u a e
  have he : ‖e‖ = 1 := by
    simp [e, P102.U4.coordinateVector]
  have he0 : e 0 = 1 := by
    simp [e, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]
  have hp : a + r • e ∈ closedBall a r := by
    simp [norm_smul, he, abs_of_pos hr]
  have hm : a - r • e ∈ closedBall a r := by
    simp [norm_smul, he, abs_of_pos hr]
  have hpos := affine_on_ball_one Ω u hu a hr hb (a + r • e) hp
  have hneg := affine_on_ball_one Ω u hu a hr hb (a - r • e) hm
  have hep : (a + r • e) 0 - a 0 = r := by simp [he0]
  have hem : (a - r • e) 0 - a 0 = -r := by simp [he0]
  rw [hep] at hpos
  rw [hem] at hneg
  have hD : |r * D| ≤ u a := abs_le.mpr (by
    constructor <;> nlinarith [hu0 _ (hb hp), hu0 _ (hb hm)])
  have hx' : |x 0 - a 0| ≤ ρ * r := by
    have hn : ‖x - a‖ = |x 0 - a 0| := by
      rw [vector_one (x - a), norm_smul, he, mul_one]
      rfl
    rwa [hn] at hx
  have hmul : |(x 0 - a 0) * D| ≤ ρ * u a := by
    rw [abs_mul]
    calc
      |x 0 - a 0| * |D| ≤ (ρ * r) * |D| := mul_le_mul_of_nonneg_right hx' (abs_nonneg _)
      _ = ρ * |r * D| := by rw [abs_mul, abs_of_pos hr]; ring
      _ ≤ ρ * u a := mul_le_mul_of_nonneg_left hD hρ
  have hxc : x ∈ closedBall a r := by
    rw [mem_closedBall_iff_norm]
    exact hx.trans (by nlinarith)
  have hux := affine_on_ball_one Ω u hu a hr hb x hxc
  change u x = u a + (x 0 - a 0) * D at hux
  constructor <;> nlinarith [(abs_le.mp hmul).1, (abs_le.mp hmul).2]

/-- The sharp ball Harnack bounds in every dimension n ≥ 1. -/
theorem ball_bounds : P201Specs.Harnack.BallBoundsStatement := by
  intro n hn Ω u hu hu0 a r hr hb ρ hρ hρ1 x hx
  by_cases hn2 : 2 ≤ n
  · exact ball_bounds_of_poisson P201.BallPoisson.poisson_harmonic
      P201.BallPoisson.representation hn2 Ω u hu hu0 a r hr hb ρ hρ hρ1 x hx
  · have hn1 : n = 1 := by omega
    subst n
    simpa using ball_bounds_one Ω u hu hu0 a r hr hb ρ hρ hρ1 x hx

/-- Ball bounds give a neighborhood comparison, with constants independent
of the function. -/
theorem neighborhood_comparison
    (hball : P201Specs.Harnack.BallBoundsStatement)
    {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n) (a : Space n) (ha : a ∈ Ω) :
    ∃ V : Set (Space n), IsOpen V ∧ a ∈ V ∧ V ⊆ (Ω : Set _) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (u : Space n → ℝ), P201Specs.MeanValues.IsHarmonic Ω u →
          (∀ y ∈ Ω, 0 ≤ u y) → ∀ x ∈ V, c * u a ≤ u x ∧ u x ≤ C * u a := by
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds ha)
  let r := s / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hb : closedBall a r ⊆ (Ω : Set _) := by
    apply Subset.trans _ hsub
    exact closedBall_subset_ball (by dsimp [r]; linarith)
  refine ⟨ball a (r / 2), isOpen_ball, mem_ball_self (by positivity),
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith) |>.trans hb),
    (1 - (1 / 2 : ℝ)) / (1 + (1 / 2 : ℝ)) ^ (n - 1),
    (1 + (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) ^ (n - 1), by positivity, by positivity, ?_⟩
  intro u hu hu0 x hx
  apply hball hn Ω u hu hu0 a r hr hb (1 / 2) (by norm_num) (by norm_num) x
  have hx' : ‖x - a‖ < r / 2 := mem_ball_iff_norm.mp hx
  linarith

/-- Reversing a lower comparison with a strictly positive coefficient. -/
theorem inverse_comparison {c a b : ℝ} (hc : 0 < c) (h : c * a ≤ b) :
    a ≤ c⁻¹ * b := by
  have h' : a ≤ b / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)
  simpa [div_eq_mul_inv, mul_comm] using h'

/-- Connectedness propagates uniform comparisons between any two points.
This uses open equivalence classes rather than choosing a polygonal chain. -/
theorem point_comparison
    (hball : P201Specs.Harnack.BallBoundsStatement)
    {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n) (hΩ : IsConnected (Ω : Set (Space n)))
    {a b : Space n} (ha : a ∈ Ω) (hb : b ∈ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space n → ℝ),
      P201Specs.MeanValues.IsHarmonic Ω u → (∀ y ∈ Ω, 0 ≤ u y) →
      u b ≤ C * u a := by
  let P : Space n → Space n → Prop := fun a b =>
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space n → ℝ),
      P201Specs.MeanValues.IsHarmonic Ω u → (∀ y ∈ Ω, 0 ≤ u y) →
      u b ≤ C * u a
  have hlocal : ∀ x ∈ (Ω : Set (Space n)),
      ∀ᶠ y in 𝓝[(Ω : Set (Space n))] x, P x y ∧ P y x := by
    intro x hx
    obtain ⟨V, hVo, hxV, _, c, C, hc, hC, hcomp⟩ :=
      neighborhood_comparison hball hn Ω x hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hxV)] with y hy
    refine ⟨⟨C, hC, ?_⟩, ⟨c⁻¹, inv_pos.mpr hc, ?_⟩⟩
    · intro u hu hu0
      exact (hcomp u hu hu0 y hy).2
    · intro u hu hu0
      exact inverse_comparison hc (hcomp u hu hu0 y hy).1
  have htrans : ∀ x y z : Space n, x ∈ Ω → y ∈ Ω → z ∈ Ω →
      P x y → P y z → P x z := by
    rintro x y z _ _ _ ⟨C, hC, hc⟩ ⟨D, hD, hd⟩
    refine ⟨D * C, mul_pos hD hC, ?_⟩
    intro u hu hu0
    calc
      u z ≤ D * u y := hd u hu hu0
      _ ≤ D * (C * u x) := mul_le_mul_of_nonneg_left (hc u hu hu0) hD.le
      _ = (D * C) * u x := by ring
  exact hΩ.isPreconnected.induction₂' P hlocal htrans ha hb

/-- Compactness makes the point comparisons uniform on the compact set,
while keeping all constants independent of the harmonic function. -/
theorem compact_bounds_of_ball_bounds
    (hball : P201Specs.Harnack.BallBoundsStatement) :
    P201Specs.Harnack.CompactBoundsStatement := by
  classical
  intro n hn Ω hΩ K hK hKΩ a₀ ha₀
  choose V hVo hyV hVΩ c C hc hC hcomp using
    (fun y : K => neighborhood_comparison hball hn Ω y (hKΩ y.property))
  choose A hA hAc using (fun y : K =>
    point_comparison hball hn Ω hΩ ha₀ (hKΩ y.property))
  choose B hB hBc using (fun y : K =>
    point_comparison hball hn Ω hΩ (hKΩ y.property) ha₀)
  have hcover : K ⊆ ⋃ y : K, V y := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hyV ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hVo hcover
  let U : ℝ := 1 + ∑ y ∈ s, C y * A y
  let D : ℝ := 1 + ∑ y ∈ s, B y * (c y)⁻¹
  have hsumU : 0 ≤ ∑ y ∈ s, C y * A y :=
    Finset.sum_nonneg (fun y _ => (mul_pos (hC y) (hA y)).le)
  have hsumD : 0 ≤ ∑ y ∈ s, B y * (c y)⁻¹ :=
    Finset.sum_nonneg (fun y _ => (mul_pos (hB y) (inv_pos.mpr (hc y))).le)
  have hU : 0 < U := by dsimp [U]; linarith
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D⁻¹, U, inv_pos.mpr hD, hU, ?_⟩
  intro u hu hu0 x hx
  obtain ⟨y, hys, hxV⟩ := mem_iUnion₂.mp (hs hx)
  have hcmp := hcomp y u hu hu0 x hxV
  have hUy : C y * A y ≤ U := by
    have h := Finset.single_le_sum
      (fun z (_ : z ∈ s) => (mul_pos (hC z) (hA z)).le) hys
    dsimp [U]
    linarith
  have hDy : B y * (c y)⁻¹ ≤ D := by
    have h := Finset.single_le_sum
      (fun z (_ : z ∈ s) => (mul_pos (hB z) (inv_pos.mpr (hc z))).le) hys
    dsimp [D]
    linarith
  have hupper : u x ≤ U * u a₀ := by
    calc
      u x ≤ C y * u y := hcmp.2
      _ ≤ C y * (A y * u a₀) := mul_le_mul_of_nonneg_left (hAc y u hu hu0) (hC y).le
      _ = (C y * A y) * u a₀ := by ring
      _ ≤ U * u a₀ := mul_le_mul_of_nonneg_right hUy (hu0 a₀ ha₀)
  have hreverse : u a₀ ≤ D * u x := by
    calc
      u a₀ ≤ B y * u y := hBc y u hu hu0
      _ ≤ B y * ((c y)⁻¹ * u x) :=
        mul_le_mul_of_nonneg_left (inverse_comparison (hc y) hcmp.1) (hB y).le
      _ = (B y * (c y)⁻¹) * u x := by ring
      _ ≤ D * u x := mul_le_mul_of_nonneg_right hDy (hu0 x (hKΩ hx))
  refine ⟨?_, hupper⟩
  have h := mul_le_mul_of_nonneg_left hreverse (inv_pos.mpr hD).le
  simpa only [← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul] using h

/-- Positive comparisons on each compact subset, uniform over all
nonnegative harmonic functions on the connected domain. -/
theorem compact_bounds : P201Specs.Harnack.CompactBoundsStatement :=
  compact_bounds_of_ball_bounds ball_bounds

end P201.Harnack
