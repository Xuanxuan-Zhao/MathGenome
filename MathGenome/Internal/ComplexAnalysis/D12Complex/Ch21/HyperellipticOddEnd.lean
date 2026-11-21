import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.HyperellipticOddEnd
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.GroupWithZero

/-! The odd infinity end, on the literal affine zero set (paper.tex:3741–3755). -/
noncomputable section
open Set Filter Topology

namespace D12Complex.HyperellipticOddEnd

lemma reverse_eval_zero (P : Polynomial ℂ) : P.reverse.eval 0 = P.leadingCoeff := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]

lemma exists_local_nonzero_sqrt (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ (R : ℝ) (h : ℂ → ℂ), 0 < R ∧ HolomorphicOn (Metric.ball 0 R) h ∧
      (∀ s ∈ Metric.ball 0 R, h s ≠ 0) ∧
      (∀ s ∈ Metric.ball 0 R, (h s) ^ 2 = P.reverse.eval s) ∧
      (h 0) ^ 2 = P.leadingCoeff ∧ P.leadingCoeff ≠ 0 := by
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hrev : P.reverse.eval 0 ≠ 0 := by rwa [reverse_eval_zero]
  obtain ⟨U, h, h0U, hUuniv, hh, hh0, hroot⟩ :=
    LocalLogarithmsRoots.local_root Set.univ P.reverse.eval 0 2
      (Complex.sqrt (P.reverse.eval 0))
      ⟨isOpen_univ, fun z _ => P.reverse.differentiableAt⟩
      (mem_univ _) hrev (by norm_num) (by rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num)
  have hh0ne : h 0 ≠ 0 := by
    intro hz
    apply hrev
    have he := hroot 0 h0U
    simpa [hz] using he.symm
  have hn : ∀ᶠ s in 𝓝 (0 : ℂ), h s ≠ 0 :=
    (hh.2 0 h0U).continuousAt.eventually_ne hh0ne
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (inter_mem (hh.1.mem_nhds h0U) hn)
  refine ⟨R, h, hR, ⟨Metric.isOpen_ball, fun s hs => hh.2 s (hRU hs).1⟩,
    fun s hs => (hRU hs).2, fun s hs => hroot s (hRU hs).1, ?_, hlead⟩
  simpa [reverse_eval_zero] using hroot 0 h0U

lemma exists_square_subradius (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ^ 2 < R ∧
      ∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R := by
  let r := Real.sqrt R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < Real.sqrt R := by
    dsimp [r]
    exact half_lt_self (Real.sqrt_pos.mpr hR)
  have hr2 : r ^ 2 < R := by
    have := (sq_lt_sq₀ hr.le (Real.sqrt_nonneg R)).mpr hrR
    rwa [Real.sq_sqrt hR.le] at this
  refine ⟨r, hr, hr2, ?_⟩
  intro t ht
  simp only [Metric.mem_ball, dist_zero_right] at ht ⊢
  rw [norm_pow]
  exact (pow_lt_pow_left₀ ht (norm_nonneg t) (by omega)).trans hr2

lemma square_pullback_holomorphic {R r : ℝ} {h : ℂ → ℂ}
    (hh : HolomorphicOn (Metric.ball 0 R) h)
    (hsq : ∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R) :
    HolomorphicOn (Metric.ball 0 r) (fun t => h (t ^ 2)) := by
  refine ⟨Metric.isOpen_ball, fun t ht => ?_⟩
  exact (hh.2 (t ^ 2) (hsq t ht)).comp t (differentiableAt_id.pow 2)

lemma square_pullback_even (h : ℂ → ℂ) :
    Function.Even (fun t : ℂ => h (t ^ 2)) := by
  intro t
  simp

lemma exists_even_local_sqrt (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ (R r : ℝ) (h : ℂ → ℂ),
      0 < R ∧ 0 < r ∧ r ^ 2 ≤ R ∧
      HolomorphicOn (Metric.ball 0 R) h ∧
      (∀ s ∈ Metric.ball 0 R, h s ≠ 0 ∧ (h s) ^ 2 = P.reverse.eval s) ∧
      (h 0) ^ 2 = P.leadingCoeff ∧ P.leadingCoeff ≠ 0 ∧
      (∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R) ∧
      HolomorphicOn (Metric.ball 0 r) (fun t => h (t ^ 2)) ∧
      Function.Even (fun t : ℂ => h (t ^ 2)) ∧
      (∀ t ∈ Metric.ball 0 r, h (t ^ 2) ≠ 0 ∧
        (h (t ^ 2)) ^ 2 = P.reverse.eval (t ^ 2)) := by
  obtain ⟨R, h, hR, hh, hne, hroot, hzero, hlead⟩ := exists_local_nonzero_sqrt P hP
  obtain ⟨r, hr, hrR, hsq⟩ := exists_square_subradius R hR
  exact ⟨R, r, h, hR, hr, hrR.le, hh, fun s hs => ⟨hne s hs, hroot s hs⟩,
    hzero, hlead, hsq, square_pullback_holomorphic hh hsq,
    square_pullback_even h, fun t ht => ⟨hne _ (hsq t ht), hroot _ (hsq t ht)⟩⟩

lemma inverse_power_holomorphic (r : ℝ) (n : ℕ) :
    HolomorphicOn {t : ℂ | t ≠ 0 ∧ ‖t‖ < r} (fun t => t⁻¹ ^ n) := by
  refine ⟨isOpen_ne_fun continuous_id continuous_const |>.inter
    (isOpen_lt continuous_norm continuous_const), ?_⟩
  intro t ht
  exact (differentiableAt_inv ht.1).pow n

lemma quotient_power_holomorphic {r : ℝ} {u : ℂ → ℂ}
    (hu : HolomorphicOn (Metric.ball 0 r) u) (n : ℕ) :
    HolomorphicOn {t : ℂ | t ≠ 0 ∧ ‖t‖ < r} (fun t => u t / t ^ n) := by
  refine ⟨(inverse_power_holomorphic r n).1, ?_⟩
  intro t ht
  exact (hu.2 t (by simpa only [Metric.mem_ball, dist_zero_right] using ht.2)).div
    (differentiableAt_id.pow n) (pow_ne_zero n ht.1)

lemma square_order : analyticOrderAt (fun t : ℂ => t ^ 2) 0 = 2 := by
  have he : ((fun t : ℂ => t - 0) ^ 2) = (fun t : ℂ => t ^ 2) := by
    funext t
    simp
  rw [← he]
  exact analyticOrderAt_centeredMonomial



lemma reverse_eval_eq (P : Polynomial ℂ) (t : ℂ) (ht : t ≠ 0) :
    P.reverse.eval t = t ^ P.natDegree * P.eval t⁻¹ := by
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) t⁻¹ P
  simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at h
  calc
    P.reverse.eval t = P.reverse.eval t * ((t⁻¹)^P.natDegree * t^P.natDegree) := by
      simp [ht]
    _ = t ^ P.natDegree * P.eval t⁻¹ := by rw [← mul_assoc, h]; ring

lemma parameter_square (g : ℕ) (z w H : ℂ) (hz : z ≠ 0) (hw : w ≠ 0)
    (hsq : H ^ 2 = (z⁻¹)^(2*g+1) * w^2) :
    (H * z^g / w)^2 = z⁻¹ := by
  rw [div_pow, mul_pow, hsq]
  rw [pow_add, pow_one]
  rw [show (z^g)^2 = z^(2*g) by ring]
  simp only [inv_pow]
  field_simp

lemma recover_parameter (g : ℕ) (h : ℂ → ℂ) (t : ℂ)
    (ht : t ≠ 0) (hu : h (t^2) ≠ 0) :
    h (((t⁻¹)^2)⁻¹) * ((t⁻¹)^2)^g / ((t⁻¹)^(2*g+1) * h (t^2)) = t := by
  rw [inv_pow, inv_inv]
  simp only [inv_pow, ← pow_mul]
  rw [pow_add, pow_one]
  field_simp

lemma parameter_recovery_coordinates (g : ℕ) (h : ℂ → ℂ) (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hsq : (h z⁻¹ * z^g / w)^2 = z⁻¹) :
    let t := h z⁻¹ * z^g / w
    (t⁻¹)^2 = z ∧ (t⁻¹)^(2*g+1) * h (t^2) = w := by
  dsimp only
  have ht : h z⁻¹ * z^g / w ≠ 0 := by
    intro ht
    simp [ht] at hsq
    exact hz hsq.symm
  have hH : h z⁻¹ ≠ 0 := by
    intro hH
    exact ht (by simp [hH])
  constructor
  · rw [inv_pow, hsq, inv_inv]
  · rw [hsq, pow_add, pow_one]
    rw [show (h z⁻¹ * z^g / w)⁻¹ ^ (2*g) = z^g by
      rw [pow_mul, inv_pow, hsq, inv_inv]]
    field_simp
    simp [hH]

lemma odd_substitution (P : Polynomial ℂ) (g : ℕ) (hd : P.natDegree = 2*g+1)
    (h : ℂ → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hsq : h (t^2)^2 = P.reverse.eval (t^2)) :
    h (t^2)^2 = t^(4*g+2) * P.eval ((t⁻¹)^2) := by
  rw [hsq, reverse_eval_eq P (t^2) (pow_ne_zero _ ht), hd]
  simp only [← inv_pow]
  congr 1
  ring

lemma odd_on_curve (P : Polynomial ℂ) (g : ℕ) (h : ℂ → ℂ) (t : ℂ)
    (ht : t ≠ 0)
    (hsq : h (t^2)^2 = t^(4*g+2) * P.eval ((t⁻¹)^2)) :
    ((t⁻¹)^(2*g+1) * h (t^2))^2 = P.eval ((t⁻¹)^2) := by
  rw [mul_pow, hsq]
  rw [show t^(4*g+2) = (t^(2*g+1))^2 by ring]
  simp [inv_pow, ht]

lemma inverse_square (P : Polynomial ℂ) (g : ℕ) (hd : P.natDegree = 2*g+1)
    (h : ℂ → ℂ) (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0)
    (heq : w^2 = P.eval z)
    (hsq : h z⁻¹^2 = P.reverse.eval z⁻¹) :
    (h z⁻¹ * z^g / w)^2 = z⁻¹ := by
  apply parameter_square g z w (h z⁻¹) hz hw
  rw [hsq, reverse_eval_eq P z⁻¹ (inv_ne_zero hz), hd, inv_inv, heq]

lemma inverse_ne_zero {k z : ℂ} (hz : z ≠ 0) (hsq : k^2 = z⁻¹) : k ≠ 0 := by
  intro hk
  simp [hk] at hsq
  exact hz hsq.symm

lemma inverse_mem_disk {k z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ 0)
    (hbound : ‖z⁻¹‖ < r^2) (hsq : k^2 = z⁻¹) : k ≠ 0 ∧ ‖k‖ < r := by
  refine ⟨inverse_ne_zero hz hsq, ?_⟩
  apply (sq_lt_sq₀ (norm_nonneg k) hr.le).mp
  rw [← norm_pow, hsq]
  exact hbound

lemma exterior_w_nonzero (P : Polynomial ℂ) (h : ℂ → ℂ) (z w : ℂ)
    (hz : z ≠ 0) (heq : w^2 = P.eval z)
    (hsq : h z⁻¹^2 = P.reverse.eval z⁻¹) (hnz : h z⁻¹ ≠ 0) : w ≠ 0 := by
  intro hw
  have hP : P.eval z = 0 := by rw [← heq, hw]; simp
  have hH : h z⁻¹ ^ 2 = 0 := by
    rw [hsq, reverse_eval_eq P z⁻¹ (inv_ne_zero hz), inv_inv, hP, mul_zero]
  exact hnz (eq_zero_of_pow_eq_zero hH)

lemma parameter_mem_exterior {t : ℂ} {r : ℝ} (hr : 0 < r)
    (ht : t ≠ 0) (htlt : ‖t‖ < r) :
    (t⁻¹)^2 ≠ 0 ∧ ‖(((t⁻¹)^2)⁻¹)‖ < r^2 := by
  refine ⟨pow_ne_zero _ (inv_ne_zero ht), ?_⟩
  rw [← inv_pow, inv_inv, norm_pow]
  exact (sq_lt_sq₀ (norm_nonneg t) hr.le).mpr htlt

lemma odd_parameter_injective (g : ℕ) (h : ℂ → ℂ) (S : Set ℂ)
    (hS0 : ∀ t ∈ S, t ≠ 0) (hSh : ∀ t ∈ S, h (t^2) ≠ 0) :
    Set.InjOn (fun t => ((t⁻¹)^2, (t⁻¹)^(2*g+1)* h (t^2))) S := by
  intro t ht s hs heq
  have hz : (t⁻¹)^2 = (s⁻¹)^2 := congrArg Prod.fst heq
  have hw : (t⁻¹)^(2*g+1)* h (t^2) = (s⁻¹)^(2*g+1)* h (s^2) := congrArg Prod.snd heq
  calc
    t = h (((t⁻¹)^2)⁻¹) * ((t⁻¹)^2)^g / ((t⁻¹)^(2*g+1) * h (t^2)) :=
      (recover_parameter g h t (hS0 t ht) (hSh t ht)).symm
    _ = h (((s⁻¹)^2)⁻¹) * ((s⁻¹)^2)^g / ((s⁻¹)^(2*g+1) * h (s^2)) := by rw [hz, hw]
    _ = s := recover_parameter g h s (hS0 s hs) (hSh s hs)



universe u

/-- Coordinate expressions suffice to compare the actual overlap maps. -/
theorem compatible_of_coordinate_formulas {X : Type u} [TopologicalSpace X]
    (z w : X → ℂ) (c e : Surfaces.ComplexChart X)
    (h : ℂ → ℂ) (U : Set ℂ) (g : ℕ)
    (hh : HolomorphicOn U h)
    (hc : ∀ q ∈ c.val.source, c.val q = h ((z q)⁻¹) * (z q)^g / w q)
    (hc_z_ne : ∀ q ∈ c.val.source, z q ≠ 0)
    (hc_w_ne : ∀ q ∈ c.val.source, w q ≠ 0)
    (hc_in : ∀ q ∈ c.val.source, (z q)⁻¹ ∈ U)
    (hc_z : HolomorphicOn c.val.target (fun t => z (c.val.symm t)))
    (hc_w : HolomorphicOn c.val.target (fun t => w (c.val.symm t)))
    (he_coord : (∀ q ∈ e.val.source, e.val q = z q) ∨
      (∀ q ∈ e.val.source, e.val q = w q))
    (he_z : HolomorphicOn e.val.target (fun t => z (e.val.symm t)))
    (he_w : HolomorphicOn e.val.target (fun t => w (e.val.symm t))) :
    Surfaces.CompatibleCharts c e := by
  let tr := c.val.symm.trans e.val
  change BiholomorphicPair tr.source tr.target tr tr.symm
  refine ⟨⟨tr.open_source, ?_⟩, ⟨tr.open_target, ?_⟩,
    tr.mapsTo, tr.symm.mapsTo, tr.leftInvOn, tr.rightInvOn⟩
  · intro t ht
    have ht' : t ∈ c.val.target ∧ c.val.symm t ∈ e.val.source := ht
    rcases he_coord with he | he
    · apply (hc_z.2 t ht'.1).congr_of_eventuallyEq
      filter_upwards [tr.open_source.mem_nhds ht] with s hs
      exact he _ hs.2
    · apply (hc_w.2 t ht'.1).congr_of_eventuallyEq
      filter_upwards [tr.open_source.mem_nhds ht] with s hs
      exact he _ hs.2
  · intro t ht
    have ht' : t ∈ e.val.target ∧ e.val.symm t ∈ c.val.source := ht
    have hd_z := he_z.2 t ht'.1
    have hd_w := he_w.2 t ht'.1
    have hd_h := (hh.2 _ (hc_in _ ht'.2)).comp t (hd_z.inv (hc_z_ne _ ht'.2))
    have hd := (hd_h.mul (hd_z.pow g)).div hd_w (hc_w_ne _ ht'.2)
    apply hd.congr_of_eventuallyEq
    filter_upwards [tr.open_target.mem_nhds ht] with s hs
    exact hc _ hs.2

/-- The inverse chart coordinates are holomorphic on its punctured target. -/
theorem inverse_coordinate_holomorphy {X : Type u} [TopologicalSpace X]
    (z w : X → ℂ) (c : Surfaces.ComplexChart X)
    (h : ℂ → ℂ) (U : Set ℂ) (g : ℕ)
    (hh : HolomorphicOn U h)
    (ht_ne : ∀ t ∈ c.val.target, t ≠ 0)
    (ht_in : ∀ t ∈ c.val.target, t^2 ∈ U)
    (hz : ∀ t ∈ c.val.target, z (c.val.symm t) = (t⁻¹)^2)
    (hw : ∀ t ∈ c.val.target,
      w (c.val.symm t) = (t⁻¹)^(2*g+1) * h (t^2)) :
    HolomorphicOn c.val.target (fun t => z (c.val.symm t)) ∧
      HolomorphicOn c.val.target (fun t => w (c.val.symm t)) := by
  constructor
  · refine ⟨c.val.open_target, fun t ht => ?_⟩
    apply ((differentiableAt_id.inv (ht_ne t ht)).pow 2).congr_of_eventuallyEq
    filter_upwards [c.val.open_target.mem_nhds ht] with s hs
    exact hz s hs
  · refine ⟨c.val.open_target, fun t ht => ?_⟩
    have hd_h := (hh.2 _ (ht_in t ht)).comp t ((differentiableAt_id : DifferentiableAt ℂ (fun t : ℂ => t) t).pow 2)
    have hd := ((differentiableAt_id.inv (ht_ne t ht)).pow (2*g+1)).mul hd_h
    apply hd.congr_of_eventuallyEq
    filter_upwards [c.val.open_target.mem_nhds ht] with s hs
    exact hw s hs

/-- Specialization to the odd parameter and the exact affine coordinate charts. -/
theorem odd_chart_compatible {P : Polynomial ℂ} (g : ℕ)
    (c e : Surfaces.ComplexChart (AffineCurve P)) (h : ℂ → ℂ) (R r : ℝ)
    (hh : HolomorphicOn (Metric.ball 0 R) h)
    (hrR : r ^ 2 ≤ R)
    (hsquare : ∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R)
    (hsource : c.val.source = exterior P r)
    (htarget : c.val.target = puncturedDisk r)
    (hc : ∀ q ∈ exterior P r,
      c.val q = h (q.val.1⁻¹) * q.val.1^g / q.val.2)
    (hw_ne : ∀ q ∈ exterior P r, q.val.2 ≠ 0)
    (hz : ∀ t ∈ puncturedDisk r, (c.val.symm t).val.1 = (t⁻¹)^2)
    (hw : ∀ t ∈ puncturedDisk r,
      (c.val.symm t).val.2 = (t⁻¹)^(2*g+1) * h (t^2))
    (he : GoodCoordinateChart e) :
    Surfaces.CompatibleCharts c e := by
  have hne : ∀ t ∈ c.val.target, t ≠ 0 := fun t ht => (htarget ▸ ht).1
  have hin : ∀ t ∈ c.val.target, t ^ 2 ∈ Metric.ball 0 R := by
    intro t ht
    apply hsquare t
    have htr := (htarget ▸ ht).2
    simpa only [Metric.mem_ball, dist_zero_right] using htr
  have hcoords := inverse_coordinate_holomorphy
    (fun q : AffineCurve P => q.val.1) (fun q => q.val.2) c h (Metric.ball 0 R) g hh
    hne hin (fun t ht => hz t (htarget ▸ ht)) (fun t ht => hw t (htarget ▸ ht))
  apply compatible_of_coordinate_formulas
    (fun q : AffineCurve P => q.val.1) (fun q => q.val.2) c e h (Metric.ball 0 R) g hh
    (fun q hq => hc q (hsource ▸ hq)) (fun q hq => (hsource ▸ hq).1)
    (fun q hq => hw_ne q (hsource ▸ hq)) ?_ hcoords.1 hcoords.2 he.1 he.2.1 he.2.2
  intro q hq
  have hqr := (hsource ▸ hq).2
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hqr hrR



lemma puncturedDisk_isDomain {r : ℝ} (hr : 0 < r) : IsDomain (puncturedDisk r) := by
  let B := OpenPartialHomeomorph.univBall (0 : ℂ) r
  have hsrc : B.source = Set.univ := OpenPartialHomeomorph.univBall_source _ _
  have htgt : B.target = Metric.ball 0 r := OpenPartialHomeomorph.univBall_target _ hr
  have hB0 : B 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have hdim : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hc : IsConnected ({0}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank hdim 0
  have hc' : IsConnected (B '' ({0}ᶜ : Set ℂ)) := hc.image B
    (OpenPartialHomeomorph.continuous_univBall (0 : ℂ) r).continuousOn
  have himg : B '' ({0}ᶜ : Set ℂ) = puncturedDisk r := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, ?_⟩
      · intro hs0
        have hs' : s = 0 := B.injOn (by rw [hsrc]; trivial) (by rw [hsrc]; trivial)
          (hs0.trans hB0.symm)
        exact hs hs'
      · have h := B.mapsTo (show s ∈ B.source by rw [hsrc]; trivial)
        rw [htgt] at h
        simpa only [Metric.mem_ball, dist_zero_right] using h
    · intro ht
      have htt : t ∈ B.target := by
        rw [htgt]
        simpa only [Metric.mem_ball, dist_zero_right] using ht.2
      refine ⟨B.symm t, ?_, B.right_inv htt⟩
      intro hinv0
      apply ht.1
      rw [← B.right_inv htt, hinv0, hB0]
  rw [himg] at hc'
  exact ⟨hc'.nonempty, (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)),
    hc'.isPreconnected⟩

lemma exterior_isOpen (P : Polynomial ℂ) (r : ℝ) : IsOpen (exterior P r) := by
  have hz : Continuous (fun q : AffineCurve P => q.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hn : IsOpen {q : AffineCurve P | q.val.1 ≠ 0} := (isOpen_ne.preimage hz)
  have hi : ContinuousOn (fun q : AffineCurve P => ‖q.val.1⁻¹‖)
      {q | q.val.1 ≠ 0} := (hz.continuousOn.inv₀ (fun _ hq => hq)).norm
  exact hi.isOpen_inter_preimage hn isOpen_Iio

lemma inverseParameter_continuousOn {P : Polynomial ℂ} (g : ℕ)
    (h : ℂ → ℂ) (R r : ℝ)
    (hh : HolomorphicOn (Metric.ball 0 R) h) (hrR : r ^ 2 ≤ R)
    (hw : ∀ q ∈ exterior P r, q.val.2 ≠ 0) :
    ContinuousOn (fun q : AffineCurve P => h (q.val.1⁻¹) * q.val.1^g / q.val.2)
      (exterior P r) := by
  have hz : Continuous (fun q : AffineCurve P => q.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h_w : Continuous (fun q : AffineCurve P => q.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hi : ContinuousOn (fun q : AffineCurve P => q.val.1⁻¹) (exterior P r) :=
    hz.continuousOn.inv₀ (fun _ hq => hq.1)
  have hhcont : ContinuousOn h (Metric.ball 0 R) := fun s hs =>
    (hh.2 s hs).continuousAt.continuousWithinAt
  have hd : MapsTo (fun q : AffineCurve P => q.val.1⁻¹) (exterior P r) (Metric.ball 0 R) := by
    intro q hq
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hq.2 hrR
  exact ((hhcont.comp hi hd).mul (hz.continuousOn.pow g)).div h_w.continuousOn hw



/-- Build the partial homeomorphism from the explicit inverse and the parameter
formula. The total extension outside the punctured disk is irrelevant to the chart. -/
lemma exists_parameter_chart (P : Polynomial ℂ) (g : ℕ)
    (hd : P.natDegree = 2 * g + 1) (h : ℂ → ℂ) (R r : ℝ)
    (hr : 0 < r) (hrR : r ^ 2 ≤ R)
    (hh : HolomorphicOn (Metric.ball 0 R) h)
    (hne : ∀ s ∈ Metric.ball 0 R, h s ≠ 0)
    (hroot : ∀ s ∈ Metric.ball 0 R, h s ^ 2 = P.reverse.eval s)
    (hsquare : ∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R)
    (hD : IsDomain (puncturedDisk r)) :
    ∃ c : Surfaces.ComplexChart (AffineCurve P),
      c.val.source = exterior P r ∧ c.val.target = puncturedDisk r ∧
      (∀ q ∈ exterior P r, c.val q = h (q.val.1⁻¹) * q.val.1 ^ g / q.val.2) ∧
      (∀ t ∈ puncturedDisk r, (c.val.symm t).val.1 = (t⁻¹)^2) ∧
      (∀ t ∈ puncturedDisk r,
        (c.val.symm t).val.2 = (t⁻¹)^(2*g+1) * h (t^2)) := by
  classical
  have hin : ∀ q ∈ exterior P r, q.val.1⁻¹ ∈ Metric.ball 0 R := by
    intro q hq
    simpa only [Metric.mem_ball, dist_zero_right] using hq.2.trans_le hrR
  have hw : ∀ q ∈ exterior P r, q.val.2 ≠ 0 := by
    intro q hq
    exact exterior_w_nonzero P h q.val.1 q.val.2 hq.1 q.property
      (hroot _ (hin q hq)) (hne _ (hin q hq))
  let k : AffineCurve P → ℂ := fun q => h (q.val.1⁻¹) * q.val.1 ^ g / q.val.2
  have hksq : ∀ q ∈ exterior P r, k q ^ 2 = q.val.1⁻¹ := by
    intro q hq
    exact inverse_square P g hd h q.val.1 q.val.2 hq.1 (hw q hq)
      q.property (hroot _ (hin q hq))
  have hkmap : MapsTo k (exterior P r) (puncturedDisk r) := by
    intro q hq
    exact inverse_mem_disk hr hq.1 hq.2 (hksq q hq)
  have hsquare' : ∀ t ∈ puncturedDisk r, t ^ 2 ∈ Metric.ball 0 R := by
    intro t ht
    exact hsquare t (by simpa only [Metric.mem_ball, dist_zero_right] using ht.2)
  have hcurve : ∀ t ∈ puncturedDisk r,
      ((t⁻¹)^(2*g+1) * h (t^2))^2 = P.eval ((t⁻¹)^2) := by
    intro t ht
    exact odd_on_curve P g h t ht.1
      (odd_substitution P g hd h t ht.1 (hroot _ (hsquare' t ht)))
  let theta : puncturedDisk r → AffineCurve P := fun t =>
    ⟨((t.val⁻¹)^2, (t.val⁻¹)^(2*g+1) * h (t.val^2)), hcurve t t.property⟩
  have hthetamap : ∀ t : puncturedDisk r, theta t ∈ exterior P r := by
    intro t
    exact parameter_mem_exterior hr t.property.1 t.property.2
  have hthetak : ∀ t : puncturedDisk r, k (theta t) = (t : ℂ) := by
    intro t
    exact recover_parameter g h t t.property.1 (hne _ (hsquare' t t.property))
  have hktheta : ∀ q (hq : q ∈ exterior P r), theta ⟨k q, hkmap hq⟩ = q := by
    intro q hq
    apply Subtype.ext
    apply Prod.ext
    · exact (parameter_recovery_coordinates g h q.val.1 q.val.2 hq.1 (hw q hq)
        (hksq q hq)).1
    · exact (parameter_recovery_coordinates g h q.val.1 q.val.2 hq.1 (hw q hq)
        (hksq q hq)).2
  have htheta : Continuous theta := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro t
    have hi : ContinuousAt (fun t : puncturedDisk r => (t : ℂ)⁻¹) t :=
      continuous_subtype_val.continuousAt.inv₀ t.property.1
    have hh' : ContinuousAt (fun t : puncturedDisk r => h ((t : ℂ)^2)) t :=
      ContinuousAt.comp (f := fun s : puncturedDisk r => (s : ℂ)^2) (x := t)
        (hh.2 _ (hsquare' t t.property)).continuousAt
        (continuous_subtype_val.continuousAt.pow 2)
    exact (hi.pow 2).prodMk ((hi.pow (2*g+1)).mul hh')
  obtain ⟨t₀, ht₀⟩ := hD.1
  let v : ℂ → AffineCurve P := fun t =>
    if ht : t ∈ puncturedDisk r then theta ⟨t, ht⟩ else theta ⟨t₀, ht₀⟩
  have hv : ∀ t (ht : t ∈ puncturedDisk r), v t = theta ⟨t, ht⟩ := by
    intro t ht
    simp only [v, dite_eq_left ht]
  have hvcont : ContinuousOn v (puncturedDisk r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert htheta using 1
    funext t
    exact hv t t.property
  let c : OpenPartialHomeomorph (AffineCurve P) ℂ :=
    { toFun := k
      invFun := v
      source := exterior P r
      target := puncturedDisk r
      map_source' := hkmap
      map_target' := fun t ht => by rw [hv t ht]; exact hthetamap _
      left_inv' := fun q hq => by rw [hv (k q) (hkmap hq)]; exact hktheta q hq
      right_inv' := fun t ht => by rw [hv t ht]; exact hthetak _
      continuousOn_toFun := inverseParameter_continuousOn g h R r hh hrR hw
      continuousOn_invFun := hvcont
      open_source := exterior_isOpen P r
      open_target := hD.2.1 }
  refine ⟨⟨c, hD⟩, rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro t ht
    change (v t).val.1 = (t⁻¹)^2
    rw [hv t ht]
  · intro t ht
    change (v t).val.2 = (t⁻¹)^(2*g+1) * h (t^2)
    rw [hv t ht]


lemma theta_openEmbedding {P : Polynomial ℂ} {r : ℝ}
    (c : Surfaces.ComplexChart (AffineCurve P))
    (ht : c.val.target = puncturedDisk r) :
    Topology.IsOpenEmbedding (fun t : puncturedDisk r => c.val.symm t) := by
  have he := c.val.symm.isOpenEmbedding_restrict
  change Topology.IsOpenEmbedding (fun t : c.val.target => c.val.symm t) at he
  rw [ht] at he
  exact he

lemma theta_range {P : Polynomial ℂ} {r : ℝ}
    (c : Surfaces.ComplexChart (AffineCurve P))
    (hs : c.val.source = exterior P r) (ht : c.val.target = puncturedDisk r) :
    Set.range (fun t : puncturedDisk r => c.val.symm t) = exterior P r := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    rw [← hs]
    exact c.val.map_target (by rw [ht]; exact t.property)
  · intro hq
    have hqs : q ∈ c.val.source := by rwa [hs]
    refine ⟨⟨c.val q, ?_⟩, c.val.left_inv hqs⟩
    rw [← ht]
    exact c.val.map_source hqs

lemma exterior_connected {P : Polynomial ℂ} {r : ℝ}
    (c : Surfaces.ComplexChart (AffineCurve P))
    (hs : c.val.source = exterior P r) :
    IsConnected (exterior P r) := by
  have hc : IsConnected c.val.target := ⟨c.property.1, c.property.2.2⟩
  have hi := hc.image c.val.symm c.val.symm.continuousOn
  change IsConnected (c.val.symm '' c.val.symm.source) at hi
  rw [c.val.symm.image_source_eq_target] at hi
  change IsConnected c.val.source at hi
  rwa [hs] at hi

lemma inverse_base {P : Polynomial ℂ} {r : ℝ}
    (c : Surfaces.ComplexChart (AffineCurve P))
    (hz : ∀ t ∈ puncturedDisk r, (c.val.symm t).val.1 = (t⁻¹) ^ 2) :
    ∀ t ∈ puncturedDisk r, ((c.val.symm t).val.1)⁻¹ = t ^ 2 := by
  intro t ht
  rw [hz t ht, ← inv_pow, inv_inv]

lemma base_analytic : AnalyticAt ℂ (fun t : ℂ => t ^ 2) 0 := by
  exact analyticAt_id.pow 2



/-- The single punctured parameter disk exhausts the whole odd-degree exterior.
Its reciprocal base coordinate extends across its one center with order two. -/
theorem exists_odd_end : Specs.D12Complex.Ch21.HyperellipticOddEnd.exists_odd_end_type := by
  intro P g _hPsf hd
  have hP : P ≠ 0 := by
    intro hp
    simp only [hp, Polynomial.natDegree_zero] at hd
    omega
  obtain ⟨R, r, h, hR, hr, hrR, hh, hroot, hzero, hlead, hsquare, hu, heven, hu_props⟩ :=
    exists_even_local_sqrt P hP
  have hne : ∀ s ∈ Metric.ball 0 R, h s ≠ 0 := fun s hs => (hroot s hs).1
  have hsqrt : ∀ s ∈ Metric.ball 0 R, h s ^ 2 = P.reverse.eval s :=
    fun s hs => (hroot s hs).2
  have hwne : ∀ q ∈ exterior P r, q.val.2 ≠ 0 := by
    intro q hq
    have hin : q.val.1⁻¹ ∈ Metric.ball 0 R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hq.2.trans_le hrR
    exact exterior_w_nonzero P h q.val.1 q.val.2 hq.1 q.property
      (hsqrt _ hin) (hne _ hin)
  obtain ⟨c, hcs, hct, hc, hcz, hcw⟩ :=
    exists_parameter_chart P g hd h R r hr hrR hh hne hsqrt hsquare (puncturedDisk_isDomain hr)
  have hcoords := inverse_coordinate_holomorphy
    (fun q : AffineCurve P => q.val.1) (fun q => q.val.2) c h (Metric.ball 0 R) g hh
    (fun t ht => (hct ▸ ht).1)
    (fun t ht => hsquare t (by
      have htr := (hct ▸ ht).2
      simpa only [Metric.mem_ball, dist_zero_right] using htr))
    (fun t ht => hcz t (hct ▸ ht)) (fun t ht => hcw t (hct ▸ ht))
  refine ⟨{
    R := R
    r := r
    R_pos := hR
    r_pos := hr
    radius_le := hrR
    h := h
    h_holomorphic := hh
    h_nonzero := hne
    h_square := hsqrt
    h_zero_square := hzero
    leadingCoeff_ne_zero := hlead
    square_maps := hsquare
    u_holomorphic := hu
    u_even := heven
    u_nonzero := fun t ht => (hu_props t ht).1
    u_square := fun t ht => (hu_props t ht).2
    u_substitution := ?_
    exterior_w_nonzero := hwne
    chart := c
    chart_source := hcs
    chart_target := hct
    chart_apply := hc
    chart_symm_z := hcz
    chart_symm_w := hcw
    inverse_coordinates_holomorphic := by simpa only [hct] using hcoords
    compatible := fun e he => odd_chart_compatible g c e h R r hh hrR hsquare
      hcs hct hc hwne hcz hcw he
    theta := fun t => c.val.symm t
    theta_eq := fun _ => rfl
    theta_openEmbedding := theta_openEmbedding c hct
    theta_range := theta_range c hcs hct
    exterior_connected := exterior_connected c hcs
    inverse_base := inverse_base c hcz
    base_analytic := base_analytic
    base_order := square_order }⟩
  intro t ht
  apply odd_substitution P g hd h t ht.1
  exact hsqrt _ (hsquare t (by simpa only [Metric.mem_ball, dist_zero_right] using ht.2))

end D12Complex.HyperellipticOddEnd
