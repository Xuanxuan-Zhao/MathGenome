import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Joukowski
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.AlgebraicClosure
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The Joukowski biholomorphism (paper.tex:2354–2361).

An arbitrary quadratic root exists by the accepted algebraic-closure theorem.
Inversion gives the reciprocal root. The unit circle maps to the closed real
segment, while every root above that segment has unit modulus. Thus exactly
one root is in the exterior. The accepted local inverse theorem then proves
holomorphy of the globally chosen inverse by local agreement.

Finally squareRoot(w) := inverse(w) - w. Its square and its normalization at
infinity follow algebraically from map(inverse(w)) = w. In particular, no
pre-existing global square root of w² - 1 is used.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Joukowski

/- The canonical objects live in the independent Spec; these exports verify
their prescribed values without introducing different mathematical objects. -/
abbrev map_export : Specs.D12Complex.Ch10.Joukowski.map_type := map
abbrev exterior_export : Specs.D12Complex.Ch10.Joukowski.exterior_type := exterior
abbrev slitPlane_export : Specs.D12Complex.Ch10.Joukowski.slitPlane_type := slitPlane
abbrev inverse_export : Specs.D12Complex.Ch10.Joukowski.inverse_type := inverse
abbrev squareRoot_export : Specs.D12Complex.Ch10.Joukowski.squareRoot_type := squareRoot

lemma exterior_ne_zero {z : ℂ} (hz : z ∈ exterior) : z ≠ 0 := by
  intro h
  norm_num [exterior, h] at hz

lemma isOpen_exterior : IsOpen exterior := isOpen_lt continuous_const continuous_norm

lemma isOpen_slitPlane : IsOpen slitPlane := by
  exact ((isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))).isOpen_compl

lemma map_eq_iff_quadratic {z w : ℂ} (hz : z ≠ 0) :
    map z = w ↔ z^2 - 2*w*z + 1 = 0 := by
  unfold map
  constructor <;> intro h
  · field_simp at h
    linear_combination h
  · apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    apply (mul_right_cancel₀ hz)
    field_simp
    linear_combination h

lemma map_inv (z : ℂ) : map z⁻¹ = map z := by simp [map, add_comm]

lemma unit_map_segment {z : ℂ} (hz : ‖z‖ = 1) :
    (map z).im = 0 ∧ -1 ≤ (map z).re ∧ (map z).re ≤ 1 := by
  have hn : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hi : z⁻¹ = star z := by
    apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, hn]
  have hm : map z = (z.re : ℂ) := by
    rw [map, hi]
    apply Complex.ext <;> simp
  rw [hm]
  have hb := Complex.abs_re_le_norm z
  simpa [hz, abs_le] using hb

lemma segment_root_unit {w z : ℂ}
    (hw : w.im = 0 ∧ -1 ≤ w.re ∧ w.re ≤ 1)
    (hz : z^2 - 2*w*z + 1 = 0) : ‖z‖ = 1 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [Complex.mul_re, Complex.mul_im, pow_two, hw.1] at hr hi
  have hprod : z.im * (z.re - w.re) = 0 := by nlinarith [hi]
  have ha : w.re^2 ≤ 1 := by nlinarith [hw.2.1, hw.2.2]
  have hs : z.re^2 + z.im^2 = 1 := by
    rcases mul_eq_zero.mp hprod with hy | hx
    · have hx : z.re = w.re := by nlinarith [sq_nonneg (z.re - w.re)]
      nlinarith
    · have hx' : z.re = w.re := sub_eq_zero.mp hx
      nlinarith
  have hn : ‖z‖^2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [hs]
  nlinarith [norm_nonneg z]

lemma mapsTo : Set.MapsTo map exterior slitPlane := by
  intro z hz hw
  have hu := segment_root_unit hw ((map_eq_iff_quadratic (exterior_ne_zero hz)).mp rfl)
  exact (ne_of_gt hz) hu

lemma injOn : Set.InjOn map exterior := by
  intro z hz u hu h
  have hq := (map_eq_iff_quadratic (exterior_ne_zero hz)).mp h
  have hq' := (map_eq_iff_quadratic (exterior_ne_zero hu)).mp (Eq.refl (map u))
  have hp : (z-u)*(z*u-1) = 0 := by
    linear_combination u * hq - z * hq'
  rcases mul_eq_zero.mp hp with he | he
  · exact sub_eq_zero.mp he
  · have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_mul, norm_one] at hn
    have hm : 1 < ‖z‖ * ‖u‖ := one_lt_mul (le_of_lt hz) hu
    linarith

lemma exists_quadratic_root (w : ℂ) : ∃ z : ℂ, z^2 - 2*w*z + 1 = 0 := by
  let P : Polynomial ℂ := Polynomial.X^2 - Polynomial.C (2*w)*Polynomial.X + 1
  have hP : 0 < P.natDegree := by
    have hc : P.coeff 2 = 1 := by norm_num [P, Polynomial.coeff_one]
    have hn := Polynomial.le_natDegree_of_ne_zero (show P.coeff 2 ≠ 0 by rw [hc]; norm_num)
    omega
  obtain ⟨z, hz⟩ := AlgebraicClosure.polynomial_exists_root_of_natDegree_pos P hP
  exact ⟨z, by simpa [P] using hz⟩

lemma surjOn : Set.SurjOn map exterior slitPlane := by
  intro w hw
  obtain ⟨z, hz⟩ := exists_quadratic_root w
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hm : map z = w := (map_eq_iff_quadratic hz0).mpr hz
  have hn : ‖z‖ ≠ 1 := by
    intro h
    exact hw (hm ▸ unit_map_segment h)
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ⟨z⁻¹, ?_, (map_inv z).trans hm⟩
    change 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hlt
  · exact ⟨z, hgt, hm⟩

lemma hasDerivAt_map {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt map ((1 - (z^2)⁻¹) / 2) z := by
  change HasDerivAt (fun x : ℂ => (x + x⁻¹) / 2) _ z
  simpa only [Pi.add_apply, id_eq, sub_eq_add_neg] using
    ((hasDerivAt_id z).add (hasDerivAt_inv hz)).div_const 2

lemma holomorphic_map : HolomorphicOn exterior map :=
  ⟨isOpen_exterior, fun _ hz => (hasDerivAt_map (exterior_ne_zero hz)).differentiableAt⟩

lemma deriv_map_ne_zero {z : ℂ} (hz : z ∈ exterior) : deriv map z ≠ 0 := by
  rw [(hasDerivAt_map (exterior_ne_zero hz)).deriv]
  intro h
  have hi : (z^2)⁻¹ = 1 := by
    have h' := (div_eq_zero_iff.mp h).resolve_right (by norm_num : (2 : ℂ) ≠ 0)
    linear_combination -h'
  have hp : z^2 = 1 := inv_injective (by simpa using hi)
  have hn := congrArg norm hp
  simp only [norm_pow, norm_one] at hn
  change 1 < ‖z‖ at hz
  nlinarith

lemma inverse_mem {w : ℂ} (hw : w ∈ slitPlane) : inverse w ∈ exterior :=
  surjOn.mapsTo_invFunOn hw

lemma map_inverse {w : ℂ} (hw : w ∈ slitPlane) : map (inverse w) = w :=
  surjOn.rightInvOn_invFunOn hw

lemma inverse_map {z : ℂ} (hz : z ∈ exterior) : inverse (map z) = z :=
  injOn.leftInvOn_invFunOn hz

/-- At each target point the chosen global inverse agrees with the local
holomorphic inverse. This uses uniqueness on the whole exterior. -/
lemma holomorphic_inverse : HolomorphicOn slitPlane inverse := by
  refine ⟨isOpen_slitPlane, ?_⟩
  intro w hw
  obtain ⟨U, V, g, haU, hwV, hU, hpair, _, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse exterior map (inverse w)
      holomorphic_map (inverse_mem hw) (deriv_map_ne_zero (inverse_mem hw))
  rw [map_inverse hw] at hwV
  rcases hpair with ⟨_, hg, _, hgm, _, hgr⟩
  have heq : inverse =ᶠ[𝓝 w] g := by
    filter_upwards [hg.1.mem_nhds hwV, isOpen_slitPlane.mem_nhds hw] with v hv hvs
    exact injOn (inverse_mem hvs) (hU (hgm hv)) ((map_inverse hvs).trans (hgr hv).symm)
  exact (hg.2 w hwV).congr_of_eventuallyEq heq

/-- The full biholomorphism, using the project's canonical weak holomorphy. -/
theorem biholomorphic_pair : Specs.D12Complex.Ch10.Joukowski.biholomorphic_pair_type :=
  ⟨holomorphic_map, holomorphic_inverse, mapsTo, fun _ hw => inverse_mem hw,
    fun _ hz => inverse_map hz, fun _ hw => map_inverse hw⟩

theorem unique_quadratic_root :
    Specs.D12Complex.Ch10.Joukowski.unique_quadratic_root_type := by
  intro w hw
  refine ⟨inverse_mem hw,
    (map_eq_iff_quadratic (exterior_ne_zero (inverse_mem hw))).mp (map_inverse hw), ?_⟩
  intro z hz hq
  exact injOn hz (inverse_mem hw)
    (((map_eq_iff_quadratic (exterior_ne_zero hz)).mpr hq).trans (map_inverse hw).symm)

lemma holomorphic_squareRoot : HolomorphicOn slitPlane squareRoot := by
  exact ⟨isOpen_slitPlane, fun w hw => (holomorphic_inverse.2 w hw).sub (differentiableAt_id)⟩

lemma squareRoot_sq {w : ℂ} (hw : w ∈ slitPlane) : squareRoot w ^ 2 = w^2 - 1 := by
  have hq := (unique_quadratic_root w hw).2.1
  dsimp [squareRoot]
  linear_combination hq

lemma inverse_formula (w : ℂ) : inverse w = w + squareRoot w := by
  simp [squareRoot]

lemma norm_le_one_of_segment {w : ℂ}
    (hw : w.im = 0 ∧ -1 ≤ w.re ∧ w.re ≤ 1) : ‖w‖ ≤ 1 := by
  have heq : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw.1]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr hw.2

lemma slitPlane_of_norm_gt_one {w : ℂ} (hw : 1 < ‖w‖) : w ∈ slitPlane := by
  intro hs
  exact (not_le_of_gt hw) (norm_le_one_of_segment hs)

lemma squareRoot_sub_eq {w : ℂ} (hw : w ∈ slitPlane) :
    squareRoot w - w = -(inverse w)⁻¹ := by
  have hm := map_inverse hw
  dsimp [map] at hm
  dsimp [squareRoot]
  linear_combination 2 * hm

lemma squareRoot_asymptotic :
    Tendsto (fun w => squareRoot w / w) (cocompact ℂ) (𝓝 1) := by
  have hnorm : Tendsto (fun w : ℂ => ‖w‖⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
  have hsmall : Tendsto (fun w => squareRoot w / w - 1) (cocompact ℂ) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hnorm
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop 1] with w hw
    have hws := slitPlane_of_norm_gt_one hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw)
    have heq : squareRoot w / w - 1 = (squareRoot w - w) / w := by
      field_simp
    rw [heq, squareRoot_sub_eq hws, norm_div, norm_neg, norm_inv]
    have hi : ‖inverse w‖⁻¹ ≤ 1 :=
      le_of_lt (inv_lt_one_of_one_lt₀ (inverse_mem hws))
    simpa [one_div] using div_le_div_of_nonneg_right hi (norm_nonneg w)
  have h := hsmall.add_const 1
  simpa only [sub_add_cancel, zero_add] using h

/-- The root branch is defined from the proved inverse and has the required
normalization at infinity, rather than being postulated on the slit plane. -/
theorem inverse_squareRoot : Specs.D12Complex.Ch10.Joukowski.inverse_squareRoot_type :=
  ⟨holomorphic_squareRoot, fun w hw => ⟨squareRoot_sq hw, inverse_formula w⟩,
    squareRoot_asymptotic⟩

end D12Complex.Joukowski
