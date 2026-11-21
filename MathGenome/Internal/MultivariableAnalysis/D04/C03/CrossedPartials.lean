import MathGenome.Internal.MultivariableAnalysis.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.CrossedPartials
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter Topology Asymptotics
namespace D04

section Square
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A line derivative based at zero is also the derivative at any parameter
of the same affine line. -/
private theorem hasDerivAt_affine_line (f : X → Y) (b v : X) (s : ℝ) (d : Y)
    (hd : HasDirectionalDerivative f (b + s • v) v d) :
    HasDerivAt (fun r : ℝ => f (b + r • v)) d s := by
  have h := ((hasDirectionalDerivative_iff_hasDerivAt f (b + s • v) v d).mp hd).scomp_of_eq s
    ((hasDerivAt_id s).sub_const s) (by simp)
  convert h using 1
  · ext r
    dsimp [Function.comp_def, id_eq]
    congr 1
    module
  · simp

/-- A quantitative square estimate needs only derivatives along its horizontal
lines and a first-order remainder estimate for that partial map at the base. -/
private theorem square_increment_bound (f p : X → Y) (A : X →L[ℝ] Y)
    (a v w : X) (t ε δ : ℝ) (ht : 0 < t) (hε : 0 ≤ ε)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (htδ : 2 * t < δ)
    (hline : ∀ x, ‖x - a‖ < δ → HasDirectionalDerivative f x v (p x))
    (hrem : ∀ z, ‖z‖ < δ → ‖p (a + z) - p a - A z‖ ≤ ε * ‖z‖) :
    ‖f (a + t • v + t • w) - f (a + t • v) - f (a + t • w) + f a -
      (t ^ 2) • A w‖ ≤ 3 * ε * t ^ 2 := by
  let g : ℝ → Y := fun s => f (a + s • v + t • w) - f (a + s • v) -
    s • (t • A w)
  let g' : ℝ → Y := fun s => p (a + s • v + t • w) - p (a + s • v) - t • A w
  have hn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      ‖s • v‖ ≤ t ∧ ‖s • v + t • w‖ ≤ 2 * t := by
    have hs' : ‖s • v‖ ≤ t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact (mul_le_mul_of_nonneg_left hv hs.1).trans (by simpa using hs.2)
    refine ⟨hs', (norm_add_le _ _).trans ?_⟩
    have hw' : ‖t • w‖ ≤ t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      simpa using mul_le_mul_of_nonneg_left hw ht.le
    linarith
  have hg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : HasDerivAt g (g' s) s := by
    have h₁ : HasDerivAt (fun r : ℝ => f (a + r • v + t • w))
        (p (a + s • v + t • w)) s := by
      have hh := hasDerivAt_affine_line f (a + t • w) v s _
        (hline (a + t • w + s • v) (by
          have he : a + t • w + s • v - a = s • v + t • w := by module
          rw [he]
          exact (hn s hs).2.trans_lt htδ))
      convert hh using 1
      · funext r; congr 1; module
      · congr 1; module
    have h₂ := hasDerivAt_affine_line f a v s _ (hline (a + s • v) (by
      simpa using (hn s hs).1.trans_lt (by linarith : t < δ)))
    convert (h₁.sub h₂).sub ((hasDerivAt_id s).smul_const (t • A w)) using 1
    · funext r; rfl
    · simp [g']
  have hb (s : ℝ) (hs : s ∈ Ico (0 : ℝ) t) : ‖g' s‖ ≤ 3 * ε * t := by
    have hscc : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
    have h₁ := hrem (s • v + t • w) ((hn s hscc).2.trans_lt htδ)
    have h₂ := hrem (s • v) ((hn s hscc).1.trans_lt (by linarith : t < δ))
    have he : g' s = (p (a + (s • v + t • w)) - p a - A (s • v + t • w)) -
        (p (a + s • v) - p a - A (s • v)) := by
      simp only [g', add_assoc, map_add, map_smul]
      module
    rw [he]
    calc
      _ ≤ ‖p (a + (s • v + t • w)) - p a - A (s • v + t • w)‖ +
          ‖p (a + s • v) - p a - A (s • v)‖ := norm_sub_le _ _
      _ ≤ ε * ‖s • v + t • w‖ + ε * ‖s • v‖ := add_le_add h₁ h₂
      _ ≤ ε * (2 * t) + ε * t := add_le_add
        (mul_le_mul_of_nonneg_left (hn s hscc).2 hε)
        (mul_le_mul_of_nonneg_left (hn s hscc).1 hε)
      _ = 3 * ε * t := by ring
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hg s hs).hasDerivWithinAt) hb t ⟨ht.le, le_rfl⟩
  have he : g t - g 0 = f (a + t • v + t • w) - f (a + t • v) -
      f (a + t • w) + f a - (t ^ 2) • A w := by
    simp only [g, zero_smul, add_zero, smul_smul, pow_two]
    module
  rw [he] at hm
  simpa only [sub_zero, pow_two, mul_assoc] using hm

/-- Differentiability of two first line-derivative maps at one point forces
the corresponding crossed derivatives to agree. No total derivative of f
at neighboring points is used. -/
private theorem crossed_directional_derivatives (f p q : X → Y)
    (A B : X →L[ℝ] Y) (a v w : X) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hfirst : ∀ᶠ x in 𝓝 a,
      HasDirectionalDerivative f x v (p x) ∧ HasDirectionalDerivative f x w (q x))
    (hp : HasFDerivAt p A a) (hq : HasFDerivAt q B a) : A w = B v := by
  by_contra hne
  have hD : 0 < ‖A w - B v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let ε := ‖A w - B v‖ / 12
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨r, hr, hfirst⟩ := Metric.eventually_nhds_iff.mp hfirst
  obtain ⟨δp, hδp, hp⟩ := Metric.eventually_nhds_iff.mp
    (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hp) hε)
  obtain ⟨δq, hδq, hq⟩ := Metric.eventually_nhds_iff.mp
    (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hq) hε)
  let δ := min r (min δp δq)
  have hδ : 0 < δ := lt_min hr (lt_min hδp hδq)
  let t := δ / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : 2 * t < δ := by dsimp [t]; linarith
  have hd₁ : δ ≤ r := min_le_left _ _
  have hd₂ : δ ≤ δp := (min_le_right _ _).trans (min_le_left _ _)
  have hd₃ : δ ≤ δq := (min_le_right _ _).trans (min_le_right _ _)
  have hb₁ := square_increment_bound f p A a v w t ε δ ht hε.le hv hw htδ
    (fun x hx => (hfirst (by simpa [dist_eq_norm] using hx.trans_le hd₁)).1)
    (fun z hz => hp (by simpa [dist_eq_norm] using hz.trans_le hd₂))
  have hb₂ := square_increment_bound f q B a w v t ε δ ht hε.le hw hv htδ
    (fun x hx => (hfirst (by simpa [dist_eq_norm] using hx.trans_le hd₁)).2)
    (fun z hz => hq (by simpa [dist_eq_norm] using hz.trans_le hd₃))
  let Q := f (a + t • v + t • w) - f (a + t • v) - f (a + t • w) + f a
  change ‖Q - t ^ 2 • A w‖ ≤ 3 * ε * t ^ 2 at hb₁
  have hb₂' : ‖Q - t ^ 2 • B v‖ ≤ 3 * ε * t ^ 2 := by
    convert hb₂ using 1
    congr 1
    dsimp [Q]
    rw [show a + t • v + t • w = a + t • w + t • v by module]
    module
  have hb : ‖t ^ 2 • (A w - B v)‖ ≤ 6 * ε * t ^ 2 := calc
    _ = ‖(Q - t ^ 2 • B v) - (Q - t ^ 2 • A w)‖ := by congr 1; module
    _ ≤ ‖Q - t ^ 2 • B v‖ + ‖Q - t ^ 2 • A w‖ := norm_sub_le _ _
    _ ≤ 3 * ε * t ^ 2 + 3 * ε * t ^ 2 := add_le_add hb₂' hb₁
    _ = 6 * ε * t ^ 2 := by ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t), mul_comm] at hb
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp hb
  dsimp [ε] at hc
  linarith

end Square

/-- Pointwise crossed partials for finite-dimensional vector targets. The
square argument above is vector valued, so it also covers the empty target. -/
theorem crossed_partials {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U)
    (hfirst : ∃ V : Set (E n), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ i : Fin n, ∃ d, HasPartialDerivative f x i d)
    (hsecond : ∀ i : Fin n, TotalDifferentiableAt U (fun x => partialDerivative f x i) a)
    (i j : Fin n) :
    partialDerivative (fun x => partialDerivative f x i) a j =
      partialDerivative (fun x => partialDerivative f x j) a i := by
  obtain ⟨V, hV, haV, _, hfirst⟩ := hfirst
  obtain ⟨A, hA⟩ := hsecond i
  obtain ⟨B, hB⟩ := hsecond j
  rw [totalDerivative_partialDerivative U _ a A hA j,
    totalDerivative_partialDerivative U _ a B hB i]
  apply crossed_directional_derivatives f (fun x => partialDerivative f x i)
    (fun x => partialDerivative f x j) A B a (standardBasis n i) (standardBasis n j)
  · have hn : ‖standardBasis n i‖ = 1 := by
      simp [standardBasis]
    exact hn.le
  · have hn : ‖standardBasis n j‖ = 1 := by
      simp [standardBasis]
    exact hn.le
  · filter_upwards [hV.mem_nhds haV] with x hx
    have hp (k : Fin n) : HasDirectionalDerivative f x (standardBasis n k) (partialDerivative f x k) := by
      obtain ⟨d, hd⟩ := hfirst x hx k
      have he : partialDerivative f x k = d := directionalDerivative_eq f x _ d hd
      rw [he]
      exact hd
    exact ⟨hp i, hp j⟩
  · exact (hasTotalDerivative_iff_hasFDerivAt U _ A a hU ha).mp hA
  · exact (hasTotalDerivative_iff_hasFDerivAt U _ B a hU ha).mp hB

/-- Twice total differentiability supplies the main theorem's hypotheses by
continuous linear evaluation of the first differential on each basis vector.
There is no continuity assumption on the second differential. -/
theorem twiceDifferentiable_crossed_partials {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (hf : TimesDifferentiableAt 2 U f a)
    (i j : Fin n) :
    partialDerivative (fun x => partialDerivative f x i) a j =
      partialDerivative (fun x => partialDerivative f x j) a i := by
  have hdom := timesDifferentiableAt_domain 2 U f a hf
  obtain ⟨V, hV, haV, hVU, hlow, hd⟩ := hf
  have hdf (x : E n) (hx : x ∈ V) : TotalDifferentiableAt U f x :=
    (timesDifferentiableAt_one U f x).mp (hlow x hx)
  apply crossed_partials U f a hdom.1 hdom.2 _ _ i j
  · refine ⟨V, hV, haV, hVU, ?_⟩
    intro x hx k
    obtain ⟨A, hA⟩ := hdf x hx
    exact ⟨A (standardBasis n k), totalDerivative_hasPartialDerivative U f x A hA k⟩
  · intro k
    let ev : Differential (E n) (E m) 1 →L[ℝ] E m :=
      ContinuousMultilinearMap.apply ℝ _ _ (fun _ => standardBasis n k)
    have hev : DifferentiableAt ℝ (fun x => higherDifferential 1 f x (fun _ => standardBasis n k)) a :=
      ev.differentiableAt.comp a
        ((totalDifferentiableAt_iff_differentiableAt V _ a hV haV).mp hd)
    apply (totalDifferentiableAt_iff_differentiableAt U _ a hdom.1 hdom.2).mpr
    apply hev.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds haV] with x hx
    obtain ⟨A, hA⟩ := hdf x hx
    change partialDerivative f x k = iteratedFDeriv ℝ 1 f x (fun _ => standardBasis n k)
    rw [iteratedFDeriv_one_apply, totalDerivative_partialDerivative U f x A hA k]
    change A (standardBasis n k) = totalDerivative f x (standardBasis n k)
    rw [totalDerivative_eq U f A x hA]

end D04
