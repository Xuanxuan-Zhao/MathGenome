import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.VariableLocal
import MathGenome.Internal.LinearPDE.P201.Elliptic.ConstantSchauder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeightedInterpolation

/-! Local variable-coefficient Schauder estimates on balls and half-balls.
Coefficient freezing, close/far pair bounds, weighted interpolation and
exhaustion establish constants uniform in the fields, centers and scales.
The half-ball proof uses the genuine one-sided jets on the flat face. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201.Elliptic.VariableLocal
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.VariableLocal

/-- The genuine frozen source: the variable principal part is moved to the
right, as are the first- and zeroth-order terms. -/
def frozenSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ) (z : Space n)
    (x : Space n) : ℝ :=
  f x + (∑ i : Fin n, ∑ j : Fin n, (a z i j - a x i j) * secondPartial u i j x) -
    (∑ i : Fin n, b x i * firstPartial u i x) - c x * u x

/-- Freezing is an identity for the shared classical operator, with precisely
the source's sign convention and with no sign assumption on c. -/
theorem constantOperator_eq_frozenSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ) (z x : Space n)
    (h : nondivergenceOperator a b c u x = f x) :
    constantOperator (a z) u x = frozenSource a b c u f z x := by
  have hs : (∑ i : Fin n, ∑ j : Fin n,
      (a z i j - a x i j) * secondPartial u i j x) =
      constantOperator (a z) u x - constantOperator (a x) u x := by
    simp only [constantOperator, sub_mul, Finset.sum_sub_distrib]
  rw [frozenSource, hs]
  unfold nondivergenceOperator at h
  unfold constantOperator
  unfold constantOperator at hs
  linarith

/-- Pointwise product Hölder estimate with independent supremum and seminorm
bounds. Keeping these four constants separate preserves the small coefficient
oscillation needed for absorption. -/
theorem holder_product_bound {n : ℕ} {α Mv Mw Hv Hw : ℝ}
    {v w : Space n → ℝ} {x y : Space n}
    (hv : ‖v x‖ ≤ Mv) (hw : ‖w y‖ ≤ Mw)
    (hdv : ‖v x - v y‖ ≤ Hv * dist x y ^ α)
    (hdw : ‖w x - w y‖ ≤ Hw * dist x y ^ α) :
    ‖v x * w x - v y * w y‖ ≤
      (Mv * Hw + Mw * Hv) * dist x y ^ α := by
  have hMv : 0 ≤ Mv := (norm_nonneg _).trans hv
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans hw
  calc
    ‖v x * w x - v y * w y‖ =
        ‖v x * (w x - w y) + (v x - v y) * w y‖ := by congr 1; ring
    _ ≤ ‖v x * (w x - w y)‖ + ‖(v x - v y) * w y‖ := norm_add_le _ _
    _ = ‖v x‖ * ‖w x - w y‖ + ‖v x - v y‖ * ‖w y‖ := by rw [norm_mul, norm_mul]
    _ ≤ Mv * (Hw * dist x y ^ α) + (Hv * dist x y ^ α) * Mw := by
      exact add_le_add (mul_le_mul hv hdw (norm_nonneg _) hMv)
        (mul_le_mul hdv hw (norm_nonneg _) (le_trans (norm_nonneg _) hdv))
    _ = (Mv * Hw + Mw * Hv) * dist x y ^ α := by ring

/-- Bounded Hölder functions form an algebra for the actual all-pairs
Hölder condition used in the independent specifications. -/
theorem isHolderOn_mul {n : ℕ} {α : ℝ} {v w : Space n → ℝ}
    {s : Set (Space n)} (hv : IsHolderOn α v s) (hw : IsHolderOn α w s) :
    IsHolderOn α (fun x => v x * w x) s := by
  obtain ⟨Mv, Hv, hMv, hHv, hvs, hvh⟩ := hv
  obtain ⟨Mw, Hw, hMw, hHw, hws, hwh⟩ := hw
  refine ⟨Mv * Mw, Mv * Hw + Mw * Hv, mul_nonneg hMv hMw,
    add_nonneg (mul_nonneg hMv hHw) (mul_nonneg hMw hHv), ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul (hvs x hx) (hws x hx) (norm_nonneg _) hMv
  · intro x hx y hy
    exact holder_product_bound (hvs x hx) (hws y hy) (hvh x hx y hy) (hwh x hx y hy)

/-- Addition for the specification's all-pairs bounded Hölder predicate. -/
theorem isHolderOn_add {n : ℕ} {α : ℝ} {v w : Space n → ℝ}
    {s : Set (Space n)} (hv : IsHolderOn α v s) (hw : IsHolderOn α w s) :
    IsHolderOn α (fun x => v x + w x) s := by
  obtain ⟨Mv, Hv, hMv, hHv, hvs, hvh⟩ := hv
  obtain ⟨Mw, Hw, hMw, hHw, hws, hwh⟩ := hw
  refine ⟨Mv + Mw, Hv + Hw, add_nonneg hMv hMw, add_nonneg hHv hHw, ?_, ?_⟩
  · intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hvs x hx) (hws x hx))
  · intro x hx y hy
    calc
      ‖(v x + w x) - (v y + w y)‖ = ‖(v x - v y) + (w x - w y)‖ := by
        congr 1; ring
      _ ≤ ‖v x - v y‖ + ‖w x - w y‖ := norm_add_le _ _
      _ ≤ Hv * dist x y ^ α + Hw * dist x y ^ α :=
        add_le_add (hvh x hx y hy) (hwh x hx y hy)
      _ = (Hv + Hw) * dist x y ^ α := by ring

theorem isHolderOn_neg {n : ℕ} {α : ℝ} {v : Space n → ℝ}
    {s : Set (Space n)} (hv : IsHolderOn α v s) :
    IsHolderOn α (fun x => -v x) s := by
  obtain ⟨Mv, Hv, hMv, hHv, hvs, hvh⟩ := hv
  refine ⟨Mv, Hv, hMv, hHv, ?_, ?_⟩
  · intro x hx
    simpa only [norm_neg] using hvs x hx
  · intro x hx y hy
    simpa only [neg_sub_neg, norm_sub_rev] using hvh x hx y hy

theorem isHolderOn_sub {n : ℕ} {α : ℝ} {v w : Space n → ℝ}
    {s : Set (Space n)} (hv : IsHolderOn α v s) (hw : IsHolderOn α w s) :
    IsHolderOn α (fun x => v x - w x) s := by
  simpa only [sub_eq_add_neg] using isHolderOn_add hv (isHolderOn_neg hw)

theorem isHolderOn_const {n : ℕ} (α d : ℝ) (s : Set (Space n)) :
    IsHolderOn α (fun _ => d) s := by
  refine ⟨‖d‖, 0, norm_nonneg _, le_refl _, ?_, ?_⟩
  · intro x hx; exact le_refl _
  · intro x hx y hy; simp

theorem isHolderOn_sum {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {ι : Type*} (I : Finset ι) (v : ι → Space n → ℝ)
    (hv : ∀ i ∈ I, IsHolderOn α (v i) s) :
    IsHolderOn α (fun x => ∑ i ∈ I, v i x) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using isHolderOn_const α 0 s
  | @insert i I hi ih =>
      simpa only [Finset.sum_insert hi] using
        isHolderOn_add (hv i (Finset.mem_insert_self _ _))
          (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

/-- The frozen right-hand side is genuinely Hölder when each actual jet
entering the equation is Hölder. Quantitative control of these jets by u
alone is still needed in the a priori estimate. -/
theorem isHolderOn_frozenSource {n : ℕ} {α : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : Space n → Space n} {c u f : Space n → ℝ}
    {s : Set (Space n)} (z : Space n)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)) (hf : IsHolderOn α f s)
    (hu : IsHolderOn α u s)
    (hdu : ∀ i, IsHolderOn α (firstPartial u i) s)
    (hddu : ∀ i j, IsHolderOn α (secondPartial u i j) s) :
    IsHolderOn α (frozenSource a b c u f z) s := by
  apply isHolderOn_sub
  · apply isHolderOn_sub
    · apply isHolderOn_add hf
      apply isHolderOn_sum
      intro i hi
      apply isHolderOn_sum
      intro j hj
      exact isHolderOn_mul
        (isHolderOn_sub (isHolderOn_const α (a z i j) s) (hcoeff.1 i j)) (hddu i j)
    · apply isHolderOn_sum
      intro i hi
      exact isHolderOn_mul (hcoeff.2.1 i) (hdu i)
  · exact isHolderOn_mul hcoeff.2.2 hu

/-- The small oscillation factor at scale R, using the same α and actual
Euclidean distance as in the source. -/
theorem frozen_coefficient_bound {n : ℕ} {α H R : ℝ} (hα : 0 ≤ α)
    (hH : 0 ≤ H) {v : Space n → ℝ} {z x : Space n}
    (hx : x ∈ ball z R)
    (hh : ‖v z - v x‖ ≤ H * dist z x ^ α) :
    ‖v z - v x‖ ≤ H * R ^ α := by
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hH
  apply Real.rpow_le_rpow (dist_nonneg) _ hα
  simpa only [dist_comm] using (mem_ball.mp hx).le

/-- The principal error product, with its crucial R^α in front of the
unknown Hessian Hölder constant. The remaining term uses only its supremum.
This is the local scalar form of formula (0.18) in Haslhofer's notes. -/
theorem frozen_product_bound {n : ℕ} {α H R M Q : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) {v w : Space n → ℝ} {z x y : Space n}
    (hx : x ∈ ball z R)
    (hvz : ‖v z - v x‖ ≤ H * dist z x ^ α)
    (hvd : ‖v x - v y‖ ≤ H * dist x y ^ α)
    (hwy : ‖w y‖ ≤ M)
    (hwd : ‖w x - w y‖ ≤ Q * dist x y ^ α) :
    ‖(v z - v x) * w x - (v z - v y) * w y‖ ≤
      (H * R ^ α * Q + M * H) * dist x y ^ α := by
  apply holder_product_bound
    (v := fun t => v z - v t) (w := w)
    (frozen_coefficient_bound hα hH hx hvz) hwy _ hwd
  have he : (v z - v x) - (v z - v y) = -(v x - v y) := by ring
  simpa only [he, norm_neg] using hvd

/-- Applying the proved interior constant-coefficient estimate to the
genuine frozen equation. The norm of the frozen source still contains
the unknown jets and must subsequently be interpolated and absorbed. -/
theorem frozen_interior_ball_estimate
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ) (z center : Space n)
        (r : ℝ), MatrixBounds ell upper (a z) → 0 < r →
        ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u (ball center (2 * r)) →
          IsBoundedOn u (ball center (2 * r)) →
          IsHolderOn α (frozenSource a b c u f z) (ball center (2 * r)) →
          (∀ x ∈ ball center (2 * r), nondivergenceOperator a b c u x = f x) →
          IsC2HolderOn α u (ball center r) ∧
          scaledSolutionNorm α r u (ball center r) ≤
            C * scaledDataNorm α r u (frozenSource a b c u f z) (ball center (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.ConstantSchauder.interior_ball_estimate
    hn α hα hα1 ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro a b c z center r hA hr u f hu hub hF heq
  exact hest (a z) hA center r hr u (frozenSource a b c u f z) hu hub hF
    (fun x hx => constantOperator_eq_frozenSource a b c u f z x (heq x hx))

/-- Scalar absorption, applied only after a genuine analytic estimate has
been derived. This lemma itself supplies no PDE estimate. -/
theorem absorb_error {N D q : ℝ} (hq : q < 1) (h : N ≤ q * N + D) :
    N ≤ D / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith

/-- The two stages of absorption in the source: first choose the radius
so q is small, then use interpolation to make the second coefficient small. -/
theorem absorb_with_interpolation {N T D U q B ε Cε : ℝ}
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hsmall : q + B * ε ≤ (1 : ℝ) / 2)
    (hestimate : N ≤ q * N + B * (D + T))
    (hinterpolate : T ≤ ε * N + Cε * U) :
    N ≤ 2 * B * (D + Cε * U) := by
  have h := mul_le_mul_of_nonneg_left hinterpolate hB
  nlinarith

/-- Separate finite supremum and Hölder bounds. This records elementary
pointwise inequalities, with no PDE or Schauder assertion. -/
structure HolderBoundsOn {n : ℕ} (α : ℝ) (v : Space n → ℝ)
    (s : Set (Space n)) (M H : ℝ) : Prop where
  sup_nonneg : 0 ≤ M
  semi_nonneg : 0 ≤ H
  norm_le : ∀ x ∈ s, ‖v x‖ ≤ M
  diff_le : ∀ x ∈ s, ∀ y ∈ s, ‖v x - v y‖ ≤ H * dist x y ^ α

namespace HolderBoundsOn

variable {n : ℕ} {α M H M' H' : ℝ} {v w : Space n → ℝ} {s : Set (Space n)}

theorem isHolderOn (hv : HolderBoundsOn α v s M H) : IsHolderOn α v s :=
  ⟨M, H, hv.sup_nonneg, hv.semi_nonneg, hv.norm_le, hv.diff_le⟩

/-- Finite bounds justify passing to the real suprema, including empty sets
and sets with no distinct pairs. -/
theorem norm_bounds (hv : HolderBoundsOn α v s M H) :
    supNormOn v s ≤ M ∧ holderSeminormOn α v s ≤ H :=
  ⟨P201.Elliptic.NewtonHessian.supNormOn_le hv.sup_nonneg hv.norm_le,
    P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hv.semi_nonneg hv.diff_le⟩

theorem canonical (hv : IsHolderOn α v s) :
    HolderBoundsOn α v s (supNormOn v s) (holderSeminormOn α v s) := by
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hv
  exact ⟨P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _,
    P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _,
    fun x hx => P201.Elliptic.PoissonSchauder.norm_le_supNormOn ⟨M, hM, hb⟩ hx,
    fun x hx y hy => P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
      ⟨M, H, hM, hH, hb, hh⟩ hx hy⟩

theorem of_norm (hv : IsHolderOn α v s) :
    HolderBoundsOn α v s (holderNormOn α v s) (holderNormOn α v s) := by
  obtain ⟨hN, hb, hh⟩ := P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hv
  exact ⟨hN, hN, hb, hh⟩

theorem mono (hv : HolderBoundsOn α v s M H) (hM : M ≤ M') (hH : H ≤ H') :
    HolderBoundsOn α v s M' H' :=
  ⟨hv.sup_nonneg.trans hM, hv.semi_nonneg.trans hH,
    fun x hx => (hv.norm_le x hx).trans hM,
    fun x hx y hy => (hv.diff_le x hx y hy).trans
      (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg dist_nonneg _))⟩

theorem add (hv : HolderBoundsOn α v s M H) (hw : HolderBoundsOn α w s M' H') :
    HolderBoundsOn α (fun x => v x + w x) s (M + M') (H + H') := by
  refine ⟨add_nonneg hv.sup_nonneg hw.sup_nonneg,
    add_nonneg hv.semi_nonneg hw.semi_nonneg, ?_, ?_⟩
  · intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hv.norm_le x hx) (hw.norm_le x hx))
  · intro x hx y hy
    calc
      ‖(v x + w x) - (v y + w y)‖ = ‖(v x - v y) + (w x - w y)‖ := by
        congr 1; ring
      _ ≤ ‖v x - v y‖ + ‖w x - w y‖ := norm_add_le _ _
      _ ≤ H * dist x y ^ α + H' * dist x y ^ α :=
        add_le_add (hv.diff_le x hx y hy) (hw.diff_le x hx y hy)
      _ = (H + H') * dist x y ^ α := by ring

theorem neg (hv : HolderBoundsOn α v s M H) :
    HolderBoundsOn α (fun x => -v x) s M H := by
  refine ⟨hv.sup_nonneg, hv.semi_nonneg, ?_, ?_⟩
  · intro x hx; simpa only [norm_neg] using hv.norm_le x hx
  · intro x hx y hy
    simpa only [neg_sub_neg, norm_sub_rev] using hv.diff_le x hx y hy

theorem sub (hv : HolderBoundsOn α v s M H) (hw : HolderBoundsOn α w s M' H') :
    HolderBoundsOn α (fun x => v x - w x) s (M + M') (H + H') := by
  simpa only [sub_eq_add_neg] using hv.add hw.neg

theorem mul (hv : HolderBoundsOn α v s M H) (hw : HolderBoundsOn α w s M' H') :
    HolderBoundsOn α (fun x => v x * w x) s (M * M') (M * H' + M' * H) := by
  refine ⟨mul_nonneg hv.sup_nonneg hw.sup_nonneg,
    add_nonneg (mul_nonneg hv.sup_nonneg hw.semi_nonneg)
      (mul_nonneg hw.sup_nonneg hv.semi_nonneg), ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul (hv.norm_le x hx) (hw.norm_le x hx) (norm_nonneg _) hv.sup_nonneg
  · intro x hx y hy
    exact holder_product_bound (hv.norm_le x hx) (hw.norm_le y hy)
      (hv.diff_le x hx y hy) (hw.diff_le x hx y hy)

theorem zero (α : ℝ) (s : Set (Space n)) :
    HolderBoundsOn α (fun _ => 0) s 0 0 := by
  constructor <;> intros <;> simp

theorem sum {ι : Type*} (I : Finset ι) (v : ι → Space n → ℝ) (M H : ι → ℝ)
    (hv : ∀ i ∈ I, HolderBoundsOn α (v i) s (M i) (H i)) :
    HolderBoundsOn α (fun x => ∑ i ∈ I, v i x) s (∑ i ∈ I, M i) (∑ i ∈ I, H i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using zero α s
  | @insert i I hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hv i (Finset.mem_insert_self _ _)).add
          (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

/-- Freezing improves the supremum bound while retaining the full coefficient
seminorm. Both points in a Hölder quotient belong to the original set. -/
theorem frozen {R : ℝ} {z : Space n} (hv : HolderBoundsOn α v s M H)
    (hα : 0 ≤ α) (hz : z ∈ s) (hs : s ⊆ ball z R) :
    HolderBoundsOn α (fun x => v z - v x) s (H * R ^ α) H := by
  have hR : 0 < R := by simpa using mem_ball.mp (hs hz)
  refine ⟨mul_nonneg hv.semi_nonneg (Real.rpow_nonneg hR.le _), hv.semi_nonneg, ?_, ?_⟩
  · intro x hx
    exact frozen_coefficient_bound hα hv.semi_nonneg (hs hx) (hv.diff_le z hz x hx)
  · intro x hx y hy
    have he : (v z - v x) - (v z - v y) = -(v x - v y) := by ring
    simpa only [he, norm_neg] using hv.diff_le x hx y hy

end HolderBoundsOn

/-- The coefficient norm controls its principal sum and each component.
These bounds use the real canonical norms, with their nonnegativity on empty
sets, rather than arbitrarily chosen witnesses for Hölder continuity. -/
theorem coefficientNormOn_controls {n : ℕ} (α : ℝ)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ) (s : Set (Space n)) :
    (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) ≤
        ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ∧
    (∀ i j, holderNormOn α (fun x => a x i j) s ≤ ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s)) ∧
    (∀ i, holderNormOn α (fun x => b x i) s ≤ ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s)) ∧
    holderNormOn α c s ≤ ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) := by
  have hN (v : Space n → ℝ) : 0 ≤ holderNormOn α v s :=
    add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hA : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hN _
  have hB : 0 ≤ ∑ i : Fin n, holderNormOn α (fun x => b x i) s :=
    Finset.sum_nonneg fun i _ => hN _
  have hAsum : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) ≤
      ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) := by
    linarith [hN c]
  refine ⟨hAsum, ?_, ?_, ?_⟩
  · intro i j
    apply le_trans _ hAsum
    exact (Finset.single_le_sum (fun k _ => hN (fun x => a x i k))
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hN (fun x => a x k l))
        (Finset.mem_univ i))
  · intro i
    have hi := Finset.single_le_sum (fun k _ => hN (fun x => b x k)) (Finset.mem_univ i)
    linarith [hN c]
  · linarith

/-- Every actual coefficient and its Hölder differences are bounded by K. -/
theorem coefficient_holder_bounds {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hc : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)) (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K) :
    (∀ i j, HolderBoundsOn α (fun x => a x i j) s K K) ∧
    (∀ i, HolderBoundsOn α (fun x => b x i) s K K) ∧ HolderBoundsOn α c s K K := by
  have h := coefficientNormOn_controls α a b c s
  exact ⟨fun i j => (HolderBoundsOn.of_norm (hc.1 i j)).mono
      ((h.2.1 i j).trans hK) ((h.2.1 i j).trans hK),
    fun i => (HolderBoundsOn.of_norm (hc.2.1 i)).mono
      ((h.2.2.1 i).trans hK) ((h.2.2.1 i).trans hK),
    (HolderBoundsOn.of_norm hc.2.2).mono (h.2.2.2.trans hK) (h.2.2.2.trans hK)⟩

/-- The upper matrix bound needed by the constant-coefficient premise follows
from the prescribed coefficient norm. No extra matrix upper-bound hypothesis
is added to the variable-coefficient problem. -/
theorem matrixBounds_of_coefficientNorm {n : ℕ} {α ell K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (he : ((∀ x ∈ s, ∀ i j, a x i j = a x j i) ∧
      ∀ x ∈ s, ∀ ξ : Space n, ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)) (hc : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s))
    (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K) {z : Space n} (hz : z ∈ s) :
    MatrixBounds ell (K + 1) (a z) := by
  refine ⟨he.1 z hz, fun ξ => ⟨he.2 z hz ξ, ?_⟩⟩
  have ht (i j : Fin n) : a z i j * ξ i * ξ j ≤
      holderNormOn α (fun x => a x i j) s * ‖ξ‖ ^ 2 := by
    calc
      a z i j * ξ i * ξ j ≤ ‖a z i j * ξ i * ξ j‖ := le_abs_self _
      _ = ‖a z i j‖ * ‖ξ i‖ * ‖ξ j‖ := by rw [norm_mul, norm_mul]
      _ ≤ (holderNormOn α (fun x => a x i j) s * ‖ξ‖) * ‖ξ‖ := by
        apply mul_le_mul _ (PiLp.norm_apply_le ξ j) (norm_nonneg _)
          (mul_nonneg (HolderBoundsOn.of_norm (hc.1 i j)).sup_nonneg (norm_nonneg _))
        exact mul_le_mul ((HolderBoundsOn.of_norm (hc.1 i j)).norm_le z hz)
          (PiLp.norm_apply_le ξ i) (norm_nonneg _)
          (HolderBoundsOn.of_norm (hc.1 i j)).sup_nonneg
      _ = holderNormOn α (fun x => a x i j) s * ‖ξ‖ ^ 2 := by ring
  calc
    (∑ i : Fin n, ∑ j : Fin n, a z i j * ξ i * ξ j) ≤
        ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s * ‖ξ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) * ‖ξ‖ ^ 2 := by
      simp only [Finset.sum_mul]
    _ ≤ K * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ((coefficientNormOn_controls α a b c s).1.trans hK)
        (sq_nonneg _)
    _ ≤ (K + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]

/-- Quantitative freezing for the genuine operator. The coefficient
oscillation multiplies the highest Hölder bound, while the full coefficient
seminorm multiplies only the Hessian supremum. Bounds on the lower jets are
explicit intermediate quantities; they still have to be interpolated. -/
theorem frozenSource_bounds {n : ℕ} {α K R M0 H0 Mf Hf : ℝ}
    {M1 H1 : Fin n → ℝ} {M2 H2 : Fin n → Fin n → ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s : Set (Space n)} {z : Space n}
    (hα : 0 ≤ α) (hz : z ∈ s) (hs : s ⊆ ball z R)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s))
    (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K)
    (hf : HolderBoundsOn α f s Mf Hf) (hu : HolderBoundsOn α u s M0 H0)
    (hdu : ∀ i, HolderBoundsOn α (firstPartial u i) s (M1 i) (H1 i))
    (hddu : ∀ i j, HolderBoundsOn α (secondPartial u i j) s (M2 i j) (H2 i j)) :
    HolderBoundsOn α (frozenSource a b c u f z) s
      (Mf + K * R ^ α * (∑ i, ∑ j, M2 i j) + K * ((∑ i, M1 i) + M0))
      (Hf + K * R ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j) +
        K * ((∑ i, H1 i) + (∑ i, M1 i) + H0 + M0)) := by
  obtain ⟨ha, hb, hc⟩ := coefficient_holder_bounds hcoeff hK
  have hP : HolderBoundsOn α
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (a z i j - a x i j) * secondPartial u i j x) s
      (K * R ^ α * (∑ i, ∑ j, M2 i j))
      (K * R ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ =>
      HolderBoundsOn.sum Finset.univ _ _ _ (fun j _ =>
        ((ha i j).frozen hα hz hs).mul (hddu i j)))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  have hB : HolderBoundsOn α (fun x => ∑ i : Fin n, b x i * firstPartial u i x) s
      (K * ∑ i, M1 i) (K * (∑ i, H1 i) + K * (∑ i, M1 i)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ => (hb i).mul (hdu i))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  convert ((hf.add hP).sub hB).sub (hc.mul hu) using 1 <;> first | rfl | ring

/-- Canonical, finite, scaled frozen-source estimate. Unlike an assumption
of the desired Schauder estimate, this conclusion still displays all unknown
jet norms. Its small R^α factor is ready for weighted absorption. -/
theorem scaledDataNorm_frozenSource_le {n : ℕ} {α K R r : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s : Set (Space n)} {z : Space n}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hz : z ∈ s) (hs : s ⊆ ball z R)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s))
    (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K)
    (hf : IsHolderOn α f s) (hu : IsHolderOn α u s)
    (hdu : ∀ i, IsHolderOn α (firstPartial u i) s)
    (hddu : ∀ i j, IsHolderOn α (secondPartial u i j) s) :
    let M0 := supNormOn u s
    let H0 := holderSeminormOn α u s
    let M1 := ∑ i : Fin n, supNormOn (firstPartial u i) s
    let H1 := ∑ i : Fin n, holderSeminormOn α (firstPartial u i) s
    let M2 := ∑ i : Fin n, ∑ j : Fin n, supNormOn (secondPartial u i j) s
    let H2 := ∑ i : Fin n, ∑ j : Fin n, holderSeminormOn α (secondPartial u i j) s
    scaledDataNorm α r u (frozenSource a b c u f z) s ≤
      M0 + r ^ 2 * (supNormOn f s + K * R ^ α * M2 + K * (M1 + M0)) +
        r ^ (2 + α) * (holderSeminormOn α f s + K * R ^ α * H2 + K * M2 +
          K * (H1 + M1 + H0 + M0)) := by
  dsimp only
  have h := frozenSource_bounds hα hz hs hcoeff hK
    (HolderBoundsOn.canonical hf) (HolderBoundsOn.canonical hu)
    (fun i => HolderBoundsOn.canonical (hdu i))
    (fun i j => HolderBoundsOn.canonical (hddu i j))
  exact add_le_add
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h.norm_bounds.1 (sq_nonneg r)))
    (mul_le_mul_of_nonneg_left h.norm_bounds.2 (Real.rpow_nonneg hr _))

theorem firstPartialWithin_congr_set {n : ℕ} (u : Space n → ℝ)
    {s t : Set (Space n)} {x : Space n} (hst : s =ᶠ[nhds x] t) (i : Fin n) :
    firstPartialWithin u s i x = firstPartialWithin u t i x := by
  unfold firstPartialWithin
  rw [fderivWithin_congr_set hst]

theorem secondPartialWithin_congr_set {n : ℕ} (u : Space n → ℝ)
    {s t : Set (Space n)} {x : Space n} (hst : s =ᶠ[nhds x] t) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartialWithin u t i j x := by
  have hfirst : firstPartialWithin u s j =ᶠ[nhds x] firstPartialWithin u t j := by
    filter_upwards [fderivWithin_eventually_congr_set (𝕜 := ℝ) (f := u) hst] with y hy
    exact congrArg (fun A : Space n →L[ℝ] ℝ => A (coordinate n j)) hy
  unfold secondPartialWithin
  rw [fderivWithin_congr_set hst, hfirst.fderivWithin_eq_of_nhds]

/-- On the interior of the observation set, the genuine one-sided first jet
coincides with the ordinary jet without requiring global regularity. -/
theorem firstPartialWithin_eq_firstPartial {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (i : Fin n) :
    firstPartialWithin u s i x = firstPartial u i x := by
  unfold firstPartialWithin firstPartial
  rw [fderivWithin_of_mem_nhds hs]

theorem secondPartialWithin_eq_secondPartial {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartial u i j x := by
  have heq : firstPartialWithin u s j =ᶠ[nhds x] firstPartial u j := by
    filter_upwards [interior_mem_nhds.mpr hs] with y hy
    exact firstPartialWithin_eq_firstPartial u (mem_interior_iff_mem_nhds.mp hy) j
  unfold secondPartialWithin secondPartial firstPartial
  rw [fderivWithin_of_mem_nhds hs, heq.fderiv_eq]
  rfl

/-- Open patch restriction preserves both actual one-sided derivatives at
all points of the patch, including points on the domain boundary. -/
theorem within_jets_restrict_open {n : ℕ} (u : Space n → ℝ)
    (s : Set (Space n)) {U : Set (Space n)} (hU : IsOpen U) {x : Space n} (hx : x ∈ U) :
    (∀ i, firstPartialWithin u (s ∩ U) i x = firstPartialWithin u s i x) ∧
    ∀ i j, secondPartialWithin u (s ∩ U) i j x = secondPartialWithin u s i j x := by
  have heq : s ∩ U =ᶠ[nhds x] s := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [mem_inter_iff, hy, and_true]
  exact ⟨fun i => firstPartialWithin_congr_set u heq i,
    fun i j => secondPartialWithin_congr_set u heq i j⟩


/-- Frozen source formed from the actual within jets on the observation set. -/
def frozenWithinSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ) (s : Set (Space n))
    (z x : Space n) : ℝ :=
  f x + (∑ i : Fin n, ∑ j : Fin n,
      (a z i j - a x i j) * secondPartialWithin u s i j x) -
    (∑ i : Fin n, b x i * firstPartialWithin u s i x) - c x * u x

/-- At interior points of the observation set the one-sided freezing source
agrees with the classical source, with no assumption on the representative
away from the observation set. -/
theorem frozenWithinSource_eq_frozenSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (z : Space n) :
    frozenWithinSource a b c u f s z x = frozenSource a b c u f z x := by
  simp only [frozenWithinSource, frozenSource,
    firstPartialWithin_eq_firstPartial u hs,
    secondPartialWithin_eq_secondPartial u hs]

/-- The classical equation freezes to the genuine within source wherever the
observation set contains a neighborhood of the point. No equation on the
flat boundary is introduced. -/
theorem constantOperator_eq_frozenWithinSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (z : Space n)
    (heq : nondivergenceOperator a b c u x = f x) :
    constantOperator (a z) u x = frozenWithinSource a b c u f s z x := by
  rw [frozenWithinSource_eq_frozenSource a b c u f hs z]
  exact constantOperator_eq_frozenSource a b c u f z x heq

/-- Quantitative source product bounds in genuine within jets. The small
coefficient oscillation multiplies the highest seminorm and the full
coefficient seminorm multiplies only the Hessian supremum. -/
theorem frozenWithinSource_bounds {n : ℕ} {α K R M0 H0 Mf Hf : ℝ}
    {M1 H1 : Fin n → ℝ} {M2 H2 : Fin n → Fin n → ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s : Set (Space n)} {z : Space n}
    (hα : 0 ≤ α) (hz : z ∈ s) (hs : s ⊆ ball z R)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s))
    (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K)
    (hf : HolderBoundsOn α f s Mf Hf) (hu : HolderBoundsOn α u s M0 H0)
    (hdu : ∀ i, HolderBoundsOn α (firstPartialWithin u s i) s (M1 i) (H1 i))
    (hddu : ∀ i j, HolderBoundsOn α (secondPartialWithin u s i j) s (M2 i j) (H2 i j)) :
    HolderBoundsOn α (frozenWithinSource a b c u f s z) s
      (Mf + K * R ^ α * (∑ i, ∑ j, M2 i j) + K * ((∑ i, M1 i) + M0))
      (Hf + K * R ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j) +
        K * ((∑ i, H1 i) + (∑ i, M1 i) + H0 + M0)) := by
  obtain ⟨ha, hb, hc⟩ := coefficient_holder_bounds hcoeff hK
  have hP : HolderBoundsOn α
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (a z i j - a x i j) * secondPartialWithin u s i j x) s
      (K * R ^ α * (∑ i, ∑ j, M2 i j))
      (K * R ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ =>
      HolderBoundsOn.sum Finset.univ _ _ _ (fun j _ =>
        ((ha i j).frozen hα hz hs).mul (hddu i j)))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  have hB : HolderBoundsOn α
      (fun x => ∑ i : Fin n, b x i * firstPartialWithin u s i x) s
      (K * ∑ i, M1 i) (K * (∑ i, H1 i) + K * (∑ i, M1 i)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ => (hb i).mul (hdu i))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  convert ((hf.add hP).sub hB).sub (hc.mul hu) using 1 <;> first | rfl | ring

/-- Passing to canonical real norms is justified by finite Hölder bounds on
all jets used by the source. In particular, the statement makes no ambient
smoothness assumption at flat boundary points. -/
theorem scaledDataNorm_frozenWithinSource_le {n : ℕ} {α K R r : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s : Set (Space n)} {z : Space n}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hz : z ∈ s) (hs : s ⊆ ball z R)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s))
    (hK : ((∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) ≤ K)
    (hf : IsHolderOn α f s) (hu : IsHolderOn α u s)
    (hdu : ∀ i, IsHolderOn α (firstPartialWithin u s i) s)
    (hddu : ∀ i j, IsHolderOn α (secondPartialWithin u s i j) s) :
    let M0 := supNormOn u s
    let H0 := holderSeminormOn α u s
    let M1 := ∑ i : Fin n, supNormOn (firstPartialWithin u s i) s
    let H1 := ∑ i : Fin n, holderSeminormOn α (firstPartialWithin u s i) s
    let M2 := ∑ i : Fin n, ∑ j : Fin n, supNormOn (secondPartialWithin u s i j) s
    let H2 := ∑ i : Fin n, ∑ j : Fin n, holderSeminormOn α (secondPartialWithin u s i j) s
    scaledDataNorm α r u (frozenWithinSource a b c u f s z) s ≤
      M0 + r ^ 2 * (supNormOn f s + K * R ^ α * M2 + K * (M1 + M0)) +
        r ^ (2 + α) * (holderSeminormOn α f s + K * R ^ α * H2 + K * M2 +
          K * (H1 + M1 + H0 + M0)) := by
  dsimp only
  have h := frozenWithinSource_bounds hα hz hs hcoeff hK
    (HolderBoundsOn.canonical hf) (HolderBoundsOn.canonical hu)
    (fun i => HolderBoundsOn.canonical (hdu i))
    (fun i j => HolderBoundsOn.canonical (hddu i j))
  exact add_le_add
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h.norm_bounds.1 (sq_nonneg r)))
    (mul_le_mul_of_nonneg_left h.norm_bounds.2 (Real.rpow_nonneg hr _))

/-- All source terms are Hölder in genuine within jets. Finiteness is
separate from the subsequent interpolation and absorption argument. -/
theorem isHolderOn_frozenWithinSource {n : ℕ} {α : ℝ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ)
    (s : Set (Space n)) (z : Space n)
    (hcoeff : ((∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)) (hf : IsHolderOn α f s)
    (hu : IsHolderOn α u s)
    (hdu : ∀ i, IsHolderOn α (firstPartialWithin u s i) s)
    (hddu : ∀ i j, IsHolderOn α (secondPartialWithin u s i j) s) :
    IsHolderOn α (frozenWithinSource a b c u f s z) s := by
  apply isHolderOn_sub
  · apply isHolderOn_sub
    · apply isHolderOn_add hf
      apply isHolderOn_sum
      intro i _
      apply isHolderOn_sum
      intro j _
      exact isHolderOn_mul
        (isHolderOn_sub (isHolderOn_const α (a z i j) s) (hcoeff.1 i j)) (hddu i j)
    · apply isHolderOn_sum
      intro i _
      exact isHolderOn_mul (hcoeff.2.1 i) (hdu i)
  · exact isHolderOn_mul hcoeff.2.2 hu

/-- Each point of the open half-ball is an interior point of the half-ball
with its flat face. This does not assert any neighborhood condition at the
flat face itself. -/
theorem halfBallWithFace_mem_nhds {m : ℕ} {R : ℝ} {x : Space (m + 1)}
    (hx : x ∈ halfBall m R) : halfBallWithFace m R ∈ nhds x := by
  have hopen : IsOpen (P201Specs.Elliptic.HalfSpaceLift.openHalfSpace m) := by
    exact isOpen_lt continuous_const
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).continuous
  apply Filter.mem_of_superset ((isOpen_ball.inter hopen).mem_nhds hx)
  intro y hy
  refine ⟨hy.1, ?_⟩
  change 0 ≤ P201Specs.Elliptic.HalfSpaceLift.height y
  exact le_of_lt (show 0 < P201Specs.Elliptic.HalfSpaceLift.height y from hy.2)

/-- Direct application of the proved constant half-ball estimate to an actual
within-jet source. The equation is required only in the open half-ball. -/
theorem frozen_within_half_ball_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ)
        (z : Space (m + 1)) (r : ℝ), MatrixBounds ell upper (a z) → 0 < r →
        ∀ u f : Space (m + 1) → ℝ, ContDiffOn ℝ 2 u (halfBall m (2 * r)) →
          ContinuousOn u (halfBallWithFace m (2 * r)) →
          (∀ x ∈ flatFace m (2 * r), u x = 0) →
          IsBoundedOn u (halfBallWithFace m (2 * r)) →
          IsHolderOn α
            (frozenWithinSource a b c u f (halfBallWithFace m (2 * r)) z)
            (halfBallWithFace m (2 * r)) →
          (∀ x ∈ halfBall m (2 * r), nondivergenceOperator a b c u x = f x) →
          IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
          scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
            C * scaledDataNorm α r u
              (frozenWithinSource a b c u f (halfBallWithFace m (2 * r)) z)
              (halfBallWithFace m (2 * r)) := by
  obtain ⟨C, hC, hest⟩ :=
    P201.Elliptic.ConstantSchauder.half_ball_estimate m α hα hα1 ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro a b c z r hA hr u f hu huc huz hub hF heq
  exact hest (a z) hA r hr u
    (frozenWithinSource a b c u f (halfBallWithFace m (2 * r)) z)
    hu huc huz hub hF
    (fun x hx => constantOperator_eq_frozenWithinSource a b c u f
      (halfBallWithFace_mem_nhds hx) z (heq x hx))

open P201Specs.Elliptic.WeightedInterpolation

/-- The spherical distance changes by at most the distance between the points.
This concerns the curved boundary only, including in the half-ball. -/
theorem radialWeight_sub_le_dist {n : ℕ} (z x y : Space n) (R : ℝ) :
    radialWeight z R x - radialWeight z R y ≤ dist x y := by
  have h := dist_triangle y x z
  dsimp [radialWeight]
  rw [dist_comm y x] at h
  linarith

/-- A patch of radius at most half the spherical distance stays inside the
outer sphere and has comparable weights. This is independent of the solution. -/
theorem radial_patch_geometry {n : ℕ} {z x y : Space n} {R ρ : ℝ}
    (hx : x ∈ ball z R) (hρ : ρ ≤ radialWeight z R x / 2)
    (hy : y ∈ ball x ρ) :
    y ∈ ball z R ∧
      radialWeight z R x / 2 < radialWeight z R y ∧
      radialWeight z R y < 3 * radialWeight z R x / 2 := by
  have hd : 0 < radialWeight z R x := sub_pos.mpr (mem_ball.mp hx)
  have hxy : dist x y < ρ := by simpa only [mem_ball, dist_comm] using hy
  have h₁ := radialWeight_sub_le_dist z x y R
  have h₂ := radialWeight_sub_le_dist z y x R
  rw [dist_comm y x] at h₂
  have hlow : radialWeight z R x / 2 < radialWeight z R y := by linarith
  refine ⟨?_, hlow, by linarith⟩
  change dist y z < R
  dsimp [radialWeight] at hd hlow
  linarith

/-- The source's scale μd gives weight comparability on every patch used
below, including the enlarged plane-centered patches. -/
theorem radial_freezing_geometry {n : ℕ} {z x y : Space n} {R μ : ℝ}
    (hx : x ∈ ball z R) (hμ : μ ≤ 1 / 32)
    (hy : y ∈ ball x (16 * (μ * radialWeight z R x))) :
    y ∈ ball z R ∧
      radialWeight z R x / 2 < radialWeight z R y ∧
      radialWeight z R y < 3 * radialWeight z R x / 2 := by
  apply radial_patch_geometry hx _ hy
  have hd : 0 < radialWeight z R x := sub_pos.mpr (mem_ball.mp hx)
  nlinarith

/-- The far-pair estimate is purely algebraic. The larger weight is never
used in the Hölder factor; both pointwise Hessian bounds use their own weight. -/
theorem far_pair_bound {n : ℕ} {g : Space n → ℝ} {x y : Space n}
    {d₁ d₂ α τ M : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hα : 0 ≤ α) (hτ : 0 < τ)
    (hx : d₁ ^ 2 * ‖g x‖ ≤ M) (hy : d₂ ^ 2 * ‖g y‖ ≤ M)
    (hfar : τ * min d₁ d₂ ≤ dist x y) :
    min d₁ d₂ ^ (2 + α) * ‖g x - g y‖ ≤
      (2 * M / τ ^ α) * dist x y ^ α := by
  let d := min d₁ d₂
  have hd : 0 < d := lt_min hd₁ hd₂
  have hM : 0 ≤ M := (mul_nonneg (sq_nonneg _) (norm_nonneg _)).trans hx
  have hdx : d ^ 2 ≤ d₁ ^ 2 := pow_le_pow_left₀ hd.le (min_le_left _ _) 2
  have hdy : d ^ 2 ≤ d₂ ^ 2 := pow_le_pow_left₀ hd.le (min_le_right _ _) 2
  have hval : d ^ 2 * ‖g x - g y‖ ≤ 2 * M := by
    calc
      _ ≤ d ^ 2 * (‖g x‖ + ‖g y‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg _)
      _ = d ^ 2 * ‖g x‖ + d ^ 2 * ‖g y‖ := by ring
      _ ≤ M + M := add_le_add
        ((mul_le_mul_of_nonneg_right hdx (norm_nonneg _)).trans hx)
        ((mul_le_mul_of_nonneg_right hdy (norm_nonneg _)).trans hy)
      _ = _ := by ring
  have hp : τ ^ α * d ^ α ≤ dist x y ^ α := by
    rw [← Real.mul_rpow hτ.le hd.le]
    exact Real.rpow_le_rpow (mul_nonneg hτ.le hd.le) hfar hα
  have hpa : d ^ α ≤ dist x y ^ α / τ ^ α := by
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hτ _)).mpr (by simpa [mul_comm] using hp)
  calc
    _ = (d ^ 2 * ‖g x - g y‖) * d ^ α := by
      rw [Real.rpow_add hd, Real.rpow_two]
      ring
    _ ≤ (2 * M) * (dist x y ^ α / τ ^ α) :=
      mul_le_mul hval hpa (Real.rpow_nonneg hd.le _) (by positivity)
    _ = _ := by ring

/-- Actual weighted Hessian suprema control every far pair. No Hölder norm
finiteness is needed for this half of the close/far argument. -/
theorem weighted_far_pair_bound {n : ℕ} {z x y : Space n} {R α τ : ℝ}
    {s : Set (Space n)} {u : Space n → ℝ}
    (hs : s ⊆ ball z R) (hf : FiniteWeightedNorms α z R u s)
    (hα : 0 ≤ α) (hτ : 0 < τ) (i j : Fin n) (hx : x ∈ s) (hy : y ∈ s)
    (hfar : τ * min (radialWeight z R x) (radialWeight z R y) ≤ dist x y) :
    min (radialWeight z R x) (radialWeight z R y) ^ (2 + α) *
        ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
      (2 * M2 z R u s / τ ^ α) * dist x y ^ α := by
  exact far_pair_bound
    (P201.Elliptic.WeightedInterpolation.radialWeight_pos hs hx)
    (P201.Elliptic.WeightedInterpolation.radialWeight_pos hs hy) hα hτ
    (P201.Elliptic.WeightedInterpolation.second_weighted_le_M2 hs hf i j hx)
    (P201.Elliptic.WeightedInterpolation.second_weighted_le_M2 hs hf i j hy) hfar

/-- Restricting quantitative Hölder bounds preserves their constants. -/
theorem HolderBoundsOn.restrict {n : ℕ} {α M H : ℝ} {v : Space n → ℝ}
    {s t : Set (Space n)} (hv : HolderBoundsOn α v s M H) (ht : t ⊆ s) :
    HolderBoundsOn α v t M H :=
  ⟨hv.sup_nonneg, hv.semi_nonneg, fun x hx => hv.norm_le x (ht hx),
    fun x hx y hy => hv.diff_le x (ht hx) y (ht hy)⟩

/-- Weighted bounds give ordinary Hölder bounds wherever the weight is
bounded below. Both finiteness hypotheses concern the actual defining sets. -/
theorem holderBoundsOn_of_weighted {n : ℕ} {α R δ : ℝ} {z : Space n}
    {s t : Set (Space n)} {g : Space n → ℝ} (j : ℕ)
    (hα : 0 ≤ α) (hδ : 0 < δ) (hs : s ⊆ ball z R) (ht : t ⊆ s)
    (hweight : ∀ x ∈ t, δ ≤ radialWeight z R x)
    (hval : BddAbove (weightedValueSet j z R g s))
    (hpair : BddAbove (weightedPairSet j α z R g s)) :
    HolderBoundsOn α g t
      (weightedSupOn j z R g s / δ ^ j)
      (weightedSeminormOn j α z R g s / δ ^ ((j : ℝ) + α)) := by
  have hM := P201.Elliptic.WeightedInterpolation.weightedSupOn_nonneg hs g j
  have hH := P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s g j hs
  refine ⟨div_nonneg hM (pow_nonneg hδ.le _),
    div_nonneg hH (Real.rpow_nonneg hδ.le _), ?_, ?_⟩
  · intro x hx
    apply (le_div_iff₀ (pow_pos hδ j)).mpr
    have hb : radialWeight z R x ^ j * ‖g x‖ ≤ weightedSupOn j z R g s :=
      le_csSup hval ⟨x, ht hx, rfl⟩
    have hp : δ ^ j ≤ radialWeight z R x ^ j :=
      pow_le_pow_left₀ hδ.le (hweight x hx) j
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hb
  · intro x hx y hy
    have hp : δ ^ ((j : ℝ) + α) ≤
        min (radialWeight z R x) (radialWeight z R y) ^ ((j : ℝ) + α) :=
      Real.rpow_le_rpow hδ.le (le_min (hweight x hx) (hweight y hy)) (by positivity)
    have hb := P201.Elliptic.WeightedInterpolation.weighted_pair_bound hs hpair (ht hx) (ht hy)
    have hb' := (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hb
    calc
      _ ≤ (weightedSeminormOn j α z R g s * dist x y ^ α) /
          δ ^ ((j : ℝ) + α) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr (by simpa [mul_comm] using hb')
      _ = _ := by ring

/-- The full coefficient norm bound remains valid after restriction. -/
theorem coefficient_norm_restrict {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s t : Set (Space n)}
    (hc : (∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)
    (hK : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (ht : t ⊆ s) :
    (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) t) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) t) + holderNormOn α c t ≤ K := by
  apply le_trans _ hK
  exact add_le_add (add_le_add
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      P201.Elliptic.PoissonSchauder.holderNormOn_mono (hc.1 i j) ht)
    (Finset.sum_le_sum fun i _ =>
      P201.Elliptic.PoissonSchauder.holderNormOn_mono (hc.2.1 i) ht))
    (P201.Elliptic.PoissonSchauder.holderNormOn_mono hc.2.2 ht)

/-- Freezing on a smaller patch uses the actual jets of the larger observation
set. This allows its source to retain the genuine boundary values while its
equation is used only at interior points. -/
theorem frozenWithinSource_bounds_on_subset {n : ℕ} {α K L M0 H0 Mf Hf : ℝ}
    {M1 H1 : Fin n → ℝ} {M2 H2 : Fin n → Fin n → ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s t : Set (Space n)} {z : Space n}
    (hα : 0 ≤ α) (hz : z ∈ t) (ht : t ⊆ ball z L)
    (hcoeff : (∀ i j : Fin n, IsHolderOn α (fun x => a x i j) t) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) t) ∧ IsHolderOn α c t)
    (hK : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) t) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) t) + holderNormOn α c t ≤ K)
    (hf : HolderBoundsOn α f t Mf Hf) (hu : HolderBoundsOn α u t M0 H0)
    (hdu : ∀ i, HolderBoundsOn α (firstPartialWithin u s i) t (M1 i) (H1 i))
    (hddu : ∀ i j, HolderBoundsOn α (secondPartialWithin u s i j) t (M2 i j) (H2 i j)) :
    HolderBoundsOn α (frozenWithinSource a b c u f s z) t
      (Mf + K * L ^ α * (∑ i, ∑ j, M2 i j) + K * ((∑ i, M1 i) + M0))
      (Hf + K * L ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j) +
        K * ((∑ i, H1 i) + (∑ i, M1 i) + H0 + M0)) := by
  obtain ⟨ha, hb, hc⟩ := coefficient_holder_bounds hcoeff hK
  have hP : HolderBoundsOn α
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (a z i j - a x i j) * secondPartialWithin u s i j x) t
      (K * L ^ α * (∑ i, ∑ j, M2 i j))
      (K * L ^ α * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ =>
      HolderBoundsOn.sum Finset.univ _ _ _ (fun j _ =>
        ((ha i j).frozen hα hz ht).mul (hddu i j)))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  have hB : HolderBoundsOn α
      (fun x => ∑ i : Fin n, b x i * firstPartialWithin u s i x) t
      (K * ∑ i, M1 i) (K * (∑ i, H1 i) + K * (∑ i, M1 i)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ => (hb i).mul (hdu i))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  convert ((hf.add hP).sub hB).sub (hc.mul hu) using 1 <;> first | rfl | ring

/-- Quantitative freezing directly in the source's weighted norms. In the
highest Hölder term the coefficient oscillation is `K * L^α`; the separate
`K * M2 / δ²` term is retained for interpolation. The jets in this source are
those of `s`, even at the flat face of a half-ball. -/
theorem weighted_frozenWithinSource_bounds {n : ℕ} {α K R δ L : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s t : Set (Space n)} {center z : Space n}
    (hα : 0 ≤ α) (hδ : 0 < δ) (hs : s ⊆ ball center R) (ht : t ⊆ s)
    (hz : z ∈ t) (hlocal : t ⊆ ball z L)
    (hweight : ∀ x ∈ t, δ ≤ radialWeight center R x)
    (hcoeff : (∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)
    (hK : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hf : IsHolderOn α f s) (hfinite : FiniteWeightedNorms α center R u s) :
    HolderBoundsOn α (frozenWithinSource a b c u f s z) t
      (supNormOn f s + K * L ^ α * (M2 center R u s / δ ^ 2) +
        K * (M1 center R u s / δ + M0 u s))
      (holderSeminormOn α f s + K * L ^ α * (N2 α center R u s / δ ^ (2 + α)) +
        K * (M2 center R u s / δ ^ 2) +
        K * (N1 α center R u s / δ ^ (1 + α) + M1 center R u s / δ +
          N0 α center R u s / δ ^ α + M0 u s)) := by
  have hu := holderBoundsOn_of_weighted 0 hα hδ hs ht hweight
    hfinite.1 hfinite.2.2.2.1
  have hdu (i : Fin n) := holderBoundsOn_of_weighted 1 hα hδ hs ht hweight
    (hfinite.2.1 i) (hfinite.2.2.2.2.1 i)
  have hddu (i j : Fin n) := holderBoundsOn_of_weighted 2 hα hδ hs ht hweight
    (hfinite.2.2.1 i j) (hfinite.2.2.2.2.2 i j)
  have hcoefft := And.intro
    (fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.1 i j) ht)
    (And.intro (fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.2.1 i) ht)
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono hcoeff.2.2 ht))
  have hKt := coefficient_norm_restrict hcoeff hK ht
  have h := frozenWithinSource_bounds_on_subset hα hz hlocal hcoefft hKt
    ((HolderBoundsOn.canonical hf).restrict ht) hu hdu hddu
  have hzero : weightedSupOn 0 center R u s = supNormOn u s := by
    simp only [weightedSupOn, weightedValueSet, pow_zero, one_mul, supNormOn]
  simpa only [M0, M1, M2, N0, N1, N2, Finset.sum_div, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add, pow_zero, pow_one, div_one, hzero] using h

/-- Passing from the weighted source bounds to the actual scaled data norm.
The scale in the estimate and the radius controlling coefficient oscillation
are separate, as required for enlarged boundary patches. -/
theorem weighted_scaledDataNorm_frozenWithinSource_le {n : ℕ} {α K R δ L r : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c u f : Space n → ℝ} {s t : Set (Space n)} {center z : Space n}
    (hα : 0 ≤ α) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hs : s ⊆ ball center R) (ht : t ⊆ s) (hz : z ∈ t) (hlocal : t ⊆ ball z L)
    (hweight : ∀ x ∈ t, δ ≤ radialWeight center R x)
    (hcoeff : (∀ i j : Fin n, IsHolderOn α (fun x => a x i j) s) ∧
      (∀ i : Fin n, IsHolderOn α (fun x => b x i) s) ∧ IsHolderOn α c s)
    (hK : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) +
      (∑ i : Fin n, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hf : IsHolderOn α f s) (hub : IsBoundedOn u s)
    (hfinite : FiniteWeightedNorms α center R u s) :
    scaledDataNorm α r u (frozenWithinSource a b c u f s z) t ≤
      M0 u s + r ^ 2 *
        (supNormOn f s + K * L ^ α * (M2 center R u s / δ ^ 2) +
          K * (M1 center R u s / δ + M0 u s)) +
      r ^ (2 + α) *
        (holderSeminormOn α f s + K * L ^ α * (N2 α center R u s / δ ^ (2 + α)) +
          K * (M2 center R u s / δ ^ 2) +
          K * (N1 α center R u s / δ ^ (1 + α) + M1 center R u s / δ +
            N0 α center R u s / δ ^ α + M0 u s)) := by
  have h := weighted_frozenWithinSource_bounds hα hδ hs ht hz hlocal hweight hcoeff hK hf hfinite
  exact add_le_add (add_le_add
    (P201.Elliptic.PoissonSchauder.supNormOn_mono hub ht)
    (mul_le_mul_of_nonneg_left h.norm_bounds.1 (sq_nonneg r)))
    (mul_le_mul_of_nonneg_left h.norm_bounds.2 (Real.rpow_nonneg hr _))

/-- Uniform weighted jet bounds on the outer set give the full scaled norm
on an inner spherical cut. The change of derivative set is justified by
germ equality, also when `q` is a closed half-space. -/
theorem inner_estimate_of_weighted_jets {n : ℕ} {α R r U A B H : ℝ}
    {z : Space n} {q : Set (Space n)} {u : Space n → ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hrR : r < R)
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hu : ContDiffOn ℝ 2 u (ball z r ∩ q))
    (hb : ∀ x ∈ ball z R ∩ q, ‖u x‖ ≤ U)
    (hj : JetBounds α z R (ball z R ∩ q) u A B H) :
    IsC2HolderUpToOn α u (ball z r ∩ q) ∧
      scaledWithinSolutionNorm α r u (ball z r ∩ q) ≤
        U + r * ((n : ℝ) * (A / (R - r))) +
          r ^ 2 * ((n : ℝ) ^ 2 * (B / (R - r) ^ 2)) +
          r ^ (2 + α) * ((n : ℝ) ^ 2 * (H / (R - r) ^ (2 + α))) := by
  have hδ : 0 < R - r := sub_pos.mpr hrR
  have hsub : ball z r ∩ q ⊆ ball z R ∩ q :=
    inter_subset_inter_left _ (ball_subset_ball hrR.le)
  have hw (x : Space n) (hx : x ∈ ball z r ∩ q) : R - r ≤ radialWeight z R x := by
    dsimp [radialWeight]
    linarith [mem_ball.mp hx.1]
  have hjets (x : Space n) (hx : x ∈ ball z r ∩ q) :=
    P201.Elliptic.WeightedInterpolation.radial_jets_restrict u z q hrR hx.1
  apply P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_le_of_bounds hr hU
    (div_nonneg hA hδ.le) (div_nonneg hB (sq_nonneg _))
    (div_nonneg hH (Real.rpow_nonneg hδ.le _)) hu (fun x hx => hb x (hsub hx))
  · intro i x hx
    rw [(hjets x hx).1 i]
    apply (le_div_iff₀ hδ).mpr
    have h := hj.1 i x (hsub hx)
    exact (by simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)).trans h)
  · intro i j x hx
    rw [(hjets x hx).2 i j]
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    have hp := pow_le_pow_left₀ hδ.le (hw x hx) 2
    exact (by simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (hj.2.1 i j x (hsub hx)))
  · intro i j x hx y hy
    rw [(hjets x hx).2 i j, (hjets y hy).2 i j]
    have hp := Real.rpow_le_rpow hδ.le (le_min (hw x hx) (hw y hy))
      (show 0 ≤ 2 + α by linarith)
    have h := (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
      (hj.2.2 i j x (hsub hx) y (hsub hy))
    calc
      _ ≤ (H * dist x y ^ α) / (R - r) ^ (2 + α) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr (by simpa [mul_comm] using h)
      _ = _ := by ring

open P201Specs.Elliptic.HalfSpaceLift

/-- The outer region for the constant-coefficient estimate. The inner region
is the upstream `normalizedHalfPatch ρ x`. -/
def outerHalfPatch {m : ℕ} (ρ : ℝ) (x : Space (m + 1)) : Set (Space (m + 1)) :=
  if 2 * ρ ≤ height x then ball x (2 * ρ) else
    ball (point (horizontal x) 0) (8 * ρ) ∩ closedHalfSpace m

/-- Every enlarged boundary patch lies within distance 16ρ of the freezing
point. The threshold includes equality, which is safe for the open ball. -/
theorem outerHalfPatch_subset_ball {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : Space (m + 1)} (hx : 0 ≤ height x) :
    outerHalfPatch ρ x ⊆ ball x (16 * ρ) := by
  unfold outerHalfPatch
  split_ifs with hh
  · exact ball_subset_ball (by linarith)
  · intro y hy
    have hq : dist (point (horizontal x) 0) x < 2 * ρ := by
      rw [dist_comm, P201.Elliptic.ConstantSchauder.dist_to_flat_plane, abs_of_nonneg hx]
      exact lt_of_not_ge hh
    have hyq : dist y (point (horizontal x) 0) < 8 * ρ := hy.1
    exact lt_of_le_of_lt (dist_triangle y (point (horizontal x) 0) x) (by linarith)

/-- Both alternatives respect the upper half-space. In the interior
alternative the entire outer ball has strictly positive height. -/
theorem outerHalfPatch_subset_closedHalfSpace {m : ℕ} {ρ : ℝ} {x : Space (m + 1)} :
    outerHalfPatch ρ x ⊆ closedHalfSpace m := by
  unfold outerHalfPatch
  split_ifs with hh
  · intro y hy
    change 0 ≤ height y
    exact le_of_lt (show 0 < height y from
      P201.Elliptic.ConstantSchauder.ball_subset_upper_halfSpace hh hy)
  · exact inter_subset_right

/-- Every point of the inner patch lies in the outer patch, and close pairs
lie together in the inner patch, including pairs with a point on the face. -/
theorem half_patch_near_pair {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x y : Space (m + 1)} (hx : 0 ≤ height x) (hy : 0 ≤ height y)
    (hxy : dist x y < ρ) :
    x ∈ P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x ∧
    y ∈ P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x ∧
    P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x ⊆ outerHalfPatch ρ x := by
  refine ⟨P201.Elliptic.ConstantSchauder.normalizedHalfPatch_mem hρ hx,
    (P201.Elliptic.ConstantSchauder.normalizedHalfPatch_near_pair hρ
      (s := closedHalfSpace m) Subset.rfl hx hy hxy).1, ?_⟩
  unfold P201.Elliptic.ConstantSchauder.normalizedHalfPatch outerHalfPatch
  split_ifs
  · exact ball_subset_ball (by linarith)
  · exact inter_subset_inter_left _ (ball_subset_ball (by linarith))

/-- All weights in the outer patch are comparable to the weight of the
freezing point, with constants independent of the coefficients and solution. -/
theorem weighted_half_patch_geometry {m : ℕ} {R μ : ℝ} {x : Space (m + 1)}
    (hx : x ∈ halfBallWithFace m R) (hμ : 0 < μ) (hμsmall : μ ≤ 1 / 32) :
    outerHalfPatch (μ * radialWeight 0 R x) x ⊆ halfBallWithFace m R ∧
      ∀ y ∈ outerHalfPatch (μ * radialWeight 0 R x) x,
        radialWeight 0 R x / 2 < radialWeight 0 R y ∧
        radialWeight 0 R y < 3 * radialWeight 0 R x / 2 := by
  have hd := P201.Elliptic.WeightedInterpolation.radialWeight_pos
    (inter_subset_left : halfBallWithFace m R ⊆ ball 0 R) hx
  have hρ : 0 < μ * radialWeight 0 R x := mul_pos hμ hd
  have hball := outerHalfPatch_subset_ball hρ hx.2
  have hh := outerHalfPatch_subset_closedHalfSpace (ρ := μ * radialWeight 0 R x) (x := x)
  constructor
  · intro y hy
    exact ⟨(radial_freezing_geometry hx.1 hμsmall (hball hy)).1, hh hy⟩
  · intro y hy
    exact (radial_freezing_geometry hx.1 hμsmall (hball hy)).2

/-- Local and outer within jets coincide on a half-space patch. Equality
comes from open-ball germs and does not assume an extension below the face. -/
theorem half_patch_jets {m : ℕ} {R r : ℝ} {p y : Space (m + 1)}
    (u : Space (m + 1) → ℝ)
    (hsub : ball p r ∩ closedHalfSpace m ⊆ halfBallWithFace m R)
    (hy : y ∈ ball p r ∩ closedHalfSpace m) :
    (∀ i, firstPartialWithin u (ball p r ∩ closedHalfSpace m) i y =
      firstPartialWithin u (halfBallWithFace m R) i y) ∧
    ∀ i j, secondPartialWithin u (ball p r ∩ closedHalfSpace m) i j y =
      secondPartialWithin u (halfBallWithFace m R) i j y := by
  have heq : ball p r ∩ closedHalfSpace m =ᶠ[nhds y] halfBallWithFace m R := by
    filter_upwards [isOpen_ball.mem_nhds hy.1, isOpen_ball.mem_nhds (hsub hy).1] with z hz hz'
    simp only [halfBallWithFace, mem_inter_iff, hz, hz', true_and]
  exact ⟨fun i => firstPartialWithin_congr_set u heq i,
    fun i j => secondPartialWithin_congr_set u heq i j⟩

/-- The weight and local Hölder scale cancel before estimating the
coefficient oscillation. This preserves the small μ^α factor: there is no
negative power of μ multiplying the unknown highest-order seminorm. -/
theorem freezing_highest_order_scale {α d μ β K N : ℝ}
    (hα : 0 ≤ α) (hd : 0 < d) (hd2 : d ≤ 2) (hμ : 0 < μ) (hβ : 0 < β)
    (hK : 0 ≤ K) (hN : 0 ≤ N) :
    d ^ (2 + α) * (K * (β * μ * d) ^ α * (N / (d / 2) ^ (2 + α))) ≤
      (K * β ^ α * (2 : ℝ) ^ (2 + α) * (2 : ℝ) ^ α) * μ ^ α * N := by
  have hdp : d ^ (2 + α) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have htwo : (2 : ℝ) ^ (2 + α) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have he : d ^ (2 + α) * (K * (β * μ * d) ^ α * (N / (d / 2) ^ (2 + α))) =
      (K * β ^ α * (2 : ℝ) ^ (2 + α) * μ ^ α * N) * d ^ α := by
    rw [Real.div_rpow hd.le (by norm_num),
      Real.mul_rpow (mul_pos hβ hμ).le hd.le, Real.mul_rpow hβ.le hμ.le]
    field_simp
  rw [he]
  have hp : d ^ α ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow hd.le hd2 hα
  have hnonneg : 0 ≤ K * β ^ α * (2 : ℝ) ^ (2 + α) * μ ^ α * N := by positivity
  calc
    _ ≤ (K * β ^ α * (2 : ℝ) ^ (2 + α) * μ ^ α * N) * (2 : ℝ) ^ α :=
      mul_le_mul_of_nonneg_left hp hnonneg
    _ = _ := by ring

/-- Choose the freezing scale using only the constants fixed before the
coefficient fields. This is the first absorption choice. -/
theorem choose_freezing_scale {α A K : ℝ}
    (hα : 0 < α) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 / 32 ∧ A * K * μ ^ α ≤ 1 / 4 := by
  let b := 1 / (4 * (A * K + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  let t := b ^ (1 / α)
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  have htα : t ^ α = b := by
    dsimp [t]
    rw [← Real.rpow_mul hb.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨min (1 / 32) t, lt_min (by norm_num) ht, min_le_left _ _, ?_⟩
  have hp : min (1 / 32) t ^ α ≤ b := by
    rw [← htα]
    exact Real.rpow_le_rpow (le_min (by norm_num) ht.le) (min_le_right _ _) hα.le
  calc
    A * K * min (1 / 32) t ^ α ≤ A * K * b :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hA hK)
    _ ≤ 1 / 4 := by
      dsimp [b]
      have hden : 0 < 4 * (A * K + 1) := by positivity
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith [mul_nonneg hA hK]

/-- Tangential translation of the full constant-matrix estimate. The matrix
and the center both vary after the constant has been fixed. -/
theorem translated_half_ball_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ), MatrixBounds ell upper A →
        ∀ (q : Space (m + 1)), height q = 0 → ∀ r : ℝ, 0 < r →
        ∀ u f : Space (m + 1) → ℝ,
          ContDiffOn ℝ 2 u (ball q (2 * r) ∩ openHalfSpace m) →
          ContinuousOn u (ball q (2 * r) ∩ closedHalfSpace m) →
          (∀ x ∈ ball q (2 * r), height x = 0 → u x = 0) →
          IsBoundedOn u (ball q (2 * r) ∩ closedHalfSpace m) →
          IsHolderOn α f (ball q (2 * r) ∩ closedHalfSpace m) →
          (∀ x ∈ ball q (2 * r) ∩ openHalfSpace m, constantOperator A u x = f x) →
          IsC2HolderUpToOn α u (ball q r ∩ closedHalfSpace m) ∧
          scaledWithinSolutionNorm α r u (ball q r ∩ closedHalfSpace m) ≤
            C * scaledDataNorm α r u f (ball q (2 * r) ∩ closedHalfSpace m) := by
  obtain ⟨C, hC, hest⟩ :=
    P201.Elliptic.ConstantSchauder.half_ball_estimate m α hα hα1 ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro A hA q hq r hr u f hu hc hz hb hf heq
  have hmap := (P201.Elliptic.ConstantSchauder.translation_bijOn q
    (halfBall m (2 * r))).mapsTo
  rw [P201.Elliptic.ConstantSchauder.translation_halfBall q hq] at hmap
  have hmapf := (P201.Elliptic.ConstantSchauder.translation_bijOn q
    (halfBallWithFace m (2 * r))).mapsTo
  rw [P201.Elliptic.ConstantSchauder.translation_halfBallWithFace q hq] at hmapf
  have hv := hu.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  have hvc := hc.comp (continuous_const.add continuous_id).continuousOn hmapf
  have hvz : ∀ x ∈ flatFace m (2 * r), u (q + x) = 0 := by
    intro x hx
    apply hz (q + x) (hmapf ⟨hx.1, by change 0 ≤ height x; rw [hx.2]⟩).1
    change height q + height x = 0
    rw [hq, hx.2, add_zero]
  have hvb := P201.Elliptic.PoissonSchauder.isBoundedOn_mapsTo_mul hmapf
    zero_le_one hb (fun x _ => (one_mul _).symm)
  have hfg := P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul hmapf
    zero_le_one zero_le_one hf (fun x _ y _ => by simp)
    (fun x _ => (one_mul _).symm)
  have hveq : ∀ x ∈ halfBall m (2 * r),
      constantOperator A (fun y => u (q + y)) x = f (q + x) := by
    intro x hx
    unfold constantOperator
    simp_rw [P201.Elliptic.ConstantSchauder.secondPartial_translation]
    exact heq (q + x) (hmap hx)
  obtain ⟨hvreg, hvnorm⟩ := hest A hA r hr _ _ hv hvc hvz hvb hfg hveq
  obtain ⟨hreg, hnorm⟩ :=
    P201.Elliptic.ConstantSchauder.within_c2_translation_transfer
      (r := r) (halfBallWithFace m r) q hvreg
  rw [P201.Elliptic.ConstantSchauder.translation_halfBallWithFace q hq] at hreg hnorm
  have hdata := P201.Elliptic.ConstantSchauder.scaledDataNorm_translation
    α r u f (halfBallWithFace m (2 * r)) q
  rw [P201.Elliptic.ConstantSchauder.translation_halfBallWithFace q hq] at hdata
  exact ⟨hreg, by rwa [← hnorm, ← hdata]⟩

/-- Positivity of the canonical scaled data expression, including empty
sets. This uses positivity of real norm suprema rather than finiteness. -/
theorem scaledDataNorm_nonneg {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    (u f : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ scaledDataNorm α r u f s := by
  unfold scaledDataNorm
  exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
    (mul_nonneg (sq_nonneg _) (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)))
    (mul_nonneg (Real.rpow_nonneg hr _)
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _))

/-- Both alternatives of the boundary patch construction admit the same
constant-matrix estimate. This is an application of actual PDE estimates,
not a hypothesis that the patches have a Schauder certificate. -/
theorem constant_half_patch_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ), MatrixBounds ell upper A →
        ∀ (ρ : ℝ), 0 < ρ → ∀ (x : Space (m + 1)), 0 ≤ height x →
        ∀ u F : Space (m + 1) → ℝ,
          ContDiffOn ℝ 2 u (outerHalfPatch ρ x) →
          (∀ y ∈ outerHalfPatch ρ x, height y = 0 → u y = 0) →
          IsBoundedOn u (outerHalfPatch ρ x) →
          IsHolderOn α F (outerHalfPatch ρ x) →
          (∀ y ∈ outerHalfPatch ρ x ∩ openHalfSpace m, constantOperator A u y = F y) →
          IsC2HolderUpToOn α u
            (P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) ∧
          scaledWithinSolutionNorm α
            (P201.Elliptic.ConstantSchauder.normalizedHalfScale ρ x) u
            (P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) ≤
          C * scaledDataNorm α
            (P201.Elliptic.ConstantSchauder.normalizedHalfScale ρ x) u F
            (outerHalfPatch ρ x) := by
  obtain ⟨Ci, hCi, hi⟩ := P201.Elliptic.ConstantSchauder.interior_ball_estimate
    (by omega : 1 ≤ m + 1) α hα hα1 ell upper hell hupper
  obtain ⟨Cb, hCb, hb⟩ := translated_half_ball_estimate m α hα hα1 ell upper hell hupper
  refine ⟨Ci + Cb, add_pos hCi hCb, ?_⟩
  intro A hA ρ hρ x hx u F hu hz hub hF heq
  unfold outerHalfPatch at hu hz hub hF heq ⊢
  unfold P201.Elliptic.ConstantSchauder.normalizedHalfPatch
    P201.Elliptic.ConstantSchauder.normalizedHalfScale
  split_ifs at hu hz hub hF heq ⊢ with hh
  · obtain ⟨hreg, hnorm⟩ := hi A hA x ρ hρ u F hu hub hF
      (fun y hy => heq y ⟨hy, P201.Elliptic.ConstantSchauder.ball_subset_upper_halfSpace hh hy⟩)
    obtain ⟨hwreg, hwnorm⟩ :=
      P201.Elliptic.ConstantSchauder.within_estimate_of_extension
        ⟨ball x (2 * ρ), isOpen_ball⟩ isOpen_ball.uniqueDiffOn
        (ball_subset_ball (show ρ ≤ 2 * ρ by linarith)) hu hreg (fun _ _ => rfl)
    refine ⟨hwreg, ?_⟩
    rw [hwnorm]
    exact hnorm.trans (mul_le_mul_of_nonneg_right (by linarith)
      (scaledDataNorm_nonneg hρ.le u F _))
  · have hr : 0 < 4 * ρ := by positivity
    have he : 2 * (4 * ρ) = 8 * ρ := by ring
    have hreg := hb A hA (point (horizontal x) 0) (by simp [height, point])
      (4 * ρ) hr u F
    rw [he] at hreg
    obtain ⟨hclass, hnorm⟩ := hreg (hu.mono (fun y hy => ⟨hy.1,
      (show 0 ≤ height y from le_of_lt (show 0 < height y from hy.2))⟩)) hu.continuousOn
      (fun y hy hyh => hz y ⟨hy, by change 0 ≤ height y; rw [hyh]⟩ hyh)
      hub hF (fun y hy => heq y ⟨⟨hy.1, (show 0 ≤ height y from le_of_lt hy.2)⟩, hy.2⟩)
    exact ⟨hclass, hnorm.trans (mul_le_mul_of_nonneg_right (by linarith)
      (scaledDataNorm_nonneg hr.le u F _))⟩

/-- The separated weighted freezing bound as a scalar expression. `δ` is the
lower weight on the patch, `L` its oscillation radius, and `σ` its estimate
scale. Keeping these parameters separate allows enlarged boundary patches. -/
def freezingDataBound (α K δ L σ U G Q V W N F H : ℝ) : ℝ :=
  U + σ ^ 2 * (F + K * L ^ α * (Q / δ ^ 2) + K * (G / δ + U)) +
    σ ^ (2 + α) * (H + K * L ^ α * (N / δ ^ (2 + α)) + K * (Q / δ ^ 2) +
      K * (W / δ ^ (1 + α) + G / δ + V / δ ^ α + U))

/-- Freezing on the actual near-pair patch of a half-ball. All derivatives in
the right-hand side belong to the original outer half-ball, including on its
face. The constant is fixed before every coefficient field, solution and
radius. -/
theorem weighted_frozen_half_patch_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c u f : Space (m + 1) → ℝ)
        (R μ : ℝ), 0 < μ → μ ≤ 1 / 32 →
        (∀ y ∈ halfBallWithFace m R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ halfBallWithFace m R, ∀ ξ : Space (m + 1),
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (halfBallWithFace m R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (halfBallWithFace m R)) ∧
          IsHolderOn α c (halfBallWithFace m R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (halfBallWithFace m R)) +
          (∑ i, holderNormOn α (fun y => b y i) (halfBallWithFace m R)) +
          holderNormOn α c (halfBallWithFace m R) ≤ K →
        ContDiffOn ℝ 2 u (halfBallWithFace m R) →
        (∀ y ∈ flatFace m R, u y = 0) →
        IsBoundedOn u (halfBallWithFace m R) → IsHolderOn α f (halfBallWithFace m R) →
        FiniteWeightedNorms α 0 R u (halfBallWithFace m R) →
        (∀ y ∈ halfBall m R, nondivergenceOperator a b c u y = f y) →
        ∀ x ∈ halfBallWithFace m R,
          let d := radialWeight 0 R x
          let ρ := μ * d
          let σ := P201.Elliptic.ConstantSchauder.normalizedHalfScale ρ x
          let s := halfBallWithFace m R
          let t := P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x
          IsC2HolderUpToOn α u t ∧ scaledWithinSolutionNorm α σ u t ≤
            C * freezingDataBound α K (d / 2) (16 * ρ) σ
              (M0 u s) (M1 0 R u s) (M2 0 R u s)
              (N0 α 0 R u s) (N1 α 0 R u s) (N2 α 0 R u s)
              (supNormOn f s) (P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f s) := by
  obtain ⟨C, hC, hest⟩ := constant_half_patch_estimate m α hα hα1 ell (K + 1)
    hell (by linarith)
  refine ⟨C, hC, ?_⟩
  intro a b c u f R μ hμ hμsmall hsym hellip hcoeff hK hu hz hub hf hfinite heq x hx
  dsimp only
  let d := radialWeight 0 R x
  let ρ := μ * d
  let s := halfBallWithFace m R
  let t := outerHalfPatch ρ x
  have hd : 0 < d := P201.Elliptic.WeightedInterpolation.radialWeight_pos
    (inter_subset_left : s ⊆ ball 0 R) hx
  have hρ : 0 < ρ := mul_pos hμ hd
  have hgeom := weighted_half_patch_geometry hx hμ hμsmall
  have hsub : t ⊆ s := hgeom.1
  have hxt : x ∈ t := (half_patch_near_pair hρ hx.2 hx.2
    (by simpa using hρ)).2.2
      (P201.Elliptic.ConstantSchauder.normalizedHalfPatch_mem hρ hx.2)
  have hsource := weighted_frozenWithinSource_bounds hα.le (half_pos hd)
    (inter_subset_left : s ⊆ ball 0 R) hsub hxt (outerHalfPatch_subset_ball hρ hx.2)
    (fun y hy => (hgeom.2 y hy).1.le) hcoeff hK hf hfinite
  obtain ⟨hreg, hnorm⟩ := hest (a x)
    (matrixBounds_of_coefficientNorm ⟨hsym, hellip⟩ hcoeff hK hx)
    ρ hρ x hx.2 u (frozenWithinSource a b c u f s x) (hu.mono hsub)
    (fun y hy hyh => hz y ⟨(hsub hy).1, hyh⟩)
    (by obtain ⟨M, hM, hb⟩ := hub; exact ⟨M, hM, fun y hy => hb y (hsub hy)⟩)
    hsource.isHolderOn (by
      intro y hy
      have hys : y ∈ halfBall m R := ⟨(hsub hy.1).1, hy.2⟩
      exact constantOperator_eq_frozenWithinSource a b c u f
        (halfBallWithFace_mem_nhds hys) x (heq y hys))
  refine ⟨hreg, hnorm.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  exact weighted_scaledDataNorm_frozenWithinSource_le hα.le (half_pos hd)
    (P201.Elliptic.ConstantSchauder.normalizedHalfScale_pos hρ x).le
    (inter_subset_left : s ⊆ ball 0 R) hsub hxt (outerHalfPatch_subset_ball hρ hx.2)
    (fun y hy => (hgeom.2 y hy).1.le) hcoeff hK hf hub hfinite

/-- The inner near-pair patch has the same derivative germs as the original
half-ball at all its points, even on the plane. -/
theorem normalized_half_patch_jets {m : ℕ} {R ρ : ℝ}
    {x y : Space (m + 1)} (u : Space (m + 1) → ℝ)
    (hρ : 0 < ρ)
    (hsub : P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x ⊆
      halfBallWithFace m R)
    (hy : y ∈ P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) :
    (∀ i, firstPartialWithin u
      (P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) i y =
      firstPartialWithin u (halfBallWithFace m R) i y) ∧
    ∀ i j, secondPartialWithin u
      (P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) i j y =
      secondPartialWithin u (halfBallWithFace m R) i j y := by
  unfold P201.Elliptic.ConstantSchauder.normalizedHalfPatch at hsub hy ⊢
  split_ifs at hsub hy ⊢ with hh
  · have hys : y ∈ halfBall m R := ⟨(hsub hy).1,
      P201.Elliptic.ConstantSchauder.ball_subset_upper_halfSpace
        hh (ball_subset_ball (show ρ ≤ 2 * ρ by linarith) hy)⟩
    have heq : ball x ρ =ᶠ[nhds y] halfBallWithFace m R := by
      filter_upwards [isOpen_ball.mem_nhds hy, halfBallWithFace_mem_nhds hys] with z hz hz'
      exact propext ⟨fun _ => hz', fun _ => hz⟩
    exact ⟨fun i => firstPartialWithin_congr_set u heq i,
      fun i j => secondPartialWithin_congr_set u heq i j⟩
  · exact half_patch_jets u hsub hy

/-- Extract the Hessian difference from a local full scaled estimate, while
retaining the outer derivative representative. The inverse patch scale is
separated from the coefficient-oscillation factor. -/
theorem weighted_pair_of_patch_estimate {n : ℕ} {α σ d E : ℝ}
    {u : Space n → ℝ} {s t : Set (Space n)} {x y : Space n}
    (hσ : 0 < σ) (hd : 0 ≤ d) (hu : IsC2HolderUpToOn α u t)
    (hx : x ∈ t) (hy : y ∈ t)
    (hjetsx : ∀ i j, secondPartialWithin u t i j x = secondPartialWithin u s i j x)
    (hjetsy : ∀ i j, secondPartialWithin u t i j y = secondPartialWithin u s i j y)
    (hbound : scaledWithinSolutionNorm α σ u t ≤ E) (i j : Fin n) :
    d ^ (2 + α) * ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
      (d ^ (2 + α) / σ ^ (2 + α) * E) * dist x y ^ α := by
  have hi := (P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_bounds hσ.le hu).2.2.2
    i j x hx y hy
  rw [hjetsx i j, hjetsy i j] at hi
  have he : σ ^ (2 + α) *
      ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
      E * dist x y ^ α := hi.trans
        (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg dist_nonneg _))
  calc
    _ ≤ d ^ (2 + α) * ((E * dist x y ^ α) / σ ^ (2 + α)) :=
      mul_le_mul_of_nonneg_left
        ((le_div_iff₀ (Real.rpow_pos_of_pos hσ _)).mpr (by simpa [mul_comm] using he))
        (Real.rpow_nonneg hd _)
    _ = _ := by ring

/-- Sum the close/far estimates for the actual defining weighted pair sets.
The near-pair hypothesis is an elementary bound for the original Hessian jets;
it is kept explicit here to separate supremum algebra from PDE patch proofs. -/
theorem N2_le_of_near_pairs {n : ℕ} {α R μ E : ℝ} {z : Space n}
    {s : Set (Space n)} {u : Space n → ℝ}
    (hα : 0 ≤ α) (hμ : 0 < μ) (hE : 0 ≤ E) (hs : s ⊆ ball z R)
    (hf : FiniteWeightedNorms α z R u s)
    (hnear : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      radialWeight z R x ≤ radialWeight z R y →
      dist x y < μ * radialWeight z R x →
      radialWeight z R x ^ (2 + α) *
        ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
        E * dist x y ^ α) :
    N2 α z R u s ≤ (n : ℝ) ^ 2 * (E + 2 * M2 z R u s / μ ^ α) := by
  have hM : 0 ≤ M2 z R u s := P201.Elliptic.WeightedInterpolation.M2_nonneg hs u
  have hB : 0 ≤ E + 2 * M2 z R u s / μ ^ α := by positivity
  have hp (i j : Fin n) : weightedSeminormOn 2 α z R (secondPartialWithin u s i j) s ≤
      E + 2 * M2 z R u s / μ ^ α := by
    apply P201.Elliptic.WeightedInterpolation.weightedSeminormOn_le hB
    intro x hx y hy
    by_cases hfar : μ * min (radialWeight z R x) (radialWeight z R y) ≤ dist x y
    · exact (weighted_far_pair_bound hs hf hα hμ i j hx hy hfar).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
    · have hclose : dist x y < μ * min (radialWeight z R x) (radialWeight z R y) :=
        lt_of_not_ge hfar
      have he : min (radialWeight z R x) (radialWeight z R y) ^ (2 + α) *
          ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
          E * dist x y ^ α := by
        rcases le_total (radialWeight z R x) (radialWeight z R y) with hxy | hyx
        · rw [min_eq_left hxy]
          exact hnear i j x hx y hy hxy (by simpa [min_eq_left hxy] using hclose)
        · rw [min_eq_right hyx, norm_sub_rev, dist_comm]
          exact hnear i j y hy x hx hyx (by simpa [min_eq_right hyx, dist_comm] using hclose)
      exact he.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity))
        (Real.rpow_nonneg dist_nonneg _))
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (E + 2 * M2 z R u s / μ ^ α) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = _ := by simp; ring

/-- The interior patch counterpart of the weighted frozen half-patch theorem.
Both its source and its unknown weighted norms use the original outer jets. -/
theorem weighted_frozen_ball_patch_estimate
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c u f : Space n → ℝ)
        (z : Space n) (R μ : ℝ), 0 < μ → μ ≤ 1 / 32 →
        (∀ y ∈ ball z R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ ball z R, ∀ ξ : Space n,
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (ball z R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (ball z R)) ∧
          IsHolderOn α c (ball z R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (ball z R)) +
          (∑ i, holderNormOn α (fun y => b y i) (ball z R)) +
          holderNormOn α c (ball z R) ≤ K →
        ContDiffOn ℝ 2 u (ball z R) →
        IsBoundedOn u (ball z R) → IsHolderOn α f (ball z R) →
        FiniteWeightedNorms α z R u (ball z R) →
        (∀ y ∈ ball z R, nondivergenceOperator a b c u y = f y) →
        ∀ x ∈ ball z R,
          let d := radialWeight z R x
          let ρ := μ * d
          let s := ball z R
          IsC2HolderUpToOn α u (ball x ρ) ∧ scaledWithinSolutionNorm α ρ u (ball x ρ) ≤
            C * freezingDataBound α K (d / 2) (16 * ρ) ρ
              (M0 u s) (M1 z R u s) (M2 z R u s)
              (N0 α z R u s) (N1 α z R u s) (N2 α z R u s)
              (supNormOn f s) (P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f s) := by
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.ConstantSchauder.interior_ball_estimate
    hn α hα hα1 ell (K + 1) hell (by linarith)
  refine ⟨C, hC, ?_⟩
  intro a b c u f z R μ hμ hμsmall hsym hellip hcoeff hK hu hub hf hfinite heq x hx
  dsimp only
  let d := radialWeight z R x
  let ρ := μ * d
  let s := ball z R
  let t := ball x (2 * ρ)
  have hd : 0 < d := P201.Elliptic.WeightedInterpolation.radialWeight_pos Subset.rfl hx
  have hρ : 0 < ρ := mul_pos hμ hd
  have ht : t ⊆ ball x (16 * ρ) := ball_subset_ball (by linarith)
  have hsub : t ⊆ s := fun y hy => (radial_freezing_geometry hx hμsmall (ht hy)).1
  have hw (y : Space n) (hy : y ∈ t) : d / 2 ≤ radialWeight z R y :=
    (radial_freezing_geometry hx hμsmall (ht hy)).2.1.le
  have hxt : x ∈ t := mem_ball_self (by positivity)
  have hsource := weighted_frozenWithinSource_bounds hα.le (half_pos hd)
    (Subset.rfl : s ⊆ ball z R) hsub hxt ht hw hcoeff hK hf hfinite
  obtain ⟨hreg, hnorm⟩ := hest (a x)
    (matrixBounds_of_coefficientNorm ⟨hsym, hellip⟩ hcoeff hK hx) x ρ hρ
    u (frozenWithinSource a b c u f s x) (hu.mono hsub)
    (by obtain ⟨M, hM, hb⟩ := hub; exact ⟨M, hM, fun y hy => hb y (hsub hy)⟩)
    hsource.isHolderOn (fun y hy => constantOperator_eq_frozenWithinSource a b c u f
      (isOpen_ball.mem_nhds (hsub hy)) x (heq y (hsub hy)))
  obtain ⟨hwreg, hwnorm⟩ := P201.Elliptic.ConstantSchauder.within_estimate_of_extension
    ⟨s, isOpen_ball⟩ isOpen_ball.uniqueDiffOn
    ((ball_subset_ball (show ρ ≤ 2 * ρ by linarith)).trans hsub) hu hreg (fun _ _ => rfl)
  refine ⟨hwreg, ?_⟩
  rw [hwnorm]
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (weighted_scaledDataNorm_frozenWithinSource_le hα.le (half_pos hd) hρ.le
      (Subset.rfl : s ⊆ ball z R) hsub hxt ht hw hcoeff hK hf hub hfinite) hC.le)
/-- Exact cancellation of the local scale in the weighted freezing bound.
The sole highest-order term has no inverse power of the patch scale. -/
theorem freezing_pair_scale_identity {α d t l : ℝ} (hd : 0 < d) (ht : 0 < t)
    (K U G Q V W N F H : ℝ) :
    d ^ (2 + α) / (t * d) ^ (2 + α) *
      freezingDataBound α K (d / 2) (l * d) (t * d) U G Q V W N F H =
    U / t ^ (2 + α) +
      (d ^ 2 * F + 4 * K * (l * d) ^ α * Q + 2 * K * d * G + K * d ^ 2 * U) /
        t ^ α +
      d ^ (2 + α) * H + K * (l * d) ^ α * 2 ^ (2 + α) * N +
      4 * K * d ^ α * Q + K * 2 ^ (1 + α) * d * W +
      2 * K * d ^ (1 + α) * G + K * 2 ^ α * d ^ 2 * V +
      K * d ^ (2 + α) * U := by
  have hdα := (Real.rpow_pos_of_pos hd α).ne'
  have htα := (Real.rpow_pos_of_pos ht α).ne'
  have h2α := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α).ne'
  unfold freezingDataBound
  simp only [Real.mul_rpow ht.le hd.le, Real.div_rpow hd.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_add hd, Real.rpow_add ht,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_two, Real.rpow_one]
  field_simp [hd.ne', ht.ne', hdα, htα, h2α]
  <;> ring
/-- A finite coefficient for the terms subsequently controlled by weighted
interpolation. It is allowed to grow as the patch scale tends to zero. -/
def freezingRemainderFactor (α K t l : ℝ) : ℝ :=
  1 + 1 / t ^ (2 + α) + 1 / t ^ α +
    4 * K * l ^ α * 2 ^ α / t ^ α + 4 * K / t ^ α +
    4 * K * 2 ^ α + 2 * K * 2 ^ (1 + α) + K * 2 ^ (2 + α)

/-- Uniform scalar bound for a near-pair contribution. The highest-order
unknown has coefficient O(l^α), while every remaining coefficient is finite
for t>0. Data keep their outer scaling, so this bound remains uniform as the
outer radius tends to zero. -/
theorem freezing_pair_scale_bound {α d R t l K U G Q V W N F H : ℝ}
    (hα : 0 ≤ α) (hd : 0 < d) (hdR : d ≤ R) (hd2 : d ≤ 2)
    (ht : 0 < t) (hl : 0 ≤ l) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hN : 0 ≤ N) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    d ^ (2 + α) / (t * d) ^ (2 + α) *
      freezingDataBound α K (d / 2) (l * d) (t * d) U G Q V W N F H ≤
    K * l ^ α * 2 ^ (2 + α) * 2 ^ α * N +
      freezingRemainderFactor α K t l *
        (U + R ^ 2 * F + R ^ (2 + α) * H + G + Q + V + W) := by
  have hR : 0 < R := hd.trans_le hdR
  have hp : 0 ≤ 2 + α := by linarith
  have hp1 : 0 ≤ 1 + α := by linarith
  have hdα : d ^ α ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow hd.le hd2 hα
  have hd1α : d ^ (1 + α) ≤ (2 : ℝ) ^ (1 + α) :=
    Real.rpow_le_rpow hd.le hd2 hp1
  have hd2α : d ^ (2 + α) ≤ (2 : ℝ) ^ (2 + α) :=
    Real.rpow_le_rpow hd.le hd2 hp
  have hdR2 : d ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hd.le hdR 2
  have hdRα : d ^ (2 + α) ≤ R ^ (2 + α) := Real.rpow_le_rpow hd.le hdR hp
  have hdsq : d ^ 2 ≤ (4 : ℝ) := by nlinarith
  have hld : (l * d) ^ α ≤ l ^ α * 2 ^ α := by
    rw [Real.mul_rpow hl hd.le]
    exact mul_le_mul_of_nonneg_left hdα (Real.rpow_nonneg hl _)
  let D := U + R ^ 2 * F + R ^ (2 + α) * H + G + Q + V + W
  have hRF : 0 ≤ R ^ 2 * F := by positivity
  have hRH : 0 ≤ R ^ (2 + α) * H := by positivity
  have hDU : U ≤ D := by dsimp [D]; linarith
  have hDF : R ^ 2 * F ≤ D := by dsimp [D]; linarith
  have hDH : R ^ (2 + α) * H ≤ D := by dsimp [D]; linarith
  have hDQ : Q ≤ D := by dsimp [D]; linarith
  have hDGU : G + U ≤ D := by dsimp [D]; linarith
  have hDQV : Q + V ≤ D := by dsimp [D]; linarith
  have hDWG : W + G ≤ D := by dsimp [D]; linarith
  rw [freezing_pair_scale_identity hd ht]
  calc
    _ ≤ U / t ^ (2 + α) +
        (R ^ 2 * F + 4 * K * (l ^ α * 2 ^ α) * Q +
          2 * K * 2 * G + K * 4 * U) / t ^ α +
        R ^ (2 + α) * H + K * (l ^ α * 2 ^ α) * 2 ^ (2 + α) * N +
        4 * K * 2 ^ α * Q + K * 2 ^ (1 + α) * 2 * W +
        2 * K * 2 ^ (1 + α) * G + K * 2 ^ α * 4 * V +
        K * 2 ^ (2 + α) * U := by
      gcongr
    _ = K * l ^ α * 2 ^ (2 + α) * 2 ^ α * N +
        (1 / t ^ (2 + α) * U + 1 / t ^ α * (R ^ 2 * F) +
          (4 * K * l ^ α * 2 ^ α / t ^ α) * Q +
          (4 * K / t ^ α) * (G + U) + R ^ (2 + α) * H +
          (4 * K * 2 ^ α) * (Q + V) +
          (2 * K * 2 ^ (1 + α)) * (W + G) + K * 2 ^ (2 + α) * U) := by ring
    _ ≤ K * l ^ α * 2 ^ (2 + α) * 2 ^ α * N +
        (1 / t ^ (2 + α) * D + 1 / t ^ α * D +
          (4 * K * l ^ α * 2 ^ α / t ^ α) * D +
          (4 * K / t ^ α) * D + D +
          (4 * K * 2 ^ α) * D + (2 * K * 2 ^ (1 + α)) * D +
          K * 2 ^ (2 + α) * D) := by
      gcongr
    _ = _ := by unfold freezingRemainderFactor; dsimp [D]; ring

/-- The coefficient of the small highest-order error is independent of the
chosen freezing radius. -/
def principalFreezingFactor (α : ℝ) : ℝ :=
  16 ^ α * 2 ^ (2 + α) * 2 ^ α

/-- One finite lower-order factor covers interior and plane-centered patches. -/
def nearFreezingFactor (α K μ : ℝ) : ℝ :=
  freezingRemainderFactor α K μ (16 * μ) +
    freezingRemainderFactor α K (4 * μ) (16 * μ)

theorem freezingRemainderFactor_pos {α K t l : ℝ}
    (ht : 0 < t) (hl : 0 ≤ l) (hK : 0 ≤ K) :
    0 < freezingRemainderFactor α K t l := by
  unfold freezingRemainderFactor
  positivity

/-- Uniform form of the scale calculation for the two patch radii. -/
theorem freezing_pair_uniform_bound {α d R μ β K U G Q V W N F H : ℝ}
    (hα : 0 ≤ α) (hd : 0 < d) (hdR : d ≤ R) (hR2 : R ≤ 2)
    (hμ : 0 < μ) (hβ : β = 1 ∨ β = 4) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hN : 0 ≤ N) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    d ^ (2 + α) / (β * μ * d) ^ (2 + α) *
      freezingDataBound α K (d / 2) (16 * (μ * d)) (β * μ * d) U G Q V W N F H ≤
    principalFreezingFactor α * K * μ ^ α * N + nearFreezingFactor α K μ *
      (U + R ^ 2 * F + R ^ (2 + α) * H + G + Q + V + W) := by
  have hβpos : 0 < β := by rcases hβ with rfl | rfl <;> norm_num
  have hR : 0 ≤ R := hd.le.trans hdR
  have hp1 := freezingRemainderFactor_pos (α := α) hμ (by positivity : 0 ≤ 16 * μ) hK
  have hp4 := freezingRemainderFactor_pos (α := α) (by positivity : 0 < 4 * μ)
    (by positivity : 0 ≤ 16 * μ) hK
  have hfactor : freezingRemainderFactor α K (β * μ) (16 * μ) ≤
      nearFreezingFactor α K μ := by
    rcases hβ with rfl | rfl
    · simpa only [one_mul, nearFreezingFactor] using
        (le_add_of_nonneg_right hp4.le :
          freezingRemainderFactor α K μ (16 * μ) ≤ _)
    · exact le_add_of_nonneg_left hp1.le
  have hscale := freezing_pair_scale_bound hα hd hdR (hdR.trans hR2)
    (mul_pos hβpos hμ) (by positivity : 0 ≤ 16 * μ) hK hU hG hQ hV hW hN hF hH
  have hL : 16 * μ * d = 16 * (μ * d) := by ring
  rw [hL, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hμ.le] at hscale
  have hsmall : K * (16 ^ α * μ ^ α) * 2 ^ (2 + α) * 2 ^ α * N =
      principalFreezingFactor α * K * μ ^ α * N := by unfold principalFreezingFactor; ring
  rw [hsmall] at hscale
  exact hscale.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactor
    (by positivity : 0 ≤ U + R ^ 2 * F + R ^ (2 + α) * H + G + Q + V + W)))

/-- Combine the actual scaled patch estimate with the uniform freezing
calculation. The only analytic premise here is a bound for the local patch;
the preceding ball/half-patch theorems supply that bound from the PDE. -/
theorem freezing_pair_of_patch {n : ℕ} {α R μ β K C : ℝ} {z x y : Space n}
    {u f : Space n → ℝ} {s t : Set (Space n)}
    (hα : 0 ≤ α) (hR2 : R ≤ 2) (hμ : 0 < μ) (hβ : β = 1 ∨ β = 4)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hs : s ⊆ ball z R) (hx : x ∈ s)
    (htx : x ∈ t) (hty : y ∈ t) (hu : IsC2HolderUpToOn α u t)
    (hjetsx : ∀ i j, secondPartialWithin u t i j x = secondPartialWithin u s i j x)
    (hjetsy : ∀ i j, secondPartialWithin u t i j y = secondPartialWithin u s i j y)
    (hpatch : scaledWithinSolutionNorm α (β * μ * radialWeight z R x) u t ≤
      C * freezingDataBound α K (radialWeight z R x / 2)
        (16 * (μ * radialWeight z R x)) (β * μ * radialWeight z R x)
        (M0 u s) (M1 z R u s) (M2 z R u s)
        (N0 α z R u s) (N1 α z R u s) (N2 α z R u s)
        (supNormOn f s) (P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f s))
    (i j : Fin n) :
    radialWeight z R x ^ (2 + α) *
      ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
      (C * principalFreezingFactor α * K * μ ^ α * N2 α z R u s +
        C * nearFreezingFactor α K μ *
          (scaledDataNorm α R u f s + M1 z R u s + M2 z R u s +
            N0 α z R u s + N1 α z R u s)) * dist x y ^ α := by
  have hd := P201.Elliptic.WeightedInterpolation.radialWeight_pos hs hx
  have hβpos : 0 < β := by rcases hβ with rfl | rfl <;> norm_num
  have hN0 : 0 ≤ N0 α z R u s :=
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s u 0 hs
  have hN1 : 0 ≤ N1 α z R u s := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s
      (firstPartialWithin u s i) 1 hs
  have hscale := freezing_pair_uniform_bound hα hd
    (P201.Elliptic.WeightedInterpolation.radialWeight_le z x R) hR2 hμ hβ hK
    (P201.Elliptic.PoissonSchauder.supNormOn_nonneg u s)
    (P201.Elliptic.WeightedInterpolation.M1_nonneg hs u)
    (P201.Elliptic.WeightedInterpolation.M2_nonneg hs u) hN0 hN1
    (P201.Elliptic.WeightedInterpolation.N2_nonneg (α := α) hs u)
    (P201.Elliptic.PoissonSchauder.supNormOn_nonneg f s)
    (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f s)
  have hpair := weighted_pair_of_patch_estimate (mul_pos (mul_pos hβpos hμ) hd)
    hd.le hu htx hty hjetsx hjetsy hpatch i j
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC)
    (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α)
  dsimp [M0] at hpair
  unfold scaledDataNorm
  apply hpair.trans
  convert h using 1 <;> ring

/-- The two absorptions, with a single resulting constant for the top and
lower weighted norms. All parameters are scalar bounds already proved from
the PDE and interpolation. -/
theorem absorb_freezing_norms {N T D U q B Cε : ℝ}
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hU : U ≤ D)
    (hB : 0 ≤ B) (hCε : 0 ≤ Cε) (hq : q ≤ 1 / 4)
    (hest : N ≤ q * N + B * (D + T))
    (hi : T ≤ (1 / (4 * (B + 1))) * N + Cε * U) :
    N ≤ (1 + 2 * B * (1 + Cε) + Cε) * D ∧
      T ≤ (1 + 2 * B * (1 + Cε) + Cε) * D := by
  have hden : 0 < 4 * (B + 1) := by positivity
  have hε : 0 ≤ 1 / (4 * (B + 1)) := by positivity
  have hε1 : 1 / (4 * (B + 1)) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith
  have hsmall : q + B * (1 / (4 * (B + 1))) ≤ (1 : ℝ) / 2 := by
    have h : B * (1 / (4 * (B + 1))) ≤ (1 : ℝ) / 4 := by
      rw [mul_one_div, div_le_iff₀ hden]
      linarith
    linarith
  have hNb := absorb_with_interpolation hN hB hsmall hest hi
  have hN' : N ≤ (2 * B * (1 + Cε)) * D := by
    calc
      N ≤ 2 * B * (D + Cε * U) := hNb
      _ ≤ 2 * B * (D + Cε * D) := by gcongr
      _ = _ := by ring
  constructor
  · nlinarith
  · have h := mul_le_mul_of_nonneg_left hU hCε
    have ht : T ≤ N + Cε * D :=
      hi.trans (add_le_add (mul_le_of_le_one_left hN hε1) h)
    nlinarith

/-- Pointwise weighted bounds are extracted only from finite actual defining
sets. The sum norms dominate every component, including for all pairs. -/
theorem jetBounds_of_weighted_norm_bounds {n : ℕ} {α R J : ℝ}
    {z : Space n} {s : Set (Space n)} {u : Space n → ℝ}
    (hs : s ⊆ ball z R) (hf : FiniteWeightedNorms α z R u s)
    (hN : N2 α z R u s ≤ J)
    (hT : M1 z R u s + M2 z R u s + N0 α z R u s + N1 α z R u s ≤ J) :
    JetBounds α z R s u J J J := by
  have hM1 := P201.Elliptic.WeightedInterpolation.M1_nonneg hs u
  have hM2 := P201.Elliptic.WeightedInterpolation.M2_nonneg hs u
  have hN0 : 0 ≤ N0 α z R u s :=
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s u 0 hs
  have hN1 : 0 ≤ N1 α z R u s := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s
      (firstPartialWithin u s i) 1 hs
  refine ⟨?_, ?_, ?_⟩
  · intro i x hx
    exact (P201.Elliptic.WeightedInterpolation.first_weighted_le_M1 hs hf i hx).trans
      (by linarith)
  · intro i j x hx
    exact (P201.Elliptic.WeightedInterpolation.second_weighted_le_M2 hs hf i j hx).trans
      (by linarith)
  · intro i j x hx y hy
    have h := P201.Elliptic.WeightedInterpolation.weighted_pair_bound hs
      (hf.2.2.2.2.2 i j) hx hy
    have hc : weightedSeminormOn 2 α z R (secondPartialWithin u s i j) s ≤
        N2 α z R u s := by
      apply (Finset.single_le_sum (fun k _ =>
        P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s
          (secondPartialWithin u s i k) 2 hs) (Finset.mem_univ j)).trans
      exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α s
          (secondPartialWithin u s k l) 2 hs) (Finset.mem_univ i)
    exact h.trans (mul_le_mul_of_nonneg_right (hc.trans hN)
      (Real.rpow_nonneg dist_nonneg _))


/-- Uniform comparison of data under restriction and a radius at most twice
its reference scale. In particular it is uniform in an exhausting radius. -/
theorem scaledDataNorm_restrict_le_eight {n : ℕ} {α R r : ℝ}
    {u f : Space n → ℝ} {s t : Set (Space n)}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R) (hr : 0 < r)
    (hRr : R ≤ 2 * r) (ht : t ⊆ s)
    (hu : IsBoundedOn u s) (hf : IsHolderOn α f s) :
    scaledDataNorm α R u f t ≤ 8 * scaledDataNorm α r u f s := by
  have hfb : IsBoundedOn f s := by
    obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
    exact ⟨M, hM, hb⟩
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_mono hu ht
  have hF := P201.Elliptic.PoissonSchauder.supNormOn_mono hfb ht
  have hH : PoissonSchauder.holderSeminormOn α f t ≤
      PoissonSchauder.holderSeminormOn α f s :=
    P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f s)
      (fun x hx y hy => P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
        hf (ht hx) (ht hy))
  have hR2 : R ^ 2 ≤ 4 * r ^ 2 := by nlinarith [sq_nonneg R]
  have h2α : (2 : ℝ) ^ (2 + α) ≤ 8 := by
    calc
      (2 : ℝ) ^ (2 + α) ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have hRα : R ^ (2 + α) ≤ 8 * r ^ (2 + α) := by
    calc
      R ^ (2 + α) ≤ (2 * r) ^ (2 + α) :=
        Real.rpow_le_rpow hR hRr (by linarith)
      _ = 2 ^ (2 + α) * r ^ (2 + α) := Real.mul_rpow (by norm_num) hr.le
      _ ≤ 8 * r ^ (2 + α) := mul_le_mul_of_nonneg_right h2α (Real.rpow_nonneg hr.le _)
  have hUs := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u s
  have hFs := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f s
  have hHs := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f s
  calc
    _ ≤ supNormOn u s + (4 * r ^ 2) * supNormOn f s +
        (8 * r ^ (2 + α)) * PoissonSchauder.holderSeminormOn α f s := by
      unfold scaledDataNorm
      exact add_le_add (add_le_add hU
        (mul_le_mul hR2 hF (P201.Elliptic.PoissonSchauder.supNormOn_nonneg f t)
          (by positivity)))
        (mul_le_mul hRα hH
          (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f t) (by positivity))
    _ ≤ _ := by
      unfold scaledDataNorm
      nlinarith [mul_nonneg (sq_nonneg r) hFs]

/-- On an open ball the one-sided class and scaled norm agree with the
canonical ordinary multi-index class and norm. -/
theorem ordinary_ball_of_within {n : ℕ} {α r : ℝ} {z : Space n}
    {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u (ball z r)) :
    IsC2HolderOn α u (ball z r) ∧
      scaledWithinSolutionNorm α r u (ball z r) =
        scaledSolutionNorm α r u (ball z r) := by
  have hjets := P201.Elliptic.ConstantSchauder.within_jets_of_extension
    (⟨ball z r, isOpen_ball⟩ : Domain n) isOpen_ball.uniqueDiffOn
    (Subset.rfl : ball z r ⊆ ball z r) hu.1 (fun _ _ => rfl)
  have hclass : IsC2HolderOn α u (ball z r) := by
    refine ⟨hu.1, hu.2.1, ?_, ?_⟩
    · intro i
      obtain ⟨M, hM, hb⟩ := hu.2.2.1 i
      refine ⟨M, hM, ?_⟩
      intro x hx
      change ‖P201.multiPartial u {i} x‖ ≤ M
      rw [← hjets.1 i hx]
      exact hb x hx
    · intro i j
      exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hu.2.2.2 i j)
        (fun x hx => (hjets.2 i j hx).symm)
  exact ⟨hclass, (P201.Elliptic.ConstantSchauder.within_estimate_of_extension
    (⟨ball z r, isOpen_ball⟩ : Domain n) isOpen_ball.uniqueDiffOn
    (Subset.rfl : ball z r ⊆ ball z r) hu.1 hclass (fun _ _ => rfl)).2⟩

/-- Exact simplification of the inner transfer bound at outer radius `2*r`.
The coefficient is dimension dependent, and independent of `r`. -/
theorem inner_two_radius_factor {α r D J : ℝ} (hr : 0 < r) (n : ℕ) :
    D + r * ((n : ℝ) * (J * D / (2 * r - r))) +
      r ^ 2 * ((n : ℝ) ^ 2 * (J * D / (2 * r - r) ^ 2)) +
      r ^ (2 + α) * ((n : ℝ) ^ 2 * (J * D / (2 * r - r) ^ (2 + α))) =
        (1 + (n : ℝ) * J + 2 * (n : ℝ) ^ 2 * J) * D := by
  rw [show 2 * r - r = r by ring]
  have hrpow := (Real.rpow_pos_of_pos hr (2 + α)).ne'
  field_simp [hr.ne', hrpow]
  <;> ring


theorem weighted_ball_N2_estimate
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c u f : Space n → ℝ)
        (z : Space n) (R μ : ℝ), 0 < R → R ≤ 2 → 0 < μ → μ ≤ 1 / 32 →
        (∀ y ∈ ball z R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ ball z R, ∀ ξ : Space n,
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (ball z R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (ball z R)) ∧
          IsHolderOn α c (ball z R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (ball z R)) +
          (∑ i, holderNormOn α (fun y => b y i) (ball z R)) +
          holderNormOn α c (ball z R) ≤ K →
        ContDiffOn ℝ 2 u (ball z R) →
        IsBoundedOn u (ball z R) → IsHolderOn α f (ball z R) →
        FiniteWeightedNorms α z R u (ball z R) →
        (∀ y ∈ ball z R, nondivergenceOperator a b c u y = f y) →
        N2 α z R u (ball z R) ≤ (n : ℝ) ^ 2 *
          (C * principalFreezingFactor α * K * μ ^ α * N2 α z R u (ball z R) +
            C * nearFreezingFactor α K μ *
              (scaledDataNorm α R u f (ball z R) + M1 z R u (ball z R) +
                M2 z R u (ball z R) + N0 α z R u (ball z R) + N1 α z R u (ball z R)) +
            2 * M2 z R u (ball z R) / μ ^ α) := by
  obtain ⟨C, hC, hpatch⟩ := weighted_frozen_ball_patch_estimate hn α hα hα1 ell K hell hK0
  refine ⟨C, hC, ?_⟩
  intro a b c u f z R μ hR hR2 hμ hμsmall hsym hellip hcoeff hK hu hub hf hfinite heq
  have hM1 := P201.Elliptic.WeightedInterpolation.M1_nonneg (Subset.rfl : ball z R ⊆ ball z R) u
  have hM2 := P201.Elliptic.WeightedInterpolation.M2_nonneg (Subset.rfl : ball z R ⊆ ball z R) u
  have hN0 := P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α (ball z R) u 0 Subset.rfl
  change 0 ≤ N0 α z R u (ball z R) at hN0
  have hN1 : 0 ≤ N1 α z R u (ball z R) := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α (ball z R)
      (firstPartialWithin u (ball z R) i) 1 Subset.rfl
  have hN2 := P201.Elliptic.WeightedInterpolation.N2_nonneg (α := α) (Subset.rfl : ball z R ⊆ ball z R) u
  have hData := scaledDataNorm_nonneg (α := α) hR.le u f (ball z R)
  have hpF : 0 ≤ principalFreezingFactor α := by unfold principalFreezingFactor; positivity
  have hnF : 0 ≤ nearFreezingFactor α K μ := by
    unfold nearFreezingFactor
    exact add_nonneg
      (freezingRemainderFactor_pos hμ (by positivity) hK0).le
      (freezingRemainderFactor_pos (by positivity) (by positivity) hK0).le
  apply N2_le_of_near_pairs hα.le hμ (by positivity) Subset.rfl hfinite
  intro i j x hx y hy hxy hclose
  let ρ := μ * radialWeight z R x
  have hd := P201.Elliptic.WeightedInterpolation.radialWeight_pos Subset.rfl hx
  have hρ : 0 < ρ := mul_pos hμ hd
  have htx : x ∈ ball x ρ := mem_ball_self hρ
  have hty : y ∈ ball x ρ := by simpa only [mem_ball, dist_comm] using hclose
  obtain ⟨hreg, hbound⟩ := hpatch a b c u f z R μ hμ hμsmall hsym hellip hcoeff hK
    hu hub hf hfinite heq x hx
  have hjets {q : Space n} (hq : q ∈ ball x ρ) (hqs : q ∈ ball z R) (i j : Fin n) :
      secondPartialWithin u (ball x ρ) i j q = secondPartialWithin u (ball z R) i j q := by
    rw [secondPartialWithin_eq_secondPartial u (isOpen_ball.mem_nhds hq),
      secondPartialWithin_eq_secondPartial u (isOpen_ball.mem_nhds hqs)]
  exact freezing_pair_of_patch hα.le hR2 hμ (Or.inl rfl) hK0 hC.le Subset.rfl hx
    htx hty hreg (hjets htx hx) (hjets hty hy) (by simpa only [one_mul] using hbound) i j

theorem weighted_half_N2_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c u f : Space (m + 1) → ℝ)
        (R μ : ℝ), 0 < R → R ≤ 2 → 0 < μ → μ ≤ 1 / 32 →
        (∀ y ∈ halfBallWithFace m R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ halfBallWithFace m R, ∀ ξ : Space (m + 1),
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (halfBallWithFace m R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (halfBallWithFace m R)) ∧
          IsHolderOn α c (halfBallWithFace m R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (halfBallWithFace m R)) +
          (∑ i, holderNormOn α (fun y => b y i) (halfBallWithFace m R)) +
          holderNormOn α c (halfBallWithFace m R) ≤ K →
        ContDiffOn ℝ 2 u (halfBallWithFace m R) →
        (∀ y ∈ flatFace m R, u y = 0) →
        IsBoundedOn u (halfBallWithFace m R) → IsHolderOn α f (halfBallWithFace m R) →
        FiniteWeightedNorms α 0 R u (halfBallWithFace m R) →
        (∀ y ∈ halfBall m R, nondivergenceOperator a b c u y = f y) →
        N2 α 0 R u (halfBallWithFace m R) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 *
          (C * principalFreezingFactor α * K * μ ^ α * N2 α 0 R u (halfBallWithFace m R) +
            C * nearFreezingFactor α K μ *
              (scaledDataNorm α R u f (halfBallWithFace m R) + M1 0 R u (halfBallWithFace m R) +
                M2 0 R u (halfBallWithFace m R) + N0 α 0 R u (halfBallWithFace m R) + N1 α 0 R u (halfBallWithFace m R)) +
            2 * M2 0 R u (halfBallWithFace m R) / μ ^ α) := by
  obtain ⟨C, hC, hpatch⟩ := weighted_frozen_half_patch_estimate m α hα hα1 ell K hell hK0
  refine ⟨C, hC, ?_⟩
  intro a b c u f R μ hR hR2 hμ hμsmall hsym hellip hcoeff hK hu hz hub hf hfinite heq
  have hM1 : 0 ≤ M1 0 R u (halfBallWithFace m R) := P201.Elliptic.WeightedInterpolation.M1_nonneg (inter_subset_left : halfBallWithFace m R ⊆ ball 0 R) u
  have hM2 : 0 ≤ M2 0 R u (halfBallWithFace m R) := P201.Elliptic.WeightedInterpolation.M2_nonneg (inter_subset_left : halfBallWithFace m R ⊆ ball 0 R) u
  have hN0 := P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg 0 R α (halfBallWithFace m R) u 0 inter_subset_left
  change 0 ≤ N0 α 0 R u (halfBallWithFace m R) at hN0
  have hN1 : 0 ≤ N1 α 0 R u (halfBallWithFace m R) := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg 0 R α (halfBallWithFace m R)
      (firstPartialWithin u (halfBallWithFace m R) i) 1 inter_subset_left
  have hN2 : 0 ≤ N2 α 0 R u (halfBallWithFace m R) := P201.Elliptic.WeightedInterpolation.N2_nonneg (α := α) (inter_subset_left : halfBallWithFace m R ⊆ ball 0 R) u
  have hData := scaledDataNorm_nonneg (α := α) hR.le u f (halfBallWithFace m R)
  have hpF : 0 ≤ principalFreezingFactor α := by unfold principalFreezingFactor; positivity
  have hnF : 0 ≤ nearFreezingFactor α K μ := by
    unfold nearFreezingFactor
    exact add_nonneg
      (freezingRemainderFactor_pos hμ (by positivity) hK0).le
      (freezingRemainderFactor_pos (by positivity) (by positivity) hK0).le
  apply N2_le_of_near_pairs hα.le hμ (by positivity) inter_subset_left hfinite
  intro i j x hx y hy hxy hclose
  let ρ := μ * radialWeight 0 R x
  have hd := P201.Elliptic.WeightedInterpolation.radialWeight_pos inter_subset_left hx
  have hρ : 0 < ρ := mul_pos hμ hd
  have hnear := half_patch_near_pair hρ hx.2 hy.2 hclose
  have hsub := hnear.2.2.trans (weighted_half_patch_geometry hx hμ hμsmall).1
  obtain ⟨hreg, hbound⟩ := hpatch a b c u f R μ hμ hμsmall hsym hellip hcoeff hK
    hu hz hub hf hfinite heq x hx
  let β : ℝ := if 2 * ρ ≤ height x then 1 else 4
  have hβ : β = 1 ∨ β = 4 := by dsimp [β]; split_ifs <;> simp
  have hσ : P201.Elliptic.ConstantSchauder.normalizedHalfScale ρ x =
      β * μ * radialWeight 0 R x := by
    dsimp [P201.Elliptic.ConstantSchauder.normalizedHalfScale, β, ρ]
    split_ifs <;> ring
  change scaledWithinSolutionNorm α
    (P201.Elliptic.ConstantSchauder.normalizedHalfScale ρ x) u
    (P201.Elliptic.ConstantSchauder.normalizedHalfPatch ρ x) ≤ _ at hbound
  rw [hσ] at hbound
  exact freezing_pair_of_patch hα.le hR2 hμ hβ hK0 hC.le inter_subset_left hx
    hnear.1 hnear.2.1 hreg
    (normalized_half_patch_jets u hρ hsub hnear.1).2
    (normalized_half_patch_jets u hρ hsub hnear.2.1).2 hbound i j


theorem JetBounds.mono {n : ℕ} {α R A B H A' B' H' : ℝ}
    {z : Space n} {s : Set (Space n)} {u : Space n → ℝ}
    (hj : JetBounds α z R s u A B H)
    (hA : A ≤ A') (hB : B ≤ B') (hH : H ≤ H') :
    JetBounds α z R s u A' B' H' := by
  exact ⟨fun i x hx => (hj.1 i x hx).trans hA,
    fun i j x hx => (hj.2.1 i j x hx).trans hB,
    fun i j x hx y hy => (hj.2.2 i j x hx y hy).trans
      (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg dist_nonneg _))⟩


/-- Include the far-pair Hessian supremum in the lower-order factor. -/
theorem normalize_freezing_N2_bound {N D T Q d A B v : ℝ}
    (hD : 0 ≤ D) (hQT : Q ≤ T) (hd : 0 ≤ d) (hv : 0 < v)
    (hraw : N ≤ d * (A * N + B * (D + T) + 2 * Q / v)) :
    N ≤ (d * A) * N + (d * (B + 2 / v)) * (D + T) := by
  have hgap : 0 ≤ d * (2 / v) * (D + T - Q) :=
    mul_nonneg (mul_nonneg hd (by positivity)) (by linarith)
  calc
    N ≤ d * (A * N + B * (D + T) + 2 * Q / v) := hraw
    _ = (d * A) * N + (d * (B + 2 / v)) * (D + T) -
      d * (2 / v) * (D + T - Q) := by ring
    _ ≤ (d * A) * N + (d * (B + 2 / v)) * (D + T) := sub_le_self _ hgap

/-- Both coefficient-freezing absorptions on a finite-radius ball.
The resulting jet constant is fixed before the fields and radius. -/
theorem finite_ball_weighted_estimate
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ J : ℝ, 0 < J ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c u f : Space n → ℝ)
        (z : Space n) (R : ℝ), 0 < R → R ≤ 2 →
        (∀ y ∈ ball z R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ ball z R, ∀ ξ : Space n,
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (ball z R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (ball z R)) ∧
          IsHolderOn α c (ball z R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (ball z R)) +
          (∑ i, holderNormOn α (fun y => b y i) (ball z R)) +
          holderNormOn α c (ball z R) ≤ K →
        IsC2HolderUpToOn α u (ball z R) →
        IsHolderOn α f (ball z R) →
        (∀ y ∈ ball z R, nondivergenceOperator a b c u y = f y) →
        JetBounds α z R (ball z R) u
          (J * scaledDataNorm α R u f (ball z R))
          (J * scaledDataNorm α R u f (ball z R))
          (J * scaledDataNorm α R u f (ball z R)) := by
  obtain ⟨C, hC, hest⟩ := weighted_ball_N2_estimate hn α hα hα1 ell K hell hK0
  let A : ℝ := (n : ℝ) ^ 2 * C * principalFreezingFactor α
  have hA : 0 ≤ A := by
    dsimp [A, principalFreezingFactor]
    positivity
  obtain ⟨μ, hμ, hμsmall, hsmall⟩ := choose_freezing_scale hα hA hK0
  let B : ℝ := (n : ℝ) ^ 2 * (C * nearFreezingFactor α K μ + 2 / μ ^ α)
  have hnear : 0 < nearFreezingFactor α K μ := by
    unfold nearFreezingFactor
    exact add_pos
      (freezingRemainderFactor_pos hμ (by positivity) hK0)
      (freezingRemainderFactor_pos (by positivity) (by positivity) hK0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let ε : ℝ := 1 / (4 * (B + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Cε, hCε, hinterp⟩ := P201.Elliptic.WeightedInterpolation.ball_interpolation
    hn α hα hα1 ε hε
  let J : ℝ := 1 + 2 * B * (1 + Cε) + Cε
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨J, hJ, ?_⟩
  intro a b c u f z R hR hR2 hsym hellip hcoeff hK hu hf heq
  obtain ⟨hfinite, hi⟩ := hinterp z R hR u hu
  have hraw := hest a b c u f z R μ hR hR2 hμ hμsmall
    hsym hellip hcoeff hK hu.1 hu.2.1 hf hfinite heq
  have hs : ball z R ⊆ ball z R := Subset.rfl
  have hM1 := P201.Elliptic.WeightedInterpolation.M1_nonneg hs u
  have hM2 := P201.Elliptic.WeightedInterpolation.M2_nonneg hs u
  have hN0 : 0 ≤ N0 α z R u (ball z R) :=
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α (ball z R) u 0 hs
  have hN1 : 0 ≤ N1 α z R u (ball z R) := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg z R α (ball z R)
      (firstPartialWithin u (ball z R) i) 1 hs
  have hN2 := P201.Elliptic.WeightedInterpolation.N2_nonneg (α := α) hs u
  have hD := scaledDataNorm_nonneg (α := α) hR.le u f (ball z R)
  have hQ : M2 z R u (ball z R) ≤
      M1 z R u (ball z R) + M2 z R u (ball z R) +
        N0 α z R u (ball z R) + N1 α z R u (ball z R) := by linarith
  have hraw' : N2 α z R u (ball z R) ≤
      ((n : ℝ) ^ 2 * (C * principalFreezingFactor α * K * μ ^ α)) *
        N2 α z R u (ball z R) + B *
          (scaledDataNorm α R u f (ball z R) +
            (M1 z R u (ball z R) + M2 z R u (ball z R) +
              N0 α z R u (ball z R) + N1 α z R u (ball z R))) := by
    apply normalize_freezing_N2_bound hD hQ (sq_nonneg _) (Real.rpow_pos_of_pos hμ α)
    convert hraw using 1 <;> ring
  have hq : (n : ℝ) ^ 2 * (C * principalFreezingFactor α * K * μ ^ α) ≤ 1 / 4 := by
    convert hsmall using 1 <;> dsimp [A] <;> ring
  have hU : M0 u (ball z R) ≤ scaledDataNorm α R u f (ball z R) := by
    unfold M0 scaledDataNorm
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (ball z R)
    have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (ball z R)
    have hRF : 0 ≤ R ^ 2 * supNormOn f (ball z R) := by positivity
    have hRH : 0 ≤ R ^ (2 + α) * PoissonSchauder.holderSeminormOn α f (ball z R) := by positivity
    linarith
  obtain ⟨hNb, hTb⟩ := absorb_freezing_norms hN2 hD hU hB hCε.le hq hraw' hi
  exact jetBounds_of_weighted_norm_bounds hs hfinite hNb hTb

/-- Both coefficient-freezing absorptions on a finite-radius half.
The resulting jet constant is fixed before the fields and radius. -/
theorem finite_half_weighted_estimate
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell K : ℝ) (hell : 0 < ell) (hK0 : 0 ≤ K) :
    ∃ J : ℝ, 0 < J ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c u f : Space (m + 1) → ℝ)
        (R : ℝ), 0 < R → R ≤ 2 →
        (∀ y ∈ halfBallWithFace m R, ∀ i j, a y i j = a y j i) →
        (∀ y ∈ halfBallWithFace m R, ∀ ξ : Space (m + 1),
          ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a y i j * ξ i * ξ j) →
        ((∀ i j, IsHolderOn α (fun y => a y i j) (halfBallWithFace m R)) ∧
          (∀ i, IsHolderOn α (fun y => b y i) (halfBallWithFace m R)) ∧
          IsHolderOn α c (halfBallWithFace m R)) →
        (∑ i, ∑ j, holderNormOn α (fun y => a y i j) (halfBallWithFace m R)) +
          (∑ i, holderNormOn α (fun y => b y i) (halfBallWithFace m R)) +
          holderNormOn α c (halfBallWithFace m R) ≤ K →
        IsC2HolderUpToOn α u (halfBallWithFace m R) →
        (∀ y ∈ flatFace m R, u y = 0) →
        IsHolderOn α f (halfBallWithFace m R) →
        (∀ y ∈ halfBall m R, nondivergenceOperator a b c u y = f y) →
        JetBounds α 0 R (halfBallWithFace m R) u
          (J * scaledDataNorm α R u f (halfBallWithFace m R))
          (J * scaledDataNorm α R u f (halfBallWithFace m R))
          (J * scaledDataNorm α R u f (halfBallWithFace m R)) := by
  obtain ⟨C, hC, hest⟩ := weighted_half_N2_estimate m α hα hα1 ell K hell hK0
  let A : ℝ := ((m + 1 : ℕ) : ℝ) ^ 2 * C * principalFreezingFactor α
  have hA : 0 ≤ A := by
    dsimp [A, principalFreezingFactor]
    positivity
  obtain ⟨μ, hμ, hμsmall, hsmall⟩ := choose_freezing_scale hα hA hK0
  let B : ℝ := ((m + 1 : ℕ) : ℝ) ^ 2 * (C * nearFreezingFactor α K μ + 2 / μ ^ α)
  have hnear : 0 < nearFreezingFactor α K μ := by
    unfold nearFreezingFactor
    exact add_pos
      (freezingRemainderFactor_pos hμ (by positivity) hK0)
      (freezingRemainderFactor_pos (by positivity) (by positivity) hK0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let ε : ℝ := 1 / (4 * (B + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Cε, hCε, hinterp⟩ := P201.Elliptic.WeightedInterpolation.halfBall_interpolation
    m α hα hα1 ε hε
  let J : ℝ := 1 + 2 * B * (1 + Cε) + Cε
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨J, hJ, ?_⟩
  intro a b c u f R hR hR2 hsym hellip hcoeff hK hu hz hf heq
  obtain ⟨hfinite, hi⟩ := hinterp R hR u hu
  have hraw := hest a b c u f R μ hR hR2 hμ hμsmall
    hsym hellip hcoeff hK hu.1 hz hu.2.1 hf hfinite heq
  have hs : halfBallWithFace m R ⊆ ball 0 R := inter_subset_left
  have hM1 := P201.Elliptic.WeightedInterpolation.M1_nonneg hs u
  have hM2 := P201.Elliptic.WeightedInterpolation.M2_nonneg hs u
  have hN0 : 0 ≤ N0 α 0 R u (halfBallWithFace m R) :=
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg
      0 R α (halfBallWithFace m R) u 0 hs
  have hN1 : 0 ≤ N1 α 0 R u (halfBallWithFace m R) := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.WeightedInterpolation.weightedSeminormOn_nonneg 0 R α (halfBallWithFace m R)
      (firstPartialWithin u (halfBallWithFace m R) i) 1 hs
  have hN2 := P201.Elliptic.WeightedInterpolation.N2_nonneg (α := α) hs u
  have hD := scaledDataNorm_nonneg (α := α) hR.le u f (halfBallWithFace m R)
  have hQ : M2 0 R u (halfBallWithFace m R) ≤
      M1 0 R u (halfBallWithFace m R) + M2 0 R u (halfBallWithFace m R) +
        N0 α 0 R u (halfBallWithFace m R) + N1 α 0 R u (halfBallWithFace m R) := by linarith
  have hraw' : N2 α 0 R u (halfBallWithFace m R) ≤
      (((m + 1 : ℕ) : ℝ) ^ 2 * (C * principalFreezingFactor α * K * μ ^ α)) *
        N2 α 0 R u (halfBallWithFace m R) + B *
          (scaledDataNorm α R u f (halfBallWithFace m R) +
            (M1 0 R u (halfBallWithFace m R) + M2 0 R u (halfBallWithFace m R) +
              N0 α 0 R u (halfBallWithFace m R) + N1 α 0 R u (halfBallWithFace m R))) := by
    apply normalize_freezing_N2_bound hD hQ (sq_nonneg _) (Real.rpow_pos_of_pos hμ α)
    convert hraw using 1 <;> ring
  have hq : ((m + 1 : ℕ) : ℝ) ^ 2 * (C * principalFreezingFactor α * K * μ ^ α) ≤ 1 / 4 := by
    convert hsmall using 1 <;> dsimp [A] <;> ring
  have hU : M0 u (halfBallWithFace m R) ≤ scaledDataNorm α R u f (halfBallWithFace m R) := by
    unfold M0 scaledDataNorm
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (halfBallWithFace m R)
    have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (halfBallWithFace m R)
    have hRF : 0 ≤ R ^ 2 * supNormOn f (halfBallWithFace m R) := by positivity
    have hRH : 0 ≤ R ^ (2 + α) * PoissonSchauder.holderSeminormOn α f (halfBallWithFace m R) := by positivity
    linarith
  obtain ⟨hNb, hTb⟩ := absorb_freezing_norms hN2 hD hU hB hCε.le hq hraw' hi
  exact jetBounds_of_weighted_norm_bounds hs hfinite hNb hTb


theorem interior_ball_estimate :
    P201Specs.Elliptic.VariableLocal.InteriorBallEstimateStatement := by
  intro n hn α hα hα1 ell K hell hK0
  obtain ⟨J, hJ, hfinite⟩ := finite_ball_weighted_estimate hn α hα hα1 ell K hell hK0
  let J' := 8 * J
  refine ⟨1 + (n : ℝ) * J' + 2 * (n : ℝ) ^ 2 * J', by dsimp [J']; positivity, ?_⟩
  intro a b c z r hr hr1 hsym hellip ha hb hc hK u f hu hub hf heq
  let D := scaledDataNorm α r u f (ball z (2 * r))
  have hD : 0 ≤ D := scaledDataNorm_nonneg hr.le u f _
  have hJD : 0 ≤ J' * D := mul_nonneg (by dsimp [J']; positivity) hD
  have hcoeff := And.intro ha (And.intro hb hc)
  have hj : JetBounds α z (2 * r) (ball z (2 * r)) u
      (J' * D) (J' * D) (J' * D) := by
    apply P201.Elliptic.WeightedInterpolation.exhaustion.1 hα (by positivity)
    intro R hRhalf hRr
    have hR : 0 < R := by linarith
    have hR2 : R ≤ 2 := by linarith
    have hsub : ball z R ⊆ ball z (2 * r) := ball_subset_ball hRr.le
    obtain ⟨hreg, _⟩ := P201.Elliptic.WeightedInterpolation.restriction.1
      hα hα1 (by positivity : 0 < 2 * r) hu R hR hRr
    have hcoeffR := And.intro
      (fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (ha i j) hsub)
      (And.intro (fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hb i) hsub)
        (P201.Elliptic.PoissonSchauder.isHolderOn_mono hc hsub))
    have hjR := hfinite a b c u f z R hR hR2
      (fun x hx => hsym x (hsub hx)) (fun x hx => hellip x (hsub hx))
      hcoeffR (coefficient_norm_restrict hcoeff hK hsub) hreg
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono hf hsub)
      (fun x hx => heq x (hsub hx))
    have hd := scaledDataNorm_restrict_le_eight hα.le hα1.le hR.le hr hRr.le hsub hub hf
    have hbound : J * scaledDataNorm α R u f (ball z R) ≤ J' * D := by
      dsimp [J', D]
      nlinarith [mul_le_mul_of_nonneg_left hd hJ.le]
    exact JetBounds.mono hjR hbound hbound hbound
  have hU : ∀ x ∈ ball z (2 * r) ∩ (univ : Set (Space n)), ‖u x‖ ≤ D := by
    intro x hx
    have h := P201.Elliptic.PoissonSchauder.norm_le_supNormOn hub hx.1
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (ball z (2 * r))
    have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (ball z (2 * r))
    dsimp [D, scaledDataNorm]
    have hRF : 0 ≤ r ^ 2 * supNormOn f (ball z (2 * r)) := by positivity
    have hRH : 0 ≤ r ^ (2 + α) * PoissonSchauder.holderSeminormOn α f (ball z (2 * r)) := by positivity
    exact h.trans (by linarith)
  have hin := inner_estimate_of_weighted_jets hα.le hr.le (by linarith : r < 2 * r)
    hD hJD hJD hJD
    (by simpa only [inter_univ] using hu.1.mono (ball_subset_ball (by linarith : r ≤ 2 * r)))
    hU (by simpa only [inter_univ] using hj)
  simp only [inter_univ] at hin
  obtain ⟨hclass, hnormeq⟩ := ordinary_ball_of_within hin.1
  refine ⟨hclass, ?_⟩
  rw [← hnormeq]
  exact hin.2.trans_eq (inner_two_radius_factor hr n)



/-- One-sided exhaustion includes the flat face and keeps the original
within derivatives. Only the ordinary interior equation is restricted. -/
theorem half_ball_estimate :
    P201Specs.Elliptic.VariableLocal.HalfBallEstimateStatement := by
  intro m α hα hα1 ell K hell hK0
  obtain ⟨J, hJ, hfinite⟩ := finite_half_weighted_estimate m α hα hα1 ell K hell hK0
  let J' := 8 * J
  refine ⟨1 + ((m + 1 : ℕ) : ℝ) * J' + 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * J',
    by dsimp [J']; positivity, ?_⟩
  intro a b c r hr hr1 hsym hellip ha hb hc hK u f hu hloc hz hub hf heq
  let D := scaledDataNorm α r u f (halfBallWithFace m (2 * r))
  have hD : 0 ≤ D := scaledDataNorm_nonneg hr.le u f _
  have hJD : 0 ≤ J' * D := mul_nonneg (by dsimp [J']; positivity) hD
  have hcoeff := And.intro ha (And.intro hb hc)
  have hj : JetBounds α 0 (2 * r) (halfBallWithFace m (2 * r)) u
      (J' * D) (J' * D) (J' * D) := by
    apply P201.Elliptic.WeightedInterpolation.exhaustion.2 hα (by positivity)
    intro R hRhalf hRr
    have hR : 0 < R := by linarith
    have hR2 : R ≤ 2 := by linarith
    have hsub : halfBallWithFace m R ⊆ halfBallWithFace m (2 * r) :=
      inter_subset_inter_left _ (ball_subset_ball hRr.le)
    obtain ⟨hreg, _⟩ := P201.Elliptic.WeightedInterpolation.restriction.2
      hα hα1 (by positivity : 0 < 2 * r) ⟨hu, hloc⟩ R hR hRr
    have hcoeffR := And.intro
      (fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (ha i j) hsub)
      (And.intro (fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hb i) hsub)
        (P201.Elliptic.PoissonSchauder.isHolderOn_mono hc hsub))
    have hjR := hfinite a b c u f R hR hR2
      (fun x hx => hsym x (hsub hx)) (fun x hx => hellip x (hsub hx))
      hcoeffR (coefficient_norm_restrict hcoeff hK hsub) hreg
      (fun x hx => hz x ⟨ball_subset_ball hRr.le hx.1, hx.2⟩)
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono hf hsub)
      (fun x hx => heq x ⟨ball_subset_ball hRr.le hx.1, hx.2⟩)
    have hd := scaledDataNorm_restrict_le_eight hα.le hα1.le hR.le hr hRr.le hsub hub hf
    have hbound : J * scaledDataNorm α R u f (halfBallWithFace m R) ≤ J' * D := by
      dsimp [J', D]
      nlinarith [mul_le_mul_of_nonneg_left hd hJ.le]
    exact JetBounds.mono hjR hbound hbound hbound
  have hU : ∀ x ∈ halfBallWithFace m (2 * r), ‖u x‖ ≤ D := by
    intro x hx
    have h := P201.Elliptic.PoissonSchauder.norm_le_supNormOn hub hx
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (halfBallWithFace m (2 * r))
    have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (halfBallWithFace m (2 * r))
    dsimp [D, scaledDataNorm]
    exact h.trans (by
      have hF' := mul_nonneg (sq_nonneg r) hF
      have hH' := mul_nonneg (Real.rpow_nonneg hr.le (2 + α)) hH
      linarith)
  have hin := inner_estimate_of_weighted_jets hα.le hr.le (by linarith : r < 2 * r)
    hD hJD hJD hJD
    (hu.mono (inter_subset_inter_left _ (ball_subset_ball (by linarith : r ≤ 2 * r))))
    hU hj
  exact ⟨hin.1, hin.2.trans_eq (inner_two_radius_factor hr (m + 1))⟩


end P201.Elliptic.VariableLocal
