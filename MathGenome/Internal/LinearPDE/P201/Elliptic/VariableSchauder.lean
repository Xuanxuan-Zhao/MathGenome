import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.VariableSchauder
import MathGenome.Internal.LinearPDE.P201.Elliptic.ConstantSchauder
import MathGenome.Internal.LinearPDE.P201.Elliptic.ChartSchauder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
Variable-coefficient a priori Schauder estimates. The local ball and genuine
curved-boundary estimates are imported from their proved upstream modules.
Compact finite-cover patching gives the nested interior estimate, the local
boundary-portion estimate, and the estimate on a bounded regular closure.
The one-sided derivatives remain those of the actual observation sets.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201.Elliptic.VariableSchauder
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.VariableSchauder

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
    (hcoeff : CoefficientsHolderOn α a b c s) (hf : IsHolderOn α f s)
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

/-- The analogous direct use of the proved half-ball estimate. The source at the
flat plane is unrestricted. Proving and absorbing its quantitative Hölder
bound is a separate, unfinished step. -/
theorem frozen_half_ball_estimate
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
          IsHolderOn α (frozenSource a b c u f z) (halfBallWithFace m (2 * r)) →
          (∀ x ∈ halfBall m (2 * r), nondivergenceOperator a b c u x = f x) →
          IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
          scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
            C * scaledDataNorm α r u (frozenSource a b c u f z)
              (halfBallWithFace m (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.ConstantSchauder.half_ball_estimate
    m α hα hα1 ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro a b c z r hA hr u f hu huc huz hub hF heq
  exact hest (a z) hA r hr u (frozenSource a b c u f z) hu huc huz hub hF
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
        coefficientNormOn α a b c s ∧
    (∀ i j, holderNormOn α (fun x => a x i j) s ≤ coefficientNormOn α a b c s) ∧
    (∀ i, holderNormOn α (fun x => b x i) s ≤ coefficientNormOn α a b c s) ∧
    holderNormOn α c s ≤ coefficientNormOn α a b c s := by
  have hN (v : Space n → ℝ) : 0 ≤ holderNormOn α v s :=
    add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hA : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hN _
  have hB : 0 ≤ ∑ i : Fin n, holderNormOn α (fun x => b x i) s :=
    Finset.sum_nonneg fun i _ => hN _
  have hAsum : (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (fun x => a x i j) s) ≤
      coefficientNormOn α a b c s := by
    unfold coefficientNormOn
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
    unfold coefficientNormOn
    linarith [hN c]
  · unfold coefficientNormOn
    linarith

/-- Every actual coefficient and its Hölder differences are bounded by K. -/
theorem coefficient_holder_bounds {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hc : CoefficientsHolderOn α a b c s) (hK : coefficientNormOn α a b c s ≤ K) :
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
    (he : UniformlyEllipticOn ell a s) (hc : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K) {z : Space n} (hz : z ∈ s) :
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
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
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
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
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

/-- The first-order multi-index derivative is the shared coordinate derivative
by definition, without any smoothness assumption. -/
theorem multiPartial_singleton_eq_firstPartial {n : ℕ} (u : Space n → ℝ) (i : Fin n) :
    multiPartial u {i} = firstPartial u i := by
  ext x
  simp only [P102.U4.multiPartial, Multiset.sort_singleton, P102.U4.partialWord]
  rfl

/-- Equality of the two classical mixed derivatives only needs C² at the
point. Global smoothness of the ambient representative is not required. -/
theorem secondPartial_comm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    secondPartial u i j x = secondPartial u j i x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change fderiv ℝ (fun y => fderiv ℝ u y (coordinate n j)) x (coordinate n i) =
    fderiv ℝ (fun y => fderiv ℝ u y (coordinate n i)) x (coordinate n j)
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinate n j)),
    fderiv_clm_apply hd (differentiableAt_const (coordinate n i))]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    hu.isSymmSndFDerivAt (by norm_num) (coordinate n i) (coordinate n j)

/-- The Hessian in the equation and the sorted multi-index Hessian in the
interior norm agree at every C² point, including repeated indices. -/
theorem secondPartial_eq_multiPartial {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    secondPartial u i j x = multiPartial u {i, j} x := by
  have ordered (i j : Fin n) (hij : i ≤ j) :
      multiPartial u {i, j} = secondPartial u i j := by
    have hs : ({i, j} : MultiIndex n).sort (· ≤ ·) = [i, j] := by
      rw [Multiset.insert_eq_cons, Multiset.sort_cons i {j} (· ≤ ·) (by simpa using hij),
        Multiset.sort_singleton]
    change P102.U4.partialWord u (({i, j} : MultiIndex n).sort (· ≤ ·)) = _
    rw [hs]
    rfl
  rcases le_total i j with hij | hji
  · exact congrFun (ordered i j hij).symm x
  · calc
      secondPartial u i j x = secondPartial u j i x := secondPartial_comm hu i j
      _ = multiPartial u {j, i} x := congrFun (ordered j i hji).symm x
      _ = multiPartial u {i, j} x := by rw [Multiset.pair_comm]

/-- Transfer the actual C²,α hypothesis to the Hessian used in freezing on an
open set. The openness supplies C² at the point; it is essential to this
ordinary-derivative representation. -/
theorem isHolderOn_secondPartial {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : IsOpen s) (hu : IsC2HolderOn α u s) (i j : Fin n) :
    IsHolderOn α (secondPartial u i j) s := by
  apply P201.Elliptic.PoissonSchauder.isHolderOn_congr (hu.2.2.2 i j)
  intro x hx
  exact secondPartial_eq_multiPartial (hu.1.contDiffAt (hs.mem_nhds hx)) i j

/-- Uniform patchwise Hölder bounds on a compact set control every pair.
The geometric constant is chosen before the function and its bounds. For
far pairs only the supremum bound is used; no connectedness is needed. -/
theorem compact_holder_patching {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {s : Set (Space n)} (hcompact : IsCompact s) {ι : Type*}
    (U : ι → Set (Space n)) (hopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Space n → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H →
      (∀ x ∈ s, ‖g x‖ ≤ M) →
      (∀ i, ∀ x ∈ s ∩ U i, ∀ y ∈ s ∩ U i,
        ‖g x - g y‖ ≤ H * dist x y ^ α) →
      HolderBoundsOn α g s M (H + C * M) := by
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric hcompact hopen hcover
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  refine ⟨2 / δ ^ α, div_pos (by norm_num) hδα, ?_⟩
  intro g M H hM hH hg hlocal
  have hCM : 0 ≤ 2 / δ ^ α * M := mul_nonneg (div_nonneg (by norm_num) hδα.le) hM
  refine ⟨hM, add_nonneg hH hCM, hg, ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hLeb x hx
    have hxU : x ∈ U i := hi (by simpa using hδ)
    have hyU : y ∈ U i := hi (by simpa only [mem_ball, dist_comm] using hxy)
    exact (hlocal i x ⟨hx, hxU⟩ y ⟨hy, hyU⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCM)
        (Real.rpow_nonneg dist_nonneg _))
  · calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hg x hx, hg y hy]
      _ = (2 / δ ^ α * M) * δ ^ α := by field_simp
      _ ≤ (2 / δ ^ α * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hδ.le (le_of_not_gt hxy) hα) hCM
      _ ≤ (H + 2 / δ ^ α * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hH)
          (Real.rpow_nonneg dist_nonneg _)

/-- A finite patch cover turns local bounds proportional to the data size
into a global canonical Hölder norm bound, with its constant fixed first.
This supplies the scalar all-pairs portion of the patching argument. -/
theorem finite_cover_holder_estimate {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {s : Set (Space n)} (hcompact : IsCompact s) {ι : Type*} [Fintype ι]
    (U : ι → Set (Space n)) (hopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Space n → ℝ) (D : ℝ), 0 ≤ D →
      (∀ i, HolderBoundsOn α g (s ∩ U i) (A i * D) (A i * D)) →
      IsHolderOn α g s ∧ holderNormOn α g s ≤ C * D := by
  classical
  obtain ⟨B, hB, hpatch⟩ := compact_holder_patching hα hcompact U hopen hcover
  let T := ∑ i, A i
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => hA i
  have hiT (i : ι) : A i ≤ T := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  refine ⟨(2 + B) * (T + 1), mul_pos (by linarith) (by linarith), ?_⟩
  intro g D hD hg
  have hpoint : ∀ x ∈ s, ‖g x‖ ≤ T * D := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact ((hg i).norm_le x ⟨hx, hi⟩).trans (mul_le_mul_of_nonneg_right (hiT i) hD)
  have hlocal : ∀ i, ∀ x ∈ s ∩ U i, ∀ y ∈ s ∩ U i,
      ‖g x - g y‖ ≤ (T * D) * dist x y ^ α := by
    intro i x hx y hy
    exact ((hg i).diff_le x hx y hy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hiT i) hD)
        (Real.rpow_nonneg dist_nonneg _))
  have hb := hpatch g (T * D) (T * D) (mul_nonneg hT hD) (mul_nonneg hT hD) hpoint hlocal
  refine ⟨hb.isHolderOn, ?_⟩
  have hnorm : holderNormOn α g s ≤ T * D + (T * D + B * (T * D)) :=
    add_le_add hb.norm_bounds.1 hb.norm_bounds.2
  calc
    holderNormOn α g s ≤ T * D + (T * D + B * (T * D)) := hnorm
    _ = ((2 + B) * T) * D := by ring
    _ ≤ ((2 + B) * (T + 1)) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hD

/-- A locally bounded all-pairs Hölder function is globally Hölder on a
compact observation set. The proof explicitly selects a finite subcover. -/
theorem isHolderOn_of_local_on_compact {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {g : Space n → ℝ} {s : Set (Space n)} (hcompact : IsCompact s)
    (hlocal : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ IsHolderOn α g (s ∩ ball x r)) :
    IsHolderOn α g s := by
  classical
  choose r hr hg using fun x : s => hlocal x x.property
  have hcover : s ⊆ ⋃ x : s, ball (x : Space n) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover _ (fun x => isOpen_ball) hcover
  let U : t → Set (Space n) := fun i => ball (i.val : Space n) (r i.val)
  have hcover' : s ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  let A : t → ℝ := fun i => holderNormOn α g (s ∩ U i)
  have hbounds (i : t) : HolderBoundsOn α g (s ∩ U i) (A i) (A i) :=
    HolderBoundsOn.of_norm (hg i.val)
  obtain ⟨C, hC, hest⟩ := finite_cover_holder_estimate hα hcompact U
    (fun i => isOpen_ball) hcover' A (fun i => (hbounds i).sup_nonneg)
  exact (hest g 1 zero_le_one (fun i => by simpa only [mul_one] using hbounds i)).1

/-- The qualitative interior conclusion is already forced by local C²,α
regularity and compact containment. This lemma supplies no quantitative
uniform bound and uses no conditional constant-coefficient premise. -/
theorem c2HolderOn_of_local_on_compact {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (Ω : Domain n) {s : Set (Space n)} (hcompact : IsCompact s) (hs : s ⊆ Ω)
    {u : Space n → ℝ} (hu : IsC2HolderLocOn α u Ω) : IsC2HolderOn α u s := by
  refine ⟨hu.1.mono hs,
    P201.Elliptic.PoissonSchauder.boundedOn_of_continuousOn_compact hcompact
      (hu.1.continuousOn.mono hs), ?_, ?_⟩
  · intro i
    have hd : ContinuousOn (multiPartial u {i}) Ω :=
      (P102.U4.partialWord_contDiffOn Ω hu.1 (({i} : MultiIndex n).sort (· ≤ ·)) 0
        (by simp)).continuousOn
    exact P201.Elliptic.PoissonSchauder.boundedOn_of_continuousOn_compact hcompact (hd.mono hs)
  · intro i j
    apply isHolderOn_of_local_on_compact hα hcompact
    intro x hx
    obtain ⟨r, hr, hrΩ, hholder⟩ := hu.2 x (hs hx)
    exact ⟨r, hr, P201.Elliptic.PoissonSchauder.isHolderOn_mono (hholder i j)
      inter_subset_right⟩

/-- In particular the bounded smaller open set in the original interior
statement has the required (finite) C²,α class. Its quantitative estimate is
the separate unresolved a priori assertion. -/
theorem interior_regularity {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (Ω Ω' Ω'' : Domain n) (hbounded : Bornology.IsBounded (Ω' : Set (Space n)))
    (hcontained : closure (Ω' : Set (Space n)) ⊆ (Ω'' : Set (Space n)))
    (hΩ : Ω'' ≤ Ω) {u : Space n → ℝ} (hu : IsC2HolderLocOn α u Ω) :
    IsC2HolderOn α u Ω' := by
  have hc : IsCompact (closure (Ω' : Set (Space n))) :=
    isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  exact P201.Elliptic.PoissonSchauder.c2HolderOn_mono
    (c2HolderOn_of_local_on_compact hα Ω hc (fun x hx => hΩ (hcontained hx)) hu) subset_closure

/-- Within jets depend only on the local set germ, even at a boundary point.
This is stronger than merely agreeing at interior points and justifies
restricting curved-boundary observation sets to relatively open patches. -/
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


/-- Locally finite scalar bounds on a compact set give a finite global bound.
This lemma does not require continuity, connectedness, or a nonempty set. -/
theorem boundedOn_of_local_on_compact {n : ℕ} {g : Space n → ℝ}
    {s : Set (Space n)} (hcompact : IsCompact s)
    (hlocal : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ IsBoundedOn g (s ∩ ball x r)) :
    IsBoundedOn g s := by
  classical
  choose r hr hg using fun x : s => hlocal x x.property
  choose M hM hb using hg
  have hcover : s ⊆ ⋃ x : s, ball (x : Space n) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover _ (fun x => isOpen_ball) hcover
  refine ⟨∑ x ∈ t, M x, Finset.sum_nonneg (fun x _ => hM x), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact (hb y x ⟨hx, hxy⟩).trans
    (Finset.single_le_sum (fun z _ => hM z) hy)

/-- Restricting a one-sided C²,α function to a relatively open patch
preserves its class because both coordinate jets depend only on set germs. -/
theorem c2HolderUpToOn_inter_open {n : ℕ} {α : ℝ}
    {u : Space n → ℝ} {s U : Set (Space n)} (hU : IsOpen U)
    (hu : IsC2HolderUpToOn α u s) : IsC2HolderUpToOn α u (s ∩ U) := by
  refine ⟨hu.1.mono inter_subset_left,
    P201.Elliptic.PoissonSchauder.boundedOn_mono hu.2.1 inter_subset_left, ?_, ?_⟩
  · intro i
    obtain ⟨M, hM, hb⟩ := hu.2.2.1 i
    refine ⟨M, hM, ?_⟩
    intro x hx
    rw [(within_jets_restrict_open u s hU hx.2).1 i]
    exact hb x hx.1
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hu.2.2.2 i j) inter_subset_left)
    intro x hx
    exact (within_jets_restrict_open u s hU hx.2).2 i j

/-- Qualitative one-sided regularity on an inner boundary portion follows
from local regularity and compact containment alone. Its derivative bounds
are finite but do not give the uniform quantitative Schauder estimate. -/
theorem local_boundary_regularity {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (Ω U V : Domain n) (hbounded : Bornology.IsBounded (V : Set (Space n)))
    (hcontained : closure (V : Set (Space n)) ⊆ (U : Set (Space n)))
    {u : Space n → ℝ} (hu : IsC2HolderLocUpToOn α u Ω U) :
    IsC2HolderUpToOn α u (closure (Ω : Set (Space n)) ∩ (V : Set (Space n))) := by
  let s : Set (Space n) := closure (Ω : Set (Space n)) ∩ (U : Set (Space n))
  let k : Set (Space n) := closure (Ω : Set (Space n)) ∩ closure (V : Set (Space n))
  let t : Set (Space n) := closure (Ω : Set (Space n)) ∩ (V : Set (Space n))
  have hV : (V : Set (Space n)) ⊆ (U : Set (Space n)) :=
    subset_closure.trans hcontained
  have hks : k ⊆ s := fun x hx => ⟨hx.1, hcontained hx.2⟩
  have htk : t ⊆ k := fun x hx => ⟨hx.1, subset_closure hx.2⟩
  have hc : IsCompact k :=
    (isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure).inter_left isClosed_closure
  have hpatch : ∀ x ∈ k, ∃ r : ℝ, 0 < r ∧
      IsBoundedOn u (k ∩ ball x r) ∧
      (∀ i, IsBoundedOn (firstPartialWithin u s i) (k ∩ ball x r)) ∧
      ∀ i j, IsHolderOn α (secondPartialWithin u s i j) (k ∩ ball x r) := by
    intro x hx
    obtain ⟨r, hr, hrU, hp⟩ := hu.2 x (hks hx)
    have hset : s ∩ ball x r = closure (Ω : Set (Space n)) ∩ ball x r := by
      ext y
      simp only [s, mem_inter_iff]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hrU h.2⟩, h.2⟩⟩
    have hsub : k ∩ ball x r ⊆ closure (Ω : Set (Space n)) ∩ ball x r :=
      fun y hy => ⟨hy.1.1, hy.2⟩
    have heq (y : Space n) (hy : y ∈ ball x r) :=
      within_jets_restrict_open u s isOpen_ball hy
    refine ⟨r, hr, P201.Elliptic.PoissonSchauder.boundedOn_mono hp.2.1 hsub, ?_, ?_⟩
    · intro i
      obtain ⟨M, hM, hb⟩ := hp.2.2.1 i
      refine ⟨M, hM, ?_⟩
      intro y hy
      have hjet := (heq y hy.2).1 i
      rw [hset] at hjet
      rw [← hjet]
      exact hb y (hsub hy)
    · intro i j
      apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
        (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hp.2.2.2 i j) hsub)
      intro y hy
      have hjet := (heq y hy.2).2 i j
      rw [hset] at hjet
      exact hjet.symm
  have hub : IsBoundedOn u k := boundedOn_of_local_on_compact hc (fun x hx => by
    obtain ⟨r, hr, hb, _⟩ := hpatch x hx
    exact ⟨r, hr, hb⟩)
  have hfirst (i : Fin n) : IsBoundedOn (firstPartialWithin u s i) k :=
    boundedOn_of_local_on_compact hc (fun x hx => by
      obtain ⟨r, hr, _, hb, _⟩ := hpatch x hx
      exact ⟨r, hr, hb i⟩)
  have hsecond (i j : Fin n) : IsHolderOn α (secondPartialWithin u s i j) k :=
    isHolderOn_of_local_on_compact hα hc (fun x hx => by
      obtain ⟨r, hr, _, _, hb⟩ := hpatch x hx
      exact ⟨r, hr, hb i j⟩)
  have hset : s ∩ (V : Set (Space n)) = t := by
    ext x
    simp only [s, t, mem_inter_iff]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hV h.2⟩, h.2⟩⟩
  have hjet (x : Space n) (hx : x ∈ t) :=
    within_jets_restrict_open u s V.isOpen hx.2
  refine ⟨hu.1.mono (fun x hx => ⟨hx.1, hV hx.2⟩),
    P201.Elliptic.PoissonSchauder.boundedOn_mono hub htk, ?_, ?_⟩
  · intro i
    obtain ⟨M, hM, hb⟩ := hfirst i
    refine ⟨M, hM, ?_⟩
    intro x hx
    have he := (hjet x hx).1 i
    rw [hset] at he
    rw [he]
    exact hb x (htk hx)
  · intro i j
    apply P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono (hsecond i j) htk)
    intro x hx
    have he := (hjet x hx).2 i j
    rw [hset] at he
    exact he


/-- The boundary freezing source uses the actual derivatives within its
observation set. Values of an ambient representative outside this set do not
enter the formula. -/
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
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
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
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
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
    (hcoeff : CoefficientsHolderOn α a b c s) (hf : IsHolderOn α f s)
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

/-- The actual first within jet depends only on values on the observation
set, without any regularity condition on the ambient representatives. -/
theorem firstPartialWithin_congr {n : ℕ} {u v : Space n → ℝ}
    {s : Set (Space n)} (huv : EqOn u v s) {x : Space n} (hx : x ∈ s)
    (i : Fin n) : firstPartialWithin u s i x = firstPartialWithin v s i x := by
  unfold firstPartialWithin
  rw [fderivWithin_congr' huv hx]

/-- The iterated within jet is equally independent of ambient representatives.
Both levels of congruence use the same observation set. -/
theorem secondPartialWithin_congr {n : ℕ} {u v : Space n → ℝ}
    {s : Set (Space n)} (huv : EqOn u v s) {x : Space n} (hx : x ∈ s)
    (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartialWithin v s i j x := by
  unfold secondPartialWithin
  rw [fderivWithin_congr' (fun y hy => firstPartialWithin_congr huv hy j) hx]

/-- The full within freezing source is independent of the solution's ambient
representative off the observation set, including at flat boundary points. -/
theorem frozenWithinSource_congr {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c f : Space n → ℝ)
    {u v : Space n → ℝ} {s : Set (Space n)} (huv : EqOn u v s)
    (z : Space n) :
    EqOn (frozenWithinSource a b c u f s z) (frozenWithinSource a b c v f s z) s := by
  intro x hx
  simp only [frozenWithinSource, firstPartialWithin_congr huv hx,
    secondPartialWithin_congr huv hx, huv hx]

/-- Restricting the observation set to an open patch preserves the boundary
source at every point of that patch. This uses actual within jets at each
level, so no extension across the boundary is needed. -/
theorem frozenWithinSource_restrict_open {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u f : Space n → ℝ)
    (s : Set (Space n)) {U : Set (Space n)} (hU : IsOpen U)
    (z : Space n) :
    EqOn (frozenWithinSource a b c u f (s ∩ U) z)
      (frozenWithinSource a b c u f s z) U := by
  intro x hx
  obtain ⟨hfirst, hsecond⟩ := within_jets_restrict_open u s hU hx
  simp only [frozenWithinSource, hfirst, hsecond]


/-- The variable nondivergence operator in actual derivatives within an
observation set. The equation is still imposed only at interior points. -/
def nondivergenceWithinOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ)
    (s : Set (Space n)) (x : Space n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, a x i j * secondPartialWithin u s i j x) +
    (∑ i : Fin n, b x i * firstPartialWithin u s i x) + c x * u x

/-- Subtracting the boundary lift changes the source by its actual one-sided
operator. Values of the lift outside the observation set are irrelevant. -/
def liftedWithinSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c G f : Space n → ℝ)
    (s : Set (Space n)) (x : Space n) : ℝ :=
  f x - nondivergenceWithinOperator a b c G s x

/-- At interior points the within operator agrees with the shared classical
operator. No differentiability outside the observation set is required. -/
theorem nondivergenceWithinOperator_eq_nondivergenceOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) :
    nondivergenceWithinOperator a b c u s x = nondivergenceOperator a b c u x := by
  simp only [nondivergenceWithinOperator, nondivergenceOperator,
    firstPartialWithin_eq_firstPartial u hs,
    secondPartialWithin_eq_secondPartial u hs]

/-- The exact lifted equation holds in an open solution region contained in
the observation set. This invokes proved classical derivative linearity;
it assumes neither an equation nor ambient regularity on the boundary. -/
theorem nondivergenceOperator_sub_eq_liftedWithinSource {n : ℕ}
    {Ω : Domain n} (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    {u G f : Space n → ℝ} {s : Set (Space n)}
    (hu : ContDiffOn ℝ 2 u (Ω : Set (Space n)))
    (hG : ContDiffOn ℝ 2 G (Ω : Set (Space n)))
    (hΩs : (Ω : Set (Space n)) ⊆ s) {x : Space n} (hx : x ∈ Ω)
    (heq : nondivergenceOperator a b c u x = f x) :
    nondivergenceOperator a b c (fun y => u y - G y) x =
      liftedWithinSource a b c G f s x := by
  have hs : s ∈ nhds x := Filter.mem_of_superset (Ω.isOpen.mem_nhds hx) hΩs
  have hlin : nondivergenceOperator a b c (fun y => u y - G y) x =
      nondivergenceOperator a b c u x - nondivergenceOperator a b c G x := by
    simpa only [one_mul] using
      P201.Elliptic.nondivergenceOperator_mul_sub a b c hu hG 1 hx
  rw [hlin, heq, liftedWithinSource,
    nondivergenceWithinOperator_eq_nondivergenceOperator a b c G hs]

/-- Separate supremum and seminorm estimates for the actual within operator.
The lower jets are explicit inputs and are not inferred on arbitrary sets. -/
theorem nondivergenceWithinOperator_bounds {n : ℕ} {α K M0 H0 : ℝ}
    {M1 H1 : Fin n → ℝ} {M2 H2 : Fin n → Fin n → ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c G : Space n → ℝ} {s : Set (Space n)}
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
    (hG : HolderBoundsOn α G s M0 H0)
    (hdG : ∀ i, HolderBoundsOn α (firstPartialWithin G s i) s (M1 i) (H1 i))
    (hddG : ∀ i j, HolderBoundsOn α (secondPartialWithin G s i j) s (M2 i j) (H2 i j)) :
    HolderBoundsOn α (nondivergenceWithinOperator a b c G s) s
      (K * ((∑ i, ∑ j, M2 i j) + (∑ i, M1 i) + M0))
      (K * ((∑ i, ∑ j, H2 i j) + (∑ i, ∑ j, M2 i j) +
        (∑ i, H1 i) + (∑ i, M1 i) + H0 + M0)) := by
  obtain ⟨ha, hb, hc⟩ := coefficient_holder_bounds hcoeff hK
  have hP : HolderBoundsOn α
      (fun x => ∑ i : Fin n, ∑ j : Fin n,
        a x i j * secondPartialWithin G s i j x) s
      (K * (∑ i, ∑ j, M2 i j))
      (K * (∑ i, ∑ j, H2 i j) + K * (∑ i, ∑ j, M2 i j)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ =>
      HolderBoundsOn.sum Finset.univ _ _ _ (fun j _ => (ha i j).mul (hddG i j)))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  have hB : HolderBoundsOn α
      (fun x => ∑ i : Fin n, b x i * firstPartialWithin G s i x) s
      (K * ∑ i, M1 i) (K * (∑ i, H1 i) + K * (∑ i, M1 i)) := by
    have h := HolderBoundsOn.sum Finset.univ _ _ _ (fun i _ => (hb i).mul (hdG i))
    convert h using 1 <;>
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring
  convert (hP.add hB).add (hc.mul hG) using 1 <;> first | rfl | ring

/-- Canonical Hölder bounds for the within operator. The displayed sum also
contains the lower-jet seminorms; their interpolation is a separate step. -/
theorem nondivergenceWithinOperator_holder_bounds {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c G : Space n → ℝ} {s : Set (Space n)}
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
    (hG : IsHolderOn α G s)
    (hdG : ∀ i, IsHolderOn α (firstPartialWithin G s i) s)
    (hddG : ∀ i j, IsHolderOn α (secondPartialWithin G s i j) s) :
    let N := (∑ i : Fin n, ∑ j : Fin n,
        holderNormOn α (secondPartialWithin G s i j) s) +
      (∑ i : Fin n, holderNormOn α (firstPartialWithin G s i) s) + holderNormOn α G s
    HolderBoundsOn α (nondivergenceWithinOperator a b c G s) s (K * N) (2 * K * N) := by
  dsimp only
  have h := nondivergenceWithinOperator_bounds hcoeff hK
    (HolderBoundsOn.of_norm hG)
    (fun i => HolderBoundsOn.of_norm (hdG i))
    (fun i j => HolderBoundsOn.of_norm (hddG i j))
  convert h using 1 <;> first | rfl | ring

/-- The boundary-lift source is Hölder with an explicit norm bound in terms
of the coefficients and all actual within jets of the lift. This does not
silently infer lower-jet Hölder bounds from mere boundedness. -/
theorem liftedWithinSource_holder_bound {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c G f : Space n → ℝ} {s : Set (Space n)}
    (hcoeff : CoefficientsHolderOn α a b c s)
    (hK : coefficientNormOn α a b c s ≤ K)
    (hf : IsHolderOn α f s) (hG : IsHolderOn α G s)
    (hdG : ∀ i, IsHolderOn α (firstPartialWithin G s i) s)
    (hddG : ∀ i j, IsHolderOn α (secondPartialWithin G s i j) s) :
    let N := (∑ i : Fin n, ∑ j : Fin n,
        holderNormOn α (secondPartialWithin G s i j) s) +
      (∑ i : Fin n, holderNormOn α (firstPartialWithin G s i) s) + holderNormOn α G s
    IsHolderOn α (liftedWithinSource a b c G f s) s ∧
      holderNormOn α (liftedWithinSource a b c G f s) s ≤
        holderNormOn α f s + 3 * K * N := by
  dsimp only
  have hb := (HolderBoundsOn.canonical hf).sub
    (nondivergenceWithinOperator_holder_bounds hcoeff hK hG hdG hddG)
  refine ⟨hb.isHolderOn, ?_⟩
  have hsum := add_le_add hb.norm_bounds.1 hb.norm_bounds.2
  change supNormOn _ _ + holderSeminormOn _ _ _ ≤ _
  rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq α f s]
  convert hsum using 1 <;> first | rfl | ring

/-- The lifted equation can also be stated entirely in actual within jets
at every point of the open solution region. -/
theorem nondivergenceWithinOperator_sub_eq_liftedWithinSource {n : ℕ}
    {Ω : Domain n} (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    {u G f : Space n → ℝ} {s : Set (Space n)}
    (hu : ContDiffOn ℝ 2 u (Ω : Set (Space n)))
    (hG : ContDiffOn ℝ 2 G (Ω : Set (Space n)))
    (hΩs : (Ω : Set (Space n)) ⊆ s) {x : Space n} (hx : x ∈ Ω)
    (heq : nondivergenceOperator a b c u x = f x) :
    nondivergenceWithinOperator a b c (fun y => u y - G y) s x =
      liftedWithinSource a b c G f s x := by
  rw [nondivergenceWithinOperator_eq_nondivergenceOperator a b c _
    (Filter.mem_of_superset (Ω.isOpen.mem_nhds hx) hΩs)]
  exact nondivergenceOperator_sub_eq_liftedWithinSource a b c hu hG hΩs hx heq


/-- Quantitative all-pairs patching for the full genuine within C²,α norm.
The geometric constant is chosen before the function and data size. Local
inequalities here are scalar norm hypotheses, independent of any PDE. -/
theorem finite_cover_c2HolderUpTo_estimate {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {s : Set (Space n)} (hcompact : IsCompact s) {ι : Type*} [Fintype ι]
    (U : ι → Set (Space n)) (hopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space n → ℝ) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ 2 u s →
      (∀ i, IsC2HolderUpToOn α u (s ∩ U i) ∧
        c2HolderUpToNormOn α u (s ∩ U i) ≤ A i * D) →
      IsC2HolderUpToOn α u s ∧ c2HolderUpToNormOn α u s ≤ C * D := by
  classical
  obtain ⟨B, hB, hpatch⟩ := compact_holder_patching hα hcompact U hopen hcover
  let T := ∑ i, A i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => hA i)
  have hiT (i : ι) : A i ≤ T := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  let F : ℝ := 1 + n + (n : ℝ)^2 + (n : ℝ)^2 * (1 + B)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F * (T + 1), mul_pos hF (by linarith), ?_⟩
  intro u D hD hu hlocal
  let M := T * D
  have hM : 0 ≤ M := mul_nonneg hT hD
  have hHM : 0 ≤ M + B * M := add_nonneg hM (mul_nonneg hB.le hM)
  have hlocalbounds (i : ι) :=
    P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_bounds
      (r := 1) zero_le_one (hlocal i).1
  have hlocalnorm (i : ι) : scaledWithinSolutionNorm α 1 u (s ∩ U i) ≤ M :=
    (hlocal i).2.trans (mul_le_mul_of_nonneg_right (hiT i) hD)
  have h0 : ∀ x ∈ s, ‖u x‖ ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact ((hlocalbounds i).1 x ⟨hx, hi⟩).trans (hlocalnorm i)
  have h1 : ∀ k : Fin n, ∀ x ∈ s, ‖firstPartialWithin u s k x‖ ≤ M := by
    intro k x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    have he := (within_jets_restrict_open u s (hopen i) hi).1 k
    rw [← he]
    have hb : ‖firstPartialWithin u (s ∩ U i) k x‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) := by
      simpa only [one_mul] using (hlocalbounds i).2.1 k x ⟨hx, hi⟩
    exact hb.trans (hlocalnorm i)
  have h2 : ∀ k l : Fin n, ∀ x ∈ s, ‖secondPartialWithin u s k l x‖ ≤ M := by
    intro k l x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    have he := (within_jets_restrict_open u s (hopen i) hi).2 k l
    rw [← he]
    have hb : ‖secondPartialWithin u (s ∩ U i) k l x‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) := by
      simpa only [one_pow, one_mul] using (hlocalbounds i).2.2.1 k l x ⟨hx, hi⟩
    exact hb.trans (hlocalnorm i)
  have hH : ∀ k l : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖secondPartialWithin u s k l x - secondPartialWithin u s k l y‖ ≤
        (M + B * M) * dist x y ^ α := by
    intro k l
    apply (hpatch (secondPartialWithin u s k l) M M hM hM (h2 k l) ?_).diff_le
    intro i x hx y hy
    have hex := (within_jets_restrict_open u s (hopen i) hx.2).2 k l
    have hey := (within_jets_restrict_open u s (hopen i) hy.2).2 k l
    rw [← hex, ← hey]
    have hb : ‖secondPartialWithin u (s ∩ U i) k l x -
        secondPartialWithin u (s ∩ U i) k l y‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) * dist x y ^ α := by
      simpa only [Real.one_rpow, one_mul] using (hlocalbounds i).2.2.2 k l x hx y hy
    exact hb.trans
      (mul_le_mul_of_nonneg_right (hlocalnorm i) (Real.rpow_nonneg dist_nonneg _))
  obtain ⟨hclass, hnorm⟩ :=
    P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_le_of_bounds
      (r := 1) zero_le_one hM hM hM hHM hu h0 h1 h2 hH
  refine ⟨hclass, hnorm.trans ?_⟩
  simp only [one_pow, Real.one_rpow, one_mul]
  calc
    M + (n : ℝ) * M + (n : ℝ)^2 * M + (n : ℝ)^2 * (M + B * M) = F * T * D := by
      dsimp [F, M]; ring
    _ ≤ (F * (T + 1)) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hF.le) hD


open P201.Elliptic.ConstantSchauder P201.Elliptic.HalfSpaceLift
open scoped Topology

lemma secondPartial_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (i j : Fin n) :
    secondPartial (u ∘ Φ) i j x =
      fderiv ℝ (fderiv ℝ u) (Φ x) (fderiv ℝ Φ x (coordinate n i))
        (fderiv ℝ Φ x (coordinate n j)) +
      fderiv ℝ u (Φ x)
        (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) := by
  have hdu : DifferentiableAt ℝ u (Φ x) := hu.differentiableAt (by norm_num)
  have hdΦ : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (by norm_num)
  have hdu2 : DifferentiableAt ℝ (fderiv ℝ u) (Φ x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdΦ2 : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEq : firstPartial (u ∘ Φ) j =ᶠ[𝓝 x]
      fun y => fderiv ℝ u (Φ y) (fderiv ℝ Φ y (coordinate n j)) := by
    filter_upwards [hΦ.eventually (by norm_num),
      hdΦ.continuousAt.eventually (hu.eventually (by norm_num))] with y hΦy huy
    unfold firstPartial
    rw [fderiv_comp y (huy.differentiableAt (by norm_num))
      (hΦy.differentiableAt (by norm_num))]
    rfl
  change fderiv ℝ (firstPartial (u ∘ Φ) j) x (coordinate n i) = _
  rw [hEq.fderiv_eq]
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ u (Φ y)) x := hdu2.comp x hdΦ
  rw [fderiv_clm_apply hA
    (hdΦ2.clm_apply (differentiableAt_const (coordinate n j)))]
  rw [show fderiv ℝ (fun y => fderiv ℝ u (Φ y)) x =
      (fderiv ℝ (fderiv ℝ u) (Φ x)).comp (fderiv ℝ Φ x) by
        exact fderiv_comp x hdu2 hdΦ,
    fderiv_clm_apply hdΦ2 (differentiableAt_const (coordinate n j))]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  ring

lemma firstPartial_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x)
    (i : Fin n) :
    firstPartial (u ∘ Φ) i x = ∑ k : Fin n,
      (fderiv ℝ Φ x (coordinate n i)) k * firstPartial u k (Φ x) := by
  unfold firstPartial
  rw [fderiv_comp x hu hΦ, ContinuousLinearMap.comp_apply]
  conv_lhs =>
    rw [← coordinateExpansion_eq (fderiv ℝ u (Φ x)), coordinateExpansion_apply]
  simp only [smul_eq_mul]

lemma secondPartial_comp_nonlinear_coordinates {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (i j : Fin n) :
    secondPartial (u ∘ Φ) i j x =
      (∑ k : Fin n, ∑ l : Fin n,
        (fderiv ℝ Φ x (coordinate n i)) k *
        (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x)) +
      ∑ k : Fin n,
        (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
          firstPartial u k (Φ x) := by
  rw [secondPartial_comp_nonlinear hu hΦ i j,
    hessian_eq_coordinateExpansion_at hu]
  conv_lhs =>
    rhs
    rw [← coordinateExpansion_eq (fderiv ℝ u (Φ x))]
  simp only [coordinateExpansion_apply, sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum, ← mul_assoc]
  rfl

private lemma sum_four_comm {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) =
      ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

/-- Actual transformed principal coefficients at a point, before precomposing
with any inverse coordinate map. -/
def transformedPrincipalAt {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => ∑ i : Fin n, ∑ j : Fin n, a x i j *
    (fderiv ℝ Φ x (coordinate n i)) k * (fderiv ℝ Φ x (coordinate n j)) l

/-- The derivative of the coordinate map contributes the expected new
first-order terms. No transformed equation is assumed. -/
def transformedDriftAt {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (Φ : Space n → Space n) (x : Space n) : Fin n → ℝ :=
  fun k => (∑ i : Fin n, ∑ j : Fin n, a x i j *
    (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) +
    ∑ i : Fin n, b x i * (fderiv ℝ Φ x (coordinate n i)) k

lemma nondivergenceOperator_comp_nonlinear {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x) :
    nondivergenceOperator a b c (u ∘ Φ) x =
      (∑ k : Fin n, ∑ l : Fin n,
        transformedPrincipalAt a Φ x k l * secondPartial u k l (Φ x)) +
      (∑ k : Fin n, transformedDriftAt a b Φ x k * firstPartial u k (Φ x)) +
      c x * u (Φ x) := by
  unfold nondivergenceOperator transformedPrincipalAt transformedDriftAt
  simp_rw [firstPartial_comp_nonlinear (hu.differentiableAt (by norm_num))
    (hΦ.differentiableAt (by norm_num)), secondPartial_comp_nonlinear_coordinates hu hΦ]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  have hprincipal :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        a x i j * ((fderiv ℝ Φ x (coordinate n i)) k *
          (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x))) =
      ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        a x i j * (fderiv ℝ Φ x (coordinate n i)) k *
          (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x) := by
    rw [sum_four_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprincipal]
  have hcurvature :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        a x i j * ((fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
          firstPartial u k (Φ x))) =
      ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        (a x i j * (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) *
          firstPartial u k (Φ x) := by
    calc
      _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
          a x i j * ((fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
            firstPartial u k (Φ x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        congr 1
        funext k
        congr 1
        funext i
        congr 1
        funext j
        ring
  rw [hcurvature, Finset.sum_comm (f := fun i k =>
    b x i * ((fderiv ℝ Φ x (coordinate n i)) k * firstPartial u k (Φ x)))]
  simp only [Function.comp_apply, mul_assoc]
  ring

/-- Reindexing the actual coefficient formula through an inverse coordinate
map gives the transformed nondivergence operator at the image point. Only the
pointwise inverse identity is needed for this algebraic chain rule. -/
lemma nondivergenceOperator_comp_coordinates {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} {Φ Ψ : Space n → Space n}
    {x : Space n} (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (hInv : Ψ (Φ x) = x) :
    nondivergenceOperator a b c (u ∘ Φ) x =
      nondivergenceOperator
        (fun y => transformedPrincipalAt a Φ (Ψ y))
        (fun y => WithLp.toLp 2 (transformedDriftAt a b Φ (Ψ y)))
        (c ∘ Ψ) u (Φ x) := by
  rw [nondivergenceOperator_comp_nonlinear a b c hu hΦ]
  simp only [nondivergenceOperator, hInv, Function.comp_apply]



/-- The analogous quantitative patching lemma for the canonical interior
norm. Its constant is uniform in the function and the data size. -/
theorem finite_cover_c2Holder_estimate {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {s : Set (Space n)} (hcompact : IsCompact s) {ι : Type*} [Fintype ι]
    (U : ι → Set (Space n)) (hopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space n → ℝ) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ 2 u s →
      (∀ i, IsC2HolderOn α u (s ∩ U i) ∧
        c2HolderNormOn α u (s ∩ U i) ≤ A i * D) →
      IsC2HolderOn α u s ∧ c2HolderNormOn α u s ≤ C * D := by
  classical
  obtain ⟨B, hB, hpatch⟩ := finite_cover_holder_estimate hα hcompact U hopen hcover A hA
  let T := ∑ i, A i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => hA i)
  have hiT (i : ι) : A i ≤ T := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  refine ⟨1 + (1 + (n : ℝ)) * T + (n : ℝ)^2 * B, by positivity, ?_⟩
  intro u D hD hu hlocal
  have hlocalnorm (i : ι) : c2HolderNormOn α u (s ∩ U i) ≤ T * D :=
    (hlocal i).2.trans (mul_le_mul_of_nonneg_right (hiT i) hD)
  have h0 : ∀ x ∈ s, ‖u x‖ ≤ T * D := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact (P201.Elliptic.PoissonSchauder.norm_le_supNormOn (hlocal i).1.2.1 ⟨hx, hi⟩).trans
      ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u (s ∩ U i)).1.trans
        (hlocalnorm i))
  have h1 (k : Fin n) : ∀ x ∈ s, ‖multiPartial u {k} x‖ ≤ T * D := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact (P201.Elliptic.PoissonSchauder.norm_le_supNormOn ((hlocal i).1.2.2.1 k) ⟨hx, hi⟩).trans
      (((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u (s ∩ U i)).2.1 k).trans
        (hlocalnorm i))
  have h2 (k l : Fin n) : IsHolderOn α (multiPartial u {k,l}) s ∧
      holderNormOn α (multiPartial u {k,l}) s ≤ B * D := by
    apply hpatch _ D hD
    intro i
    exact (HolderBoundsOn.of_norm ((hlocal i).1.2.2.2 k l)).mono
      (((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u (s ∩ U i)).2.2 k l).trans
        (hlocal i).2)
      (((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α u (s ∩ U i)).2.2 k l).trans
        (hlocal i).2)
  refine ⟨⟨hu, ⟨T * D, mul_nonneg hT hD, h0⟩,
    fun k => ⟨T * D, mul_nonneg hT hD, h1 k⟩, fun k l => (h2 k l).1⟩, ?_⟩
  have hsup : supNormOn u s ≤ T * D :=
    P201.Elliptic.NewtonHessian.supNormOn_le (mul_nonneg hT hD) h0
  have hfirst : (∑ k : Fin n, supNormOn (multiPartial u {k}) s) ≤ (n : ℝ) * (T * D) := by
    calc
      _ ≤ ∑ _k : Fin n, T * D := Finset.sum_le_sum fun k _ =>
        P201.Elliptic.NewtonHessian.supNormOn_le (mul_nonneg hT hD) (h1 k)
      _ = _ := by simp
  have hsecond : (∑ k : Fin n, ∑ l : Fin n, holderNormOn α (multiPartial u {k,l}) s) ≤
      (n : ℝ)^2 * (B * D) := by
    calc
      _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, B * D :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => (h2 k l).2
      _ = _ := by simp; ring
  change supNormOn u s + (∑ k : Fin n, supNormOn (multiPartial u {k}) s) +
    (∑ k : Fin n, ∑ l : Fin n, holderNormOn α (multiPartial u {k,l}) s) ≤ _
  calc
    _ ≤ T * D + (n : ℝ) * (T * D) + (n : ℝ)^2 * (B * D) :=
      add_le_add (add_le_add hsup hfirst) hsecond
    _ ≤ (1 + (1 + (n : ℝ)) * T + (n : ℝ)^2 * B) * D := by nlinarith

/-- The covector transformation forced by the derivative of the coordinate
map. This is the transpose Jacobian action, expressed in the fixed basis. -/
def transformedCovectorAt {n : ℕ} (Φ : Space n → Space n) (x ξ : Space n) : Space n :=
  WithLp.toLp 2 (fun i => ∑ k : Fin n,
    (fderiv ℝ Φ x (coordinate n i)) k * ξ k)

lemma transformedPrincipalAt_symmetric {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x : Space n) (ha : ∀ i j, a x i j = a x j i) (k l : Fin n) :
    transformedPrincipalAt a Φ x k l = transformedPrincipalAt a Φ x l k := by
  unfold transformedPrincipalAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

lemma transformedPrincipalAt_quadratic {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x ξ : Space n) :
    (∑ k : Fin n, ∑ l : Fin n,
      transformedPrincipalAt a Φ x k l * ξ k * ξ l) =
      ∑ i : Fin n, ∑ j : Fin n,
        a x i j * transformedCovectorAt Φ x ξ i * transformedCovectorAt Φ x ξ j := by
  unfold transformedPrincipalAt transformedCovectorAt
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma transformedCovectorAt_eq_adjoint {n : ℕ}
    (Φ : Space n → Space n) (x ξ : Space n) :
    transformedCovectorAt Φ x ξ = (fderiv ℝ Φ x).adjoint ξ := by
  ext i
  rw [← inner_coordinate ((fderiv ℝ Φ x).adjoint ξ) i]
  change (∑ k : Fin n, (fderiv ℝ Φ x (coordinate n i)) k * ξ k) =
    inner ℝ ((fderiv ℝ Φ x).adjoint ξ) (coordinate n i)
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

lemma transformedCovectorAt_norm_bounds {n : ℕ}
    {Φ : Space n → Space n} {x : Space n}
    (T : Space n ≃L[ℝ] Space n) (hT : fderiv ℝ Φ x = T.toContinuousLinearMap)
    {K L : ℝ} (hTK : ‖T.toContinuousLinearMap‖ ≤ K)
    (hTL : ‖T.symm.toContinuousLinearMap‖ ≤ L) (ξ : Space n) :
    ‖transformedCovectorAt Φ x ξ‖ ≤ K * ‖ξ‖ ∧
      ‖ξ‖ ≤ L * ‖transformedCovectorAt Φ x ξ‖ := by
  rw [transformedCovectorAt_eq_adjoint, hT]
  have hinv : T.symm.toContinuousLinearMap.adjoint (T.toContinuousLinearMap.adjoint ξ) = ξ := by
    change (T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint) ξ = ξ
    rw [← ContinuousLinearMap.adjoint_comp]
    have he : T.toContinuousLinearMap.comp T.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Space n) := by ext z; simp
    rw [he, ContinuousLinearMap.adjoint_id]
    rfl
  constructor
  · exact (T.toContinuousLinearMap.adjoint.le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (by simpa using hTK) (norm_nonneg ξ))
  · calc
      ‖ξ‖ = ‖T.symm.toContinuousLinearMap.adjoint (T.toContinuousLinearMap.adjoint ξ)‖ :=
        congrArg norm hinv.symm
      _ ≤ ‖T.symm.toContinuousLinearMap.adjoint‖ * ‖T.toContinuousLinearMap.adjoint ξ‖ :=
        T.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ L * ‖T.toContinuousLinearMap.adjoint ξ‖ :=
        mul_le_mul_of_nonneg_right (by simpa using hTL) (norm_nonneg _)

lemma transformedPrincipalAt_matrixBounds {n : ℕ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {Φ : Space n → Space n} {x : Space n}
    {ell upper K L : ℝ} (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    (hK : 0 ≤ K) (hL : 0 < L)
    (ha : P201Specs.Elliptic.ConstantSchauder.MatrixBounds ell upper (a x))
    (T : Space n ≃L[ℝ] Space n) (hT : fderiv ℝ Φ x = T.toContinuousLinearMap)
    (hTK : ‖T.toContinuousLinearMap‖ ≤ K)
    (hTL : ‖T.symm.toContinuousLinearMap‖ ≤ L) :
    P201Specs.Elliptic.ConstantSchauder.MatrixBounds (ell / L^2) (upper * K^2)
      (transformedPrincipalAt a Φ x) := by
  refine ⟨transformedPrincipalAt_symmetric a Φ x ha.1, fun ξ => ?_⟩
  rw [transformedPrincipalAt_quadratic]
  obtain ⟨hηupper, hηlower⟩ := transformedCovectorAt_norm_bounds T hT hTK hTL ξ
  obtain ⟨hlower, hupper'⟩ := ha.2 (transformedCovectorAt Φ x ξ)
  have hlowersq : ‖ξ‖^2 ≤ L^2 * ‖transformedCovectorAt Φ x ξ‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg ξ)
      (mul_nonneg hL.le (norm_nonneg _))).mpr hηlower
  have huppersq : ‖transformedCovectorAt Φ x ξ‖^2 ≤ K^2 * ‖ξ‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hK (norm_nonneg ξ))).mpr hηupper
  constructor
  · apply le_trans _ hlower
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlowersq hell]
  · apply hupper'.trans
    nlinarith [mul_le_mul_of_nonneg_left huppersq hupper]


lemma holder_interpolation_scalar {α δ M L t q : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (ht : 0 ≤ t) (hqM : q ≤ 2 * M) (hqL : q ≤ L * t) :
    q ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
  have hδa : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  have hta : 0 ≤ t ^ α := Real.rpow_nonneg ht _
  by_cases htd : t ≤ δ
  · have htprod : t ≤ δ ^ (1 - α) * t ^ α := by
      by_cases ht0 : t = 0
      · rw [ht0]; positivity
      have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      calc
        t = t ^ (1 - α) * t ^ α := by
          rw [← Real.rpow_add htp]; simp
        _ ≤ δ ^ (1 - α) * t ^ α :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htd (by linarith)) hta
    calc
      q ≤ L * t := hqL
      _ ≤ L * (δ ^ (1 - α) * t ^ α) := mul_le_mul_of_nonneg_left htprod hL
      _ ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
        have : 0 ≤ 2 * M / δ ^ α := by positivity
        nlinarith
  · have hda : δ ^ α ≤ t ^ α := Real.rpow_le_rpow hδ.le (le_of_not_ge htd) hα
    calc
      q ≤ 2 * M := hqM
      _ ≤ (2 * M / δ ^ α) * t ^ α := by
        calc
          2 * M = (2 * M / δ ^ α) * δ ^ α := by field_simp
          _ ≤ (2 * M / δ ^ α) * t ^ α :=
            mul_le_mul_of_nonneg_left hda (by positivity)
      _ ≤ (δ ^ (1 - α) * L + 2 * M / δ ^ α) * t ^ α := by
        have : 0 ≤ δ ^ (1 - α) * L := by positivity
        nlinarith

open Set Metric

lemma weighted_holder_interpolation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {d : E → ℝ} {v : E → F} {v' : E → E →L[ℝ] F}
    {α h M L : ℝ} (j : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 < h)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hd : ∀ x ∈ s, 0 < d x)
    (hc : ∀ t : ℝ, Convex ℝ {x | x ∈ s ∧ t ≤ d x})
    (hv : ∀ x ∈ s, HasFDerivWithinAt v (v' x) s x)
    (hb : ∀ x ∈ s, d x ^ j * ‖v x‖ ≤ M)
    (hD : ∀ x ∈ s, d x ^ (j + 1) * ‖v' x‖ ≤ L)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (min (d x) (d y)) ^ ((j : ℝ) + α) * ‖v x - v y‖ ≤
      (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
  let r := min (d x) (d y)
  have hr : 0 < r := lt_min (hd x hx) (hd y hy)
  have hrx : r ≤ d x := min_le_left _ _
  have hry : r ≤ d y := min_le_right _ _
  have hxb : r ^ j * ‖v x‖ ≤ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrx j) (norm_nonneg _)).trans (hb x hx)
  have hyb : r ^ j * ‖v y‖ ≤ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hry j) (norm_nonneg _)).trans (hb y hy)
  have hsup : r ^ j * ‖v x - v y‖ ≤ 2 * M := by
    have h := mul_le_mul_of_nonneg_left (norm_sub_le (v x) (v y)) (pow_nonneg hr.le j)
    nlinarith
  have hdiff : ‖v x - v y‖ ≤ (L / r ^ (j + 1)) * dist x y := by
    have hsubset : {z | z ∈ s ∧ r ≤ d z} ⊆ s := fun z hz => hz.1
    have hbound : ∀ z ∈ {z | z ∈ s ∧ r ≤ d z}, ‖v' z‖ ≤ L / r ^ (j + 1) := by
      intro z hz
      apply (le_div_iff₀ (pow_pos hr _)).mpr
      calc
        ‖v' z‖ * r ^ (j + 1) = r ^ (j + 1) * ‖v' z‖ := by ring
        _ ≤ d z ^ (j + 1) * ‖v' z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hz.2 _) (norm_nonneg _)
        _ ≤ L := hD z hz.1
    simpa only [dist_eq_norm] using (hc r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hv z hz.1).mono hsubset) hbound ⟨hy, hry⟩ ⟨hx, hrx⟩
  have hlinear : r ^ j * ‖v x - v y‖ ≤ L * (dist x y / r) := by
    calc
      r ^ j * ‖v x - v y‖ ≤ r ^ j * ((L / r ^ (j + 1)) * dist x y) :=
        mul_le_mul_of_nonneg_left hdiff (pow_nonneg hr.le j)
      _ = L * (dist x y / r) := by
        rw [pow_succ]
        field_simp
  have hi := holder_interpolation_scalar hα hα1 hh hM hL
    (div_nonneg dist_nonneg hr.le) hsup hlinear
  have hpow : r ^ ((j : ℝ) + α) = r ^ j * r ^ α := by
    rw [Real.rpow_add hr, Real.rpow_natCast]
  have hratio : r ^ α * (dist x y / r) ^ α = dist x y ^ α := by
    rw [Real.div_rpow dist_nonneg hr.le]
    field_simp
  calc
    r ^ ((j : ℝ) + α) * ‖v x - v y‖ = r ^ α * (r ^ j * ‖v x - v y‖) := by
      rw [hpow]; ring
    _ ≤ r ^ α * ((h ^ (1 - α) * L + 2 * M / h ^ α) * (dist x y / r) ^ α) :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hr.le _)
    _ = (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
      rw [← mul_assoc, mul_comm (r ^ α), mul_assoc, hratio]

/-- In a convex portion of a ball, the spherical-distance weight has convex
superlevel sets. This applies also to a half-ball together with its flat face. -/
lemma radial_weighted_holder_interpolation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {v : E → F} {v' : E → E →L[ℝ] F} {center : E}
    {α h M L R : ℝ} (j : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 < h)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hs : Convex ℝ s) (hsR : s ⊆ ball center R)
    (hv : ∀ x ∈ s, HasFDerivWithinAt v (v' x) s x)
    (hb : ∀ x ∈ s, (R - dist x center) ^ j * ‖v x‖ ≤ M)
    (hD : ∀ x ∈ s, (R - dist x center) ^ (j + 1) * ‖v' x‖ ≤ L)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (min (R - dist x center) (R - dist y center)) ^ ((j : ℝ) + α) * ‖v x - v y‖ ≤
      (h ^ (1 - α) * L + 2 * M / h ^ α) * dist x y ^ α := by
  apply weighted_holder_interpolation j hα hα1 hh hM hL
    (fun z hz => sub_pos.mpr (mem_ball.mp (hsR hz))) _ hv hb hD hx hy
  intro t
  have heq : {z | z ∈ s ∧ t ≤ R - dist z center} = s ∩ closedBall center (R - t) := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall]
    constructor
    · rintro ⟨hz, ht⟩; exact ⟨hz, by linarith⟩
    · rintro ⟨hz, ht⟩; exact ⟨hz, by linarith⟩
  rw [heq]
  exact hs.inter (convex_closedBall center (R - t))

lemma holder_interpolation_scale {α ε : ℝ} (hα : α < 1) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ^ (1 - α) = ε := by
  refine ⟨ε ^ (1 / (1 - α)), Real.rpow_pos_of_pos hε _, ?_⟩
  rw [← Real.rpow_mul hε.le]
  have hne : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα)
  rw [one_div_mul_cancel hne, Real.rpow_one]

/-- A one-sided second-order Taylor remainder from two applications of the
mean value theorem. The second derivative need only exist within the segment. -/
lemma one_sided_second_remainder_bound {f f₁ f₂ : ℝ → ℝ} {T K : ℝ}
    (_hT : 0 ≤ T) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f₁ t) (Icc 0 T) t)
    (hf₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt f₁ (f₂ t) (Icc 0 T) t)
    (hD : ∀ t ∈ Icc 0 T, ‖f₂ t - f₂ 0‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2‖ ≤ K * T * t := by
  have hfirst : ∀ t ∈ Icc 0 T, ‖f₁ t - f₁ 0 - f₂ 0 * t‖ ≤ K * t := by
    have hd : ∀ t ∈ Icc 0 T,
        HasDerivWithinAt (fun t => f₁ t - f₁ 0 - f₂ 0 * t)
          (f₂ t - f₂ 0) (Icc 0 T) t := by
      intro t ht
      convert ((hf₁ t ht).sub_const (f₁ 0)).sub
        ((hasDerivWithinAt_id t (Icc 0 T)).const_mul (f₂ 0)) using 1 <;> (try funext u) <;> (try simp only [Pi.sub_apply, id_eq]) <;> ring
    intro t ht
    simpa using norm_image_sub_le_of_norm_deriv_le_segment' hd
      (fun t ht => hD t (Ico_subset_Icc_self ht)) t ht
  have hd : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2)
        (f₁ t - f₁ 0 - f₂ 0 * t) (Icc 0 T) t := by
    intro t ht
    convert (((hf t ht).sub_const (f 0)).sub
      ((hasDerivWithinAt_id t (Icc 0 T)).const_mul (f₁ 0))).sub
      ((((hasDerivWithinAt_id t (Icc 0 T)).pow 2).const_mul (f₂ 0)).div_const 2) using 1 <;> (try funext u) <;> (try simp only [Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring
  have hb : ∀ t ∈ Ico 0 T, ‖f₁ t - f₁ 0 - f₂ 0 * t‖ ≤ K * T := by
    intro t ht
    exact (hfirst t (Ico_subset_Icc_self ht)).trans (mul_le_mul_of_nonneg_left ht.2.le hK)
  simpa using norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ht

/-- A genuine one-sided second-difference interpolation estimate. It uses
only three function values and the oscillation of the actual second derivative
on the same segment; it contains no PDE estimate among its hypotheses. -/
lemma one_sided_second_difference_bound {f f₁ f₂ : ℝ → ℝ} {h M K : ℝ}
    (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f (f₁ t) (Icc 0 (2 * h)) t)
    (hf₁ : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f₁ (f₂ t) (Icc 0 (2 * h)) t)
    (hD : ∀ t ∈ Icc 0 (2 * h), ‖f₂ t - f₂ 0‖ ≤ K)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) (hb2h : ‖f (2 * h)‖ ≤ M) :
    ‖f₂ 0‖ ≤ 4 * M / h ^ 2 + 8 * K := by
  let r₁ := f h - f 0 - f₁ 0 * h - f₂ 0 * h ^ 2 / 2
  let r₂ := f (2 * h) - f 0 - f₁ 0 * (2 * h) - f₂ 0 * (2 * h) ^ 2 / 2
  have hr₁ : ‖r₁‖ ≤ 2 * K * h ^ 2 := by
    have hr := one_sided_second_remainder_bound (by positivity : 0 ≤ 2 * h) hK hf hf₁ hD
      (show h ∈ Icc 0 (2 * h) by constructor <;> linarith)
    change ‖f h - f 0 - f₁ 0 * h - f₂ 0 * h ^ 2 / 2‖ ≤ 2 * K * h ^ 2
    convert hr using 1 <;> ring
  have hr₂ : ‖r₂‖ ≤ 4 * K * h ^ 2 := by
    have hr := one_sided_second_remainder_bound (by positivity : 0 ≤ 2 * h) hK hf hf₁ hD
      (show 2 * h ∈ Icc 0 (2 * h) by constructor <;> linarith)
    change ‖f (2 * h) - f 0 - f₁ 0 * (2 * h) - f₂ 0 * (2 * h) ^ 2 / 2‖ ≤ 4 * K * h ^ 2
    convert hr using 1 <;> ring
  have hdelta : ‖f (2 * h) - 2 * f h + f 0‖ ≤ 4 * M := by
    calc
      _ ≤ ‖f (2 * h) - 2 * f h‖ + ‖f 0‖ := norm_add_le _ _
      _ ≤ ‖f (2 * h)‖ + ‖2 * f h‖ + ‖f 0‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖f (2 * h)‖ + 2 * ‖f h‖ + ‖f 0‖ := by simp
      _ ≤ 4 * M := by linarith
  have heq : h ^ 2 * f₂ 0 = (f (2 * h) - 2 * f h + f 0) - r₂ + 2 * r₁ := by
    dsimp [r₁, r₂]
    ring
  have hmain : h ^ 2 * ‖f₂ 0‖ ≤ 4 * M + 8 * K * h ^ 2 := by
    calc
      _ = ‖h ^ 2 * f₂ 0‖ := by rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      _ = ‖(f (2 * h) - 2 * f h + f 0) - r₂ + 2 * r₁‖ := by rw [heq]
      _ ≤ ‖(f (2 * h) - 2 * f h + f 0) - r₂‖ + ‖2 * r₁‖ := norm_add_le _ _
      _ ≤ ‖f (2 * h) - 2 * f h + f 0‖ + ‖r₂‖ + ‖2 * r₁‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖f (2 * h) - 2 * f h + f 0‖ + ‖r₂‖ + 2 * ‖r₁‖ := by simp
      _ ≤ 4 * M + 8 * K * h ^ 2 := by linarith
  calc
    ‖f₂ 0‖ ≤ (4 * M + 8 * K * h ^ 2) / h ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hh)).mpr (by simpa only [mul_comm] using hmain)
    _ = 4 * M / h ^ 2 + 8 * K := by field_simp

/-- The Hölder-oscillation form used in the Hessian interpolation argument.
The step is one-sided, so no negative direction or extension across a flat
boundary is required. -/
lemma one_sided_second_difference_holder_bound {f f₁ f₂ : ℝ → ℝ} {α h M H : ℝ}
    (hα : 0 ≤ α) (hh : 0 < h) (hH : 0 ≤ H)
    (hf : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f (f₁ t) (Icc 0 (2 * h)) t)
    (hf₁ : ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt f₁ (f₂ t) (Icc 0 (2 * h)) t)
    (hD : ∀ t ∈ Icc 0 (2 * h), ‖f₂ t - f₂ 0‖ ≤ H * t ^ α)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) (hb2h : ‖f (2 * h)‖ ≤ M) :
    ‖f₂ 0‖ ≤ 4 * M / h ^ 2 + 8 * H * (2 * h) ^ α := by
  have hK : 0 ≤ H * (2 * h) ^ α := by positivity
  have hb := one_sided_second_difference_bound hh hK hf hf₁
    (fun t ht => (hD t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 hα) hH)) hb0 hbh hb2h
  convert hb using 1 <;> ring

/-- The corresponding one-sided first-difference estimate, retaining its
small step in front of the second derivative bound. -/
lemma one_sided_first_difference_bound {f f₁ f₂ : ℝ → ℝ} {h M L : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc 0 h, HasDerivWithinAt f (f₁ t) (Icc 0 h) t)
    (hf₁ : ∀ t ∈ Icc 0 h, HasDerivWithinAt f₁ (f₂ t) (Icc 0 h) t)
    (hD : ∀ t ∈ Icc 0 h, ‖f₂ t‖ ≤ L)
    (hb0 : ‖f 0‖ ≤ M) (hbh : ‖f h‖ ≤ M) :
    ‖f₁ 0‖ ≤ 2 * M / h + h * L := by
  have hfirst : ∀ t ∈ Icc 0 h, ‖f₁ t - f₁ 0‖ ≤ L * t := by
    simpa only [sub_zero] using (norm_image_sub_le_of_norm_deriv_le_segment' hf₁
      (fun t ht => hD t (Ico_subset_Icc_self ht)))
  have hdr : ∀ t ∈ Icc 0 h,
      HasDerivWithinAt (fun t => f t - f 0 - f₁ 0 * t)
        (f₁ t - f₁ 0) (Icc 0 h) t := by
    intro t ht
    convert ((hf t ht).sub_const (f 0)).sub
      ((hasDerivWithinAt_id t (Icc 0 h)).const_mul (f₁ 0)) using 1
    · funext u; simp only [Pi.sub_apply, id_eq]
    · ring
  have hrem : ‖f h - f 0 - f₁ 0 * h‖ ≤ L * h ^ 2 := by
    have hr := norm_image_sub_le_of_norm_deriv_le_segment' hdr
      (fun t ht => (hfirst t (Ico_subset_Icc_self ht)).trans
        (mul_le_mul_of_nonneg_left ht.2.le hL)) h ⟨hh.le, le_rfl⟩
    simpa only [mul_zero, sub_self, sub_zero, pow_two, mul_assoc] using hr
  have hm : ‖h * f₁ 0‖ ≤ 2 * M + L * h ^ 2 := by
    calc
      _ = ‖(f h - f 0) - (f h - f 0 - f₁ 0 * h)‖ := by congr 1; ring
      _ ≤ ‖f h - f 0‖ + ‖f h - f 0 - f₁ 0 * h‖ := norm_sub_le _ _
      _ ≤ ‖f h‖ + ‖f 0‖ + ‖f h - f 0 - f₁ 0 * h‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ 2 * M + L * h ^ 2 := by linarith
  rw [norm_mul, Real.norm_of_nonneg hh.le] at hm
  calc
    ‖f₁ 0‖ ≤ (2 * M + L * h ^ 2) / h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hm)
    _ = 2 * M / h + h * L := by field_simp

/-- Applying the one-sided interpolation argument to an actual spatial
segment. Both displayed fields are required to be actual first and second
within derivatives; no freely chosen Hessian field is substituted. -/
lemma directional_second_difference_holder_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {u : E → ℝ}
    {Du : E → E →L[ℝ] ℝ} {D₂u : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x v : E} {α h M H : ℝ} (hα : 0 ≤ α) (hh : 0 < h) (hH : 0 ≤ H)
    (hseg : MapsTo (fun t : ℝ => x + t • v) (Icc 0 (2 * h)) s)
    (hu : ∀ z ∈ s, HasFDerivWithinAt u (Du z) s z)
    (hDu : ∀ z ∈ s, HasFDerivWithinAt Du (D₂u z) s z)
    (hD : ∀ t ∈ Icc 0 (2 * h),
      ‖(D₂u (x + t • v) v) v - (D₂u x v) v‖ ≤ H * t ^ α)
    (hb0 : ‖u x‖ ≤ M) (hbh : ‖u (x + h • v)‖ ≤ M)
    (hb2h : ‖u (x + (2 * h) • v)‖ ≤ M) :
    ‖(D₂u x v) v‖ ≤ 4 * M / h ^ 2 + 8 * H * (2 * h) ^ α := by
  have hcurve : ∀ t : ℝ,
      HasDerivWithinAt (fun t : ℝ => x + t • v) v (Icc 0 (2 * h)) t := by
    intro t
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const v).const_add x |>.hasDerivWithinAt
  have hf : ∀ t ∈ Icc 0 (2 * h),
      HasDerivWithinAt (fun t => u (x + t • v)) (Du (x + t • v) v) (Icc 0 (2 * h)) t := by
    intro t ht
    exact (hu _ (hseg ht)).comp_hasDerivWithinAt t (hcurve t) hseg
  have hf₁ : ∀ t ∈ Icc 0 (2 * h),
      HasDerivWithinAt (fun t => Du (x + t • v) v)
        ((D₂u (x + t • v) v) v) (Icc 0 (2 * h)) t := by
    intro t ht
    have h := (hDu _ (hseg ht)).comp_hasDerivWithinAt t (hcurve t) hseg
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivWithinAt t h
  simpa only [zero_smul, add_zero] using
    one_sided_second_difference_holder_bound hα hh hH hf hf₁
      (by simpa only [zero_smul, add_zero] using hD)
      (by simpa only [zero_smul, add_zero] using hb0) hbh hb2h

/-- Polarization controls mixed Hessian entries using forward directions
only. The symmetry hypothesis is precisely the equality of mixed second
Fréchet derivatives supplied by local C² regularity. -/
lemma symmetric_bilinear_mixed_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) {Qv Qw Qsum : ℝ}
    (hSymm : B v w = B w v)
    (hv : ‖B v v‖ ≤ Qv) (hw : ‖B w w‖ ≤ Qw)
    (hsum : ‖B (v + w) (v + w)‖ ≤ Qsum) :
    ‖B v w‖ ≤ (Qsum + Qv + Qw) / 2 := by
  have heq : 2 * B v w = B (v + w) (v + w) - B v v - B w w := by
    simp only [map_add, add_apply]
    rw [← hSymm]
    ring
  have hb : 2 * ‖B v w‖ ≤ Qsum + Qv + Qw := by
    calc
      _ = ‖2 * B v w‖ := by simp
      _ = ‖B (v + w) (v + w) - B v v - B w w‖ := by rw [heq]
      _ ≤ ‖B (v + w) (v + w) - B v v‖ + ‖B w w‖ := norm_sub_le _ _
      _ ≤ (‖B (v + w) (v + w)‖ + ‖B v v‖) + ‖B w w‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ Qsum + Qv + Qw := by linarith
  linarith

/-- Patch the outer-set jets on a compact observation region, then restrict to
an open inner observation set. This avoids differentiating on the edge of the
compact set used only to select a finite cover. -/
theorem finite_cover_c2HolderUpTo_estimate_on {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {s k : Set (Space n)} (hcompact : IsCompact k) (hks : k ⊆ s)
    (V : Domain n) (htk : s ∩ (V : Set (Space n)) ⊆ k)
    {ι : Type*} [Fintype ι]
    (U : ι → Set (Space n)) (hopen : ∀ i, IsOpen (U i))
    (hcover : k ⊆ ⋃ i, U i) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space n → ℝ) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ 2 u s →
      (∀ i, IsC2HolderUpToOn α u (s ∩ U i) ∧
        c2HolderUpToNormOn α u (s ∩ U i) ≤ A i * D) →
      IsC2HolderUpToOn α u (s ∩ (V : Set (Space n))) ∧
        c2HolderUpToNormOn α u (s ∩ (V : Set (Space n))) ≤ C * D := by
  classical
  obtain ⟨B, hB, hpatch⟩ := compact_holder_patching hα hcompact U hopen hcover
  let T := ∑ i, A i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => hA i)
  have hiT (i : ι) : A i ≤ T := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  let F : ℝ := 1 + n + (n : ℝ)^2 + (n : ℝ)^2 * (1 + B)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F * (T + 1), mul_pos hF (by linarith), ?_⟩
  intro u D hD hu hlocal
  let M := T * D
  have hM : 0 ≤ M := mul_nonneg hT hD
  have hHM : 0 ≤ M + B * M := add_nonneg hM (mul_nonneg hB.le hM)
  have hlocalbounds (i : ι) :=
    P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_bounds
      (r := 1) zero_le_one (hlocal i).1
  have hlocalnorm (i : ι) : scaledWithinSolutionNorm α 1 u (s ∩ U i) ≤ M :=
    (hlocal i).2.trans (mul_le_mul_of_nonneg_right (hiT i) hD)
  have h0 : ∀ x ∈ k, ‖u x‖ ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact ((hlocalbounds i).1 x ⟨hks hx, hi⟩).trans (hlocalnorm i)
  have h1 : ∀ j : Fin n, ∀ x ∈ k, ‖firstPartialWithin u s j x‖ ≤ M := by
    intro j x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    rw [← (within_jets_restrict_open u s (hopen i) hi).1 j]
    have hb : ‖firstPartialWithin u (s ∩ U i) j x‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) := by
      simpa only [one_mul] using (hlocalbounds i).2.1 j x ⟨hks hx, hi⟩
    exact hb.trans (hlocalnorm i)
  have h2 : ∀ j l : Fin n, ∀ x ∈ k, ‖secondPartialWithin u s j l x‖ ≤ M := by
    intro j l x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    rw [← (within_jets_restrict_open u s (hopen i) hi).2 j l]
    have hb : ‖secondPartialWithin u (s ∩ U i) j l x‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) := by
      simpa only [one_pow, one_mul] using (hlocalbounds i).2.2.1 j l x ⟨hks hx, hi⟩
    exact hb.trans (hlocalnorm i)
  have hH : ∀ j l : Fin n, ∀ x ∈ k, ∀ y ∈ k,
      ‖secondPartialWithin u s j l x - secondPartialWithin u s j l y‖ ≤
        (M + B * M) * dist x y ^ α := by
    intro j l
    apply (hpatch (secondPartialWithin u s j l) M M hM hM (h2 j l) ?_).diff_le
    intro i x hx y hy
    rw [← (within_jets_restrict_open u s (hopen i) hx.2).2 j l,
      ← (within_jets_restrict_open u s (hopen i) hy.2).2 j l]
    have hb : ‖secondPartialWithin u (s ∩ U i) j l x -
        secondPartialWithin u (s ∩ U i) j l y‖ ≤
        scaledWithinSolutionNorm α 1 u (s ∩ U i) * dist x y ^ α := by
      simpa only [Real.one_rpow, one_mul] using
        (hlocalbounds i).2.2.2 j l x ⟨hks hx.1, hx.2⟩ y ⟨hks hy.1, hy.2⟩
    exact hb.trans
      (mul_le_mul_of_nonneg_right (hlocalnorm i) (Real.rpow_nonneg dist_nonneg _))
  have ht0 : ∀ x ∈ s ∩ (V : Set (Space n)), ‖u x‖ ≤ M :=
    fun x hx => h0 x (htk hx)
  have ht1 : ∀ j : Fin n, ∀ x ∈ s ∩ (V : Set (Space n)),
      ‖firstPartialWithin u (s ∩ (V : Set (Space n))) j x‖ ≤ M := by
    intro j x hx
    rw [(within_jets_restrict_open u s V.isOpen hx.2).1 j]
    exact h1 j x (htk hx)
  have ht2 : ∀ j l : Fin n, ∀ x ∈ s ∩ (V : Set (Space n)),
      ‖secondPartialWithin u (s ∩ (V : Set (Space n))) j l x‖ ≤ M := by
    intro j l x hx
    rw [(within_jets_restrict_open u s V.isOpen hx.2).2 j l]
    exact h2 j l x (htk hx)
  have htH : ∀ j l : Fin n, ∀ x ∈ s ∩ (V : Set (Space n)),
      ∀ y ∈ s ∩ (V : Set (Space n)),
      ‖secondPartialWithin u (s ∩ (V : Set (Space n))) j l x -
        secondPartialWithin u (s ∩ (V : Set (Space n))) j l y‖ ≤
        (M + B * M) * dist x y ^ α := by
    intro j l x hx y hy
    rw [(within_jets_restrict_open u s V.isOpen hx.2).2 j l,
      (within_jets_restrict_open u s V.isOpen hy.2).2 j l]
    exact hH j l x (htk hx) y (htk hy)
  obtain ⟨hclass, hnorm⟩ :=
    P201.Elliptic.ConstantSchauder.scaledWithinSolutionNorm_le_of_bounds
      (r := 1) zero_le_one hM hM hM hHM (hu.mono inter_subset_left) ht0 ht1 ht2 htH
  refine ⟨hclass, hnorm.trans ?_⟩
  simp only [one_pow, Real.one_rpow, one_mul]
  calc
    M + (n : ℝ) * M + (n : ℝ)^2 * M + (n : ℝ)^2 * (M + B * M) = F * T * D := by
      dsimp [F, M]; ring
    _ ≤ (F * (T + 1)) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hF.le) hD
theorem scaledWithinSolutionNorm_inter_open_le {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s U : Set (Space n)} (hU : IsOpen U)
    (hu : IsC2HolderUpToOn α u s) :
    scaledWithinSolutionNorm α r u (s ∩ U) ≤ scaledWithinSolutionNorm α r u s := by
  have hst : s ∩ U ⊆ s := inter_subset_left
  have h1 (i : Fin n) : EqOn (firstPartialWithin u (s ∩ U) i)
      (firstPartialWithin u s i) (s ∩ U) :=
    fun x hx => (within_jets_restrict_open u s hU hx.2).1 i
  have h2 (i j : Fin n) : EqOn (secondPartialWithin u (s ∩ U) i j)
      (secondPartialWithin u s i j) (s ∩ U) :=
    fun x hx => (within_jets_restrict_open u s hU hx.2).2 i j
  have hzero := P201.Elliptic.PoissonSchauder.supNormOn_mono hu.2.1 hst
  have hone := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    (show supNormOn (firstPartialWithin u (s ∩ U) i) (s ∩ U) ≤ supNormOn (firstPartialWithin u s i) s from by
      rw [P201.Elliptic.ConstantSchauder.supNormOn_congr (h1 i)]
      exact P201.Elliptic.PoissonSchauder.supNormOn_mono (hu.2.2.1 i) hst)
  have htwo := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
    (show supNormOn (secondPartialWithin u (s ∩ U) i j) (s ∩ U) ≤ supNormOn (secondPartialWithin u s i j) s from by
      rw [P201.Elliptic.ConstantSchauder.supNormOn_congr (h2 i j)]
      obtain ⟨M, H, hM, hH, hb, hh⟩ := hu.2.2.2 i j
      exact P201.Elliptic.PoissonSchauder.supNormOn_mono ⟨M, hM, hb⟩ hst)
  have hH := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
    (show P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u (s ∩ U) i j) (s ∩ U) ≤
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i j) s from by
      rw [P201.Elliptic.ConstantSchauder.holderSeminormOn_congr (h2 i j)]
      exact P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
        (fun x hx y hy => P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm (hu.2.2.2 i j) (hst hx) (hst hy)))
  exact add_le_add (add_le_add (add_le_add hzero (mul_le_mul_of_nonneg_left hone hr))
    (mul_le_mul_of_nonneg_left htwo (sq_nonneg _)))
    (mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hr _))



lemma c2HolderNormOn_le_scaled {n : ℕ} {α r : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hr : 0 < r) :
    c2HolderNormOn α u s ≤
      (1 + r⁻¹ + (r ^ 2)⁻¹ + (r ^ (2 + α))⁻¹) * scaledSolutionNorm α r u s := by
  let U := supNormOn u s
  let G := firstDerivativeNormOn u s
  let Q := secondDerivativeNormOn u s
  let H := secondDerivativeSeminormOn α u s
  let S := scaledSolutionNorm α r u s
  have hU : 0 ≤ U := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hG : 0 ≤ G := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  have hpow : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  have hS : S = U + r * G + r^2 * Q + r^(2+α) * H := rfl
  have hbU : U ≤ S := by
    nlinarith [mul_nonneg hr.le hG,
      mul_nonneg (sq_nonneg r) hQ, mul_nonneg hpow.le hH]
  have hbG : G ≤ S / r := (le_div_iff₀ hr).mpr (by
    nlinarith [mul_nonneg (sq_nonneg r) hQ, mul_nonneg hpow.le hH])
  have hbQ : Q ≤ S / r^2 := (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by
    nlinarith [mul_nonneg hr.le hG, mul_nonneg hpow.le hH])
  have hbH : H ≤ S / r^(2+α) := (le_div_iff₀ hpow).mpr (by
    nlinarith [mul_nonneg hr.le hG, mul_nonneg (sq_nonneg r) hQ])
  rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
  change U + G + Q + H ≤ _
  calc
    _ ≤ S + S / r + S / r^2 + S / r^(2+α) :=
      add_le_add (add_le_add (add_le_add hbU hbG) hbQ) hbH
    _ = _ := by dsimp [S]; simp only [div_eq_mul_inv]; ring

lemma scaledDataNorm_le_outer_norm {n : ℕ} {α r : ℝ} {u f : Space n → ℝ}
    {s t : Set (Space n)} (hr : 0 ≤ r) (hu : IsBoundedOn u t)
    (hf : IsHolderOn α f t) (hst : s ⊆ t) :
    scaledDataNorm α r u f s ≤
      (1 + r^2 + r^(2+α)) * (supNormOn u t + holderNormOn α f t) := by
  let D := supNormOn u t + holderNormOn α f t
  have hU : 0 ≤ supNormOn u t := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hF : 0 ≤ supNormOn f t := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hH : 0 ≤ holderSeminormOn α f t :=
    P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  have hFu : IsBoundedOn f t := by
    rcases hf with ⟨M,H,hM,hH,hb,hh⟩
    exact ⟨M,hM,hb⟩
  have h0 : supNormOn u s ≤ D :=
    (P201.Elliptic.PoissonSchauder.supNormOn_mono hu hst).trans (by
      dsimp only [D]; rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]; linarith)
  have h1 : supNormOn f s ≤ D :=
    (P201.Elliptic.PoissonSchauder.supNormOn_mono hFu hst).trans (by
      dsimp only [D]; rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]; linarith)
  have h2 : holderSeminormOn α f s ≤ D := by
    apply le_trans (P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hH
      (fun x hx y hy => P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm hf
        (hst hx) (hst hy)))
    dsimp only [D]; rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]; linarith
  unfold scaledDataNorm
  calc
    _ ≤ D + r^2 * D + r^(2+α) * D :=
      add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hr _))
    _ = _ := by dsimp [D]; ring


lemma isC2HolderLocOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {Ω V : Domain n} (hu : IsC2HolderLocOn α u Ω) (hV : V ≤ Ω) :
    IsC2HolderLocOn α u V := by
  refine ⟨hu.1.mono hV, ?_⟩
  intro x hx
  obtain ⟨r, hr, _, hholder⟩ := hu.2 x (hV hx)
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp V.isOpen x hx
  refine ⟨min r δ, lt_min hr hδ,
    (ball_subset_ball (min_le_right r δ)).trans hδV, ?_⟩
  intro i j
  exact P201.Elliptic.PoissonSchauder.isHolderOn_mono (hholder i j)
    (ball_subset_ball (min_le_left r δ))

lemma interior_ball_unscaled_estimate {n : ℕ} (hn : 1 ≤ n)
    {α ell K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hK : 0 ≤ K) (z : Space n) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
        (b : Space n → Space n) (c : Space n → ℝ) (s : Set (Space n)),
        ball z (2*r) ⊆ s → UniformlyEllipticOn ell a (ball z (2*r)) →
        CoefficientsHolderOn α a b c s → coefficientNormOn α a b c s ≤ K →
        ∀ u f : Space n → ℝ,
          IsC2HolderLocOn α u ⟨ball z (2*r), isOpen_ball⟩ →
          IsBoundedOn u s → IsHolderOn α f s →
          (∀ x ∈ ball z (2*r), nondivergenceOperator a b c u x = f x) →
          IsC2HolderOn α u (ball z r) ∧
          c2HolderNormOn α u (ball z r) ≤
            A * (supNormOn u s + holderNormOn α f s) := by
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.VariableLocal.interior_ball_estimate
    hn α hα hα1 ell K hell hK
  let B := 1 + r⁻¹ + (r^2)⁻¹ + (r^(2+α))⁻¹
  let E := 1 + r^2 + r^(2+α)
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨B * C * E, mul_pos (mul_pos hB hC) hE, ?_⟩
  intro a b c s hsub he hc hcK u f hu hub hf heq
  have ha' := fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.1 i j) hsub
  have hb' := fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hc.2.1 i) hsub
  have hc' := P201.Elliptic.PoissonSchauder.isHolderOn_mono hc.2.2 hsub
  have hK' := P201.Elliptic.VariableLocal.coefficient_norm_restrict hc hcK hsub
  obtain ⟨hclass, hnorm⟩ := hest a b c z r hr hr1 he.1 he.2 ha' hb' hc' hK' u f hu
    (P201.Elliptic.PoissonSchauder.boundedOn_mono hub hsub)
    (P201.Elliptic.PoissonSchauder.isHolderOn_mono hf hsub) heq
  refine ⟨hclass, ?_⟩
  calc
    c2HolderNormOn α u (ball z r) ≤ B * scaledSolutionNorm α r u (ball z r) :=
      c2HolderNormOn_le_scaled hr
    _ ≤ B * (C * scaledDataNorm α r u f (ball z (2*r))) :=
      mul_le_mul_of_nonneg_left hnorm hB.le
    _ ≤ B * (C * (E * (supNormOn u s + holderNormOn α f s))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (scaledDataNorm_le_outer_norm hr.le hub hf hsub) hC.le) hB.le
    _ = _ := by ring


/-- Compact patching of the local variable-coefficient ball estimates proves
    the nested interior estimate with a constant chosen before the fields. -/
theorem interior_estimate : P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement := by
  classical
  intro n hn α hα hα1 Ω Ω' Ω'' hbounded hcontained hΩ ell K hell hK
  let s := closure (Ω' : Set (Space n))
  have hs : IsCompact s :=
    isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  have hballs : ∀ x : s, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ball (x : Space n) (2*r) ⊆ (Ω'' : Set (Space n)) := by
    intro x
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp Ω''.isOpen x (hcontained x.property)
    refine ⟨min (δ/4) 1, lt_min (by positivity) zero_lt_one, min_le_right _ _, ?_⟩
    apply Subset.trans (ball_subset_ball ?_) hδΩ
    have hmin := min_le_left (δ/4) (1 : ℝ)
    linarith
  choose r hr hr1 hrΩ using hballs
  choose A hA hest using fun x : s =>
    interior_ball_unscaled_estimate hn hα hα1 hell hK (x : Space n) (r x) (hr x) (hr1 x)
  have hcover : s ⊆ ⋃ x : s, ball (x : Space n) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover _ (fun x => isOpen_ball) hcover
  let U : t → Set (Space n) := fun i => ball (i.val : Space n) (r i.val)
  have hcover' : s ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩, hxi⟩
  obtain ⟨C, hC, hpatch⟩ := finite_cover_c2Holder_estimate hα.le hs U
    (fun i => isOpen_ball) hcover' (fun i => A i.val) (fun i => (hA i.val).le)
  refine ⟨C, hC, ?_⟩
  intro a b c he _ hc hcK u f hu _ heq hub hf
  let D := supNormOn u (Ω'' : Set (Space n)) + holderNormOn α f (Ω'' : Set (Space n))
  have hD : 0 ≤ D := add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
    (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _))
  have hlocal : ∀ i : t, IsC2HolderOn α u (s ∩ U i) ∧
      c2HolderNormOn α u (s ∩ U i) ≤ A i.val * D := by
    intro i
    have hsub := hrΩ i.val
    have he' : UniformlyEllipticOn ell a (ball (i.val : Space n) (2*r i.val)) :=
      ⟨fun x hx => he.1 x (hΩ (hsub hx)), fun x hx => he.2 x (hΩ (hsub hx))⟩
    have hu' : IsC2HolderLocOn α u
        ⟨ball (i.val : Space n) (2*r i.val), isOpen_ball⟩ :=
      isC2HolderLocOn_mono hu (fun x hx => hΩ (hsub hx))
    obtain ⟨hclass, hnorm⟩ := hest i.val a b c Ω'' hsub he' hc hcK u f hu' hub hf
      (fun x hx => heq x (hΩ (hsub hx)))
    exact ⟨P201.Elliptic.PoissonSchauder.c2HolderOn_mono hclass inter_subset_right,
      (P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hclass inter_subset_right).trans hnorm⟩
  obtain ⟨hclass, hnorm⟩ := hpatch u D hD
    (hu.1.mono (fun x hx => hΩ (hcontained hx))) hlocal
  exact ⟨P201.Elliptic.PoissonSchauder.c2HolderOn_mono hclass subset_closure,
    (P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hclass subset_closure).trans hnorm⟩


theorem global_estimate_of_local
    (hlocal : LocalBoundaryEstimateStatement) : GlobalEstimateStatement := by
  intro m α hα hα1 Ω hbounded hboundary
  let U : Domain (m + 1) := ⟨univ, isOpen_univ⟩
  obtain ⟨R, hR⟩ := hbounded.closure.subset_ball (0 : Space (m + 1))
  let V : Domain (m + 1) := ⟨ball 0 R, isOpen_ball⟩
  have hVbounded : Bornology.IsBounded (V : Set (Space (m + 1))) := isBounded_ball
  have hVU : closure (V : Set (Space (m + 1))) ⊆ (U : Set (Space (m + 1))) := subset_univ _
  have hboundaryU : HasC2HolderBoundaryOn α Ω (U : Set (Space (m + 1))) := hboundary
  have hOuter : closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))) =
      closure (Ω : Set (Space (m + 1))) := inter_univ _
  have hInner : closure (Ω : Set (Space (m + 1))) ∩ (V : Set (Space (m + 1))) =
      closure (Ω : Set (Space (m + 1))) := inter_eq_left.mpr hR
  intro ell K hell hK
  obtain ⟨C, hC, hestimate⟩ :=
    hlocal m α hα hα1 Ω U hboundaryU V hVbounded hVU ell K hell hK
  refine ⟨C, hC, ?_⟩
  intro a b c ha hcoeff hKcoeff u f G hu hf hG heq htrace
  have huloc : IsC2HolderLocUpToOn α u Ω U := by
    refine ⟨?_, ?_⟩
    · simpa only [hOuter] using hu.1
    · intro x hx
      refine ⟨1, zero_lt_one, subset_univ _, ?_⟩
      exact c2HolderUpToOn_inter_open isOpen_ball hu
  have hresult := hestimate a b c
    (by simpa only [hOuter] using ha)
    (by simpa only [hOuter] using hcoeff)
    (by simpa only [hOuter] using hKcoeff) u f G huloc
    (by simpa only [hOuter] using hu.2.1)
    (by simpa only [hOuter] using hf)
    (by simpa only [hOuter] using hG)
    (by intro x hx; exact heq x hx.1)
    (by intro x hx; exact htrace x hx.1)
  simpa only [hInner, hOuter] using hresult.2

lemma local_upTo_interior_ball {n : ℕ} {α R : ℝ} {u : Space n → ℝ}
    {Ω U : Domain n} {z : Space n}
    (hu : IsC2HolderLocUpToOn α u Ω U)
    (hB : ball z R ⊆ (Ω : Set (Space n)) ∩ (U : Set (Space n))) :
    IsC2HolderLocOn α u ⟨ball z R, isOpen_ball⟩ := by
  refine ⟨hu.1.mono (fun x hx => ⟨subset_closure (hB hx).1, (hB hx).2⟩), ?_⟩
  intro x hx
  obtain ⟨δ, hδ, _, hreg⟩ := hu.2 x ⟨subset_closure (hB hx).1, (hB hx).2⟩
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hrδ : ball x r ⊆ ball x δ := ball_subset_ball (min_le_left _ _)
  have hrB : ball x r ⊆ ball z R := (ball_subset_ball (min_le_right _ _)).trans hεB
  have he : (closure (Ω : Set (Space n)) ∩ ball x δ) ∩ ball x r = ball x r := by
    apply inter_eq_right.mpr
    intro y hy
    exact ⟨subset_closure (hB (hrB hy)).1, hrδ hy⟩
  have hup := c2HolderUpToOn_inter_open (U := ball x r) isOpen_ball hreg
  rw [he] at hup
  have hord := (P201.Elliptic.VariableLocal.ordinary_ball_of_within hup).1
  exact ⟨r, hr, hrB, hord.2.2.2⟩

lemma local_upTo_on_boundary_ball {n : ℕ} {α R : ℝ} {u : Space n → ℝ}
    {Ω U : Domain n} {z : Space n}
    (hu : IsC2HolderLocUpToOn α u Ω U)
    (hB : ball z R ⊆ (U : Set (Space n))) :
    ContDiffOn ℝ 2 u (closure (Ω : Set (Space n)) ∩ ball z R) ∧
      ∀ x ∈ closure (Ω : Set (Space n)) ∩ ball z R,
        ∃ δ : ℝ, 0 < δ ∧ IsC2HolderUpToOn α u
          ((closure (Ω : Set (Space n)) ∩ ball z R) ∩ ball x δ) := by
  refine ⟨hu.1.mono (fun x hx => ⟨hx.1, hB hx.2⟩), ?_⟩
  intro x hx
  obtain ⟨δ, hδ, _, hreg⟩ := hu.2 x ⟨hx.1, hB hx.2⟩
  refine ⟨δ, hδ, ?_⟩
  have hh := c2HolderUpToOn_inter_open (U := ball z R) isOpen_ball hreg
  simpa only [inter_assoc, inter_comm (ball x δ) (ball z R)] using hh


lemma boundary_portion_point_patch
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (Ω U : Domain (m + 1)) (hboundary : HasC2HolderBoundaryOn α Ω U)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (p : Space (m + 1))
    (hp : p ∈ closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) :
    ∃ ρ A : ℝ, 0 < ρ ∧ 0 < A ∧
      ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ),
        UniformlyEllipticOn ell a
          (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
        CoefficientsHolderOn α a b c
          (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
        coefficientNormOn α a b c
          (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) ≤ K →
        ∀ u f G : Space (m + 1) → ℝ,
          IsC2HolderLocUpToOn α u Ω U →
          IsBoundedOn u (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
          IsHolderOn α f (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
          IsC2HolderUpToOn α G (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) →
          (∀ x ∈ (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))),
            nondivergenceOperator a b c u x = f x) →
          (∀ x ∈ frontier (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))),
            u x = G x) →
          IsC2HolderUpToOn α u
            ((closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) ∩ ball p ρ) ∧
          c2HolderUpToNormOn α u
            ((closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) ∩ ball p ρ) ≤
            A * (supNormOn u (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) +
              holderNormOn α f (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))) +
              c2HolderUpToNormOn α G (closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))))) := by
  let s : Set (Space (m + 1)) := closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))
  by_cases hpf : p ∈ frontier (Ω : Set (Space (m + 1)))
  · obtain ⟨chart, hchartp, hgraph⟩ := hboundary p hpf hp.2
    have hchart := P201.Elliptic.ChartSchauder.local_estimate m α hα hα1 Ω chart hgraph
    dsimp only at hchart
    rw [hchartp] at hchart
    obtain ⟨ρ, R, hρ, hρR, hR1, hRU, _, hchart⟩ := hchart U U.isOpen hp.2
    obtain ⟨A, hA, hest⟩ := hchart ell K hell hK
    have hρU : ball p ρ ⊆ (U : Set (Space (m + 1))) :=
      (ball_subset_ball (by linarith : ρ ≤ R)).trans hRU
    have hsetR : s ∩ ball p R = closure (Ω : Set (Space (m + 1))) ∩ ball p R := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hRU hx.2⟩, hx.2⟩⟩
    have hsetρ : s ∩ ball p ρ = closure (Ω : Set (Space (m + 1))) ∩ ball p ρ := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hρU hx.2⟩, hx.2⟩⟩
    have hsub : closure (Ω : Set (Space (m + 1))) ∩ ball p R ⊆ s :=
      fun x hx => ⟨hx.1, hRU hx.2⟩
    refine ⟨ρ, A, hρ, hA, ?_⟩
    intro a b c hellip hcoeff hnorm u f G hu hub hf hG heq htrace
    have hcoeffR : CoefficientsHolderOn α a b c
        (closure (Ω : Set (Space (m + 1))) ∩ ball p R) :=
      ⟨fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.1 i j) hsub,
        fun i => P201.Elliptic.PoissonSchauder.isHolderOn_mono (hcoeff.2.1 i) hsub,
        P201.Elliptic.PoissonSchauder.isHolderOn_mono hcoeff.2.2 hsub⟩
    have hloc := local_upTo_on_boundary_ball hu hRU
    have hGR := c2HolderUpToOn_inter_open (U := ball p R) isOpen_ball hG
    have hGnorm := scaledWithinSolutionNorm_inter_open_le (r := 1) zero_le_one
      (U := ball p R) isOpen_ball hG
    change IsC2HolderUpToOn α G (s ∩ ball p R) at hGR
    change scaledWithinSolutionNorm α 1 G (s ∩ ball p R) ≤ _ at hGnorm
    rw [hsetR] at hGR hGnorm
    have hresult := hest a b c
      (fun x hx => hellip.1 x (hsub hx)) (fun x hx => hellip.2 x (hsub hx))
      hcoeffR.1 hcoeffR.2.1 hcoeffR.2.2
      (P201.Elliptic.VariableLocal.coefficient_norm_restrict hcoeff hnorm hsub)
      u f G hloc.1 hloc.2
      (P201.Elliptic.PoissonSchauder.boundedOn_mono hub hsub)
      (P201.Elliptic.PoissonSchauder.isHolderOn_mono hf hsub) hGR
      (fun x hx => heq x ⟨hx.1, hRU hx.2⟩)
      (fun x hx => htrace x ⟨hx.1, hRU hx.2⟩)
    change IsC2HolderUpToOn α u (s ∩ ball p ρ) ∧
      c2HolderUpToNormOn α u (s ∩ ball p ρ) ≤ _
    rw [hsetρ]
    refine ⟨hresult.1, hresult.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left ?_ hA.le
    exact add_le_add (add_le_add
      (P201.Elliptic.PoissonSchauder.supNormOn_mono hub hsub)
      (P201.Elliptic.PoissonSchauder.holderNormOn_mono hf hsub)) hGnorm
  · have hpΩ : p ∈ (Ω : Set (Space (m + 1))) := by
      have hmem : p ∈ closure (Ω : Set (Space (m + 1))) \ frontier (Ω : Set (Space (m + 1))) :=
        ⟨hp.1, hpf⟩
      rwa [closure_sdiff_frontier, Ω.isOpen.interior_eq] at hmem
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (Ω.isOpen.inter U.isOpen) p ⟨hpΩ, hp.2⟩
    let r := min (δ / 4) 1
    have hr : 0 < r := lt_min (by positivity) zero_lt_one
    have hr1 : r ≤ 1 := min_le_right _ _
    have hB : ball p (2 * r) ⊆ (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1))) := by
      apply Subset.trans (ball_subset_ball ?_) hδsub
      have hmin := min_le_left (δ/4) (1 : ℝ)
      change 2 * min (δ/4) 1 ≤ δ
      linarith
    have hinner : ball p r ⊆ ball p (2 * r) := ball_subset_ball (by linarith)
    have hsub : ball p (2 * r) ⊆ s :=
      fun x hx => ⟨subset_closure (hB hx).1, (hB hx).2⟩
    have hset : s ∩ ball p r = ball p r :=
      inter_eq_right.mpr (hinner.trans hsub)
    obtain ⟨A, hA, hest⟩ := interior_ball_unscaled_estimate (by omega : 1 ≤ m + 1)
      hα hα1 hell hK p r hr hr1
    refine ⟨r, A, hr, hA, ?_⟩
    intro a b c hellip hcoeff hnorm u f G hu hub hf hG heq htrace
    have hresult := hest a b c s hsub
      ⟨fun x hx => hellip.1 x (hsub hx), fun x hx => hellip.2 x (hsub hx)⟩
      hcoeff hnorm u f (local_upTo_interior_ball hu hB) hub hf
      (fun x hx => heq x (hB hx))
    have hwithin := P201.Elliptic.ConstantSchauder.within_estimate_of_extension
      (⟨ball p r, isOpen_ball⟩ : Domain (m + 1)) isOpen_ball.uniqueDiffOn
      (Subset.rfl : ball p r ⊆ ball p r) (r := 1) hresult.1.1 hresult.1 (fun _ _ => rfl)
    have hnorm1 : scaledSolutionNorm α 1 u (ball p r) = c2HolderNormOn α u (ball p r) := by
      rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
      simp only [scaledSolutionNorm, one_mul, one_pow, Real.one_rpow]
    change IsC2HolderUpToOn α u (s ∩ ball p r) ∧
      c2HolderUpToNormOn α u (s ∩ ball p r) ≤ _
    rw [hset]
    refine ⟨hwithin.1, ?_⟩
    change scaledWithinSolutionNorm α 1 u (ball p r) ≤ _
    rw [hwithin.2, hnorm1]
    exact hresult.2.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right
        (P201.Elliptic.ChartSchauder.scaledWithinSolutionNorm_nonneg α zero_le_one G s)) hA.le)


/-- Quantitative local estimates up to a regular boundary portion are patched
using jets on the outer portion and a finite cover of the compact inner closure. -/
theorem local_boundary_estimate : LocalBoundaryEstimateStatement := by
  classical
  intro m α hα hα1 Ω U hboundary V hbounded hcontained ell K hell hK
  let s := closure (Ω : Set (Space (m + 1))) ∩ (U : Set (Space (m + 1)))
  let k := closure (Ω : Set (Space (m + 1))) ∩ closure (V : Set (Space (m + 1)))
  have hcompact : IsCompact k :=
    (isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure).inter_left isClosed_closure
  have hks : k ⊆ s := fun x hx => ⟨hx.1, hcontained hx.2⟩
  have htk : s ∩ (V : Set (Space (m + 1))) ⊆ k :=
    fun x hx => ⟨hx.1.1, subset_closure hx.2⟩
  have htarget : s ∩ (V : Set (Space (m + 1))) =
      closure (Ω : Set (Space (m + 1))) ∩ (V : Set (Space (m + 1))) := by
    ext x
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, hcontained (subset_closure h.2)⟩, h.2⟩⟩
  choose ρ A hρ hA hest using fun p : k =>
    boundary_portion_point_patch m α hα hα1 Ω U hboundary ell K hell hK
      (p : Space (m + 1)) (hks p.property)
  have hcover : k ⊆ ⋃ p : k, ball (p : Space (m + 1)) (ρ p) := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hρ ⟨p, hp⟩)⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover _ (fun _ => isOpen_ball) hcover
  let W : t → Set (Space (m + 1)) := fun i => ball (i.val : Space (m + 1)) (ρ i.val)
  have hcover' : k ⊆ ⋃ i : t, W i := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨C, hC, hpatch⟩ := finite_cover_c2HolderUpTo_estimate_on hα.le hcompact hks
    V htk W (fun _ => isOpen_ball) hcover' (fun i => A i.val) (fun i => (hA i.val).le)
  refine ⟨C, hC, ?_⟩
  intro a b c he hc hcK u f G hu hub hf hG heq htrace
  let D := supNormOn u s + holderNormOn α f s + c2HolderUpToNormOn α G s
  have hD : 0 ≤ D := add_nonneg
    (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
        (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)))
    (P201.Elliptic.ChartSchauder.scaledWithinSolutionNorm_nonneg α zero_le_one G s)
  have hlocal : ∀ i : t, IsC2HolderUpToOn α u (s ∩ W i) ∧
      c2HolderUpToNormOn α u (s ∩ W i) ≤ A i.val * D := by
    intro i
    exact hest i.val a b c he hc hcK u f G hu hub hf hG heq htrace
  have hresult := hpatch u D hD hu.1 hlocal
  simpa only [htarget] using hresult

/-- The estimate on the whole bounded closure is a specialization of the
local boundary-portion estimate, taking the outer portion to be all space. -/
theorem global_estimate : GlobalEstimateStatement :=
  global_estimate_of_local local_boundary_estimate


end P201.Elliptic.VariableSchauder
