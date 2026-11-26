import Specs.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Affine.LieBracket
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Filter Topology NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart

noncomputable section

set_option maxHeartbeats 1000000

namespace LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

universe u

section Units

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

@[simp] lemma expUnit_val (x : A) : (expUnit x).val = exp x :=
  IsUnit.unit_spec _

private lemma exp_add_commuting {x y : A} (h : Commute x y) :
    exp (x + y) = exp x * exp y := by
  apply exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h <;>
    rw [expSeries_radius_eq_top] <;> exact edist_lt_top _ _

@[simp] lemma expUnit_zero : expUnit (0 : A) = 1 := by
  apply Units.ext
  simp

@[simp] lemma expUnit_neg (x : A) : expUnit (-x) = (expUnit x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  change (expUnit (-x)).val * (expUnit x).val = 1
  rw [expUnit_val, expUnit_val, ← exp_add_commuting ((Commute.refl x).neg_left)]
  simp

lemma expUnit_nsmul (n : ℕ) (x : A) : expUnit (n • x) = expUnit x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, pow_succ, ← ih]
    apply Units.ext
    change (expUnit (n • x + x)).val = (expUnit (n • x)).val * (expUnit x).val
    simpa only [expUnit_val] using exp_add_commuting ((Commute.refl x).smul_left n)

lemma expUnit_zsmul (n : ℤ) (x : A) : expUnit (n • x) = expUnit x ^ n := by
  cases n with
  | ofNat n => simpa using expUnit_nsmul n x
  | negSucc n => rw [negSucc_zsmul, expUnit_neg, expUnit_nsmul, zpow_negSucc]

lemma continuous_expUnit : Continuous (expUnit : A → Aˣ) := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  exact (continuous_iff_continuousAt.mpr fun x => by
    simpa only [Function.comp_def, expUnit_val] using
      (exp_analytic (𝕂 := ℝ) x).continuousAt)

lemma conjugation_derivative (x y : A) :
    HasDerivAt (fun t : ℝ => conjugate (expUnit (t • x)) y) (x * y - y * x) 0 := by
  have hx : HasDerivAt (fun t : ℝ => exp (t • x)) x 0 := by
    simpa using hasDerivAt_exp_smul_const x (0 : ℝ)
  have hn : HasDerivAt (fun t : ℝ => exp (t • -x)) (-x) 0 := by
    simpa using hasDerivAt_exp_smul_const (-x) (0 : ℝ)
  have h := (hx.mul_const y).mul hn
  have h' : HasDerivAt ((fun t : ℝ => exp (t • x) * y) * fun t : ℝ => exp (t • -x))
      (x * y - y * x) 0 := by
    simpa [sub_eq_add_neg, add_comm] using h
  apply h'.congr_of_eventuallyEq
  exact Eventually.of_forall fun t => by
    simp [conjugate, ← expUnit_neg, smul_neg, Pi.mul_apply]

lemma conjugate_mem_exponentialLines {H : Subgroup Aˣ} {g : Aˣ} (hg : g ∈ H)
    {x : A} (hx : x ∈ exponentialLines H) : conjugate g x ∈ exponentialLines H := by
  intro t
  have e : expUnit (t • conjugate g x) = g * expUnit (t • x) * g⁻¹ := by
    apply Units.ext
    simp only [conjugate, expUnit_val, Units.val_mul]
    have hr : t • ((g : A) * x * (↑g⁻¹ : A)) = (g : A) * (t • x) * (↑g⁻¹ : A) := by
      calc
        _ = t • ((g : A) * x) * (↑g⁻¹ : A) := by rw [smul_mul_assoc]
        _ = _ := by rw [mul_smul_comm]
    rw [hr]
    symm
    apply map_exp_of_mem_ball (𝕂 := ℝ)
      (MulSemiringAction.toRingHom (ConjAct Aˣ) A (ConjAct.toConjAct g))
      (continuous_const_smul (ConjAct.toConjAct g))
    rw [expSeries_radius_eq_top]
    exact edist_lt_top _ _
  rw [e]
  exact H.mul_mem (H.mul_mem hg (hx t)) (H.inv_mem hg)

private def expDerivative : A ≃L[ℝ] A := ContinuousLinearEquiv.refl ℝ A

private lemma strictDerivExp :
    HasStrictFDerivAt (exp : A → A) (expDerivative (A := A)).toContinuousLinearMap 0 :=
  hasStrictFDerivAt_exp_zero

private def localLog : A → A :=
  (strictDerivExp (A := A)).localInverse exp expDerivative 0

private lemma log_one : localLog (1 : A) = 0 := by
  simpa [localLog] using (strictDerivExp (A := A)).localInverse_apply_image

private lemma exp_log_eventually : ∀ᶠ g : A in 𝓝 1, exp (localLog g) = g := by
  simpa [localLog] using (strictDerivExp (A := A)).eventually_right_inverse

private lemma deriv_log :
    HasFDerivAt (localLog : A → A) (ContinuousLinearMap.id ℝ A) 1 := by
  simpa [localLog, expDerivative] using (strictDerivExp (A := A)).to_localInverse.hasFDerivAt

/-- A differentiable curve through the identity in a closed subgroup integrates
its velocity to a one-parameter subgroup. -/
lemma exponentialLine_of_curve {H : Subgroup Aˣ} (hH : IsClosed (H : Set Aˣ))
    {f : ℝ → A} {v : A} (h1 : f 0 = 1) (hf : HasDerivAt f v 0)
    (hm : ∀ᶠ t in 𝓝 0, f t ∈ Units.val '' (H : Set Aˣ)) :
    v ∈ exponentialLines H := by
  intro t
  by_cases ht : t = 0
  · simp [ht]
  let r (n : ℕ) : ℝ := t * (1 / ((n : ℝ) + 1))
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
  have hr' : Tendsto r atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hr, Eventually.of_forall fun n => ?_⟩
    change r n ≠ 0
    exact mul_ne_zero ht (one_div_ne_zero (by positivity))
  have hd : HasDerivAt (fun u => localLog (f u)) v 0 := by
    have h := (h1.symm ▸ (deriv_log (A := A))).comp_hasDerivAt 0 hf
    simpa only [Function.comp_def, ContinuousLinearMap.id_apply] using h
  have hlim : Tendsto (fun n : ℕ => (n + 1) • localLog (f (r n))) atTop (𝓝 (t • v)) := by
    have h := hd.tendsto_slope_zero.comp hr'
    have hh := tendsto_const_nhds.smul h (c := t)
    convert hh using 1
    ext n
    change (n + 1) • localLog (f (r n)) =
      t • ((r n)⁻¹ • (localLog (f (0 + r n)) - localLog (f 0)))
    rw [zero_add, h1, log_one, sub_zero, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    congr 1
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    dsimp [r]
    field_simp
  refine hH.mem_of_tendsto ((continuous_expUnit.tendsto _).comp hlim) ?_
  have hf1 : Tendsto f (𝓝 0) (𝓝 1) := h1 ▸ hf.continuousAt
  filter_upwards [hr.eventually hm, hr.eventually (hf1.eventually exp_log_eventually)] with n hn he
  obtain ⟨g, hg, hfg⟩ := hn
  have hlog : expUnit (localLog (f (r n))) = g := Units.ext (by simpa only [expUnit_val, he] using hfg.symm)
  change expUnit ((n + 1) • localLog (f (r n))) ∈ H
  rw [expUnit_nsmul, hlog]
  exact H.pow_mem hg _

/-- Exponential lines of a closed subgroup are closed under real linear combinations. -/
def exponentialLineSubmodule (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) :
    Submodule ℝ A where
  carrier := exponentialLines H
  zero_mem' := by intro t; simp
  smul_mem' a x hx := by
    intro t
    rw [smul_smul]
    exact hx (t * a)
  add_mem' {x y} hx hy := by
    have dx : HasDerivAt (fun t : ℝ => exp (t • x)) x 0 := by
      simpa using hasDerivAt_exp_smul_const x (0 : ℝ)
    have dy : HasDerivAt (fun t : ℝ => exp (t • y)) y 0 := by
      simpa using hasDerivAt_exp_smul_const y (0 : ℝ)
    refine exponentialLine_of_curve hH
      (f := fun t : ℝ => exp (t • x) * exp (t • y)) (by simp) ?_ ?_
    · simpa [add_comm, Pi.mul_def] using dx.mul dy
    · exact Eventually.of_forall fun t =>
        ⟨expUnit (t • x) * expUnit (t • y), H.mul_mem (hx t) (hy t), by simp⟩

private lemma limit_exponentialLine {H : Subgroup Aˣ} (hH : IsClosed (H : Set Aˣ))
    (x : ℕ → A) (u : A)
    (hx : ∀ n, expUnit (x n) ∈ H) (hne : ∀ n, x n ≠ 0)
    (h0 : Tendsto x atTop (𝓝 0))
    (hu : Tendsto (fun n => ‖x n‖⁻¹ • x n) atTop (𝓝 u)) :
    u ∈ exponentialLines H := by
  intro t
  let r (n : ℕ) := ‖x n‖
  let k (n : ℕ) : ℤ := ⌊t / r n⌋
  have hpos (n : ℕ) : 0 < r n := norm_pos_iff.mpr (hne n)
  have hr : Tendsto r atTop (𝓝 0) := by simpa [r] using h0.norm
  have he (n : ℕ) : 0 ≤ t - (k n : ℝ) * r n := by
    exact sub_nonneg.mpr <| (le_div_iff₀ (hpos n)).mp (Int.floor_le _)
  have he' (n : ℕ) : t - (k n : ℝ) * r n ≤ r n :=
    (Int.sub_floor_div_mul_lt t (hpos n)).le
  have herror : Tendsto (fun n => t - (k n : ℝ) * r n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr he he'
  have hk : Tendsto (fun n => (k n : ℝ) * r n) atTop (𝓝 t) := by
    simpa using herror.const_sub t
  have hl : Tendsto (fun n => k n • x n) atTop (𝓝 (t • u)) := by
    convert hk.smul hu using 1
    ext n
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    have hn : r n ≠ 0 := (hpos n).ne'
    change (k n : ℝ) • x n = ((k n : ℝ) * r n * (r n)⁻¹) • x n
    rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
  refine hH.mem_of_tendsto ((continuous_expUnit.tendsto _).comp hl) (Eventually.of_forall fun n => ?_)
  change expUnit (k n • x n) ∈ H
  rw [expUnit_zsmul]
  exact H.zpow_mem (hx n) _

variable [FiniteDimensional ℝ A]

/-- No transverse direction whose exponential is in the subgroup can approach zero. -/
private lemma no_transverse_exponential {H : Subgroup Aˣ} (hH : IsClosed (H : Set Aˣ))
    (M : Submodule ℝ A) (hM : Disjoint (exponentialLineSubmodule H hH) M) :
    ∀ᶠ y : M in 𝓝 0, expUnit (y : A) ∈ H → y = 0 := by
  by_contra he
  have hc : (0 : M) ∈ closure {y : M | expUnit (y : A) ∈ H ∧ y ≠ 0} := by
    rw [mem_closure_iff_frequently]
    simpa only [Filter.Frequently, Set.mem_ofPred_eq, not_and, Classical.not_not] using he
  obtain ⟨x, hx, h0⟩ := mem_closure_iff_seq_limit.mp hc
  let y (n : ℕ) : M := ‖x n‖⁻¹ • x n
  have hyn (n : ℕ) : ‖y n‖ = 1 := by
    rw [show y n = ‖x n‖⁻¹ • x n from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact (norm_pos_iff.mpr (hx n).2).ne'
  obtain ⟨v, hv, φ, hφ, hy⟩ := (isCompact_sphere (0 : M) 1).tendsto_subseq
    (x := y) (fun n => by simpa [Metric.mem_sphere, dist_zero_right] using hyn n)
  have hline : (v : A) ∈ exponentialLines H := by
    apply limit_exponentialLine hH (fun n => ((x (φ n)) : A)) (v : A)
    · exact fun n => (hx (φ n)).1
    · intro n hn
      exact (hx (φ n)).2 (Subtype.ext hn)
    · simpa [Function.comp_def] using (continuous_subtype_val.tendsto (0 : M)).comp (h0.comp hφ.tendsto_atTop)
    · simpa only [Function.comp_def, y, Submodule.coe_smul, Submodule.norm_coe] using
        (continuous_subtype_val.tendsto v).comp hy
  have hv0 : (v : A) = 0 := Submodule.disjoint_def.mp hM (v : A) hline v.property
  have hvn : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
  rw [show v = 0 from Subtype.ext hv0, norm_zero] at hvn
  exact zero_ne_one hvn

/-- The exponential gives an identity chart on the subgroup of units. -/
theorem closedSubgroupExponential : ClosedSubgroupExponential.{u} := by
  intro A _ _ _ _ H hH
  let W := exponentialLineSubmodule H hH
  obtain ⟨M, hM⟩ := W.exists_isCompl
  have htop := Submodule.IsCompl.isTopCompl_of_isClosed hM W.closed_of_finiteDimensional
    M.closed_of_finiteDimensional
  let L := W.prodEquivOfIsTopCompl M htop
  let f (p : W × M) := exp (p.1 : A) * exp (p.2 : A)
  have d₁ : HasStrictFDerivAt (fun p : W × M => exp (p.1 : A))
      (W.subtypeL.comp (ContinuousLinearMap.fst ℝ W M)) 0 := by
    simpa [expDerivative] using (strictDerivExp (A := A)).comp (0 : W × M)
      (W.subtypeL.comp (ContinuousLinearMap.fst ℝ W M)).hasStrictFDerivAt
  have d₂ : HasStrictFDerivAt (fun p : W × M => exp (p.2 : A))
      (M.subtypeL.comp (ContinuousLinearMap.snd ℝ W M)) 0 := by
    simpa [expDerivative] using (strictDerivExp (A := A)).comp (0 : W × M)
      (M.subtypeL.comp (ContinuousLinearMap.snd ℝ W M)).hasStrictFDerivAt
  have df : HasStrictFDerivAt f L.toContinuousLinearMap 0 := by
    have hl : L.toContinuousLinearMap =
        W.subtypeL.comp (ContinuousLinearMap.fst ℝ W M) +
        M.subtypeL.comp (ContinuousLinearMap.snd ℝ W M) := by
      apply ContinuousLinearMap.ext
      intro p
      exact Submodule.prodEquivOfIsTopCompl_apply htop p
    rw [hl]
    change HasStrictFDerivAt
      ((fun p : W × M => exp (p.1 : A)) * fun p : W × M => exp (p.2 : A)) _ 0
    simpa [add_comm] using d₁.mul' d₂
  have htrans := no_transverse_exponential hH M hM.disjoint
  obtain ⟨U, hU, hUopen, h0U⟩ := mem_nhds_iff.mp htrans
  let e₀ := df.toOpenPartialHomeomorph f
  let e := e₀.restrOpen (Prod.snd ⁻¹' U) (hUopen.preimage continuous_snd)
  have he0 : (0 : W × M) ∈ e.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨df.mem_toOpenPartialHomeomorph_source, h0U⟩
  have hf0 : e 0 = 1 := by change f 0 = 1; simp [f]
  have hfExp (p : W × M) : e p = (expUnit (p.1 : A)).val * (expUnit (p.2 : A)).val := by
    change f p = _
    simp [f]
  have hexp (x : W) : expUnit (x : A) ∈ H := by
    have hx : (x : A) ∈ exponentialLines H := x.property
    simpa using hx 1
  let chartFun (x : W) : H := ⟨expUnit (x : A), hexp x⟩
  let chartInv (g : H) : W := (e.symm (g.val : A)).1
  let source : Set W := (fun x : W => (x, (0 : M))) ⁻¹' e.source
  let target : Set H := (fun g : H => (g.val : A)) ⁻¹' e.target
  have hsource : IsOpen source := e.open_source.preimage (continuous_id.prodMk continuous_const)
  have htarget : IsOpen target :=
    e.open_target.preimage (Units.continuous_val.comp continuous_subtype_val)
  have hforward (x : W) : e (x, 0) = ((chartFun x).val : A) := by
    rw [hfExp, Submodule.coe_zero, expUnit_zero, Units.val_one, mul_one]
  have hinverse (g : H) (hg : g ∈ target) : (chartInv g, (0 : M)) = e.symm (g.val : A) := by
    let p := e.symm (g.val : A)
    have hp : p ∈ e.source := e.map_target hg
    have heq : expUnit (p.1 : A) * expUnit (p.2 : A) = g.val := Units.ext <|
      (hfExp p).symm.trans (e.right_inv hg)
    have hg' := g.property
    rw [← heq] at hg'
    have hyH : expUnit (p.2 : A) ∈ H := by
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using H.mul_mem (H.inv_mem (hexp p.1)) hg'
    have hpU : p.2 ∈ U := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hp
      exact hp.2
    exact Prod.ext rfl (hU hpU hyH).symm
  let chart : OpenPartialHomeomorph W H :=
    { toFun := chartFun
      invFun := chartInv
      source := source
      target := target
      map_source' := by
        intro x hx
        change (((chartFun x).val : A)) ∈ e.target
        rw [← hforward]
        exact e.map_source hx
      map_target' := by
        intro g hg
        change (chartInv g, (0 : M)) ∈ e.source
        rw [hinverse g hg]
        exact e.map_target hg
      left_inv' := by
        intro x hx
        change (e.symm ((chartFun x).val : A)).1 = x
        rw [← hforward, e.left_inv hx]
      right_inv' := by
        intro g hg
        apply Subtype.ext
        apply Units.ext
        rw [← hforward, hinverse g hg, e.right_inv hg]
      continuousOn_toFun := by
        apply IsInducing.subtypeVal.continuousOn_iff.mpr
        exact (continuous_expUnit.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := continuous_fst.comp_continuousOn
        (e.continuousOn_invFun.comp (Units.continuous_val.comp continuous_subtype_val).continuousOn
          (fun _ h => h))
      open_source := hsource
      open_target := htarget }
  have h0 : (0 : W) ∈ chart.source := by
    change ((0 : W), (0 : M)) ∈ e.source
    exact he0
  have hchart0 : chart 0 = 1 := Subtype.ext (by change expUnit (0 : A) = 1; simp)
  have hdchart :
      HasStrictFDerivAt (fun x => (chart x : Aˣ).val) W.subtypeL 0 := by
    change HasStrictFDerivAt (fun x : W => (expUnit (x : A)).val) W.subtypeL 0
    simpa [expDerivative, Function.comp_def] using
      (strictDerivExp (A := A)).comp (0 : W) W.subtypeL.hasStrictFDerivAt
  refine ⟨⟨W, fun _ => Iff.rfl, chart, h0, fun _ _ => rfl, hdchart,
    fun g x => conjugate_mem_exponentialLines g.property x.property, ?_, ?_, ?_⟩⟩
  · intro x y
    let c (t : ℝ) := conjugate (expUnit (t • (x : A))) (y : A)
    have hc (t : ℝ) : c t ∈ W := conjugate_mem_exponentialLines (x.property t) y.property
    have hd : HasDerivAt c ((x : A) * (y : A) - (y : A) * (x : A)) 0 :=
      conjugation_derivative (x : A) (y : A)
    exact W.closed_of_finiteDimensional.mem_of_tendsto hd.tendsto_slope_zero
      (Eventually.of_forall fun t => W.smul_mem _ (W.sub_mem (hc (0 + t)) (hc 0)))
  · intro hw
    rw [discreteTopology_iff_isOpen_singleton_one]
    have hs (x : W) : x = 0 := Subtype.ext <| by
      have hz := Eq.mp (congrArg (fun S : Submodule ℝ A => (x : A) ∈ S) hw) x.property
      exact hz
    convert chart.open_target using 1
    ext g
    constructor
    · rintro (rfl : g = 1)
      rw [← hchart0]
      exact chart.map_source h0
    · intro hg
      exact (chart.right_inv hg).symm.trans
        ((congrArg chart (hs (chart.symm g))).trans hchart0)
  · intro hw
    have hout : IsOpen e.target := e.open_target
    apply H.isOpen_of_mem_nhds (g := (1 : Aˣ))
    refine mem_of_superset (hout.preimage Units.continuous_val |>.mem_nhds ?_) ?_
    · change (1 : A) ∈ e.target
      rw [← hf0]
      exact e.map_source he0
    · intro z hz
      let p := e.symm (z : A)
      have hy : (p.2 : A) ∈ W :=
        Eq.mpr (congrArg (fun S : Submodule ℝ A => (p.2 : A) ∈ S) hw) Submodule.mem_top
      have hz' : expUnit (p.1 : A) * expUnit (p.2 : A) = z :=
        Units.ext ((hfExp p).symm.trans (e.right_inv hz))
      rw [← hz']
      exact H.mul_mem (hexp p.1) (hexp ⟨p.2, hy⟩)

end Units

section MatrixPolynomials

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs
open scoped Matrix.Norms.Operator

variable {F ι : Type u} [Field F] [Fintype ι] [DecidableEq ι]

private abbrev MatrixPolynomial (F ι : Type u) [CommRing F] :=
  MvPolynomial (ι × ι) F

private def evaluateMatrix {R : Type u} [CommRing R] [Algebra F R] (M : Matrix ι ι R) :
    MatrixPolynomial F ι →ₐ[F] R :=
  MvPolynomial.aeval (fun ij => M ij.1 ij.2)

omit [Fintype ι] [DecidableEq ι] in
private lemma evaluateMatrix_C {R : Type u} [CommRing R] [Algebra F R]
    (M : Matrix ι ι R) (c : F) :
    evaluateMatrix M (MvPolynomial.C c) = algebraMap F R c :=
  MvPolynomial.aeval_C _ _

omit [Fintype ι] [DecidableEq ι] in
private lemma evaluateMatrix_X {R : Type u} [CommRing R] [Algebra F R]
    (M : Matrix ι ι R) (i j : ι) :
    evaluateMatrix (F := F) M (MvPolynomial.X (i, j)) = M i j :=
  MvPolynomial.aeval_X _ _

private def dualMatrix {R : Type u} [CommRing R] (M V : Matrix ι ι R) :
    Matrix ι ι (DualNumber R) :=
  fun i j => (M i j, V i j)

/-- Differentiating after right multiplication with the infinitesimal
matrix with tangent X is again a polynomial in the matrix entries. -/
private def rightDerivative (X : Matrix ι ι F) (p : MatrixPolynomial F ι) :
    MatrixPolynomial F ι :=
  let M := Specs.StandardGroups.genericMatrix F ι
  let V := M * X.map MvPolynomial.C
  (evaluateMatrix (dualMatrix M V) p).snd

omit [Fintype ι] [DecidableEq ι] in
private lemma evaluateMatrix_dual_fst {R : Type u} [CommRing R] [Algebra F R]
    (M V : Matrix ι ι R) (p : MatrixPolynomial F ι) :
    (evaluateMatrix (dualMatrix M V) p).fst = evaluateMatrix M p := by
  have h : (TrivSqZeroExt.fstHom F R R).comp (evaluateMatrix (dualMatrix M V)) =
      evaluateMatrix M := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [AlgHom.comp_apply, evaluateMatrix_X, evaluateMatrix_X]
    rfl
  exact DFunLike.congr_fun h p

private lemma evaluate_rightDerivative {R : Type u} [CommRing R] [Algebra F R]
    (X : Matrix ι ι F) (M : Matrix ι ι R) (p : MatrixPolynomial F ι) :
    evaluateMatrix M (rightDerivative X p) =
      (evaluateMatrix (dualMatrix M (M * X.map (algebraMap F R))) p).snd := by
  let P := MatrixPolynomial F ι
  let e := evaluateMatrix (F := F) M
  let D : DualNumber P →ₐ[F] DualNumber R :=
    { toRingHom := InfinitesimalCommutator.mapCoefficients e.toRingHom
      commutes' := fun r => TrivSqZeroExt.ext (e.commutes r) (map_zero e) }
  let Q := Specs.StandardGroups.genericMatrix F ι
  have hQ : Q.map e = M := by
    ext i j
    exact evaluateMatrix_X (F := F) M i j
  have hX : (X.map MvPolynomial.C).map e = X.map (algebraMap F R) := by
    ext i j
    exact evaluateMatrix_C M (X i j)
  have hV : (Q * X.map MvPolynomial.C).map e = M * X.map (algebraMap F R) := by
    change e.mapMatrix (Q * X.map MvPolynomial.C) = _
    rw [map_mul]
    change Q.map e * (X.map MvPolynomial.C).map e = _
    rw [hQ, hX]
  have h : D.comp (evaluateMatrix (dualMatrix Q (Q * X.map MvPolynomial.C))) =
      evaluateMatrix (dualMatrix M (M * X.map (algebraMap F R))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [AlgHom.comp_apply, evaluateMatrix_X, evaluateMatrix_X]
    apply TrivSqZeroExt.ext
    · exact congrArg (fun N : Matrix ι ι R => N i j) hQ
    · exact congrArg (fun N : Matrix ι ι R => N i j) hV
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h p)

end MatrixPolynomials

section AnalyticPolynomials

open scoped Matrix.Norms.Operator

variable {F ι : Type u} [NormedField F] [NormedAlgebra ℝ F] [CompleteSpace F]
  [Fintype ι] [DecidableEq ι]

private def entryCLM (i j : ι) : Matrix ι ι F →L[ℝ] F :=
  { toLinearMap := {
      toFun := fun m => m i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    cont := (continuous_apply j).comp (continuous_apply i) }

omit [DecidableEq ι] [CompleteSpace F] in
private lemma hasDerivAt_evaluateMatrix
    {f : ℝ → Matrix ι ι F} {v : Matrix ι ι F} {t : ℝ} (hf : HasDerivAt f v t)
    (p : MatrixPolynomial F ι) :
    HasDerivAt (fun a => evaluateMatrix (f a) p)
      (evaluateMatrix (dualMatrix (f t) v) p).snd t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [evaluateMatrix_C]
    exact hasDerivAt_const t c
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add]
    exact hp.add hq
  | mul_X p n hp =>
    obtain ⟨i, j⟩ := n
    simp only [map_mul, evaluateMatrix_X]
    change HasDerivAt (fun a => evaluateMatrix (f a) p * f a i j)
      ((evaluateMatrix (dualMatrix (f t) v) p).fst * v i j +
        (evaluateMatrix (dualMatrix (f t) v) p).snd * f t i j) t
    rw [evaluateMatrix_dual_fst]
    have hv : HasDerivAt (fun a => f a i j) (v i j) t :=
      (entryCLM (F := F) i j).hasFDerivAt.comp_hasDerivAt t hf
    rw [add_comm]
    exact hp.mul hv

omit [DecidableEq ι] [CompleteSpace F] in
private lemma analytic_evaluateMatrix {f : ℝ → Matrix ι ι F} {t : ℝ}
    (hf : AnalyticAt ℝ f t) (p : MatrixPolynomial F ι) :
    AnalyticAt ℝ (fun a => evaluateMatrix (f a) p) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [evaluateMatrix_C]; exact analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p n hp =>
    obtain ⟨i, j⟩ := n
    simp only [map_mul, evaluateMatrix_X]
    exact hp.mul (((entryCLM (F := F) i j).analyticAt (f t)).comp hf)

/-- An ideal of matrix polynomial equations stable under the tangent
derivation vanishes along the exponential through the identity. -/
private lemma exponential_satisfies_equations
    (X : Matrix ι ι F) (P : MatrixPolynomial F ι → Prop)
    (at_one : ∀ p, P p → evaluateMatrix (1 : Matrix ι ι F) p = 0)
    (stable : ∀ p, P p → P (rightDerivative X p))
    (p : MatrixPolynomial F ι) (hp : P p) (t : ℝ) :
    evaluateMatrix (exp (t • X)) p = 0 := by
  let f (p : MatrixPolynomial F ι) (a : ℝ) := evaluateMatrix (exp (a • X)) p
  have han (q : MatrixPolynomial F ι) (a : ℝ) : AnalyticAt ℝ (f q) a := by
    apply analytic_evaluateMatrix (f := fun a : ℝ => exp (a • X))
    have h := (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) X).analyticAt
      a
    exact AnalyticAt.comp (f := fun a : ℝ => a • X)
      (@exp_analytic ℝ (Matrix ι ι F) _ _ _ _ _ (Matrix.instCompleteSpace ι ι F) (a • X)) h
  have hderiv (q : MatrixPolynomial F ι) : deriv (f q) = f (rightDerivative X q) := by
    ext a
    have hexp := @hasDerivAt_exp_smul_const ℝ (Matrix ι ι F) _ _ _
      (Matrix.instCompleteSpace ι ι F) X a
    have h := hasDerivAt_evaluateMatrix hexp q
    change deriv (f q) a = evaluateMatrix (exp (a • X)) (rightDerivative X q)
    rw [evaluate_rightDerivative]
    have hX : X.map (algebraMap F F) = X := by ext i j; simp
    rw [hX]
    exact h.deriv
  have hzero (n : ℕ) (q : MatrixPolynomial F ι) (hq : P q) : iteratedDeriv n (f q) 0 = 0 := by
    induction n generalizing q with
    | zero => simpa [f, iteratedDeriv_zero] using at_one q hq
    | succ n hn =>
      rw [iteratedDeriv_succ', hderiv]
      exact hn _ (stable _ hq)
  have ho : analyticOrderAt (f p) 0 = ⊤ := by
    by_contra hn
    obtain ⟨n, hn'⟩ := ENat.ne_top_iff_exists.mp hn
    have hne := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (han p 0)).mp hn'.symm
    exact hne.2 (hzero n p hp)
  have hz := AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (f := f p) 0 (han p) |>.mp ho
  exact congrFun hz t

end AnalyticPolynomials


open private matrixPresentation coordinateMap_of_map glEvaluation_algebraMap
  asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry isUnit_matrixEvaluation_det
  from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixDual matrixPointMap matrixDifferentialLinear matrixDual_kernel
  from LinearAlgebraicGroups.Affine.LieBracket


section SchemePoints

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open LinearAlgebraicGroups.Specs hiding coordinateMap
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open Specs.StandardGroups (GLCoordinates genericDeterminant)
open scoped Matrix.Norms.Operator


variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private abbrev MatrixIndex (i : MatrixRealization G) := Unipotent.Index.{u} i.size

private lemma asMatrix_map (i : MatrixRealization G) {R S : Type u}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (a : R →ₐ[F] S)
    (g : PointsIn i R) :
    asMatrix i S (((groupPointsFunctor F).obj G.val).map (CommAlgCat.ofHom a) g) =
      Matrix.GeneralLinearGroup.map a.toRingHom (asMatrix i R g) := by
  let α := ((groupPointsFunctor F).map i.embedding) ≫ i.matrix.hom
  exact congrArg (fun h => h g) (α.naturality (CommAlgCat.ofHom a))

private def MatrixEquation (i : MatrixRealization G) (p : MatrixPolynomial F (MatrixIndex i)) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra F R] (g : PointsIn i R),
    evaluateMatrix (asMatrix i R g).val p = 0

private lemma matrixRange_iff (i : MatrixRealization G)
    (R : Type u) [CommRing R] [Algebra F R]
    (M : Matrix.GeneralLinearGroup (MatrixIndex i) R) :
    M ∈ (asMatrix i R).range ↔ ∀ p, MatrixEquation i p → evaluateMatrix M.val p = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ p hp
    exact hp R g
  · intro hM
    obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
    obtain ⟨a, ha, hm⟩ := matrixPresentation B.unop e i
    have heval (N : Matrix.GeneralLinearGroup (MatrixIndex i) R)
        (p : MatrixPolynomial F (MatrixIndex i)) :
        glEvaluation N (algebraMap _ (GLCoordinates F (MatrixIndex i)) p) =
          evaluateMatrix N.val p := glEvaluation_algebraMap N p
    have hz (c : GLCoordinates F (MatrixIndex i))
        (hc : c ∈ RingHom.ker a.hom) : glEvaluation M c = 0 := by
      obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (genericDeterminant F (MatrixIndex i)) c
      have hp' : a.hom (algebraMap (MatrixPolynomial F (MatrixIndex i)) _ p) = 0 := by
        rw [← hp, map_mul, RingHom.mem_ker.mp hc, zero_mul]
      have hq : MatrixEquation i p := by
        intro S _ _ g
        have hh := glEvaluation_algebraMap (asMatrix i S g) p
        change glEvaluation (asMatrix i S g) (algebraMap _ (GLCoordinates F (MatrixIndex i)) p) =
          evaluateMatrix (asMatrix i S g).val p at hh
        rw [← hh]
        rw [hm S g]
        change (coordinateMap (k := F) (g ≫ e.inv)).hom
          (a.hom (algebraMap (MatrixPolynomial F (MatrixIndex i)) _ p)) = 0
        rw [hp', map_zero]
      have h := congrArg (glEvaluation M) hp
      rw [map_mul, map_pow, heval, heval, hM p hq] at h
      exact ((isUnit_matrixEvaluation_det M).pow n).mul_right_cancel (h.trans (zero_mul _).symm)
    let ea := Ideal.quotientKerAlgEquivOfSurjective ha
    let f := Ideal.Quotient.liftₐ (RingHom.ker a.hom) (glEvaluation M) hz
    let q := CommAlgCat.ofHom (f.comp ea.symm.toAlgHom)
    let g : PointsIn i R := (testSpec F).map q.op ≫ e.hom
    have hq : coordinateMap (k := F) (g ≫ e.inv) = q := by
      change coordinateMap (((testSpec F).map q.op ≫ e.hom) ≫ e.inv) = q
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map]
    refine ⟨g, ?_⟩
    have he : glEvaluation (asMatrix i R g) = glEvaluation (k := F) M := by
      rw [hm R g, hq]
      apply AlgHom.ext
      intro c
      change f (ea.symm (a.hom c)) = glEvaluation M c
      have hc : ea (Ideal.Quotient.mk (RingHom.ker a.hom) c) = a.hom c := rfl
      rw [← hc, AlgEquiv.symm_apply_apply]
      rfl
    apply Matrix.GeneralLinearGroup.ext
    intro j l
    simpa only [glEvaluation_entry] using congrArg
      (fun f : GLCoordinates F (MatrixIndex i) →ₐ[F] R =>
        f (Specs.StandardGroups.universalMatrix F _ j l)) he

private lemma matrixDual_injective {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι] :
    Function.Injective (matrixDual (R := R) (ι := ι)) := by
  intro M N h
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · exact congrArg (fun z : DualNumber (Matrix ι ι R) => z.fst i j) h
  · exact congrArg (fun z : DualNumber (Matrix ι ι R) => z.snd i j) h

private lemma dualMatrix_mul {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A B X Y : Matrix ι ι R) :
    dualMatrix A X * dualMatrix B Y = dualMatrix (A * B) (A * Y + X * B) := by
  apply matrixDual_injective
  rw [map_mul]
  rfl

private lemma dualMatrix_one {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι] :
    dualMatrix (1 : Matrix ι ι R) 0 = 1 := by
  apply matrixDual_injective
  rw [map_one]
  rfl

private def infinitesimalUnit {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι R) : Matrix.GeneralLinearGroup ι (DualNumber R) where
  val := dualMatrix 1 X
  inv := dualMatrix 1 (-X)
  val_inv := by rw [dualMatrix_mul]; simp [dualMatrix_one]
  inv_val := by rw [dualMatrix_mul]; simp [dualMatrix_one]

private abbrev tangentPoint (i : MatrixRealization G) (x : Lie F G.val) :
    PointsIn i (DualNumber F) := x.toMul.val

private lemma tangentMatrix_dual (i : MatrixRealization G) (x : Lie F G.val) :
    (asMatrix i (DualNumber F) (tangentPoint i x)).val = dualMatrix 1 (tangentMatrix i x) := by
  apply matrixDual_injective
  exact matrixDual_kernel (mapDualKernel (matrixPointMap i.embedding i.matrix) x)

private lemma rightDerivative_equation (i : MatrixRealization G)
    (x : Lie F G.val) {p : MatrixPolynomial F (MatrixIndex i)} (hp : MatrixEquation i p) :
    MatrixEquation i (rightDerivative (tangentMatrix i x) p) := by
  intro R _ _ g
  let M := (asMatrix i R g).val
  let c := AdjointRepresentation.constants (CommAlgCat.of F R)
  let d := AdjointRepresentation.dualMap (CommAlgCat.ofHom (Algebra.ofId F R))
  let f := (groupPointsFunctor F).obj G.val
  let a : PointsIn i (DualNumber R) := f.map c g
  let b : PointsIn i (DualNumber R) := f.map d (tangentPoint i x)
  have ha : (asMatrix i (DualNumber R) a).val = dualMatrix M 0 :=
    congrArg Units.val (asMatrix_map i c.hom g)
  have hb : (asMatrix i (DualNumber R) b).val =
      dualMatrix 1 ((tangentMatrix i x).map (algebraMap F R)) := by
    have h := congrArg Units.val (asMatrix_map i d.hom (tangentPoint i x))
    change (asMatrix i (DualNumber R) b).val =
      (asMatrix i (DualNumber F) (tangentPoint i x)).val.map d.hom at h
    rw [tangentMatrix_dual] at h
    rw [h]
    apply Matrix.ext
    intro j l
    apply TrivSqZeroExt.ext
    · change algebraMap F R ((1 : Matrix (MatrixIndex i) (MatrixIndex i) F) j l) =
        (1 : Matrix (MatrixIndex i) (MatrixIndex i) R) j l
      by_cases hj : j = l <;> simp [Matrix.one_apply, hj]
    · rfl
  have h := hp (DualNumber R) (a * b)
  simp only [map_mul, Units.val_mul, ha, hb, dualMatrix_mul, mul_one, add_zero] at h
  rw [evaluate_rightDerivative]
  exact congrArg TrivSqZeroExt.snd h

end SchemePoints

section SchemeTangent

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs hiding coordinateMap
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open scoped Matrix.Norms.Operator

variable {F : Type u} [NormedField F] [NormedAlgebra ℝ F] [CompleteSpace F]
  {G : AffineAlgebraicGroup F} (i : MatrixRealization G)

private lemma exponentialLines_matrix_iff (X : Matrix (MatrixIndex i) (MatrixIndex i) F) :
    X ∈ exponentialLines (asMatrix i F).range ↔
      ∃ x : Lie F G.val, tangentMatrix i x = X := by
  constructor
  · intro hX
    have hM : infinitesimalUnit X ∈ (asMatrix i (DualNumber F)).range := by
      apply (matrixRange_iff i _ _).2
      intro p hp
      change evaluateMatrix (dualMatrix 1 X) p = 0
      have h₀ : evaluateMatrix (1 : Matrix (MatrixIndex i) (MatrixIndex i) F) p = 0 := by
        simpa only [map_one, Units.val_one] using hp F 1
      have hzer (t : ℝ) : evaluateMatrix (exp (t • X)) p = 0 := by
        simpa only [expUnit_val] using (matrixRange_iff i F _).1 (hX t) p hp
      have h := hasDerivAt_evaluateMatrix
        (hasDerivAt_exp_smul_const X (0 : ℝ)) p
      simp only [zero_smul, exp_zero, one_mul] at h
      have h' : (fun t : ℝ => evaluateMatrix (exp (t • X)) p) = fun _ => 0 := funext hzer
      rw [h'] at h
      exact TrivSqZeroExt.ext
        ((evaluateMatrix_dual_fst 1 X p).trans h₀)
        (h.unique (hasDerivAt_const 0 (0 : F)))
    obtain ⟨g, hg⟩ := hM
    have hr : reduceTangentPoints G.val g = 1 := by
      apply (asMatrix_isClosedEmbedding i F).injective
      rw [map_one]
      change asMatrix i F (((groupPointsFunctor F).obj G.val).map
        (CommAlgCat.ofHom (TrivSqZeroExt.fstHom F F F)) g) = 1
      rw [asMatrix_map, hg]
      apply Units.ext
      rfl
    let x : Lie F G.val := Additive.ofMul ⟨g, hr⟩
    refine ⟨x, ?_⟩
    have he := congrArg (fun z : Matrix.GeneralLinearGroup (MatrixIndex i) (DualNumber F) =>
      (matrixDual z.val).snd) hg
    exact he
  · rintro ⟨x, rfl⟩ t
    apply (matrixRange_iff i F _).2
    intro p hp
    simpa only [expUnit_val] using
      exponential_satisfies_equations (tangentMatrix i x) (MatrixEquation i)
        (fun q hq => by simpa only [map_one, Units.val_one] using hq F 1)
        (fun _ hq => rightDerivative_equation i x hq) p hp t

omit [NormedAlgebra ℝ F] [CompleteSpace F] in
private lemma tangentMatrix_conjugate (g : PointsIn i F) (x : Lie F G.val) :
    ∃ y : Lie F G.val,
      y.toMul.val = AdjointRepresentation.conjugate (G := G.val)
        (R := CommAlgCat.of F F) g x ∧
      tangentMatrix i y = conjugate (asMatrix i F g) (tangentMatrix i x) := by
  let q : PointsIn i (DualNumber F) := AdjointRepresentation.conjugate (G := G.val) (R := CommAlgCat.of F F) g x
  let c := (TrivSqZeroExt.inlAlgHom F F F)
  let a : PointsIn i (DualNumber F) := ((groupPointsFunctor F).obj G.val).map (CommAlgCat.ofHom c) g
  have hq : q = a * tangentPoint i x * a⁻¹ := rfl
  have hx : reduceTangentPoints G.val x.toMul.val = 1 := x.toMul.property
  have hr : reduceTangentPoints G.val q = 1 := by
    rw [hq, map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  let y : Lie F G.val := Additive.ofMul ⟨q, hr⟩
  refine ⟨y, rfl, ?_⟩
  let M := asMatrix i F g
  have ha : (asMatrix i (DualNumber F) a).val = dualMatrix M.val 0 :=
    congrArg Units.val (asMatrix_map i c g)
  have ha' : (asMatrix i (DualNumber F) a⁻¹).val =
      dualMatrix (M⁻¹ : Matrix.GeneralLinearGroup (MatrixIndex i) F).val 0 := by
    change (asMatrix i (DualNumber F)
      ((((groupPointsFunctor F).obj G.val).map (CommAlgCat.ofHom c)).hom g)⁻¹).val = _
    rw [← map_inv]
    exact congrArg Units.val (asMatrix_map i c (g⁻¹))
  have he := tangentMatrix_dual i y
  change (asMatrix i (DualNumber F) q).val = dualMatrix 1 (tangentMatrix i y) at he
  rw [hq, map_mul, map_mul, Units.val_mul, Units.val_mul, ha,
    tangentMatrix_dual, ha', dualMatrix_mul, dualMatrix_mul] at he
  have hs := congrArg (fun z : Matrix (MatrixIndex i) (MatrixIndex i) (DualNumber F) =>
    (matrixDual z).snd) he
  simpa [dualMatrix, matrixDual, conjugate] using hs.symm

omit [NormedAlgebra ℝ F] [CompleteSpace F] in
private lemma tangentMatrix_linear_laws :
    (∀ x y : Lie F G.val, tangentMatrix i (x + y) = tangentMatrix i x + tangentMatrix i y) ∧
    (∀ (a : F) (x : Lie F G.val),
      tangentMatrix i (scalePointKernel G.val a x) = a • tangentMatrix i x) := by
  let : IsAffine G.val.X.left := G.property.1
  let d := matrixDifferentialLinear i.embedding i.matrix
  exact ⟨d.map_add, d.map_smul⟩

/-- Comparison with the intrinsic dual-number Lie algebra, including the
derivative of the actual scheme conjugation action. -/
theorem matrixTangentComparison : MatrixTangentComparison.{u} := by
  intro F _ _ _ _ G i s
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine i.ambient.val.X.left := i.ambient.property.1
  let : LieRing (Lie F G.val) := s.lieRing
  let : AddCommGroup (Lie F G.val) := s.lieRing.toAddCommGroup
  let : AddCommMonoid (Lie F G.val) := s.lieRing.toAddCommGroup.toAddCommMonoid
  let : LieAlgebra F (Lie F G.val) := s.lieAlgebra
  let : Module F (Lie F G.val) := s.lieAlgebra.toModule
  let : Module ℝ (Lie F G.val) := Module.restrictScalars ℝ F (Lie F G.val)
  have hh := identityLieBracketMatrix F G.val i.ambient.val (MatrixIndex i)
    i.embedding i.matrix i.closed
  obtain ⟨hadd, hsmul⟩ := tangentMatrix_linear_laws i
  let d₀ : Lie F G.val →ₗ[F] Matrix (MatrixIndex i) (MatrixIndex i) F :=
    { toFun := tangentMatrix i
      map_add' := fun x y => by
        have hs := congrArg (fun g : AddGroup (PointKernel G.val) => g.toAdd.add) s.group_law
        have he := congrFun (congrFun hs x) y
        exact (congrArg (tangentMatrix i) he).trans (hadd x y)
      map_smul' := fun a x => by
        have he := congrFun (congrFun s.scalar_law a) x
        exact (congrArg (tangentMatrix i) he).trans (hsmul a x) }
  let d : Lie F G.val →ₗ[ℝ] Matrix (MatrixIndex i) (MatrixIndex i) F :=
    { toFun := tangentMatrix i
      map_add' := d₀.map_add
      map_smul' := fun r x => by
        exact (d₀.map_smul (algebraMap ℝ F r) x).trans
          (IsScalarTower.algebraMap_smul F r (d₀ x)) }
  refine ⟨d, hh.1, fun _ => rfl, exponentialLines_matrix_iff i,
    tangentMatrix_conjugate i, ?_⟩
  intro x y
  have he : d ⁅x, y⁆ = d x * d y - d y * d x := hh.2 s x y
  rw [he]
  exact conjugation_derivative _ _

end SchemeTangent


section Products

set_option backward.isDefEq.respectTransparency false

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open scoped Matrix.Norms.Operator

/-- Taking the exponential commutes with each projection of a finite product. -/
theorem expUnit_apply {J : Type u} [Fintype J] {A : J → Type u}
    [∀ j, NormedRing (A j)] [∀ j, NormedAlgebra ℝ (A j)] [∀ j, CompleteSpace (A j)]
    (x : ∀ j, A j) (j : J) :
    ((expUnit x).val j) = (expUnit (x j)).val := by
  simp only [expUnit_val]
  apply map_exp_of_mem_ball (𝕂 := ℝ) (Pi.evalRingHom A j) (continuous_apply j)
  rw [expSeries_radius_eq_top]
  exact edist_lt_top _ _

private lemma piUnits_expUnit {J : Type u} [Fintype J] {A : J → Type u}
    [∀ j, NormedRing (A j)] [∀ j, NormedAlgebra ℝ (A j)] [∀ j, CompleteSpace (A j)]
    (x : ∀ j, A j) (j : J) :
    ContinuousMulEquiv.piUnits (expUnit x) j = expUnit (x j) :=
  Units.ext (expUnit_apply x j)

variable {J : Type u} [Fintype J] {F : J → Type u} [∀ j, NormedField (F j)]
  [∀ j, NormedAlgebra ℝ (F j)] [∀ j, CompleteSpace (F j)]
  {G : ∀ j, AffineAlgebraicGroup (F j)} (i : ∀ j, MatrixRealization (G j))

omit [Fintype J] [∀ j, NormedAlgebra ℝ (F j)] [∀ j, CompleteSpace (F j)] in
private lemma pointMatrices_closedEmbedding :
    IsClosedEmbedding (pointMatrices F G i) := by
  have h := IsClosedEmbedding.piMap fun j => asMatrix_isClosedEmbedding (i j) (F j)
  exact ContinuousMulEquiv.piUnits.symm.toHomeomorph.isClosedEmbedding.comp h

omit [Fintype J] [∀ j, NormedAlgebra ℝ (F j)] [∀ j, CompleteSpace (F j)] in
private lemma pointMatrices_range_iff (g : (MatrixProduct F G i)ˣ) :
    g ∈ (pointMatrices F G i).range ↔
      ∀ j, ContinuousMulEquiv.piUnits g j ∈ (asMatrix (i j) (F j)).range := by
  constructor
  · rintro ⟨p, rfl⟩ j
    exact ⟨p j, rfl⟩
  · intro h
    choose p hp using h
    refine ⟨p, ?_⟩
    apply ContinuousMulEquiv.piUnits.injective
    funext j
    exact hp j

private def subgroupImageHomeomorph {P B : Type u} [Group P] [Group B]
    [TopologicalSpace P] [TopologicalSpace B] (m : P →* B) (hm : IsEmbedding m)
    (H : Subgroup P) : H ≃ₜ H.map m := by
  let e := H.equivMapOfInjective m hm.injective
  apply e.toEquiv.toHomeomorphOfIsInducing
  apply (IsInducing.of_comp_iff (g := (Subtype.val : H.map m → B))
    IsInducing.subtypeVal).mp
  exact hm.isInducing.comp IsInducing.subtypeVal

private lemma isOpen_of_full_lines {P A : Type u} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (m : P →* Aˣ) (hm : IsEmbedding m) (H : Subgroup P)
    (chart : ClosedSubgroupChart m.range)
    (hline : ∀ x : A, x ∈ chart.tangent → x ∈ exponentialLines (H.map m)) :
    IsOpen (H : Set P) := by
  let j : P → m.range := fun p => ⟨m p, ⟨p, rfl⟩⟩
  have hj : Continuous j := IsInducing.subtypeVal.continuous_iff.mpr hm.continuous
  have h1 : j 1 ∈ chart.expOpen.target := by
    have h0 := chart.expOpen.map_source chart.zero_mem
    have he := chart.exp_chart 0 chart.zero_mem
    simp only [Submodule.coe_zero, expUnit_zero] at he
    have he' : chart.expOpen 0 = j 1 := Subtype.ext (he.trans m.map_one.symm)
    simpa only [he'] using h0
  apply H.isOpen_of_mem_nhds (g := (1 : P))
  refine mem_of_superset ((chart.expOpen.open_target.preimage hj).mem_nhds h1) ?_
  intro g hg
  have hg' : j g ∈ chart.expOpen.target := hg
  let x := chart.expOpen.symm (j g)
  have hx := chart.expOpen.map_target hg'
  have h := chart.exp_chart x hx
  rw [chart.expOpen.right_inv hg'] at h
  have hx' : expUnit (x : A) ∈ H.map m := by simpa using hline x x.property 1
  obtain ⟨y, hy, e⟩ := hx'
  exact hm.injective (e.trans h.symm) ▸ hy

/-- Simultaneous real exponential charts on the product and on closed subgroups. -/
theorem productChart : ProductChart.{u} := by
  intro J _ F _ _ _ _ G i s
  let : ∀ j, LieRing (Lie (F j) (G j).val) := fun j => (s j).lieRing
  let : ∀ j, LieAlgebra (F j) (Lie (F j) (G j).val) := fun j => (s j).lieAlgebra
  let : ∀ j, Module ℝ (Lie (F j) (G j).val) :=
    fun j => Module.restrictScalars ℝ (F j) (Lie (F j) (G j).val)
  classical
  choose d hd hdval hdline hdadj hdderiv using
    fun j => matrixTangentComparison (F j) (G j) (i j) (s j)
  let D : (∀ j, Lie (F j) (G j).val) →ₗ[ℝ] MatrixProduct F G i :=
    LinearMap.pi fun j => (d j).comp (LinearMap.proj j)
  let A := MatrixProduct F G i
  let m := pointMatrices F G i
  have hm : IsClosedEmbedding m := pointMatrices_closedEmbedding i
  have hlines (x : A) : x ∈ exponentialLines m.range ↔ x ∈ D.range := by
    constructor
    · intro h
      have hh (j : J) : x j ∈ exponentialLines (asMatrix (i j) (F j)).range := by
        intro t
        have h' := (pointMatrices_range_iff i _).1 (h t) j
        have he := piUnits_expUnit (t • x : MatrixProduct F G i) j
        exact he ▸ h'
      choose v hv using fun j => (hdline j _).1 (hh j)
      exact ⟨v, funext hv⟩
    · rintro ⟨v, rfl⟩ t
      apply (pointMatrices_range_iff i _).2
      intro j
      have he := piUnits_expUnit (t • D v : MatrixProduct F G i) j
      exact he.symm ▸ (hdline j _).2 ⟨v j, rfl⟩ t
  obtain ⟨C⟩ := closedSubgroupExponential A m.range hm.isClosed_range
  have hCrange : C.tangent = D.range := SetLike.ext fun x => (C.mem_tangent x).trans (hlines x)
  refine ⟨D, ?_, fun x j => hdval j (x j), hlines, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y e
    funext j
    exact hd j (congrFun e j)
  · intro H hH
    have hclosed : IsClosed (H.map m : Set Aˣ) := hm.isClosedMap _ hH
    obtain ⟨CH⟩ := closedSubgroupExponential A (H.map m) hclosed
    let e := subgroupImageHomeomorph m hm.isEmbedding H
    refine ⟨CH.tangent, CH.expOpen.transHomeomorph e.symm, ?_, CH.mem_tangent, CH.zero_mem,
      ?_, ?_, CH.bracket_mem, ?_, ?_⟩
    · intro x hx
      apply (hlines x).1
      intro t
      obtain ⟨g, hg, he⟩ := (CH.mem_tangent x).1 hx t
      exact ⟨g, he⟩
    · intro x hx
      have he : ∀ g : H, ((e g : H.map m) : Aˣ) = m g.val := fun _ => rfl
      change m (e.symm (CH.expOpen x)).val = _
      rw [← he, e.apply_symm_apply]
      exact CH.exp_chart x hx
    · intro g x
      have he : ((e g : H.map m) : Aˣ) = m g.val := rfl
      change conjugate (m g.val) x ∈ CH.tangent
      rw [← he]
      exact CH.conjugation (e g) x
    · intro h
      let : DiscreteTopology (H.map m) := CH.discrete_of_zero h
      exact e.isEmbedding.discreteTopology
    · intro h
      apply isOpen_of_full_lines m hm.isEmbedding H C
      intro x hx
      exact (CH.mem_tangent x).1 (show x ∈ CH.tangent from (h.trans hCrange.symm).symm ▸ hx)
  · rw [← hCrange]
    let e : PointProduct F G i ≃ₜ m.range := hm.isEmbedding.toHomeomorph
    have he (g : m.range) : m (e.symm g) = g.val := by
      change (e (e.symm g)).val = g.val
      rw [e.apply_symm_apply]
    refine ⟨C.expOpen.transHomeomorph e.symm, C.zero_mem, ?_, ?_⟩
    · intro x hx
      exact (he (C.expOpen x)).trans (C.exp_chart x hx)
    · convert C.exp_derivative using 1
      funext x
      exact congrArg Units.val (he (C.expOpen x))
  · intro x j
    rw [expUnit_apply]
    exact congrArg (fun y => (expUnit y).val) (hdval j (x j))
  · intro g x
    choose y hy hmat using fun j => hdadj j (g j) (x j)
    exact ⟨y, hy, funext hmat⟩
  · intro x y
    apply hasDerivAt_pi.mpr
    intro j
    have h := hdderiv j (x j) (y j)
    apply h.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => by
      change (expUnit (t • D x)).val j * (D y j) * ((expUnit (t • D x))⁻¹).val j = _
      simp only [conjugate, ← expUnit_neg, expUnit_apply, D, LinearMap.pi_apply,
        LinearMap.comp_apply, LinearMap.proj_apply, Pi.smul_apply, Pi.neg_apply]

/-- The exponential charts use the same coordinate projection and insertion maps
as the adelic point groups. -/
theorem productCoordinateCompatibility :
    ProductCoordinateCompatibility.{u} := by
  intro J _ F _ _ _ _ G i P _
  constructor
  · intro x g h
    apply Units.ext
    funext j
    change (asMatrix (i j) (F j) (g j)).val = (expUnit (fun j : {a // P a} => x j)).val j
    rw [expUnit_apply]
    exact (congrArg (fun z : (MatrixProduct F G i)ˣ => z.val j) h).trans (expUnit_apply x j)
  · intro x g h
    apply Units.ext
    funext j
    let X : MatrixProduct F G i := fun a => if ha : P a then x ⟨a, ha⟩ else 0
    change (asMatrix (i j) (F j) (if hj : P j then g ⟨j, hj⟩ else 1)).val =
      (expUnit X).val j
    rw [expUnit_apply]
    by_cases hj : P j
    · simp only [X, dite_eq_left hj]
      exact (congrArg
        (fun z : (MatrixProduct (fun a : {a // P a} => F a) (fun a => G a) (fun a => i a))ˣ =>
          z.val ⟨j, hj⟩) h).trans (expUnit_apply x ⟨j, hj⟩)
    · simp [X, hj]

end Products


section BaseChange

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization)
open scoped CategoryTheory.MonObj

open private baseChangePointIso isAffine_baseChange
  from LinearAlgebraicGroups.Affine.IdentityTangent

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

private def extendAffineGroup (G : AffineAlgebraicGroup k) : AffineAlgebraicGroup F := by
  let : IsAffine G.val.X.left := G.property.1
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let : QuasiCompact G.val.X.hom := G.property.2.2
  refine ⟨(groupBaseChange k F).obj G.val, isAffine_baseChange F G.val, ?_, ?_⟩
  · change LocallyOfFiniteType (pullback.snd G.val.X.hom (fieldSpecMap k F))
    infer_instance
  · change QuasiCompact (pullback.snd G.val.X.hom (fieldSpecMap k F))
    infer_instance

private def extendMatrixRealization {G : AffineAlgebraicGroup k} (i : MatrixRealization G) :
    MatrixRealization (extendAffineGroup (F := F) G) where
  size := i.size
  ambient := extendAffineGroup i.ambient
  matrix := baseChangePointIso F i.ambient.val ≪≫ Functor.isoWhiskerLeft _ i.matrix
  embedding := (groupBaseChange k F).map i.embedding
  closed := baseChangeClosedSubgroup k F i.embedding i.closed

/-- Scalar extension identifies the local points with their original matrix topology. -/
theorem baseChangeMatrixComparison : BaseChangeMatrixComparison.{u} := by
  intro k F _ _ _ _ G i
  let H := extendAffineGroup (F := F) G
  let iF := extendMatrixRealization (F := F) i
  let R := CommAlgCat.of F F
  let R₀ := (restrictTestAlgebra k F).obj R
  let R₁ := CommAlgCat.of k F
  let f : @AlgHom k R₀ R₁ _ _ _ R₀.algebra R₁.algebra :=
    @AlgHom.mk k R₀ R₁ _ _ _ R₀.algebra R₁.algebra (RingHom.id F) (fun _ => rfl)
  let g : @AlgHom k R₁ R₀ _ _ _ R₁.algebra R₀.algebra :=
    @AlgHom.mk k R₁ R₀ _ _ _ R₁.algebra R₀.algebra (RingHom.id F) (fun _ => rfl)
  let a : R₀ ⟶ R₁ := ConcreteCategory.ofHom (C := CommAlgCat k) (X := R₀) (Y := R₁) f
  let a' : R₁ ⟶ R₀ := ConcreteCategory.ofHom (C := CommAlgCat k) (X := R₁) (Y := R₀) g
  let eR : R₀ ≅ R₁ :=
    { hom := a, inv := a'
      hom_inv_id := CommAlgCat.hom_ext
        (@AlgHom.ext k R₀ R₀ _ _ _ R₀.algebra R₀.algebra _ _ fun _ => rfl)
      inv_hom_id := CommAlgCat.hom_ext
        (@AlgHom.ext k R₁ R₁ _ _ _ R₁.algebra R₁.algebra _ _ fun _ => rfl) }
  let ePoints := (baseChangePointIso F G.val).app R ≪≫
    ((groupPointsFunctor k).obj G.val).mapIso eR
  let e : PointsIn iF F ≃* PointsIn i F := ePoints.groupIsoToMulEquiv
  have heScheme (p : PointsIn iF F) :
      (show Points G.val.X R₁ from e p).left = (baseChangePoint k F G.val.X R p).left := by
    change ((testSpec k).map a.op).left ≫ (baseChangePoint k F G.val.X R p).left = _
    have he : ((testSpec k).map a.op).left = 𝟙 _ := by
      change Scheme.Spec.map ((𝟙 (CommRingCat.of F)).op) = _
      exact Scheme.Spec.map_id _
    rw [he, Category.id_comp]
  have heMatrix (p : PointsIn iF F) : asMatrix iF F p = asMatrix i F (e p) := by
    have hnat := baseChangePointsSchemeNaturality k F i.embedding.hom.hom R p
    let m := ((groupPointsFunctor k).map i.embedding) ≫ i.matrix.hom
    have ha := NatTrans.naturality_apply m a (baseChangePoint k F G.val.X R p)
    change (i.matrix.hom.app R₀).hom
      (baseChangePoint k F i.ambient.val.X R (p ≫ (baseChange k F).map i.embedding.hom.hom)) = _
    rw [hnat]
    have hb := ha.symm
    change Matrix.GeneralLinearGroup.map (RingHom.id F)
      ((i.matrix.hom.app R₀).hom (baseChangePoint k F G.val.X R p ≫ i.embedding.hom.hom)) =
        asMatrix i F (e p) at hb
    simpa only [Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply] using hb
  have hind : IsInducing (asMatrix i F) := .induced _
  have heq : (asMatrix i F) ∘ e = asMatrix iF F := funext fun p => (heMatrix p).symm
  have heInd : IsInducing e := (IsInducing.of_comp_iff hind).mp (by
    rw [heq]
    exact .induced _)
  let e' : PointsIn iF F ≃ₜ* PointsIn i F := { e, e.toEquiv.toHomeomorphOfIsInducing heInd with }
  exact ⟨H.property, iF, rfl, e', heScheme, heMatrix⟩

end BaseChange

section Completions

/-- Transport the real scalar action along an isometric ring equivalence. -/
private theorem realStructure_of_isometricRingEquiv
    {F E : Type*} [NormedField F] [NormedField E] [NormedAlgebra ℝ E]
    [FiniteDimensional ℝ E] (e : F ≃+* E) (he : Isometry e) :
    ∃ A : NormedAlgebra ℝ F,
      letI := A
      FiniteDimensional ℝ F ∧ ∀ r : ℝ, e (algebraMap ℝ F r) = algebraMap ℝ E r := by
  let a : ℝ →+* F := e.symm.toRingHom.comp (algebraMap ℝ E)
  let : Algebra ℝ F := a.toAlgebra
  have halg (r : ℝ) : e (algebraMap ℝ F r) = algebraMap ℝ E r := e.apply_symm_apply _
  have hs (r : ℝ) (x : F) : e (r • x) = r • e x := by
    simp only [Algebra.smul_def, map_mul, halg]
  have hn (x : F) : ‖e x‖ = ‖x‖ := by
    simpa only [map_zero, dist_zero_right] using he.dist_eq x 0
  let n : NormedAlgebra ℝ F := ⟨fun r x => by
    rw [← hn (r • x), hs, ← hn x]
    exact norm_smul_le _ _⟩
  refine ⟨n, ?_, halg⟩
  let e' : F ≃ₗ[ℝ] E := { e.toAddEquiv with map_smul' := hs }
  exact Module.Finite.of_surjective e'.symm.toLinearMap e'.symm.surjective

/-- Every actual infinite completion has the finite-dimensional real
scalar action transported from its real or complex completion model. -/
theorem completionRealStructures : CompletionRealStructures.{u} := by
  intro K _ v
  rcases v.isReal_or_isComplex with hr | hc
  · obtain ⟨A, hA, hmap⟩ := realStructure_of_isometricRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hr)
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hr).isometry
    exact ⟨A, hA, fun _ r => hmap r,
      fun h' _ => False.elim (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr h' hr)⟩
  · obtain ⟨A, hA, hmap⟩ := realStructure_of_isometricRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).isometry
    exact ⟨A, hA,
      fun h' _ => False.elim (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc h'),
      fun _ r => hmap r⟩

end Completions

end LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
