import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.Lidskii
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.LogDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant
open TraceClassDefinitions TraceIdeals.TraceClassDefinitions
open TraceIdeals.TraceNormIdeal TraceDeterminantContinuity
open Filter
open scoped Topology Classical

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exterior_series_formula : Spec.ExteriorSeriesFormula.{u} := by
  intro H _ _ _ T hT z
  have hs := ((fredholm_series_bound T hT z).1.of_norm).hasSum
  exact hs.congr_fun (fun n => congrArg (fun a : ℂ => z ^ n * a)
    (exterior_construction T hT n).2.2.2)

/-- The full algebraic eigenvalue multiset has absolutely summable weights. -/
lemma summable_scaled_eigenvalues (T : H →L[ℂ] H) (hT : IsTraceClass T) (z : ℂ) :
    Summable (fun i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T =>
      ‖z * TraceIdeals.Lidskii.Spec.eigenvalue T i‖) := by
  simpa only [norm_mul] using
    ((TraceIdeals.Lidskii.absolute_eigenvalue_sum H T hT).1.mul_left ‖z‖)

lemma eigenvalue_product_multipliable (T : H →L[ℂ] H) (hT : IsTraceClass T) (z : ℂ) :
    Multipliable (fun i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T =>
      1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i) :=
  multipliable_one_add_of_summable (summable_scaled_eigenvalues T hT z)

theorem uniform_eigenvalue_product : Spec.UniformEigenvalueProduct.{u} := by
  intro H _ _ _ T hT R hR
  have hs := (TraceIdeals.Lidskii.absolute_eigenvalue_sum H T hT).1.mul_left R
  have hu := Summable.hasProdUniformlyOn_one_add (R := ℂ)
    (K := Metric.closedBall (0 : ℂ) R) (f := fun i z =>
      z * TraceIdeals.Lidskii.Spec.eigenvalue T i)
    (isCompact_closedBall 0 R) hs
    (Filter.Eventually.of_forall (fun i z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hz) (norm_nonneg _)))
    (fun i => (continuous_id.mul_const _).continuousOn)
  exact hu.tendstoUniformlyOn

theorem entire_eigenvalue_product : Spec.EntireEigenvalueProduct.{u} := by
  intro H _ _ _ T hT
  have hu := locallyUniform_of_disks (uniform_eigenvalue_product H T hT)
  have hd := hu.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (fun s =>
      (Differentiable.fun_finsetProd (fun i _ =>
        (differentiable_const _).add (differentiable_id.mul_const _))).differentiableOn))
    isOpen_univ
  exact differentiableOn_univ.mp hd

/-- Differentiation of the locally uniformly convergent finite products gives
the logarithmic derivative as a convergent unordered spectral sum. -/
lemma eigenvalue_product_logDeriv_hasSum (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (z : ℂ) (hz : ∀ i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T,
      1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i ≠ 0) :
    HasSum (fun i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T =>
      TraceIdeals.Lidskii.Spec.eigenvalue T i /
        (1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i))
      (logDeriv (Spec.EigenvalueProductValue T) z) := by
  have hp : Spec.EigenvalueProductValue T z ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hz (summable_scaled_eigenvalues T hT z)
  have hu := (locallyUniform_of_disks (uniform_eigenvalue_product H T hT)).tendstoLocallyUniformlyOn (s := Set.univ)
  have hd (s : Finset (TraceIdeals.Lidskii.Spec.EigenvalueIndex T)) :
      Differentiable ℂ (fun w => ∏ i ∈ s, (1 + w * TraceIdeals.Lidskii.Spec.eigenvalue T i)) :=
    Differentiable.fun_finsetProd (fun i _ =>
      (differentiable_const _).add (differentiable_id.mul_const _))
  have hl := Complex.logDeriv_tendsto isOpen_univ (Set.mem_univ z) hu
    (Filter.Eventually.of_forall (fun s => (hd s).differentiableOn)) hp
  change Tendsto _ atTop _
  convert hl using 1
  ext s
  rw [logDeriv_fun_prod (fun i _ => hz i) (fun i _ =>
    ((differentiable_const _).add (differentiable_id.mul_const _)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [logDeriv_apply]
  have hdi : HasDerivAt (fun w : ℂ => 1 + w * TraceIdeals.Lidskii.Spec.eigenvalue T i)
      (TraceIdeals.Lidskii.Spec.eigenvalue T i) z := by
    convert ((hasDerivAt_id z).mul_const
      (TraceIdeals.Lidskii.Spec.eigenvalue T i)).const_add 1 using 1 <;> simp only [id_eq, one_mul]
  rw [hdi.deriv]

/-- Differentiating the absolutely convergent exterior series at zero gives
its degree-one coefficient, the canonical trace. -/
lemma determinant_hasDerivAt_zero (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    HasDerivAt (fredholmDeterminant T) (trace T) 0 := by
  have hs := Complex.hasSum_deriv_of_summable_norm
    (Real.summable_pow_div_factorial (traceNorm T))
    (F := fun n : ℕ => fun z : ℂ => z ^ n * exteriorTrace T n)
    (U := Metric.ball 0 1)
    (fun n => ((differentiable_id.pow n).mul_const _).differentiableOn)
    Metric.isOpen_ball
    (fun n z hz => by
      simpa only [one_mul] using exterior_term_bound T hT zero_le_one
        (mem_ball_zero_iff.mp hz).le n)
    (by simp : (0 : ℂ) ∈ Metric.ball 0 1)
  have hterm (n : ℕ) :
      deriv (fun z : ℂ => z ^ n * exteriorTrace T n) 0 =
        if n = 1 then trace T else 0 := by
    rw [((hasDerivAt_pow n (0 : ℂ)).mul_const (exteriorTrace T n)).deriv]
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp [exterior_trace_one H T]
    · simp [Nat.succ_ne_zero]
  simp_rw [hterm] at hs
  have heq : deriv (fredholmDeterminant T) 0 = trace T := by
    exact hs.unique (hasSum_ite_eq 1 (trace T))
  rw [← heq]
  exact (determinant_differentiable T hT 0).hasDerivAt

/-- Multiplicativity computes the derivative wherever `I + zT` is a unit.
This uses only the exterior determinant, before its spectral identification. -/
lemma determinant_hasDerivAt_of_unit (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (z : ℂ) (a : (H →L[ℂ] H)ˣ)
    (ha : (a : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H + z • T) :
    HasDerivAt (fredholmDeterminant T)
      (fredholmDeterminant T z * trace ((↑(a⁻¹) : H →L[ℂ] H).comp T)) z := by
  let U : H →L[ℂ] H := (↑(a⁻¹) : H →L[ℂ] H).comp T
  have hU : IsTraceClass U := (traceNorm_comp_left_le _ T hT).1
  have hprod (w : ℂ) :
      fredholmDeterminant T (z + w) =
        fredholmDeterminant T z * fredholmDeterminant U w := by
    have heq : z • T + w • U + (z • T).comp (w • U) = (z + w) • T := by
      have hAU : (ContinuousLinearMap.id ℂ H + z • T).comp U = T := by
        change (ContinuousLinearMap.id ℂ H + z • T) *
          ((↑(a⁻¹) : H →L[ℂ] H) * T) = T
        rw [← ha, ← mul_assoc, Units.mul_inv, one_mul]
      ext x
      have hx := congrArg (fun B : H →L[ℂ] H => B x) hAU
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply] at hx ⊢
      rw [map_smul]
      calc
        z • T x + w • U x + z • w • T (U x) =
            z • T x + w • (U x + z • T (U x)) := by module
        _ = (z + w) • T x := by rw [hx]; module
    have hm := (determinant_multiplicative (z • T) (w • U)
      (traceClass_smul z T hT).1 (traceClass_smul w U hU).1).2
    simpa only [heq, determinant_smul, one_mul] using hm
  have hd := (determinant_hasDerivAt_zero U hU).const_mul (fredholmDeterminant T z)
  have hshift : HasDerivAt (fun w => fredholmDeterminant T (z + w))
      (fredholmDeterminant T z * trace U) 0 := by
    simpa only [← hprod] using hd
  have hshift' : HasDerivAt (fun w => fredholmDeterminant T (z + w))
      (fredholmDeterminant T z * trace U) (z - z) := by simpa using hshift
  have hback := hshift'.comp z (h := fun w : ℂ => w - z) (by exact (hasDerivAt_id z).sub_const z)
  simpa only [Function.comp_def, sub_self, mul_one, add_sub_cancel] using hback

/-- The rank-one case follows from the proved finite nuclear expansion. -/
lemma determinant_rankOne (u v : H) (c : ℂ) :
    fredholmDeterminant (c • rankOne u v) 1 = 1 + c * inner ℂ v u := by
  letI : DecidableEq Unit := Classical.decEq Unit
  have h := finite_nuclear_determinant_expansion (fun _ : Unit => u)
    (fun _ : Unit => v) (fun _ : Unit => c) (c • rankOne u v)
    (fun x => by simp [rankOne_apply, smul_smul])
  have hu : (Finset.univ : Finset (Finset Unit)) = {∅, {()}} := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hs : () ∈ s
    · right
      ext a
      have ha : a = () := Subsingleton.elim _ _
      subst a
      simp [hs]
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a
      have ha : a = () := Subsingleton.elim _ _
      simpa only [ha] using hs
  rw [hu] at h
  rw [Finset.sum_pair (by simp : (∅ : Finset Unit) ≠ {()})] at h
  simp only [Finset.prod_empty, Matrix.det_isEmpty, mul_one, Finset.prod_singleton] at h
  have hdet : (Matrix.of (fun (_i _j : ({()} : Finset Unit)) => inner ℂ v u)).det =
      inner ℂ v u :=
    Matrix.det_eq_elem_of_subsingleton _ ⟨(), by simp⟩
  exact h.trans (congrArg (fun a : ℂ => 1 + c * a) hdet)

/-- An invertible identity-plus-trace-class operator has a trace-class
inverse perturbation; multiplicativity then gives a reciprocal determinant. -/
lemma determinant_ne_zero_of_isUnit (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (hA : IsUnit (ContinuousLinearMap.id ℂ H + T)) :
    fredholmDeterminant T 1 ≠ 0 := by
  obtain ⟨a, ha⟩ := hA
  let B : H →L[ℂ] H := -((↑(a⁻¹) : H →L[ℂ] H).comp T)
  have hB : IsTraceClass B :=
    (traceClass_neg _ (traceNorm_comp_left_le _ T hT).1).1
  have hAB : T + B + T.comp B = 0 := by
    have hab : (ContinuousLinearMap.id ℂ H + T) * (↑(a⁻¹) : H →L[ℂ] H) = 1 := by
      rw [← ha]
      exact a.val_inv
    have habT := congrArg (fun A : H →L[ℂ] H => A * T) hab
    change (ContinuousLinearMap.id ℂ H + T).comp
      ((↑(a⁻¹) : H →L[ℂ] H).comp T) = T at habT
    ext x
    have hx := congrArg (fun A : H →L[ℂ] H => A x) habT
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hx
    simp only [B, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, map_neg, ContinuousLinearMap.zero_apply]
    calc
      _ = T x - ((↑(a⁻¹) : H →L[ℂ] H) (T x) +
        T ((↑(a⁻¹) : H →L[ℂ] H) (T x))) := by abel
      _ = 0 := by rw [hx, sub_self]
  have hm := (determinant_multiplicative T B hT hB).2
  rw [hAB] at hm
  have hzero : fredholmDeterminant (0 : H →L[ℂ] H) 1 = 1 := by
    simpa using determinant_rankOne (0 : H) 0 0
  change fredholmDeterminant 0 1 = fredholmDeterminant T 1 * fredholmDeterminant B 1 at hm
  rw [hzero] at hm
  intro hz
  rw [hz, zero_mul] at hm
  exact one_ne_zero hm

/-- A kernel vector creates an annihilated rank-one projection. Multiplying
by its complementary projection forces the determinant to vanish. -/
lemma determinant_eq_zero_of_kernel (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (x : H) (hx : x ≠ 0) (hTx : T x = -x) :
    fredholmDeterminant T 1 = 0 := by
  let c : ℂ := (inner ℂ x x)⁻¹
  let P : H →L[ℂ] H := c • rankOne x x
  have hi : inner ℂ x x ≠ 0 := by simpa using hx
  have hP : IsTraceClass P := by
    have hr : (rankOne x x : H →L[ℂ] H).range ≤ Submodule.span ℂ {x} := by
      rintro _ ⟨y, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    haveI : FiniteDimensional ℂ (rankOne x x : H →L[ℂ] H).range :=
      Submodule.finiteDimensional_of_le hr
    exact (traceClass_smul c _ (finite_rank_traceClass _)).1
  have hTP : T.comp P = -P := by
    ext y
    simp [P, rankOne_apply, hTx, map_smul, smul_neg]
  have heq : T + (-P) + T.comp (-P) = T := by
    rw [ContinuousLinearMap.comp_neg, hTP, neg_neg]
    abel
  have hd : fredholmDeterminant (-P) 1 = 0 := by
    rw [show -P = (-c) • rankOne x x by simp [P]]
    rw [determinant_rankOne]
    dsimp only [c]
    rw [neg_mul, inv_mul_cancel₀ hi]
    exact add_neg_cancel 1
  have hm := (determinant_multiplicative T (-P) hT (traceClass_neg P hP).1).2
  simpa only [heq, hd, mul_zero] using hm

lemma exists_kernel_of_not_isUnit (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (hA : ¬IsUnit (ContinuousLinearMap.id ℂ H + T)) :
    ∃ x : H, x ≠ 0 ∧ T x = -x := by
  have halt := Fredholm.riesz_schauder_alternative (-T) (traceClass_neg T hT).1.1
  simp only [sub_neg_eq_add] at halt
  have hker : (ContinuousLinearMap.id ℂ H + T).toLinearMap.ker ≠ ⊥ := by
    intro hk
    have hi : Function.Injective (ContinuousLinearMap.id ℂ H + T) :=
      LinearMap.ker_eq_bot.mp hk
    exact hA (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hi, halt.mp hi⟩)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨x, hx0, ?_⟩
  change x + T x = 0 at hx
  exact eq_neg_of_add_eq_zero_right hx

theorem nonvanishing_iff_invertible : Spec.NonvanishingIffInvertible.{u} := by
  intro H _ _ _ T hT z
  change fredholmDeterminant T z ≠ 0 ↔ _
  have hU := (traceClass_smul z T hT).1
  have heq : fredholmDeterminant (z • T) 1 = fredholmDeterminant T z := by
    rw [determinant_smul, one_mul]
  constructor
  · intro hd
    by_contra hA
    obtain ⟨x, hx, hTx⟩ := exists_kernel_of_not_isUnit (z • T) hU hA
    exact hd (heq.symm.trans (determinant_eq_zero_of_kernel (z • T) hU x hx hTx))
  · intro hA
    rw [← heq]
    exact determinant_ne_zero_of_isUnit (z • T) hU hA

theorem zeros_exactly : Spec.ZerosExactly.{u} := by
  intro H _ _ _ T hT z
  change fredholmDeterminant T z = 0 ↔ _
  constructor
  · intro hd
    have hz : z ≠ 0 := by
      rintro rfl
      exact zero_ne_one (hd.symm.trans (determinant_at_zero H T))
    have hn : ¬IsUnit (ContinuousLinearMap.id ℂ H + z • T) := by
      intro hu
      exact ((nonvanishing_iff_invertible H T hT z).mpr hu) hd
    obtain ⟨x, hx, hTx⟩ := exists_kernel_of_not_isUnit (z • T)
      (traceClass_smul z T hT).1 hn
    have he : T x = (-z⁻¹) • x := by
      calc
        T x = z⁻¹ • (z • T x) := by simp [hz]
        _ = z⁻¹ • (-x) := by rw [← ContinuousLinearMap.smul_apply, hTx]
        _ = (-z⁻¹) • x := by simp
    refine ⟨-z⁻¹, neg_ne_zero.mpr (inv_ne_zero hz), ?_, ?_⟩
    · exact (Submodule.ne_bot_iff _).mpr ⟨x, Module.End.mem_eigenspace_iff.mpr he, hx⟩
    · simp [hz]
  · rintro ⟨μ, hμ, he, hez⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp he
    have heigen : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    have hTx : (z • T) x = -x := by
      have hzμ : z * μ = -1 := eq_neg_of_add_eq_zero_right hez
      simp [heigen, smul_smul, hzμ]
    have hd := determinant_eq_zero_of_kernel (z • T) (traceClass_smul z T hT).1 x hx0 hTx
    simpa only [determinant_smul, one_mul] using hd

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
lemma ker_mul_unit (B C : Module.End ℂ V) (hB : IsUnit B) (hc : Commute B C) (n : ℕ) :
    LinearMap.ker ((B * C) ^ n) = LinearMap.ker (C ^ n) := by
  obtain ⟨b, hb⟩ := hB.pow n
  rw [hc.mul_pow, ← hb]
  ext x
  simp only [LinearMap.mem_ker, Module.End.mul_apply]
  constructor
  · intro hx
    have h := congrArg (fun y => (↑(b⁻¹) : Module.End ℂ V) y) hx
    simpa only [map_zero, ← Module.End.mul_apply, ← mul_assoc, Units.inv_mul, one_mul, Module.End.one_apply] using h
  · intro hx
    rw [hx, map_zero]

lemma maxGenEigenspace_eq_of_unit_factor (T U : Module.End ℂ V) (μ ν : ℂ)
    (B : Module.End ℂ V) (hB : IsUnit B) (hc : Commute B (T - μ • 1))
    (h : U - ν • 1 = B * (T - μ • 1)) :
    U.maxGenEigenspace ν = T.maxGenEigenspace μ := by
  ext x
  simp only [Module.End.mem_maxGenEigenspace, h]
  exact exists_congr fun n => by
    change x ∈ LinearMap.ker ((B * (T - μ • 1)) ^ n) ↔
      x ∈ LinearMap.ker ((T - μ • 1) ^ n)
    rw [ker_mul_unit B _ hB hc]

lemma resolvent_maxGenEigenspace (T : Module.End ℂ V) (z μ : ℂ)
    (a : (Module.End ℂ V)ˣ) (ha : (a : Module.End ℂ V) = 1 + z • T)
    (hμ : 1 + z * μ ≠ 0) :
    ((↑(a⁻¹) : Module.End ℂ V) * T).maxGenEigenspace (μ / (1 + z * μ)) =
      T.maxGenEigenspace μ := by
  let c : ℂ := (1 + z * μ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hμ
  have haT : Commute (a : Module.End ℂ V) T := by
    rw [ha]
    exact (Commute.one_left T).add_left ((Commute.refl T).smul_left z)
  have haiT : Commute (↑(a⁻¹) : Module.End ℂ V) T :=
    haT.units_inv_left
  let B : Module.End ℂ V := c • (↑(a⁻¹) : Module.End ℂ V)
  apply maxGenEigenspace_eq_of_unit_factor T _ μ _ B
  · change IsUnit (c • (↑(a⁻¹) : Module.End ℂ V))
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ _)).mul a⁻¹.isUnit
  · exact ((haiT.smul_left c).sub_right (Commute.one_right _ |>.smul_right μ))
  · apply a.isUnit.mul_left_cancel
    change (a : Module.End ℂ V) * (_ - _) = (a : Module.End ℂ V) * _
    simp only [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_smul_comm,
      B, mul_one]
    rw [ha]
    simp only [smul_add, smul_smul]
    have hcμ : μ / (1 + z * μ) = c * μ := by dsimp only [c]; ring
    have hcc : c * (1 + z * μ) = 1 := inv_mul_cancel₀ hμ
    have hcz : 1 - μ / (1 + z * μ) * z = c := by
      rw [hcμ]
      linear_combination -hcc
    calc
      T - ((μ / (1 + z * μ)) • 1 + (μ / (1 + z * μ) * z) • T) =
          (1 - μ / (1 + z * μ) * z) • T - (μ / (1 + z * μ)) • 1 := by module
      _ = _ := by rw [hcz, hcμ]; simp only [smul_mul_assoc, one_mul]; module

lemma one_add_mul_eigenvalue_ne_zero (T : Module.End ℂ V) (z μ : ℂ)
    (a : (Module.End ℂ V)ˣ) (ha : (a : Module.End ℂ V) = 1 + z • T)
    (he : T.HasEigenvalue μ) : 1 + z * μ ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp he
  have hTx : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
  intro hzero
  have hax : (a : Module.End ℂ V) x = 0 := by
    rw [ha]
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, hTx, smul_smul]
    calc
      x + (z * μ) • x = (1 + z * μ) • x := by module
      _ = 0 := by rw [hzero, zero_smul]
  have hinv := congrArg (fun y => (↑(a⁻¹) : Module.End ℂ V) y) hax
  apply hx0
  simpa only [map_zero, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using hinv

lemma resolvent_hasEigenvalue (T : Module.End ℂ V) (z μ : ℂ)
    (a : (Module.End ℂ V)ˣ) (ha : (a : Module.End ℂ V) = 1 + z • T)
    (hμ : 1 + z * μ ≠ 0) :
    ((↑(a⁻¹) : Module.End ℂ V) * T).HasEigenvalue (μ / (1 + z * μ)) ↔
      T.HasEigenvalue μ := by
  have hiff (S : Module.End ℂ V) (w : ℂ) :
      S.HasEigenvalue w ↔ S.maxGenEigenspace w ≠ ⊥ := by
    exact (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (f := S) (μ := w)
      (k := ⊤) (by simp)).symm
  rw [hiff, hiff, resolvent_maxGenEigenspace T z μ a ha hμ]

lemma inverse_resolvent_identity (T : Module.End ℂ V) (z : ℂ)
    (a : (Module.End ℂ V)ˣ) (ha : (a : Module.End ℂ V) = 1 + z • T) :
    (↑(a⁻¹) : Module.End ℂ V) =
      1 + (-z) • ((↑(a⁻¹) : Module.End ℂ V) * T) := by
  have heq := Units.inv_mul a
  rw [ha, mul_add, mul_one, mul_smul_comm] at heq
  rw [← smul_mul_assoc] at heq
  rw [neg_smul]
  simpa only [smul_mul_assoc, sub_eq_add_neg] using eq_sub_of_add_eq heq

lemma resolvent_scalar_roundtrip (z μ : ℂ) (hμ : 1 + z * μ ≠ 0) :
    (μ / (1 + z * μ)) / (1 + (-z) * (μ / (1 + z * μ))) = μ := by
  have hden : 1 + (-z) * (μ / (1 + z * μ)) = (1 + z * μ)⁻¹ := by
    field_simp [hμ]
    <;> ring
  rw [hden, div_inv_eq_mul, div_mul_cancel₀ _ hμ]

end Algebraic

/-- The Möbius transformation bijects actual nonzero eigenvalues and preserves
all their root spaces. -/
def resolventEigenvalueEquiv (T : H →L[ℂ] H) (z : ℂ)
    (a : (H →L[ℂ] H)ˣ) (ha : (a : H →L[ℂ] H) = 1 + z • T) :
    TraceIdeals.Lidskii.Spec.NonzeroEigenvalues T ≃ TraceIdeals.Lidskii.Spec.NonzeroEigenvalues ((↑(a⁻¹) : H →L[ℂ] H) * T) := by
  let b : (Module.End ℂ H)ˣ := Units.map ContinuousLinearMap.toLinearMapRingHom.toMonoidHom a
  have hb : (b : Module.End ℂ H) = 1 + z • T.toLinearMap := congrArg ContinuousLinearMap.toLinearMap ha
  let U : H →L[ℂ] H := (↑(a⁻¹) : H →L[ℂ] H) * T
  have hi : (↑(b⁻¹) : Module.End ℂ H) = 1 + (-z) • U.toLinearMap :=
    inverse_resolvent_identity T.toLinearMap z b hb
  have hTU : (↑((b⁻¹)⁻¹) : Module.End ℂ H) * U.toLinearMap = T.toLinearMap := by
    change (b : Module.End ℂ H) * ((↑(b⁻¹) : Module.End ℂ H) * T.toLinearMap) = T.toLinearMap
    rw [← mul_assoc, Units.mul_inv, one_mul]
  let f : TraceIdeals.Lidskii.Spec.NonzeroEigenvalues T → TraceIdeals.Lidskii.Spec.NonzeroEigenvalues U := fun μ =>
    ⟨μ.val / (1 + z * μ.val),
      div_ne_zero μ.property.1 (one_add_mul_eigenvalue_ne_zero _ _ _ b hb μ.property.2),
      (resolvent_hasEigenvalue T.toLinearMap z μ.val b hb
        (one_add_mul_eigenvalue_ne_zero _ _ _ b hb μ.property.2)).mpr μ.property.2⟩
  let g : TraceIdeals.Lidskii.Spec.NonzeroEigenvalues U → TraceIdeals.Lidskii.Spec.NonzeroEigenvalues T := fun ν =>
    ⟨ν.val / (1 + (-z) * ν.val),
      div_ne_zero ν.property.1 (one_add_mul_eigenvalue_ne_zero _ _ _ b⁻¹ hi ν.property.2), by
      have he := (resolvent_hasEigenvalue U.toLinearMap (-z) ν.val b⁻¹ hi
        (one_add_mul_eigenvalue_ne_zero _ _ _ b⁻¹ hi ν.property.2)).mpr ν.property.2
      rwa [hTU] at he⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro μ
    apply Subtype.ext
    exact resolvent_scalar_roundtrip z μ.val (one_add_mul_eigenvalue_ne_zero _ _ _ b hb μ.property.2)
  · intro ν
    apply Subtype.ext
    have h := resolvent_scalar_roundtrip (-z) ν.val
      (one_add_mul_eigenvalue_ne_zero _ _ _ b⁻¹ hi ν.property.2)
    simpa only [neg_neg] using h


lemma resolvent_algebraicMultiplicity (T : H →L[ℂ] H) (z : ℂ)
    (a : (H →L[ℂ] H)ˣ) (ha : (a : H →L[ℂ] H) = 1 + z • T)
    (μ : TraceIdeals.Lidskii.Spec.NonzeroEigenvalues T) :
    TraceIdeals.WeylProducts.Spec.algebraicMultiplicity ((↑(a⁻¹) : H →L[ℂ] H) * T)
      (resolventEigenvalueEquiv T z a ha μ).val =
      TraceIdeals.WeylProducts.Spec.algebraicMultiplicity T μ.val := by
  let b : (Module.End ℂ H)ˣ := Units.map ContinuousLinearMap.toLinearMapRingHom.toMonoidHom a
  have hb : (b : Module.End ℂ H) = 1 + z • T.toLinearMap := congrArg ContinuousLinearMap.toLinearMap ha
  exact congrArg (fun E : Submodule ℂ H => Module.finrank ℂ E) (resolvent_maxGenEigenspace T.toLinearMap z μ.val b hb
    (one_add_mul_eigenvalue_ne_zero _ _ _ b hb μ.property.2))

def resolventEigenvalueIndexEquiv (T : H →L[ℂ] H) (z : ℂ)
    (a : (H →L[ℂ] H)ˣ) (ha : (a : H →L[ℂ] H) = 1 + z • T) :
    TraceIdeals.Lidskii.Spec.EigenvalueIndex T ≃ TraceIdeals.Lidskii.Spec.EigenvalueIndex ((↑(a⁻¹) : H →L[ℂ] H) * T) :=
  Equiv.sigmaCongr (resolventEigenvalueEquiv T z a ha)
    (fun μ => finCongr (resolvent_algebraicMultiplicity T z a ha μ).symm)

lemma trace_resolvent_hasSum (T : H →L[ℂ] H)
    (hT : TraceIdeals.TraceClassDefinitions.IsTraceClass T) (z : ℂ)
    (a : (H →L[ℂ] H)ˣ) (ha : (a : H →L[ℂ] H) = 1 + z • T) :
    HasSum (fun i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T => TraceIdeals.Lidskii.Spec.eigenvalue T i / (1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i))
      (TraceIdeals.TraceClassDefinitions.trace ((↑(a⁻¹) : H →L[ℂ] H) * T)) := by
  have hU := (FredholmDeterminant.TraceDeterminantContinuity.traceNorm_comp_left_le
    (↑(a⁻¹) : H →L[ℂ] H) T hT).1
  have hs := (TraceIdeals.Lidskii.lidskii H _ hU).2
  exact (resolventEigenvalueIndexEquiv T z a ha).hasSum_iff.mpr hs

/-- Lidskii applied to the resolvent transform identifies both logarithmic
derivatives, with multiplicities transported by the proved root-space identity. -/
lemma determinant_logDeriv_eq_product (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (z : ℂ) (hz : fredholmDeterminant T z ≠ 0) :
    logDeriv (fredholmDeterminant T) z = logDeriv (Spec.EigenvalueProductValue T) z := by
  obtain ⟨a, ha⟩ := (nonvanishing_iff_invertible H T hT z).mp hz
  have hb : (a : H →L[ℂ] H) = 1 + z • T := ha
  have hden (i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T) :
      1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i ≠ 0 := by
    let b : (Module.End ℂ H)ˣ := Units.map ContinuousLinearMap.toLinearMapRingHom.toMonoidHom a
    have hb' : (b : Module.End ℂ H) = 1 + z • T.toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap hb
    exact one_add_mul_eigenvalue_ne_zero _ _ _ b hb' i.1.property.2
  have heq := (eigenvalue_product_logDeriv_hasSum T hT z hden).unique
    (trace_resolvent_hasSum T hT z a hb)
  rw [heq, logDeriv_apply, (determinant_hasDerivAt_of_unit T hT z a ha).deriv]
  exact mul_div_cancel_left₀ _ hz

/-- Both entire functions have value one at zero. Equality of their logarithmic
derivatives on a small zero-free disk makes their quotient constant there. -/
lemma determinant_eventuallyEq_product (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    fredholmDeterminant T =ᶠ[𝓝 (0 : ℂ)] Spec.EigenvalueProductValue T := by
  let D := fredholmDeterminant T
  let P := Spec.EigenvalueProductValue T
  have hD := determinant_differentiable T hT
  have hP := entire_eigenvalue_product H T hT
  have hD0 : D 0 = 1 := determinant_at_zero H T
  have hP0 : P 0 = 1 := by simp [P, Spec.EigenvalueProductValue]
  have hopen : IsOpen {z : ℂ | D z ≠ 0 ∧ P z ≠ 0} :=
    (isOpen_ne_fun hD.continuous continuous_const).inter
      (isOpen_ne_fun hP.continuous continuous_const)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simp [hD0, hP0])
  have hq : DifferentiableOn ℂ (fun z => D z / P z) (Metric.ball 0 r) := by
    intro z hz
    exact ((hD z).div (hP z) (hball hz).2).differentiableWithinAt
  have hq' : (Metric.ball (0 : ℂ) r).EqOn (deriv (fun z => D z / P z)) 0 := by
    intro z hz
    have hDz := (hball hz).1
    have hPz := (hball hz).2
    have hl := logDeriv_div z hDz hPz (hD z) (hP z)
    have he := determinant_logDeriv_eq_product T hT z hDz
    have hzq : D z / P z ≠ 0 := div_ne_zero hDz hPz
    change logDeriv (fun z => D z / P z) z = _ at hl
    rw [he, sub_self, logDeriv_apply] at hl
    exact (div_eq_zero_iff.mp hl).resolve_right (by exact hzq)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  have heq := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) r).isPreconnected hq hq' (y := (0 : ℂ)) hz (by simp [hr])
  rw [hD0, hP0, div_one] at heq
  exact (div_eq_one_iff_eq (hball hz).2).mp heq

/-- The scalar identity theorem globalizes the proved equality near zero. -/
lemma determinant_eq_product_of_eventuallyEq (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (hlocal : fredholmDeterminant T =ᶠ[𝓝 (0 : ℂ)] Spec.EigenvalueProductValue T) :
    fredholmDeterminant T = Spec.EigenvalueProductValue T := by
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (determinant_differentiable T hT)).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (entire_eigenvalue_product H T hT)) hlocal

/-- The exterior determinant equals the convergent product over every algebraic
eigenvalue occurrence, without normality or separability. -/
theorem product_formula : Spec.ProductFormula.{u} := by
  intro H _ _ _ T hT z
  have hlocal := determinant_eventuallyEq_product T hT
  have heq := determinant_eq_product_of_eventuallyEq T hT hlocal
  change HasProd (fun i : TraceIdeals.Lidskii.Spec.EigenvalueIndex T =>
    1 + z * TraceIdeals.Lidskii.Spec.eigenvalue T i) (fredholmDeterminant T z)
  rw [congrFun heq z]
  exact (eigenvalue_product_multipliable T hT z).hasProd

theorem fredholm_determinant : Spec.FredholmDeterminantTheorem.{u,w} := by
  exact ⟨entire_exterior_series, uniform_exterior_series, traceNorm_locally_uniform,
    determinant_multiplicative, exterior_series_formula, product_formula,
    uniform_eigenvalue_product, entire_eigenvalue_product, nonvanishing_iff_invertible,
    zeros_exactly⟩

end ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant
