import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.CriticalConeNecessity
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ActiveConstraints
import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorPeano
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff
namespace D04
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints

abbrev criticalCone : Specs.D04.C05.CriticalConeNecessity.criticalConeType :=
  Specs.D04.C05.CriticalConeNecessity.criticalConeValue

namespace CriticalCone

/-- C² on a neighborhood supplies the paper's recursive pointwise hypothesis. -/
theorem twice_at {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} {a : X}
    (hf : ContDiffAt ℝ 2 f a) :
    ∃ V : Set X, TimesDifferentiableAt 2 V f a := by
  obtain ⟨V, hV, ha, h⟩ := hf.contDiffOn' le_rfl (by simp)
  exact ⟨V, crOn_timesDifferentiableAt 2 V f hV
    ((crOn_iff_contDiffOn 2 V f hV).mpr (by simpa using h)) a ha⟩

/-- The one-sided order-two scalar test needs zero first derivative. -/
theorem right_second_nonneg {F : ℝ → ℝ} (hF : ContDiffAt ℝ 2 F 0)
    (hd : deriv F 0 = 0)
    (hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), F 0 ≤ F t) :
    0 ≤ iteratedDeriv 2 F 0 := by
  obtain ⟨V, hV⟩ := twice_at hF
  have hr := taylorPeano_scalar 2 (by norm_num) V F 0 hV
  have ht := hr.tendsto_div_nhds_zero.mono_left (nhdsGT_le_nhdsNE 0)
  have hp (t : ℝ) : (∑ j ∈ Finset.range (2+1),
      iteratedDeriv j F 0 / (j.factorial : ℝ) * t^j) =
      F 0 + (iteratedDeriv 2 F 0 / 2) * t^2 := by
    simp [Finset.sum_range_succ, iteratedDeriv_succ, hd]
  simp_rw [zero_add, hp, sq_abs] at ht
  have ht' : Tendsto (fun t => (F t - F 0) / t^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv 2 F 0 / 2)) := by
    have H := ht.add_const (iteratedDeriv 2 F 0 / 2)
    simp only [zero_add] at H
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ne_of_gt ht
    field_simp
    <;> ring
  have hn : 0 ≤ iteratedDeriv 2 F 0 / 2 := ge_of_tendsto ht' (by
    filter_upwards [hm] with t ht
    exact div_nonneg (sub_nonneg.mpr ht) (sq_nonneg t))
  linarith

end CriticalCone

/-- Pull a straight coordinate ray back through the accepted constraint chart. -/
theorem critical_direction_curve :
    Specs.D04.C05.CriticalConeNecessity.critical_direction_curveType := by
  classical
  intro n q s U g h c a v hU hg hh ha hli hgv hhv
  obtain ⟨k, w, X, A, B, C, inv, hchart⟩ :=
    active_constraint_coordinates 2 U g h c a (by norm_num) hU hg hh
      ha.1 ha.2.1 ha.2.2 hli
  rcases hchart with ⟨_, hX, hA, hB, hC, haX, h0A, h0B, hwC, hXU,
    hφa, hbij, hInv, hleft, hright, hφCr, hInvCr, hpos, hfeas, hfeasInv⟩
  let φ := coordinateMap g h c a w
  let Y := A ×ˢ (B ×ˢ C)
  let y0 : (Fin q → ℝ) × ((Active h a → ℝ) × E k) := (0, (0, w a))
  have hY : IsOpen Y := hA.prod (hB.prod hC)
  have hy0 : y0 ∈ Y := ⟨h0A, h0B, hwC⟩
  have hIa : inv y0 = a := by rw [show y0 = φ a from hφa.symm]; exact hleft haX
  have hgAt := ((crOn_iff_contDiffOn 2 U g hU).mp hg).contDiffAt (hU.mem_nhds ha.1)
  have hhAt := ((crOn_iff_contDiffOn 2 U h hU).mp hh).contDiffAt (hU.mem_nhds ha.1)
  have hdg := (hgAt.differentiableAt (by norm_num)).hasFDerivAt
  have hdgs (j : Fin q) := (PiLp.hasFDerivAt_apply 2 (g a) j).comp a hdg
  have hdh := (hhAt.differentiableAt (by norm_num)).hasFDerivAt
  have hdhs (i : Fin s) := (PiLp.hasFDerivAt_apply 2 (h a) i).comp a hdh
  have hgsc (j : Fin q) : HasFDerivAt (fun x => g x j)
      (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a) a := (hdgs j).differentiableAt.hasFDerivAt
  have hhsc (i : Fin s) : HasFDerivAt (fun x => h x i)
      (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a) a := (hdhs i).differentiableAt.hasFDerivAt
  let P := (ContinuousLinearMap.pi (fun j : Fin q =>
      Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a)).prod
    ((ContinuousLinearMap.pi (fun i : Active h a =>
      Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i.val) a)).prod w.toContinuousLinearMap)
  have hdφ : HasFDerivAt φ P a :=
    (hasFDerivAt_pi.mpr (fun j => (hgsc j).sub_const (c j))).prodMk
      ((hasFDerivAt_pi.mpr (fun i : Active h a => hhsc i.val)).prodMk
        w.toContinuousLinearMap.hasFDerivAt)
  have hIAt := ((crOn_iff_contDiffOn 2 Y inv hY).mp hInvCr).contDiffAt (hY.mem_nhds hy0)
  have hdI := (hIAt.differentiableAt (by norm_num)).hasFDerivAt
  have hDP : (fderiv ℝ inv y0).comp P = ContinuousLinearMap.id ℝ (E n) := by
    have hdI' : HasFDerivAt inv (fderiv ℝ inv y0) (φ a) := by
      rw [show φ a = y0 from hφa]; exact hdI
    have hchain := hdI'.comp a hdφ
    have hid : HasFDerivAt (fun x : E n => x) ((fderiv ℝ inv y0).comp P) a := by
      apply hchain.congr_of_eventuallyEq
      filter_upwards [hX.mem_nhds haX] with x hx
      exact (hleft hx).symm
    simpa using hid.unique (hasFDerivAt_id a)
  have hPv : (P v).1 = 0 := by
    funext j
    change Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a v = 0
    change fderiv ℝ (fun x => g x j) a v = 0
    have he := (hgsc j).unique (hdgs j)
    change Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a = _ at he
    rw [show fderiv ℝ (fun x => g x j) a = _ from he]
    change (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative g a v) j = 0
    rw [hgv]
    rfl
  let line : ℝ → (Fin q → ℝ) × ((Active h a → ℝ) × E k) := fun t => y0 + t • P v
  have hline : ContDiff ℝ 2 line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : line 0 = y0 := by simp [line]
  have hdline : HasDerivAt line (P v) 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const (P v)).const_add y0
  have hlineY : ∀ᶠ t in 𝓝 (0 : ℝ), line t ∈ Y :=
    hline.continuous.continuousAt.preimage_mem_nhds (by simpa [hl0] using hY.mem_nhds hy0)
  let γ := inv ∘ line
  have hγ0 : γ 0 = a := by simp [γ, hl0, hIa]
  have hIAt' : ContDiffAt ℝ 2 inv (line 0) := by rw [hl0]; exact hIAt
  have hγ : ContDiffAt ℝ 2 γ 0 := hIAt'.comp 0 hline.contDiffAt
  have hdγ : HasDerivAt γ v 0 := by
    have H := (by rw [hl0]; exact hdI : HasFDerivAt inv (fderiv ℝ inv y0) (line 0)).comp_hasDerivAt 0 hdline
    convert H using 1
    have H := congrArg (fun T : E n →L[ℝ] E n => T v) hDP
    exact H.symm
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), g (γ t) = c ∧ ∀ i : Active h a,
      h (γ t) i.val = t * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i.val) a v := by
    filter_upwards [hlineY] with t ht
    have H := hright ht
    change φ (γ t) = line t at H
    constructor
    · ext j
      have Hj := congrArg (fun y => y.1 j) H
      change g (γ t) j - c j = (line t).1 j at Hj
      have hz : (line t).1 j = 0 := by simp [line, y0, hPv]
      rw [hz] at Hj
      exact sub_eq_zero.mp Hj
    · intro i
      have Hi := congrArg (fun y => y.2.1 i) H
      simpa [φ, coordinateMap, line, y0, P] using Hi
  have hfeasible : ∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ Feasible U g h c := by
    filter_upwards [hlineY.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    apply (hfeasInv (line t) ht).mpr
    refine ⟨?_, fun i => ?_⟩
    · simp [line, y0, hPv]
    · change 0 ≤ (y0 + t • P v).2.1 i
      simp only [Prod.snd_add, Prod.fst_add, Prod.snd_smul, Prod.fst_smul]
      change 0 ≤ (0 : ℝ) + t * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i.val) a v
      simpa only [zero_add] using mul_nonneg ht0 (hhv i)
  refine ⟨γ, hγ0, hγ, hdγ, hfeasible, he, ?_, ?_⟩
  · have H : g ∘ γ =ᶠ[𝓝 (0 : ℝ)] fun _ => c := he.mono (fun _ ht => ht.1)
    rw [H.iteratedDeriv_eq 2]
    simp only [iteratedDeriv_const, OfNat.ofNat_ne_zero, ite_false]
  · intro i
    have H : (fun t => h (γ t) i.val) =ᶠ[𝓝 (0 : ℝ)]
        (fun t => t * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i.val) a v) := he.mono (fun _ ht => ht.2 i)
    rw [H.iteratedDeriv_eq 2]
    simp [iteratedDeriv_succ, deriv_mul_const]


/-- The necessary second-order condition on the entire critical cone. -/
theorem critical_cone_necessity :
    Specs.D04.C05.CriticalConeNecessity.critical_cone_necessityType := by
  classical
  intro n q s U f g h c a lam μ hU hf hg hh hli hμ hinactive hmult hm v hv
  have ha : a ∈ Feasible U g h c := hm.1
  have hfc := (crOn_iff_contDiffOn 2 U f hU).mp hf
  have hgc := (crOn_iff_contDiffOn 2 U g hU).mp hg
  have hhc := (crOn_iff_contDiffOn 2 U h hU).mp hh
  have hgsc (j : Fin q) : ContDiffOn ℝ 2 (fun x => g x j) U := (contDiffOn_piLp 2).mp hgc j
  have hhsc (i : Fin s) : ContDiffOn ℝ 2 (fun x => h x i) U := (contDiffOn_piLp 2).mp hhc i
  have hdf := (hfc.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdg (j : Fin q) := ((hgsc j).contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdh (i : Fin s) := ((hhsc i).contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  let L := lagrangian f g h lam μ
  have hL : ContDiffOn ℝ 2 L U :=
    (hfc.sub (ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) => (hgsc j).const_smul (lam j)))).sub
      (ContDiffOn.sum (fun i (_ : i ∈ Finset.univ) => (hhsc i).const_smul (μ i)))
  have hdL : HasFDerivAt L (0 : E n →L[ℝ] ℝ) a := by
    have H := (hdf.sub (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hdg j).const_mul (lam j)))).sub
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hdh i).const_mul (μ i)))
    have hz : fderiv ℝ f a - (∑ j, lam j • fderiv ℝ (fun x => g x j) a) -
        (∑ i, μ i • fderiv ℝ (fun x => h x i) a) = 0 := by
      ext z
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply]
      change Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative f a z - (∑ j, lam j * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a z) -
        (∑ i, μ i * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a z) = 0
      rw [hmult]
      ring
    rw [hz] at H
    exact H
  obtain ⟨γ, hγ0, hγ, hdγ, hfeas, hcoords, _, _⟩ :=
    critical_direction_curve U g h c a v hU hg hh ha hli hv.1 hv.2.1
  have hgs (j : Fin q) : Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a v = 0 := by
    have hgAt := (hgc.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
    have H := (PiLp.hasFDerivAt_apply 2 (g a) j).comp a hgAt
    change fderiv ℝ (fun x => g x j) a v = 0
    have he := (hdg j).unique H
    rw [show fderiv ℝ (fun x => g x j) a = _ from he]
    change (Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative g a v) j = 0
    rw [hv.1]
    rfl
  have hμsum : (∑ i, μ i * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a v) = 0 := by
    have H := hmult v
    rw [hv.2.2] at H
    simp only [hgs, mul_zero, Finset.sum_const_zero, zero_add] at H
    exact H.symm
  have hμa : (∑ i, μ i * h a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : h a i = 0
    · rw [hi, mul_zero]
    · rw [hinactive i hi, zero_mul]
  have hvalues : ∀ᶠ t in 𝓝 (0 : ℝ), L (γ t) - L a = f (γ t) - f a := by
    filter_upwards [hcoords] with t ht
    have hsum : (∑ i, μ i * h (γ t) i) = 0 := by
      calc
        _ = ∑ i, t * (μ i * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a v) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : h a i = 0
          · rw [ht.2 ⟨i, hi⟩]; ring
          · rw [hinactive i hi]; ring
        _ = t * (∑ i, μ i * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a v) := (Finset.mul_sum _ _ _).symm
        _ = 0 := by rw [hμsum, mul_zero]
    simp only [L, lagrangian, ht.1, ha.2.1, hsum, hμa]
    ring
  have hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), L (γ 0) ≤ L (γ t) := by
    have hfmin := ((localMinimumOn_iff (Feasible U g h c) f a).mp hm).2
    have htend : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[Feasible U g h c] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa [hγ0] using hdγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · exact hfeas.filter_mono (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    filter_upwards [htend.eventually hfmin, hvalues.filter_mono nhdsWithin_le_nhds] with t ht hvv
    rw [hγ0]
    linarith
  have hLat : ContDiffAt ℝ 2 L a := hL.contDiffAt (hU.mem_nhds ha.1)
  have hLγ : ContDiffAt ℝ 2 (L ∘ γ) 0 :=
    (by rw [hγ0]; exact hLat : ContDiffAt ℝ 2 L (γ 0)).comp 0 hγ
  have hdLγ : deriv (L ∘ γ) 0 = 0 := by
    have H := (by rw [hγ0]; exact hdL : HasFDerivAt L 0 (γ 0)).comp_hasDerivAt 0 hdγ
    simpa using H.deriv
  have hnonneg := CriticalCone.right_second_nonneg hLγ hdLγ hmin
  have hsecond := iteratedDeriv_vcomp_two
    (by rw [hγ0]; exact hLat : ContDiffAt ℝ 2 L (γ 0)) hγ
  rw [hγ0, hdγ.deriv, hdL.fderiv, ContinuousLinearMap.zero_apply, add_zero] at hsecond
  change 0 ≤ iteratedFDeriv ℝ 2 L a (fun _ => v)
  rwa [hsecond] at hnonneg

end D04
