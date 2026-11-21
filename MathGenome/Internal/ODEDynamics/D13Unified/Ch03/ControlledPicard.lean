import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.ControlledPicard
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open Set Metric Filter MeasureTheory Function
open scoped Topology NNReal

namespace D13Unified.Ch03.ControlledPicard
universe u
open Specs.D13Unified.Ch03.ControlledPicard
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Convert the shared norm estimate into the library metric estimate. -/
lemma state_lipschitz {f : ℝ → E → E} {T : Set ℝ} {B : Set E} {L : ℝ}
    (hL : 0 ≤ L) (hf : StateLipschitzOn f T B L) {t : ℝ} (ht : t ∈ T) :
    LipschitzOnWith (NNReal.mk L hL) (f t) B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [dist_eq_norm, NNReal.coe_mk] using hf t ht x hx y hy

/-- The controlled-box Picard theorem, including the actual Picard sequence. -/
theorem controlled_picard : controlledPicardExpected.{u} := by
  intro E _ _ _ F s ξ a b M L h hM hL hh hha hMh hLh hQ hbound hlip
  have hb : 0 ≤ b := (mul_nonneg hM hh.le).trans hMh
  have hs : s ∈ Icc (s-h) (s+h) := ⟨by linarith, by linarith⟩
  have hsub : Icc (s-h) (s+h) ⊆ Icc (s-a) (s+a) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let t₀ : Icc (s-h) (s+h) := ⟨s, hs⟩
  have hPic : IsPicardLindelof F.eval t₀ ξ (NNReal.mk b hb) 0 (NNReal.mk M hM) (NNReal.mk L hL) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact state_lipschitz hL hlip (hsub ht)
    · intro z hz
      exact F.continuousOn_eval.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => hQ ⟨hsub ht, hz⟩)
    · intro t ht z hz
      exact hbound t (hsub ht) z hz
    · change M * max ((s+h)-s) (s-(s-h)) ≤ b - (0 : ℝ)
      simpa using hMh
  have hξ : ξ ∈ closedBall ξ (0 : ℝ≥0) := mem_closedBall_self le_rfl
  let N := _root_.ODE.FunSpace.next hPic hξ
  have hc : ContractingWith (NNReal.mk (L*h) (mul_nonneg hL hh.le)) N := by
    refine ⟨hLh, LipschitzWith.of_dist_le_mul ?_⟩
    intro α β
    have he := _root_.ODE.FunSpace.dist_iterate_next_iterate_next_le hPic hξ α β 1
    simpa [N, t₀] using he
  let α := hc.fixedPoint N
  have hfix : IsFixedPt N α := hc.fixedPoint_isFixedPt
  let x := α.compProj
  have hxball : MapsTo x (Icc (s-h) (s+h)) (closedBall ξ b) := by
    intro t ht
    exact α.compProj_mem_closedBall hPic.mul_max_le
  have hxgraph : ∀ t ∈ Icc (s-h) (s+h), (t, x t) ∈ F.domain :=
    fun t ht => hQ ⟨hsub ht, hxball ht⟩
  have hxeq : ∀ t ∈ Icc (s-h) (s+h),
      x t = ξ + ∫ r in s..t, F.eval r (x r) := by
    intro t ht
    dsimp only [x]
    rw [_root_.ODE.FunSpace.compProj_of_mem (α := α) ht]
    exact (_root_.ODE.FunSpace.isFixedPt_next_iff hPic hξ).mp hfix ⟨t, ht⟩
  have hx : IsIVPOn F (controlledInterval s h hh) x s ξ :=
    (ivp_iff_integral F (controlledInterval s h hh) x s ξ hs
      α.continuous_compProj.continuousOn hxgraph).mpr hxeq
  let α₀ : _root_.ODE.FunSpace t₀ ξ 0 (NNReal.mk M hM) := default
  have hiter : ∀ n : ℕ, ∀ t ∈ Icc (s-h) (s+h),
      picardIterate F s ξ n t = ((N^[n]) α₀).compProj t := by
    intro n
    induction n with
    | zero => intro t ht; rfl
    | succ n ih =>
      intro t ht
      rw [Function.iterate_succ_apply', _root_.ODE.FunSpace.compProj_of_mem ht]
      change ξ + (∫ r in s..t, F.eval r (picardIterate F s ξ n r)) =
        ξ + (∫ r in s..t, F.eval r (((N^[n]) α₀).compProj r))
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      exact congrArg (F.eval r) (ih r (uIcc_subset_Icc hs ht hr))
  refine ⟨x, hx, hxball, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev := (Metric.tendsto_atTop.mp (hc.tendsto_iterate_fixedPoint α₀)) ε hε
    obtain ⟨n, hn⟩ := hev
    filter_upwards [eventually_ge_atTop n] with j hj t ht
    rw [hiter j t ht]
    have hd : dist (α.toContinuousMap ⟨t, ht⟩)
        (((N^[j]) α₀).toContinuousMap ⟨t, ht⟩) ≤ dist α ((N^[j]) α₀) :=
      ContinuousMap.dist_apply_le_dist (f := α.toContinuousMap)
        (g := ((N^[j]) α₀).toContinuousMap) ⟨t, ht⟩
    have hjε := hn j hj
    rw [dist_comm] at hjε
    apply lt_of_le_of_lt (b := dist α ((N^[j]) α₀)) _ hjε
    change dist (α.compProj t) (((N^[j]) α₀).compProj t) ≤ _
    rw [_root_.ODE.FunSpace.compProj_of_mem ht, _root_.ODE.FunSpace.compProj_of_mem ht]
    exact hd
  · intro y hy hyball
    apply ODE_solution_unique_of_mem_Icc
      (s := fun _ => closedBall ξ b) (K := (NNReal.mk L hL))
      (fun t ht => state_lipschitz hL hlip (hsub (Ioo_subset_Icc_self ht)))
      (show s ∈ Ioo (s-h) (s+h) from ⟨by linarith, by linarith⟩)
      hy.1.1
      (fun t ht => (hy.1.2.2 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hyball (Ioo_subset_Icc_self ht))
      hx.1.1
      (fun t ht => (hx.1.2.2 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hxball (Ioo_subset_Icc_self ht))
      (hy.2.2.trans hx.2.2.symm)

/-- Local state Lipschitz control gives uniqueness on the entire overlap of
any two classical solution intervals, with either sign of elapsed time. -/
theorem overlap_uniqueness : overlapUniquenessExpected.{u} := by
  intro E _ _ _ F hF I J x y s ξ hx hy
  let S := I.carrier ∩ J.carrier
  have hlocal (t : S) (heq : x t = y t) : x =ᶠ[𝓝 (t : ℝ)] y := by
    obtain ⟨a, b, L, ha, hb, hL, _, hLip⟩ := hF t (x t) (hx.1.2.1 t t.2.1)
    have htime : ∀ᶠ r in 𝓝 (t : ℝ), r ∈ ball (t : ℝ) a :=
      ball_mem_nhds _ ha
    have hxball : ∀ᶠ r in 𝓝 (t : ℝ), x r ∈ ball (x t) b :=
      (hx.1.1.continuousOn.continuousAt (I.isOpen.mem_nhds t.2.1)).eventually
        (ball_mem_nhds _ hb)
    have hyball : ∀ᶠ r in 𝓝 (t : ℝ), y r ∈ ball (x t) b := by
      rw [heq]
      exact (hy.1.1.continuousOn.continuousAt (J.isOpen.mem_nhds t.2.2)).eventually
        (ball_mem_nhds _ hb)
    have hxd : ∀ᶠ r in 𝓝 (t : ℝ), HasDerivAt x (F.eval r (x r)) r := by
      filter_upwards [I.isOpen.mem_nhds t.2.1] with r hr
      exact hx.1.2.2 r hr
    have hyd : ∀ᶠ r in 𝓝 (t : ℝ), HasDerivAt y (F.eval r (y r)) r := by
      filter_upwards [J.isOpen.mem_nhds t.2.2] with r hr
      exact hy.1.2.2 r hr
    exact ODE_solution_unique_of_eventually
      (s := fun _ => ball (x t) b) (K := NNReal.mk L hL)
      (htime.mono (fun r hr => state_lipschitz hL hLip hr))
      (hxd.and hxball) (hyd.and hyball) heq
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (I.ordConnected.inter J.ordConnected).isPreconnected
  have hclosed : IsClosed {t : S | x t = y t} :=
    isClosed_eq (hx.1.1.continuousOn.mono inter_subset_left).domRestrict
      (hy.1.1.continuousOn.mono inter_subset_right).domRestrict
  have hopen : IsOpen {t : S | x t = y t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (hlocal t ht).comp_tendsto (continuous_subtype_val.tendsto t)
  have hall : {t : S | x t = y t} = univ :=
    (show IsClopen {t : S | x t = y t} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨s, hx.2.1, hy.2.1⟩, hx.2.2.trans hy.2.2.symm⟩
  intro t ht
  exact (show (⟨t, ht⟩ : S) ∈ {t : S | x t = y t} from hall ▸ mem_univ _)

end D13Unified.Ch03.ControlledPicard
