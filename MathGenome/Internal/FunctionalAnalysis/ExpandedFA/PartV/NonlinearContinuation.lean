import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearContinuation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.NonlinearVolterra
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-! A bounded Lipschitz cutoff permits a global auxiliary Volterra solution.
Uniqueness identifies it with any bounded old solution. Its continuity then
keeps the cutoff equal to one beyond the alleged maximal endpoint. This proof
works for every positive power-kernel order; the upstream singular existence
proof uses integrability of the kernel and dominated convergence. -/
noncomputable section
namespace ExpandedFA.PartV.NonlinearContinuation
open Set MeasureTheory Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]

/-- A scalar cutoff equal to one on the radius `R` ball and zero outside the
radius `R+1` ball. -/
def cutoff (R : ℝ) (z : E) : ℝ := max 0 (min 1 (R+1-‖z‖))

lemma cutoff_nonneg (R : ℝ) (z : E) : 0 ≤ cutoff R z := le_max_left _ _
lemma cutoff_le_one (R : ℝ) (z : E) : cutoff R z ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)
lemma cutoff_eq_one {R : ℝ} {z : E} (hz : ‖z‖ ≤ R) : cutoff R z = 1 := by
  simp [cutoff, min_eq_left (by linarith : 1 ≤ R+1-‖z‖)]
lemma cutoff_eq_zero {R : ℝ} {z : E} (hz : R+1 ≤ ‖z‖) : cutoff R z = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

lemma lipschitz_cutoff (R : ℝ) : LipschitzWith 1 (cutoff R : E → ℝ) := by
  have hn : LipschitzWith 1 (fun z : E => R+1-‖z‖) := by
    simpa only [zero_add] using (LipschitzWith.const (R+1)).sub lipschitzWith_one_norm
  change LipschitzWith 1 (fun z : E => max 0 (min 1 (R+1-‖z‖)))
  simpa only [max_self, zero_le_one, max_eq_right] using
    (LipschitzWith.const 0).max ((LipschitzWith.const 1).min hn)

variable [NormedSpace ℝ E]

/-- A globally bounded, globally Lipschitz auxiliary nonlinearity. -/
def truncate {T : ℝ} (R : ℝ) (G : C(volterraTriangle 0 T × E,E)) :
    C(volterraTriangle 0 T × E,E) :=
  ⟨fun p => cutoff R p.2 • G p,
    (((lipschitz_cutoff R).continuous).comp continuous_snd).smul G.continuous⟩

lemma truncate_eq {T R : ℝ} (G : C(volterraTriangle 0 T × E,E))
    (p : volterraTriangle 0 T) {z : E} (hz : ‖z‖ ≤ R) :
    truncate R G (p,z) = G (p,z) := by simp [truncate, cutoff_eq_one hz]

lemma truncate_bound {T R B : ℝ} (G : C(volterraTriangle 0 T × E,E))
    (hB : 0 ≤ B) (hbound : ∀ p z, ‖z‖ ≤ R+1 → ‖G (p,z)‖ ≤ B)
    (p : volterraTriangle 0 T) (z : E) : ‖truncate R G (p,z)‖ ≤ B := by
  by_cases hz : ‖z‖ ≤ R+1
  · change ‖cutoff R z • G (p,z)‖ ≤ B
    rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R z)]
    exact (mul_le_mul_of_nonneg_left (hbound p z hz) (cutoff_nonneg R z)).trans
      (mul_le_of_le_one_left hB (cutoff_le_one R z))
  · simp [truncate, cutoff_eq_zero (le_of_lt (lt_of_not_ge hz)), hB]

lemma truncate_lipschitz {T R B L : ℝ} (G : C(volterraTriangle 0 T × E,E))
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ p z, ‖z‖ ≤ R+1 → ‖G (p,z)‖ ≤ B)
    (hlip : ∀ p z w, ‖z‖ ≤ R+1 → ‖w‖ ≤ R+1 →
      ‖G (p,z)-G (p,w)‖ ≤ L * ‖z-w‖)
    (p : volterraTriangle 0 T) (z w : E) :
    ‖truncate R G (p,z)-truncate R G (p,w)‖ ≤ (B+L) * ‖z-w‖ := by
  have hcase (z w : E) (hz : ‖z‖ ≤ R+1) (hw : ‖w‖ ≤ R+1) :
      ‖truncate R G (p,z)-truncate R G (p,w)‖ ≤ (B+L)*‖z-w‖ := by
    have hc' : ‖cutoff R z-cutoff R w‖ ≤ ‖z-w‖ := by
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using (lipschitz_cutoff R).dist_le_mul z w
    have he : cutoff R z • G (p,z)-cutoff R w • G (p,w) =
        (cutoff R z-cutoff R w) • G (p,z) + cutoff R w • (G (p,z)-G (p,w)) := by
      simp only [sub_smul, smul_sub]; abel
    change ‖cutoff R z • G (p,z)-cutoff R w • G (p,w)‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖(cutoff R z-cutoff R w) • G (p,z)‖ +
          ‖cutoff R w • (G (p,z)-G (p,w))‖ := norm_add_le _ _
      _ ≤ ‖z-w‖*B + 1*(L*‖z-w‖) := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (cutoff_nonneg R w)]
        exact add_le_add (mul_le_mul hc' (hbound p z hz) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (cutoff_le_one R w) (hlip p z w hz hw) (norm_nonneg _) zero_le_one)
      _ = _ := by ring
  have hout (z w : E) (hz : ‖z‖ ≤ R+1) (hw : R+1 ≤ ‖w‖) :
      ‖truncate R G (p,z)-truncate R G (p,w)‖ ≤ (B+L)*‖z-w‖ := by
    have hc' : ‖cutoff R z‖ ≤ ‖z-w‖ := by
      simpa [cutoff_eq_zero hw, dist_eq_norm] using (lipschitz_cutoff R).dist_le_mul z w
    simp only [truncate, ContinuousMap.coe_mk, cutoff_eq_zero hw, zero_smul, sub_zero, norm_smul]
    exact (mul_le_mul hc' (hbound p z hz) (norm_nonneg _) (norm_nonneg _)).trans
      (by nlinarith [mul_nonneg hL (norm_nonneg (z-w))])
  by_cases hz : ‖z‖ ≤ R+1
  · by_cases hw : ‖w‖ ≤ R+1
    · exact hcase z w hz hw
    · exact hout z w hz (le_of_lt (lt_of_not_ge hw))
  · by_cases hw : ‖w‖ ≤ R+1
    · simpa only [norm_sub_rev] using hout w z hw (le_of_lt (lt_of_not_ge hz))
    · simp [truncate, cutoff_eq_zero (le_of_lt (lt_of_not_ge hz)),
        cutoff_eq_zero (le_of_lt (lt_of_not_ge hw)), mul_nonneg (add_nonneg hB hL) (norm_nonneg (z-w))]

/-- Constant continuation outside a closed interval, used only to express
integrals as integrals of ordinary functions of a real variable. -/
def extend {h : ℝ} (hh : 0 ≤ h) (u : C(VolterraInterval 0 h,E)) : ℝ → E :=
  fun s => u (Set.projIcc 0 h hh s)

omit [NormedSpace ℝ E] in
lemma extend_coe {h : ℝ} (hh : 0 ≤ h) (u : C(VolterraInterval 0 h,E))
    (t : VolterraInterval 0 h) : extend hh u t = u t := by
  simp [extend, Set.projIcc_of_mem]

omit [NormedSpace ℝ E] in
lemma continuous_extend {h : ℝ} (hh : 0 ≤ h) (u : C(VolterraInterval 0 h,E)) :
    Continuous (extend hh u) := u.continuous.comp continuous_projIcc

def ClosedSolution {h : ℝ} (hh : 0 ≤ h) (α : ℝ)
    (f : C(VolterraInterval 0 h,E)) (G : C(volterraTriangle 0 h × E,E))
    (u : C(VolterraInterval 0 h,E)) : Prop :=
  ∀ t, equation α f G (extend hh u) t

def ballKernel {h R : ℝ} (G : C(volterraTriangle 0 h × E,E)) :
    C(volterraTriangle 0 h × Metric.closedBall (0 : E) R,E) :=
  ⟨fun p => G (p.1,p.2.val), G.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

lemma ball_solution_iff {h R α : ℝ} (hh : 0 ≤ h)
    (f : C(VolterraInterval 0 h,E)) (G : C(volterraTriangle 0 h × E,E))
    (u : NonlinearVolterra.Ball 0 h (0 : E) R) :
    NonlinearVolterra.WeaklySingular.IsSolution hh α f (ballKernel G) u ↔
      ClosedSolution hh α f G u.val := by
  unfold NonlinearVolterra.WeaklySingular.IsSolution ClosedSolution equation
    NonlinearVolterra.WeaklySingular.rhs
  simp only [extend_coe]
  rfl

section Complete
variable [CompleteSpace E]

lemma exists_closedSolution {h α B L : ℝ} (hh : 0 ≤ h) (hα : 0 < α)
    (f : C(VolterraInterval 0 h,E)) (G : C(volterraTriangle 0 h × E,E))
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hbound : ∀ p z, ‖G (p,z)‖ ≤ B)
    (hlip : ∀ p z w, ‖G (p,z)-G (p,w)‖ ≤ L * ‖z-w‖) :
    ∃ u : C(VolterraInterval 0 h,E), ClosedSolution hh α f G u := by
  let R := ‖f‖ + B * h ^ α / α
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _)
    (div_nonneg (mul_nonneg hB (Real.rpow_nonneg hh _)) hα.le)
  obtain ⟨_, _, u, hu, _⟩ := nonlinear_volterra_weakly_singular ℝ E α h R hα hh hR
    0 f (ballKernel G) B L hB hL (fun p z => hbound p z)
    (fun p z w => hlip p z w) (by simp [R])
  exact ⟨u.val, (ball_solution_iff hh f G u).mp hu⟩

lemma closedSolution_unique {h α B L : ℝ} (hh : 0 ≤ h) (hα : 0 < α)
    (f : C(VolterraInterval 0 h,E)) (G : C(volterraTriangle 0 h × E,E))
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hbound : ∀ p z, ‖G (p,z)‖ ≤ B)
    (hlip : ∀ p z w, ‖G (p,z)-G (p,w)‖ ≤ L * ‖z-w‖)
    (u v : C(VolterraInterval 0 h,E))
    (hu : ClosedSolution hh α f G u) (hv : ClosedSolution hh α f G v) : u = v := by
  let R := ‖u‖ + ‖v‖ + ‖f‖ + B * h ^ α / α
  have hm : 0 ≤ B * h ^ α / α :=
    div_nonneg (mul_nonneg hB (Real.rpow_nonneg hh _)) hα.le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRu : ‖u‖ ≤ R := by dsimp [R]; linarith [norm_nonneg v, norm_nonneg f]
  have hRv : ‖v‖ ≤ R := by dsimp [R]; linarith [norm_nonneg u, norm_nonneg f]
  let u' : NonlinearVolterra.Ball 0 h (0 : E) R :=
    ⟨u, by simpa [Metric.mem_closedBall, dist_eq_norm] using hRu⟩
  let v' : NonlinearVolterra.Ball 0 h (0 : E) R :=
    ⟨v, by simpa [Metric.mem_closedBall, dist_eq_norm] using hRv⟩
  have hinv : ‖f - ContinuousMap.const _ (0 : E)‖ + B * h ^ α / α ≤ R := by
    simp only [ContinuousMap.const_zero, sub_zero]
    dsimp [R]; linarith [norm_nonneg u, norm_nonneg v]
  obtain ⟨_, _, w, _, hw, _⟩ := nonlinear_volterra_weakly_singular ℝ E α h R hα hh hR
    0 f (ballKernel G) B L hB hL (fun p z => hbound p z)
    (fun p z w => hlip p z w) hinv
  exact congrArg Subtype.val ((hw u' ((ball_solution_iff hh f G u').mpr hu)).trans
    (hw v' ((ball_solution_iff hh f G v').mpr hv)).symm)

end Complete

/-- The order-one predicate is exactly the regular integral equation. -/
lemma equation_one {T : ℝ} (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (u : ℝ → E)
    (t : VolterraInterval 0 T) :
    equation 1 f G u t ↔
      u t = f t + ∫ s in Ioc 0 (t : ℝ), G (volterraRetraction t s,u s) := by
  simp [equation]

/-- Equation transport needs agreement only on the integration history. -/
lemma equation_congr {T α : ℝ} (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (u v : ℝ → E)
    (t : VolterraInterval 0 T) (he : EqOn u v (Icc 0 (t : ℝ))) :
    equation α f G u t ↔ equation α f G v t := by
  have hi : (∫ s in Ioc 0 (t : ℝ),
      ((t : ℝ)-s) ^ (α-1) • G (volterraRetraction t s,u s)) =
      ∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) • G (volterraRetraction t s,v s) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [he ⟨hs.1.le,hs.2⟩]
  unfold equation
  rw [hi, he ⟨t.property.1,le_rfl⟩]

/-- Restriction of the time triangle without changing its points. -/
def triangleInclusion {c T : ℝ} (hcT : c ≤ T) :
    C(volterraTriangle 0 c,volterraTriangle 0 T) :=
  ⟨fun p => ⟨p.val,p.property.1,p.property.2.1,p.property.2.2.trans hcT⟩,
    continuous_subtype_val.subtype_mk _⟩

def intervalInclusion {c T : ℝ} (hcT : c ≤ T) :
    C(VolterraInterval 0 c,VolterraInterval 0 T) :=
  ⟨fun t => ⟨t.val,t.property.1,t.property.2.trans hcT⟩,
    continuous_subtype_val.subtype_mk _⟩

def restrictKernel {c T : ℝ} (hcT : c ≤ T)
    (G : C(volterraTriangle 0 T × E,E)) : C(volterraTriangle 0 c × E,E) :=
  G.comp ((triangleInclusion hcT).prodMap (ContinuousMap.id E))

def restrictCurve {c T : ℝ} (hcT : c ≤ T) (u : C(VolterraInterval 0 T,E)) :
    C(VolterraInterval 0 c,E) := u.comp (intervalInclusion hcT)

lemma equation_restrict {c T α : ℝ} (hcT : c ≤ T)
    (f : C(VolterraInterval 0 T,E)) (G : C(volterraTriangle 0 T × E,E))
    (u : ℝ → E) (t : VolterraInterval 0 c) :
    equation α (restrictCurve hcT f) (restrictKernel hcT G) u t ↔
      equation α f G u (intervalInclusion hcT t) := Iff.rfl

lemma restrict_closedSolution {c T α : ℝ} (hc : 0 ≤ c) (hcT : c ≤ T)
    (f : C(VolterraInterval 0 T,E)) (G : C(volterraTriangle 0 T × E,E))
    (u : C(VolterraInterval 0 T,E)) (hu : ClosedSolution (hc.trans hcT) α f G u) :
    ClosedSolution hc α (restrictCurve hcT f) (restrictKernel hcT G) (restrictCurve hcT u) := by
  intro t
  rw [equation_restrict]
  apply (equation_congr f G _ _ _ ?_).mpr (hu (intervalInclusion hcT t))
  intro s hs
  have hsc : s ∈ Icc 0 c := ⟨hs.1,hs.2.trans t.property.2⟩
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hsc.2.trans hcT⟩
  simp only [extend, Set.projIcc_of_mem _ hsc, Set.projIcc_of_mem _ hsT]
  rfl

/-- Compare the bounded old solution with the auxiliary global solution.
Every comparison takes place on a compact prefix strictly before `b`. -/
lemma agrees_before [CompleteSpace E] {T b α R B L : ℝ} (hT : 0 ≤ T) (hbT : b ≤ T)
    (hα : 0 < α) (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (u : ℝ → E)
    (hu : IsSolution α f G b u) (hboundu : ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ p z, ‖truncate R G (p,z)‖ ≤ B)
    (hlip : ∀ p z w, ‖truncate R G (p,z)-truncate R G (p,w)‖ ≤ L*‖z-w‖)
    (w : C(VolterraInterval 0 T,E))
    (hw : ClosedSolution hT α f (truncate R G) w) :
    EqOn u (extend hT w) (Ico 0 b) := by
  intro t ht
  let c := (t+b)/2
  have htc : t ≤ c := by dsimp [c]; linarith [ht.2]
  have hcb : c < b := by dsimp [c]; linarith [ht.2]
  have hc : 0 ≤ c := ht.1.trans htc
  have hcT : c ≤ T := hcb.le.trans hbT
  let v : C(VolterraInterval 0 c,E) :=
    ⟨fun s => u s, (hu.1.mono (fun s hs => ⟨hs.1,hs.2.trans_lt hcb⟩)).domRestrict⟩
  have hv : ClosedSolution hc α (restrictCurve hcT f)
      (restrictKernel hcT (truncate R G)) v := by
    intro s
    rw [equation_restrict]
    have hsu := hu.2 (intervalInclusion hcT s) (s.property.2.trans_lt hcb)
    have hsTrunc : equation α f (truncate R G) u (intervalInclusion hcT s) := by
      unfold equation at hsu ⊢
      rw [hsu]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      dsimp only
      rw [truncate_eq G _ (hboundu r ⟨hr.1.le,hr.2.trans_lt (s.property.2.trans_lt hcb)⟩)]
    apply (equation_congr f (truncate R G) _ _ _ ?_).mpr hsTrunc
    intro r hr
    simp only [extend, Set.projIcc_of_mem hc ⟨hr.1,hr.2.trans s.property.2⟩]
    rfl
  have hwc := restrict_closedSolution hc hcT f (truncate R G) w hw
  have he : v = restrictCurve hcT w := closedSolution_unique hc hα _ _ hB hL
    (fun p z => hbound (triangleInclusion hcT p) z)
    (fun p z w => hlip (triangleInclusion hcT p) z w) v _ hv hwc
  have he' := congrArg (fun v : C(VolterraInterval 0 c,E) => v ⟨t,ht.1,htc⟩) he
  change u t = w ⟨t,ht.1,htc.trans hcT⟩ at he'
  simpa only [extend, Set.projIcc_of_mem hT ⟨ht.1,htc.trans hcT⟩] using he'

/-- A bounded solution has a strict continuation. This stronger form does
not require time uniformity on unused states: the cutoff solution's own
continuity supplies the endpoint limit and the short extension. -/
lemma bounded_extension [CompleteSpace E] {T b α M : ℝ} (hb : 0 < b) (hbT : b < T) (hα : 0 < α)
    (f : C(VolterraInterval 0 T,E)) (G : C(volterraTriangle 0 T × E,E))
    (hG : LocalBounds G) (u : ℝ → E) (hu : IsSolution α f G b u)
    (hM : ∀ t ∈ Ico 0 b, ‖u t‖ ≤ M) :
    ∃ c : ℝ, b < c ∧ c ≤ T ∧
      ∃ v : ℝ → E, IsSolution α f G c v ∧ EqOn u v (Ico 0 b) := by
  have hT : 0 ≤ T := (hb.trans hbT).le
  have hM0 : 0 ≤ M := (norm_nonneg (u 0)).trans (hM 0 ⟨le_rfl,hb⟩)
  let R := M+1
  obtain ⟨B,L,hB,hL,hbound,hlip⟩ := hG (R+1) (by dsimp [R]; linarith)
  have hB' := truncate_bound G hB hbound
  have hL' := truncate_lipschitz G hB hL hbound hlip
  obtain ⟨w,hw⟩ := exists_closedSolution hT hα f (truncate R G) hB (add_nonneg hB hL) hB' hL'
  have he : EqOn u (extend hT w) (Ico 0 b) :=
    agrees_before hT hbT.le hα f G u hu
      (fun t ht => (hM t ht).trans (by dsimp [R]; linarith))
      hB (add_nonneg hB hL) hB' hL' w hw
  have hcM : IsClosed {t : ℝ | ‖extend hT w t‖ ≤ M} :=
    isClosed_le (continuous_extend hT w).norm continuous_const
  have hwb : ‖extend hT w b‖ ≤ M := by
    apply closure_minimal (fun t ht => ?_) hcM (show b ∈ closure (Ico 0 b) by
      rw [closure_Ico hb.ne]; exact ⟨hb.le,le_rfl⟩)
    change ‖extend hT w t‖ ≤ M
    rw [← he ht]
    exact hM t ht
  have hnear : ∀ᶠ t in 𝓝 b, ‖extend hT w t‖ < R :=
    (continuous_extend hT w).norm.continuousAt.eventually
      (gt_mem_nhds (show ‖extend hT w b‖ < R by dsimp [R]; linarith))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let c := min T (b+δ/2)
  have hbc : b < c := lt_min hbT (by linarith)
  have hcT : c ≤ T := min_le_left _ _
  have hcm : c ≤ b+δ/2 := min_le_right _ _
  have hnorm : ∀ t ∈ Ico 0 c, ‖extend hT w t‖ ≤ R := by
    intro t ht
    by_cases htb : t < b
    · rw [← he ⟨ht.1,htb⟩]
      exact (hM t ⟨ht.1,htb⟩).trans (by dsimp [R]; linarith)
    · apply (hnear ?_).le
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt htb))]
      linarith [ht.2]
  refine ⟨c,hbc,hcT,extend hT w,⟨(continuous_extend hT w).continuousOn,?_⟩,he⟩
  intro t ht
  have hwt := hw t
  unfold equation at hwt ⊢
  rw [hwt]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [truncate_eq G _ (hnorm s ⟨hs.1.le,hs.2.trans_lt ht⟩)]

/-- The blow-up alternative, retaining exactly the source's time-uniformity
hypothesis. The proof actually establishes the stronger bounded-extension
lemma above under the other stated hypotheses alone. -/
theorem nonlinear_continuation : Spec.ContinuationTheorem := by
  intro 𝕜 E _ _ _ _ α T b hα hb hbT f G u
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  intro hG _hTime hmax M
  by_contra h
  push Not at h
  obtain ⟨c,hbc,hcT,v,hv,he⟩ := bounded_extension hb hbT hα f G hG u hmax.1 h
  exact hmax.2 c hbc hcT ⟨v,hv,he⟩

omit [NormedSpace ℝ E] in
lemma uniformTimeOnBalls_of_proper [ProperSpace E] {T : ℝ}
    (G : C(volterraTriangle 0 T × E,E)) : UniformTimeOnBalls G := by
  intro R _hR ε hε
  let : CompactSpace (Metric.closedBall (0 : E) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let H : C(volterraTriangle 0 T × Metric.closedBall (0 : E) R,E) :=
    ⟨fun p => G (p.1,p.2.val), G.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  obtain ⟨δ,hδ,hH⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous H.continuous) ε hε
  refine ⟨δ,hδ,?_⟩
  intro p q z hz hpq
  have hz' : z ∈ Metric.closedBall (0 : E) R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  exact hH (a := (p,⟨z,hz'⟩)) (b := (q,⟨z,hz'⟩)) (by simpa using hpq)

/-- Compact finite-dimensional cylinders provide the required uniformity,
for both real and complex normed spaces. -/
theorem finiteDimensional_uniformTime : Spec.FiniteDimensionalUniformity := by
  intro 𝕜 E _ _ _ _ T G
  let : ProperSpace E := FiniteDimensional.proper 𝕜 E
  exact uniformTimeOnBalls_of_proper G

end ExpandedFA.PartV.NonlinearContinuation
