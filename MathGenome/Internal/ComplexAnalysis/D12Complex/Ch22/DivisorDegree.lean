import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.DivisorDegree
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.EllipticResidueSum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.EntireEllipticConstant
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.LogarithmicDerivative
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace D12Complex.DivisorDegree
open TorusSurface

lemma logDeriv_periodic {ω₁ ω₂ : ℂ} {f : ℂ → ℂ} (hf : Periodic ω₁ ω₂ f) :
    Periodic ω₁ ω₂ (logDeriv f) := by
  intro z l hl
  have he : (fun w => f (w + l)) = f := funext (fun w => hf w l hl)
  have hd : deriv f (z + l) = deriv f z := by
    rw [← deriv_comp_add_const, he]
  simp only [logDeriv_apply, hd, hf z l hl]

lemma residue_logDeriv {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (ho : meromorphicOrderAt f a ≠ ⊤) :
    Residue.residue (logDeriv f) a = ((meromorphicOrderAt f a).untop₀ : ℂ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho
  obtain ⟨h, hh, he⟩ := LogarithmicDerivative.expansion_germ hf hm.symm
  have he' := eventually_nhdsWithin_iff.mp he
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hh.eventually_analyticAt.and he')
  have hres := LogarithmicDerivative.residue_of_expansion hr
    (show HolomorphicOn (Metric.ball a r) h from
      ⟨Metric.isOpen_ball, fun z hz => (hball (Metric.mem_ball.mp hz)).1.differentiableAt⟩)
    (show ∀ z ∈ puncturedDisk a r, logDeriv f z = (m : ℂ) / (z - a) + h z from by
      intro z hz
      exact (hball (by simpa only [dist_eq_norm] using hz.2)).2
        (sub_ne_zero.mp (norm_pos_iff.mp hz.1)))
  simpa [← hm] using hres

lemma logDeriv_pole_iff {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (ho : meromorphicOrderAt f a ≠ ⊤) :
    a ∈ EllipticResidueSum.poleSet (logDeriv f) ↔ meromorphicOrderAt f a ≠ 0 := by
  by_cases hz : meromorphicOrderAt f a = 0
  · simp only [hz, ne_eq, not_true_eq_false, iff_false]
    exact not_lt.mpr (meromorphicOrderAt_logDeriv_nonneg hf hz)
  · have h := meromorphicOrderAt_logDeriv_eq_neg_one hf hz ho
    simp only [EllipticResidueSum.poleSet, mem_ofPred_eq, h, iff_true_intro hz]
    exact iff_true_intro (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0))

/-- Residue cancellation gives equal effective divisors for a nonzero germ
at every point. Nonconstancy is needed later only for positivity and shifts. -/
lemma effective_divisors {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {f : ℂ → ℂ} (hm : ∀ a, MeromorphicAt f a) (hf : Periodic ω₁ ω₂ f)
    (ho : ∀ a, meromorphicOrderAt f a ≠ ⊤) :
    ∃ Z P : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a, Z (projection ω₁ ω₂ a) = (meromorphicOrderAt f a).untop₀.toNat ∧
        P (projection ω₁ ω₂ a) = (-(meromorphicOrderAt f a).untop₀).toNat) ∧
      Z.sum (fun _ n => n) = P.sum (fun _ n => n) := by
  classical
  obtain ⟨s, hs⟩ := EllipticResidueSum.exists_complete_representatives ω₁ ω₂ h₁ h₂
    (logDeriv f) (fun a => (hm a).logDeriv) (logDeriv_periodic hf)
  obtain ⟨k, hk, _⟩ := TorusSurface.descent ω₁ ω₂ ℤ
    (fun a => (meromorphicOrderAt f a).untop₀)
    (fun a l hl => congrArg WithTop.untop₀ (EllipticResidueSum.order_translation hf a l hl))
  have hk' (a : ℂ) : k (projection ω₁ ω₂ a) = (meromorphicOrderAt f a).untop₀ := congrFun hk a
  let t := s.image (projection ω₁ ω₂)
  have hsupport (q) (hq : k q ≠ 0) : q ∈ t := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change k (projection ω₁ ω₂ a) ≠ 0 at hq
    change projection ω₁ ω₂ a ∈ t
    have ha : a ∈ EllipticResidueSum.poleSet (logDeriv f) :=
      (logDeriv_pole_iff (hm a) (ho a)).mpr (by intro hz; simp [hk', hz] at hq)
    have himage : projection ω₁ ω₂ a ∈ EllipticResidueSum.poleClasses ω₁ ω₂ (logDeriv f) :=
      ⟨a, ha, rfl⟩
    rw [← hs.2.2] at himage
    obtain ⟨b, hb, hba⟩ := himage
    exact Finset.mem_image.mpr ⟨b, hb, hba⟩
  let Z := Finsupp.onFinset t (fun q => (k q).toNat) (fun q hq => hsupport q (by
    intro h; simp [h] at hq))
  let P := Finsupp.onFinset t (fun q => (-k q).toNat) (fun q hq => hsupport q (by
    intro h; simp [h] at hq))
  refine ⟨Z, P, fun a => by simp [Z, P, hk'], ?_⟩
  have hsum : ∑ a ∈ s, (meromorphicOrderAt f a).untop₀ = 0 := by
    have hres := EllipticResidueSum.residue_sum ω₁ ω₂ h₁ h₂ (logDeriv f)
      (fun a => (hm a).logDeriv) (logDeriv_periodic hf) s hs
    simp_rw [residue_logDeriv (hm _) (ho _)] at hres
    exact_mod_cast hres
  have hksum : ∑ q ∈ t, k q = 0 := by
    rw [Finset.sum_image (by exact hs.2.1)]
    simpa only [hk'] using hsum
  have heq : (∑ q ∈ t, ((k q).toNat : ℤ)) = ∑ q ∈ t, ((-k q).toNat : ℤ) := by
    have hsub : (∑ q ∈ t, ((k q).toNat : ℤ)) - ∑ q ∈ t, ((-k q).toNat : ℤ) = 0 := by
      rw [← Finset.sum_sub_distrib]
      simpa only [Int.toNat_sub_toNat_neg] using hksum
    omega
  simpa only [Z, P, Finsupp.sum_onFinset, Int.cast_zero, implies_true] using
    (show ∑ q ∈ t, (k q).toNat = ∑ q ∈ t, (-k q).toNat by exact_mod_cast heq)

lemma pole_order_sub_const {f : ℂ → ℂ} {a : ℂ} (_hf : MeromorphicAt f a) (c : ℂ) :
    (meromorphicOrderAt (fun z => f z - c) a < 0 ↔ meromorphicOrderAt f a < 0) ∧
    (meromorphicOrderAt f a < 0 →
      meromorphicOrderAt (fun z => f z - c) a = meromorphicOrderAt f a) := by
  have hforward {g : ℂ → ℂ} (d : ℂ) (hg : meromorphicOrderAt g a < 0) :
      meromorphicOrderAt (fun z => g z - d) a = meromorphicOrderAt g a := by
    change meromorphicOrderAt (g + fun _ => -d) a = _
    exact meromorphicOrderAt_add_eq_left_of_lt analyticAt_const.meromorphicAt
      (hg.trans_le (show 0 ≤ meromorphicOrderAt (fun _ : ℂ => -d) a from
        analyticAt_const.meromorphicOrderAt_nonneg))
  refine ⟨⟨fun h => ?_, fun h => by rw [hforward c h]; exact h⟩, hforward c⟩
  have he := hforward (g := fun z => f z - c) (-c) h
  simp only [sub_neg_eq_add, sub_add_cancel] at he
  rwa [he]

lemma shifted_finite_order {F : ℂ → RiemannSphere} (hF : ScalarMeromorphicOn univ F)
    (hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c) (c a : ℂ) :
    meromorphicOrderAt (fun z => scalarFinitePart F z - c) a ≠ ⊤ := by
  have hm : MeromorphicOn (fun z => scalarFinitePart F z - c) univ :=
    fun z hz => (LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF z hz).sub
      analyticAt_const.meromorphicAt
  intro ho
  apply hn
  refine ⟨c, fun b => ?_⟩
  have hob := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ a) (mem_univ b) ho
  have he : scalarFinitePart F =ᶠ[𝓝[≠] b] (fun _ => c) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hob] with z hz
    exact sub_eq_zero.mp hz
  exact (LocalQuotientsArithmetic.scalar_eq_fill univ F hF (mem_univ b)).trans
    ((LocalQuotientsArithmetic.fill_congr _ _ b he).trans
      (LocalQuotientsArithmetic.fill_const c b))

lemma negative_part_sub_const {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (c : ℂ)
    (ho : meromorphicOrderAt f a ≠ ⊤)
    (hc : meromorphicOrderAt (fun z => f z - c) a ≠ ⊤) :
    (-(meromorphicOrderAt (fun z => f z - c) a).untop₀).toNat =
      (-(meromorphicOrderAt f a).untop₀).toNat := by
  obtain ⟨hiff, heq⟩ := pole_order_sub_const hf c
  by_cases hp : meromorphicOrderAt f a < 0
  · rw [heq hp]
  · have h := le_of_not_gt hp
    have h' := le_of_not_gt (hiff.not.mpr hp)
    have he := WithTop.coe_untop₀_of_ne_top ho
    have he' := WithTop.coe_untop₀_of_ne_top hc
    have hi : 0 ≤ (meromorphicOrderAt f a).untop₀ := by exact_mod_cast (he ▸ h)
    have hi' : 0 ≤ (meromorphicOrderAt (fun z => f z - c) a).untop₀ := by
      exact_mod_cast (he' ▸ h')
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr hi'), Int.toNat_of_nonpos (neg_nonpos.mpr hi)]

/-- The natural positive part records precisely the actual finite fibre. -/
lemma positive_part_iff_value {F : ℂ → RiemannSphere} (hF : ScalarMeromorphicOn univ F)
    (c a : ℂ) (ho : meromorphicOrderAt (fun z => scalarFinitePart F z - c) a ≠ ⊤) :
    (meromorphicOrderAt (fun z => scalarFinitePart F z - c) a).untop₀.toNat ≠ 0 ↔
      F a = sphereFinite c := by
  have hm := LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF a (mem_univ a)
  obtain ⟨m, hmorder⟩ := WithTop.ne_top_iff_exists.mp ho
  have hnat : (meromorphicOrderAt (fun z => scalarFinitePart F z - c) a).untop₀.toNat ≠ 0 ↔
      0 < meromorphicOrderAt (fun z => scalarFinitePart F z - c) a := by
    rw [← hmorder]
    simp only [WithTop.untop₀_coe, WithTop.coe_pos]
    omega
  rw [hnat]
  by_cases hp : F a = sphereInfty
  · have hporder : meromorphicOrderAt (scalarFinitePart F) a < 0 := by
      apply (LocalQuotientsArithmetic.fill_eq_infty_iff _ _).mp
      exact (show F a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a from
        LocalQuotientsArithmetic.scalar_eq_fill univ F hF (mem_univ a)).symm.trans hp
    have hs := (pole_order_sub_const hm c).2 hporder
    rw [hs]
    exact iff_of_false (not_lt.mpr hporder.le) (by
      rw [hp]; exact (OnePoint.coe_ne_infty c).symm)
  · have han := scalarMeromorphicOn_finite_analytic univ F hF a (mem_univ a) hp
    have hanc : AnalyticAt ℂ (fun z => scalarFinitePart F z - c) a := han.sub analyticAt_const
    have hz : 0 < meromorphicOrderAt (fun z => scalarFinitePart F z - c) a ↔
        scalarFinitePart F a = c := by
      rw [← tendsto_zero_iff_meromorphicOrderAt_pos hanc.meromorphicAt]
      constructor
      · intro h
        have he := tendsto_nhds_unique h hanc.continuousAt.continuousWithinAt.tendsto
        exact sub_eq_zero.mp he.symm
      · intro he
        simpa only [he, sub_self] using hanc.continuousAt.continuousWithinAt.tendsto
    rw [hz]
    obtain hinf | ⟨b, hb⟩ := sphere_eq_infty_or_finite (F a)
    · exact (hp hinf).elim
    · simp [scalarFinitePart, hb, finiteCoordinate_sphereFinite, sphereFinite_injective.eq_iff]

lemma finsupp_apply_le_total {A : Type*} (P : A →₀ ℕ) (q : A) :
    P q ≤ P.sum (fun _ n => n) := by
  classical
  by_cases h : q ∈ P.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) h
  · simp [Finsupp.notMem_support_iff.mp h, Finsupp.sum]

/-- Nonconstancy forces at least one pole: otherwise the canonical finite
representative is entire and the accepted elliptic Liouville theorem applies. -/
lemma total_poles_pos {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {F : ℂ → RiemannSphere} (hF : ScalarMeromorphicOn univ F) (hf : Periodic ω₁ ω₂ F)
    (hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c)
    (P : Torus ω₁ ω₂ →₀ ℕ)
    (hP : ∀ a, P (projection ω₁ ω₂ a) = (-(meromorphicOrderAt (scalarFinitePart F) a).untop₀).toNat)
    (ho : ∀ a, meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤) :
    0 < P.sum (fun _ n => n) := by
  by_contra hpos
  have hzero : P.sum (fun _ n => n) = 0 := Nat.eq_zero_of_not_pos hpos
  have hno (a : ℂ) : F a ≠ sphereInfty := by
    intro hp
    have hporder : meromorphicOrderAt (scalarFinitePart F) a < 0 := by
      apply (LocalQuotientsArithmetic.fill_eq_infty_iff _ _).mp
      exact (show F a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a from
        LocalQuotientsArithmetic.scalar_eq_fill univ F hF (mem_univ a)).symm.trans hp
    have hz := finsupp_apply_le_total P (projection ω₁ ω₂ a)
    rw [hzero, hP a] at hz
    have he := WithTop.coe_untop₀_of_ne_top (ho a)
    have hi : (meromorphicOrderAt (scalarFinitePart F) a).untop₀ < 0 := by
      exact_mod_cast (he ▸ hporder)
    have hnat : 0 < (-(meromorphicOrderAt (scalarFinitePart F) a).untop₀).toNat := by
      omega
    omega
  have hper : Periodic ω₁ ω₂ (scalarFinitePart F) := fun z l hl =>
    congrArg finiteCoordinate (hf z l hl)
  have hhol : HolomorphicOn univ (scalarFinitePart F) :=
    ⟨isOpen_univ, fun a _ =>
      (scalarMeromorphicOn_finite_analytic univ F hF a (mem_univ a) (hno a)).differentiableAt⟩
  obtain ⟨c, hc⟩ := Ch22.EntireEllipticConstant.entire_elliptic_constant ω₁ ω₂ h₁ h₂
    (scalarFinitePart F) hhol hper
  apply hn
  refine ⟨c, fun a => ?_⟩
  exact (show F a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a from
    LocalQuotientsArithmetic.scalar_eq_fill univ F hF (mem_univ a)).trans
    ((LocalQuotientsArithmetic.fill_of_analyticAt
      (scalarMeromorphicOn_finite_analytic univ F hF a (mem_univ a) (hno a))).trans
        (congrArg sphereFinite (hc a)))

/-- Equal zero and pole degree, and the same finite-fibre count for every c. -/
theorem divisor_degree : Specs.D12Complex.Ch22.DivisorDegree.divisor_degree_type := by
  intro ω₁ ω₂ h₁ h₂ F hF hf hn
  have hm : ∀ a, MeromorphicAt (scalarFinitePart F) a :=
    fun a => LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF a (mem_univ a)
  have hper : Periodic ω₁ ω₂ (scalarFinitePart F) := fun z l hl =>
    congrArg finiteCoordinate (hf z l hl)
  have ho : ∀ a, meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤ := by
    simpa only [sub_zero] using shifted_finite_order hF hn 0
  obtain ⟨Z, P, hZP, heq⟩ := effective_divisors h₁ h₂ hm hper ho
  refine ⟨P.sum (fun _ n => n), total_poles_pos h₁ h₂ hF hf hn P (fun a => (hZP a).2) ho,
    Z, P, fun a => ⟨ho a, hZP a⟩, heq, rfl, ?_⟩
  intro c
  have hmc : ∀ a, MeromorphicAt (fun z => scalarFinitePart F z - c) a :=
    fun a => (hm a).sub analyticAt_const.meromorphicAt
  have hpc : Periodic ω₁ ω₂ (fun z => scalarFinitePart F z - c) := by
    intro z l hl
    exact congrArg (fun w : ℂ => w - c) (hper z l hl)
  have hoc := shifted_finite_order hF hn c
  obtain ⟨V, Q, hVQ, heqVQ⟩ := effective_divisors h₁ h₂ hmc hpc hoc
  have hQP : Q = P := by
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change Q (projection ω₁ ω₂ a) = P (projection ω₁ ω₂ a)
    rw [(hVQ a).2, (hZP a).2]
    exact negative_part_sub_const (hm a) c (ho a) (hoc a)
  refine ⟨V, fun a => ?_, by simpa only [hQP] using heqVQ⟩
  exact ⟨hoc a, (hVQ a).1, (hVQ a).1 ▸ positive_part_iff_value hF c a (hoc a),
    pole_order_sub_const (hm a) c⟩

end D12Complex.DivisorDegree
