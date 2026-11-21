import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Meromorphic
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Algebra.Field.MinimalAxioms

noncomputable section
open Set Filter
open scoped Topology Classical

namespace D12Complex.LocalQuotientsArithmetic
/-- The sphere value of a meromorphic germ, with its removable value restored. -/
def fill (f : ℂ → ℂ) (a : ℂ) : RiemannSphere :=
  if meromorphicOrderAt f a < 0 then sphereInfty
  else sphereFinite (toMeromorphicNFAt f a a)

/-- A local quotient uses weak holomorphy and a genuinely nonzero denominator
on a disk. Equality includes all filled values at the denominator's zeros. -/
def LocalQuotientsOn (Ω : Set ℂ) (F : ℂ → RiemannSphere) : Prop :=
  IsOpen Ω ∧ ∀ a ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧
    ∃ p q : ℂ → ℂ, HolomorphicOn (Metric.ball a r) p ∧
      HolomorphicOn (Metric.ball a r) q ∧
      ¬ EqOn q (fun _ => 0) (Metric.ball a r) ∧
      EqOn F (fill (p / q)) (Metric.ball a r)

/-- Arithmetic is applied to punctured representatives and then filled. -/
def add (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F + scalarFinitePart G)
def neg (F : ℂ → RiemannSphere) := fill (-scalarFinitePart F)
def sub (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F - scalarFinitePart G)
def mul (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F * scalarFinitePart G)
def inv (F : ℂ → RiemannSphere) := fill (scalarFinitePart F)⁻¹
def div (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F / scalarFinitePart G)

/-- Actual scalar functions on Ω, represented with the fixed value zero outside Ω.
The outside normalization makes equality exactly equality on Ω. -/
def ScalarFunction (Ω : Set ℂ) :=
  {F : ℂ → RiemannSphere // ScalarMeromorphicOn Ω F ∧
    ∀ a ∉ Ω, F a = sphereFinite 0}


open private pole_integer_factorization from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Meromorphic

/-- A scalar function gives an ordinary meromorphic punctured germ. -/
theorem scalar_meromorphicAt :
    Specs.D12Complex.Ch07.LocalQuotientsArithmetic.scalar_meromorphicAt_type := by
  intro Ω F hF a ha
  by_cases hfin : F a ≠ sphereInfty
  · exact (scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin).meromorphicAt
  · obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha (not_ne_iff.mp hfin)
    obtain ⟨g, hg, _, heq⟩ := pole_integer_factorization hm
    exact MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-(m : ℤ), g, hg, heq⟩

/-- Filled values depend only on punctured germs, including at cancellations. -/
theorem fill_congr :
    Specs.D12Complex.Ch07.LocalQuotientsArithmetic.fill_congr_type := by
  intro f g a hfg
  change fill f a = fill g a
  unfold fill
  rw [meromorphicOrderAt_congr hfg,
    (toMeromorphicNFAt_eventuallyEq_nhds_congr hfg).eq_of_nhds]

/-- Recover the actual finite or infinite scalar value from its punctured germ. -/
theorem scalar_eq_fill :
    Specs.D12Complex.Ch07.LocalQuotientsArithmetic.scalar_eq_fill_type := by
  intro Ω F hF a ha
  change F a = fill (scalarFinitePart F) a
  have hm := scalar_meromorphicAt Ω F hF a ha
  by_cases hfin : F a ≠ sphereInfty
  · have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin
    have hn : ¬ meromorphicOrderAt (scalarFinitePart F) a < 0 :=
      not_lt.mpr han.meromorphicOrderAt_nonneg
    rw [fill, ite_eq_right hn, toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt]
    rcases sphere_eq_infty_or_finite (F a) with h | ⟨c, hc⟩
    · exact (hfin h).elim
    · simp only [scalarFinitePart, hc, finiteCoordinate_sphereFinite]
  · have hInf := not_ne_iff.mp hfin
    obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha hInf
    have ho := scalarSignedOrder_pole F a m hm
    have hn : meromorphicOrderAt (scalarFinitePart F) a < 0 := by
      change meromorphicOrderAt (scalarFinitePart F) a = (-(m : ℤ) : WithTop ℤ) at ho
      rw [ho]
      have hpos : 1 ≤ m := hm.1
      exact WithTop.coe_lt_coe.mpr (neg_neg_of_pos (Int.natCast_pos.mpr (by omega)))
    rw [fill, ite_eq_left hn]
    exact hInf

theorem scalar_order_mul_germ :
    Specs.D12Complex.Ch07.LocalQuotientsArithmetic.scalar_order_mul_germ_type := by
  intro Ω F G hF hG a ha m n hm hn
  change meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) at hm
  change meromorphicOrderAt (scalarFinitePart G) a = (n : WithTop ℤ) at hn
  rw [meromorphicOrderAt_mul (scalar_meromorphicAt Ω F hF a ha)
    (scalar_meromorphicAt Ω G hG a ha), hm, hn]
  rfl

theorem scalar_order_div_germ :
    Specs.D12Complex.Ch07.LocalQuotientsArithmetic.scalar_order_div_germ_type := by
  intro Ω F G hF hG a ha m n hm hn
  change meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) at hm
  change meromorphicOrderAt (scalarFinitePart G) a = (n : WithTop ℤ) at hn
  rw [meromorphicOrderAt_div (scalar_meromorphicAt Ω F hF a ha)
    (scalar_meromorphicAt Ω G hG a ha), hm, hn]
  rfl


@[simp] theorem fill_eq_infty_iff (f : ℂ → ℂ) (a : ℂ) :
    fill f a = sphereInfty ↔ meromorphicOrderAt f a < 0 := by
  unfold fill
  split_ifs <;> simp_all [sphereFinite, sphereInfty]

/-- At an analytic point the filling is the original finite value. -/
theorem fill_of_analyticAt {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    fill f a = sphereFinite (f a) := by
  rw [fill, ite_eq_right (not_lt.mpr hf.meromorphicOrderAt_nonneg),
    toMeromorphicNFAt_eq_self.mpr hf.meromorphicNFAt]

/-- Filling preserves the punctured finite representative. -/
theorem finitePart_fill_germ {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    scalarFinitePart (fill f) =ᶠ[𝓝[≠] a] f := by
  filter_upwards [hf.eventually_analyticAt] with z hz
  simp only [scalarFinitePart, fill_of_analyticAt hz, finiteCoordinate_sphereFinite]

/-- Normalization on an open set is exactly the finite coordinate of filling. -/
theorem finitePart_fill_eq_normalize {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : MeromorphicOn f Ω) :
    EqOn (scalarFinitePart (fill f)) (toMeromorphicNFOn f Ω) Ω := by
  intro a ha
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf ha]
  by_cases hn : meromorphicOrderAt f a < 0
  · simp [scalarFinitePart, fill, hn,
      toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero hn.ne, finiteCoordinate, sphereInfty]
  · simp [scalarFinitePart, fill, hn]

/-- A negative meromorphic order yields the source's exact positive pole order. -/
theorem poleOfOrder_of_order {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (m : ℕ) (hm : 1 ≤ m) (ho : meromorphicOrderAt f a = (-(m : ℤ) : WithTop ℤ)) :
    PoleOfOrderAt f a m := by
  obtain ⟨g, hg, hg0, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have hga : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ g z := hg.eventually_analyticAt.mono
    (fun _ hz => hz.differentiableAt)
  have hfa : ∀ᶠ z in 𝓝 a, z ≠ a → DifferentiableAt ℂ f z :=
    eventually_nhdsWithin_iff.mp (hf.eventually_analyticAt.mono
      (fun _ hz => hz.differentiableAt))
  have he : ∀ᶠ z in 𝓝 a, z ≠ a → f z = ((z - a)^m)⁻¹ * g z := by
    simpa only [zpow_neg, zpow_natCast, smul_eq_mul, mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp heq)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hga.and (hfa.and he))
  have hgB : HolomorphicOn (Metric.ball a r) g :=
    ⟨Metric.isOpen_ball, fun z hz => (hball (Metric.mem_ball.mp hz)).1⟩
  have hfB : HolomorphicOn (puncturedDisk a r) f := by
    refine ⟨?_, ?_⟩
    · have heq : puncturedDisk a r = Metric.ball a r \ {a} := by
        ext z
        simp [puncturedDisk, Metric.mem_ball, dist_eq_norm, norm_pos_iff, sub_ne_zero]
        tauto
      rw [heq]
      exact Metric.isOpen_ball.sdiff isClosed_singleton
    · intro z hz
      exact (hball (by simpa only [dist_eq_norm] using hz.2)).2.1
        (sub_ne_zero.mp (norm_pos_iff.mp hz.1))
  exact ⟨hm, ⟨r, hr, hfB⟩, r, hr, g, hgB, hg0, fun z hz =>
    (hball (by simpa only [dist_eq_norm] using hz.2)).2.2
      (sub_ne_zero.mp (norm_pos_iff.mp hz.1))⟩


/-- Every ordinary meromorphic representative has a scalar sphere-valued filling.
No nonzero condition is needed here; zero components fill as finite zero. -/
theorem scalarMeromorphicOn_fill (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : MeromorphicOn f Ω) : ScalarMeromorphicOn Ω (fill f) := by
  let h := toMeromorphicNFOn f Ω
  have hN : MeromorphicNFOn h Ω := meromorphicNFOn_toMeromorphicNFOn f Ω
  have horder (a : ℂ) (ha : a ∈ Ω) : meromorphicOrderAt h a = meromorphicOrderAt f a :=
    meromorphicOrderAt_congr (hf.toMeromorphicNFOn_eq_self_on_nhdsNE ha)
  have hfin (a : ℂ) (ha : a ∈ Ω) :
      fill f a ≠ sphereInfty ↔ AnalyticAt ℂ h a := by
    rw [ne_eq, fill_eq_infty_iff, not_lt, ← horder a ha,
      (hN ha).meromorphicOrderAt_nonneg_iff_analyticAt]
  have hloc : {z | z ∈ Ω ∧ fill f z ≠ sphereInfty} = Ω ∩ {z | AnalyticAt ℂ h z} := by
    ext a
    exact and_congr_right (fun ha => hfin a ha)
  have heq := finitePart_fill_eq_normalize hf
  have han (a : ℂ) (ha : a ∈ Ω) (hfa : fill f a ≠ sphereInfty) :
      AnalyticAt ℂ (scalarFinitePart (fill f)) a := by
    apply (analyticAt_congr (eventually_of_mem (hΩ.mem_nhds ha) heq)).mpr
    exact (hfin a ha).mp hfa
  refine ⟨hΩ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← isOpen_compl_iff]
    convert (isOpen_analyticAt ℂ h).preimage continuous_subtype_val using 1
    ext a
    exact hfin a a.property
  · apply isDiscrete_iff_nhdsNE.mpr
    intro a ha
    rw [← disjoint_iff, disjoint_principal_right]
    filter_upwards [(hf a ha.1).eventually_analyticAt] with z hz hzP
    exact (not_lt.mpr hz.meromorphicOrderAt_nonneg) ((fill_eq_infty_iff f z).mp hzP.2)
  · refine ⟨?_, fun a ha => (han a ha.1 ha.2).differentiableAt⟩
    rw [hloc]
    exact hΩ.inter (isOpen_analyticAt ℂ h)
  · intro a ha hfa
    have ho := (fill_eq_infty_iff f a).mp hfa
    lift meromorphicOrderAt f a to ℤ using ho.ne_top with n hn
    have hnneg : n < 0 := WithTop.coe_lt_coe.mp ho
    let m := (-n).toNat
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hnm : -(m : ℤ) = n := by dsimp [m]; omega
    have hfg := finitePart_fill_germ (hf a ha)
    refine ⟨m, poleOfOrder_of_order ((hf a ha).congr hfg.symm) m hm ?_⟩
    rw [meromorphicOrderAt_congr hfg]
    simpa only [WithTop.LinearOrderedAddCommGroup.coe_neg] using
      hn.symm.trans (congrArg (fun k : ℤ => (k : WithTop ℤ)) hnm).symm
  · intro a ha
    have hC : connectedComponentIn Ω a ∈ 𝓝 a :=
      hΩ.connectedComponentIn.mem_nhds (mem_connectedComponentIn ha)
    have he : ∀ᶠ z in 𝓝[≠] a,
        z ∈ connectedComponentIn Ω a ∧ fill f z ≠ sphereInfty := by
      filter_upwards [nhdsWithin_le_nhds hC, (hf a ha).eventually_analyticAt] with z hz hza
      exact ⟨hz, (fill_eq_infty_iff f z).not.mpr (not_lt.mpr hza.meromorphicOrderAt_nonneg)⟩
    exact he.exists


/-- Restriction equality respects the scalar meromorphic definition. -/
theorem scalar_congr {Ω : Set ℂ} {F G : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) (hFG : EqOn F G Ω) : ScalarMeromorphicOn Ω G := by
  have hp : scalarPoleSet Ω F = scalarPoleSet Ω G := by
    ext z
    exact and_congr_right (fun hz => by rw [hFG hz])
  have hl : {z | z ∈ Ω ∧ F z ≠ sphereInfty} = {z | z ∈ Ω ∧ G z ≠ sphereInfty} := by
    ext z
    exact and_congr_right (fun hz => by rw [hFG hz])
  have he (a : ℂ) (ha : a ∈ Ω) : scalarFinitePart F =ᶠ[𝓝 a] scalarFinitePart G := by
    filter_upwards [hF.1.mem_nhds ha] with z hz
    exact congrArg finiteCoordinate (hFG hz)
  refine ⟨hF.1, ?_, hp ▸ hF.2.2.1, ?_, ?_, ?_⟩
  · convert hF.2.1 using 1
    ext a
    change G a = sphereInfty ↔ F a = sphereInfty
    rw [hFG a.property]
  · refine ⟨hl ▸ hF.2.2.2.1.1, ?_⟩
    intro a ha
    apply ((scalarMeromorphicOn_finite_analytic Ω F hF a ha.1 ?_).congr (he a ha.1)).differentiableAt
    simpa only [hFG ha.1] using ha.2
  · intro a ha hga
    obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha ((hFG ha).trans hga)
    refine ⟨m, poleOfOrder_of_order ((scalar_meromorphicAt Ω F hF a ha).congr
      ((he a ha).filter_mono nhdsWithin_le_nhds)) m hm.1 ?_⟩
    rw [← meromorphicOrderAt_congr ((he a ha).filter_mono nhdsWithin_le_nhds)]
    exact scalarSignedOrder_pole F a m hm
  · intro a ha
    obtain ⟨b, hb, hfb⟩ := hF.2.2.2.2.2 a ha
    exact ⟨b, hb, by rwa [← hFG (connectedComponentIn_subset Ω a hb)]⟩

/-- A criterion separating raw punctured germs from the prescribed filled values. -/
theorem scalar_iff_filled (Ω : Set ℂ) (F : ℂ → RiemannSphere) :
    ScalarMeromorphicOn Ω F ↔ IsOpen Ω ∧ MeromorphicOn (scalarFinitePart F) Ω ∧
      EqOn F (fill (scalarFinitePart F)) Ω := by
  constructor
  · intro hF
    exact ⟨hF.1, scalar_meromorphicAt Ω F hF, scalar_eq_fill Ω F hF⟩
  · rintro ⟨hΩ, hf, heq⟩
    exact scalar_congr (scalarMeromorphicOn_fill Ω hΩ _ hf) heq.symm

/-- A meromorphic germ is a quotient on a whole disk after filling, with a
power denominator. Values at the one exceptional center do not affect filling. -/
theorem local_quotient_of_meromorphicAt {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ}
    (ha : a ∈ Ω) {f : ℂ → ℂ} (hf : MeromorphicAt f a) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧ ∃ p q : ℂ → ℂ,
      HolomorphicOn (Metric.ball a r) p ∧ HolomorphicOn (Metric.ball a r) q ∧
      ¬ EqOn q (fun _ => 0) (Metric.ball a r) ∧
      EqOn (fill f) (fill (p / q)) (Metric.ball a r) := by
  obtain ⟨n, hp⟩ := hf
  let p : ℂ → ℂ := fun z => (z - a)^n * f z
  let q : ℂ → ℂ := fun z => (z - a)^n
  have hp' : AnalyticAt ℂ p a := hp
  have hpa := hp'.eventually_analyticAt.mono (fun _ hz => hz.differentiableAt)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((show ∀ᶠ z in 𝓝 a, z ∈ Ω from hΩ.mem_nhds ha).and hpa)
  have hq (z : ℂ) (hza : z ≠ a) : q z ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hza)
  refine ⟨r, hr, fun z hz => (hball (Metric.mem_ball.mp hz)).1, p, q,
    ⟨Metric.isOpen_ball, fun z hz => (hball (Metric.mem_ball.mp hz)).2⟩,
    ⟨Metric.isOpen_ball, fun z _ => by dsimp [q]; fun_prop⟩, ?_, ?_⟩
  · intro hzero
    have he : ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r ∧ z ≠ a :=
      (show ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)).and self_mem_nhdsWithin
    obtain ⟨z, hz, hza⟩ := he.exists
    exact hq z hza (hzero hz)
  · intro b hb
    apply fill_congr
    have he : ∀ᶠ z in 𝓝[≠] b, z ≠ a := by
      rcases eq_or_ne b a with rfl | hba
      · exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin hba
    filter_upwards [he] with z hz
    dsimp [p, q]
    rw [mul_div_cancel_left₀ (f z) (hq z hz)]

/-- The scalar/local quotient characterization, including the canceled values. -/
theorem scalar_iff_localQuotients (Ω : Set ℂ) (F : ℂ → RiemannSphere) :
    ScalarMeromorphicOn Ω F ↔ LocalQuotientsOn Ω F := by
  constructor
  · intro hF
    refine ⟨hF.1, fun a ha => ?_⟩
    obtain ⟨r, hr, hb, p, q, hp, hq, hq0, heq⟩ :=
      local_quotient_of_meromorphicAt hF.1 ha (scalar_meromorphicAt Ω F hF a ha)
    exact ⟨r, hr, hb, p, q, hp, hq, hq0, (scalar_eq_fill Ω F hF).mono hb |>.trans heq⟩
  · rintro ⟨hΩ, hF⟩
    apply (scalar_iff_filled Ω F).mpr
    have hlocal (a : ℂ) (ha : a ∈ Ω) :
        MeromorphicAt (scalarFinitePart F) a ∧ F a = fill (scalarFinitePart F) a := by
      obtain ⟨r, hr, hb, p, q, hp, hq, hq0, heq⟩ := hF a ha
      have hpa : AnalyticAt ℂ p a := (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
        ⟨Metric.ball a r, Metric.mem_ball_self hr, hp⟩
      have hqa : AnalyticAt ℂ q a := (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp
        ⟨Metric.ball a r, Metric.mem_ball_self hr, hq⟩
      have hmero := hpa.meromorphicAt.div hqa.meromorphicAt
      have hrep : scalarFinitePart F =ᶠ[𝓝[≠] a] p / q := by
        have he : scalarFinitePart F =ᶠ[𝓝 a] scalarFinitePart (fill (p / q)) := by
          filter_upwards [Metric.ball_mem_nhds a hr] with z hz
          exact congrArg finiteCoordinate (heq hz)
        exact (he.filter_mono nhdsWithin_le_nhds).trans (finitePart_fill_germ hmero)
      exact ⟨hmero.congr hrep.symm, (heq (Metric.mem_ball_self hr)).trans (fill_congr _ _ _ hrep).symm⟩
    exact ⟨hΩ, fun a ha => (hlocal a ha).1, fun a ha => (hlocal a ha).2⟩


/-- Closure under the filled sum, difference, product, and reciprocal.
The inverse of a zero component is totalized as zero; the reciprocal law
below imposes precisely the source's componentwise nonzero condition. -/
theorem arithmetic_closed (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G) :
    ScalarMeromorphicOn Ω (add F G) ∧ ScalarMeromorphicOn Ω (neg F) ∧
    ScalarMeromorphicOn Ω (sub F G) ∧ ScalarMeromorphicOn Ω (mul F G) ∧
    ScalarMeromorphicOn Ω (inv F) ∧ ScalarMeromorphicOn Ω (div F G) := by
  have hf : MeromorphicOn (scalarFinitePart F) Ω := scalar_meromorphicAt Ω F hF
  have hg : MeromorphicOn (scalarFinitePart G) Ω := scalar_meromorphicAt Ω G hG
  exact ⟨scalarMeromorphicOn_fill Ω hF.1 _ (hf.add hg),
    scalarMeromorphicOn_fill Ω hF.1 _ hf.neg,
    scalarMeromorphicOn_fill Ω hF.1 _ (hf.sub hg),
    scalarMeromorphicOn_fill Ω hF.1 _ (hf.mul hg),
    scalarMeromorphicOn_fill Ω hF.1 _ hf.inv,
    scalarMeromorphicOn_fill Ω hF.1 _ (hf.div hg)⟩

theorem signedOrder_fill {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (a : ℂ) (ha : a ∈ Ω) :
    scalarSignedOrder (fill f) a = meromorphicOrderAt f a :=
  meromorphicOrderAt_congr (finitePart_fill_germ (hf a ha))

/-- The signed order law for the actual filled product and quotient. -/
theorem signedOrder_mul_div (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G)
    (a : ℂ) (ha : a ∈ Ω) (m n : ℤ)
    (hm : scalarSignedOrder F a = some m) (hn : scalarSignedOrder G a = some n) :
    scalarSignedOrder (mul F G) a = some (m + n) ∧
    scalarSignedOrder (div F G) a = some (m - n) := by
  have hf : MeromorphicOn (scalarFinitePart F) Ω := scalar_meromorphicAt Ω F hF
  have hg : MeromorphicOn (scalarFinitePart G) Ω := scalar_meromorphicAt Ω G hG
  exact ⟨(signedOrder_fill (hf.mul hg) a ha).trans
      (scalar_order_mul_germ Ω F G hF hG a ha m n hm hn),
    (signedOrder_fill (hf.div hg) a ha).trans
      (scalar_order_div_germ Ω F G hF hG a ha m n hm hn)⟩

private theorem analyticOnNhd_of_holomorphicOn {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) : AnalyticOnNhd ℂ f U := fun a ha =>
  (LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mp ⟨U, ha, hf⟩

/-- The denominator on a connected disk is nonzero as a germ at every point. -/
theorem denominator_eventually_ne_zero {a : ℂ} {r : ℝ} {q : ℂ → ℂ}
    (hq : HolomorphicOn (Metric.ball a r) q)
    (hq0 : ¬ EqOn q (fun _ => 0) (Metric.ball a r)) {b : ℂ} (hb : b ∈ Metric.ball a r) :
    ∀ᶠ z in 𝓝[≠] b, q z ≠ 0 := by
  have hqa := analyticOnNhd_of_holomorphicOn hq
  rcases (hqa b hb).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact (hq0 (hqa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball a r).isPreconnected hb hzero)).elim
  · exact hne

/-- Explicit common-denominator formulas hold at the filled values too. -/
theorem local_arithmetic_formulas (a : ℂ) (r : ℝ) (hr : 0 < r)
    (F G : ℂ → RiemannSphere) (p q u v : ℂ → ℂ)
    (hp : HolomorphicOn (Metric.ball a r) p) (hq : HolomorphicOn (Metric.ball a r) q)
    (hu : HolomorphicOn (Metric.ball a r) u) (hv : HolomorphicOn (Metric.ball a r) v)
    (hq0 : ¬ EqOn q (fun _ => 0) (Metric.ball a r))
    (hv0 : ¬ EqOn v (fun _ => 0) (Metric.ball a r))
    (hF : EqOn F (fill (p / q)) (Metric.ball a r))
    (hG : EqOn G (fill (u / v)) (Metric.ball a r)) :
    ¬ EqOn (q * v) (fun _ => 0) (Metric.ball a r) ∧
    EqOn (add F G) (fill ((p * v + u * q) / (q * v))) (Metric.ball a r) ∧
    EqOn (sub F G) (fill ((p * v - u * q) / (q * v))) (Metric.ball a r) ∧
    EqOn (mul F G) (fill ((p * u) / (q * v))) (Metric.ball a r) := by
  have hqne := fun {b : ℂ} (hb : b ∈ Metric.ball a r) =>
    denominator_eventually_ne_zero hq hq0 hb
  have hvne := fun {b : ℂ} (hb : b ∈ Metric.ball a r) =>
    denominator_eventually_ne_zero hv hv0 hb
  have hrep (b : ℂ) (hb : b ∈ Metric.ball a r) :
      scalarFinitePart F =ᶠ[𝓝[≠] b] p / q ∧ scalarFinitePart G =ᶠ[𝓝[≠] b] u / v := by
    have hfp : scalarFinitePart F =ᶠ[𝓝[≠] b] scalarFinitePart (fill (p / q)) := by
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hb)] with z hz
      exact congrArg finiteCoordinate (hF hz)
    have hgp : scalarFinitePart G =ᶠ[𝓝[≠] b] scalarFinitePart (fill (u / v)) := by
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hb)] with z hz
      exact congrArg finiteCoordinate (hG hz)
    exact ⟨hfp.trans (finitePart_fill_germ
        (((analyticOnNhd_of_holomorphicOn hp) b hb).meromorphicAt.div
          ((analyticOnNhd_of_holomorphicOn hq) b hb).meromorphicAt)),
      hgp.trans (finitePart_fill_germ
        (((analyticOnNhd_of_holomorphicOn hu) b hb).meromorphicAt.div
          ((analyticOnNhd_of_holomorphicOn hv) b hb).meromorphicAt))⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    have he : ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r ∧ q z ≠ 0 ∧ v z ≠ 0 :=
      (show ∀ᶠ z in 𝓝[≠] a, z ∈ Metric.ball a r from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)).and
        ((hqne (Metric.mem_ball_self hr)).and (hvne (Metric.mem_ball_self hr)))
    obtain ⟨z, hz, hqz, hvz⟩ := he.exists
    exact mul_ne_zero hqz hvz (hzero hz)
  · intro b hb
    apply fill_congr
    filter_upwards [(hrep b hb).1, (hrep b hb).2, hqne hb, hvne hb] with z hz hz' hqz hvz
    simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, hz, hz']
    field_simp
  · intro b hb
    apply fill_congr
    filter_upwards [(hrep b hb).1, (hrep b hb).2, hqne hb, hvne hb] with z hz hz' hqz hvz
    simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply, hz, hz']
    field_simp
  · intro b hb
    apply fill_congr
    filter_upwards [(hrep b hb).1, (hrep b hb).2] with z hz hz'
    simp only [Pi.mul_apply, Pi.div_apply, hz, hz']
    exact div_mul_div_comm _ _ _ _


@[simp] theorem fill_const (c : ℂ) (a : ℂ) : fill (fun _ => c) a = sphereFinite c :=
  fill_of_analyticAt analyticAt_const

theorem fill_of_order_top {f : ℂ → ℂ} {a : ℂ} (ho : meromorphicOrderAt f a = ⊤) :
    fill f a = sphereFinite 0 := by
  exact (fill_congr f (fun _ => 0) a (meromorphicOrderAt_eq_top_iff.mp ho)).trans (fill_const 0 a)

/-- Nonzero on each component is precisely the condition that all local orders
are finite. It excludes the zero germ, rather than merely a zero value. -/
theorem finite_order_of_componentwise_nonzero {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F)
    (hn : ∀ a ∈ Ω, ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a))
    (a : ℂ) (ha : a ∈ Ω) : meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤ := by
  intro ho
  apply hn a ha
  intro b hb
  have hC : MeromorphicOn (scalarFinitePart F) (connectedComponentIn Ω a) :=
    (show MeromorphicOn (scalarFinitePart F) Ω from scalar_meromorphicAt Ω F hF).mono_set (connectedComponentIn_subset Ω a)
  have hob := hC.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_connectedComponentIn (mem_connectedComponentIn ha) hb ho
  exact (scalar_eq_fill Ω F hF (connectedComponentIn_subset Ω a hb)).trans (fill_of_order_top hob)

/-- The componentwise condition makes the filled inverse a genuine reciprocal. -/
theorem reciprocal_law (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F)
    (hn : ∀ a ∈ Ω, ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a)) :
    ScalarMeromorphicOn Ω (inv F) ∧ EqOn (mul F (inv F)) (fun _ => sphereFinite 1) Ω := by
  have hf : MeromorphicOn (scalarFinitePart F) Ω := scalar_meromorphicAt Ω F hF
  refine ⟨scalarMeromorphicOn_fill Ω hF.1 _ hf.inv, ?_⟩
  intro a ha
  have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf a ha)).mp
    (finite_order_of_componentwise_nonzero hF hn a ha)
  have hi := finitePart_fill_germ (hf a ha).inv
  change fill (scalarFinitePart F * scalarFinitePart (fill (scalarFinitePart F)⁻¹)) a = _
  rw [← fill_const 1 a]
  apply fill_congr
  filter_upwards [hne, hi] with z hz hzi
  simp only [Pi.mul_apply, Pi.inv_apply, hzi, mul_inv_cancel₀ hz, Pi.one_apply]

/-- Reciprocal local formulas exchange numerator and denominator, including
removable zeros and poles. The genuine inverse law uses the condition above. -/
theorem local_reciprocal_formula (a : ℂ) (r : ℝ) (F : ℂ → RiemannSphere)
    (p q : ℂ → ℂ) (hp : HolomorphicOn (Metric.ball a r) p)
    (hq : HolomorphicOn (Metric.ball a r) q)
    (hF : EqOn F (fill (p / q)) (Metric.ball a r)) :
    EqOn (inv F) (fill (q / p)) (Metric.ball a r) := by
  intro b hb
  have hm := ((analyticOnNhd_of_holomorphicOn hp) b hb).meromorphicAt.div
    ((analyticOnNhd_of_holomorphicOn hq) b hb).meromorphicAt
  have he : scalarFinitePart F =ᶠ[𝓝[≠] b] p / q := by
    have he' : scalarFinitePart F =ᶠ[𝓝[≠] b] scalarFinitePart (fill (p / q)) := by
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hb)] with z hz
      exact congrArg finiteCoordinate (hF hz)
    exact he'.trans (finitePart_fill_germ hm)
  apply fill_congr
  filter_upwards [he] with z hz
  simp only [Pi.inv_apply, Pi.div_apply, hz, inv_div]


/-- The source's nonzero-germ formulation of both signed order rules. -/
theorem signedOrder_rules (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G)
    (a : ℂ) (ha : a ∈ Ω) (hf0 : ¬ scalarZeroGerm F a) (hg0 : ¬ scalarZeroGerm G a) :
    ∃ m n : ℤ, scalarSignedOrder F a = some m ∧ scalarSignedOrder G a = some n ∧
      scalarSignedOrder (mul F G) a = some (m + n) ∧
      scalarSignedOrder (div F G) a = some (m - n) := by
  obtain ⟨m, hm⟩ := (scalarSignedOrder_exists_iff Ω F hF a ha).mpr hf0
  obtain ⟨n, hn⟩ := (scalarSignedOrder_exists_iff Ω G hG a ha).mpr hg0
  exact ⟨m, n, hm, hn, signedOrder_mul_div Ω F G hF hG a ha m n hm hn⟩

namespace FieldConstruction
variable {Ω : Set ℂ} [hΩ : Fact (IsOpen Ω)]

/-- Choose the zero extension outside the domain, preserving every value inside. -/
def ofRepresentative (f : ℂ → ℂ) (hf : MeromorphicOn f Ω) : ScalarFunction Ω :=
  ⟨fun a => if a ∈ Ω then fill f a else sphereFinite 0,
    scalar_congr (scalarMeromorphicOn_fill Ω hΩ.out f hf) (fun a ha => by simp [ha]),
    fun a ha => by simp [ha]⟩

def representative (F : ScalarFunction Ω) : ℂ → ℂ := scalarFinitePart F.val

lemma representative_meromorphic (F : ScalarFunction Ω) : MeromorphicOn (representative F) Ω :=
  scalar_meromorphicAt Ω F.val F.property.1

@[simp] lemma ofRepresentative_apply (f : ℂ → ℂ) (hf : MeromorphicOn f Ω)
    (a : ℂ) (ha : a ∈ Ω) : (ofRepresentative f hf).val a = fill f a := by
  simp only [ofRepresentative, ha, ↓reduceIte]

lemma representative_ofRepresentative (f : ℂ → ℂ) (hf : MeromorphicOn f Ω)
    (a : ℂ) (ha : a ∈ Ω) : representative (ofRepresentative f hf) =ᶠ[𝓝[≠] a] f := by
  have he : representative (ofRepresentative f hf) =ᶠ[𝓝 a] scalarFinitePart (fill f) := by
    filter_upwards [hΩ.out.mem_nhds ha] with z hz
    simp only [representative, scalarFinitePart, ofRepresentative_apply f hf z hz]
  exact (he.filter_mono nhdsWithin_le_nhds).trans (finitePart_fill_germ (hf a ha))

lemma ext_on {F G : ScalarFunction Ω} (he : EqOn F.val G.val Ω) : F = G := by
  apply Subtype.ext
  funext a
  by_cases ha : a ∈ Ω
  · exact he ha
  · exact (F.property.2 a ha).trans (G.property.2 a ha).symm

lemma ext_germ {F G : ScalarFunction Ω}
    (he : ∀ a ∈ Ω, representative F =ᶠ[𝓝[≠] a] representative G) : F = G := by
  apply ext_on
  intro a ha
  exact (scalar_eq_fill Ω F.val F.property.1 ha).trans
    ((fill_congr _ _ a (he a ha)).trans (scalar_eq_fill Ω G.val G.property.1 ha).symm)

local instance : Zero (ScalarFunction Ω) := ⟨ofRepresentative 0 (MeromorphicOn.const 0)⟩
local instance : One (ScalarFunction Ω) := ⟨ofRepresentative 1 (MeromorphicOn.const 1)⟩
local instance : Add (ScalarFunction Ω) := ⟨fun F G => ofRepresentative
  (representative F + representative G) ((representative_meromorphic F).add (representative_meromorphic G))⟩
local instance : Mul (ScalarFunction Ω) := ⟨fun F G => ofRepresentative
  (representative F * representative G) ((representative_meromorphic F).mul (representative_meromorphic G))⟩
local instance : Neg (ScalarFunction Ω) := ⟨fun F => ofRepresentative
  (-representative F) (representative_meromorphic F).neg⟩
local instance : Inv (ScalarFunction Ω) := ⟨fun F => ofRepresentative
  (representative F)⁻¹ (representative_meromorphic F).inv⟩

lemma rep_zero (a : ℂ) (ha : a ∈ Ω) : representative (0 : ScalarFunction Ω) =ᶠ[𝓝[≠] a] 0 :=
  representative_ofRepresentative _ _ a ha
lemma rep_one (a : ℂ) (ha : a ∈ Ω) : representative (1 : ScalarFunction Ω) =ᶠ[𝓝[≠] a] 1 :=
  representative_ofRepresentative _ _ a ha
lemma rep_add (F G : ScalarFunction Ω) (a : ℂ) (ha : a ∈ Ω) :
    representative (F + G) =ᶠ[𝓝[≠] a] representative F + representative G :=
  representative_ofRepresentative _ _ a ha
lemma rep_mul (F G : ScalarFunction Ω) (a : ℂ) (ha : a ∈ Ω) :
    representative (F * G) =ᶠ[𝓝[≠] a] representative F * representative G :=
  representative_ofRepresentative _ _ a ha
lemma rep_neg (F : ScalarFunction Ω) (a : ℂ) (ha : a ∈ Ω) :
    representative (-F) =ᶠ[𝓝[≠] a] -representative F :=
  representative_ofRepresentative _ _ a ha
lemma rep_inv (F : ScalarFunction Ω) (a : ℂ) (ha : a ∈ Ω) :
    representative F⁻¹ =ᶠ[𝓝[≠] a] (representative F)⁻¹ :=
  representative_ofRepresentative _ _ a ha

lemma add_assoc (F G H : ScalarFunction Ω) : F + G + H = F + (G + H) := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_add (F + G) H a ha, rep_add F G a ha,
    rep_add F (G + H) a ha, rep_add G H a ha] with z h1 h2 h3 h4
  simp only [Pi.add_apply] at *
  rw [h1, h2, h3, h4, _root_.add_assoc]

lemma zero_add (F : ScalarFunction Ω) : 0 + F = F := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_add 0 F a ha, rep_zero a ha] with z h1 h2
  simpa only [Pi.add_apply, h2, Pi.zero_apply, _root_.zero_add] using h1

lemma neg_add_cancel (F : ScalarFunction Ω) : -F + F = 0 := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_add (-F) F a ha, rep_neg F a ha, rep_zero a ha] with z h1 h2 h3
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at *
  rw [h1, h2, h3, _root_.neg_add_cancel]

lemma mul_assoc (F G H : ScalarFunction Ω) : F * G * H = F * (G * H) := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_mul (F * G) H a ha, rep_mul F G a ha,
    rep_mul F (G * H) a ha, rep_mul G H a ha] with z h1 h2 h3 h4
  simp only [Pi.mul_apply] at *
  rw [h1, h2, h3, h4, _root_.mul_assoc]

lemma mul_comm (F G : ScalarFunction Ω) : F * G = G * F := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_mul F G a ha, rep_mul G F a ha] with z h1 h2
  simp only [Pi.mul_apply] at *
  rw [h1, h2, _root_.mul_comm]

lemma one_mul (F : ScalarFunction Ω) : 1 * F = F := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_mul 1 F a ha, rep_one a ha] with z h1 h2
  simpa only [Pi.mul_apply, h2, Pi.one_apply, _root_.one_mul] using h1

lemma left_distrib (F G H : ScalarFunction Ω) : F * (G + H) = F * G + F * H := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_mul F (G + H) a ha, rep_add G H a ha,
    rep_add (F * G) (F * H) a ha, rep_mul F G a ha, rep_mul F H a ha] with z h1 h2 h3 h4 h5
  simp only [Pi.add_apply, Pi.mul_apply] at *
  rw [h1, h2, h3, h4, h5, _root_.mul_add]

lemma inv_zero : (0 : ScalarFunction Ω)⁻¹ = 0 := by
  apply ext_germ
  intro a ha
  filter_upwards [rep_inv 0 a ha, rep_zero a ha] with z h1 h2
  simpa only [Pi.inv_apply, h2, Pi.zero_apply, _root_.inv_zero] using h1

lemma mul_inv_cancel (hconn : IsPreconnected Ω) (F : ScalarFunction Ω) (hF : F ≠ 0) :
    F * F⁻¹ = 1 := by
  have horder (a : ℂ) (ha : a ∈ Ω) : meromorphicOrderAt (representative F) a ≠ ⊤ := by
    intro ho
    apply hF
    apply ext_germ
    intro b hb
    have hob := (representative_meromorphic F).meromorphicOrderAt_eq_top_of_isPreconnected
      hconn ha hb ho
    have he : representative F =ᶠ[𝓝[≠] b] 0 := meromorphicOrderAt_eq_top_iff.mp hob
    exact he.trans (rep_zero b hb).symm
  apply ext_germ
  intro a ha
  have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (representative_meromorphic F a ha)).mp (horder a ha)
  filter_upwards [rep_mul F F⁻¹ a ha, rep_inv F a ha, rep_one a ha, hne] with z h1 h2 h3 h4
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] at *
  rw [h1, h2, h3, mul_inv_cancel₀ h4]

lemma zero_ne_one (hne : Ω.Nonempty) : (0 : ScalarFunction Ω) ≠ 1 := by
  intro he
  obtain ⟨a, ha⟩ := hne
  have hh := congrArg (fun F : ScalarFunction Ω => F.val a) he
  change (ofRepresentative 0 _).val a = (ofRepresentative 1 _).val a at hh
  have hh' : (0 : ℂ) = 1 := OnePoint.coe_injective (by
    simpa only [ofRepresentative_apply _ _ a ha, Pi.zero_def, Pi.one_def, fill_const,
      sphereFinite] using hh)
  exact _root_.zero_ne_one hh'

omit hΩ in
theorem field_exists : ∀ Ω : Set ℂ, IsDomain Ω →
  ∃ I : Field (ScalarFunction Ω), (letI := I;
    EqOn (0 : ScalarFunction Ω).val (fun _ => sphereFinite 0) Ω ∧
    EqOn (1 : ScalarFunction Ω).val (fun _ => sphereFinite 1) Ω ∧
    (∀ F G : ScalarFunction Ω, EqOn (F + G).val (add F.val G.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F * G).val (mul F.val G.val) Ω) ∧
    (∀ F : ScalarFunction Ω, EqOn (-F).val (neg F.val) Ω) ∧
    (∀ F : ScalarFunction Ω, EqOn (F⁻¹).val (inv F.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F - G).val (sub F.val G.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F / G).val (div F.val G.val) Ω)) := by
  intro U hU
  letI : Fact (IsOpen U) := ⟨hU.2.1⟩
  letI : Field (ScalarFunction U) := Field.ofMinimalAxioms (ScalarFunction U)
    add_assoc zero_add neg_add_cancel mul_assoc mul_comm one_mul
    (mul_inv_cancel hU.2.2) inv_zero left_distrib ⟨0, 1, zero_ne_one hU.1⟩
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    change (ofRepresentative 0 _).val a = sphereFinite 0
    rw [ofRepresentative_apply _ _ a ha]
    exact fill_const 0 a
  · intro a ha
    change (ofRepresentative 1 _).val a = sphereFinite 1
    rw [ofRepresentative_apply _ _ a ha]
    exact fill_const 1 a
  · intro F G a ha
    exact ofRepresentative_apply _ _ a ha
  · intro F G a ha
    exact ofRepresentative_apply _ _ a ha
  · intro F a ha
    exact ofRepresentative_apply _ _ a ha
  · intro F a ha
    exact ofRepresentative_apply _ _ a ha
  · intro F G a ha
    change (ofRepresentative (representative F + representative (-G))
      ((representative_meromorphic F).add (representative_meromorphic (-G)))).val a = _
    rw [ofRepresentative_apply _ _ a ha]
    apply fill_congr
    filter_upwards [rep_neg G a ha] with z hz
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at *
    rw [hz, sub_eq_add_neg]
    rfl
  · intro F G a ha
    change (ofRepresentative (representative F * representative G⁻¹)
      ((representative_meromorphic F).mul (representative_meromorphic G⁻¹))).val a = _
    rw [ofRepresentative_apply _ _ a ha]
    apply fill_congr
    filter_upwards [rep_inv G a ha] with z hz
    simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply] at *
    rw [hz, div_eq_mul_inv]
    rfl

end FieldConstruction

/-- Every scalar map gives exactly one function on its open domain with the
fixed outside extension. This connects the field carrier with arbitrary source maps. -/
theorem scalarFunction_restrict (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) :
    ∃ G : ScalarFunction Ω, EqOn G.val F Ω := by
  letI : Fact (IsOpen Ω) := ⟨hF.1⟩
  have hf : MeromorphicOn (scalarFinitePart F) Ω := scalar_meromorphicAt Ω F hF
  refine ⟨FieldConstruction.ofRepresentative (scalarFinitePart F) hf, ?_⟩
  intro a ha
  rw [FieldConstruction.ofRepresentative_apply _ _ a ha]
  exact (scalar_eq_fill Ω F hF ha).symm

theorem scalarFunction_ext (Ω : Set ℂ) (F G : ScalarFunction Ω) :
    EqOn F.val G.val Ω ↔ F = G := by
  constructor
  · intro he
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ Ω
    · exact he ha
    · exact (F.property.2 a ha).trans (G.property.2 a ha).symm
  · rintro rfl
    exact fun _ _ => rfl

end D12Complex.LocalQuotientsArithmetic
