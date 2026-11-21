import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.Rouche
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.ArgumentPrinciple
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexOperationsHomotopy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Rouché's theorem (paper.tex:2287–2292) for the canonical finite cycles.
A straight homotopy compares the original parametrized image paths. The
argument principle then gives equality of finite weighted zero sums, after
proving that trace nonvanishing excludes zero germs on relevant components.
The final specializations enumerate the actual zero sets and compare their
ordinary natural multiplicity counts. The Green-region theorem includes the
source's full-boundary coverage condition explicitly.
-/
noncomputable section
open Set Classical
open scoped unitInterval BigOperators Topology

namespace D12Complex.Rouche

/-- The strict Rouché estimate excludes zero at both endpoints. -/
theorem trace_nonzero {f g : ℂ → ℂ} {s : Set ℂ}
    (h : ∀ z ∈ s, ‖g z - f z‖ < ‖f z‖) :
    (∀ z ∈ s, f z ≠ 0) ∧ (∀ z ∈ s, g z ≠ 0) := by
  constructor
  · intro z hz hzero
    have := h z hz
    rw [hzero, norm_zero] at this
    exact (not_lt_of_ge (norm_nonneg _) this)
  · intro z hz hzero
    have hest := h z hz
    rw [hzero, zero_sub, norm_neg] at hest
    exact lt_irrefl _ hest

private theorem affine_mem_interval (γ : PiecewiseC1Path) (t : I) :
    γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ) ∈ Icc γ.path.a γ.path.b := by
  constructor
  · have := mul_nonneg (sub_nonneg.mpr γ.path.ordered) t.property.1
    linarith
  · have := mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr γ.path.ordered)
    linarith

/-- Homotopy of the original parametrized image paths; intermediate paths
need only be continuous. -/
theorem imagePath_index_eq (f g : ℂ → ℂ) (γ : PiecewiseC1Path)
    (hf : AnalyticOnNhd ℂ f γ.trace) (hg : AnalyticOnNhd ℂ g γ.trace)
    (hγ : γ.IsClosed) (h : ∀ z ∈ γ.trace, ‖g z - f z‖ < ‖f z‖) :
    (ArgumentPrinciple.imagePath f γ).index 0 =
      (ArgumentPrinciple.imagePath g γ).index 0 := by
  let p : I → ℂ := fun t => γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))
  have hp : Continuous p :=
    γ.path.continuousOn.comp_continuous
      (continuous_const.add (continuous_const.mul continuous_subtype_val))
      (affine_mem_interval γ)
  have hpTrace (t : I) : p t ∈ γ.trace := ⟨_, affine_mem_interval γ t, rfl⟩
  have hfp : Continuous (fun t : I => f (p t)) :=
    hf.continuousOn.comp_continuous hp hpTrace
  have hgp : Continuous (fun t : I => g (p t)) :=
    hg.continuousOn.comp_continuous hp hpTrace
  let H : C(I × I, ℂ) := ⟨fun q => f (p q.2) + (q.1 : ℝ) * (g (p q.2) - f (p q.2)),
    (hfp.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        ((hgp.comp continuous_snd).sub (hfp.comp continuous_snd)))⟩
  have hn := trace_nonzero h
  have havoid (k : ℂ → ℂ) (hk : AnalyticOnNhd ℂ k γ.trace)
      (hnk : ∀ z ∈ γ.trace, k z ≠ 0) :
      (0 : ℂ) ∉ (ArgumentPrinciple.imagePath k γ).trace := by
    rintro ⟨t, ht, ht0⟩
    rw [ArgumentPrinciple.imagePath_a, ArgumentPrinciple.imagePath_b] at ht
    rw [ArgumentPrinciple.imagePath_apply k γ hk t] at ht0
    exact hnk _ ⟨t, ht, rfl⟩ ht0
  apply IndexOperationsHomotopy.free_loop_index _ _ 0
    (havoid f hf hn.1) (havoid g hg hn.2)
    (ArgumentPrinciple.imagePath_closed f γ hγ)
    (ArgumentPrinciple.imagePath_closed g γ hγ) H
  · intro q hq
    have hest := h (p q.2) (hpTrace q.2)
    have hcoef : ‖((q.1 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg q.1.property.1]
      exact q.1.property.2
    have hsmall : ‖((q.1 : ℝ) : ℂ) * (g (p q.2) - f (p q.2))‖ < ‖f (p q.2)‖ := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans_lt hest
    have heq : ((q.1 : ℝ) : ℂ) * (g (p q.2) - f (p q.2)) = -f (p q.2) := by
      change f (p q.2) + _ = 0 at hq
      exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hq)
    rw [heq, norm_neg] at hsmall
    exact (lt_irrefl _ hsmall)
  · intro t
    simp [H, p, ArgumentPrinciple.imagePath_a, ArgumentPrinciple.imagePath_b,
      ArgumentPrinciple.imagePath_apply f γ hf]
  · intro t
    simp [H, p, ArgumentPrinciple.imagePath_a, ArgumentPrinciple.imagePath_b,
      ArgumentPrinciple.imagePath_apply g γ hg]
  · intro s
    have he : p 0 = p 1 := by
      simpa [p, PiecewiseC1Path.IsClosed, ComplexPath.IsClosed,
        ComplexPath.source, ComplexPath.target] using hγ.symm
    change f (p 0) + _ * (g (p 0) - f (p 0)) =
      f (p 1) + _ * (g (p 1) - f (p 1))
    rw [he]

/-- The logarithmic-derivative integrals of the two functions agree on
any finite cycle satisfying the strict boundary estimate. -/
theorem logDeriv_integral_eq (f g : ℂ → ℂ) (Γ : IntegralCycle)
    (hf : AnalyticOnNhd ℂ f Γ.trace) (hg : AnalyticOnNhd ℂ g Γ.trace)
    (h : ∀ z ∈ Γ.trace, ‖g z - f z‖ < ‖f z‖) :
    Γ.integral (logDeriv f) = Γ.integral (logDeriv g) := by
  change Γ.chain.integral (logDeriv f) = Γ.chain.integral (logDeriv g)
  unfold IntegralChain.integral
  apply Finsupp.sum_congr
  intro γ hγ
  have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
  have hfγ := hf.mono hsub
  have hgγ := hg.mono hsub
  have hγest := fun z hz => h z (hsub hz)
  have hn := trace_nonzero hγest
  have he := imagePath_index_eq f g γ hfγ hgγ (Γ.property γ hγ) hγest
  have havoid (k : ℂ → ℂ) (hk : AnalyticOnNhd ℂ k γ.trace)
      (hnk : ∀ z ∈ γ.trace, k z ≠ 0) :
      (0 : ℂ) ∉ (ArgumentPrinciple.imagePath k γ).trace := by
    rintro ⟨t, ht, ht0⟩
    rw [ArgumentPrinciple.imagePath_a, ArgumentPrinciple.imagePath_b] at ht
    rw [ArgumentPrinciple.imagePath_apply k γ hk t] at ht0
    exact hnk _ ⟨t, ht, rfl⟩ ht0
  rw [IndexOperationsHomotopy.path_index_eq_integral _ _ (havoid f hfγ hn.1),
    IndexOperationsHomotopy.path_index_eq_integral _ _ (havoid g hgγ hn.2)] at he
  simp only [sub_zero] at he
  rw [ArgumentPrinciple.imagePath_reciprocal_integral f γ hfγ hn.1,
    ArgumentPrinciple.imagePath_reciprocal_integral g γ hgγ hn.2] at he
  have hc : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    exact inv_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)
  rw [(mul_left_cancel₀ hc he)]

end D12Complex.Rouche


namespace D12Complex.Rouche

/-- A nonzero-index point lies in an ambient component which meets the trace. -/
theorem component_inter_trace_nonempty {Ω : Set ℂ} (Γ : IntegralCycle)
    (hΩ : IsOpen Ω) (hΓ : Γ.trace ⊆ Ω)
    (hzero : ∀ w, w ∉ Ω → Γ.index w = 0)
    {a : ℂ} (ha : a ∈ Ω) (hix : Γ.index a ≠ 0) :
    ((connectedComponentIn Ω a) ∩ Γ.trace).Nonempty := by
  by_contra hempty
  let C := connectedComponentIn Ω a
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hCtr : C ⊆ Γ.traceᶜ := by
    intro b hb hbt
    exact hempty ⟨b, hb, hbt⟩
  have hCcomp : C ⊆ connectedComponentIn Γ.traceᶜ a :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn haC hCtr
  have hCK : C ⊆ ResidueCycle.filledTrace Γ := by
    intro b hb
    right
    change Γ.index b ≠ 0
    rw [IndexProperties.cycle_index_constant_on_component Γ a (hCtr haC) (hCcomp hb)]
    exact hix
  have hclK : closure C ⊆ ResidueCycle.filledTrace Γ :=
    (closure_minimal hCK (ResidueCycle.filledTrace_isCompact Γ).isClosed)
  have hclΩ : closure C ⊆ Ω :=
    hclK.trans (ResidueCycle.filledTrace_subset Ω Γ hΓ hzero)
  have hclC : closure C ⊆ C :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure haC) hclΩ
  have hCclosed : IsClosed C := isClosed_of_closure_subset hclC
  have hCopen : IsOpen C := hΩ.connectedComponentIn
  have hCuniv : C = univ := IsClopen.eq_univ ⟨hCclosed, hCopen⟩ ⟨a, haC⟩
  have hbuniv : Bornology.IsBounded (univ : Set ℂ) := by
    rw [← hCuniv]
    exact (ResidueCycle.filledTrace_isCompact Γ).isBounded.subset hCK
  exact NormedSpace.unbounded_univ ℂ ℂ hbuniv

/-- Boundary nonvanishing excludes an identically zero relevant component. -/
theorem component_nonzero_of_trace {α : Type*} {Ω : Set ℂ} (Γ : IntegralCycle)
    (hΩ : IsOpen Ω) (hΓ : Γ.trace ⊆ Ω)
    (hzero : ∀ w, w ∉ Ω → Γ.index w = 0)
    (F : ℂ → α) (c : α) (havoid : ∀ z ∈ Γ.trace, F z ≠ c)
    {a : ℂ} (ha : a ∈ Ω) (hix : Γ.index a ≠ 0) :
    ¬ EqOn F (fun _ => c) (connectedComponentIn Ω a) := by
  obtain ⟨b, hbC, hbt⟩ := component_inter_trace_nonempty Γ hΩ hΓ hzero ha hix
  intro he
  exact havoid b hbt (he hbC)


theorem meromorphic_of_holomorphic {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) : ScalarMeromorphicOn Ω (sphereFinite ∘ f) := by
  have hfin (z : ℂ) : (sphereFinite ∘ f) z ≠ sphereInfty := OnePoint.coe_ne_infty _
  have hempty : scalarPoleSet Ω (sphereFinite ∘ f) = ∅ := by
    ext z
    exact iff_false_intro (fun hz => hfin z hz.2)
  refine ⟨hf.1, ?_, ?_, ?_, ?_, ?_⟩
  · have he : {z : Ω | (sphereFinite ∘ f) z = sphereInfty} = ∅ := by
      ext z
      exact iff_false_intro (hfin z)
    rw [he]
    exact isClosed_empty
  · rw [hempty]
    exact Set.subsingleton_empty.isDiscrete
  · have heq : {z | z ∈ Ω ∧ (sphereFinite ∘ f) z ≠ sphereInfty} = Ω := by
      ext z
      exact and_iff_left (hfin z)
    rw [heq]
    have hpart : scalarFinitePart (sphereFinite ∘ f) = f := rfl
    simpa only [hpart] using hf
  · intro a _ ha
    exact (hfin a ha).elim
  · intro a ha
    exact ⟨a, mem_connectedComponentIn ha, hfin a⟩

theorem holomorphic_signed_order {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) {a : ℂ} (ha : a ∈ Ω) {m : ℤ}
    (hm : scalarSignedOrder (sphereFinite ∘ f) a = some m) :
    0 ≤ m ∧ analyticOrderNatAt f a = m.toNat ∧
      LocalZeroFactorization.HasFiniteOrder f a (analyticOrderNatAt f a) := by
  have hc := ArgumentPrinciple.order_classification Ω (sphereFinite ∘ f)
    (meromorphic_of_holomorphic hf) a ha m hm
  have hnot : (sphereFinite ∘ f) a ≠ sphereInfty := OnePoint.coe_ne_infty _
  have hmnonneg : 0 ≤ m := le_of_not_gt (fun hn => hnot (hc.2.1.mpr hn))
  have hfinite : LocalZeroFactorization.HasFiniteOrder f a m.toNat := by
    simpa [scalarFinitePart, Function.comp_def,
      LocalZeroFactorization.HasFiniteOrder, LocalZeroFactorization.HolomorphicNear,
      Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value,
      Specs.D12Complex.Ch05.LocalZeroFactorization.HolomorphicNear_value] using hc.2.2.1 hnot
  have ho : analyticOrderAt f a = (m.toNat : ℕ∞) :=
    (LocalZeroFactorization.order_eq_nat_iff f a ⟨Ω, ha, hf⟩ m.toNat).mpr hfinite
  have hn : analyticOrderNatAt f a = m.toNat := by simp [analyticOrderNatAt, ho]
  exact ⟨hmnonneg, hn, hn.symm ▸ hfinite⟩

theorem holomorphic_argument_principle (Ω : Set ℂ) (Γ : IntegralCycle) (f : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (htrace : Γ.trace ⊆ Ω)
    (hindex : ∀ z, Γ.index z ≠ 0 → z ∈ Ω)
    (havoid : ∀ z ∈ Γ.trace, f z ≠ 0) :
    (∀ a, Γ.index a ≠ 0 →
      LocalZeroFactorization.HasFiniteOrder f a (analyticOrderNatAt f a)) ∧
    (Function.support (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ))).Finite ∧
    Γ.integral (logDeriv f) / (2 * Real.pi * Complex.I : ℂ) =
      ∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ) := by
  have hF := meromorphic_of_holomorphic hf
  have houtside : ∀ z, z ∉ Ω → Γ.index z = 0 := by
    intro z hz
    by_contra hi
    exact hz (hindex z hi)
  have havoidF : ∀ z ∈ Γ.trace,
      (sphereFinite ∘ f) z ≠ sphereFinite 0 ∧ (sphereFinite ∘ f) z ≠ sphereInfty := by
    intro z hz
    refine ⟨?_, OnePoint.coe_ne_infty _⟩
    intro he
    exact havoid z hz (sphereFinite_injective he)
  have hn : ∀ a ∈ Ω, Γ.index a ≠ 0 →
      ¬ EqOn (sphereFinite ∘ f) (fun _ => sphereFinite 0)
        (connectedComponentIn Ω a) := by
    intro a ha hi
    exact component_nonzero_of_trace Γ hf.1 htrace houtside
      (sphereFinite ∘ f) (sphereFinite 0) (fun z hz => (havoidF z hz).1) ha hi
  obtain ⟨horders, hsupp, heq⟩ := ArgumentPrinciple.argument_principle Ω
    (sphereFinite ∘ f) Γ hF htrace havoidF houtside hn
  have hweight : ArgumentPrinciple.weightedOrder (sphereFinite ∘ f) Γ =
      (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ)) := by
    funext a
    by_cases hi : Γ.index a = 0
    · simp [ArgumentPrinciple.weightedOrder, hi]
    obtain ⟨m, hm⟩ := horders a (hindex a hi) hi
    have hc := holomorphic_signed_order hf (hindex a hi) hm
    have hcast : (m.toNat : ℂ) = (m : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hc.1
    simp only [ArgumentPrinciple.weightedOrder, ArgumentPrinciple.order, hm,
      Option.getD_some, hc.2.1, hcast]
  refine ⟨?_, ?_, ?_⟩
  · intro a hi
    obtain ⟨m, hm⟩ := horders a (hindex a hi) hi
    exact (holomorphic_signed_order hf (hindex a hi) hm).2.2
  · rw [← hweight]
    exact hsupp
  · have hpart : scalarFinitePart (sphereFinite ∘ f) = f := rfl
    simpa only [LogarithmicDerivative.coefficient, hpart, hweight] using heq

end D12Complex.Rouche


namespace D12Complex.Rouche

/-- Rouché's theorem for the original finite cycle, with finite local orders
and finite index-weighted sums. The ambient open set may be disconnected. -/
theorem cycle : Specs.D12Complex.Ch09.Rouche.cycle_type := by
  intro Ω Γ f g hf hg htrace hindex hlt
  have hn := trace_nonzero hlt
  obtain ⟨hfo, hff, hfe⟩ := holomorphic_argument_principle Ω Γ f hf htrace hindex hn.1
  obtain ⟨hgo, hgf, hge⟩ := holomorphic_argument_principle Ω Γ g hg htrace hindex hn.2
  have hfa : AnalyticOnNhd ℂ f Γ.trace := fun a ha =>
    (LocalZeroFactorization.holomorphicNear_iff_analyticAt f a).mp ⟨Ω, htrace ha, hf⟩
  have hga : AnalyticOnNhd ℂ g Γ.trace := fun a ha =>
    (LocalZeroFactorization.holomorphicNear_iff_analyticAt g a).mp ⟨Ω, htrace ha, hg⟩
  refine ⟨fun a ha => ⟨hfo a ha, hgo a ha⟩, hff, hgf, ?_⟩
  exact hfe.symm.trans ((congrArg
    (fun w : ℂ => w / (2 * Real.pi * Complex.I : ℂ))
    (logDeriv_integral_eq f g Γ hfa hga hlt)).trans hge)

end D12Complex.Rouche


namespace D12Complex.Rouche

lemma finiteOrder_natOrder {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : LocalZeroFactorization.HolomorphicNear f a)
    (hm : LocalZeroFactorization.HasFiniteOrder f a m) :
    analyticOrderNatAt f a = m := by
  have ho := (LocalZeroFactorization.order_eq_nat_iff f a hf m).mpr hm
  change analyticOrderAt f a = (m : ℕ∞) at ho
  simp [analyticOrderNatAt, ho]

lemma ordinary_counts (D Ω : Set ℂ) (Γ : IntegralCycle) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g) (hDΩ : D ⊆ Ω)
    (hidx : ∀ a, Γ.index a = if a ∈ D then 1 else 0)
    (horders : ∀ a, Γ.index a ≠ 0 → ∃ m n : ℕ,
      LocalZeroFactorization.HasFiniteOrder f a m ∧
      LocalZeroFactorization.HasFiniteOrder g a n)
    (hfinitef : (Function.support (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ))).Finite)
    (hfiniteg : (Function.support (fun a => Γ.index a * (analyticOrderNatAt g a : ℂ))).Finite)
    (heq : (∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ)) =
      ∑ᶠ a, Γ.index a * (analyticOrderNatAt g a : ℂ)) :
    ∃ s t : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ D ∧ f a = 0) ∧
      (∀ a, a ∈ t ↔ a ∈ D ∧ g a = 0) ∧
      (∑ a ∈ s, analyticOrderNatAt f a) = ∑ a ∈ t, analyticOrderNatAt g a := by
  have hsupport (q : ℂ → ℂ) (hq : HolomorphicOn Ω q)
      (hord : ∀ a ∈ D, ∃ m : ℕ, LocalZeroFactorization.HasFiniteOrder q a m) :
      Function.support (fun a => Γ.index a * (analyticOrderNatAt q a : ℂ)) =
        {a | a ∈ D ∧ q a = 0} := by
    ext a
    by_cases ha : a ∈ D
    · obtain ⟨m, hm⟩ := hord a ha
      have hnat := finiteOrder_natOrder ⟨Ω, hDΩ ha, hq⟩ hm
      have hz := LocalZeroFactorization.finiteOrder_zero_iff q a m hm
      have hnz : m ≠ 0 ↔ q a = 0 := Nat.pos_iff_ne_zero.symm.trans hz.symm
      simpa [Function.mem_support, hidx a, ha, hnat] using hnz
    · simp [Function.mem_support, hidx a, ha]
  have hordersD (a : ℂ) (ha : a ∈ D) := horders a (by simp [hidx a, ha])
  have hs := hsupport f hf (fun a ha => by
    obtain ⟨m, n, hm, _⟩ := hordersD a ha
    exact ⟨m, hm⟩)
  have ht := hsupport g hg (fun a ha => by
    obtain ⟨m, n, _, hn⟩ := hordersD a ha
    exact ⟨n, hn⟩)
  let s := hfinitef.toFinset
  let t := hfiniteg.toFinset
  have hsf : ∀ a, a ∈ s ↔ a ∈ D ∧ f a = 0 := by
    intro a
    rw [Set.Finite.mem_toFinset, hs]
    rfl
  have htg : ∀ a, a ∈ t ↔ a ∈ D ∧ g a = 0 := by
    intro a
    rw [Set.Finite.mem_toFinset, ht]
    rfl
  refine ⟨s, t, hsf, htg, ?_⟩
  have hsumf : (∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ)) =
      ((∑ a ∈ s, analyticOrderNatAt f a : ℕ) : ℂ) := by
    rw [finsum_eq_sum_of_support_subset _ (by intro a ha; exact hfinitef.mem_toFinset.mpr ha)]
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp [hidx a, (hsf a).mp ha |>.1]
  have hsumg : (∑ᶠ a, Γ.index a * (analyticOrderNatAt g a : ℂ)) =
      ((∑ a ∈ t, analyticOrderNatAt g a : ℕ) : ℂ) := by
    rw [finsum_eq_sum_of_support_subset _ (by intro a ha; exact hfiniteg.mem_toFinset.mpr ha)]
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp [hidx a, (htg a).mp ha |>.1]
  exact_mod_cast hsumf.symm.trans (heq.trans hsumg)

lemma green_index_indicator (D : Set ℂ) (Γ : IntegralCycle)
    (hD : GreenRegionIndex.SpecifiedGreenRegularRegion D Γ)
    (hfull : frontier D ⊆ Γ.trace) :
    ∀ a, Γ.index a = if a ∈ D then 1 else 0 := by
  obtain ⟨hin, hout⟩ := GreenRegionIndex.specified_green_region_index D Γ hD
  intro a
  by_cases ha : a ∈ D
  · simpa [ha] using hin a ha
  · rw [ite_eq_right ha]
    by_cases hac : a ∈ closure D
    · have haf : a ∈ frontier D := by
        rw [frontier, hD.isOpen.interior_eq]
        exact ⟨hac, ha⟩
      have hat : a ∈ Γ.chain.trace := hfull haf
      simp [IntegralCycle.index, IntegralChain.index, hat]
    · exact hout a hac

def positiveCircle (c : ℂ) (r : ℝ) : IntegralCycle :=
  ⟨Finsupp.single (DiskCauchyFormula.circlePath c r) 1, by
    intro γ hγ
    have he : γ = DiskCauchyFormula.circlePath c r := by simpa using hγ
    subst γ
    exact DiskCauchyFormula.circlePath_closed c r⟩

lemma positiveCircle_trace (c : ℂ) (r : ℝ) (hr : 0 < r) :
    (positiveCircle c r).trace = Metric.sphere c r := by
  change IntegralChain.trace (Finsupp.single (DiskCauchyFormula.circlePath c r) 1) = _
  rw [IndexOperationsHomotopy.single_trace, DiskCauchyFormula.circlePath_trace c r hr.le]

lemma circle_index_indicator (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∀ a, (positiveCircle c r).index a = if a ∈ Metric.ball c r then 1 else 0 := by
  intro a
  have hid : (positiveCircle c r).index a = (DiskCauchyFormula.circlePath c r).index a := rfl
  by_cases ha : a ∈ Metric.ball c r
  · rw [ite_eq_left ha, hid]
    exact IndexComputations.circle_index_interior c a r hr (mem_ball_iff_norm.mp ha)
  · rw [ite_eq_right ha]
    by_cases hat : a ∈ Metric.sphere c r
    · have ht : a ∈ (positiveCircle c r).chain.trace := by
        change a ∈ (positiveCircle c r).trace
        rwa [positiveCircle_trace c r hr]
      simp [IntegralCycle.index, IntegralChain.index, ht]
    · rw [hid]
      apply IndexComputations.circle_index_exterior c a r hr
      have hge : r ≤ ‖a - c‖ := not_lt.mp (mt mem_ball_iff_norm.mpr ha)
      have hne : ‖a - c‖ ≠ r := by simpa only [mem_sphere_iff_norm] using hat
      exact lt_of_le_of_ne hge hne.symm

/-- Ordinary zero counts for the full positive boundary of a specified Green region. -/
theorem region :
    Specs.D12Complex.Ch09.Rouche.region_type := by
  intro D Ω Γ f g hD hfull hf hg htrace hindex hlt
  have hidx := green_index_indicator D Γ hD hfull
  have hin (a : ℂ) (ha : a ∈ D) : Γ.index a ≠ 0 := by simp [hidx a, ha]
  have hDΩ : D ⊆ Ω := fun a ha => hindex a (hin a ha)
  obtain ⟨horders, hfinitef, hfiniteg, heq⟩ := cycle Ω Γ f g hf hg htrace hindex hlt
  refine ⟨fun a ha => horders a (hin a ha), ?_⟩
  apply ordinary_counts D Ω Γ f g hf hg hDΩ hidx _ hfinitef hfiniteg heq
  intro a ha
  exact ⟨analyticOrderNatAt f a, analyticOrderNatAt g a, horders a ha⟩

theorem circle :
    Specs.D12Complex.Ch09.Rouche.circle_type := by
  intro Ω c r f g hr hf hg hclosed hlt
  let Γ := positiveCircle c r
  have hidx := circle_index_indicator c r hr
  have hin (a : ℂ) (ha : a ∈ Metric.ball c r) : Γ.index a ≠ 0 := by
    change (positiveCircle c r).index a ≠ 0
    simp [hidx a, ha]
  have htrace : Γ.trace ⊆ Ω := by
    change (positiveCircle c r).trace ⊆ Ω
    rw [positiveCircle_trace c r hr]
    exact Metric.sphere_subset_closedBall.trans hclosed
  have hindex : ∀ a, Γ.index a ≠ 0 → a ∈ Ω := by
    intro a ha
    apply hclosed
    apply Metric.ball_subset_closedBall
    by_contra hn
    exact ha (by simp [Γ, hidx a, hn])
  have hlt' : ∀ z ∈ Γ.trace, ‖g z - f z‖ < ‖f z‖ := by
    intro z hz
    apply hlt z
    rwa [positiveCircle_trace c r hr] at hz
  obtain ⟨horders, hfinitef, hfiniteg, heq⟩ := cycle Ω Γ f g hf hg htrace hindex hlt'
  refine ⟨fun a ha => horders a (hin a ha), ?_⟩
  apply ordinary_counts (Metric.ball c r) Ω Γ f g hf hg
    (Metric.ball_subset_closedBall.trans hclosed) hidx _ hfinitef hfiniteg heq
  intro a ha
  exact ⟨analyticOrderNatAt f a, analyticOrderNatAt g a, horders a ha⟩
end D12Complex.Rouche
