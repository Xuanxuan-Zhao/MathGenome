import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.ArgumentPrinciple
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch09.LogarithmicDerivative
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GreenRegionIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WindingIndex
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected

/-! The argument principle (paper.tex, D12.09.02).
The filled logarithmic derivative supplies a globally discrete pole set even
when unrelated components carry the identically zero function. Contour
congruence restores the ordinary logarithmic derivative on the original cycle.
The image cycle uses the original interval parametrizations and pushforward
integer coefficients. The final specialization uses supplied real Green
geometry, including its disk-deletion data, for the original positive boundary.
-/
noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology BigOperators

namespace D12Complex.ArgumentPrinciple

def order (F : ℂ → RiemannSphere) (a : ℂ) : ℤ :=
  (scalarSignedOrder F a).getD 0

def weightedOrder (F : ℂ → RiemannSphere) (Γ : IntegralCycle) (a : ℂ) : ℂ :=
  Γ.index a * (order F a : ℂ)

theorem residue_congr_germ {f g : ℂ → ℂ} {a : ℂ} (he : f =ᶠ[𝓝[≠] a] g) :
    Residue.residue f a = Residue.residue g a := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp he)
  unfold Residue.residue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hr)] with ρ hρ hρr
  change 0 < ρ at hρ
  change ρ < r at hρr
  congr 1
  apply circleIntegral.integral_congr hρ.le
  intro z hz
  have hd : dist z a = ρ := Metric.mem_sphere.mp hz
  exact hball (hd.trans_lt hρr) (by
    intro hza
    change z = a at hza
    simp [hza] at hd
    linarith)

theorem coefficient_analytic {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω)
    (hz : F a ≠ sphereFinite 0) (hi : F a ≠ sphereInfty) :
    AnalyticAt ℂ (LogarithmicDerivative.coefficient F) a := by
  have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hi
  have hf0 : scalarFinitePart F a ≠ 0 := by
    rcases sphere_eq_infty_or_finite (F a) with h | ⟨c, hc⟩
    · exact (hi h).elim
    · have hc0 : c ≠ 0 := fun h0 => hz (hc.trans (congrArg sphereFinite h0))
      simpa [scalarFinitePart, hc] using hc0
  exact han.deriv.div han hf0

theorem filled_coefficient_eq {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω)
    (hz : F a ≠ sphereFinite 0) (hi : F a ≠ sphereInfty) :
    LogarithmicDerivative.filled F a =
      sphereFinite (LogarithmicDerivative.coefficient F a) :=
  LocalQuotientsArithmetic.fill_of_analyticAt (coefficient_analytic hF ha hz hi)

theorem argument_principle (Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle)
    (hF : ScalarMeromorphicOn Ω F) (hΓ : Γ.trace ⊆ Ω)
    (havoid : ∀ z ∈ Γ.trace, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty)
    (hzero : ∀ w, w ∉ Ω → Γ.index w = 0)
    (hn : ∀ a ∈ Ω, Γ.index a ≠ 0 →
      ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a)) :
    (∀ a ∈ Ω, Γ.index a ≠ 0 → ∃ m : ℤ, scalarSignedOrder F a = some m) ∧
    (Function.support (weightedOrder F Γ)).Finite ∧
    Γ.integral (LogarithmicDerivative.coefficient F) /
      (2 * Real.pi * Complex.I : ℂ) = ∑ᶠ a, weightedOrder F Γ a := by
  classical
  let G := LogarithmicDerivative.filled F
  let A := scalarPoleSet Ω G
  have hG : ScalarMeromorphicOn Ω G := LogarithmicDerivative.filled_meromorphic Ω F hF
  have hAΩ : A ⊆ Ω := fun a ha => ha.1
  have hclosed : IsClosed ((Subtype.val : Ω → ℂ) ⁻¹' A) := by
    convert hG.2.1 using 1
    ext a
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, A, scalarPoleSet, a.property, true_and]
  have hdis : IsDiscrete A := hG.2.2.1
  have hhol : HolomorphicOn (Ω \ A) (scalarFinitePart G) := by
    have heq : Ω \ A = {z | z ∈ Ω ∧ G z ≠ sphereInfty} := by
      ext a
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, A, scalarPoleSet]
      tauto
    rw [heq]
    exact hG.2.2.2.1
  have hΓG : ∀ a ∈ Γ.trace, G a = sphereFinite (LogarithmicDerivative.coefficient F a) := by
    intro a ha
    exact filled_coefficient_eq hF (hΓ ha) (havoid a ha).1 (havoid a ha).2
  have hdisjoint : Disjoint Γ.trace A := by
    apply Set.disjoint_left.mpr
    intro a ha hA
    exact OnePoint.coe_ne_infty _ ((hΓG a ha).symm.trans hA.2)
  obtain ⟨s, hs, hint⟩ := ResidueCycle.residue_theorem Ω A (scalarFinitePart G) Γ
    hF.1 hAΩ hclosed hdis hhol hΓ hdisjoint hzero
  have hfinite (a : ℂ) (ha : a ∈ Ω) (hix : Γ.index a ≠ 0) :
      ∃ m : ℤ, scalarSignedOrder F a = some m :=
    LogarithmicDerivative.finite_order_on_component hF ha (hn a ha hix)
  have hsupport : Function.support (weightedOrder F Γ) ⊆ s := by
    intro a ha
    have hix : Γ.index a ≠ 0 := by
      intro hx
      exact ha (by simp [weightedOrder, hx])
    have haΩ : a ∈ Ω := by
      by_contra h
      exact hix (hzero a h)
    obtain ⟨m, hm⟩ := hfinite a haΩ hix
    have hm0 : m ≠ 0 := by
      intro hz
      exact ha (by simp [weightedOrder, order, hm, hz])
    have hGA : G a = sphereInfty :=
      (LogarithmicDerivative.local_pole_classification Ω F hF a haΩ m hm).1.mpr hm0
    exact (hs a).mpr ⟨⟨haΩ, hGA⟩, hix⟩
  refine ⟨hfinite, s.finite_toSet.subset hsupport, ?_⟩
  have hres (a : ℂ) (ha : a ∈ s) :
      Γ.index a * Residue.residue (scalarFinitePart G) a = weightedOrder F Γ a := by
    have haA := ((hs a).mp ha).1
    have haΩ : a ∈ Ω := haA.1
    obtain ⟨m, hm⟩ := hfinite a haΩ ((hs a).mp ha).2
    have hgerm : scalarFinitePart G =ᶠ[𝓝[≠] a] LogarithmicDerivative.coefficient F :=
      LocalQuotientsArithmetic.finitePart_fill_germ
        (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a haΩ).logDeriv
    have hr : Residue.residue (LogarithmicDerivative.coefficient F) a = (m : ℂ) :=
      (LogarithmicDerivative.residue_eq_order Ω F hF a haΩ m hm).1
    rw [residue_congr_germ hgerm, hr]
    simp [weightedOrder, order, hm]
  have heq : Γ.integral (LogarithmicDerivative.coefficient F) =
      Γ.integral (scalarFinitePart G) := by
    apply FiniteCycleCauchy.chain_integral_congr
    intro a ha
    simp [scalarFinitePart, hΓG a ha]
  rw [heq, hint, Finset.sum_congr rfl hres,
    finsum_eq_sum_of_support_subset _ hsupport]
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

end D12Complex.ArgumentPrinciple


namespace D12Complex.ArgumentPrinciple

def analyticImagePath (f : ℂ → ℂ) (γ : PiecewiseC1Path)
    (hf : AnalyticOnNhd ℂ f γ.trace) : PiecewiseC1Path := by
  let δ : ComplexPath := ⟨γ.path.a, γ.path.b, γ.path.ordered, f ∘ γ,
    hf.continuousOn.comp γ.path.continuousOn (fun t ht => ⟨t, ht, rfl⟩)⟩
  refine ⟨δ, ⟨{
    count := γ.partition.count
    node := γ.partition.node
    strictMono := γ.partition.strictMono
    first := γ.partition.first
    last := γ.partition.last
    smooth := ?_ }⟩⟩
  intro i
  have hC : ContDiffOn ℝ 1 f γ.trace := fun z hz =>
    ((hf z hz).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  exact hC.comp (γ.partition.smooth i) (fun t ht =>
    ⟨t, γ.partition.piece_subset i ht, rfl⟩)

def imagePath (f : ℂ → ℂ) (γ : PiecewiseC1Path) : PiecewiseC1Path :=
  if hf : AnalyticOnNhd ℂ f γ.trace then analyticImagePath f γ hf else γ

theorem imagePath_eq (f : ℂ → ℂ) (γ : PiecewiseC1Path)
    (hf : AnalyticOnNhd ℂ f γ.trace) :
    imagePath f γ = analyticImagePath f γ hf := by simp [imagePath, hf]

@[simp] theorem imagePath_a (f : ℂ → ℂ) (γ : PiecewiseC1Path) :
    (imagePath f γ).path.a = γ.path.a := by
  unfold imagePath
  split_ifs <;> rfl

@[simp] theorem imagePath_b (f : ℂ → ℂ) (γ : PiecewiseC1Path) :
    (imagePath f γ).path.b = γ.path.b := by
  unfold imagePath
  split_ifs <;> rfl

theorem imagePath_apply (f : ℂ → ℂ) (γ : PiecewiseC1Path)
    (hf : AnalyticOnNhd ℂ f γ.trace) (t : ℝ) :
    imagePath f γ t = f (γ t) := by rw [imagePath_eq f γ hf]; rfl

theorem imagePath_closed (f : ℂ → ℂ) (γ : PiecewiseC1Path) (hγ : γ.IsClosed) :
    (imagePath f γ).IsClosed := by
  unfold imagePath
  split_ifs with hf
  · exact congrArg f hγ
  · exact hγ

def imageChain (f : ℂ → ℂ) (Γ : IntegralChain) : IntegralChain :=
  Γ.mapDomain (imagePath f)

def imageCycle (f : ℂ → ℂ) (Γ : IntegralCycle) : IntegralCycle :=
  ⟨imageChain f Γ.chain, by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hδ)
    exact imagePath_closed f γ (Γ.property γ hγ)⟩

theorem imageChain_trace_subset (f : ℂ → ℂ) (Γ : IntegralChain)
    (hf : AnalyticOnNhd ℂ f Γ.trace) : (imageChain f Γ).trace ⊆ f '' Γ.trace := by
  rintro z ⟨δ, hδ, t, ht, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hδ)
  have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
  have hfg := hf.mono hsub
  rw [imagePath_a, imagePath_b] at ht
  exact ⟨γ t, hsub ⟨t, ht, rfl⟩, (imagePath_apply f γ hfg t).symm⟩

theorem imageChain_integral (f : ℂ → ℂ) (Γ : IntegralChain) (g : ℂ → ℂ) :
    (imageChain f Γ).integral g =
      Γ.sum (fun γ m => (m : ℂ) * (imagePath f γ).integral g) := by
  unfold imageChain IntegralChain.integral
  apply Finsupp.sum_mapDomain_index
  · intro δ; simp
  · intro δ m n; simp [add_mul]

theorem imagePath_reciprocal_integral (f : ℂ → ℂ) (γ : PiecewiseC1Path)
    (hf : AnalyticOnNhd ℂ f γ.trace) (h0 : ∀ z ∈ γ.trace, f z ≠ 0) :
    (imagePath f γ).integral (fun z => 1 / z) = γ.integral (logDeriv f) := by
  have hfη : ContinuousOn (fun z : ℂ => 1 / z) (imagePath f γ).trace := by
    apply continuousOn_const.div continuousOn_id
    rintro z ⟨t, ht, rfl⟩
    rw [imagePath_a, imagePath_b] at ht
    rw [imagePath_apply f γ hf t]
    exact h0 _ ⟨t, ht, rfl⟩
  have hld : ContinuousOn (logDeriv f) γ.trace := by
    intro z hz
    exact ((hf z hz).deriv.continuousAt.div (hf z hz).continuousAt (h0 z hz)).continuousWithinAt
  rw [PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral _ _ _ hfη,
    PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral _ _ _ hld,
    imagePath_a, imagePath_b]
  have hpieces (i : Fin γ.partition.count) :
      (∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
        (1 / imagePath f γ t) * deriv (imagePath f γ) t) =
      ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
        logDeriv f (γ t) * deriv γ t := by
    apply intervalIntegral.integral_congr_Ioo_of_le (γ.partition.piece_lt i).le
    intro t ht
    have hγ := γ.partition.differentiableAt_piece i ht
    have hft := (hf (γ t) ⟨t, γ.partition.piece_subset i ⟨ht.1.le, ht.2.le⟩, rfl⟩).differentiableAt
    have hder : deriv (imagePath f γ) t = deriv f (γ t) * deriv γ t := by
      rw [imagePath_eq f γ hf]
      change deriv (f ∘ (γ : ℝ → ℂ)) t = _
      simpa [mul_comm] using (hft.hasDerivAt.scomp t hγ.hasDerivAt).deriv
    change (1 / imagePath f γ t) * deriv (imagePath f γ) t = logDeriv f (γ t) * deriv γ t
    rw [hder, imagePath_apply f γ hf t, logDeriv_apply]
    ring
  have hη := C1Partition.parameter_integrable (imagePath f γ).path
    (imagePath f γ).partition (fun z => 1 / z) hfη
  rw [imagePath_a, imagePath_b] at hη
  have hηpiece (i : Fin γ.partition.count) : IntervalIntegrable
      (fun t => (1 / imagePath f γ t) * deriv (imagePath f γ) t) volume
      (γ.partition.node i.castSucc) (γ.partition.node i.succ) := by
    apply hη.mono_set
    rw [uIcc_of_le (γ.partition.piece_lt i).le, uIcc_of_le γ.path.ordered]
    exact γ.partition.piece_subset i
  have hp := intervalIntegral_fin_partition γ.partition.node
    (fun t => (1 / imagePath f γ t) * deriv (imagePath f γ) t) hηpiece
  rw [γ.partition.first, γ.partition.last] at hp
  have hldp := intervalIntegral_fin_partition γ.partition.node
    (fun t => logDeriv f (γ t) * deriv γ t) (γ.partition.piece_integrable_deriv (logDeriv f) hld)
  rw [γ.partition.first, γ.partition.last] at hldp
  rw [← hp.2, ← hldp.2]
  exact Finset.sum_congr rfl (fun i _ => hpieces i)

theorem imageCycle_index (f : ℂ → ℂ) (Γ : IntegralCycle)
    (hf : AnalyticOnNhd ℂ f Γ.trace) (h0 : ∀ z ∈ Γ.trace, f z ≠ 0) :
    (imageCycle f Γ).index 0 =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Γ.integral (logDeriv f) := by
  have ha : (0 : ℂ) ∉ (imageCycle f Γ).trace := by
    intro hz
    obtain ⟨z, hz, hfz⟩ := imageChain_trace_subset f Γ.chain hf hz
    exact h0 z hz hfz
  rw [IntegralCycle.index_eq_integral _ _ ha]
  congr 1
  simp only [sub_zero]
  change (imageChain f Γ.chain).integral (fun z => 1 / z) = Γ.chain.integral (logDeriv f)
  rw [imageChain_integral]
  apply Finsupp.sum_congr
  intro γ hγ
  have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
  rw [imagePath_reciprocal_integral f γ (hf.mono hsub) (fun z hz => h0 z (hsub hz))]

end D12Complex.ArgumentPrinciple

namespace D12Complex.ArgumentPrinciple

theorem image_index (Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle)
    (hF : ScalarMeromorphicOn Ω F) (htrace : Γ.trace ⊆ Ω)
    (havoid : ∀ z ∈ Γ.trace, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty) :
    ∃ p : PiecewiseC1Path → PiecewiseC1Path,
      (∀ γ ∈ Γ.chain.support, (p γ).path.a = γ.path.a ∧
        (p γ).path.b = γ.path.b ∧ ∀ t, p γ t = scalarFinitePart F (γ t)) ∧
      ∃ Δ : IntegralCycle, Δ.chain = Γ.chain.mapDomain p ∧ 0 ∉ Δ.trace ∧
        Γ.integral (Specs.D12Complex.Ch09.LogarithmicDerivative.Objects.coefficient F) /
          (2 * (Real.pi : ℂ) * Complex.I) = Δ.index 0 := by
  let f := scalarFinitePart F
  have hf : AnalyticOnNhd ℂ f Γ.trace := fun z hz =>
    scalarMeromorphicOn_finite_analytic Ω F hF z (htrace hz) (havoid z hz).2
  have h0 : ∀ z ∈ Γ.trace, f z ≠ 0 := by
    intro z hz hzero
    obtain hinf | ⟨c, hc⟩ := sphere_eq_infty_or_finite (F z)
    · exact (havoid z hz).2 hinf
    · apply (havoid z hz).1
      change finiteCoordinate (F z) = 0 at hzero
      rw [hc, finiteCoordinate_sphereFinite] at hzero
      exact hc.trans (congrArg sphereFinite hzero)
  refine ⟨imagePath f, ?_, imageCycle f Γ, rfl, ?_, ?_⟩
  · intro γ hγ
    have hsub : γ.trace ⊆ Γ.trace := fun z hz => ⟨γ, hγ, hz⟩
    exact ⟨imagePath_a _ _, imagePath_b _ _, imagePath_apply f γ (hf.mono hsub)⟩
  · intro hz
    obtain ⟨z, hz, hfz⟩ := imageChain_trace_subset f Γ.chain hf hz
    exact h0 z hz hfz
  · rw [imageCycle_index f Γ hf h0]
    change Γ.integral (logDeriv f) / _ = _
    rw [div_eq_mul_inv, mul_comm]

end D12Complex.ArgumentPrinciple


namespace D12Complex.ArgumentPrinciple

theorem order_classification :
    Specs.D12Complex.Ch09.ArgumentPrinciple.order_classification_type := by
  intro Ω F hF a ha m hm
  have hmf : meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) := hm
  have hp : F a = sphereInfty ↔ m < 0 := by
    rw [LocalQuotientsArithmetic.scalar_eq_fill Ω F hF ha]
    change LocalQuotientsArithmetic.fill (scalarFinitePart F) a = sphereInfty ↔ m < 0
    rw [LocalQuotientsArithmetic.fill_eq_infty_iff, hmf]
    exact WithTop.coe_lt_coe
  have hfinite (h : F a ≠ sphereInfty) :
      Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value
        (scalarFinitePart F) a m.toNat := by
    have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha h
    have ho := scalarSignedOrder_finite Ω F hF a ha h
    rw [hm] at ho
    cases hn : analyticOrderAt (scalarFinitePart F) a with
    | top => simp [hn] at ho
    | coe n =>
      have heq : m = (n : ℤ) := by
        rw [hn] at ho
        change some m = some (n : ℤ) at ho
        exact Option.some.inj ho
      rw [heq, Int.toNat_natCast]
      exact (LocalZeroFactorization.order_eq_nat_iff _ _
        ((LocalZeroFactorization.holomorphicNear_iff_analyticAt _ _).mpr han) n).mp hn
  refine ⟨?_, hp, hfinite, ?_⟩
  · constructor
    · intro hz
      have hn : F a ≠ sphereInfty := by rw [hz]; exact OnePoint.coe_ne_infty _
      have hzero : scalarFinitePart F a = 0 := by simp [scalarFinitePart, hz]
      have hpos := (LocalZeroFactorization.finiteOrder_zero_iff _ _ _ (hfinite hn)).mp hzero
      omega
    · intro hmpos
      have hn : F a ≠ sphereInfty := fun h => (by have := hp.mp h; omega)
      have hzero : scalarFinitePart F a = 0 :=
        (LocalZeroFactorization.finiteOrder_zero_iff _ _ _ (hfinite hn)).mpr (by omega)
      obtain hinf | ⟨c, hc⟩ := sphere_eq_infty_or_finite (F a)
      · exact (hn hinf).elim
      · have hc0 : c = 0 := by simpa [scalarFinitePart, hc] using hzero
        exact hc.trans (congrArg sphereFinite hc0)
  · intro hi
    have hneg := hp.mp hi
    apply LocalQuotientsArithmetic.poleOfOrder_of_order
      (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha) (-m).toNat (by omega)
    have he : m = -((-m).toNat : ℤ) := by omega
    exact hmf.trans (congrArg (fun k : ℤ => (k : WithTop ℤ)) he)

end D12Complex.ArgumentPrinciple


namespace D12Complex.ArgumentPrinciple
lemma component_nonzero_of_boundary_regular {D Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hΩ : IsOpen Ω) (hclosure : closure D ⊆ Ω)
    (hboundary : ∀ b ∈ frontier D, F b ≠ sphereFinite 0)
    {a : ℂ} (ha : a ∈ D) :
    ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a) := by
  intro hzero
  let C := connectedComponentIn Ω a
  have haΩ : a ∈ Ω := hclosure (subset_closure ha)
  have haC : a ∈ C := mem_connectedComponentIn haΩ
  have hCD : C ⊆ D := by
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hD ⟨a, haC, ha⟩
    intro b hb
    by_contra hbD
    have hbfront : b ∈ frontier D := by
      rw [frontier, hD.interior_eq]
      exact ⟨hb.1, hbD⟩
    exact hboundary b hbfront (hzero hb.2)
  have hclΩ : closure C ⊆ Ω := (closure_mono hCD).trans hclosure
  have hclC : closure C ⊆ C :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure haC) hclΩ
  have hCclosed : IsClosed C := isClosed_of_closure_subset hclC
  have hCopen : IsOpen C := hΩ.connectedComponentIn
  have hCuniv : C = univ := (IsClopen.eq_univ ⟨hCclosed, hCopen⟩ ⟨a, haC⟩)
  have hbuniv : Bornology.IsBounded (univ : Set ℂ) := by
    rw [← hCuniv]
    exact hbounded.subset hCD
  exact NormedSpace.unbounded_univ ℂ ℂ hbuniv

theorem region_count (D Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle)
    (hD : GreenRegionIndex.SpecifiedGreenRegularRegion D Γ)
    (hF : ScalarMeromorphicOn Ω F) (hclosure : closure D ⊆ Ω)
    (hboundary : ∀ z ∈ frontier D, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty) :
    (∀ a ∈ D, ∃ m : ℤ, scalarSignedOrder F a = some m) ∧
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ D ∧ (F a = sphereFinite 0 ∨ F a = sphereInfty)) ∧
      Γ.integral (LogarithmicDerivative.coefficient F) /
        (2 * Real.pi * Complex.I : ℂ) =
        ((∑ a ∈ s, (order F a).toNat : ℕ) : ℂ) -
        ((∑ a ∈ s, (-(order F a)).toNat : ℕ) : ℂ) := by
  have hnonzero : ∀ a ∈ D, ¬ EqOn F (fun _ => sphereFinite 0)
      (connectedComponentIn Ω a) := fun a ha =>
    component_nonzero_of_boundary_regular hD.isOpen hD.bounded hF.1 hclosure
      (fun b hb => (hboundary b hb).1) ha
  have horders : ∀ a ∈ D, ∃ m : ℤ, scalarSignedOrder F a = some m := by
    intro a ha
    exact LogarithmicDerivative.finite_order_on_component hF
      (hclosure (subset_closure ha)) (hnonzero a ha)
  have hi := GreenRegionIndex.specified_green_region_index D Γ hD
  have htraceΩ : Γ.trace ⊆ Ω := fun z hz => hclosure (hD.boundary_trace hz).1
  have htraceRegular : ∀ z ∈ Γ.trace, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty :=
    fun z hz => hboundary z (hD.boundary_trace hz)
  have houtside : ∀ w, w ∉ Ω → Γ.index w = 0 := by
    intro w hw
    exact hi.2 w (fun hc => hw (hclosure hc))
  have hrelevant : ∀ a ∈ Ω, Γ.index a ≠ 0 → ¬ EqOn F (fun _ => sphereFinite 0)
      (connectedComponentIn Ω a) := by
    intro a ha hidx
    by_cases haD : a ∈ D
    · exact hnonzero a haD
    · by_cases hac : a ∈ closure D
      · intro hz
        have hf : a ∈ frontier D := by
          rw [frontier, hD.isOpen.interior_eq]
          exact ⟨hac, haD⟩
        exact (hboundary a hf).1 (hz (mem_connectedComponentIn ha))
      · exact (hidx (hi.2 a hac)).elim
  obtain ⟨_, hfinite, heq⟩ := argument_principle Ω F Γ hF htraceΩ htraceRegular houtside hrelevant
  refine ⟨horders, hfinite.toFinset, ?_, ?_⟩
  · intro a
    rw [hfinite.mem_toFinset, Function.mem_support]
    by_cases haD : a ∈ D
    · obtain ⟨m, hm⟩ := horders a haD
      have haΩ : a ∈ Ω := hclosure (subset_closure haD)
      have hr := LogarithmicDerivative.order_zero_iff_regular hF haΩ
      have hz : m = 0 ↔ F a ≠ sphereFinite 0 ∧ F a ≠ sphereInfty := by
        simpa only [hm, Option.some.injEq] using hr
      simp only [ArgumentPrinciple.weightedOrder, hi.1 a haD, one_mul,
        ArgumentPrinciple.order, hm, Option.getD_some, Int.cast_ne_zero,
        haD, true_and]
      tauto
    · simp only [haD, false_and, iff_false]
      by_cases hac : a ∈ closure D
      · have hf : a ∈ frontier D := by
          rw [frontier, hD.isOpen.interior_eq]
          exact ⟨hac, haD⟩
        have ho : scalarSignedOrder F a = some 0 :=
          (LogarithmicDerivative.order_zero_iff_regular hF (hclosure hac)).mpr (hboundary a hf)
        simp [ArgumentPrinciple.weightedOrder, ArgumentPrinciple.order, ho]
      · simp [ArgumentPrinciple.weightedOrder, hi.2 a hac]
  · rw [heq, finsum_eq_sum_of_support_subset _ (by intro a ha; exact hfinite.mem_toFinset.mpr ha)]
    have hs : ∀ a ∈ hfinite.toFinset, a ∈ D := by
      intro a ha
      have hw : ArgumentPrinciple.weightedOrder F Γ a ≠ 0 := hfinite.mem_toFinset.mp ha
      by_contra haD
      by_cases hac : a ∈ closure D
      · have hf : a ∈ frontier D := by
          rw [frontier, hD.isOpen.interior_eq]
          exact ⟨hac, haD⟩
        have ho : scalarSignedOrder F a = some 0 :=
          (LogarithmicDerivative.order_zero_iff_regular hF (hclosure hac)).mpr (hboundary a hf)
        exact hw (by simp [ArgumentPrinciple.weightedOrder, ArgumentPrinciple.order, ho])
      · exact hw (by simp [ArgumentPrinciple.weightedOrder, hi.2 a hac])
    simp only [Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ArgumentPrinciple.weightedOrder, hi.1 a (hs a ha), one_mul]
    exact_mod_cast (Int.toNat_sub_toNat_neg (ArgumentPrinciple.order F a)).symm
end D12Complex.ArgumentPrinciple
