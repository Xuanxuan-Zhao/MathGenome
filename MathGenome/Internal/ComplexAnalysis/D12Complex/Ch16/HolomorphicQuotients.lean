import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.HolomorphicQuotients
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.OpenSetZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.HolomorphicQuotients

/-- The effective pole divisor is the negative part of the signed divisor,
with its nonnegative integer values converted to natural numbers. -/
def poleDivisor (Ω : Set ℂ) (F : ℂ → RiemannSphere) :
    Function.locallyFinsuppWithin Ω ℕ :=
  (MeromorphicOn.divisor (scalarFinitePart F) Ω).mapRange
    (fun k : ℤ => (-k).toNat) (by simp)

lemma poleDivisor_of_order {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω)
    {m : ℕ} (hm : PoleOfOrderAt (scalarFinitePart F) a m) :
    poleDivisor Ω F a = m := by
  have ho := scalarSignedOrder_pole F a m hm
  change meromorphicOrderAt (scalarFinitePart F) a = (-(m : ℤ) : WithTop ℤ) at ho
  simp [poleDivisor, MeromorphicOn.divisor_apply
    (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF) ha, ho]

lemma poleDivisor_of_finite {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω)
    (hfin : F a ≠ sphereInfty) : poleDivisor Ω F a = 0 := by
  have han := scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin
  have hn : 0 ≤ (meromorphicOrderAt (scalarFinitePart F) a).untop₀ :=
    WithTop.untop₀_nonneg.mpr han.meromorphicOrderAt_nonneg
  simp only [poleDivisor, Function.locallyFinsuppWithin.mapRange_apply,
    MeromorphicOn.divisor_apply (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF) ha]
  exact Int.toNat_eq_zero.mpr (by omega)

lemma poleDivisor_support {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω) :
    poleDivisor Ω F a ≠ 0 ↔ F a = sphereInfty := by
  constructor
  · intro hd
    by_contra hfin
    exact hd (poleDivisor_of_finite hF ha hfin)
  · intro hp
    obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha hp
    rw [poleDivisor_of_order hF ha hm]
    have := hm.1
    omega

lemma denominator_order {Ω : Set ℂ} {d : Function.locallyFinsuppWithin Ω ℕ}
    {h : ℂ → ℂ} (hh : OpenSetZeros.Realizes Ω d h) {a : ℂ} (ha : a ∈ Ω) :
    meromorphicOrderAt h a = ((d a : ℤ) : WithTop ℤ) := by
  have han := HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha
  rw [han.meromorphicOrderAt_eq, hh.2.1 a ha]
  rfl

lemma product_order_nonneg {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {h : ℂ → ℂ}
    (hh : OpenSetZeros.Realizes Ω (poleDivisor Ω F) h) {a : ℂ} (ha : a ∈ Ω) :
    0 ≤ meromorphicOrderAt (h * scalarFinitePart F) a := by
  have hha := HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha
  rw [meromorphicOrderAt_mul hha.meromorphicAt
    (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha)]
  by_cases hfin : F a ≠ sphereInfty
  · exact add_nonneg hha.meromorphicOrderAt_nonneg
      (scalarMeromorphicOn_finite_analytic Ω F hF a ha hfin).meromorphicOrderAt_nonneg
  · obtain ⟨m, hm⟩ := hF.2.2.2.2.1 a ha (not_ne_iff.mp hfin)
    have ho := scalarSignedOrder_pole F a m hm
    change meromorphicOrderAt (scalarFinitePart F) a = (-(m : ℤ) : WithTop ℤ) at ho
    rw [denominator_order hh ha, poleDivisor_of_order hF ha hm, ho]
    simp

/-- Canceling the pole divisor makes the normalized product holomorphic on
the entire original open set. Normalization changes only removable values. -/
lemma numerator_holomorphic {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {h : ℂ → ℂ}
    (hh : OpenSetZeros.Realizes Ω (poleDivisor Ω F) h) :
    HolomorphicOn Ω (toMeromorphicNFOn (h * scalarFinitePart F) Ω) := by
  have hm : MeromorphicOn (h * scalarFinitePart F) Ω := fun a ha =>
    (HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha).meromorphicAt.mul
      (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha)
  refine ⟨hF.1, fun a ha => ?_⟩
  apply AnalyticAt.differentiableAt
  have hn := ((meromorphicNFOn_toMeromorphicNFOn (h * scalarFinitePart F) Ω) ha).meromorphicOrderAt_nonneg_iff_analyticAt
  apply hn.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm ha]
  exact product_order_nonneg hF hh ha

/-- The denominator has finite order, hence is nonzero in a punctured
neighborhood of every point, including its prescribed zeros. -/
lemma denominator_eventually_ne_zero {Ω : Set ℂ} {d : Function.locallyFinsuppWithin Ω ℕ}
    {h : ℂ → ℂ} (hh : OpenSetZeros.Realizes Ω d h) {a : ℂ} (ha : a ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] a, h z ≠ 0 := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha).meromorphicAt).mp
  rw [denominator_order hh ha]
  exact WithTop.coe_ne_top

/-- D12.16.06, with the exact pole divisor and equality of filled quotients.
In particular zero components of F and empty open sets are allowed. -/
theorem holomorphic_quotients :
    Specs.D12Complex.Ch16.HolomorphicQuotients.holomorphic_quotients_type := by
  intro Ω F hF
  let d := poleDivisor Ω F
  obtain ⟨h, hh⟩ := OpenSetZeros.open_set_prescribed_zeros Ω hF.1 d
  let g := toMeromorphicNFOn (h * scalarFinitePart F) Ω
  have hm : MeromorphicOn (h * scalarFinitePart F) Ω := fun a ha =>
    (HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha).meromorphicAt.mul
      (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha)
  have hgerm : ∀ a ∈ Ω, g =ᶠ[𝓝[≠] a] h * scalarFinitePart F :=
    fun _ ha => hm.toMeromorphicNFOn_eq_self_on_nhdsNE ha
  refine ⟨d, g, h, hh, fun a ha => poleDivisor_support hF ha,
    fun a ha m hm => poleDivisor_of_order hF ha hm,
    numerator_holomorphic hF hh, hgerm, ?_, ?_⟩
  · intro a ha
    have han : AnalyticAt ℂ (h * scalarFinitePart F) a :=
      (HolomorphicProducts.analyticAt_of_holomorphic hh.1 ha.1).mul
        (scalarMeromorphicOn_finite_analytic Ω F hF a ha.1 ha.2)
    change toMeromorphicNFOn (h * scalarFinitePart F) Ω a = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm ha.1,
      toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt]
  · intro a ha
    have hquot : g / h =ᶠ[𝓝[≠] a] scalarFinitePart F := by
      filter_upwards [hgerm a ha, denominator_eventually_ne_zero hh ha] with z hz hn
      change g z / h z = scalarFinitePart F z
      rw [show g z = h z * scalarFinitePart F z from hz]
      exact mul_div_cancel_left₀ _ hn
    exact (LocalQuotientsArithmetic.scalar_eq_fill Ω F hF ha).trans
      (LocalQuotientsArithmetic.fill_congr _ _ a hquot).symm

end D12Complex.HolomorphicQuotients
