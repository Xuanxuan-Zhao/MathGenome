import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.HyperellipticEvenEnds
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.PunctureCompletion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Explicit even-degree hyperelliptic infinity parameters. The affine curve
has its subtype topology throughout; no surface structure is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.HyperellipticEvenEnds
open Surfaces

lemma reverse_eval_eq (P : Polynomial ℂ) (t : ℂ) (ht : t ≠ 0) :
    P.reverse.eval t = t ^ P.natDegree * P.eval t⁻¹ := by
  letI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) t⁻¹ P
  simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at h
  calc
    P.reverse.eval t = P.reverse.eval t * (t⁻¹ ^ P.natDegree * t ^ P.natDegree) := by
      rw [← mul_pow, inv_mul_cancel₀ ht, one_pow, mul_one]
    _ = (P.reverse.eval t * t⁻¹ ^ P.natDegree) * t ^ P.natDegree := by ring
    _ = P.eval t⁻¹ * t ^ P.natDegree := by rw [h]
    _ = t ^ P.natDegree * P.eval t⁻¹ := by ring

lemma reverse_eval_zero (P : Polynomial ℂ) :
    P.reverse.eval 0 = P.leadingCoeff := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]

lemma exists_local_nonzero_sqrt (P : Polynomial ℂ) (hP : P ≠ 0)
    (c : ℂ) (hc : c ^ 2 = P.leadingCoeff) :
    ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℂ,
      HolomorphicOn (Metric.ball 0 r) h ∧ h 0 = c ∧
      (∀ t ∈ Metric.ball 0 r, h t ^ 2 = P.reverse.eval t) ∧
      (∀ t ∈ Metric.ball 0 r, h t ≠ 0) := by
  have hQ : HolomorphicOn Set.univ (fun t => P.reverse.eval t) :=
    ⟨isOpen_univ, fun t _ => P.reverse.differentiableAt⟩
  have hn : P.reverse.eval 0 ≠ 0 := by
    rw [reverse_eval_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  obtain ⟨U, h, hU0, _, hh, hh0, hsq⟩ :=
    LocalLogarithmsRoots.local_root Set.univ (fun t => P.reverse.eval t) 0 2 c hQ
      (Set.mem_univ _) hn (by norm_num) (by simpa [reverse_eval_zero] using hc)
  have hc0 : c ≠ 0 := by
    intro h0
    have := Polynomial.leadingCoeff_ne_zero.mpr hP
    apply this
    simpa [h0] using hc.symm
  have hnhds : {t | h t ≠ 0} ∈ 𝓝 (0 : ℂ) :=
    (hh.2 0 hU0).continuousAt.eventually_ne (by simpa [hh0] using hc0)
  have hU : U ∩ {t | h t ≠ 0} ∈ 𝓝 (0 : ℂ) :=
    inter_mem (hh.1.mem_nhds hU0) hnhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, h, ⟨Metric.isOpen_ball, fun t ht => hh.2 t (hball ht).1⟩,
    hh0, fun t ht => hsq t (hball ht).1, fun t ht => (hball ht).2⟩

lemma even_substitution (P : Polynomial ℂ) (g : ℕ)
    (hdeg : P.natDegree = 2 * g + 2) (h : ℂ → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hsq : h t ^ 2 = P.reverse.eval t) :
    (h t / t ^ (g + 1)) ^ 2 = P.eval t⁻¹ := by
  rw [div_pow, hsq, reverse_eval_eq P t ht, hdeg]
  have he : 2 * g + 2 = (g + 1) * 2 := by omega
  rw [he, pow_mul]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ ht))

lemma even_sheet_values (P : Polynomial ℂ) (g : ℕ)
    (hdeg : P.natDegree = 2 * g + 2) (h : ℂ → ℂ) (t w : ℂ) (ht : t ≠ 0)
    (hsq : h t ^ 2 = P.reverse.eval t) (hw : w ^ 2 = P.eval t⁻¹) :
    w = h t / t ^ (g + 1) ∨ w = -h t / t ^ (g + 1) := by
  have hp : w ^ 2 = (h t / t ^ (g + 1)) ^ 2 := by
    rw [hw, even_substitution P g hdeg h t ht hsq]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr (by simpa only [neg_div] using hp)

lemma opposite_sheet_values_ne (g : ℕ) (h : ℂ → ℂ) (t : ℂ)
    (ht : t ≠ 0) (hh : h t ≠ 0) :
    h t / t ^ (g + 1) ≠ -h t / t ^ (g + 1) := by
  intro he
  have hn : h t / t ^ (g + 1) ≠ 0 := div_ne_zero hh (pow_ne_zero _ ht)
  have he' : h t / t ^ (g + 1) = -(h t / t ^ (g + 1)) := by
    simpa only [neg_div] using he
  apply hn
  linear_combination (norm := ring_nf) (1 / 2 : ℂ) * he'


lemma normalized_sheet_values (P : Polynomial ℂ) (g : ℕ)
    (hdeg : P.natDegree = 2 * g + 2) (h : ℂ → ℂ) (t w : ℂ) (ht : t ≠ 0)
    (hsq : h t ^ 2 = P.reverse.eval t) (hw : w ^ 2 = P.eval t⁻¹) :
    w * t ^ (g + 1) = h t ∨ w * t ^ (g + 1) = -h t := by
  rcases even_sheet_values P g hdeg h t w ht hsq hw with hw | hw
  · exact Or.inl (by rw [hw, div_mul_cancel₀ _ (pow_ne_zero _ ht)])
  · exact Or.inr (by rw [hw, div_mul_cancel₀ _ (pow_ne_zero _ ht)])

noncomputable def theta (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t) (t : parameterDomain r) : Affine P :=
  ⟨(t.val⁻¹, h t / t.val ^ (g + 1)),
    even_substitution P g hdeg h t t.property.1 (hsq t t.property)⟩

lemma inverse_theta (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t) (t : parameterDomain r) :
    (theta P g r h hdeg hsq t).val.1⁻¹ = t.val := by
  exact inv_inv _

lemma theta_injective (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t) :
    Function.Injective (theta P g r h hdeg hsq) := by
  intro t u he
  apply Subtype.ext
  have he' := congrArg (fun x : Affine P => x.val.1⁻¹) he
  simpa only [inverse_theta] using he'

lemma mem_range_theta_iff (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hnon : ∀ t ∈ parameterDomain r, h t ≠ 0) (x : Affine P) :
    x ∈ Set.range (theta P g r h hdeg hsq) ↔
      x.val.1 ≠ 0 ∧ ‖x.val.1⁻¹‖ < r ∧
        x.val.2 * (x.val.1⁻¹) ^ (g + 1) ≠ -h x.val.1⁻¹ := by
  constructor
  · rintro ⟨t, rfl⟩
    have ht := t.property.1
    change t.val⁻¹ ≠ 0 ∧ ‖t.val⁻¹⁻¹‖ < r ∧
      (h t / t.val ^ (g + 1)) * (t.val⁻¹⁻¹) ^ (g + 1) ≠ -h t.val⁻¹⁻¹
    simp only [inv_inv, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    refine ⟨inv_ne_zero ht, t.property.2, ?_⟩
    intro he
    have hn := hnon t t.property
    apply hn
    linear_combination (norm := ring_nf) (1 / 2 : ℂ) * he
  · rintro ⟨hz, hnorm, hne⟩
    let t : parameterDomain r := ⟨x.val.1⁻¹, inv_ne_zero hz, hnorm⟩
    have heq : x.val.2 * t.val ^ (g + 1) = h t := by
      have hw : x.val.2 ^ 2 = P.eval t.val⁻¹ := by
        simpa only [t, inv_inv] using x.property
      rcases normalized_sheet_values P g hdeg h t x.val.2 t.property.1
        (hsq t t.property) hw with he | he
      · exact he
      · exact (hne he).elim
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact inv_inv _
    · change h t / t.val ^ (g + 1) = x.val.2
      rw [← heq, mul_div_cancel_right₀ _ (pow_ne_zero _ t.property.1)]

lemma neg_root (P : Polynomial ℂ) (r : ℝ) (h : ℂ → ℂ)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t) :
    ∀ t ∈ parameterDomain r, (-h t) ^ 2 = P.reverse.eval t := by
  intro t ht
  simpa only [neg_sq] using hsq t ht

lemma ranges_union (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hnon : ∀ t ∈ parameterDomain r, h t ≠ 0) :
    Set.range (theta P g r h hdeg hsq) ∪
      Set.range (theta P g r (fun t => -h t) hdeg (neg_root P r h hsq)) =
        {x : Affine P | x.val.1 ≠ 0 ∧ ‖x.val.1⁻¹‖ < r} := by
  ext x
  rw [Set.mem_union, mem_range_theta_iff P g r h hdeg hsq hnon,
    mem_range_theta_iff P g r (fun t => -h t) hdeg (neg_root P r h hsq)
      (fun t ht => neg_ne_zero.mpr (hnon t ht))]
  simp only [neg_neg, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hz, hn, _⟩ | ⟨hz, hn, _⟩) <;> exact ⟨hz, hn⟩
  · rintro ⟨hz, hn⟩
    by_cases he : x.val.2 * (x.val.1⁻¹) ^ (g + 1) = -h x.val.1⁻¹
    · right
      refine ⟨hz, hn, ?_⟩
      rw [he]
      have hh := hnon x.val.1⁻¹ ⟨inv_ne_zero hz, hn⟩
      intro he'
      apply hh
      linear_combination (norm := ring_nf) -(1 / 2 : ℂ) * he'
    · exact Or.inl ⟨hz, hn, he⟩

lemma ranges_disjoint (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hnon : ∀ t ∈ parameterDomain r, h t ≠ 0) :
    Disjoint (Set.range (theta P g r h hdeg hsq))
      (Set.range (theta P g r (fun t => -h t) hdeg (neg_root P r h hsq))) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨u, he⟩
  have htu : u.val = t.val := by
    have hp := congrArg (fun y : Affine P => y.val.1⁻¹) he
    simpa only [inverse_theta] using hp
  have hw := congrArg (fun y : Affine P => y.val.2) he
  change -h u / u.val ^ (g + 1) = h t / t.val ^ (g + 1) at hw
  rw [htu] at hw
  exact opposite_sheet_values_ne g h t t.property.1 (hnon t t.property) hw.symm

lemma theta_continuous (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hh : HolomorphicOn (Metric.ball 0 r) h) :
    Continuous (theta P g r h hdeg hsq) := by
  have hval : Continuous (fun t : parameterDomain r => (t : ℂ)) := continuous_subtype_val
  have hhval : Continuous (fun t : parameterDomain r => h t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hh.2 t (by simpa only [Metric.mem_ball, dist_zero_right] using t.property.2)).continuousAt.comp
      continuousAt_subtype_val
  have hinv : Continuous (fun t : parameterDomain r => (t : ℂ)⁻¹) :=
    hval.inv₀ (fun t => t.property.1)
  have hw : Continuous (fun t : parameterDomain r => h t / (t : ℂ) ^ (g + 1)) :=
    hhval.div (hval.pow _) (fun t => pow_ne_zero _ t.property.1)
  exact (hinv.prodMk hw).subtype_mk _

lemma inverse_continuousOn_range (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t) :
    ContinuousOn (fun x : Affine P => x.val.1⁻¹) (Set.range (theta P g r h hdeg hsq)) := by
  rintro x ⟨t, rfl⟩
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_subtype_val.fst.inv₀ (inv_ne_zero t.property.1)

lemma inverse_continuousAt_range (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (x : Affine P) (hx : x ∈ Set.range (theta P g r h hdeg hsq)) :
    ContinuousAt (fun x : Affine P => x.val.1⁻¹) x := by
  rcases hx with ⟨t, rfl⟩
  exact continuousAt_subtype_val.fst.inv₀ (inv_ne_zero t.property.1)


lemma normalized_sheet_isOpen {X : Type*} [TopologicalSpace X]
    (z w : X → ℂ) (hz : Continuous z) (hw : Continuous w)
    (r : ℝ) (h : ℂ → ℂ) (hh : HolomorphicOn (Metric.ball 0 r) h) (n : ℕ) :
    IsOpen {x : X | z x ≠ 0 ∧ ‖(z x)⁻¹‖ < r ∧
      w x * ((z x)⁻¹) ^ n ≠ -h ((z x)⁻¹)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hp : ContinuousAt (fun y => (z y)⁻¹) x := hz.continuousAt.inv₀ hx.1
  have hball : (z x)⁻¹ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2.1
  have hhx : ContinuousAt h ((z x)⁻¹) := (hh.2 _ hball).continuousAt
  have hnon : ∀ᶠ y in 𝓝 x, z y ≠ 0 := hz.continuousAt.eventually_ne hx.1
  have hbound : ∀ᶠ y in 𝓝 x, ‖(z y)⁻¹‖ < r :=
    hp.norm.eventually_lt continuousAt_const hx.2.1
  have hne : ∀ᶠ y in 𝓝 x, w y * ((z y)⁻¹) ^ n ≠ -h ((z y)⁻¹) := by
    have hc := ((hw.continuousAt.mul (hp.pow n)).sub (hhx.comp (f := fun y : X => (z y)⁻¹) hp).neg).eventually_ne
      (sub_ne_zero.mpr hx.2.2)
    filter_upwards [hc] with y hy
    exact sub_ne_zero.mp hy
  filter_upwards [hnon, hbound, hne] with y hyz hyr hyne
  exact ⟨hyz, hyr, hyne⟩


universe u
variable {X : Type u} [TopologicalSpace X]


noncomputable def parameterRangeHomeomorph (U : Set ℂ) (θ : U → X) (p : X → ℂ)
    (hθ : Continuous θ) (hp : ∀ x ∈ range θ, ContinuousAt p x)
    (hleft : ∀ t : U, p (θ t) = t) : U ≃ₜ range θ where
  toFun t := ⟨θ t, mem_range_self t⟩
  invFun x := ⟨p x, by
    obtain ⟨t, ht⟩ := x.property
    rw [← ht, hleft]
    exact t.property⟩
  left_inv t := by
    apply Subtype.ext
    exact hleft t
  right_inv x := by
    obtain ⟨t, ht⟩ := x.property
    apply Subtype.ext
    change θ ⟨p x, _⟩ = x
    calc
      θ ⟨p x, _⟩ = θ t := congrArg θ (Subtype.ext ((congrArg p ht).symm.trans (hleft t)))
      _ = x := ht
  continuous_toFun := hθ.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hp x x.property).comp continuousAt_subtype_val

theorem parameter_isOpenEmbedding (U : Set ℂ) (θ : U → X) (p : X → ℂ)
    (hθ : Continuous θ) (hp : ∀ x ∈ range θ, ContinuousAt p x)
    (hleft : ∀ t : U, p (θ t) = t) (hrange : IsOpen (range θ)) :
    Topology.IsOpenEmbedding θ := by
  exact hrange.isOpenEmbedding_subtypeVal.comp
    (parameterRangeHomeomorph U θ p hθ hp hleft).isOpenEmbedding



noncomputable def inverseParameterChart (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ) : ComplexChart X := by
  letI : Nonempty U := hU.1.to_subtype
  let a := hθ.toOpenPartialHomeomorph θ
  let b := hU.2.1.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → ℂ)
  refine ⟨a.symm.trans b, ?_⟩
  simpa [a, b, OpenPartialHomeomorph.trans_target] using hU


@[simp] theorem inverseParameterChart_source (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ) :
    (inverseParameterChart U hU θ hθ).val.source = range θ := by
  simp [inverseParameterChart, OpenPartialHomeomorph.trans_source]

@[simp] theorem inverseParameterChart_target (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ) :
    (inverseParameterChart U hU θ hθ).val.target = U := by
  simp [inverseParameterChart, OpenPartialHomeomorph.trans_target]

@[simp] theorem inverseParameterChart_apply_parameter (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ) (t : U) :
    (inverseParameterChart U hU θ hθ).val (θ t) = t := by
  letI : Nonempty U := hU.1.to_subtype
  change ((hU.2.1.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : U → ℂ)) ((hθ.toOpenPartialHomeomorph θ).symm (θ t))) = t
  rw [hθ.toOpenPartialHomeomorph_left_inv]
  rfl

@[simp] theorem inverseParameterChart_symm_apply (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ) (t : ℂ) (ht : t ∈ U) :
    (inverseParameterChart U hU θ hθ).val.symm t = θ ⟨t, ht⟩ := by
  have he := inverseParameterChart_apply_parameter U hU θ hθ ⟨t, ht⟩
  exact (congrArg (inverseParameterChart U hU θ hθ).val.symm he.symm).trans
    ((inverseParameterChart U hU θ hθ).val.left_inv (by
      rw [inverseParameterChart_source]
      exact mem_range_self _))

theorem inverseParameterChart_apply (U : Set ℂ) (hU : IsDomain U)
    (θ : U → X) (hθ : Topology.IsOpenEmbedding θ)
    (p : X → ℂ) (hleft : ∀ t : U, p (θ t) = t) (x : X) (hx : x ∈ range θ) :
    (inverseParameterChart U hU θ hθ).val x = p x := by
  obtain ⟨t, rfl⟩ := hx
  rw [inverseParameterChart_apply_parameter, hleft]


/-- A reciprocal end coordinate is compatible with every coordinate projection chart. -/
theorem reciprocal_chart_compatible
    (d e : ComplexChart X) (z w : X → ℂ)
    (hd : ∀ x ∈ d.val.source, d.val x = (z x)⁻¹)
    (hnz : ∀ x ∈ d.val.source, z x ≠ 0)
    (hz : HolomorphicOn d.val.target (z ∘ d.val.symm))
    (hw : HolomorphicOn d.val.target (w ∘ d.val.symm))
    (hez : HolomorphicOn e.val.target (z ∘ e.val.symm))
    (he : EqOn e.val z e.val.source ∨ EqOn e.val w e.val.source) :
    CompatibleCharts d e := by
  let t := d.val.symm.trans e.val
  change BiholomorphicPair t.source t.target t t.symm
  refine ⟨⟨t.open_source, ?_⟩, ⟨t.open_target, ?_⟩,
    t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
  · intro a ha
    have ha' : a ∈ d.val.target ∧ d.val.symm a ∈ e.val.source := ha
    rcases he with he | he
    · apply (hz.2 a ha'.1).congr_of_eventuallyEq
      filter_upwards [t.open_source.mem_nhds ha] with b hb
      exact (he (show d.val.symm b ∈ e.val.source from hb.2))
    · apply (hw.2 a ha'.1).congr_of_eventuallyEq
      filter_upwards [t.open_source.mem_nhds ha] with b hb
      exact (he (show d.val.symm b ∈ e.val.source from hb.2))
  · intro a ha
    have ha' : a ∈ e.val.target ∧ e.val.symm a ∈ d.val.source := ha
    apply ((hez.2 a ha'.1).inv (hnz _ ha'.2)).congr_of_eventuallyEq
    filter_upwards [t.open_target.mem_nhds ha] with b hb
    exact (hd (e.val.symm b) hb.2)

/-- Explicit inverse coordinates imply the regularity used in the compatibility lemma. -/
theorem explicit_inverse_holomorphic
    (d : ComplexChart X) (z w : X → ℂ) (r : ℝ) (h : ℂ → ℂ)
    (c : ℂ) (n : ℕ)
    (ht : d.val.target = {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < r})
    (hh : HolomorphicOn (Metric.ball 0 r) h)
    (hz : ∀ t ∈ d.val.target, z (d.val.symm t) = t⁻¹)
    (hw : ∀ t ∈ d.val.target, w (d.val.symm t) = c * h t / t^n) :
    HolomorphicOn d.val.target (z ∘ d.val.symm) ∧
    HolomorphicOn d.val.target (w ∘ d.val.symm) := by
  constructor
  · refine ⟨d.val.open_target, ?_⟩
    intro a ha
    have ha' : 0 < ‖a‖ ∧ ‖a‖ < r := by simpa only [ht, mem_setOf_eq] using ha
    apply (differentiableAt_id.inv (norm_pos_iff.mp ha'.1)).congr_of_eventuallyEq
    filter_upwards [d.val.open_target.mem_nhds ha] with b hb
    exact hz b hb
  · refine ⟨d.val.open_target, ?_⟩
    intro a ha
    have ha' : 0 < ‖a‖ ∧ ‖a‖ < r := by simpa only [ht, mem_setOf_eq] using ha
    have hab : a ∈ Metric.ball (0 : ℂ) r := by simpa [Metric.mem_ball, dist_zero_right] using ha'.2
    apply ((differentiableAt_const c).mul (hh.2 a hab) |>.div
      (differentiableAt_id.pow n) (pow_ne_zero n (norm_pos_iff.mp ha'.1))).congr_of_eventuallyEq
    filter_upwards [d.val.open_target.mem_nhds ha] with b hb
    exact hw b hb



/-- Each sheet is open by separating its normalized value from the opposite root. -/
lemma theta_range_isOpen (P : Polynomial ℂ) (g : ℕ) (r : ℝ)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hnon : ∀ t ∈ parameterDomain r, h t ≠ 0)
    (hh : HolomorphicOn (Metric.ball 0 r) h) :
    IsOpen (range (theta P g r h hdeg hsq)) := by
  have he : range (theta P g r h hdeg hsq) =
      {x : Affine P | x.val.1 ≠ 0 ∧ ‖x.val.1⁻¹‖ < r ∧
        x.val.2 * (x.val.1⁻¹) ^ (g + 1) ≠ -h x.val.1⁻¹} :=
    Set.ext (fun x => mem_range_theta_iff P g r h hdeg hsq hnon x)
  rw [he]
  exact normalized_sheet_isOpen (fun x : Affine P => x.val.1)
    (fun x => x.val.2) continuous_subtype_val.fst continuous_subtype_val.snd r h hh (g+1)

/-- Construct a genuine inverse chart from one nonvanishing square-root branch. -/
noncomputable def makeSheet (P : Polynomial ℂ) (g : ℕ) (r : ℝ) (hr : 0 < r)
    (h : ℂ → ℂ) (hdeg : P.natDegree = 2 * g + 2)
    (hh : HolomorphicOn (Metric.ball 0 r) h)
    (hsq : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t)
    (hnon : ∀ t ∈ parameterDomain r, h t ≠ 0) : Sheet P g r h := by
  let θ := theta P g r h hdeg hsq
  have hU : IsDomain (parameterDomain r) := by
    simpa only [parameterDomain, norm_pos_iff] using (D12Complex.Ch20.PunctureCompletion.disk_isDomain hr)
  have hθ : Topology.IsOpenEmbedding θ :=
    parameter_isOpenEmbedding (parameterDomain r) θ (fun x => x.val.1⁻¹)
      (theta_continuous P g r h hdeg hsq hh)
      (inverse_continuousAt_range P g r h hdeg hsq)
      (inverse_theta P g r h hdeg hsq)
      (theta_range_isOpen P g r h hdeg hsq hnon hh)
  let d := inverseParameterChart (parameterDomain r) hU θ hθ
  have hdS : d.val.source = range θ := inverseParameterChart_source _ _ _ _
  have hdT : d.val.target = parameterDomain r := inverseParameterChart_target _ _ _ _
  have hdI : ∀ t (ht : t ∈ parameterDomain r), d.val.symm t = θ ⟨t, ht⟩ :=
    inverseParameterChart_symm_apply _ _ _ _
  have hdA : ∀ x ∈ d.val.source, d.val x = x.val.1⁻¹ := by
    intro x hx
    exact inverseParameterChart_apply (parameterDomain r) hU θ hθ (fun y : Affine P => y.val.1⁻¹)
      (inverse_theta P g r h hdeg hsq) x
      (hdS ▸ hx)
  have hnz : ∀ x ∈ d.val.source, x.val.1 ≠ 0 := by
    intro x hx
    obtain ⟨t, rfl⟩ := (show x ∈ range θ from hdS ▸ hx)
    exact inv_ne_zero t.property.1
  have hhol := explicit_inverse_holomorphic d
    (fun x : Affine P => x.val.1) (fun x => x.val.2) r h 1 (g+1)
    (by simpa only [parameterDomain, norm_pos_iff] using hdT) hh
    (fun t ht => by rw [hdI t (hdT ▸ ht)]; rfl)
    (fun t ht => by rw [hdI t (hdT ▸ ht)]; simp only [one_mul]; rfl)
  refine {
    parameter := θ
    parameter_z := fun _ => rfl
    parameter_w := fun _ => rfl
    openEmbedding := hθ
    chart := d
    chart_source := hdS
    chart_target := hdT
    chart_apply := hdA
    chart_inverse := hdI
    left_inverse := fun x hx => d.val.left_inv hx
    right_inverse := fun t ht => d.val.right_inv (hdT.symm ▸ ht)
    inverse_z_holomorphic := hhol.1
    inverse_w_holomorphic := hhol.2
    compatible := ?_
    inverse_base_parameter := ?_ }
  · intro e he
    exact reciprocal_chart_compatible d e (fun x => x.val.1) (fun x => x.val.2)
      hdA hnz hhol.1 hhol.2 he.2.1 he.1
  · intro t ht
    rw [hdI t ht]
    exact inv_inv t

/-- Two open punctured parameter disks at even-degree infinity. -/
theorem even_ends : Specs.D12Complex.Ch21.HyperellipticEvenEnds.even_ends_type := by
  intro P g _hsquarefree hdeg
  have hP : P ≠ 0 := by
    intro he
    simp only [he, Polynomial.natDegree_zero] at hdeg
    omega
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  let c := Complex.exp (Complex.log P.leadingCoeff / 2)
  have hc : c ^ 2 = P.leadingCoeff := by
    change Complex.exp (Complex.log P.leadingCoeff / 2) ^ 2 = _
    rw [pow_two, ← Complex.exp_add]
    convert Complex.exp_log hlead using 1
    congr 1
    ring
  obtain ⟨r, hr, h, hh, hh0, hsq, hnon⟩ := exists_local_nonzero_sqrt P hP c hc
  have hball : ∀ t ∈ parameterDomain r, t ∈ Metric.ball (0 : ℂ) r := by
    intro t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht.2
  have hs : ∀ t ∈ parameterDomain r, h t ^ 2 = P.reverse.eval t :=
    fun t ht => hsq t (hball t ht)
  have hn : ∀ t ∈ parameterDomain r, h t ≠ 0 := fun t ht => hnon t (hball t ht)
  have hm : HolomorphicOn (Metric.ball 0 r) (fun t => -h t) :=
    ⟨hh.1, fun t ht => (hh.2 t ht).neg⟩
  refine ⟨{
    radius := r
    radius_pos := hr
    root := h
    root_holomorphic := hh
    root_nonzero := hnon
    root_square := hsq
    root_zero_square := by rw [hh0]; exact hc
    leadingCoeff_nonzero := hlead
    reverse_extension := ?_
    plus := makeSheet P g r hr h hdeg hh hs hn
    minus := makeSheet P g r hr (fun t => -h t) hdeg hm (neg_root P r h hs)
      (fun t ht => neg_ne_zero.mpr (hn t ht))
    disjoint := ranges_disjoint P g r h hdeg hs hn
    exterior := ranges_union P g r h hdeg hs hn
    inverse_base_holomorphic := ⟨Metric.isOpen_ball, fun _ _ => differentiableAt_id⟩
    inverse_base_order := by
      simpa using (analyticOrderAt_id_sub_const_self (c := (0 : ℂ))) }⟩
  intro t ht
  simpa only [hdeg] using reverse_eval_eq P t ht

end D12Complex.HyperellipticEvenEnds
