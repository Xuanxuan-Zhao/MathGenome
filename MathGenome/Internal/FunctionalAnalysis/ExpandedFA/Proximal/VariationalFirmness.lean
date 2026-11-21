import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.VariationalFirmness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.Existence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Tactic.Ring

/-! Variational characterization and firm continuity of proximal maps.
All competitors at infinity are retained. Finite competitors are treated using
real heights, and no bounded-below hypothesis on the original function is used. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def VariationalInequality : VariationalSpec.VariationalInequalityType.{u} :=
  VariationalSpec.VariationalInequalityValue

private lemma square_segment (f u v : H) (t : ℝ) :
    ‖f - ((1 - t) • u + t • v)‖ ^ 2 = ‖f - u‖ ^ 2 -
      2 * t * ⟪f - u, v - u⟫_ℝ + t ^ 2 * ‖v - u‖ ^ 2 := by
  have heq : f - ((1 - t) • u + t • v) = (f - u) - t • (v - u) := by module
  rw [heq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma minimizer_variational (φ : ExtendedFunction H) (hc : ExtendedConvex H φ)
    (μ : ℝ) (hμ : 0 < μ) (f u : H) (hu : IsProximalMinimizer H φ μ f u) :
    VariationalInequality H φ μ f u := by
  refine ⟨hu.1, ?_⟩
  intro v r s hur hvs
  have hsegment (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      ⟪f - u, v - u⟫_ℝ ≤ μ * (s - r) + t * ‖v - u‖ ^ 2 / 2 := by
    let w := (1 - t) • u + t • v
    have hc' : φ w ≤ (((1 - t) * r + t * s : ℝ) : WithTop ℝ) :=
      hc u v r s (1 - t) t hur hvs (by linarith) ht.le (by ring)
    have hh := (hu.2 w).trans (add_le_add hc'
      (le_refl (((‖f - w‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ))))
    change φ u + ((‖f - u‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) ≤ _ at hh
    rw [hur] at hh
    rw [← WithTop.coe_add, ← WithTop.coe_add] at hh
    have hh' := WithTop.coe_le_coe.mp hh
    have hs := square_segment f u v t
    change ‖f - w‖ ^ 2 = _ at hs
    have hden : 0 < 2 * μ := by positivity
    have hmult := (mul_le_mul_of_nonneg_right hh' hden.le)
    have hμ0 : 2 * μ ≠ 0 := ne_of_gt hden
    field_simp [hμ0] at hmult
    have htprod : t * (⟪f - u, v - u⟫_ℝ - μ * (s - r) -
        t * ‖v - u‖ ^ 2 / 2) ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_right htprod ht
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let t := min 1 (ε / (‖v - u‖ ^ 2 + 1))
  have hd : 0 < ‖v - u‖ ^ 2 + 1 := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hd)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hte : t * (‖v - u‖ ^ 2 + 1) ≤ ε :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have hh := hsegment t ht ht1
  nlinarith [sq_nonneg ‖v - u‖]

private lemma variational_minimizer (φ : ExtendedFunction H)
    (μ : ℝ) (hμ : 0 < μ) (f u : H) (hu : VariationalInequality H φ μ f u) :
    IsProximalMinimizer H φ μ f u := by
  refine ⟨hu.1, ?_⟩
  intro v
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  by_cases hv : φ v = ⊤
  · change φ u + _ ≤ φ v + _
    simp [hv]
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv
    have hh := hu.2 v r s hr.symm hs.symm
    have hn := square_segment f u v 1
    simp only [sub_self, zero_smul, one_smul, zero_add, one_pow, mul_one, one_mul] at hn
    change φ u + _ ≤ φ v + _
    rw [← hr, ← hs, ← WithTop.coe_add, ← WithTop.coe_add]
    apply WithTop.coe_le_coe.mpr
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * μ)).mp
    field_simp
    nlinarith [sq_nonneg ‖v - u‖]

theorem minimizer_iff_variational : VariationalSpec.MinimizerIffVariational.{u} := by
  intro H _ _ φ hc μ hμ f u
  exact ⟨minimizer_variational φ hc μ hμ f u, variational_minimizer φ μ hμ f u⟩

theorem variational_iff_subgradient : VariationalSpec.VariationalIffSubgradient.{u} := by
  intro H _ _ φ μ hμ f u
  constructor
  · intro hu
    refine ⟨hu.1, ?_⟩
    intro v
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
    by_cases hv : φ v = ⊤
    · simp [hv]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv
      have hh := hu.2 v r s hr.symm hs.symm
      rw [← hr, ← hs, real_inner_smul_left, ← WithTop.coe_add]
      apply WithTop.coe_le_coe.mpr
      have hd : ⟪f - u, v - u⟫_ℝ / μ ≤ s - r :=
        (div_le_iff₀ hμ).mpr (by nlinarith)
      rw [div_eq_mul_inv] at hd
      nlinarith
  · intro hu
    refine ⟨hu.1, ?_⟩
    intro v r s hr hs
    have hh := hu.2 v
    rw [hr, hs, real_inner_smul_left, ← WithTop.coe_add] at hh
    have hh' := WithTop.coe_le_coe.mp hh
    have heq : μ * (μ⁻¹ * ⟪f - u, v - u⟫_ℝ) = ⟪f - u, v - u⟫_ℝ := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hh' hμ.le]

/-- Re-export the accepted analytic existence result for the full theorem. -/
theorem variational_exists_unique : ExistenceSpec.UniqueMinimizer.{u} :=
  exists_unique_proximalMinimizer

theorem variational_finite_envelope : ExistenceSpec.FiniteEnvelope.{u} :=
  moreauEnvelope_finite

theorem proximalMap_characterization : VariationalSpec.ProximalCharacterization.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f u
  have hmin := minimizer_iff_eq_proximalMap H φ μ f
    (exists_unique_proximalMinimizer H φ hp hc hl μ hμ f) u
  have hvi := hmin.symm.trans (minimizer_iff_variational H φ hc μ hμ f u)
  exact ⟨hvi, hvi.trans (variational_iff_subgradient H φ μ hμ f u)⟩

private lemma firm_of_variational (φ : ExtendedFunction H) (μ : ℝ) (f g u z : H)
    (hu : VariationalInequality H φ μ f u) (hz : VariationalInequality H φ μ g z) :
    ‖u - z‖ ^ 2 ≤ ⟪f - g, u - z⟫_ℝ := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hz.1
  have h1 := hu.2 z r s hr.symm hs.symm
  have h2 := hz.2 u s r hs.symm hr.symm
  have heq : ⟪f - g, u - z⟫_ℝ - ‖u - z‖ ^ 2 =
      -⟪f - u, z - u⟫_ℝ - ⟪g - z, u - z⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm z u]
    ring
  nlinarith

theorem proximalMap_firm : VariationalSpec.FirmBound.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f g
  exact firm_of_variational φ μ f g _ _
    (minimizer_variational φ hc μ hμ f _ (proximalMap_minimizes H φ hp hc hl μ hμ f))
    (minimizer_variational φ hc μ hμ g _ (proximalMap_minimizes H φ hp hc hl μ hμ g))

theorem proximalMap_nonexpansive : VariationalSpec.Nonexpansive.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f g
  have hf := proximalMap_firm H φ hp hc hl μ hμ f g
  have hcs := real_inner_le_norm (f - g) (proximalMap H φ μ f - proximalMap H φ μ g)
  change ‖proximalMap H φ μ f - proximalMap H φ μ g‖ ^ 2 ≤
    ⟪f - g, proximalMap H φ μ f - proximalMap H φ μ g⟫_ℝ at hf
  change ‖proximalMap H φ μ f - proximalMap H φ μ g‖ ≤ ‖f - g‖
  nlinarith [norm_nonneg (proximalMap H φ μ f - proximalMap H φ μ g), norm_nonneg (f - g)]

/-- Indicator objectives have exactly the nearest-point projector, independently
of the positive parameter. -/
theorem proximalMap_indicator : VariationalSpec.IndicatorProjection.{u} := by
  classical
  intro H _ _ _ K hne hclosed hc μ hμ
  let φ : ExtendedFunction H := fun v => if v ∈ K then 0 else ⊤
  have hcφ : ExtendedConvex H φ := by
    intro x y r s a b hx hy ha hb hab
    have hxK : x ∈ K := by
      by_contra hn
      simp [φ, hn] at hx
    have hyK : y ∈ K := by
      by_contra hn
      simp [φ, hn] at hy
    have hr : r = 0 := by simpa [φ, hxK] using hx.symm
    have hs : s = 0 := by simpa [φ, hyK] using hy.symm
    simp [φ, hc hxK hyK ha hb hab, hr, hs]
  let p := Hilbert.Projection.convexProjection ℝ H K hne hclosed hc
  funext f
  have hpvi := (Hilbert.Projection.eq_convexProjection_iff_variational
    ℝ H K hne hclosed hc f (p f)).mp rfl
  have hvp : VariationalInequality H φ μ f (p f) := by
    refine ⟨?_, ?_⟩
    · change φ (p f) ≠ ⊤
      simp [φ, hpvi.1]
    · intro v r s hr hs
      have hvK : v ∈ K := by
        by_contra hn
        simp [φ, hn] at hs
      have hr0 : r = 0 := by simpa [φ, hpvi.1] using hr.symm
      have hs0 : s = 0 := by simpa [φ, hvK] using hs.symm
      simpa [hr0, hs0] using hpvi.2 v hvK
  have hmin := variational_minimizer φ μ hμ f (p f) hvp
  have hP : IsProximalMinimizer H φ μ f (proximalMap H φ μ f) :=
    proximalMap_isMinimizer H φ μ f ⟨p f, hmin⟩
  have hfirm := firm_of_variational φ μ f f (proximalMap H φ μ f) (p f)
    (minimizer_variational φ hcφ μ hμ f _ hP) hvp
  simp only [sub_self, inner_zero_left] at hfirm
  have heq : proximalMap H φ μ f = p f :=
    sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (proximalMap H φ μ f - p f)]))
  exact heq

end ExpandedFA.Proximal
