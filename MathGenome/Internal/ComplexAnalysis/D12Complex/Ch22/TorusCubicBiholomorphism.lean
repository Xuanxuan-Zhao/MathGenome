import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicBiholomorphism
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusCubicLocalMap
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassDegreeBranching
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The global identification of the torus with its literal projective cubic.
Degree two exhausts the even fibres, and the odd derivative separates the two
classes. The inverse in local coordinates is proved to be the inverse of the
global homeomorphism, so the infinity inverse branch is included. -/
noncomputable section
open Set Filter
open scoped Topology Classical BigOperators
namespace D12Complex.TorusCubicBiholomorphism
open TorusSurface CubicFiniteCharts CubicInfinityChart
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open TorusCubicLocalMap (phi IsCubicChart QuotientLocalInverseAt)

lemma homogeneous_nonsingular {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (heq : homogeneousEquation (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) v = 0) :
    v 2 ^ 2 + 2 * g₂ ω₁ ω₂ * v 1 * v 0 + 3 * g₃ ω₁ ω₂ * v 0 ^ 2 ≠ 0 ∨
    -12 * v 1 ^ 2 + g₂ ω₁ ω₂ * v 0 ^ 2 ≠ 0 ∨
    2 * v 2 * v 0 ≠ 0 := by
  by_cases hz : v 0 = 0
  · have hx : v 1 = 0 := by
      have hcube : v 1 ^ 3 = 0 := by
        unfold homogeneousEquation at heq
        simp only [hz, mul_zero, zero_pow (by decide : 2 ≠ 0),
          zero_pow (by decide : 3 ≠ 0), add_zero, zero_sub] at heq
        exact (mul_eq_zero.mp (neg_eq_zero.mp heq)).resolve_left (by norm_num)
      exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hcube
    have hy : v 2 ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i <;> simp [hz, hx, hy]
    left
    simpa [hz] using pow_ne_zero 2 hy
  · have heq' : (v 2 / v 0) ^ 2 =
        q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (v 1 / v 0) := by
      unfold q
      field_simp [hz]
      unfold homogeneousEquation at heq
      linear_combination heq
    rcases nonsingular ω₁ ω₂ h₁ h₂ _ _ heq' with hy | hx
    · right; right
      have hY : v 2 ≠ 0 := by
        intro hY
        exact hy (by simp [hY])
      exact mul_ne_zero (mul_ne_zero (by norm_num) hY) hz
    · right; left
      intro hX
      apply hx
      field_simp [hz]
      linear_combination -hX

lemma wp_surjective {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (c : ℂ) :
    ∃ z : ℂ, z ∉ lattice ω₁ ω₂ ∧ weierstrassP ω₁ ω₂ z = c := by
  classical
  obtain ⟨d, S, F, hd, hS, hF, hhol, hInf, hhalf, horder, hfib, hram, hvals⟩ :=
    Ch22.WeierstrassDegreeBranching.degree_branching ω₁ ω₂ h₁ h₂
  obtain ⟨D, hD, hM, hsum⟩ := hfib (sphereFinite c)
  have hDne : D ≠ 0 := by
    intro hz
    simp [hz] at hsum
  obtain ⟨t, ht⟩ : ∃ t, D t ≠ 0 := by
    by_contra h
    push Not at h
    exact hDne (Finsupp.ext h)
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup t
  have hval := (hD _).mp ht
  change F (projection ω₁ ω₂ z) = sphereFinite c at hval
  rw [Ch22.WeierstrassDegreeBranching.descent_apply hF z] at hval
  have hz : z ∉ lattice ω₁ ω₂ := by
    intro hz
    simp [Specs.D12Complex.Ch22.WeierstrassDegreeBranching.planeMap, hz,
      sphereInfty, sphereFinite] at hval
  refine ⟨z, hz, ?_⟩
  simpa [Specs.D12Complex.Ch22.WeierstrassDegreeBranching.planeMap, hz,
    sphereFinite_injective.eq_iff] using hval

lemma finite_values_surjective {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (x y : ℂ)
    (hxy : y ^ 2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x) :
    ∃ z : ℂ, z ∉ lattice ω₁ ω₂ ∧ weierstrassP ω₁ ω₂ z = x ∧
      deriv (weierstrassP ω₁ ω₂) z = y := by
  obtain ⟨z, hz, hx⟩ := wp_surjective h₁ h₂ x
  have hsq : deriv (weierstrassP ω₁ ω₂) z ^ 2 = y ^ 2 := by
    rw [Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz, hx]
    exact hxy.symm
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hy | hy
  · exact ⟨z, hz, hx, hy⟩
  · have hnz : -z ∉ lattice ω₁ ω₂ := by simpa using hz
    have hneg : weierstrassP ω₁ ω₂ (-z) = weierstrassP ω₁ ω₂ z :=
      (Ch22.WeierstrassSeries.periodPair h₁ h₂).weierstrassP_neg z
    have hderiv : deriv (weierstrassP ω₁ ω₂) (-z) =
        -deriv (weierstrassP ω₁ ω₂) z := by
      change deriv (Ch22.WeierstrassSeries.periodPair h₁ h₂).weierstrassP (-z) =
        -deriv (Ch22.WeierstrassSeries.periodPair h₁ h₂).weierstrassP z
      rw [(Ch22.WeierstrassSeries.periodPair h₁ h₂).deriv_weierstrassP]
      exact (Ch22.WeierstrassSeries.periodPair h₁ h₂).derivWeierstrassP_neg z
    exact ⟨-z, hnz, hneg.trans hx, by rw [hderiv, hy, neg_neg]⟩

lemma finite_surjectivity {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (x y : ℂ) (hxy : y ^ 2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x) :
    ∃ t : Torus ω₁ ω₂, phi ω₁ ω₂ t = affinePoint x y := by
  obtain ⟨z, hz, hx, hy⟩ := finite_values_surjective h₁ h₂ x y hxy
  refine ⟨projection ω₁ ω₂ z, ?_⟩
  rw [TorusCubicLocalMap.phi_finite h₁ h₂ hz]
  change affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) = _
  rw [hx, hy]

lemma phi_surjective {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (p : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) :
    ∃ t : Torus ω₁ ω₂, TorusCubicLocalMap.phi ω₁ ω₂ t = p.val := by
  classical
  by_cases hp : p.val ∈ ProjectivePlaneTopology.coordinatePatch 0
  · have hxy := (affine_equation _ _ _ hp).mp p.property
    obtain ⟨t, ht⟩ := finite_surjectivity h₁ h₂ _ _ hxy
    exact ⟨t, ht.trans (affinePoint_coordinates hp)⟩
  · refine ⟨0, ?_⟩
    rw [TorusCubicLocalMap.phi_zero h₁ h₂]
    exact (eq_O_of_not_finite _ _ p.property hp).symm

theorem compact_connected_surface_of_bijective
    (ω₁ ω₂ : ℂ) (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ t, (F t).val = phi ω₁ ω₂ t) (hbij : Function.Bijective F) :
    ConnectedSpace (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ∧
    CompactSpace (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ∧
    (∃ S : Surfaces.RiemannSurface (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)),
      ∀ e ∈ S.atlas, IsCubicChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) e.val) ∧
    ∃ h : Torus ω₁ ω₂ ≃ₜ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂), (h : _ → _) = F := by
  obtain ⟨hcT, hT2T, hscT, hcompT⟩ := TorusSurface.topology ω₁ ω₂ h₁ h₂
  let := hcT
  let := hcompT
  have hcont := (TorusCubicLocalMap.locally_biholomorphic ω₁ ω₂ h₁ h₂ F hF).1
  have hcE := hbij.2.connectedSpace hcont
  obtain ⟨hneE, hcompE, hT2E, hscE, A, hA, hreg⟩ :=
    CubicInfinityChart.complex_manifold ω₁ ω₂ h₁ h₂
  let := hT2E
  let e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) := Equiv.ofBijective F hbij
  have hce : Continuous e := hcont
  let h := e.toHomeomorphOfContinuousClosed hce hce.isClosedMap
  exact ⟨hcE, hcompE, ⟨⟨hcE, hT2E, hscE, A, hA⟩, hreg⟩, h, rfl⟩

lemma pair_symm {U V : Set ℂ} {f g : ℂ → ℂ}
    (h : BiholomorphicPair U V f g) : BiholomorphicPair V U g f :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma global_inverse_coordinates {ω₁ ω₂ G H : ℂ}
    (h : Torus ω₁ ω₂ ≃ Cubic G H) (t : Torus ω₁ ω₂)
    (hl : QuotientLocalInverseAt h t) :
    ∃ d : ℝ, Separation ω₁ ω₂ d ∧
      ∃ s ∈ quotientAtlas ω₁ ω₂ d, t ∈ s.val.source ∧
        ∃ e : OpenPartialHomeomorph (Cubic G H) ℂ, IsCubicChart G H e ∧
          ∃ U V : Set ℂ, s.val t ∈ U ∧ U ⊆ s.val.target ∧ V ⊆ e.target ∧
            MapsTo (h ∘ s.val.symm) U e.source ∧
            BiholomorphicPair U V (e ∘ h ∘ s.val.symm)
              (s.val ∘ h.symm ∘ e.symm) := by
  obtain ⟨d, hd, s, hs, hts, e, he, U, V, g, ht, hU, hmap, hb⟩ := hl
  have hV : V ⊆ e.target := by
    intro y hy
    have hgy := hb.2.2.2.1 hy
    have hxy := hb.2.2.2.2.2 hy
    exact hxy ▸ e.map_source (hmap hgy)
  have heq : EqOn (s.val ∘ h.symm ∘ e.symm) g V := by
    intro y hy
    have hgy := hb.2.2.2.1 hy
    have hxy := hb.2.2.2.2.2 hy
    have hpoint : h (s.val.symm (g y)) = e.symm y :=
      (e.left_inv (hmap hgy)).symm.trans (congrArg e.symm hxy)
    change s.val (h.symm (e.symm y)) = g y
    rw [← hpoint, h.symm_apply_apply, s.val.right_inv (hU hgy)]
  exact ⟨d, hd, s, hs, hts, e, he, U, V, ht, hU, hV, hmap,
    pair_symm (TorusCubicLocalMap.biholomorphicPair_congr_left (pair_symm hb) heq)⟩

namespace ChartBridge
open TorusSurface CubicFiniteCharts CubicInfinityChart TorusCubicLocalMap Surfaces
open private Refines exists_domain_subchart regular_refinements from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.CubicInfinityChart

lemma quotientAtlas_mono {ω₁ ω₂ : ℂ} {d d' : ℝ} (hdd : d ≤ d') :
    quotientAtlas ω₁ ω₂ d ⊆ quotientAtlas ω₁ ω₂ d' := by
  rintro e ⟨a, r, hr, hd, ht, hi⟩
  exact ⟨a, r, hr, hd.trans_le (div_le_div_of_nonneg_right hdd (by norm_num)), ht, hi⟩

lemma quotientCharts_compatible {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {d d' : ℝ} {e f : ComplexChart (Torus ω₁ ω₂)}
    (he : e ∈ quotientAtlas ω₁ ω₂ d) (hf : f ∈ quotientAtlas ω₁ ω₂ d') :
    CompatibleCharts e f := by
  have he' := quotientAtlas_mono (le_max_left d d') he
  have hf' := quotientAtlas_mono (le_max_right d d') hf
  let t := e.val.symm.trans f.val
  exact ⟨TorusSurface.holomorphic_transition h₁ h₂ he' hf',
    TorusSurface.holomorphic_transition h₁ h₂ hf' he',
    t.mapsTo, t.mapsTo_symm, t.leftInvOn, t.rightInvOn⟩

lemma cubicCharts_compatible {G H : ℂ} {e f : ComplexChart (Cubic G H)}
    (he : IsCubicChart G H e.val) (hf : IsCubicChart G H f.val) :
    CompatibleCharts e f := by
  rcases he with he | ⟨axis, he⟩ <;> rcases hf with hf | ⟨axis', hf⟩
  · exact infinity_transitions G H e.val f.val he hf
  · exact compatibleCharts_symm
      (finite_infinity_transitions G H axis' f.val e.val hf he)
  · exact finite_infinity_transitions G H axis e.val f.val he hf
  · exact CubicFiniteCharts.transitions G H axis axis' e.val f.val he hf

lemma cubic_domain_subchart {G H : ℂ} (e : OpenPartialHomeomorph (Cubic G H) ℂ)
    (he : IsCubicChart G H e) (p : Cubic G H) (hp : p ∈ e.source) :
    ∃ c : ComplexChart (Cubic G H), p ∈ c.val.source ∧
      IsCubicChart G H c.val ∧ (c.val : _ → _) = e ∧
      (c.val.symm : _ → _) = e.symm := by
  obtain ⟨c, hc, hce⟩ := exists_domain_subchart e p hp
  exact ⟨c, hc, regular_refinements hce he, hce.2.2.1, hce.2.2.2⟩

/-- Transport both inverse coordinate germs into the fixed natural atlases. -/
lemma global_holomorphic_from_local {ω₁ ω₂ G H : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (h : Torus ω₁ ω₂ ≃ₜ Cubic G H)
    (S : RiemannSurface (Torus ω₁ ω₂)) (T : RiemannSurface (Cubic G H))
    (d₀ : ℝ) (hS : S.atlas = quotientAtlas ω₁ ω₂ d₀)
    (hT : ∀ e ∈ T.atlas, IsCubicChart G H e.val)
    (hl : ∀ t, QuotientLocalInverseAt h t) :
    HolomorphicMap S T h ∧ HolomorphicMap T S h.symm := by
  have hboth (t : Torus ω₁ ω₂) :
      HolomorphicMapAt S T h t ∧ HolomorphicMapAt T S h.symm (h t) := by
    obtain ⟨d, hd, s, hs, hts, e, he, U, V, ht, hU, hV, hmap, hb⟩ :=
      global_inverse_coordinates h.toEquiv t (hl t)
    have hte : h t ∈ e.source := by
      simpa only [Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv, Function.comp_apply, s.val.left_inv hts] using hmap ht
    obtain ⟨c, htc, hcc, hcmap, hcinv⟩ := cubic_domain_subchart e he (h t) hte
    obtain ⟨s₀, hs₀, hts₀⟩ := S.isAtlas.1 t
    obtain ⟨c₀, hc₀, htc₀⟩ := T.isAtlas.1 (h t)
    have hs₀' : s₀ ∈ quotientAtlas ω₁ ω₂ d₀ := hS ▸ hs₀
    have hsrc : CompatibleCharts s₀ s := quotientCharts_compatible h₁ h₂ hs₀' hs
    have htgt : CompatibleCharts c c₀ := cubicCharts_compatible hcc (hT c₀ hc₀)
    have hlocal : HolomorphicGermAt (coordinateMap s c h) (s.val t) := by
      refine ⟨U, ht, ?_⟩
      change HolomorphicOn U (c.val ∘ h ∘ s.val.symm)
      simpa only [hcmap, Homeomorph.coe_toEquiv] using hb.1
    have hval : e (h t) ∈ V := by
      simpa only [Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv, Function.comp_apply, s.val.left_inv hts] using hb.2.2.1 ht
    have hilocal : HolomorphicGermAt (coordinateMap c s h.symm) (c.val (h t)) := by
      refine ⟨V, ?_, ?_⟩
      · simpa only [hcmap] using hval
      · change HolomorphicOn V (s.val ∘ h.symm ∘ c.val.symm)
        simpa only [hcinv, Homeomorph.coe_symm_toEquiv] using hb.2.1
    constructor
    · refine ⟨h.continuous.continuousAt, s₀, hs₀, c₀, hc₀, hts₀, htc₀, ?_⟩
      exact coordinate_germ_change h.continuous.continuousAt hsrc htgt hts hts₀ htc htc₀ hlocal
    · refine ⟨h.symm.continuous.continuousAt, c₀, hc₀, s₀, hs₀, htc₀, ?_, ?_⟩
      · simpa only [h.symm_apply_apply] using hts₀
      · apply coordinate_germ_change h.symm.continuous.continuousAt
          (compatibleCharts_symm htgt) (compatibleCharts_symm hsrc) htc htc₀
        · simpa only [h.symm_apply_apply] using hts
        · simpa only [h.symm_apply_apply] using hts₀
        · exact hilocal
  constructor
  · exact fun t => (hboth t).1
  · intro p
    simpa only [h.apply_symm_apply] using (hboth (h.symm p)).2
end ChartBridge

namespace Fibres
open D12Complex TorusSurface
open D12Complex.Ch22
open Specs.D12Complex.Ch22.WeierstrassDegreeBranching
open _root_.D12Complex.Ch22.WeierstrassSeries (periodPair)

/-- A degree-two fibre is exhausted by a point and its negative; when those
classes coincide, its multiplicity two exhausts the fibre by itself. -/
lemma two_fiber_points {A : Type*} [AddGroup A] (D : A →₀ ℕ)
    (hD : D.sum (fun _ n => n) = 2) (q r : A)
    (hq : D q ≠ 0) (hnq : D (-q) ≠ 0) (hr : D r ≠ 0)
    (hm : q = -q → D q = 2) : r = q ∨ r = -q := by
  classical
  by_contra h
  obtain ⟨hrq, hrnq⟩ := not_or.mp h
  have hqr : q ≠ r := Ne.symm hrq
  have hnqr : -q ≠ r := Ne.symm hrnq
  by_cases hqnq : q = -q
  · have hb := HalfPeriodValues.finite_sum_le D {q, r}
    simp only [Finset.sum_insert, Finset.mem_singleton, hqr, not_false_eq_true,
      Finset.sum_singleton] at hb
    rw [hD, hm hqnq] at hb
    omega
  · have hb := HalfPeriodValues.finite_sum_le D {q, -q, r}
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      hqnq, hqr, hnqr, or_self, not_false_eq_true, Finset.sum_singleton] at hb
    rw [hD] at hb
    omega

lemma self_neg_multiplicity {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {q : Torus ω₁ ω₂} (hq : q = -q) : multiplicity ω₁ ω₂ q = 2 := by
  classical
  apply ite_eq_left
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · have hq2 : (2 : ℕ) • q = 0 := by
      rw [two_nsmul]
      exact (congrArg (· + q) hq).trans (neg_add_cancel q)
    obtain ⟨i, hi⟩ := ((HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.2 q).mp ⟨hq0, hq2⟩
    exact Or.inr ⟨i, hi.symm⟩

/-- Evenness supplies the two classes in the degree-two fibre. -/
lemma wp_eq_imp_projection_eq_or_neg {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z w : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hw : w ∉ lattice ω₁ ω₂)
    (he : weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w) :
    projection ω₁ ω₂ w = projection ω₁ ω₂ z ∨
      projection ω₁ ω₂ w = -projection ω₁ ω₂ z := by
  classical
  obtain ⟨F, hF, _⟩ := descent ω₁ ω₂ RiemannSphere (planeMap ω₁ ω₂)
    (WeierstrassDegreeBranching.planeMap_periodic h₁ h₂)
  obtain ⟨D, hD, hm, ht⟩ :=
    WeierstrassDegreeBranching.finite_fiber_divisor h₁ h₂ hF (weierstrassP ω₁ ω₂ z)
  have hzF : F (projection ω₁ ω₂ z) = sphereFinite (weierstrassP ω₁ ω₂ z) := by
    rw [WeierstrassDegreeBranching.descent_apply hF]
    simp [planeMap, hz]
  have hnz : -z ∉ lattice ω₁ ω₂ := by simpa using hz
  have hnzF : F (-projection ω₁ ω₂ z) = sphereFinite (weierstrassP ω₁ ω₂ z) := by
    rw [← map_neg, WeierstrassDegreeBranching.descent_apply hF]
    simp only [planeMap, ite_eq_right hnz]
    exact congrArg sphereFinite ((periodPair h₁ h₂).weierstrassP_neg z)
  have hwF : F (projection ω₁ ω₂ w) = sphereFinite (weierstrassP ω₁ ω₂ z) := by
    rw [WeierstrassDegreeBranching.descent_apply hF]
    simp [planeMap, hw, he]
  apply two_fiber_points D ht (projection ω₁ ω₂ z) (projection ω₁ ω₂ w)
    ((hD _).mpr hzF) ((hD _).mpr hnzF) ((hD _).mpr hwF)
  intro hq
  exact (hm _ hzF).trans (self_neg_multiplicity h₁ h₂ hq)

lemma deriv_eq_of_projection_eq {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z w : ℂ} (he : projection ω₁ ω₂ z = projection ω₁ ω₂ w) :
    deriv (weierstrassP ω₁ ω₂) z = deriv (weierstrassP ω₁ ω₂) w := by
  let L := periodPair h₁ h₂
  change deriv L.weierstrassP z = deriv L.weierstrassP w
  rw [L.deriv_weierstrassP]
  have h := L.derivWeierstrassP_add_coe w
    ⟨z - w, (projection_eq_iff z w).mp he⟩
  convert h using 1 <;> (congr 1; ring)

lemma deriv_neg {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (z : ℂ) :
    deriv (weierstrassP ω₁ ω₂) (-z) = -deriv (weierstrassP ω₁ ω₂) z := by
  change deriv (periodPair h₁ h₂).weierstrassP (-z) =
    -deriv (periodPair h₁ h₂).weierstrassP z
  rw [(periodPair h₁ h₂).deriv_weierstrassP]
  exact (periodPair h₁ h₂).derivWeierstrassP_neg z

lemma deriv_zero_imp_projection_self_neg {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hd : deriv (weierstrassP ω₁ ω₂) z = 0) :
    projection ω₁ ω₂ z = -projection ω₁ ω₂ z := by
  have hhalf := (HalfPeriodValues.zeros ω₁ ω₂ h₁ h₂ z hz).mp hd
  have ht := ((HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.2 _).mpr hhalf
  apply eq_neg_of_add_eq_zero_left
  simpa only [two_nsmul] using ht.2

lemma wp_deriv_separates {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z w : ℂ} (hz : z ∉ lattice ω₁ ω₂) (hw : w ∉ lattice ω₁ ω₂)
    (he : weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w)
    (hd : deriv (weierstrassP ω₁ ω₂) z = deriv (weierstrassP ω₁ ω₂) w) :
    projection ω₁ ω₂ z = projection ω₁ ω₂ w := by
  rcases wp_eq_imp_projection_eq_or_neg h₁ h₂ hz hw he with h | h
  · exact h.symm
  · have hn : projection ω₁ ω₂ w = projection ω₁ ω₂ (-z) := by simpa using h
    have hneg := deriv_eq_of_projection_eq h₁ h₂ hn
    rw [deriv_neg h₁ h₂] at hneg
    have hd0 : deriv (weierstrassP ω₁ ω₂) z = 0 :=
      CharZero.eq_neg_self_iff.mp (hd.trans hneg)
    exact (deriv_zero_imp_projection_self_neg h₁ h₂ hz hd0).trans h.symm

lemma wp_eq_of_projection_eq {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z w : ℂ} (he : projection ω₁ ω₂ z = projection ω₁ ω₂ w) :
    weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w := by
  apply periodic_eq_of_projection_eq (f := weierstrassP ω₁ ω₂) ?_ he
  intro a l hl
  exact (periodPair h₁ h₂).weierstrassP_add_coe a ⟨l, hl⟩

theorem fibre_separation : ∀ ω₁ ω₂ : ℂ,
    ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z w : ℂ,
    z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
      (weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w ↔
        projection ω₁ ω₂ w = projection ω₁ ω₂ z ∨
        projection ω₁ ω₂ w = -projection ω₁ ω₂ z) := by
  intro ω₁ ω₂ h₁ h₂ z w hz hw
  refine ⟨wp_eq_imp_projection_eq_or_neg h₁ h₂ hz hw, ?_⟩
  rintro (h | h)
  · exact (wp_eq_of_projection_eq h₁ h₂ h).symm
  · have hn : projection ω₁ ω₂ w = projection ω₁ ω₂ (-z) := by simpa using h
    exact ((wp_eq_of_projection_eq h₁ h₂ hn).trans
      ((periodPair h₁ h₂).weierstrassP_neg z)).symm

theorem derivative_separation : ∀ ω₁ ω₂ : ℂ,
    ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    (∀ z w : ℂ, z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
      (weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w ∧
        deriv (weierstrassP ω₁ ω₂) z = deriv (weierstrassP ω₁ ω₂) w ↔
          projection ω₁ ω₂ w = projection ω₁ ω₂ z)) ∧
    (∀ z : ℂ, z ∉ lattice ω₁ ω₂ →
      (deriv (weierstrassP ω₁ ω₂) z = 0 ↔
        projection ω₁ ω₂ z = -projection ω₁ ω₂ z)) := by
  intro ω₁ ω₂ h₁ h₂
  constructor
  · intro z w hz hw
    constructor
    · intro h
      exact (wp_deriv_separates h₁ h₂ hz hw h.1 h.2).symm
    · intro h
      exact ⟨wp_eq_of_projection_eq h₁ h₂ h.symm, deriv_eq_of_projection_eq h₁ h₂ h.symm⟩
  · intro z hz
    refine ⟨deriv_zero_imp_projection_self_neg h₁ h₂ hz, ?_⟩
    intro h
    have hn : projection ω₁ ω₂ z = projection ω₁ ω₂ (-z) := by simpa using h
    have hd := deriv_eq_of_projection_eq h₁ h₂ hn
    rw [deriv_neg h₁ h₂] at hd
    exact CharZero.eq_neg_self_iff.mp hd

lemma phi_injective {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    Function.Injective (_root_.D12Complex.TorusCubicLocalMap.phi ω₁ ω₂) := by
  intro q r heq
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup r
  change projection ω₁ ω₂ z = projection ω₁ ω₂ w
  change _root_.D12Complex.TorusCubicLocalMap.phi ω₁ ω₂ (projection ω₁ ω₂ z) =
    _root_.D12Complex.TorusCubicLocalMap.phi ω₁ ω₂ (projection ω₁ ω₂ w) at heq
  rw [_root_.D12Complex.TorusCubicLocalMap.phi_projection h₁ h₂ z,
    _root_.D12Complex.TorusCubicLocalMap.phi_projection h₁ h₂ w] at heq
  by_cases hz : z ∈ lattice ω₁ ω₂
  · by_cases hw : w ∈ lattice ω₁ ω₂
    · exact ((HalfPeriodValues.projection_zero_iff z).mpr hz).trans
        ((HalfPeriodValues.projection_zero_iff w).mpr hw).symm
    · have hm := CubicFiniteCharts.affinePoint_mem_patch
        (weierstrassP ω₁ ω₂ w) (deriv (weierstrassP ω₁ ω₂) w)
      simp only [_root_.D12Complex.TorusCubicLocalMap.planeMap, ite_eq_left hz, ite_eq_right hw] at heq
      rw [← heq] at hm
      exact (CubicInfinityChart.O_not_mem_finitePatch hm).elim
  · by_cases hw : w ∈ lattice ω₁ ω₂
    · have hm := CubicFiniteCharts.affinePoint_mem_patch
        (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z)
      simp only [_root_.D12Complex.TorusCubicLocalMap.planeMap, ite_eq_right hz, ite_eq_left hw] at heq
      rw [heq] at hm
      exact (CubicInfinityChart.O_not_mem_finitePatch hm).elim
    · simp only [_root_.D12Complex.TorusCubicLocalMap.planeMap, ite_eq_right hz, ite_eq_right hw] at heq
      apply wp_deriv_separates h₁ h₂ hz hw
      · simpa only [CubicFiniteCharts.finiteX_affinePoint] using
          congrArg CubicFiniteCharts.finiteX heq
      · simpa only [CubicFiniteCharts.finiteY_affinePoint] using
          congrArg CubicFiniteCharts.finiteY heq

end Fibres

theorem nonsingular : Specs.D12Complex.Ch22.TorusCubicBiholomorphism.nonsingular_type := by
  intro ω₁ ω₂ h₁ h₂ v hv
  exact homogeneous_nonsingular h₁ h₂ v.val v.property hv

theorem surjectivity : Specs.D12Complex.Ch22.TorusCubicBiholomorphism.surjectivity_type := by
  intro ω₁ ω₂ h₁ h₂
  exact ⟨finite_values_surjective h₁ h₂, phi_surjective h₁ h₂⟩

theorem degree_branching :
    Specs.D12Complex.Ch22.TorusCubicBiholomorphism.degree_branching_type :=
  Ch22.WeierstrassDegreeBranching.degree_branching

theorem infinity_bridge :
    Specs.D12Complex.Ch22.TorusCubicBiholomorphism.infinity_bridge_type :=
  TorusCubicLocalMap.infinity_bridge

theorem fibre_separation :
    Specs.D12Complex.Ch22.TorusCubicBiholomorphism.fibre_separation_type :=
  Fibres.fibre_separation

theorem derivative_separation :
    Specs.D12Complex.Ch22.TorusCubicBiholomorphism.derivative_separation_type :=
  Fibres.derivative_separation

theorem pole_fibre : Specs.D12Complex.Ch22.TorusCubicBiholomorphism.pole_fibre_type := by
  intro ω₁ ω₂ h₁ h₂ t
  constructor
  · intro ht
    apply Fibres.phi_injective h₁ h₂
    exact ht.trans (TorusCubicLocalMap.phi_zero h₁ h₂).symm
  · rintro rfl
    exact TorusCubicLocalMap.phi_zero h₁ h₂

theorem biholomorphism :
    Specs.D12Complex.Ch22.TorusCubicBiholomorphism.biholomorphism_type := by
  intro ω₁ ω₂ h₁ h₂
  let F := TorusCubicLocalMap.map h₁ h₂
  have hF : ∀ t, (F t).val = phi ω₁ ω₂ t := fun _ => rfl
  have hbij : Function.Bijective F := by
    constructor
    · intro t s hts
      exact Fibres.phi_injective h₁ h₂ (congrArg Subtype.val hts)
    · intro p
      obtain ⟨t, ht⟩ := phi_surjective h₁ h₂ p
      exact ⟨t, Subtype.ext ht⟩
  obtain ⟨_, hcompE, ⟨T, hT⟩, h, heq⟩ :=
    compact_connected_surface_of_bijective ω₁ ω₂ h₁ h₂ F hF hbij
  have hh : ∀ t, (h t).val = phi ω₁ ω₂ t := by
    intro t
    rw [heq]
    exact hF t
  obtain ⟨d, hd, _, S, hS, hcomp⟩ := TorusSurface.compact_surface ω₁ ω₂ h₁ h₂
  have hl := (TorusCubicLocalMap.locally_biholomorphic ω₁ ω₂ h₁ h₂ h hh).2
  obtain ⟨hhol, hihol⟩ := ChartBridge.global_holomorphic_from_local h₁ h₂ h S T d hS hT hl
  refine ⟨d, S, T, h, hd, hS, hcomp, hcompE, hT, hh, hhol, hihol, ?_⟩
  intro t
  exact global_inverse_coordinates h.toEquiv t (hl t)

end D12Complex.TorusCubicBiholomorphism
