import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NonsymmetricResolvent
import MathGenome.Internal.LinearPDE.P201.Elliptic.ClosedForm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramSolvability
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.P102.U4.SlabPoincare
import MathGenome.Internal.FourierSobolev.P102.Sobolev.Rellich
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
universe u v w
namespace P201.Elliptic.Nonsymmetric
open P201Specs

section Hilbert
variable {𝕜 H V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- The adjoint of an injective map has dense range. In particular this does
not confuse injectivity of a nonsymmetric resolvent with density of its range. -/
theorem denseRange_adjoint (j : V →L[𝕜] H) (hj : Function.Injective j) :
    DenseRange j.adjoint := by
  change Dense (j.adjoint.range : Set V)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  let K := j.adjoint.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, ContinuousLinearMap.orthogonal_range,
    ContinuousLinearMap.adjoint_adjoint]
  exact LinearMap.ker_eq_bot.mpr hj

theorem adjoint_injective (j : V →L[𝕜] H) (hj : DenseRange j) :
    Function.Injective j.adjoint := by
  intro x y hxy
  apply Dense.eq_of_inner_right (𝕜 := 𝕜) hj
  rintro _ ⟨v, rfl⟩
  rw [← j.adjoint_inner_right, ← j.adjoint_inner_right, hxy]

omit [CompleteSpace H] in
/-- A bounded everywhere inverse describes a closed unbounded graph. -/
theorem closed_of_shifted_inverse (a : DenseForm 𝕜 H) (T : H →L[𝕜] H) (μ : ℝ)
    (hT : ∀ u f, (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.graph ↔ T f = u) :
    a.associatedOperator.IsClosed := by
  change IsClosed (a.associatedOperator.graph : Set (H × H))
  have he : (a.associatedOperator.graph : Set (H × H)) =
      {p | T (p.2 + (μ : 𝕜) • p.1) = p.1} := by
    ext ⟨u, g⟩
    change ((u, g) ∈ a.associatedOperator.graph) ↔ _
    convert hT u (g + (μ : 𝕜) • u) using 2 <;> simp
  rw [he]
  exact isClosed_eq (T.continuous.comp (continuous_snd.add (continuous_const.smul continuous_fst)))
    continuous_fst

/-- Exact adjoint inverse identity, with both directions and the precise
unshifted adjoint domain. The scalar shift is real, so it is self-conjugate. -/
theorem adjoint_shifted_inverse (a : DenseForm 𝕜 H) (T : H →L[𝕜] H) (μ : ℝ)
    (hd : Dense (a.associatedOperator.domain : Set H))
    (hT : ∀ u f, (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.graph ↔ T f = u) :
    ∀ u f, (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.adjoint.graph ↔ T.adjoint f = u := by
  intro u f
  change (u, f - (μ : 𝕜) • u) ∈
    (ExpandedFA.Unbounded.hilbertAdjoint a.associatedOperator).graph ↔ _
  rw [ExpandedFA.Unbounded.mem_hilbertAdjoint_graph_iff a.associatedOperator hd]
  constructor
  · intro h
    apply ext_inner_left 𝕜
    intro x
    have hx := (hT (T x) x).mpr rfl
    obtain ⟨hxd, hxe⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp hx
    have hh := h ⟨T x, hxd⟩
    rw [hxe, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal] at hh
    rw [T.adjoint_inner_right]
    linear_combination -hh
  · intro h x
    have hx := (hT (x : H) (a.associatedOperator x + (μ : 𝕜) • (x : H))).mp
      (by simpa only [add_sub_cancel_right] using a.associatedOperator.mem_graph x)
    have hh := T.adjoint_inner_right (a.associatedOperator x + (μ : 𝕜) • (x : H)) f
    rw [h, hx, inner_add_left, inner_smul_left, RCLike.conj_ofReal] at hh
    rw [inner_sub_right, inner_smul_right]
    linear_combination hh

end Hilbert

/-- The general nonsymmetric coercive-form argument. The representing bounded
operator is invertible by complex/real Lax–Milgram; its inverse is composed
with the actual embedding and its adjoint. Density is proved through that
factorization, and does not require symmetry of the form. -/
theorem abstract_resolvent : NonsymmetricExpected.AbstractResolvent.{u, v, w} := by
  intro 𝕜 H V _ _ _ _ _ _ _ a e j hj B hB μ α hα hc
  have hji : Function.Injective j := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    simpa only [hj] using hxy
  have hjd : DenseRange j := by
    have he : Set.range j = (a.domain : Set H) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        rw [← hj]
        exact (e v).property
      · intro hx
        obtain ⟨v, hv⟩ := e.surjective ⟨x, hx⟩
        exact ⟨v, (hj v).symm.trans (congrArg Subtype.val hv)⟩
    change Dense (Set.range j)
    rw [he]
    exact a.dense
  let b : V →L⋆[𝕜] V →L[𝕜] 𝕜 :=
    B.flip + (μ : 𝕜) • (innerSL 𝕜).bilinearComp j j
  have hb (x y : V) : b x y = B y x + (μ : 𝕜) * inner 𝕜 (j x) (j y) := rfl
  obtain ⟨A, hA, _, _⟩ :=
    ExpandedFA.Hilbert.RieszRepresentation.form_representation 𝕜 V b
  have hAbij := ExpandedFA.Hilbert.LaxMilgramSolvability.operator_bijective A hα (by
    intro x
    rw [← hA]
    exact hc x)
  let E : V ≃L[𝕜] V := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hAbij.1) (LinearMap.range_eq_top.mpr hAbij.2)
  have hE (x : V) : E x = A x := rfl
  let S : H →L[𝕜] V := E.symm.toContinuousLinearMap.comp j.adjoint
  let T : H →L[𝕜] H := j.comp S
  have hsol (f : H) (v : V) :
      B (S f) v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j (S f)) (j v) =
        paperInner (𝕜 := 𝕜) f (j v) := by
    change b v (S f) = inner 𝕜 (j v) f
    rw [hA, ← hE]
    change inner 𝕜 v (E (E.symm (j.adjoint f))) = _
    rw [E.apply_symm_apply, j.adjoint_inner_right]
  have huniq (f : H) (u : V)
      (hu : ∀ v, B u v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j u) (j v) =
        paperInner (𝕜 := 𝕜) f (j v)) : u = S f := by
    apply hAbij.1
    apply ext_inner_left 𝕜
    intro v
    rw [← hA, ← hA]
    exact (hu v).trans (hsol f v).symm
  have hTi : Function.Injective T :=
    hji.comp (E.symm.injective.comp (adjoint_injective j hjd))
  have hTd : DenseRange T := by
    exact hjd.comp
      (E.symm.surjective.denseRange.comp (denseRange_adjoint j hji) E.symm.continuous)
      j.continuous
  have hgraph (u f : H) :
      (u, f - (μ : 𝕜) • u) ∈ a.associatedOperator.graph ↔ T f = u := by
    rw [a.mem_associated_graph]
    constructor
    · rintro ⟨hu, hf⟩
      let v : V := e.symm ⟨u, hu⟩
      have hv : j v = u := (hj v).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
      have hvs : v = S f := by
        apply huniq
        intro w
        rw [hB, show e v = ⟨u, hu⟩ from e.apply_symm_apply _, hf, hj, hv]
        simp only [paperInner, inner_sub_right, inner_smul_right]
        ring
      change j (S f) = u
      rw [← hvs]
      exact hv
    · intro h
      have hu : u ∈ a.domain := by
        rw [← h]
        change j (S f) ∈ a.domain
        rw [← hj]
        exact (e (S f)).property
      refine ⟨hu, ?_⟩
      intro w
      obtain ⟨v, rfl⟩ := e.surjective w
      have hue : (⟨u, hu⟩ : a.domain) = e (S f) :=
        Subtype.ext (h.symm.trans (hj (S f)).symm)
      rw [hue, ← hB]
      have hs := hsol f v
      rw [paperInner, inner_sub_right, inner_smul_right, hj, ← h]
      exact eq_sub_iff_add_eq.mpr hs
  have hdom (u : H) : u ∈ a.associatedOperator.domain ↔ u ∈ Set.range T := by
    rw [LinearPMap.mem_domain_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g + (μ : 𝕜) • u, (hgraph u _).mp (by simpa using hg)⟩
    · rintro ⟨f, hf⟩
      exact ⟨f - (μ : 𝕜) • u, (hgraph u f).mpr hf⟩
  have hd : Dense (a.associatedOperator.domain : Set H) := by
    have he : (a.associatedOperator.domain : Set H) = Set.range T := Set.ext hdom
    rw [he]
    exact hTd
  exact ⟨S, hsol, huniq, hTi, hTd, hd, closed_of_shifted_inverse a T μ hgraph,
    hdom, hgraph, adjoint_shifted_inverse a T μ hd hgraph,
    fun hcj => hcj.comp_clm S⟩

section Assembly
variable {𝕜 H V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- The canonical graph can be constructed from an injective dense embedding,
without replacing it by a separately postulated PDE operator. -/
theorem embedded_resolvent (j : V →L[𝕜] H) (hi : Function.Injective j)
    (hd : DenseRange j) (B : V →L[𝕜] V →L⋆[𝕜] 𝕜) (μ α : ℝ) (hα : 0 < α)
    (hc : ∀ v, α * ‖v‖ ^ 2 ≤ RCLike.re
      (B v v + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j v) (j v))) :
    NonsymmetricExpected.ResolventAt (NonsymmetricExpected.embeddedForm j hi hd B) j B μ := by
  let e := LinearEquiv.ofInjective j.toLinearMap hi
  apply abstract_resolvent (NonsymmetricExpected.embeddedForm j hi hd B) e j
    (fun _ => rfl) B ?_ μ α hα hc
  intro u v
  change B u v = B (e.symm (e u)) (e.symm (e v))
  simp only [e.symm_apply_apply]

omit [CompleteSpace H] [CompleteSpace V] [InnerProductSpace 𝕜 V] in
/-- The gradient estimate plus the actual full norm gives coercivity for all
μ>C. The coercivity constant is min(λ/2, μ-C), including small positive shifts. -/
theorem coercive_of_garding (j : V → H) (B : V → V → 𝕜)
    (G : V → ℝ) (lam C μ : ℝ) (hlam : 0 < lam) (hμ : C < μ)
    (hnorm : ∀ u, ‖u‖ ^ 2 = ‖j u‖ ^ 2 + (G u) ^ 2)
    (hc : ∀ u, (lam / 2) * (G u) ^ 2 - C * ‖j u‖ ^ 2 ≤ RCLike.re (B u u)) :
    ∃ α : ℝ, 0 < α ∧ ∀ u, α * ‖u‖ ^ 2 ≤
      RCLike.re (B u u + (μ : 𝕜) * paperInner (𝕜 := 𝕜) (j u) (j u)) := by
  refine ⟨min (lam / 2) (μ - C), lt_min (by linarith) (sub_pos.mpr hμ), fun u => ?_⟩
  have hg := mul_le_mul_of_nonneg_right (min_le_left (lam / 2) (μ - C)) (sq_nonneg (G u))
  have hj := mul_le_mul_of_nonneg_right (min_le_right (lam / 2) (μ - C)) (sq_nonneg ‖j u‖)
  have hreal : RCLike.re ((μ : 𝕜) * paperInner (𝕜 := 𝕜) (j u) (j u)) = μ * ‖j u‖ ^ 2 := by
    simp only [paperInner, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [map_add, hreal, hnorm]
  nlinarith [hc u]

end Assembly

set_option backward.isDefEq.respectTransparency true in
/-- Assemble the Sobolev and coefficient estimates with the abstract graph theorem. -/
theorem pde_from_bridges : P201Specs.Nonsymmetric.SobolevBridge →
    P201Specs.Nonsymmetric.Garding → P201Specs.Nonsymmetric.PDE := by
  intro hs hg m Ω hΩ 𝕜 _ q hq lam hlam hell
  obtain ⟨hi, hd, hjc, hnorm⟩ := hs m Ω hΩ 𝕜
  obtain ⟨B, C, hC, hB, hG⟩ := hg m Ω hΩ 𝕜 q hq lam hlam hell
  refine ⟨B, C, hi, hd, ?_⟩
  refine ⟨hC, hB, hG, hjc, ?_⟩
  intro μ hμ
  obtain ⟨α, hα, hc⟩ := coercive_of_garding (𝕜 := 𝕜) (H := Lp 𝕜 Ω 2) (V := H10 𝕜 Ω)
    (hZeroUnderlying (𝕜 := 𝕜) Ω) (fun u v => B u v)
    (fun u : H10 𝕜 Ω => ‖hGradient (𝕜 := 𝕜) (Ω := Ω) u.val‖)
    lam C μ hlam hμ hnorm hG
  refine ⟨⟨α, hα, hc⟩, ?_⟩
  exact @embedded_resolvent 𝕜 (Lp 𝕜 Ω 2) (H10 𝕜 Ω)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (hZeroUnderlying (𝕜 := 𝕜) Ω) hi hd B μ α hα hc


lemma norm_sq_split {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖(WithLp.toLp 2 (fun i => (z i).re) : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => (z i).im) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (z i).re * (z i).re + (z i).im * (z i).im = (z i).re ^ 2 + (z i).im ^ 2
  ring

lemma principal_split {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℂ (Fin n)) :
    (∑ i, ∑ j, (A i j : ℂ) * z j * conj (z i)).re =
      (∑ i, ∑ j, A i j * (z j).re * (z i).re) +
      (∑ i, ∑ j, A i j * (z j).im * (z i).im) := by
  change Complex.reCLM (∑ i, ∑ j, (A i j : ℂ) * z j * conj (z i)) = _
  simp only [← Finset.sum_add_distrib, map_sum, Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma principal_elliptic_complex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hA : ∀ ξ : EuclideanSpace ℝ (Fin n),
      lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ j * ξ i)
    (z : EuclideanSpace ℂ (Fin n)) :
    lam * ‖z‖ ^ 2 ≤ (∑ i, ∑ j, (A i j : ℂ) * z j * conj (z i)).re := by
  have hr := hA (WithLp.toLp 2 fun i => (z i).re)
  have hi := hA (WithLp.toLp 2 fun i => (z i).im)
  rw [principal_split, norm_sq_split, mul_add]
  exact add_le_add hr hi

open MeasureTheory
open P201Specs
open scoped ENNReal Matrix.Norms.Elementwise

lemma elliptic_complexify {n : ℕ} {Ω : Domain n} {q : P201Specs.Nonsymmetric.Coefficients n ℝ}
    {lam : ℝ} (h : P201Specs.Nonsymmetric.Elliptic Ω q lam) :
    P201Specs.Nonsymmetric.Elliptic Ω (P201Specs.Nonsymmetric.complexify q) lam := by
  filter_upwards [h] with x hx
  intro z
  apply principal_elliptic_complex (q.1 x) lam ?_ z
  intro ξ
  simpa using hx ξ


lemma bounded_complexify {n : ℕ} {Ω : Domain n} {q : P201Specs.Nonsymmetric.Coefficients n ℝ}
    (h : P201Specs.Nonsymmetric.Bounded Ω q) : P201Specs.Nonsymmetric.Bounded Ω (P201Specs.Nonsymmetric.complexify q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply MemLp.of_eval
    intro i
    apply MemLp.of_eval
    intro j
    exact ((h.1.eval i).eval j).ofReal
  · apply MemLp.of_eval
    intro i
    exact (h.2.1.eval i).ofReal
  · apply MemLp.of_eval
    intro i
    exact (h.2.2.1.eval i).ofReal
  · exact h.2.2.2.ofReal

/-- The real and complex coefficient conventions have the same applicability. -/
theorem coefficient_complexification : P201Specs.Nonsymmetric.Complexification := by
  intro n Ω q lam hb he
  exact ⟨bounded_complexify hb, elliptic_complexify he⟩

/-- Every compact smooth test lies in the actual full-H¹ closure. -/
def testH10 {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (φ : Test 𝕜 Ω) :
    H10 𝕜 Ω := by
  let w := (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose
  have hw := (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose_spec
  let u := (hToW 𝕜 Ω 1).symm w
  refine ⟨u, ?_⟩
  apply ((P102.U4.smoothSobolevSubmodule 𝕜 Ω 1 2).comap
    (hToW 𝕜 Ω 1).toLinearMap).le_topologicalClosure
  change ∃ ψ, P102.U4.testToDomainLp Ω 2 ψ = P102.U4.sobolevUnderlying (hToW 𝕜 Ω 1 u)
  exact ⟨φ, by simpa only [u, ContinuousLinearEquiv.apply_symm_apply] using hw.symm⟩

@[simp] theorem testH10_underlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (φ : Test 𝕜 Ω) :
    hZeroUnderlying Ω (testH10 Ω φ) = P102.U4.testToDomainLp Ω 2 φ :=
  (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose_spec

/-- The actual zero-boundary Sobolev inclusion is injective on every open set. -/
theorem sobolev_injective {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) :
    Function.Injective (hZeroUnderlying (𝕜 := 𝕜) Ω) := by
  intro u v h
  apply Subtype.ext
  exact P201.hilbertUnderlyingInjective Ω 1 h

/-- Density follows from testing against conjugate compact smooth functions. -/
theorem sobolev_denseRange {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) :
    DenseRange (hZeroUnderlying (𝕜 := 𝕜) Ω) := by
  let j : H10 𝕜 Ω →L[𝕜] Lp 𝕜 Ω 2 := hZeroUnderlying (𝕜 := 𝕜) Ω
  change Dense (j.range : Set (Lp 𝕜 Ω 2))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  let K := j.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  apply P102.U4.regularLp_injective Ω 2
  ext φ
  rw [P102.U4.regularLp_pairing, P102.U4.regularLp_pairing,
    map_zero, P102.U4.lpTestPairing_eq_integral]
  let ψ : Test 𝕜 Ω := TestFunction.postcompCLM (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap φ
  have hh := (Submodule.mem_orthogonal j.range f).mp hf (j (testH10 Ω ψ)) ⟨_, rfl⟩
  rw [L2.inner_def] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [P102.U4.testToDomainLp_ae Ω 2 ψ] with x hx
  change f x * φ x = inner 𝕜 (hZeroUnderlying Ω (testH10 Ω ψ) x) (f x)
  rw [testH10_underlying, hx]
  simp only [ψ, TestFunction.postcompCLM_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, RCLike.conjCLE_apply, RCLike.inner_apply,
    starRingEnd_apply, star_star]

 theorem zeroUnderlying_compact (m : ℕ) (Ω : P201.Domain (m+1))
    (hΩ : P201.IsBoundedLipschitzOpen Ω) (𝕜 : Type) [RCLike 𝕜] :
    IsCompactOperator (P201.hZeroUnderlying (𝕜 := 𝕜) Ω) := by
  obtain ⟨I, _, hI, hc⟩ := P102.Sobolev.Rellich.same_exponent m (P201.graphFrame m) Ω hΩ 𝕜 2 (by norm_num)
  let T : P201.H10 𝕜 Ω →L[𝕜] P102.U4.Sobolev 𝕜 Ω 1 2 :=
    (P201.hToW 𝕜 Ω 1).toContinuousLinearMap.comp (P201Specs.hZeroSubmodule 𝕜 Ω).subtypeL
  have heq : I.comp T = P201.hZeroUnderlying (𝕜 := 𝕜) Ω := by
    ext u
    exact hI (T u)
  rw [← heq]
  apply (isCompactOperator_iff_isCompact_closure_image_ball _ zero_lt_one).mpr
  change IsCompact (closure ((I.comp T) '' Metric.ball 0 1))
  rw [ContinuousLinearMap.coe_comp, Set.image_comp]
  exact hc _ (T.lipschitzWith.isBounded_image (Metric.isBounded_ball))

 theorem l2_norm_sq_integral {α E 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (u : MeasureTheory.Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

 theorem gradient_norm_sq {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : P201.Domain n)
    (u : P201.H 𝕜 Ω 1) :
    ‖P201.hGradient u‖ ^ 2 = ∑ j : Fin n, ‖P201.hFirstDerivative u j‖ ^ 2 := by
  rw [l2_norm_sq_integral (𝕜 := 𝕜)]
  have hgrad : (P201.hGradient u : P201.Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[P201.domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun j => P201.hFirstDerivative u j x) :=
    MemLp.coeFn_toLp _
  calc
    _ = ∫ x, ∑ j : Fin n, ‖P201.hFirstDerivative u j x‖ ^ 2 ∂P201.domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx, PiLp.norm_sq_eq_of_L2]
    _ = ∑ j : Fin n, ∫ x, ‖P201.hFirstDerivative u j x‖ ^ 2 ∂P201.domainMeasure Ω := by
      apply integral_finsetSum
      intro j hj
      have := (L2.integrable_inner (𝕜 := 𝕜) (P201.hFirstDerivative u j) (P201.hFirstDerivative u j)).re
      simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using this
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (l2_norm_sq_integral (𝕜 := 𝕜) (P201.hFirstDerivative u j)).symm

 theorem hOne_norm_sq {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : P201.Domain n)
    (u : P201.H 𝕜 Ω 1) :
    ‖u‖ ^ 2 = ‖P201.hUnderlying Ω 1 u‖ ^ 2 + ‖P201.hGradient u‖ ^ 2 := by
  rw [P201.fullHilbertNorm, gradient_norm_sq]
  rw [← (P102.U4.SlabPoincareProof.firstOrderIndexEquiv (d := n)).sum_comp]
  rw [Fintype.sum_option]
  rfl

/-- Actual Sobolev inclusion, compactness and full norm over both scalar fields. -/
theorem sobolev_bridge : P201Specs.Nonsymmetric.SobolevBridge := by
  intro m Ω hΩ 𝕜 _
  exact ⟨sobolev_injective 𝕜 Ω, sobolev_denseRange 𝕜 Ω,
    zeroUnderlying_compact m Ω hΩ 𝕜, fun u => hOne_norm_sq 𝕜 Ω u.val⟩

section CoefficientBridge
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
open P201Specs
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

local instance (Ω : Domain n) : NormedAddCommGroup (H10 𝕜 Ω) := inferInstance
local instance (Ω : Domain n) : NormedSpace 𝕜 (H10 𝕜 Ω) := inferInstance

/-- All derivatives are the actual H¹ coordinates. -/
def derivativeCLM (Ω : Domain n) (j : Fin n) : H10 𝕜 Ω →L[𝕜] Lp 𝕜 Ω 2 :=
  ((PiLp.proj 2 _ ⟨{j}, by simp⟩).comp (hilbertSubmodule 𝕜 Ω 1).subtypeL).comp
    (hZeroSubmodule 𝕜 Ω).subtypeL

@[simp] theorem derivativeCLM_apply (Ω : Domain n) (j : Fin n) (u : H10 𝕜 Ω) :
    derivativeCLM Ω j u = hFirstDerivative u.val j := rfl

def coordinateLp {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Ω : Domain n) (f : Space n → E) (hf : MemLp f ∞ (domainMeasure Ω))
    (π : E →L[𝕜] 𝕜) : Lp 𝕜 Ω ∞ := π.compLp (hf.toLp f)

theorem coordinateLp_ae {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Ω : Domain n) (f : Space n → E) (hf : MemLp f ∞ (domainMeasure Ω))
    (π : E →L[𝕜] 𝕜) :
    (coordinateLp Ω f hf π : Space n → 𝕜) =ᵐ[domainMeasure Ω] fun x => π (f x) := by
  filter_upwards [π.coeFn_compLp (hf.toLp f), hf.coeFn_toLp] with x hx hy
  exact hx.trans (congrArg π hy)

def matrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) 𝕜 →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) j).comp
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => Fin n → 𝕜) i)

def vectorEntry (i : Fin n) : (Fin n → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj i

def multiplier (Ω : Domain n) (f : Lp 𝕜 Ω ∞) : Lp 𝕜 Ω 2 →L[𝕜] Lp 𝕜 Ω 2 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL (domainMeasure Ω) ∞ 2 2 f

theorem multiplier_ae (Ω : Domain n) (f : Lp 𝕜 Ω ∞) (u : Lp 𝕜 Ω 2) :
    (multiplier Ω f u : Space n → 𝕜) =ᵐ[domainMeasure Ω] fun x => f x * u x :=
  (ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder f u

theorem multiplier_norm (Ω : Domain n) (f : Lp 𝕜 Ω ∞) (u : Lp 𝕜 Ω 2) :
    ‖multiplier Ω f u‖ ≤ ‖f‖ * ‖u‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖f‖ * ‖u‖ :=
      (ContinuousLinearMap.mul 𝕜 𝕜).norm_holder_apply_apply_le (r := 2) f u
    _ ≤ 1 * ‖f‖ * ‖u‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
    _ = _ := by ring

def principalForm (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) : H10 𝕜 Ω →L[𝕜] H10 𝕜 Ω →L⋆[𝕜] 𝕜 :=
  ∑ i : Fin n, ∑ j : Fin n,
    (innerSLFlip 𝕜).bilinearComp
      ((multiplier Ω (coordinateLp Ω q.1 hq.1 (matrixEntry i j))).comp (derivativeCLM Ω j))
      (derivativeCLM Ω i)

def lowerForm (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) : H10 𝕜 Ω →L[𝕜] H10 𝕜 Ω →L⋆[𝕜] 𝕜 :=
  (∑ j : Fin n, (innerSLFlip 𝕜).bilinearComp
    ((multiplier Ω (coordinateLp Ω q.2.1 hq.2.1 (vectorEntry j))).comp (derivativeCLM Ω j))
    (hZeroUnderlying Ω)) +
  (∑ i : Fin n, (innerSLFlip 𝕜).bilinearComp
    ((multiplier Ω (coordinateLp Ω q.2.2.1 hq.2.2.1 (vectorEntry i))).comp (hZeroUnderlying Ω))
    (derivativeCLM Ω i)) +
  (innerSLFlip 𝕜).bilinearComp ((multiplier Ω (hq.2.2.2.toLp q.2.2.2)).comp (hZeroUnderlying Ω))
    (hZeroUnderlying Ω)

/-- A generic L² pairing provides the exact scalar integrand. -/
theorem multiplier_pairing_integrable (Ω : Domain n) (f : Lp 𝕜 Ω ∞)
    (u v : Lp 𝕜 Ω 2) :
    Integrable (fun x => f x * u x * conj (v x)) (domainMeasure Ω) := by
  apply (L2.integrable_inner (𝕜 := 𝕜) v (multiplier Ω f u)).congr
  filter_upwards [multiplier_ae Ω f u] with x hx
  simp only [hx, RCLike.inner_apply]

theorem multiplier_pairing (Ω : Domain n) (f : Lp 𝕜 Ω ∞)
    (u v : Lp 𝕜 Ω 2) :
    inner 𝕜 v (multiplier Ω f u) =
      ∫ x, f x * u x * conj (v x) ∂domainMeasure Ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_ae Ω f u] with x hx
  simp only [hx, RCLike.inner_apply]


theorem coordinate_pairing_integrable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Ω : Domain n) (f : Space n → E) (hf : MemLp f ∞ (domainMeasure Ω))
    (π : E →L[𝕜] 𝕜) (u v : Lp 𝕜 Ω 2) :
    Integrable (fun x => π (f x) * u x * conj (v x)) (domainMeasure Ω) := by
  apply (multiplier_pairing_integrable Ω (coordinateLp Ω f hf π) u v).congr
  filter_upwards [coordinateLp_ae Ω f hf π] with x hx
  rw [hx]

theorem coordinate_pairing {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Ω : Domain n) (f : Space n → E) (hf : MemLp f ∞ (domainMeasure Ω))
    (π : E →L[𝕜] 𝕜) (u v : Lp 𝕜 Ω 2) :
    inner 𝕜 v (multiplier Ω (coordinateLp Ω f hf π) u) =
      ∫ x, π (f x) * u x * conj (v x) ∂domainMeasure Ω := by
  rw [multiplier_pairing]
  apply integral_congr_ae
  filter_upwards [coordinateLp_ae Ω f hf π] with x hx
  rw [hx]

theorem principal_summand_integrable (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) (i j : Fin n) :
    Integrable (fun x => q.1 x i j * hFirstDerivative u.val j x *
      conj (hFirstDerivative v.val i x)) (domainMeasure Ω) :=
  coordinate_pairing_integrable Ω q.1 hq.1 (matrixEntry i j) _ _

theorem principal_integrable (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    Integrable (fun x => ∑ i, ∑ j, q.1 x i j * hFirstDerivative u.val j x *
      conj (hFirstDerivative v.val i x)) (domainMeasure Ω) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => principal_summand_integrable Ω q hq u v i j))

theorem principal_apply (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    principalForm Ω q hq u v = ∫ x, ∑ i, ∑ j,
      q.1 x i j * hFirstDerivative u.val j x * conj (hFirstDerivative v.val i x)
      ∂domainMeasure Ω := by
  simp only [principalForm, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    derivativeCLM_apply, innerSLFlip_apply_apply, ContinuousLinearMap.comp_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => principal_summand_integrable Ω q hq u v i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    principal_summand_integrable Ω q hq u v i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact coordinate_pairing Ω q.1 hq.1 (matrixEntry i j) _ _

/-- All coordinate L² norms are controlled by the actual vector-gradient norm. -/
theorem derivative_norm_le_gradient (Ω : Domain n) (u : H10 𝕜 Ω) (j : Fin n) :
    ‖hFirstDerivative u.val j‖ ≤ ‖hGradient u.val‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [show (hGradient u.val : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun i => hFirstDerivative u.val i x) from MemLp.coeFn_toLp _]
    with x hx
  simpa only [hx, PiLp.toLp_apply] using
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => hFirstDerivative u.val i x)) j)

theorem principal_coercive (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (lam : ℝ) (hell : Nonsymmetric.Elliptic Ω q lam)
    (u : H10 𝕜 Ω) :
    lam * ‖hGradient u.val‖ ^ 2 ≤ RCLike.re (principalForm Ω q hq u u) := by
  have hg : Integrable (fun x => ‖hGradient u.val x‖ ^ 2) (domainMeasure Ω) := by
    have := (L2.integrable_inner (𝕜 := 𝕜) (hGradient u.val) (hGradient u.val)).re
    simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using this
  have hgeq : (∫ x, ‖hGradient u.val x‖ ^ 2 ∂domainMeasure Ω) = ‖hGradient u.val‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def,
      ← integral_re (L2.integrable_inner (hGradient u.val) (hGradient u.val))]
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  rw [principal_apply, ← integral_re (principal_integrable Ω q hq u u), ← hgeq,
    ← integral_const_mul]
  apply integral_mono_ae (hg.const_mul _) ((principal_integrable Ω q hq u u).re)
  filter_upwards [hell, show (hGradient u.val : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun i => hFirstDerivative u.val i x) from MemLp.coeFn_toLp _]
    with x hx hxu
  simpa only [hxu, PiLp.toLp_apply] using hx (hGradient u.val x)

theorem lower_b_integrable (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    Integrable (fun x => ∑ j, q.2.1 x j * hFirstDerivative u.val j x *
      conj (hZeroUnderlying Ω v x)) (domainMeasure Ω) :=
  integrable_finsetSum _ (fun j _ => coordinate_pairing_integrable Ω q.2.1 hq.2.1
    (vectorEntry j) _ _)

theorem lower_d_integrable (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    Integrable (fun x => ∑ i, q.2.2.1 x i * hZeroUnderlying Ω u x *
      conj (hFirstDerivative v.val i x)) (domainMeasure Ω) :=
  integrable_finsetSum _ (fun i _ => coordinate_pairing_integrable Ω q.2.2.1 hq.2.2.1
    (vectorEntry i) _ _)

theorem lower_c_integrable (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    Integrable (fun x => q.2.2.2 x * hZeroUnderlying Ω u x *
      conj (hZeroUnderlying Ω v x)) (domainMeasure Ω) := by
  apply (multiplier_pairing_integrable Ω (hq.2.2.2.toLp q.2.2.2) _ _).congr
  filter_upwards [hq.2.2.2.coeFn_toLp] with x hx
  rw [hx]

theorem lower_apply (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    lowerForm Ω q hq u v = ∫ x,
      (∑ j, q.2.1 x j * hFirstDerivative u.val j x * conj (hZeroUnderlying Ω v x)) +
      (∑ i, q.2.2.1 x i * hZeroUnderlying Ω u x * conj (hFirstDerivative v.val i x)) +
      q.2.2.2 x * hZeroUnderlying Ω u x * conj (hZeroUnderlying Ω v x)
      ∂domainMeasure Ω := by
  have hb' (j : Fin n) : Integrable (fun x => q.2.1 x j * hFirstDerivative u.val j x *
      conj (hZeroUnderlying Ω v x)) (domainMeasure Ω) :=
    coordinate_pairing_integrable Ω q.2.1 hq.2.1 (vectorEntry j) _ _
  have hd' (i : Fin n) : Integrable (fun x => q.2.2.1 x i * hZeroUnderlying Ω u x *
      conj (hFirstDerivative v.val i x)) (domainMeasure Ω) :=
    coordinate_pairing_integrable Ω q.2.2.1 hq.2.2.1 (vectorEntry i) _ _
  have hb := lower_b_integrable Ω q hq u v
  have hd := lower_d_integrable Ω q hq u v
  have hc := lower_c_integrable Ω q hq u v
  have hs := integral_add (hb.add hd) hc
  have ht := integral_add hb hd
  simp only [Pi.add_apply] at hs ht
  rw [hs, ht]

  simp only [lowerForm, add_apply, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    derivativeCLM_apply, ContinuousLinearMap.comp_apply, innerSLFlip_apply_apply]
  congr 1
  · congr 1
    · rw [integral_finsetSum _ (fun j _ =>
        hb' j)]
      apply Finset.sum_congr rfl
      intro j _
      exact coordinate_pairing Ω q.2.1 hq.2.1 (vectorEntry j) _ _
    · rw [integral_finsetSum _ (fun i _ =>
        hd' i)]
      apply Finset.sum_congr rfl
      intro i _
      exact coordinate_pairing Ω q.2.2.1 hq.2.2.1 (vectorEntry i) _ _
  · rw [multiplier_pairing]
    apply integral_congr_ae
    filter_upwards [hq.2.2.2.coeFn_toLp] with x hx
    rw [hx]

def boundedForm (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) : H10 𝕜 Ω →L[𝕜] H10 𝕜 Ω →L⋆[𝕜] 𝕜 :=
  principalForm Ω q hq + lowerForm Ω q hq

theorem boundedForm_apply (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u v : H10 𝕜 Ω) :
    boundedForm Ω q hq u v = Nonsymmetric.form Ω q u v := by
  change principalForm Ω q hq u v + lowerForm Ω q hq u v = _
  rw [principal_apply, lower_apply]
  have hl := ((lower_b_integrable Ω q hq u v).add (lower_d_integrable Ω q hq u v)).add
      (lower_c_integrable Ω q hq u v)
  have hs := integral_add (principal_integrable Ω q hq u v) hl
  simp only [Pi.add_apply] at hs
  rw [← hs]

  apply integral_congr_ae
  filter_upwards [] with x
  rw [Finset.sum_mul, Finset.mul_sum]
  have hd : (∑ i, q.2.2.1 x i * hZeroUnderlying Ω u x *
      conj (hFirstDerivative v.val i x)) =
      ∑ i, hZeroUnderlying Ω u x * (q.2.2.1 x i * conj (hFirstDerivative v.val i x)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  ring

lemma lowerForm_expand (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u : H10 𝕜 Ω) :
    lowerForm Ω q hq u u =
      (∑ j, inner 𝕜 (hZeroUnderlying Ω u)
        (multiplier Ω (coordinateLp Ω q.2.1 hq.2.1 (vectorEntry j))
          (hFirstDerivative u.val j))) +
      (∑ i, inner 𝕜 (hFirstDerivative u.val i)
        (multiplier Ω (coordinateLp Ω q.2.2.1 hq.2.2.1 (vectorEntry i))
          (hZeroUnderlying Ω u))) +
      inner 𝕜 (hZeroUnderlying Ω u)
        (multiplier Ω (hq.2.2.2.toLp q.2.2.2) (hZeroUnderlying Ω u)) := by
  simp [lowerForm, ContinuousLinearMap.bilinearComp_apply]

lemma lowerForm_norm_le (Ω : Domain n) (q : Nonsymmetric.Coefficients n 𝕜)
    (hq : Nonsymmetric.Bounded Ω q) (u : H10 𝕜 Ω) (G : ℝ)
    (hD : ∀ j, ‖hFirstDerivative u.val j‖ ≤ G) :
    ‖lowerForm Ω q hq u u‖ ≤
      ((∑ j, ‖coordinateLp Ω q.2.1 hq.2.1 (vectorEntry j)‖) +
        (∑ i, ‖coordinateLp Ω q.2.2.1 hq.2.2.1 (vectorEntry i)‖)) * G *
        ‖hZeroUnderlying Ω u‖ +
      ‖hq.2.2.2.toLp q.2.2.2‖ * ‖hZeroUnderlying Ω u‖ ^ 2 := by
  let U := hZeroUnderlying Ω u
  let b := fun j => coordinateLp Ω q.2.1 hq.2.1 (vectorEntry j)
  let d := fun j => coordinateLp Ω q.2.2.1 hq.2.2.1 (vectorEntry j)
  let c := hq.2.2.2.toLp q.2.2.2
  have hb j : ‖inner 𝕜 U (multiplier Ω (b j) (hFirstDerivative u.val j))‖ ≤
      ‖b j‖ * G * ‖U‖ := by
    calc
      _ ≤ ‖U‖ * ‖multiplier Ω (b j) (hFirstDerivative u.val j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖U‖ * (‖b j‖ * ‖hFirstDerivative u.val j‖) :=
        mul_le_mul_of_nonneg_left (multiplier_norm Ω _ _) (norm_nonneg _)
      _ ≤ ‖U‖ * (‖b j‖ * G) := by gcongr; exact hD j
      _ = _ := by ring
  have hd i : ‖inner 𝕜 (hFirstDerivative u.val i) (multiplier Ω (d i) U)‖ ≤
      ‖d i‖ * G * ‖U‖ := by
    calc
      _ ≤ ‖hFirstDerivative u.val i‖ * ‖multiplier Ω (d i) U‖ := norm_inner_le_norm _ _
      _ ≤ ‖hFirstDerivative u.val i‖ * (‖d i‖ * ‖U‖) :=
        mul_le_mul_of_nonneg_left (multiplier_norm Ω _ _) (norm_nonneg _)
      _ ≤ G * (‖d i‖ * ‖U‖) := by gcongr; exact hD i
      _ = _ := by ring
  have hc : ‖inner 𝕜 U (multiplier Ω c U)‖ ≤ ‖c‖ * ‖U‖ ^ 2 := by
    calc
      _ ≤ ‖U‖ * ‖multiplier Ω c U‖ := norm_inner_le_norm _ _
      _ ≤ ‖U‖ * (‖c‖ * ‖U‖) :=
        mul_le_mul_of_nonneg_left (multiplier_norm Ω _ _) (norm_nonneg _)
      _ = _ := by ring
  rw [lowerForm_expand]
  calc
    _ ≤ ‖∑ j, inner 𝕜 U (multiplier Ω (b j) (hFirstDerivative u.val j))‖ +
        ‖∑ i, inner 𝕜 (hFirstDerivative u.val i) (multiplier Ω (d i) U)‖ +
        ‖inner 𝕜 U (multiplier Ω c U)‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (∑ j, ‖inner 𝕜 U (multiplier Ω (b j) (hFirstDerivative u.val j))‖) +
        (∑ i, ‖inner 𝕜 (hFirstDerivative u.val i) (multiplier Ω (d i) U)‖) +
        ‖c‖ * ‖U‖ ^ 2 := by
      exact add_le_add (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) hc
    _ ≤ (∑ j, ‖b j‖ * G * ‖U‖) +
        (∑ i, ‖d i‖ * G * ‖U‖) + ‖c‖ * ‖U‖ ^ 2 := by
      exact add_le_add (add_le_add (Finset.sum_le_sum fun j _ => hb j)
        (Finset.sum_le_sum fun i _ => hd i)) le_rfl
    _ = _ := by simp only [← Finset.sum_mul]; ring


/-- Absorption of the two first-order contributions in half the ellipticity. -/
theorem garding_young_bound (lam K K0 G U : ℝ) (hlam : 0 < lam)
    (hK0 : 0 ≤ K0) :
    0 ≤ K ^ 2 / (2 * lam) + K0 ∧
    (lam / 2) * G ^ 2 - (K ^ 2 / (2 * lam) + K0) * U ^ 2 ≤
      lam * G ^ 2 - K * G * U - K0 * U ^ 2 := by
  have hlam2 : 0 < 2 * lam := by positivity
  have hden : K ^ 2 / (2 * lam) * (2 * lam) = K ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hlam2)
  constructor
  · positivity
  · nlinarith [sq_nonneg (lam * G - K * U)]

/-- The actual four-term coefficient form over ℝ or ℂ obeys Gårding's bound. -/
theorem garding : P201Specs.Nonsymmetric.Garding := by
  intro m Ω _ 𝕜 _ q hq lam hlam hell
  let K : ℝ := (∑ j, ‖coordinateLp Ω q.2.1 hq.2.1 (vectorEntry j)‖) +
    (∑ i, ‖coordinateLp Ω q.2.2.1 hq.2.2.1 (vectorEntry i)‖)
  let K0 : ℝ := ‖hq.2.2.2.toLp q.2.2.2‖
  let C : ℝ := K ^ 2 / (2 * lam) + K0
  refine ⟨boundedForm Ω q hq, C, ?_, boundedForm_apply Ω q hq, ?_⟩
  · dsimp [C, K0]
    positivity
  · intro u
    have hp := principal_coercive Ω q hq lam hell u
    have hl := lowerForm_norm_le Ω q hq u ‖hGradient u.val‖
      (derivative_norm_le_gradient Ω u)
    have hre := (abs_le.mp (RCLike.abs_re_le_norm (lowerForm Ω q hq u u))).1
    obtain ⟨_, hY⟩ := garding_young_bound lam K K0 ‖hGradient u.val‖
      ‖hZeroUnderlying Ω u‖ hlam (norm_nonneg _)
    change _ ≤ RCLike.re (principalForm Ω q hq u u + lowerForm Ω q hq u u)
    rw [map_add]
    change ‖lowerForm Ω q hq u u‖ ≤ K * ‖hGradient u.val‖ *
      ‖hZeroUnderlying Ω u‖ + K0 * ‖hZeroUnderlying Ω u‖ ^ 2 at hl
    dsimp [C]
    linarith


end CoefficientBridge


/-- The complete nonsymmetric shifted Dirichlet realization on the actual
Sobolev closure, with compact resolvent and the exact Hilbert-adjoint identity. -/
theorem pde_resolvent : P201Specs.Nonsymmetric.PDE :=
  pde_from_bridges sobolev_bridge garding

end P201.Elliptic.Nonsymmetric
