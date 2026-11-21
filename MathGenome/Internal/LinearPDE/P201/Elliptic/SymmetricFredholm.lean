import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.SymmetricFredholm
import MathGenome.Internal.LinearPDE.P201.Elliptic.ClosedForm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange
import Mathlib.Topology.MetricSpace.Antilipschitz

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
universe u v
namespace P201.Elliptic.SymmetricFredholm
open ExpandedFA.Unbounded
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Factor the unbounded equation through any bounded resolvent, retaining
its exact domain. The sign agrees with the library's ζI−A convention. -/
lemma shifted_range (A : Operator 𝕜 H H) (ζ : 𝕜) (R : ResolventInverse A ζ)
    (r : ℝ) :
    (shifted A r).range =
      (ContinuousLinearMap.id 𝕜 H - (ζ - (r : 𝕜)) • R.inverse).toLinearMap.range := by
  let T := ContinuousLinearMap.id 𝕜 H - (ζ - (r : 𝕜)) • R.inverse
  have hfactor (u : A.domain) :
      shifted A r u = -T (ζ • (u : H) - A u) := by
    change A u - (r : 𝕜) • (u : H) =
      -((ζ • (u : H) - A u) - (ζ - (r : 𝕜)) • R.inverse (ζ • (u : H) - A u))
    rw [R.left_inverse, sub_smul]
    abel
  have honto : Function.Surjective (fun u : A.domain => ζ • (u : H) - A u) := by
    intro f
    exact ⟨⟨R.inverse f, R.mem_domain f⟩, R.right_inverse f⟩
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨-(ζ • (u : H) - A u), ?_⟩
    change T (-(ζ • (u : H) - A u)) = shifted A r u
    rw [map_neg]
    exact (hfactor u).symm
  · rintro ⟨f, rfl⟩
    obtain ⟨u, hu⟩ := honto (-f)
    change ζ • (u : H) - A u = -f at hu
    exact ⟨u, by rw [hfactor, hu, map_neg, neg_neg]; rfl⟩

omit [CompleteSpace H] in
lemma shifted_closed_range (A : Operator 𝕜 H H) (hc : HasCompactResolvent A)
    (r : ℝ) : IsClosed ((shifted A r).range : Set H) := by
  obtain ⟨ζ, R, hR⟩ := hc
  rw [shifted_range A ζ R r]
  apply ExpandedFA.Fredholm.identity_sub_compact_closed_range
  exact (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
    (hR.smul (ζ - (r : 𝕜)))

/-- For real r the adjoint kernel is the same eigenspace, over R or C. -/
lemma shifted_orthogonal (A : Operator 𝕜 H H) (hd : Dense (A.domain : Set H))
    (hs : A = A.adjoint) (r : ℝ) (y : H) :
    y ∈ (shifted A r).range.orthogonal ↔
      ∃ v : A.domain, (v : H) = y ∧ shifted A r v = 0 := by
  change (∀ z ∈ (shifted A r).range, inner 𝕜 z y = 0) ↔ _
  constructor
  · intro hy
    have he (x : A.domain) : inner 𝕜 (A x) y = inner 𝕜 (x : H) ((r : 𝕜) • y) := by
      have h := hy (shifted A r x) ⟨x, rfl⟩
      change inner 𝕜 (A x - (r : 𝕜) • (x : H)) y = 0 at h
      simpa only [inner_sub_left, inner_smul_left, inner_smul_right,
        RCLike.conj_ofReal, sub_eq_zero] using h
    have hg := (mem_hilbertAdjoint_graph_iff A hd y ((r : 𝕜) • y)).mpr he
    change (y, (r : 𝕜) • y) ∈ A.adjoint.graph at hg
    rw [← hs] at hg
    obtain ⟨v, hv, hAv⟩ := A.mem_graph_iff.mp hg
    exact ⟨v, hv, by change A v - (r : 𝕜) • (v : H) = 0; rw [hv, hAv, sub_self]⟩
  · rintro ⟨v, rfl, hv⟩ z ⟨x, rfl⟩
    have ha := (LinearPMap.adjoint_isFormalAdjoint hd).symm
    rw [← hs] at ha
    have he : A v = (r : 𝕜) • (v : H) := sub_eq_zero.mp hv
    change inner 𝕜 (A x - (r : 𝕜) • (x : H)) (v : H) = 0
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, ha, he,
      inner_smul_right, sub_self]

/-- Closed range and the self-adjoint kernel identity give compatibility. -/
theorem abstract_symmetric_fredholm : Expected.Abstract.{u, v} := by
  intro 𝕜 H _ _ _ _ A hd hs hc r
  let B := shifted A r
  have hr := shifted_closed_range A hc r
  have hcompat (f : H) : (∃ u : A.domain, B u = f) ↔
      ∀ v : A.domain, B v = 0 → paperInner (𝕜 := 𝕜) f (v : H) = 0 := by
    change f ∈ B.range ↔ _
    rw [← hr.submodule_topologicalClosure_eq,
      ← Submodule.orthogonal_orthogonal_eq_closure]
    change (∀ y ∈ B.range.orthogonal, inner 𝕜 y f = 0) ↔ _
    constructor
    · intro hf v hv
      exact hf v ((shifted_orthogonal A hd hs r v).mpr ⟨v, rfl, hv⟩)
    · intro hf y hy
      obtain ⟨v, rfl, hv⟩ := (shifted_orthogonal A hd hs r y).mp hy
      exact hf v hv
  refine ⟨?_, hcompat, ?_⟩
  · intro hn f
    obtain ⟨u, hu⟩ := (hcompat f).mpr (by
      intro v hv
      have hz := hn v hv
      simp [paperInner, hz])
    refine ⟨u, hu, ?_⟩
    intro v hv
    apply sub_eq_zero.mp
    apply Subtype.ext
    exact hn (v - u) (by rw [map_sub, hv, hu, sub_self])
  · intro f u hu v
    rw [map_sub, hu, sub_eq_zero]

/-- E10 supplies density and self-adjointness of the common canonical operator. -/
theorem closed_form_symmetric_fredholm : Expected.ClosedForms.{u, v} := by
  intro 𝕜 H _ _ _ _ a hs hn hclosed hc r
  obtain ⟨_, hd, hsa, _⟩ := closed_form a hs hn hclosed
  exact abstract_symmetric_fredholm a.associatedOperator hd hsa hc r

section Dirichlet
open P201Specs
variable {𝕜 : Type} [RCLike 𝕜] {m : ℕ} (Ω : Domain (m + 1))
  (a : DenseForm 𝕜 (Lp 𝕜 Ω 2)) (hd : DirichletDomain Ω a)

lemma dirichletLift_surjective : Function.Surjective (dirichletLift Ω a hd) := by
  intro w
  have hw : (w : Lp 𝕜 Ω 2) ∈ (hZeroUnderlying (𝕜 := 𝕜) Ω).toLinearMap.range :=
    hd ▸ w.property
  obtain ⟨u, hu⟩ := hw
  exact ⟨u, Subtype.ext hu⟩

lemma dirichlet_nonnegative (hc : DirichletCoercive Ω a hd) : a.IsNonnegative := by
  obtain ⟨c, hc, hb⟩ := hc
  intro w
  obtain ⟨u, rfl⟩ := dirichletLift_surjective Ω a hd w
  exact (mul_nonneg hc.le (sq_nonneg ‖u‖)).trans (hb u)

/-- Boundedness and coercivity on the full H¹₀ norm prove completeness
for the form norm. No energy-space completeness is assumed. -/
lemma dirichlet_closed (hs : a.IsHermitian) (hb : DirichletBounded Ω a hd)
    (hc : DirichletCoercive Ω a hd) :
    (a.toNonnegative hs (dirichlet_nonnegative Ω a hd hc)).IsClosed := by
  let hn := dirichlet_nonnegative Ω a hd hc
  let q := a.toNonnegative hs hn
  let e : H10 𝕜 Ω →ₗ[𝕜] q.EnergySpace :=
    { toFun := fun u => show q.EnergySpace from dirichletLift Ω a hd u
      map_add' := fun u v => Subtype.ext ((hZeroUnderlying Ω).map_add u v)
      map_smul' := fun c u => Subtype.ext ((hZeroUnderlying Ω).map_smul c u) }
  have he (u : H10 𝕜 Ω) :
      ‖e u‖ ^ 2 = RCLike.re (a.form (dirichletLift Ω a hd u) (dirichletLift Ω a hd u)) +
        ‖hZeroUnderlying Ω u‖ ^ 2 := q.energy_norm (e u)
  obtain ⟨M, hM⟩ := hb
  let D := |M| + ‖hZeroUnderlying (𝕜 := 𝕜) Ω‖ ^ 2 + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hupper (u : H10 𝕜 Ω) : ‖e u‖ ≤ Real.sqrt D * ‖u‖ := by
    have ha := (RCLike.re_le_norm (a.form (dirichletLift Ω a hd u)
      (dirichletLift Ω a hd u))).trans (hM u u)
    have hj : ‖hZeroUnderlying Ω u‖ ≤ ‖hZeroUnderlying (𝕜 := 𝕜) Ω‖ * ‖u‖ :=
      (hZeroUnderlying (𝕜 := 𝕜) Ω).le_opNorm u
    have hj2 := pow_le_pow_left₀ (norm_nonneg _) hj 2
    have hm : M * ‖u‖ * ‖u‖ ≤ |M| * ‖u‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self M)) (sq_nonneg ‖u‖)]
    have hsq : ‖e u‖ ^ 2 ≤ D * ‖u‖ ^ 2 := by
      rw [he]
      dsimp only [D]
      nlinarith only [he u, ha, hj2, hm, sq_nonneg ‖u‖]
    have hroot : (Real.sqrt D * ‖u‖) ^ 2 = D * ‖u‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hD]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg D) (norm_nonneg u))).mp
      (hsq.trans_eq hroot.symm)
  let E : H10 𝕜 Ω →L[𝕜] q.EnergySpace := e.mkContinuous (Real.sqrt D) hupper
  obtain ⟨c, hcp, hcoerce⟩ := hc
  have hlower (u : H10 𝕜 Ω) : ‖u‖ ≤ (Real.sqrt c)⁻¹ * ‖E u‖ := by
    have hcu : c * ‖u‖ ^ 2 ≤ ‖E u‖ ^ 2 := by
      change c * ‖u‖ ^ 2 ≤ ‖e u‖ ^ 2
      rw [he]
      exact (hcoerce u).trans (le_add_of_nonneg_right (sq_nonneg _))
    have hroot : (Real.sqrt c * ‖u‖) ^ 2 = c * ‖u‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcp.le]
    have hh : Real.sqrt c * ‖u‖ ≤ ‖E u‖ := by
      exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg u)) (norm_nonneg _)).mp
        (hroot.trans_le hcu)
    exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hcp)).mpr hh
  let K : NNReal := ⟨(Real.sqrt c)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg c)⟩
  have hanti := E.antilipschitz_of_bound (K := K) hlower
  have hsurj : Function.Surjective E := dirichletLift_surjective Ω a hd
  exact (hanti.isUniformInducing E.uniformContinuous).completeSpace_congr hsurj |>.mp inferInstance

end Dirichlet

/-- Symmetric compatibility for every bounded coercive Hermitian Dirichlet form,
including lower-order terms, on the canonical L² and full-H¹₀ spaces. -/
theorem symmetric_dirichlet_fredholm : Expected.Dirichlet := by
  intro 𝕜 _ m Ω _ a hd hs hb hc hcompact r
  exact closed_form_symmetric_fredholm a hs (dirichlet_nonnegative Ω a hd hc)
    (dirichlet_closed Ω a hd hs hb hc) hcompact r

end P201.Elliptic.SymmetricFredholm
