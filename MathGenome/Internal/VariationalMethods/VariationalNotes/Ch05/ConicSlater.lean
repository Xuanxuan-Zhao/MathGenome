import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicSlater
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.ConicProgramModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.LocalValueSupport
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open Set Topology
universe u v
namespace VariationalNotes.Ch05.ConicSlater
open ConicProgramModels VariationalNotes.ConvexGeometry VariationalNotes.ConvexAnalysis

section Perturbation
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- A finite objective precisely on the perturbed feasible fiber. -/
private def perturbation (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X)
    (j : W →ₗ[ℝ] Y) (z : X × W) : WithTop ℝ := by
  classical
  exact if z.1 ∈ K ∧ A z.1 = b + j z.2 then (inner ℝ c z.1 : ℝ) else ⊤

private theorem perturbation_convex (K : Set X) (hK : Convex ℝ K)
    (A : X →ₗ[ℝ] Y) (b : Y) (c : X) (j : W →ₗ[ℝ] Y) :
    IsConvex (perturbation K A b c j) := by
  classical
  apply (convex_iff_twoPoint _).mpr
  intro z z' r s hz hz' a d ha hd had
  have hcond : z.1 ∈ K ∧ A z.1 = b + j z.2 := by
    by_contra h
    simp [perturbation, h] at hz
  have hcond' : z'.1 ∈ K ∧ A z'.1 = b + j z'.2 := by
    by_contra h
    simp [perturbation, h] at hz'
  have hr : inner ℝ c z.1 = r := by simpa [perturbation, hcond] using hz
  have hs : inner ℝ c z'.1 = s := by simpa [perturbation, hcond'] using hz'
  have heq : A (a • z.1 + d • z'.1) = b + j (a • z.2 + d • z'.2) := by
    simp only [map_add, map_smul, hcond.2, hcond'.2, smul_add]
    have hb : a • b + d • b = b := by rw [← add_smul, had, one_smul]
    calc
      _ = (a • b + d • b) + (a • j z.2 + d • j z'.2) := by abel
      _ = _ := by rw [hb]
  have hc : a • z.1 + d • z'.1 ∈ K := hK hcond.1 hcond'.1 ha hd had
  change (if _ then _ else _) ≤ _
  rw [ite_eq_left ⟨hc, heq⟩]
  simp [inner_add_right, inner_smul_right, hr, hs]

private theorem perturbation_zero (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X)
    (j : W →ₗ[ℝ] Y) :
    Ch04.marginal (perturbation K A b c j) 0 =
      (⨅ x ∈ {x | x ∈ K ∧ A x = b}, (inner ℝ c x : EReal)) := by
  classical
  change (⨅ x, ConvexAnalysis.Specs.toEReal (perturbation K A b c j (x, 0))) = _
  apply iInf_congr
  intro x
  by_cases h : x ∈ K ∧ A x = b <;>
    simp [perturbation, ConvexAnalysis.Specs.toEReal, h] <;> rfl
end Perturbation

/-- For a cone containing zero its affine hull is its linear span. -/
private theorem interior_in_span
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (h0 : (0 : X) ∈ K) (x₀ : X) (hx : x₀ ∈ relativeInterior K) :
    (⟨x₀, Submodule.subset_span (intrinsicInterior_subset hx)⟩ : Submodule.span ℝ K) ∈
      interior ((Subtype.val : Submodule.span ℝ K → X) ⁻¹' K) := by
  have hspan : affineSpan ℝ K = (Submodule.span ℝ K).toAffineSubspace :=
    affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ K h0)
  have hxK : x₀ ∈ K := intrinsicInterior_subset hx
  change x₀ ∈ intrinsicInterior ℝ K at hx
  rw [intrinsicInterior, hspan] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hz' : z = ⟨x₀, Submodule.subset_span hxK⟩ := Subtype.ext hzx
  exact hz' ▸ hz

/-- Relative Slater feasibility gives a supporting multiplier even when
K and A have proper spans. -/
theorem conic_slater : Specs.conic_slater.{u,v} := by
  classical
  intro X _ _ _ Y _ _ _ K A b c _hclosed hcone p hp hex
  obtain ⟨x₀, hx₀, hAx₀⟩ := hex
  have hconv : Convex ℝ K := cone_convex K hcone
  have hx₀K : x₀ ∈ K := intrinsicInterior_subset hx₀
  let V := Submodule.span ℝ K
  let B : V →ₗ[ℝ] Y := A.comp V.subtype
  let W := B.range
  let D : V →ₗ[ℝ] W := B.rangeRestrict
  obtain ⟨R, hR⟩ := D.exists_rightInverse_of_surjective B.range_rangeRestrict
  let j : W →ₗ[ℝ] Y := W.subtype
  let xV : V := ⟨x₀, Submodule.subset_span hx₀K⟩
  have hR' (u : W) : A (R u : X) = (u : Y) :=
    congrArg Subtype.val (LinearMap.congr_fun hR u)
  have hxV : xV ∈ interior ((Subtype.val : V → X) ⁻¹' K) :=
    interior_in_span K hcone.1 x₀ hx₀
  have hT : Continuous (fun u : W => xV + R u) :=
    continuous_const.add R.continuous_of_finiteDimensional
  have hnear : ∀ᶠ u : W in 𝓝 0, ((xV + R u : V) : X) ∈ K := by
    have hh : (Subtype.val ⁻¹' K : Set V) ∈ 𝓝 (xV + R (0 : W)) := by
      simpa only [map_zero, add_zero] using mem_interior_iff_mem_nhds.mp hxV
    exact hT.continuousAt.preimage_mem_nhds hh
  have hcost : Continuous (fun u : W => inner ℝ c ((xV + R u : V) : X)) :=
    continuous_const.inner (continuous_subtype_val.comp hT)
  have hbound : ∀ᶠ u : W in 𝓝 0,
      inner ℝ c ((xV + R u : V) : X) < inner ℝ c x₀ + 1 := by
    apply hcost.continuousAt.eventually_lt_const
    simp [xV]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hnear.and hbound)
  let Φ : X × W → WithTop ℝ := perturbation K A b c j
  have hΦ : IsConvex Φ := perturbation_convex K hconv A b c j
  have hΦ0 : Φ (x₀, 0) = (inner ℝ c x₀ : WithTop ℝ) := by
    simp [Φ, perturbation, hx₀K, hAx₀]
  have hproper : Proper Φ := (proper_iff_exists_real Φ).mpr ⟨(x₀, 0), _, hΦ0⟩
  have hm0 : Ch04.marginal Φ 0 = (p : EReal) :=
    (perturbation_zero K A b c j).trans hp
  have hM : ∀ u : W, ‖u‖ < r →
      Ch04.marginal Φ u ≤ ((inner ℝ c x₀ + 1 : ℝ) : EReal) := by
    intro u hu
    have hh := hball (show u ∈ Metric.ball (0 : W) r by simpa using hu)
    have heq : A ((xV + R u : V) : X) = b + j u := by
      change A (x₀ + (R u : X)) = b + (u : Y)
      rw [map_add, hAx₀, hR']
    have heval : Φ (((xV + R u : V) : X), u) =
        (inner ℝ c ((xV + R u : V) : X) : WithTop ℝ) := by
      dsimp only [Φ, perturbation]
      rw [ite_eq_left ⟨hh.1, heq⟩]
    have hcand := Ch04.marginal_le_candidate Φ ((xV + R u : V) : X) u
    rw [heval] at hcand
    exact hcand.trans (EReal.coe_le_coe_iff.mpr hh.2.le)
  obtain ⟨_, _, g, hg⟩ := Ch04.local_value_support Φ hproper hΦ p r
    (inner ℝ c x₀ + 1) hm0 hr hM
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq W g
  let y : Y := (InnerProductSpace.toDual ℝ Y).symm G
  have hy (u : W) : inner ℝ y (u : Y) = g u := by
    exact (InnerProductSpace.toDual_symm_apply).trans (hG u)
  have hsupp (x : X) (hx : x ∈ K) :
      p + inner ℝ y (A x - b) ≤ inner ℝ c x := by
    let u : W := D (⟨x, Submodule.subset_span hx⟩ - xV)
    have hu : (u : Y) = A x - b := by
      change A (x - x₀) = A x - b
      rw [map_sub, hAx₀]
    have hcand := Ch04.marginal_le_candidate Φ x u
    have heval : Φ (x, u) = (inner ℝ c x : WithTop ℝ) := by
      have heq : A x = b + j u := by change A x = b + (u : Y); rw [hu]; abel
      simp [Φ, perturbation, hx, heq]
    have hh := (hg u).trans hcand
    rw [heval] at hh
    have hh' : p + g u ≤ inner ℝ c x := EReal.coe_le_coe_iff.mp hh
    rw [← hy u, hu] at hh'
    exact hh'
  have hpb : p ≤ inner ℝ b y := by
    have hh := hsupp 0 hcone.1
    simp only [map_zero, zero_sub, inner_neg_right, inner_zero_right] at hh
    have hcomm : inner ℝ y b = inner ℝ b y := real_inner_comm _ _
    rw [hcomm] at hh
    linarith
  have hdual : y ∈ dualFeasible K A c := by
    apply (mem_innerPositiveDual K (c - A.adjoint y)).mpr
    intro x hx
    have hscale (t : ℝ) (ht : 0 ≤ t) :
        p - inner ℝ y b ≤ t * inner ℝ (c - A.adjoint y) x := by
      have hh := hsupp (t • x) (hcone.2.2 t ht hx)
      rw [map_smul, inner_sub_right, inner_smul_right, inner_smul_right] at hh
      rw [inner_sub_left, LinearMap.adjoint_inner_left]
      nlinarith
    by_contra hn
    have hn' : inner ℝ (c - A.adjoint y) x < 0 := lt_of_not_ge hn
    let t : ℝ := (|p - inner ℝ y b| + 1) / (-inner ℝ (c - A.adjoint y) x)
    have ht : 0 ≤ t := le_of_lt (div_pos (by positivity) (by linarith))
    have hh := hscale t ht
    have heq : t * inner ℝ (c - A.adjoint y) x = -(|p - inner ℝ y b| + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hn']
    rw [heq] at hh
    linarith [neg_abs_le (p - inner ℝ y b)]
  have hyp : inner ℝ b y ≤ p := by
    have hh : (inner ℝ b y : EReal) ≤ primalValue K A b c := by
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      exact EReal.coe_le_coe_iff.mpr (weak_duality K A b c x y hx hdual)
    change (inner ℝ b y : EReal) ≤ ConicProgramModels.Specs.primalValue K A b c at hh
    rw [hp] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have heq : inner ℝ b y = p := le_antisymm hyp hpb
  refine ⟨y, hdual, heq, le_antisymm ?_ ?_⟩
  · exact (value_weak_duality K A b c).trans_eq hp
  · rw [← heq]
    exact le_iSup_of_le y (le_iSup_of_le hdual le_rfl)

end VariationalNotes.Ch05.ConicSlater
