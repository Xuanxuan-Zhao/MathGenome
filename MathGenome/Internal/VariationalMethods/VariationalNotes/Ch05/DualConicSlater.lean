import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.DualConicSlater
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.ConicSlater
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorAffine
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open Set
universe u v
namespace VariationalNotes.Ch05.DualConicSlater
open ConicProgramModels VariationalNotes.ConvexGeometry

section Cone
variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem innerPositiveDual_closed (K : Set X) : IsClosed (innerPositiveDual K) := by
  have heq : innerPositiveDual K = ⋂ x ∈ K, {s : X | 0 ≤ inner ℝ s x} := by
    ext s
    change (∀ x ∈ K, 0 ≤ inner ℝ s x) ↔ _
    simp
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem innerPositiveDual_cone (K : Set X) : IsCone (innerPositiveDual K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp
  · intro s t hs ht x hx
    change 0 ≤ inner ℝ (s + t) x
    change ∀ x ∈ K, 0 ≤ inner ℝ s x at hs
    change ∀ x ∈ K, 0 ≤ inner ℝ t x at ht
    simpa only [inner_add_left] using add_nonneg (hs x hx) (ht x hx)
  · intro r hr s hs x hx
    change 0 ≤ inner ℝ (r • s) x
    change ∀ x ∈ K, 0 ≤ inner ℝ s x at hs
    simpa only [inner_smul_left, conj_trivial] using mul_nonneg hr (hs x hx)

variable [FiniteDimensional ℝ X]

theorem innerPositiveDual_bipolar (K : Set X) (hK : IsClosed K) (hcone : IsCone K) :
    innerPositiveDual (innerPositiveDual K) = K := by
  conv_rhs => rw [← closed_cone_positive_bipolar K hK hcone]
  ext x
  constructor
  · intro hx l hl
    let s : X := (InnerProductSpace.toDual ℝ X).symm l
    have hs : s ∈ innerPositiveDual K := by
      intro t ht
      change (InnerProductSpace.toDual ℝ X) s t ≥ 0
      simpa [s] using hl t ht
    change ∀ s ∈ innerPositiveDual K, 0 ≤ inner ℝ x s at hx
    have hlsx : inner ℝ s x = l x := by
      change (InnerProductSpace.toDual ℝ X) s x = l x
      simp [s]
    rw [← hlsx, real_inner_comm]
    exact hx s hs
  · intro hx s hs
    change 0 ≤ inner ℝ x s
    rw [real_inner_comm]
    exact hx ((InnerProductSpace.toDual ℝ X) s) hs
end Cone

/-- Apply primal Slater to the dual written in equality-constrained conic form. -/
theorem dual_conic_slater : Specs.dual_conic_slater.{u,v} := by
  classical
  intro X _ _ _ Y _ _ _ K A b c hclosed hcone d hd hex
  change dualValue K A b c = (d : EReal) at hd
  obtain ⟨y₀, hy₀⟩ := hex
  let S := innerPositiveDual K
  have hSclosed : IsClosed S := innerPositiveDual_closed K
  have hScone : IsCone S := innerPositiveDual_cone K
  have hSconv : Convex ℝ S := cone_convex S hScone
  let Z := WithLp 2 (Y × X)
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ Y X
  let C : Set Z := {q | q.snd ∈ S}
  let B : Z →ₗ[ℝ] X := A.adjoint.comp (WithLp.fstₗ 2 ℝ Y X) +
    WithLp.sndₗ 2 ℝ Y X
  let cost : Z := WithLp.toLp 2 (-b, 0)
  have hCclosed : IsClosed C := hSclosed.preimage (WithLp.sndL 2 ℝ Y X).continuous
  have hCcone : IsCone C := by
    refine ⟨hScone.1, ?_, ?_⟩
    · intro q r hq hr
      exact hScone.2.1 hq hr
    · intro t ht q hq
      exact hScone.2.2 t ht hq
  have hcost (q : Z) : inner ℝ cost q = -inner ℝ b q.fst := by
    change inner ℝ (-b) q.fst + inner ℝ (0 : X) q.snd = _
    simp
  have hB (q : Z) : B q = A.adjoint q.fst + q.snd := rfl
  have hCeq : C = e ⁻¹' ((univ : Set Y) ×ˢ S) := by
    ext q
    simp [C, e]
  have hri : WithLp.toLp 2 (y₀, c - A.adjoint y₀) ∈ relativeInterior C := by
    have hyri : y₀ ∈ relativeInterior (univ : Set Y) :=
      interior_subset_intrinsicInterior (by simp)
    have hprod : (y₀, c - A.adjoint y₀) ∈
        relativeInterior ((univ : Set Y) ×ˢ S) := by
      rw [relativeInterior_product _ _ convex_univ (by simp) hSconv ⟨0, hScone.1⟩]
      exact ⟨hyri, hy₀⟩
    rw [hCeq]
    change _ ∈ relativeInterior (e.toLinearMap.toAffineMap ⁻¹' ((univ : Set Y) ×ˢ S))
    rw [relativeInterior_affine_preimage e.toLinearMap.toAffineMap _
      (convex_univ.prod hSconv)
      ⟨(y₀, c - A.adjoint y₀),
        ⟨WithLp.toLp 2 (y₀, c - A.adjoint y₀), rfl⟩, hprod⟩]
    exact hprod
  have hneg : -(dualValue K A b c) =
      ⨅ y ∈ dualFeasible K A c, ((-inner ℝ b y : ℝ) : EReal) := by
    exact EReal.negOrderIso.map_iSup₂
      (fun y (_ : y ∈ dualFeasible K A c) => (inner ℝ b y : EReal))
  have hval : primalValue C B c cost = (-d : ℝ) := by
    have heq : primalValue C B c cost =
        ⨅ y ∈ dualFeasible K A c, ((-inner ℝ b y : ℝ) : EReal) := by
      apply le_antisymm
      · apply le_iInf
        intro y
        apply le_iInf
        intro hy
        let q : Z := WithLp.toLp 2 (y, c - A.adjoint y)
        have hq : q ∈ primalFeasible C B c := by
          refine ⟨hy, ?_⟩
          rw [hB]
          change A.adjoint y + (c - A.adjoint y) = c
          abel
        exact (iInf_le_of_le q (iInf_le_of_le hq le_rfl)).trans_eq
          (by rw [hcost]; rfl)
      · apply le_iInf
        intro q
        apply le_iInf
        intro hq
        have hy : q.fst ∈ dualFeasible K A c := by
          have hqB := hq.2
          rw [hB] at hqB
          have hs : c - A.adjoint q.fst = q.snd := by rw [← hqB]; abel
          change c - A.adjoint q.fst ∈ S
          rw [hs]
          exact hq.1
        rw [hcost]
        exact iInf_le_of_le q.fst (iInf_le_of_le hy le_rfl)
    rw [heq, ← hneg, hd, ← EReal.coe_neg]
  obtain ⟨z, hz, hzval, _⟩ := ConicSlater.conic_slater C B c cost
    hCclosed hCcone (-d) hval
    ⟨WithLp.toLp 2 (y₀, c - A.adjoint y₀), hri, by
      rw [hB]; change A.adjoint y₀ + (c - A.adjoint y₀) = c; abel⟩
  have hineq (y : Y) (s : X) (hs : s ∈ S) :
      0 ≤ -inner ℝ b y - inner ℝ z (A.adjoint y + s) := by
    have hi := hz (WithLp.toLp 2 (y, s)) hs
    change 0 ≤ inner ℝ (cost - B.adjoint z) (WithLp.toLp 2 (y, s)) at hi
    rw [inner_sub_left, LinearMap.adjoint_inner_left, hcost, hB] at hi
    exact hi
  have hAz : A z = -b := by
    have hi := hineq (b + A z) 0 hScone.1
    rw [add_zero, LinearMap.adjoint_inner_right] at hi
    have hself : inner ℝ (b + A z) (b + A z) ≤ 0 := by
      rw [inner_add_left]
      linarith
    have heq : b + A z = 0 := inner_self_eq_zero.mp
      (le_antisymm hself real_inner_self_nonneg)
    exact eq_neg_of_add_eq_zero_right heq
  have hxK : -z ∈ K := by
    rw [← innerPositiveDual_bipolar K hclosed hcone]
    change ∀ s ∈ S, 0 ≤ inner ℝ (-z) s
    intro s hs
    have hi := hineq 0 s hs
    simpa using hi
  have hx : -z ∈ primalFeasible K A b := by
    exact ⟨hxK, by rw [map_neg, hAz, neg_neg]⟩
  have hxval : inner ℝ c (-z) = d := by
    rw [inner_neg_right, hzval, neg_neg]
  refine ⟨-z, hx, hxval, le_antisymm ?_ ?_⟩
  · exact (iInf_le_of_le (-z) (iInf_le_of_le hx le_rfl)).trans_eq
      (congrArg (fun r : ℝ => (r : EReal)) hxval)
  · exact hd ▸ value_weak_duality K A b c

end VariationalNotes.Ch05.DualConicSlater
