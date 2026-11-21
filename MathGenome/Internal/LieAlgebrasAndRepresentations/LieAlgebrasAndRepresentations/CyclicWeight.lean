import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CyclicWeight

universe u v w t

namespace LieAlgebrasAndRepresentations

open Specs.LieAlgebrasAndRepresentations.CyclicWeight

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type v} [LieRing G] [LieAlgebra k G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [LieRingModule G V] [LieModule k G V] [Module.Finite k V]

/-- The full common eigenspace is stable under the ambient Lie algebra.
Mathlib's theorem uses the same finite-dimensional, characteristic-zero trace
argument as the source; it assumes neither solvability nor algebraic closure. -/
theorem common_weight_stable (B : LieIdeal k G) (χ : B → k)
    (x : G) (z : V) (hz : ∀ b : B, ⁅b, z⁆ = χ b • z) :
    ∀ b : B, ⁅b, ⁅x, z⁆⁆ = χ b • ⁅x, z⁆ := by
  have hz' : z ∈ LieModule.weightSpaceOfIsLieTower k V χ :=
    (LieModule.mem_weightSpace χ z).mpr hz
  exact (LieModule.mem_weightSpace χ ⁅x, z⁆).mp
    ((LieModule.weightSpaceOfIsLieTower k V χ).lie_mem hz')

theorem cyclic_weight (B : LieIdeal k G) (x : G) (χ : B → k) (v : V)
    (hv : v ≠ 0) (he : ∀ b : B, ⁅b, v⁆ = χ b • v) :
    (∀ z ∈ cyclicSpace (k := k) x v, ⁅x, z⁆ ∈ cyclicSpace (k := k) x v) ∧
    (∀ b : B, ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ ∈ cyclicSpace (k := k) x v) ∧
    (∀ b : B, ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ = χ b • z) ∧
    (∀ b : B, χ ⁅x, b⁆ = 0) ∧
    (∀ z : V, (∀ b : B, ⁅b, z⁆ = χ b • z) →
      ∀ b : B, ⁅b, ⁅x, z⁆⁆ = χ b • ⁅x, z⁆) := by
  have hstable := common_weight_stable (V := V) B χ x
  have hpowers (n : ℕ) : ∀ b : B,
      ⁅b, (LieModule.toEnd k G V x ^ n) v⁆ =
        χ b • (LieModule.toEnd k G V x ^ n) v := by
    induction n with
    | zero => simpa using he
    | succ n ih =>
      simpa only [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
        using hstable _ ih
  have hW : cyclicSpace (k := k) x v ≤ (LieModule.weightSpace V χ).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro z ⟨n, rfl⟩
    exact (LieModule.mem_weightSpace χ _).mpr (hpowers n)
  have hxW : ∀ z ∈ cyclicSpace (k := k) x v, ⁅x, z⁆ ∈ cyclicSpace (k := k) x v := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      exact Submodule.subset_span ⟨n + 1, by
        simp only [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]⟩
    | zero => simp
    | add z t hz ht ihz iht => simpa only [lie_add] using add_mem ihz iht
    | smul a z hz ih => simpa only [lie_smul] using Submodule.smul_mem _ a ih
  refine ⟨hxW, ?_, ?_, ?_, fun z hz => hstable z hz⟩
  · intro b z hz
    rw [(LieModule.mem_weightSpace χ z).mp (hW hz) b]
    exact Submodule.smul_mem _ _ hz
  · intro b z hz
    exact (LieModule.mem_weightSpace χ z).mp (hW hz) b
  · intro b
    have h := leibniz_lie x b v
    rw [he b, lie_smul, hstable v he b, he ⁅x, b⁆] at h
    have hzero : χ ⁅x, b⁆ • v = 0 := by
      exact add_right_cancel (h.symm.trans (zero_add _).symm)
    exact (smul_eq_zero.mp hzero).resolve_right hv

/-- The ideal acts by scalar matrices in every basis of k[x]v, hence in its
cyclic basis. Both the invariant-subspace proof and all matrix entries are
included explicitly. -/
theorem cyclic_weight_diagonal (B : LieIdeal k G) (x : G) (χ : B → k) (v : V)
    (hv : v ≠ 0) (he : ∀ b : B, ⁅b, v⁆ = χ b • v)
    {ι : Type t} [DecidableEq ι]
    (e : Module.Basis ι k (cyclicSpace (k := k) x v)) (b : B) :
    ∃ hb : ∀ z ∈ cyclicSpace (k := k) x v, ⁅b, z⁆ ∈ cyclicSpace (k := k) x v,
      ∀ i j : ι,
        e.repr ⟨⁅b, (e j : V)⁆, hb (e j) (e j).property⟩ i =
          if i = j then χ b else 0 := by
  obtain ⟨_, hb, hs, _, _⟩ := cyclic_weight B x χ v hv he
  refine ⟨hb b, fun i j => ?_⟩
  have h : (⟨⁅b, (e j : V)⁆, hb b (e j) (e j).property⟩ :
      cyclicSpace (k := k) x v) = χ b • e j :=
    Subtype.ext (hs b (e j) (e j).property)
  rw [h, map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply]
  by_cases hij : i = j <;> simp [hij, eq_comm]

end LieAlgebrasAndRepresentations
