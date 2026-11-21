import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.LocalUniformBound

/-! The local uniform bound for pointwise bounded families, without any
separation, metric, or countability hypothesis on the nonempty Baire domain.
-/

open Set
universe u

namespace D10Topology.Ch14

/-- `paper.tex`, proposition `d10:14:local-uniform-boundedness`. -/
theorem local_uniform_bound {X : Type u} [TopologicalSpace X] [Nonempty X]
    (hX : BaireIn X) (A : Set C(X, ℝ))
    (hA : ∀ x : X, ∃ b : ℝ, ∀ f ∈ A, |f x| ≤ b) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∃ M : ℤ, 1 ≤ M ∧ ∀ f ∈ A, ∀ x ∈ U, |f x| ≤ (M : ℝ) := by
  let : BaireSpace X := (baire_iff_library X).mp hX
  let F : ℕ → Set X := fun n => {x | ∀ f ∈ A, |f x| ≤ ((n + 1 : ℕ) : ℝ)}
  have hclosed (n : ℕ) : IsClosed (F n) := by
    simp only [F, ofPred_forall]
    refine isClosed_iInter fun f => isClosed_iInter fun _ => ?_
    simpa only [preimage_ofPred_eq, Icc, abs_le] using
      (isClosed_Icc.preimage f.continuous :
        IsClosed (f ⁻¹' Icc (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)))
  have hcover : ⋃ n, F n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨b, hb⟩ := hA x
    obtain ⟨n, hn⟩ := exists_nat_gt b
    apply mem_iUnion.mpr
    refine ⟨n, fun f hf => (hb f hf).trans ?_⟩
    exact hn.le.trans (by exact_mod_cast Nat.le_succ n)
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  refine ⟨interior (F n), isOpen_interior, hn, ((n + 1 : ℕ) : ℤ), ?_, ?_⟩
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  · intro f hf x hx
    simpa only [Int.cast_natCast] using (interior_subset hx : x ∈ F n) f hf

end D10Topology.Ch14
