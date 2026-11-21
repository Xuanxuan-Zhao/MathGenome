import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringHomotopies
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.CoveringPaths

/-! Homotopy lifting and invariance of lifted endpoints for topological
coverings. No separation, metric, or regularity assumption on the base
is needed. -/

namespace D12Complex.Ch20.CoveringHomotopies

open unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Lift the square with the constant map on its initial edge. The
covering homotopy theorem gives joint continuity, and path uniqueness
gives uniqueness on the whole square. -/
theorem homotopy_lifting (p : E → B) (hp : IsCovering p)
    (H : I × I → B) (hH : Continuous H) (a b : B)
    (h₀ : ∀ s, H (0, s) = a) (_h₁ : ∀ s, H (1, s) = b)
    (e₀ : E) (he₀ : p e₀ = a) :
    ∃! F : I × I → E, Continuous F ∧ (∀ s, F (0, s) = e₀) ∧ p ∘ F = H := by
  let cov := CoveringPaths.covering_bridge p hp
  let Hc : C(I × I, B) := ⟨H, hH⟩
  let f : C(I, E) := ContinuousMap.const I e₀
  have hi : ∀ s, Hc (0, s) = p (f s) := fun s => (h₀ s).trans he₀.symm
  let F := cov.liftHomotopy Hc f hi
  have hF₀ : ∀ s, F (0, s) = e₀ := cov.liftHomotopy_zero Hc f hi
  have hFp : p ∘ F = H := cov.liftHomotopy_lifts Hc f hi
  refine ⟨F, ⟨F.continuous, hF₀, hFp⟩, ?_⟩
  intro G hG
  exact (cov.eq_liftHomotopy_iff hi G).mpr
    ⟨fun s => hG.1.comp (Continuous.prodMk_left s), hG.2.2, hG.2.1⟩

/-- Every horizontal path in a lifted homotopy is the unique lift of
the corresponding base path from the prescribed starting point. -/
theorem restriction_path_lifting (p : E → B) (hp : IsCovering p)
    (H : I × I → B) (e₀ : E) (F : I × I → E)
    (hF : Continuous F) (hF₀ : ∀ s, F (0, s) = e₀) (hFp : p ∘ F = H)
    (s : I) :
    Continuous (fun t => F (t, s)) ∧ F (0, s) = e₀ ∧
      p ∘ (fun t => F (t, s)) = (fun t => H (t, s)) ∧
      ∀ Γ : I → E, Continuous Γ → Γ 0 = e₀ →
        p ∘ Γ = (fun t => H (t, s)) → Γ = (fun t => F (t, s)) := by
  have hcont : Continuous (fun t => F (t, s)) :=
    hF.comp (Continuous.prodMk_left s)
  have hlift : p ∘ (fun t => F (t, s)) = (fun t => H (t, s)) :=
    funext fun t => congrFun hFp (t, s)
  refine ⟨hcont, hF₀ s, hlift, ?_⟩
  intro Γ hΓ hΓ₀ hΓp
  exact (CoveringPaths.covering_bridge p hp).eq_of_comp_eq hΓ hcont
    (hΓp.trans hlift.symm) 0 (hΓ₀.trans (hF₀ s).symm)

/-- A continuous edge lying over a single base point is constant:
uniqueness for covering maps applies to a connected parameter interval. -/
theorem lifted_endpoints (p : E → B) (hp : IsCovering p)
    (H : I × I → B) (b : B) (h₁ : ∀ s, H (1, s) = b)
    (F : I × I → E) (hF : Continuous F) (hFp : p ∘ F = H)
    (s s' : I) : F (1, s) = F (1, s') := by
  apply (CoveringPaths.covering_bridge p hp).const_of_comp
    (hF.comp (Continuous.prodMk_right (1 : I))) _ s s'
  intro r r'
  exact (congrFun hFp (1, r)).trans
    ((h₁ r).trans ((h₁ r').symm.trans (congrFun hFp (1, r')).symm))

end D12Complex.Ch20.CoveringHomotopies
