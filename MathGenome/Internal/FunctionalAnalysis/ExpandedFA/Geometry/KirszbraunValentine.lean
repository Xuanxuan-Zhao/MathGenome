import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.KirszbraunValentine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.HilbertBallIntersection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Order.Zorn

/-! Kirszbraun–Valentine for arbitrary Hilbert spaces. The finite intersection
result is the accepted finite stage. For the unrestricted intersection we use
Riesz representation and weak-star compactness of a dual ball (equivalently,
weak compactness of a Hilbert ball). Zorn's lemma is applied to graphs of
contractions; no countability hypothesis enters either step. -/
noncomputable section
open Set
namespace ExpandedFA.Geometry.KirszbraunValentine

/-- Arbitrary, possibly uncountable, Kirszbraun ball intersection. -/
lemma ball_intersection_real {ι H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (s : ι → H₁) (y : ι → H₂)
    (h : ∀ i j, ‖y i - y j‖ ≤ ‖s i - s j‖) (x : H₁) :
    ∃ p : H₂, ∀ i, ‖p - y i‖ ≤ ‖s i - x‖ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi => exact ⟨0, fun i => (hi.false i).elim⟩
  | inr hi =>
    let e := InnerProductSpace.toDual ℝ H₂
    let B : ι → Set (WeakDual ℝ H₂) := fun i =>
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (e (y i)) ‖s i - x‖
    let i₀ : ι := hi.some
    have hf : ∀ u : Finset ι, (⋂ i ∈ u, B i).Nonempty := by
      intro u
      obtain ⟨p, hp⟩ := HilbertBallIntersection.finite_ball_intersection_real
        (fun i : u => s i) (fun i : u => y i) (fun i j => h i j) x
      refine ⟨StrongDual.toWeakDual (e p), mem_iInter₂.mpr fun i hi => ?_⟩
      have hp' := mem_iInter.mp hp (⟨i, hi⟩ : u)
      change dist (e p) (e (y i)) ≤ ‖s i - x‖
      rw [e.isometry.dist_eq]
      exact hp'
    have hc : IsCompact (B i₀) := WeakDual.isCompact_closedBall _ _
    have hcl : ∀ i, IsClosed (B i) := fun i => WeakDual.isClosed_closedBall _ _
    obtain ⟨q, _, hq⟩ := hc.inter_iInter_nonempty B hcl (fun u => by
      obtain ⟨q, hq⟩ := hf (insert i₀ u)
      refine ⟨q, ?_, ?_⟩
      · exact mem_iInter₂.mp hq i₀ (Finset.mem_insert_self _ _)
      · exact mem_iInter₂.mpr fun i hi =>
          mem_iInter₂.mp hq i (Finset.mem_insert_of_mem hi))
    refine ⟨e.symm (WeakDual.toStrongDual q), fun i => ?_⟩
    have hqi := mem_iInter.mp hq i
    change dist (WeakDual.toStrongDual q) (e (y i)) ≤ ‖s i - x‖ at hqi
    rw [← e.apply_symm_apply (WeakDual.toStrongDual q), e.isometry.dist_eq,
      dist_eq_norm] at hqi
    exact hqi

/-- A contraction on a subset of a real inner-product space extends to the
whole space when the target is Hilbert. The source need not be complete. -/
lemma extend_contraction_real {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (S : Set H₁) (f : S → H₂)
    (hf : ∀ s t : S, ‖f s - f t‖ ≤ ‖(s : H₁) - (t : H₁)‖) :
    ∃ g : H₁ → H₂, (∀ x y, ‖g x - g y‖ ≤ ‖x - y‖) ∧
      ∀ s : S, g s = f s := by
  classical
  let C : Set (Set (H₁ × H₂)) := {G | ∀ p ∈ G, ∀ q ∈ G,
    ‖p.2 - q.2‖ ≤ ‖p.1 - q.1‖}
  let A : Set (H₁ × H₂) := Set.range (fun s : S => ((s : H₁), f s))
  have hA : A ∈ C := by
    rintro p ⟨s, rfl⟩ q ⟨t, rfl⟩
    exact hf s t
  obtain ⟨G, hAG, hG, hmax⟩ := zorn_subset_nonempty C (fun c hc hchain _ => by
    refine ⟨⋃₀ c, ?_, fun K hK => subset_sUnion_of_mem hK⟩
    rintro p ⟨K, hK, hp⟩ q ⟨J, hJ, hq⟩
    rcases hchain.total hK hJ with hKJ | hJK
    · exact hc hJ p (hKJ hp) q hq
    · exact hc hK p hp q (hJK hq)) A hA
  have htotal : ∀ x : H₁, ∃ y : H₂, (x, y) ∈ G := by
    intro x
    obtain ⟨y, hy⟩ := ball_intersection_real
      (fun p : G => p.val.1) (fun p : G => p.val.2)
      (fun p q => hG p p.property q q.property) x
    have hins : insert (x, y) G ∈ C := by
      intro p hp q hq
      rcases mem_insert_iff.mp hp with rfl | hp
      · rcases mem_insert_iff.mp hq with rfl | hq
        · simp
        · simpa only [norm_sub_rev] using hy (⟨q, hq⟩ : G)
      · rcases mem_insert_iff.mp hq with rfl | hq
        · have := hy (⟨p, hp⟩ : G)
          simpa only [norm_sub_rev] using this
        · exact hG p hp q hq
    exact ⟨y, hmax hins (subset_insert _ _) (mem_insert _ _)⟩
  choose g hg using htotal
  refine ⟨g, fun x y => hG _ (hg x) _ (hg y), fun s => ?_⟩
  have hs : ((s : H₁), f s) ∈ G := hAG ⟨s, rfl⟩
  have hh := hG _ (hg s) _ hs
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using hh

/-- Kirszbraun–Valentine with the same bound L, for independent real or
complex Hilbert spaces and every subset, including the empty subset. -/
theorem kirszbraun_valentine : Spec.Extension := by
  intro 𝕜₁ 𝕜₂ H₁ H₂ _ _ _ _ _ _ _ _ S L hL f hf
  let := InnerProductSpace.rclikeToReal 𝕜₁ H₁
  let := InnerProductSpace.rclikeToReal 𝕜₂ H₂
  by_cases hz : L = 0
  · cases isEmpty_or_nonempty S with
    | inl hi =>
      exact ⟨fun _ => 0, by simp [hz], fun s => (hi.false s).elim⟩
    | inr hi =>
      have hconst : ∀ s : S, f s = f hi.some := by
        intro s
        simpa only [hz, zero_mul, norm_le_zero_iff, sub_eq_zero] using hf s hi.some
      exact ⟨fun _ => f hi.some, by simp [hz], fun s => (hconst s).symm⟩
  · have hpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hz)
    have hn : ∀ s t : S, ‖L⁻¹ • f s - L⁻¹ • f t‖ ≤ ‖(s : H₁) - (t : H₁)‖ := by
      intro s t
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      calc
        L⁻¹ * ‖f s - f t‖ ≤ L⁻¹ * (L * ‖(s : H₁) - (t : H₁)‖) :=
          mul_le_mul_of_nonneg_left (hf s t) (inv_nonneg.mpr hL)
        _ = ‖(s : H₁) - (t : H₁)‖ := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    obtain ⟨g, hg, hgf⟩ := extend_contraction_real S (fun s => L⁻¹ • f s) hn
    refine ⟨fun x => L • g x, ?_, ?_⟩
    · intro x y
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
      exact mul_le_mul_of_nonneg_left (hg x y) hL
    · intro s
      change L • g (s : H₁) = f s
      rw [hgf s, smul_smul, mul_inv_cancel₀ hz, one_smul]

end ExpandedFA.Geometry.KirszbraunValentine
