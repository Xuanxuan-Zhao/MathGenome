import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.LICQMultiplierUniqueness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.KKTNecessity
import Mathlib.LinearAlgebra.LinearIndependent.Basic

noncomputable section
universe u v w
namespace VariationalNotes.Ch06
open ContinuousLinearMap

theorem kkt_multipliers_unique_of_licq :
    LICQMultiplierUniquenessSpecs.kkt_multipliers_unique_of_licq.{u,v,w} := by
  classical
  intro X _ _ I J _ _ U f g h x lam lam' nu nu' hl hk hk'
  have hactive (a : I → ℝ) (b : J → ℝ) (ha : KKT U f g h x a b) :
      (∑ i : {i // i ∈ activeSet g x}, a i.val • fderiv ℝ (g i.val) x) =
        ∑ i, a i • fderiv ℝ (g i) x := by
    have hinactive : (∑ i : {i // i ∉ activeSet g x},
        a i.val • fderiv ℝ (g i.val) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [kkt_inactive_multiplier U f g h x a b ha i.val i.property, zero_smul]
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun i => i ∈ activeSet g x) (fun i => a i • fderiv ℝ (g i) x)
    rwa [hinactive, add_zero] at hsplit
  let l : ({i // i ∈ activeSet g x} ⊕ J) → X →L[ℝ] ℝ :=
    Sum.elim (fun i => fderiv ℝ (g i.val) x) (fun j => fderiv ℝ (h j) x)
  let c : ({i // i ∈ activeSet g x} ⊕ J) → ℝ :=
    Sum.elim (fun i => lam i.val) nu
  let c' : ({i // i ∈ activeSet g x} ⊕ J) → ℝ :=
    Sum.elim (fun i => lam' i.val) nu'
  have heq : ∑ k, c k • l k = ∑ k, c' k • l k := by
    simp only [Fintype.sum_sum_type, c, c', l, Sum.elim_inl, Sum.elim_inr]
    rw [hactive lam nu hk, hactive lam' nu' hk']
    apply add_left_cancel (a := fderiv ℝ f x)
    simpa only [add_assoc] using hk.2.2.2.trans hk'.2.2.2.symm
  have hcoords : ∀ k, c k = c' k := hl.2.eq_coords_of_eq heq
  constructor
  · funext i
    by_cases hi : i ∈ activeSet g x
    · exact hcoords (Sum.inl ⟨i, hi⟩)
    · rw [kkt_inactive_multiplier U f g h x lam nu hk i hi,
        kkt_inactive_multiplier U f g h x lam' nu' hk' i hi]
  · funext j
    exact hcoords (Sum.inr j)

theorem existsUnique_kkt_of_licq :
    LICQMultiplierUniquenessSpecs.existsUnique_kkt_of_licq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hmin hl
  obtain ⟨lam, nu, hk⟩ := kkt_of_licq U f g h x hs hmin hl
  refine ⟨(lam, nu), hk, kkt_inactive_multiplier U f g h x lam nu hk, ?_⟩
  intro q hq
  obtain ⟨hlam, hnu⟩ := kkt_multipliers_unique_of_licq U f g h x q.1 lam q.2 nu hl hq hk
  exact Prod.ext hlam hnu

end VariationalNotes.Ch06
