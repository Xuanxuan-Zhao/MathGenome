import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationExactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationAlgebra
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Ring

noncomputable section
universe u v
open Set Filter
open scoped Topology
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis

section Pointwise
variable {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- A finite upper bound on the conjugate is the corresponding affine minorant. -/
lemma extendedConjugate_le_real_iff (g : Y → EReal) (y : Y →L[ℝ] ℝ) (c : ℝ) :
    Specs.extendedConjugate g y ≤ (c : EReal) ↔
      ∀ u, ((y u - c : ℝ) : EReal) ≤ g u := by
  change (⨆ u, (y u : EReal) - g u) ≤ (c : EReal) ↔ _
  simp only [iSup_le_iff, real_sub_le_real_iff]

/-- Equality with the biconjugate at a finite value implies pointwise lower
semicontinuity, by continuous affine minorants approaching that value. -/
lemma lowerSemicontinuousAt_of_biconjugate_eq (g : Y → EReal) (p : ℝ)
    (hp : g 0 = (p : EReal)) (heq : Specs.extendedBiconjugate g 0 = (p : EReal)) :
    LowerSemicontinuousAt g 0 := by
  intro z hz
  rw [hp] at hz
  obtain ⟨r, hzr, hrp⟩ := EReal.lt_iff_exists_real_btwn.mp hz
  have hrB : (r : EReal) < Specs.extendedBiconjugate g 0 := by rwa [heq]
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hrB
  have hlow : ((-p : ℝ) : EReal) ≤ Specs.extendedConjugate g y := by
    have h := le_iSup (fun u => (y u : EReal) - g u) 0
    simpa only [hp, map_zero, EReal.coe_zero, zero_sub, EReal.coe_neg, Specs.extendedConjugate] using h
  have hbot : Specs.extendedConjugate g y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  have htop : Specs.extendedConjugate g y ≠ ⊤ := by
    intro h
    simp only [h, EReal.sub_top] at hy
    exact not_lt_bot hy
  lift Specs.extendedConjugate g y to ℝ using ⟨htop, hbot⟩ with c hc
  have hm := (extendedConjugate_le_real_iff g y c).mp hc.ge
  have hz0 : z < ((y 0 - c : ℝ) : EReal) := by
    apply hzr.trans
    simpa only [← EReal.coe_sub] using hy
  have hcont : Continuous (fun u => ((y u - c : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (y.continuous.sub continuous_const)
  filter_upwards [hcont.lowerSemicontinuous 0 z hz0] with u hu
  exact hu.trans_le (hm u)

omit [Module ℝ Y] in
/-- Local lower semicontinuity excludes every point strictly below the finite
value from the closure of the real-height epigraph. -/
lemma below_not_mem_epigraph_closure (g : Y → EReal) (p : ℝ)
    (hp : g 0 = (p : EReal)) (hl : LowerSemicontinuousAt g 0)
    (r : ℝ) (hr : r < p) :
    (0, r) ∉ closure {q : Y × ℝ | g q.1 ≤ (q.2 : EReal)} := by
  obtain ⟨c, hrc, hcp⟩ := exists_between hr
  have hU : {u | (c : EReal) < g u} ∈ 𝓝 (0 : Y) :=
    hl (c : EReal) (by change (c : EReal) < g 0; rw [hp]; exact EReal.coe_lt_coe_iff.mpr hcp)
  have hV : Iio c ∈ 𝓝 r := Iio_mem_nhds hrc
  intro hcl
  obtain ⟨⟨u, t⟩, ⟨hu, ht⟩, hgt⟩ :=
    (mem_closure_iff_nhds.mp hcl) _ (prod_mem_nhds hU hV)
  exact (not_lt_of_ge hgt) ((EReal.coe_lt_coe_iff.mpr ht).trans hu)

variable [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y]

/-- Separating a point below the graph at zero supplies an affine minorant
whose value at zero exceeds the prescribed level. -/
lemma affine_minorant_above_at_zero (g : Y → EReal) (p : ℝ)
    (hp : g 0 = (p : EReal)) (hbot : ∀ u, g u ≠ ⊥)
    (hconv : Convex ℝ {q : Y × ℝ | g q.1 ≤ (q.2 : EReal)})
    (hl : LowerSemicontinuousAt g 0) (r : ℝ) (hr : r < p) :
    ∃ (y : Y →L[ℝ] ℝ) (c : ℝ), r < c ∧
      ∀ u, ((y u + c : ℝ) : EReal) ≤ g u := by
  obtain ⟨L, γ, hgap, hsep⟩ := geometric_hahn_banach_point_closed
    hconv.closure isClosed_closure (below_not_mem_epigraph_closure g p hp hl r hr)
  let a : Y →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ Y ℝ)
  let b : ℝ := L (0, 1)
  have hsplit (u : Y) (t : ℝ) : L (u, t) = a u + b * t := by
    have heq : (u, t) = (u, 0) + t • (0, (1 : ℝ)) := by ext <;> simp
    rw [heq, map_add, map_smul]
    simp [a, b, mul_comm]
  have hminor (u : Y) (t : ℝ) (ht : g u ≤ (t : EReal)) : γ ≤ a u + b * t := by
    rw [← hsplit]
    exact (hsep (u, t) (subset_closure ht)).le
  rw [hsplit, map_zero, zero_add] at hgap
  have hp' := hminor 0 p hp.le
  simp only [map_zero, zero_add] at hp'
  have hb : 0 < b := by nlinarith
  refine ⟨(-b⁻¹) • a, γ / b, (lt_div_iff₀ hb).mpr (by linarith), ?_⟩
  intro u
  rcases eq_or_ne (g u) ⊤ with hu | hu
  · rw [hu]; exact le_top
  · lift g u to ℝ using ⟨hu, hbot u⟩ with t ht
    apply EReal.coe_le_coe_iff.mpr
    have hh := hminor u t ht.ge
    change -b⁻¹ * a u + γ / b ≤ t
    rw [show -b⁻¹ * a u + γ / b = (γ - a u) / b by
      simp only [div_eq_mul_inv]; ring]
    exact (div_le_iff₀ hb).mpr (by linarith)

lemma biconjugate_eq_of_lowerSemicontinuousAt (g : Y → EReal) (p : ℝ)
    (hp : g 0 = (p : EReal)) (hbot : ∀ u, g u ≠ ⊥)
    (hconv : Convex ℝ {q : Y × ℝ | g q.1 ≤ (q.2 : EReal)})
    (hbound : Specs.extendedBiconjugate g 0 ≤ (p : EReal))
    (hl : LowerSemicontinuousAt g 0) :
    Specs.extendedBiconjugate g 0 = (p : EReal) := by
  apply le_antisymm hbound
  by_contra hn
  obtain ⟨r, hBr, hr⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  have hrp : r < p := EReal.coe_lt_coe_iff.mp hr
  obtain ⟨y, c, hrc, hm⟩ := affine_minorant_above_at_zero g p hp hbot hconv hl r hrp
  have hc : Specs.extendedConjugate g y ≤ ((-c : ℝ) : EReal) := by
    apply (extendedConjugate_le_real_iff g y (-c)).mpr
    simpa only [sub_neg_eq_add] using hm
  have hle : (c : EReal) ≤ Specs.extendedBiconjugate g 0 := by
    apply le_trans _ (le_iSup (fun y : Y →L[ℝ] ℝ =>
      (y 0 : EReal) - Specs.extendedConjugate g y) y)
    simpa only [map_zero, EReal.coe_zero, zero_sub, EReal.coe_neg, neg_neg] using
      EReal.neg_le_neg_iff.mpr hc
  exact (not_lt_of_ge ((EReal.coe_le_coe_iff.mpr hrc.le).trans hle)) hBr
end Pointwise

/-- Properness lets the finite-endpoint marginal inequality give the full
convexity of its finite-height epigraph. -/
lemma marginal_epigraph_convex {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hΦ : IsConvex Φ)
    (hbot : ∀ u, Specs.marginal Φ u ≠ ⊥) :
    Convex ℝ {q : Y × ℝ | Specs.marginal Φ q.1 ≤ (q.2 : EReal)} := by
  have hrep (u : Y) : ConvexAnalysis.Specs.toEReal (marginalFunction Φ u) =
      Specs.marginal Φ u := marginalFunction_representation Φ hbot u
  have hc : IsConvex (marginalFunction Φ) := by
    apply (convex_iff_twoPoint _).mpr
    intro u v r s hu hv a b ha hb hab
    apply (toEReal_conventions.2.2.2.2 _ _).mp
    rw [hrep]
    exact marginal_convex_finite Φ hΦ u v r s
      (by rw [← hrep, hu]; rfl) (by rw [← hrep, hv]; rfl) a b ha hb hab
  have hsets : {q : Y × ℝ | Specs.marginal Φ q.1 ≤ (q.2 : EReal)} =
      ConvexAnalysis.Specs.epigraph (marginalFunction Φ) := by
    ext q
    change Specs.marginal Φ q.1 ≤ (q.2 : EReal) ↔
      marginalFunction Φ q.1 ≤ (q.2 : WithTop ℝ)
    rw [← hrep]
    exact toEReal_conventions.2.2.2.2 _ _
  rw [hsets]
  exact hc

theorem perturbation_exactness : Specs.perturbation_exactness.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ hproper hconv hv p hp
  have hid := (perturbation_dual_bound Φ p hp).1
  rw [hid]
  constructor
  · exact lowerSemicontinuousAt_of_biconjugate_eq (Specs.marginal Φ) p hp
  · exact biconjugate_eq_of_lowerSemicontinuousAt (Specs.marginal Φ) p hp hv.1
      (marginal_epigraph_convex Φ hconv hv.1) (perturbation_dual_bound Φ p hp).2.1

theorem perturbation_duality : Specs.perturbation_duality.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ hproper hconv hv p hp
  exact ⟨perturbation_duality_algebra Φ hproper hconv hv p hp,
    perturbation_exactness Φ hproper hconv hv p hp⟩

end VariationalNotes.Ch04
