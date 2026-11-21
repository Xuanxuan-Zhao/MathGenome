import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.FenchelMoreau
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolarsBipolar
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Tactic.Linarith

noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis

def subdifferential {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) : Set (X →L[ℝ] ℝ) := Specs.subdifferential f x

def pairingSubdifferential {X : Type u} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] (g : (X →L[ℝ] ℝ) → EReal) (y : X →L[ℝ] ℝ) : Set X :=
  Specs.pairingSubdifferential g y

section Basic
variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- Unpack the support inequality using a specified finite value. -/
theorem mem_subdifferential_iff {f : X → WithTop ℝ} {x : X} {r : ℝ}
    (hx : f x = (r : WithTop ℝ)) (y : X →L[ℝ] ℝ) :
    y ∈ subdifferential f x ↔ ∀ z, ((r + y (z - x) : ℝ) : WithTop ℝ) ≤ f z := by
  constructor
  · rintro ⟨s, hs, h⟩
    have hsr : s = r := WithTop.coe_injective (hs.symm.trans hx)
    simpa [hsr] using h
  · intro h
    exact ⟨r, hx, h⟩

theorem subdifferential_eq_empty_of_top : Specs.subdifferential_eq_empty_of_top.{u} := by
  intro X _ _ _ f x hx
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨r, hr, _⟩
  exact WithTop.coe_ne_top (hr.symm.trans hx)

theorem pairingSubdifferential_eq_empty_of_infinite :
    Specs.pairingSubdifferential_eq_empty_of_infinite.{u} := by
  intro X _ _ _ g y hy
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨s, hs, _⟩
  rcases hy with ht | hb
  · exact EReal.coe_ne_top s (hs.symm.trans ht)
  · exact EReal.coe_ne_bot s (hs.symm.trans hb)

theorem minimizes_iff_zero_mem_subdifferential :
    Specs.minimizes_iff_zero_mem_subdifferential.{u} := by
  intro X _ _ _ f _ _ x hx
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
  change (∀ z, f x ≤ f z) ↔ (0 : X →L[ℝ] ℝ) ∈ subdifferential f x
  rw [mem_subdifferential_iff hr]
  simp [hr]

theorem subdifferential_indicator : Specs.subdifferential_indicator.{u} := by
  intro X _ _ _ C _ _ x hx
  classical
  have hix : indicator C x = ((0 : ℝ) : WithTop ℝ) := by
    simp [indicator, Specs.indicator, hx]
  ext y
  change y ∈ subdifferential (indicator C) x ↔ ∀ z ∈ C, y (z - x) ≤ 0
  rw [mem_subdifferential_iff hix]
  constructor
  · intro h z hz
    have h' : ((0 + y (z - x) : ℝ) : WithTop ℝ) ≤ ((0 : ℝ) : WithTop ℝ) := by
      simpa only [indicator, Specs.indicator, ite_eq_left hz, WithTop.coe_zero] using h z
    simpa only [zero_add] using WithTop.coe_le_coe.mp h'
  · intro h z
    by_cases hz : z ∈ C
    · rw [indicator, Specs.indicator, ite_eq_left hz]
      exact WithTop.coe_le_coe.mpr (by simpa only [zero_add] using h z hz)
    · simp [indicator, Specs.indicator, hz]

/-- The supporting slope makes the defining supremum attain its value at x. -/
theorem subgradient_iff_conjugate_eq {f : X → WithTop ℝ} {x : X} {r : ℝ}
    (hx : f x = (r : WithTop ℝ)) (y : X →L[ℝ] ℝ) :
    y ∈ subdifferential f x ↔ conjugate f y = ((y x - r : ℝ) : EReal) := by
  rw [mem_subdifferential_iff hx]
  constructor
  · intro h
    apply le_antisymm
    · change Specs.conjugate f y ≤ _
      apply iSup₂_le
      intro z hz
      obtain ⟨s, hs⟩ := (mem_domain_iff f z).mp hz
      have hz' : r + (y z - y x) ≤ s := by
        have hh : ((r + y (z - x) : ℝ) : WithTop ℝ) ≤ (s : WithTop ℝ) := hs ▸ h z
        simpa only [map_sub] using WithTop.coe_le_coe.mp hh
      simp only [hs, WithTop.untopD_coe]
      apply EReal.coe_le_coe_iff.mpr
      linarith
    · exact conjugate_finite_lower_bound f x r hx y
  · intro hy z
    induction hz : f z using WithTop.recTopCoe with
    | top => exact le_top
    | coe s =>
      have h := conjugate_finite_lower_bound f z s hz y
      rw [show Specs.conjugate f y = ((y x - r : ℝ) : EReal) from hy] at h
      have h' := EReal.coe_le_coe_iff.mp h
      apply WithTop.coe_le_coe.mpr
      rw [map_sub]
      linarith

theorem subgradient_iff_fenchel_equality : Specs.subgradient_iff_fenchel_equality.{u} := by
  intro X _ _ _ f x hx y
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
  change y ∈ subdifferential f x ↔ _
  rw [subgradient_iff_conjugate_eq hr]
  rw [hr]
  change conjugate f y = ((y x - r : ℝ) : EReal) ↔
    (r : EReal) + conjugate f y = (y x : EReal)
  constructor
  · intro h
    rw [h, ← EReal.coe_add]
    congr 1
    ring
  · intro h
    apply le_antisymm
    · apply (EReal.addLECancellable_coe r).add_le_add_iff_left.mp
      rw [h, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · apply (EReal.addLECancellable_coe r).add_le_add_iff_left.mp
      rw [h, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)

end Basic

/-- Fenchel–Moreau supplies the reverse support inequality in the original
X–X′ pairing. No reflexivity or existence of subgradients is assumed. -/
theorem subgradient_iff_pairing_subgradient :
    Specs.subgradient_iff_pairing_subgradient.{u} := by
  intro X _ _ _ _ _ _ _ f hp hc hl x hx y
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
  change y ∈ subdifferential f x ↔ x ∈ pairingSubdifferential (conjugate f) y
  rw [subgradient_iff_conjugate_eq hr]
  constructor
  · intro hy
    refine ⟨y x - r, hy, ?_⟩
    intro v
    have h := conjugate_finite_lower_bound f x r hr v
    change ((y x - r + (v - y) x : ℝ) : EReal) ≤ conjugate f v
    rw [sub_apply]
    convert h using 1
    · congr 1
      ring
    · rfl
  · rintro ⟨s, hs, h⟩
    have hbi : biconjugate f x ≤ ((y x - s : ℝ) : EReal) := by
      apply iSup_le
      intro v
      apply (EReal.sub_le_iff_le_add
        (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))).mpr
      have hv := add_le_add (le_refl ((y x - s : ℝ) : EReal)) (h v)
      change ((y x - s : ℝ) : EReal) + ((s + (v - y) x : ℝ) : EReal) ≤
        ((y x - s : ℝ) : EReal) + conjugate f v at hv
      rw [← EReal.coe_add, sub_apply] at hv
      convert hv using 1
      · congr 1
        ring
      · rfl
    have hfm := fenchel_moreau f hp hc hl x
    have hrbound : r ≤ y x - s := by
      rw [← show Specs.biconjugate f x = biconjugate f x from rfl] at hbi
      rw [← hfm, hr] at hbi
      exact EReal.coe_le_coe_iff.mp hbi
    have hlow := conjugate_finite_lower_bound f x r hr y
    rw [show Specs.conjugate f y = (s : EReal) from hs] at hlow
    have hlow' := EReal.coe_le_coe_iff.mp hlow
    rw [hs]
    congr 1
    linarith

end VariationalNotes.ConvexAnalysis
