import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FenchelMoreauLcs
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LcsStrongSeparation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Fenchel–Moreau for the given real Hausdorff locally convex topology.

Separate a point below the closed convex real epigraph. Splitting the continuous
linear separator gives a nonnegative vertical coefficient. At a finite domain
point this coefficient is positive and yields an initial affine minorant.
Adding a small multiple of its epigraph inequality makes any separator's
vertical coefficient positive, preserving the strict gap. Thus affine minorants
approximate every primal value from below, including +∞. Conjugation then gives
the asserted equality using suprema in the full extended real line.
-/
noncomputable section
namespace ExpandedFA.P1.FenchelMoreauLcs

open Set ExtendedConvexFunctions
open C06Conjugates (extendedRealValue)

/-- Conjugation over the continuous real-linear dual of the given topology. -/
def convexConjugate (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (φ : ExtendedFunction E) (f : E →L[ℝ] ℝ) : EReal :=
  ⨆ x, (f x : EReal) - extendedRealValue (φ x)

/-- Biconjugation with the same dual and extended-real conventions. -/
def convexBiconjugate (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (φ : ExtendedFunction E) (x : E) : EReal :=
  ⨆ f : E →L[ℝ] ℝ, (f x : EReal) - convexConjugate E φ f

theorem convexConjugate_normed_agreement : Spec.NormedConjugateAgreement := by
  intro E _ _ φ f
  rfl

theorem convexBiconjugate_normed_agreement : Spec.NormedBiconjugateAgreement := by
  intro E _ _ φ x
  rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A finite upper bound on the conjugate is precisely a bound at every
finite domain point. Infinite primal values impose no constraint. -/
theorem convexConjugate_le_real_iff (φ : ExtendedFunction E)
    (f : E →L[ℝ] ℝ) (r : ℝ) :
    convexConjugate E φ f ≤ (r : EReal) ↔
      ∀ (x : E) (s : ℝ), φ x = (s : WithTop ℝ) → f x - s ≤ r := by
  unfold convexConjugate
  rw [iSup_le_iff]
  constructor
  · intro h x s hs
    have hx := h x
    rw [hs] at hx
    exact EReal.coe_le_coe_iff.mp hx
  · intro h x
    by_cases hx : φ x = ⊤
    · rw [hx]
      change (f x : EReal) - ⊤ ≤ (r : EReal)
      rw [EReal.sub_top]
      exact bot_le
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hx
      rw [← hs]
      exact EReal.coe_le_coe_iff.mpr (h x s hs.symm)

theorem convexConjugate_ne_bot (φ : ExtendedFunction E) (hp : Proper E φ)
    (f : E →L[ℝ] ℝ) : convexConjugate E φ f ≠ ⊥ := by
  obtain ⟨x, r, hr⟩ := (proper_iff_finite_value E φ).mp hp
  have hle : ((f x - r : ℝ) : EReal) ≤ convexConjugate E φ f := by
    calc
      ((f x - r : ℝ) : EReal) = (f x : EReal) - extendedRealValue (φ x) := by
        rw [hr]
        rfl
      _ ≤ convexConjugate E φ f :=
        le_iSup (fun y : E => (f y : EReal) - extendedRealValue (φ y)) x
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle

theorem fenchel_inequality (φ : ExtendedFunction E) (hp : Proper E φ)
    (x : E) (f : E →L[ℝ] ℝ) :
    (f x : EReal) ≤ extendedRealValue (φ x) + convexConjugate E φ f := by
  have h := le_iSup (fun y => (f y : EReal) - extendedRealValue (φ y)) x
  rw [add_comm]
  exact (EReal.sub_le_iff_le_add
    (Or.inl (C06Conjugates.extendedRealValue_conventions.2.2.1 (φ x)))
    (Or.inr (convexConjugate_ne_bot φ hp f))).mp h

section LocallyConvex

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ E]

/-- Split an epigraph separator into its horizontal and vertical parts.
Upward closure forces the vertical coefficient to be nonnegative. -/
lemma epigraph_separator (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ)
    (x : E) (t : ℝ) (ht : (t : WithTop ℝ) < φ x) :
    ∃ (ℓ : E →L[ℝ] ℝ) (b α : ℝ), 0 ≤ b ∧ ℓ x + b * t < α ∧
      ∀ (y : E) (s : ℝ), φ y ≤ (s : WithTop ℝ) → α ≤ ℓ y + b * s := by
  obtain ⟨x₁, r₁, hr₁⟩ := (proper_iff_finite_value E φ).mp hp
  have hne : (realEpigraph E φ).Nonempty := ⟨(x₁, r₁), hr₁.le⟩
  have hclosed := (lowerSemicontinuous_iff_closed_epigraph E φ).mp hl
  have hconv := (convex_iff_convex_epigraph E φ).mp hc
  obtain ⟨f, _, hbd, hlt⟩ := C06.real_locally_convex_point_strong_separation
    (realEpigraph E φ) (x, t) hne hclosed hconv (not_le_of_gt ht)
  let L : (E × ℝ) →L[ℝ] ℝ := -f
  let ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := L (0, 1)
  let α : ℝ := -sSup (f '' realEpigraph E φ)
  have hsplit (y : E) (s : ℝ) : L (y, s) = ℓ y + b * s := by
    have heq : (y, s) = (y, 0) + s • (0, (1 : ℝ)) := by ext <;> simp
    rw [heq, map_add, map_smul]
    simp [ℓ, b, mul_comm]
  have hsep (y : E) (s : ℝ) (hs : φ y ≤ (s : WithTop ℝ)) : α ≤ ℓ y + b * s := by
    rw [← hsplit]
    exact neg_le_neg (le_csSup hbd ⟨(y, s), hs, rfl⟩)
  have hgap : ℓ x + b * t < α := by
    rw [← hsplit]
    exact neg_lt_neg hlt
  have hb : 0 ≤ b := by
    by_contra hn
    have hbneg : b < 0 := lt_of_not_ge hn
    let d : ℝ := ℓ x₁ + b * r₁ - α
    have hd : 0 ≤ d := by dsimp [d]; linarith [hsep x₁ r₁ hr₁.le]
    let k : ℝ := (d + 1) / (-b)
    have hk : 0 < k := div_pos (by linarith) (neg_pos.mpr hbneg)
    have hbk : b * k = -(d + 1) := by
      dsimp [k]
      field_simp [hbneg.ne]
    have hs : φ x₁ ≤ ((r₁ + k : ℝ) : WithTop ℝ) :=
      hr₁.le.trans (WithTop.coe_le_coe.mpr (by linarith))
    have hh := hsep x₁ (r₁ + k) hs
    dsimp [d] at hbk
    nlinarith
  exact ⟨ℓ, b, α, hb, hgap, hsep⟩

/-- A finite domain point ensures the existence of an initial affine minorant. -/
theorem exists_continuous_affine_minorant (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ) :
    ∃ (h : E →L[ℝ] ℝ) (c : ℝ), ∀ y, ((h y + c : ℝ) : WithTop ℝ) ≤ φ y := by
  obtain ⟨x₁, r₁, hr₁⟩ := (proper_iff_finite_value E φ).mp hp
  obtain ⟨ℓ, b, α, hb, hgap, hsep⟩ := epigraph_separator φ hp hc hl x₁ (r₁ - 1)
    (by rw [hr₁]; exact WithTop.coe_lt_coe.mpr (by linarith))
  have hbpos : 0 < b := by
    have hh := hsep x₁ r₁ hr₁.le
    nlinarith
  refine ⟨(-b⁻¹) • ℓ, α / b, ?_⟩
  intro y
  by_cases hy : φ y = ⊤
  · simp [hy]
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← hs]
    apply WithTop.coe_le_coe.mpr
    have hh := hsep y s hs.ge
    change (-b⁻¹) * ℓ y + α / b ≤ s
    have heq : -b⁻¹ * ℓ y + α / b = (α - ℓ y) / b := by
      simp only [div_eq_mul_inv]; ring
    rw [heq]
    exact (div_le_iff₀ hbpos).mpr (by linarith)

/-- Affine minorants strictly exceed any real level below the primal value.
The initial minorant removes the possible zero vertical coefficient. -/
theorem continuous_affine_minorant_above (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ)
    (x : E) (t : ℝ) (ht : (t : WithTop ℝ) < φ x) :
    ∃ (h : E →L[ℝ] ℝ) (c : ℝ),
      (∀ y, ((h y + c : ℝ) : WithTop ℝ) ≤ φ y) ∧ t < h x + c := by
  obtain ⟨h₀, c₀, hm₀⟩ := exists_continuous_affine_minorant φ hp hc hl
  obtain ⟨ℓ, b, α, hb, hgap, hsep⟩ := epigraph_separator φ hp hc hl x t ht
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt
    (show 0 < α - (ℓ x + b * t) by linarith) (t - (h₀ x + c₀))
  let B : ℝ := b + ε
  have hB : 0 < B := by dsimp [B]; linarith
  let h : E →L[ℝ] ℝ := B⁻¹ • (ε • h₀ - ℓ)
  let c : ℝ := (α + ε * c₀) / B
  have heval (y : E) : h y + c = (α + ε * c₀ - ℓ y + ε * h₀ y) / B := by
    simp only [h, c, smul_apply, sub_apply,
      smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨h, c, ?_, ?_⟩
  · intro y
    by_cases hy : φ y = ⊤
    · simp [hy]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      rw [← hs]
      apply WithTop.coe_le_coe.mpr
      rw [heval]
      apply (div_le_iff₀ hB).mpr
      have hm : h₀ y + c₀ ≤ s := WithTop.coe_le_coe.mp (by simpa [hs] using hm₀ y)
      have hh := hsep y s hs.ge
      dsimp [B]
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hm)]
  · rw [heval]
    apply (lt_div_iff₀ hB).mpr
    dsimp [B]
    nlinarith

/-- Fenchel–Moreau, with no normability or completeness assumption. -/
theorem fenchel_moreau : Spec.FenchelMoreau := by
  intro E _ _ _ _ _ _ _ φ hp hc hl x
  change convexBiconjugate E φ x = extendedRealValue (φ x)
  apply le_antisymm
  · unfold convexBiconjugate
    apply iSup_le
    intro f
    exact EReal.sub_le_of_le_add (fenchel_inequality φ hp x f)
  · by_contra hn
    obtain ⟨t, hbt, htf⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have ht : (t : WithTop ℝ) < φ x := WithBot.coe_lt_coe.mp htf
    obtain ⟨h, c, hm, htc⟩ := continuous_affine_minorant_above φ hp hc hl x t ht
    have hbound : convexConjugate E φ h ≤ ((-c : ℝ) : EReal) := by
      rw [convexConjugate_le_real_iff]
      intro y s hs
      have hh : h y + c ≤ s := WithTop.coe_le_coe.mp (by simpa [hs] using hm y)
      linarith
    have hle : ((h x + c : ℝ) : EReal) ≤ convexBiconjugate E φ x := by
      calc
        ((h x + c : ℝ) : EReal) = (h x : EReal) - ((-c : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ (h x : EReal) - convexConjugate E φ h := EReal.sub_le_sub le_rfl hbound
        _ ≤ convexBiconjugate E φ x :=
          le_iSup (fun f : E →L[ℝ] ℝ => (f x : EReal) - convexConjugate E φ f) h
    exact (not_lt_of_ge hle) (hbt.trans (EReal.coe_lt_coe_iff.mpr htc))

end LocallyConvex
end ExpandedFA.P1.FenchelMoreauLcs
