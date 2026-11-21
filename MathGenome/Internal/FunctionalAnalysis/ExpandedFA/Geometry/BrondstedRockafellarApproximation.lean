import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.BrondstedRockafellarApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.EpsilonSubgradient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Ekeland
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelRockafellar

namespace ExpandedFA.Geometry.BrondstedRockafellarApproximation

open Set Filter
open scoped Topology
open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates
open ExpandedFA.BanachConvex

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- The source's closed real-sublevel condition is ordinary lower
semicontinuity after inclusion in the full extended real line. -/
lemma lowerSemicontinuous_extendedRealValue (φ : ExtendedFunction X)
    (hφ : ExpandedFA.P1.ExtendedConvexFunctions.LowerSemicontinuous X φ) :
    _root_.LowerSemicontinuous (fun x => extendedRealValue (φ x)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  induction a with
  | bot =>
    have he : (fun x => extendedRealValue (φ x)) ⁻¹' Iic ⊥ = ∅ := by
      ext x
      change ((φ x : WithBot (WithTop ℝ)) ≤ ⊥) ↔ False
      exact iff_false_intro (WithBot.not_coe_le_bot _)
    rw [he]
    exact isClosed_empty
  | coe r =>
    have he : (fun x => extendedRealValue (φ x)) ⁻¹' Iic (r : EReal) =
        {x | φ x ≤ (r : WithTop ℝ)} := by
      ext x
      change ((φ x : WithBot (WithTop ℝ)) ≤ ((r : WithTop ℝ) : WithBot (WithTop ℝ))) ↔ _
      exact WithBot.coe_le_coe
    rw [he]
    exact hφ r
  | top => simp

/-- Tilting by a continuous linear functional preserves lower semicontinuity. -/
lemma lowerSemicontinuous_tilt (φ : ExtendedFunction X)
    (hφ : ExpandedFA.P1.ExtendedConvexFunctions.LowerSemicontinuous X φ)
    (f : X →L[ℝ] ℝ) :
    _root_.LowerSemicontinuous (fun x => extendedRealValue (φ x) - (f x : EReal)) := by
  have hc : Continuous (fun x => ((-f x : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp f.continuous.neg
  simp only [EReal.coe_neg] at hc
  exact (lowerSemicontinuous_extendedRealValue φ hφ).add' hc.lowerSemicontinuous
    (fun x => EReal.continuousAt_add
      (Or.inr (by simp)) (Or.inl WithBot.coe_ne_bot))

/-- Separation at a minimizer of the norm-penalized, tilted function
produces an exact subgradient within the penalty coefficient of the tilt. -/
lemma exists_subgradient_of_penalized_min (φ : ExtendedFunction X)
    (hc : ExtendedConvex X φ) (z : X) (r : ℝ) (hz : φ z = (r : WithTop ℝ))
    (f₀ : X →L[ℝ] ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hmin : ∀ (y : X) (s : ℝ), φ y = (s : WithTop ℝ) →
      r - f₀ z ≤ s - f₀ y + k * ‖y - z‖) :
    ∃ f₁ : X →L[ℝ] ℝ, f₁ ∈ subdifferential X φ z ∧ ‖f₁ - f₀‖ ≤ k := by
  let p : X → ℝ := fun y => k * ‖y - z‖ - f₀ y
  let ψ : ExtendedFunction X := fun y => (p y : WithTop ℝ)
  have hpconv : ExtendedConvex X ψ := by
    intro x y r' s' a b hx hy ha hb hab
    have hr : p x = r' := WithTop.coe_inj.mp hx
    have hs : p y = s' := WithTop.coe_inj.mp hy
    change ((p (a • x + b • y) : ℝ) : WithTop ℝ) ≤ _
    apply WithTop.coe_le_coe.mpr
    rw [← hr, ← hs]
    have he : a • x + b • y - z = a • (x - z) + b • (y - z) := by
      symm
      calc
        a • (x - z) + b • (y - z) = a • x + b • y - (a • z + b • z) := by
          rw [smul_sub, smul_sub]
          abel
        _ = a • x + b • y - z := by rw [← add_smul, hab, one_smul]
    have hn : ‖a • x + b • y - z‖ ≤ a * ‖x - z‖ + b * ‖y - z‖ := by
      rw [he]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
        using norm_add_le (a • (x - z)) (b • (y - z))
    have hmul := mul_le_mul_of_nonneg_left hn hk
    dsimp [p]
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith only [hmul]
  have hpcont : ContinuousAt ψ z :=
    (WithTop.continuous_coe.comp
      ((continuous_const.mul (continuous_id.sub continuous_const).norm).sub f₀.continuous)).continuousAt
  have hpz : ψ z = ((-f₀ z : ℝ) : WithTop ℝ) := by simp [ψ, p]
  have hbound : ∀ (y : X) (r' s' : ℝ), ψ y = (r' : WithTop ℝ) →
      φ y = (s' : WithTop ℝ) → r - f₀ z ≤ r' + s' := by
    intro y r' s' hp hy
    have hp' : p y = r' := WithTop.coe_inj.mp hp
    have hh := hmin y s' hy
    dsimp [p] at hp'
    linarith
  obtain ⟨g, c, hp, hφ⟩ :=
    ExpandedFA.P1.FenchelRockafellar.affine_minorants_of_lower_bound ψ φ hpconv hc
      z (-f₀ z) r hpz hz hpcont (r - f₀ z) hbound
  have hgz : g z + c = -f₀ z := by
    have h₁ := hp z
    have h₂ := hφ z
    rw [hpz, WithTop.coe_le_coe] at h₁
    rw [hz, WithTop.coe_le_coe] at h₂
    linarith
  have hupper (v : X) : g v + f₀ v ≤ k * ‖v‖ := by
    have hh := hp (z + v)
    change ((g (z + v) + c : ℝ) : WithTop ℝ) ≤ (p (z + v) : WithTop ℝ) at hh
    rw [WithTop.coe_le_coe] at hh
    dsimp [p] at hh
    simp only [add_sub_cancel_left, map_add] at hh
    linarith
  refine ⟨-g, ?_, ?_⟩
  · apply (mem_subdifferential_iff_of_value φ z r hz (-g)).mpr
    intro y s hy
    have hh := hφ y
    rw [hy, WithTop.coe_le_coe] at hh
    simp only [neg_apply, map_sub]
    linarith
  · apply (-g - f₀).opNorm_le_bound hk
    intro v
    have hu := hupper v
    have hl := hupper (-v)
    simp only [map_neg, norm_neg] at hl
    rw [Real.norm_eq_abs, abs_le]
    simp only [sub_apply, neg_apply]
    exact ⟨by linarith, by linarith⟩

/-- Brøndsted–Rockafellar approximation, with the source's constants. -/
theorem brondsted_rockafellar_approximation : Spec.Approximation.{u} := by
  intro X _ _ _ φ _hproper hlsc hconv x₀ f₀ ε hε hf₀ k hk
  change f₀ ∈ EpsilonSubgradient.epsilonSubdifferential X φ ε x₀ at hf₀
  obtain ⟨r₀, hr₀⟩ := WithTop.ne_top_iff_exists.mp hf₀.1
  have hsupport := (EpsilonSubgradient.mem_epsilonSubdifferential_iff_of_value
    φ ε x₀ r₀ hr₀.symm f₀).mp hf₀
  let F : X → EReal := fun x => extendedRealValue (φ x) - (f₀ x : EReal)
  have hF (x : X) (r : ℝ) (hx : φ x = (r : WithTop ℝ)) :
      F x = ((r - f₀ x : ℝ) : EReal) := by
    dsimp [F]
    rw [hx]
    rfl
  have hFtop (x : X) (hx : φ x = ⊤) : F x = ⊤ := by
    dsimp [F]
    rw [hx]
    exact EReal.top_sub_coe _
  have hF₀ : F x₀ = ((r₀ - f₀ x₀ : ℝ) : EReal) := hF x₀ r₀ hr₀.symm
  have hbound (y : X) : ((r₀ - f₀ x₀ - ε : ℝ) : EReal) ≤ F y := by
    by_cases hy : φ y = ⊤
    · rw [hFtop y hy]
      exact le_top
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      rw [hF y s hs.symm, EReal.coe_le_coe_iff]
      have hh := hsupport y s hs.symm
      rw [map_sub] at hh
      linarith
  have hinf : ((r₀ - f₀ x₀ - ε : ℝ) : EReal) ≤ ⨅ x, F x := le_iInf hbound
  have hnear : F x₀ ≤ (⨅ x, F x) + ((k * (ε / k) : ℝ) : EReal) := by
    have hprod : k * (ε / k) = ε := by field_simp
    rw [hprod]
    calc
      F x₀ = ((r₀ - f₀ x₀ - ε : ℝ) : EReal) + (ε : EReal) := by
        rw [hF₀, ← EReal.coe_add, sub_add_cancel]
      _ ≤ (⨅ x, F x) + (ε : EReal) := add_le_add hinf le_rfl
  obtain ⟨z, hdist, hzle, hstrict⟩ := ExpandedFA.P1.ekeland F
    (lowerSemicontinuous_tilt φ hlsc f₀) ⟨r₀ - f₀ x₀ - ε, hbound⟩
    ⟨x₀, by rw [hF₀]; exact EReal.coe_ne_top _⟩
    x₀ k (ε / k) hk (div_pos hε hk) hnear
  have hzfinite : φ z ≠ ⊤ := by
    intro hz
    rw [hFtop z hz, hF₀] at hzle
    exact (not_le_of_gt (EReal.coe_lt_top _)) hzle
  obtain ⟨r₁, hr₁⟩ := WithTop.ne_top_iff_exists.mp hzfinite
  have hmin : ∀ (y : X) (s : ℝ), φ y = (s : WithTop ℝ) →
      r₁ - f₀ z ≤ s - f₀ y + k * ‖y - z‖ := by
    intro y s hy
    by_cases heq : y = z
    · subst y
      have hs : s = r₁ := WithTop.coe_inj.mp (hy.symm.trans hr₁.symm)
      simp [hs]
    · have hh := hstrict y heq
      rw [hF z r₁ hr₁.symm, hF y s hy, ← EReal.coe_sub, EReal.coe_lt_coe_iff,
        dist_eq_norm] at hh
      linarith
  obtain ⟨f₁, hf₁, hnorm⟩ :=
    exists_subgradient_of_penalized_min φ hconv z r₁ hr₁.symm f₀ k hk.le hmin
  exact ⟨z, f₁, hf₁, by simpa only [dist_eq_norm] using hdist, hnorm⟩

end ExpandedFA.Geometry.BrondstedRockafellarApproximation
