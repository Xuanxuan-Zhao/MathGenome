import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.GateauxSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.GateauxNormDerivative
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BidualClosedImage

namespace ExpandedFA.P1.GateauxSmoothness

open Set
universe u v

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The native strict convexity predicate is exactly the manuscript's
strict midpoint inequality on distinct unit vectors. -/
lemma strictlyConvex_iff_midpoint : Spec.StrictlyConvex 𝕜 E ↔
    ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y →
      ‖((1 / 2 : ℝ) : 𝕜) • (x + y)‖ < 1 := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  constructor
  · intro hs
    letI : StrictConvexSpace ℝ E := hs
    intro x y hx hy hne
    change ‖(1 / 2 : ℝ) • (x + y)‖ < 1
    simpa [hx] using (norm_midpoint_lt_iff (hx.trans hy.symm)).2 hne
  · intro hm
    apply StrictConvexSpace.of_norm_add_ne_two
    intro x y hx hy hne he
    have h := hm x y hx hy hne
    rw [norm_smul, RCLike.norm_ofReal, he] at h
    norm_num at h

/-- Unit norming sets are singletons exactly when they have a unique member. -/
lemma smoothAt_iff_unique (x : E) :
    SmoothnessDefinitions.Spec.SmoothAtValue 𝕜 x ↔
      ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = 1 ∧
        ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = 1 → g = f := by
  change (∃ f, {g : E →L[𝕜] 𝕜 | ‖g‖ = 1 ∧ g x = 1} = {f}) ↔ _
  constructor
  · rintro ⟨f, hf⟩
    have hff : ‖f‖ = 1 ∧ f x = 1 := by
      change f ∈ {g : E →L[𝕜] 𝕜 | ‖g‖ = 1 ∧ g x = 1}
      rw [hf]; exact mem_singleton f
    exact ⟨f, hff.1, hff.2, fun g hg hgx => by
      have : g ∈ {f} := hf ▸ (show g ∈ {g : E →L[𝕜] 𝕜 |
        ‖g‖ = 1 ∧ g x = 1} from ⟨hg, hgx⟩)
      exact mem_singleton_iff.mp this⟩
  · rintro ⟨f, hf, hfx, hu⟩
    refine ⟨f, Set.ext fun g => ?_⟩
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hg => hu g hg.1 hg.2, fun he => he ▸ ⟨hf, hfx⟩⟩

/-- A scalar in the closed unit disk whose real part is one is actually one. -/
lemma eq_one_of_re_eq_one {a : 𝕜} (hn : ‖a‖ ≤ 1) (hr : RCLike.re a = 1) : a = 1 := by
  have he := RCLike.re_eq_self_of_le (hn.trans hr.ge)
  simpa [hr] using he.symm

/-- If a unit functional norms a sum of two unit vectors of norm two,
it takes the value one on each vector, also over the complex field. -/
lemma support_sum (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (f : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1) (hfxy : f (x + y) = (2 : 𝕜)) :
    f x = 1 ∧ f y = 1 := by
  have hnx : ‖f x‖ ≤ 1 := by simpa [hf, hx] using f.le_opNorm x
  have hny : ‖f y‖ ≤ 1 := by simpa [hf, hy] using f.le_opNorm y
  have hr := congrArg RCLike.re hfxy
  simp only [map_add, RCLike.ofNat_re] at hr
  have hrx := (RCLike.re_le_norm (f x)).trans hnx
  have hry := (RCLike.re_le_norm (f y)).trans hny
  exact ⟨eq_one_of_re_eq_one hnx (by linarith),
    eq_one_of_re_eq_one hny (by linarith)⟩

/-- Two unit vectors sharing a unit support coincide in a strictly convex space. -/
lemma eq_of_common_support (hs : Spec.StrictlyConvex 𝕜 E) (x y : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (f : E →L[𝕜] 𝕜)
    (hf : ‖f‖ = 1) (hfx : f x = 1) (hfy : f y = 1) : x = y := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : StrictConvexSpace ℝ E := hs
  apply eq_of_norm_eq_of_norm_add_eq (hx.trans hy.symm)
  have hlo := f.le_opNorm (x + y)
  have hhi := norm_add_le x y
  norm_num [map_add, hf, hfx, hfy, hx, hy] at hlo hhi ⊢
  exact le_antisymm hhi hlo

theorem smooth_iff_gateaux : Spec.Characterization.{u,v} :=
  GateauxNormDerivative.smooth_iff_gateaux

theorem unit_derivative_formula : Spec.UnitDerivativeFormula.{u,v} :=
  GateauxNormDerivative.unit_derivative_formula

/-- Strict convexity of the scalar-linear dual forces unique support. -/
theorem strict_dual_implies_smooth : Spec.StrictDualImpliesSmooth.{u,v} := by
  intro 𝕜 E _ _ _ hs x hx
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional_nonzero 𝕜 E x hx0
  have hfx1 : f x = 1 := by simpa [hx] using hfx
  apply (smoothAt_iff_unique x).2
  refine ⟨f, hf, hfx1, ?_⟩
  intro g hg hgx
  exact eq_of_common_support hs g f hg hf
    (C04CanonicalMap.canonicalEvaluation 𝕜 E x)
    (by simpa [hx] using BidualClosedImage.canonicalEvaluation_norm 𝕜 E x) hgx hfx1

/-- Smoothness of the dual separates the canonical images of unit vectors. -/
theorem smooth_dual_implies_strict : Spec.SmoothDualImpliesStrict.{u,v} := by
  intro 𝕜 E _ _ _ hs
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hne hxy
  have hxy0 : x + y ≠ 0 := by intro he; simp [he] at hxy
  obtain ⟨f, hf, hfxy⟩ := C05Norming.norming_functional_nonzero 𝕜 E (x + y) hxy0
  have hv := support_sum x y hx hy f hf (by simpa only [hxy, RCLike.ofReal_ofNat] using hfxy)
  obtain ⟨Φ, _, _, hu⟩ := (smoothAt_iff_unique f).1 (hs f hf)
  have hJx := hu (C04CanonicalMap.canonicalEvaluation 𝕜 E x)
    (by simpa [hx] using BidualClosedImage.canonicalEvaluation_norm 𝕜 E x) hv.1
  have hJy := hu (C04CanonicalMap.canonicalEvaluation 𝕜 E y)
    (by simpa [hy] using BidualClosedImage.canonicalEvaluation_norm 𝕜 E y) hv.2
  exact hne ((BidualClosedImage.canonicalEvaluation_isometry 𝕜 E).injective (hJx.trans hJy.symm))

/-- In a reflexive space a support of two dual vectors comes from a primal vector. -/
theorem reflexive_smooth_implies_strict_dual : Spec.ReflexiveSmoothImpliesStrictDual.{u,v} := by
  intro 𝕜 E _ _ _ hr hs
  letI : NormedSpace ℝ (E →L[𝕜] 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 _
  apply StrictConvexSpace.of_norm_add_ne_two
  intro f g hf hg hne hfg
  have hfg0 : f + g ≠ 0 := by intro he; simp [he] at hfg
  obtain ⟨Φ, hΦ, hΦfg⟩ := C05Norming.norming_functional_nonzero 𝕜 (E →L[𝕜] 𝕜) (f + g) hfg0
  have hv := support_sum f g hf hg Φ hΦ (by simpa only [hfg, RCLike.ofReal_ofNat] using hΦfg)
  obtain ⟨x, hxΦ⟩ := hr Φ
  change C04CanonicalMap.canonicalEvaluation 𝕜 E x = Φ at hxΦ
  have hx : ‖x‖ = 1 := by
    rw [← BidualClosedImage.canonicalEvaluation_norm 𝕜 E x, hxΦ, hΦ]
  obtain ⟨k, _, _, hu⟩ := (smoothAt_iff_unique x).1 (hs x hx)
  have hfx : f x = 1 := by simpa [← hxΦ] using hv.1
  have hgx : g x = 1 := by simpa [← hxΦ] using hv.2
  exact hne ((hu f hf hfx).trans (hu g hg hgx).symm)

/-- Reflexivity turns every bidual norming functional into a unit primal vector. -/
theorem reflexive_strict_implies_smooth_dual : Spec.ReflexiveStrictImpliesSmoothDual.{u,v} := by
  intro 𝕜 E _ _ _ hr hs f hf
  have hf0 : f ≠ 0 := by intro he; simp [he] at hf
  obtain ⟨Φ, hΦ, hΦf⟩ := C05Norming.norming_functional_nonzero 𝕜 (E →L[𝕜] 𝕜) f hf0
  apply (smoothAt_iff_unique f).2
  refine ⟨Φ, hΦ, by simpa [hf] using hΦf, ?_⟩
  intro Ψ hΨ hΨf
  obtain ⟨x, hxΦ⟩ := hr Φ
  obtain ⟨y, hyΨ⟩ := hr Ψ
  change C04CanonicalMap.canonicalEvaluation 𝕜 E x = Φ at hxΦ
  change C04CanonicalMap.canonicalEvaluation 𝕜 E y = Ψ at hyΨ
  have hx : ‖x‖ = 1 := by
    rw [← BidualClosedImage.canonicalEvaluation_norm 𝕜 E x, hxΦ, hΦ]
  have hy : ‖y‖ = 1 := by
    rw [← BidualClosedImage.canonicalEvaluation_norm 𝕜 E y, hyΨ, hΨ]
  have hfx : f x = 1 := by simpa [← hxΦ, hf] using hΦf
  have hfy : f y = 1 := by simpa [← hyΨ] using hΨf
  have he := eq_of_common_support hs x y hx hy f hf hfx hfy
  rw [← hyΨ, ← hxΦ, he]

end ExpandedFA.P1.GateauxSmoothness
