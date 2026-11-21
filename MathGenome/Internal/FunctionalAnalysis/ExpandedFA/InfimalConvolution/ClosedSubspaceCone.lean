import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.ClosedSubspaceCone
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.BanachFullConeExactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.InfimalConvolution.ClosedSubspaceCone

open Set
open ExpandedFA.P1 ExtendedConvexFunctions
open Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translate the common finite point to zero in the subspace. -/
def translated (φ : ExtendedFunction E) (L : Submodule ℝ E) (x₀ : E) :
    ExtendedFunction L := fun z => φ (x₀ + (z : E))

/-- Both domains are contained in the same affine subspace. -/
lemma domains_in_affine_subspace (φ ψ : ExtendedFunction E) (L : Submodule ℝ E)
    (hc : domainDifferenceCone E φ ψ = (L : Set E))
    (x₀ : E) (hφ₀ : x₀ ∈ Definitions.finiteDomain E φ) (hψ₀ : x₀ ∈ Definitions.finiteDomain E ψ) :
    (∀ x ∈ Definitions.finiteDomain E φ, x - x₀ ∈ L) ∧
    (∀ y ∈ Definitions.finiteDomain E ψ, y - x₀ ∈ L) := by
  constructor
  · intro x hx
    change x - x₀ ∈ (L : Set E)
    rw [← hc]
    exact (mem_domainDifferenceCone E φ ψ _).mpr
      ⟨1, zero_le_one, x, x₀, hx, hψ₀, (one_smul ℝ _).symm⟩
  · intro y hy
    have hh : x₀ - y ∈ L := by
      change x₀ - y ∈ (L : Set E)
      rw [← hc]
      exact (mem_domainDifferenceCone E φ ψ _).mpr
        ⟨1, zero_le_one, x₀, y, hφ₀, hy, (one_smul ℝ _).symm⟩
    simpa only [neg_sub] using L.neg_mem hh

lemma translated_convex (φ : ExtendedFunction E) (L : Submodule ℝ E) (x₀ : E)
    (hc : ExtendedConvex E φ) : ExtendedConvex L (translated φ L x₀) := by
  intro x y r s a b hx hy ha hb hab
  have he : x₀ + ((a • x + b • y : L) : E) =
      a • (x₀ + (x : E)) + b • (x₀ + (y : E)) := by
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
    rw [add_add_add_comm, ← add_smul, hab, one_smul]
  change φ (x₀ + ((a • x + b • y : L) : E)) ≤ _
  rw [he]
  exact hc _ _ r s a b hx hy ha hb hab

lemma translated_lsc (φ : ExtendedFunction E) (L : Submodule ℝ E) (x₀ : E)
    (hl : LowerSemicontinuous E φ) : LowerSemicontinuous L (translated φ L x₀) := by
  intro r
  exact (hl r).preimage (continuous_const.add continuous_subtype_val)

lemma translated_full_cone (φ ψ : ExtendedFunction E) (L : Submodule ℝ E)
    (hc : domainDifferenceCone E φ ψ = (L : Set E))
    (x₀ : E) (hφ₀ : x₀ ∈ Definitions.finiteDomain E φ) (hψ₀ : x₀ ∈ Definitions.finiteDomain E ψ) :
    domainDifferenceCone L (translated φ L x₀) (translated ψ L x₀) = univ := by
  obtain ⟨hφ, hψ⟩ := domains_in_affine_subspace φ ψ L hc x₀ hφ₀ hψ₀
  apply eq_univ_of_forall
  intro z
  have hz : (z : E) ∈ domainDifferenceCone E φ ψ := by rw [hc]; exact z.property
  obtain ⟨a, ha, x, y, hx, hy, he⟩ := (mem_domainDifferenceCone E φ ψ _).mp hz
  apply (mem_domainDifferenceCone L _ _ z).mpr
  refine ⟨a, ha, ⟨x - x₀, hφ x hx⟩, ⟨y - x₀, hψ y hy⟩, ?_, ?_, ?_⟩
  · change φ (x₀ + (x - x₀)) ≠ ⊤
    have he : x₀ + (x - x₀) = x := by abel
    rw [he]
    exact hx
  · change ψ (x₀ + (y - x₀)) ≠ ⊤
    have he : x₀ + (y - x₀) = y := by abel
    rw [he]
    exact hy
  · apply Subtype.ext
    change (z : E) = a • ((x - x₀) - (y - x₀))
    simpa only [sub_sub_sub_cancel_right] using he

lemma translated_hypotheses (φ ψ : ExtendedFunction E) (L : Submodule ℝ E)
    (h : Spec.Hypotheses E φ ψ L) (x₀ : E)
    (hφ₀ : x₀ ∈ Definitions.finiteDomain E φ) (hψ₀ : x₀ ∈ Definitions.finiteDomain E ψ) :
    BanachFullConeExactness.Spec.Hypotheses L (translated φ L x₀) (translated ψ L x₀) := by
  have hφ : (0 : L) ∈ Definitions.finiteDomain L (translated φ L x₀) := by
    change φ (x₀ + (0 : E)) ≠ ⊤
    simpa only [add_zero] using (show φ x₀ ≠ ⊤ from hφ₀)
  have hψ : (0 : L) ∈ Definitions.finiteDomain L (translated ψ L x₀) := by
    change ψ (x₀ + (0 : E)) ≠ ⊤
    simpa only [add_zero] using (show ψ x₀ ≠ ⊤ from hψ₀)
  exact ⟨⟨0, hφ⟩, ⟨0, hψ⟩, translated_convex φ L x₀ h.2.2.1,
    translated_convex ψ L x₀ h.2.2.2.1, translated_lsc φ L x₀ h.2.2.2.2.1,
    translated_lsc ψ L x₀ h.2.2.2.2.2.1, ⟨0, hφ, hψ⟩,
    translated_full_cone φ ψ L h.2.2.2.2.2.2.2.2 x₀ hφ₀ hψ₀⟩

/-- Adding a finite real is an order isomorphism of the full extended line. -/
private def erealTranslate (a : ℝ) : EReal ≃o EReal where
  toFun := fun x => (a : EReal) + x
  invFun := fun x => ((-a : ℝ) : EReal) + x
  left_inv x := by
    change ((-a : ℝ) : EReal) + ((a : EReal) + x) = x
    rw [← add_assoc, ← EReal.coe_add]
    simp
  right_inv x := by
    change (a : EReal) + (((-a : ℝ) : EReal) + x) = x
    rw [← add_assoc, ← EReal.coe_add]
    simp
  map_rel_iff' := (EReal.addLECancellable_coe a).add_le_add_iff_left

/-- The conjugate translation/restriction identity holds at infinite values too. -/
lemma conjugate_translation (φ : ExtendedFunction E) (L : Submodule ℝ E) (x₀ : E)
    (hs : ∀ x ∈ Definitions.finiteDomain E φ, x - x₀ ∈ L) (f : E →L[ℝ] ℝ) :
    C06Conjugates.convexConjugate E φ f = (f x₀ : EReal) +
      C06Conjugates.convexConjugate L (translated φ L x₀) (f.comp L.subtypeL) := by
  have hshift (z : L) :
      (f (x₀ + (z : E)) : EReal) - C06Conjugates.extendedRealValue (φ (x₀ + (z : E))) =
      (f x₀ : EReal) + ((f.comp L.subtypeL z : EReal) -
        C06Conjugates.extendedRealValue (translated φ L x₀ z)) := by
    rw [map_add, EReal.coe_add, add_sub_assoc]
    rfl
  change (⨆ x : E, (f x : EReal) - C06Conjugates.extendedRealValue (φ x)) = _
  rw [show (f x₀ : EReal) + C06Conjugates.convexConjugate L
      (translated φ L x₀) (f.comp L.subtypeL) =
      ⨆ z : L, (f x₀ : EReal) + ((f.comp L.subtypeL z : EReal) -
        C06Conjugates.extendedRealValue (translated φ L x₀ z)) from
    (erealTranslate (f x₀)).map_iSup _]
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : φ x = ⊤
    · rw [hx]
      exact bot_le
    · let z : L := ⟨x - x₀, hs x hx⟩
      have he : x₀ + (z : E) = x := by dsimp [z]; abel
      rw [← he, hshift]
      exact le_iSup (fun z : L => (f x₀ : EReal) +
        ((f.comp L.subtypeL z : EReal) -
          C06Conjugates.extendedRealValue (translated φ L x₀ z))) z
  · apply iSup_le
    intro z
    rw [← hshift]
    exact le_iSup (fun x : E => (f x : EReal) -
      C06Conjugates.extendedRealValue (φ x)) (x₀ + (z : E))

lemma split_cost_translation (φ ψ : ExtendedFunction E) (L : Submodule ℝ E) (x₀ : E)
    (hφ : ∀ x ∈ Definitions.finiteDomain E φ, x - x₀ ∈ L)
    (hψ : ∀ x ∈ Definitions.finiteDomain E ψ, x - x₀ ∈ L) (f g : E →L[ℝ] ℝ) :
    conjugateSplitCost E φ ψ f g = (f x₀ : EReal) +
      conjugateSplitCost L (translated φ L x₀) (translated ψ L x₀)
        (f.comp L.subtypeL) (g.comp L.subtypeL) := by
  unfold conjugateSplitCost
  rw [conjugate_translation φ L x₀ hφ, conjugate_translation ψ L x₀ hψ]
  have he : (f - g).comp L.subtypeL = f.comp L.subtypeL - g.comp L.subtypeL := by
    ext z
    rfl
  rw [he, add_add_add_comm, sub_apply, ← EReal.coe_add]
  simp only [sub_add_cancel]

/-- Lift a minimizing restricted split by norm-preserving Hahn–Banach.
The equality also holds at +∞, where it makes no finiteness assertion. -/
lemma exists_split_eq_sum [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (L : Submodule ℝ E) (h : Spec.Hypotheses E φ ψ L) (f : E →L[ℝ] ℝ) :
    ∃ g : E →L[ℝ] ℝ, conjugateSplitCost E φ ψ f g =
      C06Conjugates.convexConjugate E (fun x => φ x + ψ x) f := by
  let : CompleteSpace L := h.2.2.2.2.2.2.2.1.completeSpace_coe
  obtain ⟨x₀, hφ₀, hψ₀⟩ := h.2.2.2.2.2.2.1
  obtain ⟨hφ, hψ⟩ := domains_in_affine_subspace φ ψ L h.2.2.2.2.2.2.2.2 x₀ hφ₀ hψ₀
  have ht := translated_hypotheses φ ψ L h x₀ hφ₀ hψ₀
  obtain ⟨k, hk⟩ := BanachFullConeExactness.exists_minimizing_split
    (translated φ L x₀) (translated ψ L x₀) ht.1 ht.2.1 ht.2.2.2.2.2.2.2
    (f.comp L.subtypeL)
  obtain ⟨g, hg, _⟩ := C05NormExtension.norm_preserving_extension ℝ E L k
  have hgr : g.comp L.subtypeL = k := by ext z; exact hg z
  have hsum : ∀ x ∈ Definitions.finiteDomain E (fun x => φ x + ψ x), x - x₀ ∈ L := by
    intro x hx
    apply hφ x
    change φ x ≠ ⊤
    intro he
    exact hx (by simp [he])
  refine ⟨g, ?_⟩
  have hformula := BanachFullConeExactness.exact_conjugate_formula L _ _ ht (f.comp L.subtypeL)
  change infimalConvolution L (translated φ L x₀) (translated ψ L x₀)
    (f.comp L.subtypeL) = C06Conjugates.convexConjugate L
      (fun z => translated φ L x₀ z + translated ψ L x₀ z) (f.comp L.subtypeL) at hformula
  rw [split_cost_translation φ ψ L x₀ hφ hψ, hgr, hk, hformula]
  exact (conjugate_translation (fun x => φ x + ψ x) L x₀ hsum f).symm

/-- Exactness on the closed subspace transfers to the entire continuous dual. -/
theorem exact_conjugate_formula : Spec.ExactConjugateFormula := by
  intro E _ _ _ φ ψ L h f
  obtain ⟨g, hg⟩ := exists_split_eq_sum φ ψ L h f
  exact le_antisymm ((iInf_le (conjugateSplitCost E φ ψ f) g).trans hg.le)
    (BanachFullConeExactness.sum_conjugate_le_infimal φ ψ f)

theorem finite_value_attainment : Spec.FiniteValueAttainment := by
  intro E _ _ _ φ ψ L h f r hr
  obtain ⟨g, hg⟩ := exists_split_eq_sum φ ψ L h f
  exact ⟨g, hg.trans hr⟩

/-- The domain sum is literal; no closure is taken. -/
theorem exact_domain_sum : Spec.ExactDomainSum := by
  intro E _ _ _ φ ψ L h f
  have finite_cost (a b : E →L[ℝ] ℝ) :
      conjugateSplitCost E φ ψ (a + b) b < ⊤ ↔
        C06Conjugates.convexConjugate E φ a < ⊤ ∧
        C06Conjugates.convexConjugate E ψ b < ⊤ := by
    unfold conjugateSplitCost
    simp only [add_sub_cancel_right, lt_top_iff_ne_top]
    exact EReal.add_ne_top_iff_ne_top₂
      (C06Conjugates.convexConjugate_ne_bot E φ h.1 a)
      (C06Conjugates.convexConjugate_ne_bot E ψ h.2.1 b)
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := exists_split_eq_sum φ ψ L h f
    refine ⟨f - g, g, (sub_add_cancel f g).symm, (finite_cost _ _).mp ?_⟩
    rw [sub_add_cancel, hg]
    exact hf
  · rintro ⟨a, b, rfl, ha, hb⟩
    exact (BanachFullConeExactness.sum_conjugate_le_infimal φ ψ (a + b)).trans_lt
      ((iInf_le (conjugateSplitCost E φ ψ (a + b)) b).trans_lt
        ((finite_cost a b).mpr ⟨ha, hb⟩))

/-- Weak duality bounds every dual value, while the lifted zero-functional
split reaches the primal infimum, including the extended value −∞. -/
theorem primal_dual_identity : Spec.PrimalDualIdentity := by
  intro E _ _ _ φ ψ L h
  let p := ⨅ x : E, C06Conjugates.extendedRealValue (φ x + ψ x)
  have hzero : C06Conjugates.convexConjugate E (fun x => φ x + ψ x) 0 = -p :=
    BanachFullConeExactness.conjugate_zero _
  have hneg (g : E →L[ℝ] ℝ) :
      -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g =
        -conjugateSplitCost E φ ψ 0 g :=
    (BanachFullConeExactness.neg_split_cost_zero φ ψ h.1 h.2.1 g).symm
  obtain ⟨g₀, hg₀⟩ := exists_split_eq_sum φ ψ L h 0
  have hmax : -C06Conjugates.convexConjugate E φ (-g₀) -
      C06Conjugates.convexConjugate E ψ g₀ = p := by
    rw [hneg, hg₀, hzero, neg_neg]
  have hbound (g : E →L[ℝ] ℝ) :
      -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g ≤ p := by
    have hw := (BanachFullConeExactness.sum_conjugate_le_infimal φ ψ 0).trans
      (iInf_le (conjugateSplitCost E φ ψ 0) g)
    rw [hzero] at hw
    simpa only [hneg, neg_neg] using (EReal.neg_le_neg_iff.mpr hw)
  have hproper : Proper E (fun x => φ x + ψ x) := by
    obtain ⟨x, hx, hy⟩ := h.2.2.2.2.2.2.1
    exact ⟨x, WithTop.add_ne_top.mpr ⟨hx, hy⟩⟩
  have hnt : p ≠ ⊤ := by
    have hh : C06Conjugates.convexConjugate E (fun x => φ x + ψ x) 0 ≠ ⊥ :=
      C06Conjugates.convexConjugate_ne_bot E _ hproper 0
    rw [hzero, ne_eq, EReal.neg_eq_bot_iff] at hh
    exact hh
  refine ⟨hnt, le_antisymm ?_ (iSup_le hbound), ?_⟩
  · exact hmax.symm.le.trans (le_iSup (fun g : E →L[ℝ] ℝ =>
      -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g) g₀)
  · intro r hr
    exact ⟨g₀, hmax.trans hr⟩

/-- Translate the ambient cost bound and apply the full-cone bound on L.
The shift f(x₀) is uniformly controlled when the total functionals are bounded. -/
theorem bounded_restricted_splits : Spec.BoundedRestrictedSplits := by
  intro E _ _ _ φ ψ L h B hB α
  let : CompleteSpace L := h.2.2.2.2.2.2.2.1.completeSpace_coe
  obtain ⟨x₀, hφ₀, hψ₀⟩ := h.2.2.2.2.2.2.1
  obtain ⟨hφ, hψ⟩ := domains_in_affine_subspace φ ψ L h.2.2.2.2.2.2.2.2 x₀ hφ₀ hψ₀
  have ht := translated_hypotheses φ ψ L h x₀ hφ₀ hψ₀
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hB
  let B' : Set (L →L[ℝ] ℝ) := (fun f : E →L[ℝ] ℝ => f.comp L.subtypeL) '' B
  have hrestriction (f : E →L[ℝ] ℝ) : ‖f.comp L.subtypeL‖ ≤ ‖f‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro z
    exact f.le_opNorm (z : E)
  have hB' : Bornology.IsBounded B' := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro k ⟨f, hf, rfl⟩
    exact (hrestriction f).trans (hM f hf)
  have hb := UniformSplitBounds.bounded_split_sublevel
    (translated φ L x₀) (translated ψ L x₀) ht.2.2.2.2.2.2.2
    B' hB' (α + M * ‖x₀‖)
  apply hb.subset
  rintro k ⟨f, g, hf, hcost, rfl⟩
  refine ⟨f.comp L.subtypeL, ⟨f, hf, rfl⟩, ?_⟩
  apply (EReal.addLECancellable_coe (f x₀)).add_le_add_iff_left.mp
  calc
    _ = conjugateSplitCost E φ ψ f g :=
      (split_cost_translation φ ψ L x₀ hφ hψ f g).symm
    _ ≤ (α : EReal) := hcost
    _ ≤ (f x₀ : EReal) + ((α + M * ‖x₀‖ : ℝ) : EReal) := by
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      have hfx : -f x₀ ≤ M * ‖x₀‖ := (neg_le_abs _).trans
        ((f.le_opNorm x₀).trans (mul_le_mul_of_nonneg_right (hM f hf) (norm_nonneg x₀)))
      linarith

/-- Replacing a split by a norm-preserving extension of its restriction changes
neither its cost nor its restricted values. -/
theorem bounded_representatives : Spec.BoundedRepresentatives := by
  intro E _ _ _ φ ψ L h B hB α
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (bounded_restricted_splits E φ ψ L h B hB α)
  obtain ⟨x₀, hφ₀, hψ₀⟩ := h.2.2.2.2.2.2.1
  obtain ⟨hφ, hψ⟩ := domains_in_affine_subspace φ ψ L h.2.2.2.2.2.2.2.2 x₀ hφ₀ hψ₀
  refine ⟨C, ?_⟩
  intro f g hf hcost
  obtain ⟨G, hG, hn⟩ := C05NormExtension.norm_preserving_extension ℝ E L (g.comp L.subtypeL)
  have he : G.comp L.subtypeL = g.comp L.subtypeL := by ext z; exact hG z
  refine ⟨G, he, ?_, ?_⟩
  · change conjugateSplitCost E φ ψ f G = conjugateSplitCost E φ ψ f g
    rw [split_cost_translation φ ψ L x₀ hφ hψ,
      split_cost_translation φ ψ L x₀ hφ hψ, he]
  · rw [hn]
    exact hC _ ⟨f, g, hf, hcost, rfl⟩

/-- In the special case L=E this is the full ambient split bound. -/
theorem full_cone_uniform_bounds : Spec.FullConeUniformBounds :=
  UniformSplitBounds.uniform_split_bounds

end ExpandedFA.InfimalConvolution.ClosedSubspaceCone
