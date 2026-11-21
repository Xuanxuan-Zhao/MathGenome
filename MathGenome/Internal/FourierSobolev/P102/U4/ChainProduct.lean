import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ChainProduct
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.MeanValue

import MathGenome.Internal.FourierSobolev.P102.U4.ACL
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology
namespace P102.U4

/-- Coordinate equations suffice to construct the full order-one derivative graph,
including when there are no coordinates. -/
theorem firstOrder_graph (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {𝕜 : Type} [RCLike 𝕜] (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (h : ∀ j, distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω (g j)) :
    ∃ w : Sobolev 𝕜 Ω 1 p, sobolevUnderlying w = u ∧
      ∀ j, firstWeakDerivative w j = g j := by
  have hu : HasSobolevDerivatives Ω 1 p u := by
    intro α hα
    by_cases hz : α = 0
    · subst α
      exact ⟨u, derivative_zero d 𝕜 Ω _⟩
    · have hc : α.card = 1 := by
        have hn := Multiset.card_eq_zero.not.mpr hz
        omega
      obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      exact ⟨g j, h j⟩
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (sobolev_range Ω 1 p) u).mpr hu
  refine ⟨w, hw, fun j => ?_⟩
  symm
  apply sobolev_derivative_unique Ω 1 p w (firstSobolevIndex j)
  simpa only [hw, firstSobolevIndex] using h j

/-- Completed Fubini transfers ambient a.e. assertions to almost every fiber
of the Euclidean coordinate lines used in the independent ACL specification. -/
theorem acl_ae_on_fibers {d : ℕ} (Ω : Opens (Space d)) (j : Fin d)
    {P : Space d → Prop} (h : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), P x) :
    ∀ᵐ z : ACL.Transverse j ∂volume,
      ∀ᵐ t ∂volume.restrict (ACL.fiber Ω j z), P (ACL.line j z t) := by
  let U : Opens (Fin d → ℝ) := ⟨WithLp.toLp 2 ⁻¹' (Ω : Set (Space d)),
    Ω.isOpen.preimage (PiLp.continuous_toLp 2 _)⟩
  have hh := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' Ω.isOpen.measurableSet).mp h)
  let e : (Fin d → ℝ) ≃ᵐ ℝ × ACL.Transverse j :=
    (Homeomorph.funSplitAt ℝ j).toMeasurableEquiv
  have he : MeasurePreserving e volume volume := by
    let : Unique {i : Fin d // i = j} :=
      ⟨⟨⟨j, rfl⟩⟩, fun i => Subtype.ext i.property⟩
    have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
      (fun i => i = j)
    have hone := (volume_preserving_funUnique {i : Fin d // i = j} ℝ).prod
      (MeasurePreserving.id (volume : Measure (ACL.Transverse j)))
    have hsplit' : MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (fun i => i = j))
        volume ((volume : Measure ({i : Fin d // i = j} → ℝ)).prod
          (volume : Measure (ACL.Transverse j))) := by
      convert hsplit using 1
      congr
      exact Subsingleton.elim _ _
    exact hone.comp hsplit'
  have hes (t : ℝ) (z : ACL.Transverse j) :
      e.symm (t, z) = ExpandedFA.Sobolev.Lines.coordinateLine j z t := by
    ext i
    simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
      Equiv.piSplitAt, ExpandedFA.Sobolev.Lines.coordinateLine]
  have hprod := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      ((he.symm e).quasiMeasurePreserving.ae hh))
  filter_upwards [hprod] with z hz
  apply (ae_restrict_iff'
    (ExpandedFA.Sobolev.Lines.fiber U j z).isOpen.measurableSet).mpr
  simpa [hes, ACL.line, ExpandedFA.Sobolev.Lines.fiber, U] using hz

/-- Bounded real differential implies the required zero-order Lp integrability
in each of the three source cases. -/
theorem scalar_composition_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) (u : DomainLp 𝕜 Ω p) (F : 𝕜 → 𝕜)
    (hF : ContDiff ℝ 1 F) (hbound : ∃ C : ℝ≥0, ∀ t, ‖fderiv ℝ F t‖ ≤ C)
    (hcase : F 0 = 0 ∨ volume (Ω : Set (Space d)) < ⊤ ∨ p = ⊤) :
    MemLp (fun x => F (u x)) p (volume.restrict (Ω : Set (Space d))) := by
  obtain ⟨C, hC⟩ := hbound
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le
    (hF.differentiable (by decide)) (fun t => by exact_mod_cast hC t)
  have hLip0 : LipschitzWith C (fun t => F t - F 0) := by
    intro x y
    simpa only [edist_sub_right] using hLip x y
  rcases hcase with hz | hfinite | htop
  · exact hLip.comp_memLp hz (Lp.memLp u)
  · let : IsFiniteMeasure (volume.restrict (Ω : Set (Space d))) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
    have h := (hLip0.comp_memLp (sub_self _) (Lp.memLp u)).add
      (memLp_const (F 0))
    simpa only [Pi.add_def, Function.comp_def, sub_add_cancel] using h
  · have h := (hLip0.comp_memLp (sub_self _) (Lp.memLp u)).add
      (htop.symm ▸ memLp_top_const (μ := volume.restrict (Ω : Set (Space d))) (F 0))
    simpa only [Pi.add_def, Function.comp_def, sub_add_cancel] using h

/-- A bounded continuous field of real differentials applied to an Lp vector
field remains in Lp; no complex linearity is assumed. -/
theorem scalar_differential_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) (u v : DomainLp 𝕜 Ω p) (F : 𝕜 → 𝕜)
    (hF : ContDiff ℝ 1 F) (hbound : ∃ C : ℝ≥0, ∀ t, ‖fderiv ℝ F t‖ ≤ C) :
    MemLp (fun x => fderiv ℝ F (u x) (v x)) p
      (volume.restrict (Ω : Set (Space d))) := by
  obtain ⟨C, hC⟩ := hbound
  apply (Lp.memLp v).of_le_mul
  · exact (hF.continuous_fderiv_apply (by decide)).comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable u).prodMk (Lp.aestronglyMeasurable v))
  · exact Eventually.of_forall fun x =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- Conditional draft of the scalar chain rule, with the complete frozen ACL
premises in their prescribed order. -/
theorem chain_rule_conditional
    (hACL : ACLExpected.Characterization)
    (hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : ChainProductExpected.ChainRule := by
  intro d 𝕜 _ Ω p _ u F hF hbound hcase
  let μ := volume.restrict (Ω : Set (Space d))
  have hm := scalar_composition_memLp Ω p (sobolevUnderlying u) F hF hbound hcase
  have hk (j : Fin d) := scalar_differential_memLp Ω p
    (sobolevUnderlying u) (firstWeakDerivative u j) F hF hbound
  let w : DomainLp 𝕜 Ω p := hm.toLp (fun x => F (sobolevUnderlying u x))
  let k : Fin d → DomainLp 𝕜 Ω p := fun j =>
    (hk j).toLp (fun x => fderiv ℝ F (sobolevUnderlying u x) (firstWeakDerivative u j x))
  have hw : w =ᵐ[μ] (fun x => F (sobolevUnderlying u x)) := hm.coeFn_toLp
  have hke (j : Fin d) : k j =ᵐ[μ]
      (fun x => fderiv ℝ F (sobolevUnderlying u x) (firstWeakDerivative u j x)) :=
    (hk j).coeFn_toLp
  have heq (j : Fin d) : distributionPartial {j} (regularDistribution Ω w) =
      regularDistribution Ω (k j) := by
    have hd : 0 < d := Nat.zero_lt_of_lt j.isLt
    obtain ⟨f, huf, hf⟩ := (hACL d hd 𝕜 Ω j (sobolevUnderlying u)
      (firstWeakDerivative u j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)).mp
        (sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j))
    apply hConverse d hd 𝕜 Ω j w (k j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)
    refine ⟨F ∘ f, hw.trans (huf.fun_comp F), ?_⟩
    obtain ⟨C, hC⟩ := hbound
    have hFd : Differentiable ℝ F := hF.differentiable (by decide)
    have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hFd
      (fun t => by exact_mod_cast hC t)
    filter_upwards [hf, acl_ae_on_fibers Ω j huf, acl_ae_on_fibers Ω j (hke j)]
      with z hfz huz hkz
    refine ⟨fun a b hab => hLip.comp_absolutelyContinuousOnInterval (hfz.1 a b hab), ?_⟩
    filter_upwards [hfz.2, huz, hkz] with t hft hut hkt
    rw [hkt, hut]
    exact (hFd _).hasFDerivAt.comp_hasDerivAt t hft
  obtain ⟨W, hW, hD⟩ := firstOrder_graph Ω p w k heq
  refine ⟨W, ?_, fun j => ?_⟩
  · simpa only [hW] using hw
  · simpa only [hD] using hke j

/-- Conditional draft of the bounded product rule. -/
theorem product_rule_conditional
    (hACL : ACLExpected.Characterization)
    (hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : ChainProductExpected.ProductRule := by
  intro d 𝕜 _ Ω p _ u v hub hvb
  let μ := volume.restrict (Ω : Set (Space d))
  have hm : MemLp (fun x => sobolevUnderlying u x * sobolevUnderlying v x) p μ :=
    hub.mul (Lp.memLp (sobolevUnderlying v))
  have hk (j : Fin d) : MemLp (fun x =>
      sobolevUnderlying v x * firstWeakDerivative u j x +
      sobolevUnderlying u x * firstWeakDerivative v j x) p μ :=
    (hvb.mul (Lp.memLp (firstWeakDerivative u j))).add
      (hub.mul (Lp.memLp (firstWeakDerivative v j)))
  let w : DomainLp 𝕜 Ω p := hm.toLp _
  let k : Fin d → DomainLp 𝕜 Ω p := fun j => (hk j).toLp _
  have hw : w =ᵐ[μ] (fun x => sobolevUnderlying u x * sobolevUnderlying v x) :=
    hm.coeFn_toLp
  have hke (j : Fin d) : k j =ᵐ[μ] (fun x =>
      sobolevUnderlying v x * firstWeakDerivative u j x +
      sobolevUnderlying u x * firstWeakDerivative v j x) := (hk j).coeFn_toLp
  have heq (j : Fin d) : distributionPartial {j} (regularDistribution Ω w) =
      regularDistribution Ω (k j) := by
    have hd : 0 < d := Nat.zero_lt_of_lt j.isLt
    obtain ⟨f, huf, hf⟩ := (hACL d hd 𝕜 Ω j (sobolevUnderlying u)
      (firstWeakDerivative u j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)).mp
        (sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j))
    obtain ⟨q, hvq, hq⟩ := (hACL d hd 𝕜 Ω j (sobolevUnderlying v)
      (firstWeakDerivative v j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)).mp
        (sobolev_derivative_distribution Ω 1 p v (firstSobolevIndex j))
    apply hConverse d hd 𝕜 Ω j w (k j) (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)
    refine ⟨fun x => f x * q x, hw.trans (huf.mul hvq), ?_⟩
    filter_upwards [hf, hq, acl_ae_on_fibers Ω j huf, acl_ae_on_fibers Ω j hvq,
      acl_ae_on_fibers Ω j (hke j)] with z hfz hqz huz hvz hkz
    refine ⟨?_, ?_⟩
    · intro a b hab
      convert (hfz.1 a b hab).smul (hqz.1 a b hab) using 1
    · filter_upwards [hfz.2, hqz.2, huz, hvz, hkz] with t hft hqt hut hvt hkt
      rw [hkt, hut, hvt]
      convert hft.mul hqt using 1; simp only [mul_comm]
  obtain ⟨W, hW, hD⟩ := firstOrder_graph Ω p w k heq
  refine ⟨W, ?_, fun j => ?_⟩
  · simpa only [hW] using hw
  · simpa only [hD] using hke j

end P102.U4

theorem _root_.«P102».«U4».«chain_rule» : _root_.«P102».«U4».«ChainProductExpected».«ChainRule» :=
  @_root_.«P102».«U4».«chain_rule_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
theorem _root_.«P102».«U4».«product_rule» : _root_.«P102».«U4».«ChainProductExpected».«ProductRule» :=
  @_root_.«P102».«U4».«product_rule_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
