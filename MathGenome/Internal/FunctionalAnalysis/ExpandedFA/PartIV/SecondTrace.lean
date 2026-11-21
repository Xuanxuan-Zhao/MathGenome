import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceFlat
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceLift

/-! Two jets on bounded C² domains, assembled from the geometric, flat,
transport, boundedness and lifting components. The outward sign and bounded
fractional coefficient correction are also explicit. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SecondTraceFlat ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Trace existence here is supplied by the actual bounded C¹ theorem. -/
theorem domain_first_trace_exists : Specs.ExpandedFA.PartIV.SecondTrace.TraceExists := by
  intro 𝕜 _ d Ω hb hΩ p _ _hp1 hp
  exact (ExpandedFA.Sobolev.Trace.trace_exists 𝕜 d Ω hb (c2Charts_to_c1 Ω hΩ) p hp).exists

/-- Positive inward coordinate, negative outward normal: precompose the
simultaneous lift with (g,h) ↦ (g,-h). This preserves its full norm estimate. -/
theorem flat_outward_extension : Specs.ExpandedFA.PartIV.SecondTrace.FlatOutwardExtension := by
  intro n p _ hp1 hp
  obtain ⟨C, hC, hE⟩ := bounded_jet_extension_clm n p hp1 hp
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  obtain ⟨E, hBound, _, hJets⟩ := hE 𝕜 i
  let A : (HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p ×
      FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) →L[𝕜]
      (HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p ×
      FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) :=
    (ContinuousLinearMap.id 𝕜 _).prodMap (-ContinuousLinearMap.id 𝕜 _)
  refine ⟨fun g h => E.comp A (g,h), ?_, ?_⟩
  · intro g h
    change ‖E (g,-h)‖ ≤ C * (‖g‖ + ‖h‖)
    have hh := hBound g (-h)
    change ‖E (g,-h)‖ ≤ C * (‖g‖ + ‖-h‖) at hh
    simpa only [norm_neg] using hh
  · intro T hT g h
    exact hJets T hT g (-h)

/-- Recover the prescribed outward derivative after replacing the inward
coefficient by (h-b·∇g)/a. -/
theorem coefficient_correction : Specs.ExpandedFA.PartIV.SecondTrace.CoefficientCorrection := by
  intro 𝕜 _ n a b q h ha x
  simp only [correctedNormalDatum, smul_smul, mul_inv_cancel₀ (ha x), one_smul,
    sub_add_cancel]

/-- The flat coefficient is a=-1 and has no tangential part. -/
theorem correctedNormalDatum_flat {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (q : Fin n → Domain n → 𝕜) (h : Domain n → 𝕜) :
    correctedNormalDatum (fun _ => -1) (fun _ _ => 0) q h = -h := by
  funext x
  simp [correctedNormalDatum]

/-- For an inward defining covector r, the outward normal is -r/|r|.
Its coefficient on the inward derivative is negative and nonzero. -/
theorem outward_chart_coefficient {d : ℕ} (r : Fin d → ℝ) (hpos : 0 < ∑ j, (r j)^2) :
    (∑ j, (-r j / Real.sqrt (∑ k, (r k)^2)) * r j) =
      -Real.sqrt (∑ k, (r k)^2) := by
  have hs : Real.sqrt (∑ k, (r k)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  calc
    (∑ j, (-r j / Real.sqrt (∑ k, (r k)^2)) * r j) =
        -(∑ j, (r j)^2) / Real.sqrt (∑ k, (r k)^2) := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      apply (div_eq_iff hs).2
      nlinarith [Real.sq_sqrt hpos.le]

theorem reciprocal_coefficient_bounds {n : ℕ} (a : Domain n → ℝ) (δ L : ℝ) (hδ : 0 < δ)
    (ha : ∀ x, δ ≤ |a x|)
    (hL : ∀ x y, |a x-a y| ≤ L * euclideanLength (x-y)) :
    (∀ x, |(a x)⁻¹| ≤ δ⁻¹) ∧
    (∀ x y, |(a x)⁻¹-(a y)⁻¹| ≤ (L / δ^2) * euclideanLength (x-y)) := by
  have ha0 (x) : a x ≠ 0 := abs_pos.mp (hδ.trans_le (ha x))
  constructor
  · intro x
    rw [abs_inv]
    exact inv_anti₀ hδ (ha x)
  · intro x y
    have he : |(a x)⁻¹-(a y)⁻¹| = |a x-a y| / (|a x| * |a y|) := by
      simpa only [Real.dist_eq, Real.norm_eq_abs] using dist_inv_inv₀ (ha0 x) (ha0 y)
    rw [he]
    have hden : δ^2 ≤ |a x| * |a y| := by nlinarith [ha x, ha y]
    calc
      |a x-a y| / (|a x| * |a y|) ≤ |a x-a y| / δ^2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ) hden
      _ ≤ (L * euclideanLength (x-y)) / δ^2 :=
        div_le_div_of_nonneg_right (hL x y) (sq_nonneg _)
      _ = _ := by ring

/-- Bounded multipliers implement the curvature correction in the full
fractional norm, including dimension zero and complex scalar data. -/
theorem bounded_coefficient_correction :
    Specs.ExpandedFA.PartIV.SecondTrace.BoundedCoefficientCorrection := by
  intro 𝕜 _ n s p _ hs0 hs1 hp a b M L Mb Lb hM hL hbM hbL
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  let A : FractionalSpace 𝕜 n s p →L[𝕜] FractionalSpace 𝕜 n s p :=
    boundedLipschitzMultiplier s p hs0 hs1 (fun x => (RCLike.ofReal ((a x)⁻¹) : 𝕜)) M L
      (by intro x; simpa only [RCLike.norm_ofReal] using hM x)
      (by intro x y; simpa only [← RCLike.ofReal_sub, RCLike.norm_ofReal] using hL x y)
  let B (j : Fin n) : FractionalSpace 𝕜 n s p →L[𝕜] FractionalSpace 𝕜 n s p :=
    boundedLipschitzMultiplier s p hs0 hs1 (fun x => (b j x : 𝕜)) (Mb j) (Lb j)
      (by intro x; simpa only [RCLike.norm_ofReal] using hbM j x)
      (by intro x y; simpa only [← RCLike.ofReal_sub, RCLike.norm_ofReal] using hbL j x y)
  let K : ℝ := 1 + ∑ j, ‖B j‖
  have hK : 1 ≤ K := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => norm_nonneg (B j))
  have hBK (j : Fin n) : ‖B j‖ ≤ K := by
    have h := Finset.single_le_sum (fun j _ => norm_nonneg (B j)) (Finset.mem_univ j)
    exact h.trans (by dsimp [K]; linarith)
  refine ⟨‖A‖ * K, mul_nonneg (norm_nonneg _) (le_trans zero_le_one hK), ?_⟩
  intro q h
  let v : FractionalSpace 𝕜 n s p := ∑ j, B j (q j)
  refine ⟨A (h-v), ?_, ?_⟩
  · have hsum : v.val = ∑ j, (B j (q j)).val := by
      exact map_sum (fractionalInclusion s p) (fun j => B j (q j)) Finset.univ
    have hv : v.val =ᵐ[volume] fun x => ∑ j, b j x • (q j).val x := by
      rw [hsum]
      have hc : ∀ᵐ x ∂(volume : Measure (Domain n)),
          ∀ j, (B j (q j)).val x = (b j x : 𝕜) * (q j).val x := by
        exact ae_all_iff.mpr fun j => boundedLipschitzMultiplier_representative
          s p hs0 hs1 (fun x => (b j x : 𝕜)) (Mb j) (Lb j) _ _ (q j)
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => (B j (q j)).val), hc]
        with x hx hc
      rw [hx]
      apply Finset.sum_congr rfl
      intro j _
      rw [hc j]
      exact (RCLike.real_smul_eq_coe_mul (b j x) ((q j).val x)).symm
    have hA := boundedLipschitzMultiplier_representative s p hs0 hs1
      (fun x => (RCLike.ofReal ((a x)⁻¹) : 𝕜)) M L
      (by intro x; simpa only [RCLike.norm_ofReal] using hM x)
      (by intro x y; simpa only [← RCLike.ofReal_sub, RCLike.norm_ofReal] using hL x y) (h-v)
    filter_upwards [hA, Lp.coeFn_sub h.val v.val, hv] with x hx hsub hvx
    change (A (h-v)).val x = _
    rw [show (A (h-v)).val x = _ from hx]
    change (RCLike.ofReal ((a x)⁻¹) : 𝕜) * (h.val - v.val) x = _
    rw [hsub]
    simp only [Pi.sub_apply, hvx, correctedNormalDatum, RCLike.real_smul_eq_coe_mul]
  · change ‖A (h-v)‖ ≤ _
    have hvbound : ‖v‖ ≤ K * ∑ j, ‖q j‖ := by
      calc
        ‖v‖ ≤ ∑ j, ‖B j (q j)‖ := norm_sum_le _ _
        _ ≤ ∑ j, K * ‖q j‖ := Finset.sum_le_sum fun j _ =>
          (ContinuousLinearMap.le_opNorm (B j) (q j)).trans
            (mul_le_mul_of_nonneg_right (hBK j) (norm_nonneg _))
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc
      ‖A (h-v)‖ ≤ ‖A‖ * ‖h-v‖ := A.le_opNorm _
      _ ≤ ‖A‖ * (‖h‖ + ‖v‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖A‖ * (K * ‖h‖ + K * ∑ j, ‖q j‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact add_le_add (le_mul_of_one_le_left (norm_nonneg _) hK) hvbound
      _ = (‖A‖ * K) * (fractionalNorm s p h + ∑ j, fractionalNorm s p (q j)) := by
        rw [← mul_add, mul_assoc]
        rfl

/-- For a fixed genuine first trace the two jet values are unique. -/
theorem domainJets_unique {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) {g h g' h' : BoundaryLp 𝕜 Ω p}
    (h₁ : HasDomainJets ν T u g h) (h₂ : HasDomainJets ν T u g' h') :
    g = g' ∧ h = h' := by
  rw [hasDomainJets_iff] at h₁ h₂
  exact ⟨h₁.1.symm.trans h₂.1, Lp.ext (h₁.2.trans h₂.2.symm)⟩

/-- The original first trace yields a bounded scalar-linear pair of surface
Lp jets for any measurable essentially bounded real normal field. Sharp
fractional regularity is a separate assertion in BoundedTrace. -/
theorem lp_jet_map : Specs.ExpandedFA.PartIV.SecondTrace.LpJetMap := by
  intro 𝕜 _ d Ω p _ ν hν hνbound T
  let N (j : Fin d) : BoundaryLp 𝕜 Ω p →L[𝕜] BoundaryLp 𝕜 Ω p :=
    Transport.aeSmulLpCLM (fun x => ν x j) (hν j) 1 (hνbound j)
  let D (j : Fin d) : SpaceValue 𝕜 d Ω 2 p →L[𝕜] BoundaryLp 𝕜 Ω p :=
    (N j).comp (T.comp (derivativePartCLM 𝕜 d Ω p j))
  let J : SpaceValue 𝕜 d Ω 2 p →L[𝕜]
      (BoundaryLp 𝕜 Ω p × BoundaryLp 𝕜 Ω p) :=
    (T.comp (orderOnePartCLM 𝕜 d Ω p)).prod (∑ j, D j)
  refine ⟨J, ?_⟩
  intro u
  rw [hasDomainJets_iff]
  refine ⟨rfl, ?_⟩
  change (∑ j, D j) u =ᵐ[surfaceMeasure Ω] _
  have he : (∑ j, D j) u = ∑ j, D j u := by simp
  rw [he]
  have hrep : ∀ᵐ x ∂surfaceMeasure Ω, ∀ j,
      D j u x = ν x j • T (derivativePart j u) x := by
    exact ae_all_iff.mpr fun j => Transport.aeSmulLp_coe
      (fun x => ν x j) (hν j) 1 (hνbound j) (T (derivativePart j u))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => D j u), hrep] with x hx hj
  rw [hx]
  simpa only [RCLike.real_smul_eq_coe_mul] using
    Finset.sum_congr rfl (fun j _ => hj j)

/-- The local weak derivative graph chosen by higherPiece is unique. -/
theorem higherPiece_unique {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : C2BoundaryModel 𝕜 Ω p) (σ : ℝ) (g : B.HigherData σ)
    (j : Fin B.chartCount) (v : HigherFractionalSpace 𝕜 (d-1) σ p)
    (hv : wholeLp (v.val.val (zeroIndex (d-1) 1)) = B.atlas.localizedLp p j (B.identify g.val)) :
    B.higherPiece σ g j = v := by
  apply Subtype.ext
  apply sobolev_underlying_injective 𝕜 (d-1) ⊤ 1 p
  apply wholeLpLI.injective
  exact (g.property j).choose_spec.trans hv.symm

/-- The boundedness child uses real scalar multiplication; the lifting child
uses its equal scalar-field multiplication. Both refer to the same actual
surface classes and first weak derivatives. -/
theorem hasDomainJets_bound_iff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) :
    Specs.ExpandedFA.PartIV.SecondTraceBound.HasDomainJets ν T u g h ↔
      HasDomainJets ν T u g h := by
  simp only [Specs.ExpandedFA.PartIV.SecondTraceBound.HasDomainJets,
    HasDomainJets, RCLike.real_smul_eq_coe_mul]

/-- Geometry and the genuine first trace remove vacuity. Uniqueness of the
jets identifies the sharp boundedness witnesses and the onto witnesses with
the values of the same bounded scalar-linear map. -/
theorem domain_jet_theorem_of_components
    (hGeometry : Specs.ExpandedFA.PartIV.SecondTrace.GeometryExists)
    (hBound : Specs.ExpandedFA.PartIV.SecondTrace.BoundedTrace)
    (hOnto : Specs.ExpandedFA.PartIV.SecondTrace.OntoTrace) :
    Specs.ExpandedFA.PartIV.SecondTrace.DomainJetTheorem := by
  intro 𝕜 _ d Ω hb hΩ p _ hp1 hp
  obtain ⟨⟨B⟩, ν, hν⟩ := hGeometry 𝕜 d Ω hb hΩ p hp1 hp
  obtain ⟨T, hT⟩ := domain_first_trace_exists 𝕜 d Ω hb hΩ p hp1 hp
  obtain ⟨J, hJ⟩ := lp_jet_map 𝕜 d Ω p ν
    (fun j => (hν.1 j).aestronglyMeasurable)
    (fun j => by simpa only [Real.norm_eq_abs] using hν.2.1 j) T
  obtain ⟨C, hC, hBC⟩ := hBound 𝕜 d Ω hb hΩ p hp1 hp B ν hν
  refine ⟨B, ν, T, J, C, hν, hT, hC, ?_, ?_⟩
  · intro u
    obtain ⟨g, h, hjet, hnorm⟩ := hBC T hT u
    have he := domainJets_unique ν T u
      ((hasDomainJets_bound_iff ν T u g.val h.val).mp hjet) (hJ u)
    exact ⟨hJ u, g, h, he.1, he.2, hnorm⟩
  · intro g h
    obtain ⟨u, hu⟩ := hOnto 𝕜 d Ω hb hΩ p hp1 hp B ν hν T hT g h
    have he := domainJets_unique ν T u (hJ u) hu
    exact ⟨u, Prod.ext he.1 he.2⟩

/-- Assembly retains every geometric, higher-atlas, boundedness and
simultaneous surjectivity obligation of the independent statement. -/
theorem second_trace_of_components
    (hGeometry : Specs.ExpandedFA.PartIV.SecondTrace.GeometryExists)
    (hAtlas : Specs.ExpandedFA.PartIV.SecondTrace.HigherAtlasIndependence)
    (hBound : Specs.ExpandedFA.PartIV.SecondTrace.BoundedTrace)
    (hOnto : Specs.ExpandedFA.PartIV.SecondTrace.OntoTrace) :
    Specs.ExpandedFA.PartIV.SecondTrace.SecondTrace :=
  ⟨hGeometry, domain_first_trace_exists, hAtlas, hBound, hOnto,
    domain_jet_theorem_of_components hGeometry hBound hOnto⟩

/-- Bounded and onto two-jet trace on every bounded C² domain, for both
scalar fields and 1 < p < ∞, with the actual outward normal. -/
theorem second_trace : Specs.ExpandedFA.PartIV.SecondTrace.SecondTrace :=
  second_trace_of_components geometry_exists higher_atlas_independence bounded_trace onto_trace

/-- The simultaneous map form of the theorem. -/
theorem domain_jet_theorem : Specs.ExpandedFA.PartIV.SecondTrace.DomainJetTheorem :=
  second_trace.2.2.2.2.2

end ExpandedFA.PartIV.SecondTrace
