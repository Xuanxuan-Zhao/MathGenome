import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.ConvexBodySetup
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace ExpandedFA.HilbertCharacterization

universe u
open Set Metric Filter
open scoped Topology
open Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
open Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness

section Normed
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized supporting functional is dominated by the Minkowski gauge. -/
theorem normal_le_gauge {K : Set E} {p : E} (ha : Absorbent ℝ K)
    {f : E →L[ℝ] ℝ} (hf : f ∈ NormalCone K p) (hp : f p = 1) (x : E) :
    f x ≤ gauge K x := by
  apply le_csInf ha.gauge_set_nonempty
  rintro r ⟨hr, y, hy, rfl⟩
  simpa [map_smul, hp] using mul_le_mul_of_nonneg_left (hf y hy) hr.le

/-- Differentiability of the gauge makes a normalized supporting functional unique.
The contact point can be any positive rescaling of the differentiability point. -/
theorem normal_eq_fderiv_gauge {K : Set E} {p x : E} (ha : Absorbent ℝ K)
    (hd : DifferentiableAt ℝ (gauge K) x) {f : E →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hp : f p = 1) (hx : f x = gauge K x) :
    f = fderiv ℝ (gauge K) x := by
  have hmin : IsLocalMin (fun y => gauge K y - f y) x := by
    apply Filter.Eventually.of_forall
    intro y
    change gauge K x - f x ≤ gauge K y - f y
    rw [hx, sub_self]
    exact sub_nonneg.mpr (normal_le_gauge ha hf hp y)
  have hz := hmin.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub f.hasFDerivAt)
  exact (sub_eq_zero.mp hz).symm

/-- Taking a central section preserves the canonical body conditions. -/
theorem symmetricConvexBody_section [FiniteDimensional ℝ E]
    {K : Set E} (hK : SymmetricConvexBody K) (L : Submodule ℝ E) :
    SymmetricConvexBody ((fun x : L => (x : E)) ⁻¹' K) := by
  refine ⟨L.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage hK.1,
    hK.2.1.linear_preimage L.subtype, ?_, ?_⟩
  · intro x hx
    exact hK.2.2.1 x hx
  · apply mem_interior_iff_mem_nhds.mpr
    exact L.subtypeL.continuous.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hK.2.2.2)

/-- Smooth supporting normals separate vectors. Rademacher is applied only to
the gauge of this body (later, a planar section), not to the ambient boundary. -/
theorem exists_smooth_normal_separating [FiniteDimensional ℝ E]
    {K : Set E} (hK : SymmetricConvexBody K) {v : E} (hv : v ≠ 0) :
    ∃ p ∈ frontier K, ∃ f ∈ NormalCone K p,
      f p = 1 ∧ f v ≠ 0 ∧
      ∀ g ∈ NormalCone K p, g p = 1 → g = f := by
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.2.2
  have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK
  have hgv : 0 < gauge K v :=
    (div_pos (norm_pos_iff.mpr hv) hR).trans_le
      (le_gauge_of_subset_closedBall ha hR.le hout)
  obtain ⟨C, hC⟩ := hK.2.1.lipschitz_gauge hzero
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hdense : Dense {x : E | DifferentiableAt ℝ (gauge K) x} :=
    MeasureTheory.Measure.dense_of_ae
      (hC.ae_differentiableAt (μ := (Module.Basis.ofVectorSpace ℝ E).addHaar))
  have hopen : IsOpen {x : E | (C : ℝ) * ‖x - v‖ < gauge K x} :=
    isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).norm))
      (continuous_gauge hK.2.1 hzero)
  obtain ⟨x, hdx, hx⟩ := hdense.exists_mem_open hopen
    ⟨v, by simpa using hgv⟩
  let a := gauge K x
  have hapos : 0 < a := (mul_nonneg C.coe_nonneg (norm_nonneg _)).trans_lt hx
  let p : E := a⁻¹ • x
  have hp : p ∈ frontier K := by
    apply (gauge_eq_one_iff_mem_frontier hK.2.1 hzero).mp
    simp [p, gauge_smul_of_nonneg (inv_nonneg.mpr hapos.le), a, hapos.ne']
  obtain ⟨f₀, hf₀, hfn₀⟩ := normalCone_nonzero K p hK hp
  have hfpos : 0 < f₀ p := normalCone_positive K p hK.2.2.2 f₀ hf₀ hfn₀
  let f : E →L[ℝ] ℝ := (f₀ p)⁻¹ • f₀
  have hf : f ∈ NormalCone K p := by
    intro y hy
    exact mul_le_mul_of_nonneg_left (hf₀ y hy) (inv_nonneg.mpr hfpos.le)
  have hfp : f p = 1 := by simp [f, hfpos.ne']
  have contact : ∀ g : E →L[ℝ] ℝ, g p = 1 → g x = a := by
    intro g hgp
    have h := congrArg (fun z : ℝ => a * z) hgp
    simpa [p, map_smul, ← mul_assoc, hapos.ne'] using h
  have hfx : f x = a := contact f hfp
  have hfd : f = fderiv ℝ (gauge K) x := normal_eq_fderiv_gauge ha hdx hf hfp hfx
  have hnorm : ‖f‖ ≤ C := by rw [hfd]; exact norm_fderiv_le_of_lipschitz ℝ hC
  have hfv : f v ≠ 0 := by
    have hval : f (x - v) < f x := calc
      f (x - v) ≤ ‖f (x - v)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x - v‖ := f.le_opNorm _
      _ ≤ (C : ℝ) * ‖x - v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ < f x := by simpa [hfx] using hx
    rw [map_sub] at hval
    exact ne_of_gt (by linarith)
  refine ⟨p, hp, f, hf, hfp, hfv, ?_⟩
  intro g hg hgp
  exact (normal_eq_fderiv_gauge ha hdx hg hgp (contact g hgp)).trans hfd.symm

end Normed

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A common nonzero tangent forces uniqueness of normalized ambient normals.
The proof uses planes span(p,t+εu); it does not assume boundary regularity. -/
theorem normalized_normal_unique_of_tangent
    {K : Set E} (hK : ProjectionBody K) {p t : E}
    (htne : t ≠ 0) (ht : ∀ f ∈ NormalCone K p, f t = 0)
    {f g : E →L[ℝ] ℝ} (hf : f ∈ NormalCone K p) (hg : g ∈ NormalCone K p)
    (hfp : f p = 1) (hgp : g p = 1) : f = g := by
  by_contra hfg
  obtain ⟨u, hu⟩ : ∃ u : E, f u ≠ g u := by
    by_contra h
    push Not at h
    exact hfg (ContinuousLinearMap.ext h)
  let d : E →L[ℝ] ℝ := f - g
  have hdp : d p = 0 := by simp [d, hfp, hgp]
  have hdt : d t = 0 := by simp [d, ht f hf, ht g hg]
  have hdu : d u ≠ 0 := sub_ne_zero.mpr hu
  obtain ⟨r, R, hr, hR, hin, hout, hbound⟩ := projectionBody_uniform_bound K hK
  let C : ℝ := R / r
  have hC : 0 ≤ C := div_nonneg hR.le hr.le
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (norm_pos_iff.mpr htne) ((C + 1) * ‖u‖)
  let w : E := t + ε • u
  have hdw : d w = ε * d u := by simp [w, map_add, map_smul, hdt]
  have hdwne : d w ≠ 0 := by rw [hdw]; exact mul_ne_zero hε.ne' hdu
  have hli : LinearIndependent ℝ (![p, w] : Fin 2 → E) := by
    apply linearIndependent_fin2.mpr
    change w ≠ 0 ∧ ∀ c : ℝ, c • w ≠ p
    constructor
    · intro hw
      exact hdwne (by simp [hw])
    · intro c hc
      have hdc := congrArg d hc
      simp only [map_smul, hdp, smul_eq_mul] at hdc
      have hc0 : c = 0 := (mul_eq_zero.mp hdc).resolve_right hdwne
      have hp0 : p = 0 := by simpa [hc0] using hc.symm
      have := hfp
      simp [hp0] at this
  let M : Submodule ℝ E := Submodule.span ℝ {p, w}
  have hdim : Module.finrank ℝ M = 2 := by
    have hrange : Set.range (![p, w] : Fin 2 → E) = {p, w} := by
      exact Matrix.range_cons_cons_empty p w ![]
    change Module.finrank ℝ (Submodule.span ℝ {p, w}) = 2
    rw [← hrange]
    exact finrank_span_eq_card hli
  obtain ⟨P, hP⟩ := hK.2.2 M hdim
  have hpM : p ∈ M := Submodule.subset_span (by simp)
  have hwM : w ∈ M := Submodule.subset_span (by simp)
  have pull : ∀ h ∈ NormalCone K p, h.comp P ∈ NormalCone K p := by
    intro h hh y hy
    change h (P y) ≤ h (P p)
    rw [hP.2.1 p hpM]
    exact hh (P y) (hP.2.2 hy)
  have hfPt : f (P t) = 0 := ht (f.comp P) (pull f hf)
  have hgPt : g (P t) = 0 := ht (g.comp P) (pull g hg)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hP.1 t)
  have hb0 : b = 0 := by
    have hdab := congrArg d hab
    simp only [map_add, map_smul, hdp, smul_eq_mul, mul_zero, zero_add] at hdab
    have hdPt : d (P t) = 0 := by simp [d, hfPt, hgPt]
    rw [hdPt] at hdab
    exact (mul_eq_zero.mp hdab).resolve_right hdwne
  have ha0 : a = 0 := by
    have hfab := congrArg f hab
    simpa [map_add, map_smul, hb0, hfp, hfPt] using hfab
  have hPt : P t = 0 := by simpa [ha0, hb0] using hab.symm
  have hw : w = ε • P u := by
    calc
      w = P w := (hP.2.1 w hwM).symm
      _ = ε • P u := by simp [w, map_add, map_smul, hPt]
  have hnorm : ‖w‖ ≤ ε * (C * ‖u‖) := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left
      ((P.le_opNorm u).trans (mul_le_mul_of_nonneg_right (hbound M P hP) (norm_nonneg _))) hε.le
  have hnormt : ‖t‖ ≤ ‖w‖ + ε * ‖u‖ := by
    calc
      ‖t‖ = ‖w - ε • u‖ := by simp [w]
      _ ≤ ‖w‖ + ‖ε • u‖ := norm_sub_le _ _
      _ = ‖w‖ + ε * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  nlinarith

/-- A smooth section supplies a common tangent for all ambient supporting
normals, even before any ambient regularity has been established. -/
theorem normalized_normal_unique_of_smooth_section {K : Set E} (hK : ProjectionBody K)
    (L : Submodule ℝ E) (hL : Module.finrank ℝ L = 2) (p : L)
    (g : L →L[ℝ] ℝ)
    (hunique : ∀ h ∈ PlanarNormalCone K L p, h p = 1 → h = g)
    {f₁ f₂ : E →L[ℝ] ℝ} (hf₁ : f₁ ∈ NormalCone K (p : E))
    (hf₂ : f₂ ∈ NormalCone K (p : E)) (hfp₁ : f₁ p = 1) (hfp₂ : f₂ p = 1) :
    f₁ = f₂ := by
  have hrange : Module.finrank ℝ g.toLinearMap.range ≤ 1 := by
    simpa using g.toLinearMap.range.finrank_le
  have hsum := g.toLinearMap.finrank_range_add_finrank_ker
  have hker : 0 < Module.finrank ℝ g.toLinearMap.ker := by omega
  obtain ⟨t, htne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hker
  have hgt : g (t : L) = 0 := t.property
  have htneE : ((t : L) : E) ≠ 0 := by
    intro ht0
    apply htne
    apply Subtype.ext
    exact Subtype.ext ht0
  apply normalized_normal_unique_of_tangent hK htneE ?_ hf₁ hf₂ hfp₁ hfp₂
  intro f hf
  by_cases hfn : f = 0
  · simp [hfn]
  have hpos : 0 < f (p : E) := normalCone_positive K p hK.2.1.2.2.2 f hf hfn
  let h : L →L[ℝ] ℝ := (f (p : E))⁻¹ • restrictNormal L f
  have hh : h ∈ PlanarNormalCone K L p := by
    intro y hy
    exact mul_le_mul_of_nonneg_left (hf y hy) (inv_nonneg.mpr hpos.le)
  have hhp : h p = 1 := by simp [h, restrictNormal, hpos.ne']
  have heq := congrArg (fun k : L →L[ℝ] ℝ => k (t : L)) (hunique h hh hhp)
  change (f (p : E))⁻¹ * f ((t : L) : E) = g (t : L) at heq
  rw [hgt] at heq
  exact (mul_eq_zero.mp heq).resolve_left (inv_ne_zero hpos.ne')

/-- Uniqueness of projections, deduced from separating smooth section normals. -/
theorem bodyProjection_unique {K : Set E} (hK : ProjectionBody K)
    (L : Submodule ℝ E) (hL : Module.finrank ℝ L = 2)
    {P Q : E →L[ℝ] E} (hP : BodyProjection K L P) (hQ : BodyProjection K L Q) : P = Q := by
  ext x
  by_contra hx
  let v : L := ⟨P x - Q x, L.sub_mem (hP.1 x) (hQ.1 x)⟩
  have hv : v ≠ 0 := by
    intro hv0
    exact hx (sub_eq_zero.mp (congrArg (fun y : L => (y : E)) hv0))
  obtain ⟨p, _hp, g, hg, hgp, hgv, huniq⟩ :=
    exists_smooth_normal_separating (symmetricConvexBody_section hK.2.1 L) hv
  have hg' : g ∈ PlanarNormalCone K L p := hg
  obtain ⟨fP, hfP, hrestrP, hformP⟩ := planarNormal_extend K L P hP p g hg'
  obtain ⟨fQ, hfQ, hrestrQ, hformQ⟩ := planarNormal_extend K L Q hQ p g hg'
  have hfp : fP p = 1 := (congrArg (fun h : L →L[ℝ] ℝ => h p) hrestrP).trans hgp
  have hfq : fQ p = 1 := (congrArg (fun h : L →L[ℝ] ℝ => h p) hrestrQ).trans hgp
  have heq : fP = fQ := normalized_normal_unique_of_smooth_section hK L hL p g
    (fun h hh hhp => huniq h hh hhp) hfP hfQ hfp hfq
  have hxg : g ⟨P x, hP.1 x⟩ = g ⟨Q x, hQ.1 x⟩ :=
    (hformP x).symm.trans ((congrArg (fun h : E →L[ℝ] ℝ => h x) heq).trans (hformQ x))
  apply hgv
  change g ((⟨P x, hP.1 x⟩ : L) - ⟨Q x, hQ.1 x⟩) = 0
  rw [map_sub, hxg, sub_self]

theorem projection_uniqueness : uniquenessType.{u} := by
  intro E _ _ _ K hK L hL
  obtain ⟨P, hP⟩ := hK.2.2 L hL
  exact ⟨P, hP, fun Q hQ => bodyProjection_unique hK L hL hQ hP⟩

/-- Projection equations written using the auxiliary Euclidean projector. -/
theorem bodyProjection_iff_starProjection {K : Set E} (L : Submodule ℝ E)
    (P : E →L[ℝ] E) :
    BodyProjection K L P ↔ L.starProjection.comp P = P ∧
      P.comp L.starProjection = L.starProjection ∧ MapsTo P K K := by
  constructor
  · intro hP
    refine ⟨?_, ?_, hP.2.2⟩
    · ext x
      exact L.starProjection_eq_self_iff.mpr (hP.1 x)
    · ext x
      exact hP.2.1 _ (L.starProjection_apply_mem x)
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun x => L.starProjection_eq_self_iff.mp ?_, ?_, h₃⟩
    · exact congrArg (fun A : E →L[ℝ] E => A x) h₁
    · intro x hx
      have h := congrArg (fun A : E →L[ℝ] E => A x) h₂
      simpa [L.starProjection_eq_self_iff.mpr hx] using h

/-- The full projection relation has a closed graph when planes are represented
by their orthogonal projectors. -/
theorem isClosed_bodyProjection {X : Type*} [TopologicalSpace X]
    {K : Set E} (hK : IsClosed K) (L : X → Submodule ℝ E)
    (hL : Continuous (fun x => (L x).starProjection)) :
    IsClosed {z : X × (E →L[ℝ] E) | BodyProjection K (L z.1) z.2} := by
  have hmaps : IsClosed {z : X × (E →L[ℝ] E) | MapsTo z.2 K K} := by
    have heq : {z : X × (E →L[ℝ] E) | MapsTo z.2 K K} =
        ⋂ y ∈ K, (fun z : X × (E →L[ℝ] E) => z.2 y) ⁻¹' K := by
      ext z
      simp [MapsTo]
    rw [heq]
    exact isClosed_biInter fun y _ => hK.preimage
      ((ContinuousLinearMap.apply ℝ E y).continuous.comp continuous_snd)
  have h₁ : IsClosed {z : X × (E →L[ℝ] E) |
      (L z.1).starProjection.comp z.2 = z.2} :=
    isClosed_eq ((hL.comp continuous_fst).clm_comp continuous_snd) continuous_snd
  have h₂ : IsClosed {z : X × (E →L[ℝ] E) |
      z.2.comp (L z.1).starProjection = (L z.1).starProjection} :=
    isClosed_eq (continuous_snd.clm_comp (hL.comp continuous_fst))
      (hL.comp continuous_fst)
  convert h₁.inter (h₂.inter hmaps) using 1
  ext z
  exact bodyProjection_iff_starProjection (L z.1) z.2

/-- The unique admissible projections depend continuously on their planes. -/
theorem bodyProjection_family_continuous {K : Set E} (hK : ProjectionBody K)
    (P : CentralPlane E → (E →L[ℝ] E))
    (hP : ∀ L, BodyProjection K L.subspace (P L)) : Continuous P := by
  obtain ⟨r, R, hr, hR, hin, hout, hbound⟩ := projectionBody_uniform_bound K hK
  let B : Set (E →L[ℝ] E) := closedBall 0 (R / r)
  have hB : IsCompact B := isCompact_closedBall _ _
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let F : CentralPlane E → B := fun L => ⟨P L, by
    simpa [B, mem_closedBall, dist_eq_norm] using hbound L.subspace (P L) (hP L)⟩
  have hgraph : IsClosed F.graph := by
    have hc : IsClosed {z : CentralPlane E × B |
        BodyProjection K z.1.subspace (z.2 : E →L[ℝ] E)} :=
      (isClosed_bodyProjection hK.2.1.1.isClosed
        (fun L : CentralPlane E => L.subspace) continuous_induced_dom).preimage
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    convert hc using 1
    ext z
    change F z.1 = z.2 ↔ BodyProjection K z.1.subspace (z.2 : E →L[ℝ] E)
    constructor
    · intro hz
      exact hz ▸ hP z.1
    · intro hz
      exact Subtype.ext (bodyProjection_unique hK z.1.subspace z.1.finrank_eq_two (hP z.1) hz)
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph hgraph)

/-- Constant one-dimensional kernels of continuous idempotents vary
continuously in the Euclidean line topology. Locally they are spanned by
v - P(x)v, with v a nonzero vector in the kernel at the base point. -/
theorem kernel_starProjection_continuous {X : Type*} [TopologicalSpace X]
    (P : X → (E →L[ℝ] E)) (hP : Continuous P)
    (hid : ∀ x, (P x).comp (P x) = P x)
    (hrank : ∀ x, Module.finrank ℝ (P x).toLinearMap.ker = 1) :
    Continuous (fun x => (P x).toLinearMap.ker.starProjection) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hpos : 0 < Module.finrank ℝ (P a).toLinearMap.ker := by rw [hrank]; decide
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hvE : (v : E) ≠ 0 := fun h => hv (Subtype.ext h)
  have hPv : P a v = 0 := v.property
  let w : X → E := fun x => (v : E) - P x v
  have hw : Continuous w := continuous_const.sub (hP.clm_apply continuous_const)
  have hwa : w a = v := by simp [w, hPv]
  have hne : ∀ᶠ x in 𝓝 a, w x ≠ 0 :=
    (isOpen_ne_fun hw continuous_const).mem_nhds (by change w a ≠ 0; rw [hwa]; exact hvE)
  have hmem : ∀ x, w x ∈ (P x).toLinearMap.ker := by
    intro x
    change P x ((v : E) - P x v) = 0
    have h := congrArg (fun A : E →L[ℝ] E => A v) (hid x)
    simpa [map_sub] using sub_eq_zero.mpr h.symm
  have hformula : ∀ᶠ x in 𝓝 a,
      (P x).toLinearMap.ker.starProjection =
        (‖w x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (w x) (w x) := by
    filter_upwards [hne] with x hx
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one (hrank x) (hmem x) hx
    simp only [hspan]
    ext z
    simp [Submodule.starProjection_singleton, div_eq_mul_inv, smul_smul, mul_comm]
  have hcont : ContinuousAt (fun x =>
      (‖w x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (w x) (w x)) a := by
    have hs : ContinuousAt (fun x => (‖w x‖ ^ 2)⁻¹) a :=
      (hw.norm.pow 2).continuousAt.inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (by
        rw [hwa]; exact hvE)))
    have hr : ContinuousAt (fun x => InnerProductSpace.rankOne ℝ (w x) (w x)) a :=
      ((ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
        ((innerSL ℝ).continuous.comp hw) hw).continuousAt
    exact hs.smul hr
  exact hcont.congr_of_eventuallyEq hformula

/-- Full continuity conclusion, with the kernels proved to be lines. -/
theorem projection_continuity : continuityType.{u} := by
  intro E _ _ _ K hK
  classical
  choose P hP using fun L : CentralPlane E => hK.2.2 L.subspace L.finrank_eq_two
  have hcont : Continuous P := bodyProjection_family_continuous hK P hP
  have hker : ∀ L, Module.finrank ℝ (P L).toLinearMap.ker = 1 := by
    intro L
    have hsum := (P L).toLinearMap.finrank_range_add_finrank_ker
    rw [(bodyProjection_algebra K L.subspace (P L) (hP L)).1,
      L.finrank_eq_two, hK.1] at hsum
    omega
  exact ⟨P, hP, hcont, hker, kernel_starProjection_continuous P hcont
    (fun L => (bodyProjection_algebra K L.subspace (P L) (hP L)).2) hker⟩

end ExpandedFA.HilbertCharacterization
