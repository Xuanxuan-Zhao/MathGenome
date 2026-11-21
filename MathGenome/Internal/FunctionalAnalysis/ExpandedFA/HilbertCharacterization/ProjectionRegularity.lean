import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ProjectionRegularity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.ProjectionUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Dual

namespace ExpandedFA.HilbertCharacterization

universe u
open Set Metric Filter
open scoped Topology
open Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
open Specs.ExpandedFA.HilbertCharacterization.ProjectionRegularity

section Normed
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalize any nonzero supporting functional at a point of the boundary.
The strict positivity follows from the inner ball, not from regularity. -/
theorem exists_normalized_support {K : Set E} (hK : SymmetricConvexBody K)
    {p : E} (hp : p ∈ frontier K) :
    ∃ f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1 := by
  obtain ⟨f, hf, hfn⟩ := normalCone_nonzero K p hK hp
  have hpos := normalCone_positive K p hK.2.2.2 f hf hfn
  refine ⟨(f p)⁻¹ • f, ?_, ?_⟩
  · intro x hx
    exact mul_le_mul_of_nonneg_left (hf x hx) (inv_nonneg.mpr hpos.le)
  · simp [hpos.ne']

/-- The supporting-normal relation has closed graph. -/
theorem isClosed_normalCone_graph (K : Set E) :
    IsClosed {z : E × (E →L[ℝ] ℝ) | z.2 ∈ NormalCone K z.1} := by
  have heq : {z : E × (E →L[ℝ] ℝ) | z.2 ∈ NormalCone K z.1} =
      ⋂ x ∈ K, {z : E × (E →L[ℝ] ℝ) | z.2 x ≤ z.2 z.1} := by
    ext z
    simp [NormalCone]
  rw [heq]
  exact isClosed_biInter fun x _ => isClosed_le
    (continuous_snd.clm_apply continuous_const)
    (continuous_snd.clm_apply continuous_fst)

/-- Every boundary point has an outward unit supporting conormal. -/
theorem exists_unit_support {K : Set E} (hK : SymmetricConvexBody K)
    {p : E} (hp : p ∈ frontier K) :
    ∃ f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ ‖f‖ = 1 := by
  obtain ⟨f, hf, hfn⟩ := normalCone_nonzero K p hK hp
  refine ⟨‖f‖⁻¹ • f, ?_, ?_⟩
  · intro x hx
    exact mul_le_mul_of_nonneg_left (hf x hx) (inv_nonneg.mpr (norm_nonneg f))
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg f)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hfn)

/-- Normalization by contact value and by Euclidean norm give the same notion
of uniqueness of the supporting plane. -/
theorem unit_support_unique_of_normalized_support_unique {K : Set E}
    (hzero : (0 : E) ∈ interior K) {p : E}
    (huniq : ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1)
    {f g : E →L[ℝ] ℝ} (hf : f ∈ NormalCone K p) (hg : g ∈ NormalCone K p)
    (hfn : ‖f‖ = 1) (hgn : ‖g‖ = 1) : f = g := by
  have hfp : 0 < f p := normalCone_positive K p hzero f hf (by
    intro h; simp [h] at hfn)
  have hgp : 0 < g p := normalCone_positive K p hzero g hg (by
    intro h; simp [h] at hgn)
  have hnf : (f p)⁻¹ • f ∈ NormalCone K p := by
    intro x hx
    exact mul_le_mul_of_nonneg_left (hf x hx) (inv_nonneg.mpr hfp.le)
  have hng : (g p)⁻¹ • g ∈ NormalCone K p := by
    intro x hx
    exact mul_le_mul_of_nonneg_left (hg x hx) (inv_nonneg.mpr hgp.le)
  have heq : (f p)⁻¹ • f = (g p)⁻¹ • g :=
    huniq.unique ⟨hnf, by simp [hfp.ne']⟩ ⟨hng, by simp [hgp.ne']⟩
  have hnorm := congrArg norm heq
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hfp,
    abs_of_pos hgp, hfn, hgn, mul_one] at hnorm
  have heval : f p = g p := inv_injective hnorm
  rw [← heval] at heq
  exact (smul_right_injective _ (inv_ne_zero hfp.ne')) heq

/-- A continuous choice of supporting linear minorants differentiates their
common upper envelope at every contact point. This is the two-support
inequality, with no differentiability assumption on the envelope. -/
theorem hasFDerivAt_of_continuous_support {a : E} {F : E → ℝ}
    {s : E → (E →L[ℝ] ℝ)} (hs : ContinuousAt s a)
    (hcontact : ∀ᶠ y in 𝓝 a, s y y = F y)
    (hsupport : ∀ᶠ y in 𝓝 a, ∀ z, s y z ≤ F z) :
    HasFDerivAt F (s a) a := by
  have hca : s a a = F a := hcontact.self_of_nhds
  have hsa : ∀ z, s a z ≤ F z := hsupport.self_of_nhds
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝 a, ‖s y - s a‖ < ε := by
    have ht : ContinuousAt (fun y => ‖s y - s a‖) a :=
      (hs.sub continuousAt_const).norm
    have h := ht.eventually (gt_mem_nhds (by simpa using hε))
    simpa using h
  filter_upwards [hcontact, hsupport, hsmall] with y hcy hsy hdist
  have hlow : 0 ≤ F y - F a - s a (y - a) := by
    rw [map_sub, hca]
    linarith [hsa y]
  have hupp : F y - F a - s a (y - a) ≤ (s y - s a) (y - a) := by
    simp only [sub_apply, map_sub]
    linarith [hsy a]
  rw [Real.norm_eq_abs, abs_of_nonneg hlow]
  exact hupp.trans ((le_abs_self _).trans ((s y - s a).le_opNorm _)) |>.trans
    (mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _))

/-- At a smooth contact point the support is fixed by every admissible
projection onto a subspace through that point. -/
theorem normalized_support_fixed_by_projection {K : Set E} {p : E}
    (huniq : ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1)
    (L : Submodule ℝ E) (P : E →L[ℝ] E) (hP : BodyProjection K L P)
    (hpL : p ∈ L) {f : E →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1) : f.comp P = f := by
  apply huniq.unique _ ⟨hf, hfp⟩
  constructor
  · intro x hx
    change f (P x) ≤ f (P p)
    rw [hP.2.1 p hpL]
    exact hf (P x) (hP.2.2 hx)
  · change f (P p) = 1
    rw [hP.2.1 p hpL, hfp]

/-- Normalized supporting functionals have one common bound from the inner
Euclidean ball. This controls all possible limits, including at corners. -/
theorem normalized_support_norm_le {K : Set E} {p : E} {r : ℝ}
    (hr : 0 < r) (hin : closedBall (0 : E) r ⊆ K)
    {f : E →L[ℝ] ℝ} (hf : f ∈ NormalCone K p) (hfp : f p = 1) :
    ‖f‖ ≤ r⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (inv_nonneg.mpr hr.le)
  intro x hx
  have hmem : ∀ y : E, ‖y‖ = 1 → r • y ∈ K := by
    intro y hy
    apply hin
    simp [mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hy]
  have hu : r * f x ≤ 1 := by
    simpa [map_smul, hfp] using hf (r • x) (hmem x hx)
  have hl : -(r * f x) ≤ 1 := by
    simpa [map_smul, hfp] using hf (r • -x) (hmem (-x) (by simpa using hx))
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hb : -1 ≤ r * f x := by linarith
    have h := (div_le_iff₀ hr).mpr (by simpa [mul_comm] using hb)
    simpa [div_eq_mul_inv, mul_comm] using h
  · have h := (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hu)
    simpa [one_div, mul_comm] using h

/-- Closedness of the full supporting relation and of the normalization
passes contact to limits. This applies to arbitrary nontrivial filters. -/
theorem normalized_support_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Set E} {q : ι → E} {s : ι → (E →L[ℝ] ℝ)} {p : E} {f : E →L[ℝ] ℝ}
    (hq : Tendsto q l (𝓝 p)) (hs : Tendsto s l (𝓝 f))
    (h : ∀ᶠ i in l, s i ∈ NormalCone K (q i) ∧ s i (q i) = 1) :
    f ∈ NormalCone K p ∧ f p = 1 := by
  constructor
  · exact (isClosed_normalCone_graph K).mem_of_tendsto
      (hq.prodMk_nhds hs) (h.mono fun _ hi => hi.1)
  · exact tendsto_nhds_unique (((continuous_fst.clm_apply continuous_snd).tendsto (f, p)).comp
      (hs.prodMk_nhds hq))
      (tendsto_const_nhds.congr' (h.mono fun _ hi => hi.2.symm))

/-- Fixed-support identities also pass to limits of operators. The separate
geometric task is to construct central planes through the varying contacts. -/
theorem support_fixed_by_projection_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {s : ι → (E →L[ℝ] ℝ)} {Q : ι → (E →L[ℝ] E)}
    {f : E →L[ℝ] ℝ} {P : E →L[ℝ] E}
    (hs : Tendsto s l (𝓝 f)) (hQ : Tendsto Q l (𝓝 P))
    (h : ∀ᶠ i in l, (s i).comp (Q i) = s i) : f.comp P = f := by
  exact tendsto_nhds_unique (((continuous_fst.clm_comp continuous_snd).tendsto (f, P)).comp
      (hs.prodMk_nhds hQ))
    (hs.congr' (h.mono fun _ hi => hi.symm))

end Normed

section FiniteDimensional
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A unique supporting plane implies continuity of the unit conormal.
The codomain unit sphere is compact in finite dimension, and the graph is
closed. This statement assumes uniqueness explicitly and does not purport to
prove the geometric rigidity step. -/
theorem continuous_unit_support_of_unique {K : Set E} (hK : SymmetricConvexBody K)
    (huniq : ∀ p ∈ frontier K,
      ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1) :
    ∃ n : frontier K → (E →L[ℝ] ℝ), Continuous n ∧
      ∀ p : frontier K, n p ∈ NormalCone K (p : E) ∧ ‖n p‖ = 1 ∧
        ∀ g ∈ NormalCone K (p : E), ‖g‖ = 1 → g = n p := by
  classical
  choose n hn hnorm using fun p : frontier K => exists_unit_support hK p.property
  let S : Set (E →L[ℝ] ℝ) := sphere 0 1
  have hS : IsCompact S := isCompact_sphere _ _
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let N : frontier K → S := fun p => ⟨n p, by simpa [S, mem_sphere, dist_eq_norm] using hnorm p⟩
  have hgraph : IsClosed N.graph := by
    have hc : IsClosed {z : frontier K × S |
        (z.2 : E →L[ℝ] ℝ) ∈ NormalCone K (z.1 : E)} :=
      (isClosed_normalCone_graph K).preimage
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))
    convert hc using 1
    ext z
    change N z.1 = z.2 ↔ (z.2 : E →L[ℝ] ℝ) ∈ NormalCone K (z.1 : E)
    constructor
    · intro hz
      exact hz ▸ hn z.1
    · intro hz
      apply Subtype.ext
      exact unit_support_unique_of_normalized_support_unique hK.2.2.2
        (huniq z.1 z.1.property) (hn z.1) hz (hnorm z.1)
        (by simpa [S, mem_sphere, dist_eq_norm] using z.2.property)
  refine ⟨n, continuous_subtype_val.comp (continuous_of_isClosed_graph hgraph), ?_⟩
  intro p
  exact ⟨hn p, hnorm p, fun g hg hgn =>
    unit_support_unique_of_normalized_support_unique hK.2.2.2
      (huniq p p.property) hg (hn p) hgn (hnorm p)⟩

/-- Supporting functionals of the gauge, with contact at a nonzero point,
are precisely the value-normalized normals at its radial boundary point. -/
theorem unique_gauge_support_of_unique {K : Set E} (hK : SymmetricConvexBody K)
    (huniq : ∀ p ∈ frontier K,
      ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1)
    {x : E} (hx : x ≠ 0) :
    ∃! f : E →L[ℝ] ℝ, (∀ y, f y ≤ gauge K y) ∧ f x = gauge K x := by
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.2.2
  have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK
  have hpos : 0 < gauge K x :=
    (div_pos (norm_pos_iff.mpr hx) hR).trans_le
      (le_gauge_of_subset_closedBall ha hR.le hout)
  let p : E := (gauge K x)⁻¹ • x
  have hp : p ∈ frontier K := by
    apply (gauge_eq_one_iff_mem_frontier hK.2.1 hzero).mp
    simp [p, gauge_smul_of_nonneg (inv_nonneg.mpr hpos.le), hpos.ne']
  obtain ⟨f, ⟨hf, hfp⟩, hfu⟩ := huniq p hp
  have hfx : f x = gauge K x := by
    have h := congrArg (fun a : ℝ => gauge K x * a) hfp
    simpa [p, map_smul, ← mul_assoc, hpos.ne'] using h
  refine ⟨f, ⟨normal_le_gauge ha hf hfp, hfx⟩, ?_⟩
  rintro g ⟨hg, hgx⟩
  have hgp : g p = 1 := by simp [p, map_smul, hgx, hpos.ne']
  apply hfu
  refine ⟨?_, hgp⟩
  intro y hy
  rw [hgp]
  exact (hg y).trans (gauge_le_one_of_mem hy)

/-- In finite dimension uniqueness of all supporting planes gives a continuous
family of supporting linear minorants of the gauge away from zero. -/
theorem continuous_gauge_support_of_unique {K : Set E} (hK : SymmetricConvexBody K)
    (huniq : ∀ p ∈ frontier K,
      ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1) :
    ∃ F : E → (E →L[ℝ] ℝ), ContinuousOn F {x | x ≠ 0} ∧
      ∀ x, (∀ y, F x y ≤ gauge K y) ∧ F x x = gauge K x := by
  classical
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.2.2
  have hgauge : Continuous (gauge K) := continuous_gauge hK.2.1 hzero
  have hex : ∀ x : E, ∃ f : E →L[ℝ] ℝ,
      (∀ y, f y ≤ gauge K y) ∧ f x = gauge K x := by
    intro x
    by_cases hx : x = 0
    · subst x
      exact ⟨0, fun y => by simpa using gauge_nonneg (s := K) y, by simp⟩
    · exact (unique_gauge_support_of_unique hK huniq hx).exists
  choose F hF using hex
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK
  have hbound : ∀ x : E, x ≠ 0 → ‖F x‖ ≤ r⁻¹ := by
    intro x hx
    have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
    have hpos : 0 < gauge K x :=
      (div_pos (norm_pos_iff.mpr hx) hR).trans_le
        (le_gauge_of_subset_closedBall ha hR.le hout)
    let p : E := (gauge K x)⁻¹ • x
    have hfp : F x p = 1 := by simp [p, map_smul, (hF x).2, hpos.ne']
    apply normalized_support_norm_le hr hin (p := p) _ hfp
    intro y hy
    rw [hfp]
    exact ((hF x).1 y).trans (gauge_le_one_of_mem hy)
  let X := {x : E | x ≠ 0}
  let B : Set (E →L[ℝ] ℝ) := closedBall 0 r⁻¹
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let N : X → B := fun x => ⟨F x, by
    simpa [B, mem_closedBall, dist_eq_norm] using hbound x x.property⟩
  have hgraph : IsClosed N.graph := by
    have hc : IsClosed {z : X × B |
        (∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y) ∧
          (z.2 : E →L[ℝ] ℝ) (z.1 : E) = gauge K (z.1 : E)} := by
      have h₁ : IsClosed {z : X × B | ∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} := by
        have heq : {z : X × B | ∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} =
            ⋂ y : E, {z : X × B | (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} := by
          ext z
          simp
        rw [heq]
        exact isClosed_iInter fun y => isClosed_le
          ((continuous_subtype_val.comp continuous_snd).clm_apply continuous_const)
          continuous_const
      exact h₁.inter (isClosed_eq
        ((continuous_subtype_val.comp continuous_snd).clm_apply
          (continuous_subtype_val.comp continuous_fst))
        (hgauge.comp (continuous_subtype_val.comp continuous_fst)))
    convert hc using 1
    ext z
    change N z.1 = z.2 ↔
      (∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y) ∧
        (z.2 : E →L[ℝ] ℝ) (z.1 : E) = gauge K (z.1 : E)
    constructor
    · intro hz
      exact hz ▸ hF z.1
    · intro hz
      exact Subtype.ext ((unique_gauge_support_of_unique hK huniq z.1.property).unique
        (hF z.1) hz)
  exact ⟨F, continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp (continuous_of_isClosed_graph hgraph)), hF⟩

/-- For a finite-dimensional convex body, unique supporting planes imply that
its gauge is C¹ away from zero. The derivative comes from the support inequality,
not from an assumed smooth norm. -/
theorem contDiffOn_gauge_of_unique {K : Set E} (hK : SymmetricConvexBody K)
    (huniq : ∀ p ∈ frontier K,
      ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1) :
    ContDiffOn ℝ 1 (gauge K) {x | x ≠ 0} := by
  obtain ⟨F, hcont, hF⟩ := continuous_gauge_support_of_unique hK huniq
  have hopen : IsOpen {x : E | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hd : ∀ x : E, x ≠ 0 → HasFDerivAt (gauge K) (F x) x := by
    intro x hx
    exact hasFDerivAt_of_continuous_support (hcont.continuousAt (hopen.mem_nhds hx))
      (Eventually.of_forall fun y => (hF y).2) (Eventually.of_forall fun y => (hF y).1)
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  exact contDiffAt_one_iff.mpr ⟨F, {x : E | x ≠ 0}, hopen.mem_nhds hx,
    hcont, hd⟩

end FiniteDimensional

/-- Explicit radial-transverse local C¹ graphs follow from unique support.
This is an ordinary implicit-function application to the gauge, whose C¹
regularity has already been proved from the support inequalities. -/
theorem boundary_local_graph_of_unique
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : SymmetricConvexBody K)
    (hdim : Module.finrank ℝ E = 3)
    (huniq : ∀ p ∈ frontier K,
      ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1)
    {p : E} (hp : p ∈ frontier K) :
    ∃ f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1 ∧
      Module.finrank ℝ f.ker = 2 ∧
      ∃ (U : Set f.ker) (V : Set E) (h : f.ker → ℝ),
        IsOpen U ∧ (0 : f.ker) ∈ U ∧ IsOpen V ∧ p ∈ V ∧
        ContDiffOn ℝ 1 h U ∧ h 0 = 0 ∧
        HasFDerivAt h (0 : f.ker →L[ℝ] ℝ) 0 ∧
        ∀ x ∈ V, x ∈ frontier K ↔ ∃ y ∈ U, x = p + (y : E) + h y • p := by
  obtain ⟨f, ⟨hf, hfp⟩, _hfu⟩ := huniq p hp
  have hpne : p ≠ 0 := by intro h; simp [h] at hfp
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro t
    exact ⟨t • p, by simp [map_smul, hfp]⟩
  have hker : Module.finrank ℝ f.ker = 2 := by
    have h := f.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at h
    omega
  let H := f.ker
  let A : H × ℝ →L[ℝ] E :=
    H.subtypeL.comp (ContinuousLinearMap.fst ℝ H ℝ) +
      (ContinuousLinearMap.toSpanSingleton ℝ p).comp (ContinuousLinearMap.snd ℝ H ℝ)
  have hA : ∀ z : H × ℝ, A z = (z.1 : E) + z.2 • p := by
    intro z
    rfl
  let G : H × ℝ → ℝ := fun z => gauge K (p + A z)
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.2.2
  have hgaugep : gauge K p = 1 := (gauge_eq_one_iff_mem_frontier hK.2.1 hzero).mpr hp
  have hopen : IsOpen {x : E | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hgauge : ContDiffAt ℝ 1 (gauge K) p :=
    (contDiffOn_gauge_of_unique hK huniq).contDiffAt (hopen.mem_nhds hpne)
  have hdf : HasFDerivAt (gauge K) f p := by
    have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
    have heq := normal_eq_fderiv_gauge ha (hgauge.differentiableAt one_ne_zero) hf hfp
      (hfp.trans hgaugep.symm)
    rw [heq]
    exact (hgauge.differentiableAt one_ne_zero).hasFDerivAt
  have hG : ContDiffAt ℝ 1 G (0, 0) := by
    have hh : ContDiffAt ℝ 1 (gauge K) (p + A (0, 0)) := by simpa [hA] using hgauge
    exact ContDiffAt.comp (f := fun z : H × ℝ => p + A z) (g := gauge K)
      (0, 0) hh (contDiffAt_const.add A.contDiff.contDiffAt)
  have hDG : fderiv ℝ G (0, 0) = ContinuousLinearMap.snd ℝ H ℝ := by
    have hdA : HasFDerivAt (fun z : H × ℝ => p + A z) A (0, 0) := by
      convert! (hasFDerivAt_const p (0 : H × ℝ)).add A.hasFDerivAt using 1; simp
    have hdf' : HasFDerivAt (gauge K) f (p + A (0, 0)) := by simpa [hA] using hdf
    have h := hdf'.comp (0, 0) hdA
    have hcomp : f.comp A = ContinuousLinearMap.snd ℝ H ℝ := by
      apply ContinuousLinearMap.ext
      intro z
      change f (A z) = z.2
      simp [hA, map_add, map_smul, hfp, show f (z.1 : E) = 0 from z.1.property]
    change fderiv ℝ (gauge K ∘ fun z : H × ℝ => p + A z) (0, 0) = _
    exact h.fderiv.trans hcomp
  have hinv : (fderiv ℝ G (0, 0) ∘L ContinuousLinearMap.inr ℝ H ℝ).IsInvertible := by
    rw [hDG]
    have heq : (ContinuousLinearMap.snd ℝ H ℝ).comp (ContinuousLinearMap.inr ℝ H ℝ) =
        (ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap := by
      rfl
    rw [heq]
    exact ContinuousLinearMap.isInvertible_equiv
  let h : H → ℝ := hG.implicitFunction one_ne_zero hinv
  have hh0 : h 0 = 0 := hG.implicitFunction_apply_self one_ne_zero hinv
  have hhD : HasFDerivAt h (0 : H →L[ℝ] ℝ) 0 := by
    have hd := (hG.hasStrictFDerivAt_implicitFunction one_ne_zero hinv).hasFDerivAt
    convert hd using 1
    rw [hDG]
    ext y
    simp
  have hhC : ContDiffAt ℝ 1 h 0 := hG.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨U₀, hU₀, hhCU₀⟩ := hhC.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUU, hU, h0U⟩ := _root_.mem_nhds_iff.mp hU₀
  have hEq := hG.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv
  obtain ⟨W, hWsub, hW, h0W⟩ := _root_.mem_nhds_iff.mp hEq
  let C : E → H × ℝ := fun x =>
    (⟨x - p - f (x - p) • p, by simp [H, map_sub, map_smul, hfp]⟩, f (x - p))
  have hC : Continuous C := by
    apply Continuous.prodMk
    · exact ((continuous_id.sub continuous_const).sub
        ((f.continuous.comp (continuous_id.sub continuous_const)).smul continuous_const)).subtype_mk _
    · exact f.continuous.comp (continuous_id.sub continuous_const)
  have hCp : C p = (0, 0) := by simp [C]
  have hAC : ∀ x : E, p + A (C x) = x := by
    intro x
    rw [hA]
    dsimp [C]
    abel
  have hCA : ∀ z : H × ℝ, C (p + A z) = z := by
    rintro ⟨y, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [C, hA, map_add, map_smul, hfp, show f (y : E) = 0 from y.property]
    · simp [C, hA, map_add, map_smul, hfp, show f (y : E) = 0 from y.property]
  let V : Set E := C ⁻¹' (W ∩ (U ×ˢ univ)) ∩ {x | x ≠ 0}
  have hV : IsOpen V := ((hW.inter (hU.prod isOpen_univ)).preimage hC).inter hopen
  have hpV : p ∈ V := by
    exact ⟨⟨by simpa [hCp] using h0W, by simpa [hCp] using h0U⟩, hpne⟩
  refine ⟨f, hf, hfp, hker, U, V, h, hU, h0U, hV, hpV, hhCU₀.mono hUU,
    hh0, hhD, ?_⟩
  intro x hx
  have hxW : C x ∈ W := hx.1.1
  have hxU : (C x).1 ∈ U := hx.1.2.1
  have hEqx : gauge K x = 1 ↔ h (C x).1 = (C x).2 := by
    have heq := hWsub hxW
    change (gauge K (p + A (C x)) = gauge K (p + A (0, 0)) ↔
      h (C x).1 = (C x).2) at heq
    rw [hAC] at heq
    simpa [hA, hgaugep] using heq
  rw [← gauge_eq_one_iff_mem_frontier hK.2.1 hzero, hEqx]
  constructor
  · intro heq
    refine ⟨(C x).1, hxU, ?_⟩
    have hh := hAC x
    rw [hA] at hh
    rw [heq]
    simpa only [add_assoc] using hh.symm
  · rintro ⟨y, hy, hxy⟩
    have hCx : C x = (y, h y) := by
      rw [hxy]
      simpa [hA, add_assoc] using hCA (y, h y)
    simp [hCx]

section PlaneVariation
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
open Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness

/-- A central plane through p can be moved continuously to pass through nearby
points. The formula adjusts a Euclidean normal without assuming body regularity. -/
theorem exists_continuous_plane_through (hdim : Module.finrank ℝ E = 3)
    {p : E} (hpne : p ≠ 0) (L : CentralPlane E) (hpL : p ∈ L.subspace) :
    ∃ (U : Set E) (hU : IsOpen U) (hpU : p ∈ U) (M : U → CentralPlane E),
      Continuous M ∧ M ⟨p, hpU⟩ = L ∧ ∀ x : U, (x : E) ∈ (M x).subspace := by
  have hdimperp : Module.finrank ℝ L.subspaceᗮ = 1 := by
    have h := L.subspace.finrank_add_finrank_orthogonal
    rw [L.finrank_eq_two, hdim] at h
    omega
  obtain ⟨n, hn⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega :
    0 < Module.finrank ℝ L.subspaceᗮ)
  have hnE : (n : E) ≠ 0 := fun h => hn (Subtype.ext h)
  have hnp : inner ℝ (n : E) p = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpL n.property
  have hpp : inner ℝ p p ≠ 0 := inner_self_ne_zero.mpr hpne
  let v : E → E := fun x => (n : E) - (inner ℝ (n : E) x / inner ℝ p x) • p
  have hvp : v p = n := by simp [v, hnp]
  have hvcont : ∀ x : E, inner ℝ p x ≠ 0 → ContinuousAt v x := by
    intro x hx
    exact continuousAt_const.sub
      (((continuous_const.inner continuous_id).continuousAt.div
        (continuous_const.inner continuous_id).continuousAt hx).smul continuousAt_const)
  let U : Set E := {x | inner ℝ p x ≠ 0 ∧ v x ≠ 0}
  have hpU : p ∈ U := ⟨hpp, by rw [hvp]; exact hnE⟩
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have h₁ : ∀ᶠ y in 𝓝 x, inner ℝ p y ≠ 0 :=
      (isOpen_ne_fun (continuous_const.inner continuous_id) continuous_const).mem_nhds hx.1
    have h₂ : ∀ᶠ y in 𝓝 x, v y ≠ 0 :=
      (hvcont x hx.1).eventually (compl_singleton_mem_nhds hx.2)
    exact h₁.and h₂
  have hdimv : ∀ x : U, Module.finrank ℝ (ℝ ∙ v x)ᗮ = 2 := by
    intro x
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_span_singleton x.property.2, hdim]
  let M : U → CentralPlane E := fun x => ⟨(ℝ ∙ v x)ᗮ, hdimv x⟩
  have hvU : Continuous (fun x : U => v x) := by
    exact continuous_iff_continuousAt.mpr fun x =>
      (hvcont x x.property.1).comp continuous_subtype_val.continuousAt
  have hproj : ∀ x : U, (M x).subspace.starProjection =
      ContinuousLinearMap.id ℝ E -
        (‖v x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (v x) (v x) := by
    intro x
    rw [Submodule.starProjection_orthogonal]
    congr 1
    apply ContinuousLinearMap.ext
    intro y
    simp [Submodule.starProjection_singleton, div_eq_mul_inv, smul_smul, mul_comm]
  have hMc : Continuous M := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : U => (M x).subspace.starProjection)
    simp_rw [hproj]
    have hinv : Continuous (fun x : U => (‖v x‖ ^ 2)⁻¹) :=
      (hvU.norm.pow 2).inv₀ (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr x.property.2))
    have hr : Continuous (fun x : U => InnerProductSpace.rankOne ℝ (v x) (v x)) :=
      (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂
        ((innerSL ℝ).continuous.comp hvU) hvU
    exact continuous_const.sub (hinv.smul hr)
  have hMp : M ⟨p, hpU⟩ = L := by
    have hspan : L.subspaceᗮ = ℝ ∙ (n : E) :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdimperp n.property hnE
    have heq : (M ⟨p, hpU⟩).subspace = L.subspace := by
      change (ℝ ∙ v p)ᗮ = L.subspace
      rw [hvp, ← hspan, Submodule.orthogonal_orthogonal]
    have hext : ∀ (A B : CentralPlane E), A.subspace = B.subspace → A = B := by
      rintro ⟨S, hS⟩ ⟨T, hT⟩ h
      cases h
      rfl
    exact hext _ _ heq
  refine ⟨U, hU, hpU, M, hMc, hMp, ?_⟩
  intro x
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change inner ℝ (v x) (x : E) = 0
  simp only [v, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
  field_simp [x.property.1]
  simp

/-- Existence of a gauge support at every nonzero vector, with no uniqueness
or smoothness assumption on the body. -/
theorem exists_gauge_support {K : Set E} (hK : SymmetricConvexBody K)
    {x : E} (hx : x ≠ 0) :
    ∃ f : E →L[ℝ] ℝ, (∀ y, f y ≤ gauge K y) ∧ f x = gauge K x := by
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.2.2
  have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK
  have hpos : 0 < gauge K x :=
    (div_pos (norm_pos_iff.mpr hx) hR).trans_le
      (le_gauge_of_subset_closedBall ha hR.le hout)
  let p : E := (gauge K x)⁻¹ • x
  have hp : p ∈ frontier K := by
    apply (gauge_eq_one_iff_mem_frontier hK.2.1 hzero).mp
    simp [p, gauge_smul_of_nonneg (inv_nonneg.mpr hpos.le), hpos.ne']
  obtain ⟨f, hf, hfp⟩ := exists_normalized_support hK hp
  refine ⟨f, normal_le_gauge ha hf hfp, ?_⟩
  have h := congrArg (fun a : ℝ => gauge K x * a) hfp
  simpa [p, map_smul, ← mul_assoc, hpos.ne'] using h

/-- A gauge minorant has the same uniform bound as normalized body normals. -/
theorem gauge_support_norm_le {K : Set E} {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : E) r ⊆ K) {f : E →L[ℝ] ℝ}
    (hf : ∀ y, f y ≤ gauge K y) : ‖f‖ ≤ r⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (inv_nonneg.mpr hr.le)
  intro x hx
  have hu : ∀ y : E, ‖y‖ = 1 → r * f y ≤ 1 := by
    intro y hy
    have hmem : r • y ∈ K := hin (by
      simp [mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hy])
    have h := (hf (r • y)).trans (gauge_le_one_of_mem hmem)
    simpa [map_smul] using h
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h : -1 ≤ f x * r := by have h := hu (-x) (by simpa using hx); simpa [mul_comm] using neg_le_neg h
    simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hr).mpr h
  · have h : f x * r ≤ 1 := by simpa [mul_comm] using hu x hx
    simpa [one_div] using (le_div_iff₀ hr).mpr h

/-- At a differentiability point of the gauge every contact minorant is fixed
by projections onto central planes through that vector. -/
theorem gauge_support_fixed_of_differentiable {K : Set E} (hK : ProjectionBody K)
    {x : E} (hx : x ≠ 0) (hd : DifferentiableAt ℝ (gauge K) x)
    {f : E →L[ℝ] ℝ} (hf : ∀ y, f y ≤ gauge K y) (hfx : f x = gauge K x)
    (L : CentralPlane E) (hxL : x ∈ L.subspace)
    (P : E →L[ℝ] E) (hP : BodyProjection K L.subspace P) : f.comp P = f := by
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2
  have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK.2.1
  have hpos : 0 < gauge K x :=
    (div_pos (norm_pos_iff.mpr hx) hR).trans_le
      (le_gauge_of_subset_closedBall ha hR.le hout)
  let p : E := (gauge K x)⁻¹ • x
  have hfp : f p = 1 := by simp [p, map_smul, hfx, hpos.ne']
  have hfn : f ∈ NormalCone K p := by
    intro y hy
    rw [hfp]
    exact (hf y).trans (gauge_le_one_of_mem hy)
  have huniq : ∃! g : E →L[ℝ] ℝ, g ∈ NormalCone K p ∧ g p = 1 := by
    refine ⟨f, ⟨hfn, hfp⟩, ?_⟩
    rintro g ⟨hg, hgp⟩
    have hgx : g x = gauge K x := by
      have h := congrArg (fun a : ℝ => gauge K x * a) hgp
      simpa [p, map_smul, ← mul_assoc, hpos.ne'] using h
    exact (normal_eq_fderiv_gauge ha hd hg hgp hgx).trans
      (normal_eq_fderiv_gauge ha hd hfn hfp hfx).symm
  exact normalized_support_fixed_by_projection huniq L.subspace P hP
    (L.subspace.smul_mem _ hxL) hfn hfp

/-- All projection pullback identities and one nonzero contact value determine
a functional uniquely. Apply the identity for the plane ker(f-g). -/
theorem eq_of_all_plane_pullbacks (hdim : Module.finrank ℝ E = 3)
    {p : E} {f g : E →L[ℝ] ℝ} (hval : f p = g p)
    (P : CentralPlane E → (E →L[ℝ] E))
    (hP : ∀ L, ∀ x, P L x ∈ L.subspace)
    (hf : ∀ L, p ∈ L.subspace → f.comp (P L) = f)
    (hg : ∀ L, p ∈ L.subspace → g.comp (P L) = g) : f = g := by
  by_contra hne
  let d : E →L[ℝ] ℝ := f - g
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hrange : LinearMap.range d.toLinearMap = ⊤ := by
    exact Module.Dual.range_eq_top_of_ne_zero (by exact_mod_cast hd)
  have hker : Module.finrank ℝ d.ker = 2 := by
    have h := d.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at h
    omega
  let L : CentralPlane E := ⟨d.ker, hker⟩
  have hpL : p ∈ L.subspace := by change f p - g p = 0; exact sub_eq_zero.mpr hval
  have hfL := hf L hpL
  have hgL := hg L hpL
  apply hd
  apply ContinuousLinearMap.ext
  intro x
  have hx : d (P L x) = 0 := hP L x
  have hfx := congrArg (fun a : E →L[ℝ] ℝ => a x) hfL
  have hgx := congrArg (fun a : E →L[ℝ] ℝ => a x) hgL
  change f x - g x = 0
  change f (P L x) - g (P L x) = 0 at hx
  change f (P L x) = f x at hfx
  change g (P L x) = g x at hgx
  rwa [← hfx, ← hgx]

/-- Close the graph of supports at differentiability points of the gauge.
Projection continuity forces each fiber of the closed graph to be a singleton;
compactness then provides a continuous supporting selection everywhere away
from zero. No support uniqueness at nonsmooth points is assumed here. -/
theorem projection_continuous_gauge_support {K : Set E} (hK : ProjectionBody K) :
    ∃ F : E → (E →L[ℝ] ℝ), ContinuousOn F {x | x ≠ 0} ∧
      ∀ x, (∀ y, F x y ≤ gauge K y) ∧ F x x = gauge K x := by
  classical
  obtain ⟨P, hP, hPc, _⟩ := projection_continuity K hK
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2
  have hgauge : Continuous (gauge K) := continuous_gauge hK.2.1.2.1 hzero
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK.2.1
  let X := {x : E | x ≠ 0}
  have hX : IsOpen X := isOpen_ne_fun continuous_id continuous_const
  let B : Set (E →L[ℝ] ℝ) := closedBall 0 r⁻¹
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let T : Set (X × B) := {z | (∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y) ∧
    (z.2 : E →L[ℝ] ℝ) (z.1 : E) = gauge K (z.1 : E)}
  have hT : IsClosed T := by
    have h₁ : IsClosed {z : X × B | ∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} := by
      have heq : {z : X × B | ∀ y : E, (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} =
          ⋂ y : E, {z : X × B | (z.2 : E →L[ℝ] ℝ) y ≤ gauge K y} := by ext z; simp
      rw [heq]
      exact isClosed_iInter fun y => isClosed_le
        ((continuous_subtype_val.comp continuous_snd).clm_apply continuous_const) continuous_const
    exact h₁.inter (isClosed_eq
      ((continuous_subtype_val.comp continuous_snd).clm_apply
        (continuous_subtype_val.comp continuous_fst))
      (hgauge.comp (continuous_subtype_val.comp continuous_fst)))
  let S : Set (X × B) := {z | DifferentiableAt ℝ (gauge K) (z.1 : E) ∧ z ∈ T}
  let Γ : Set (X × B) := closure S
  have hΓT : Γ ⊆ T := closure_minimal (fun _ hz => hz.2) hT
  have hfixed : ∀ z ∈ Γ, ∀ L : CentralPlane E, (z.1 : E) ∈ L.subspace →
      (z.2 : E →L[ℝ] ℝ).comp (P L) = (z.2 : E →L[ℝ] ℝ) := by
    intro z hz L hzL
    obtain ⟨U, hU, hpU, M, hMc, hMp, hthrough⟩ :=
      exists_continuous_plane_through hK.1 z.1.property L hzL
    obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.mp hz
    have hq : Tendsto (fun j => ((a j).1 : E)) atTop (𝓝 (z.1 : E)) :=
      (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hat)
    have hs : Tendsto (fun j => ((a j).2 : E →L[ℝ] ℝ)) atTop
        (𝓝 (z.2 : E →L[ℝ] ℝ)) :=
      (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hat)
    have hlate : ∀ᶠ j in atTop, ((a j).1 : E) ∈ U := hq.eventually (hU.mem_nhds hpU)
    let q : ℕ → U := fun j => if hj : ((a j).1 : E) ∈ U then ⟨(a j).1, hj⟩ else ⟨z.1, hpU⟩
    have hqt : Tendsto q atTop (𝓝 ⟨(z.1 : E), hpU⟩) := by
      apply tendsto_subtype_rng.mpr
      exact hq.congr' (hlate.mono fun j hj => by simp [q, hj])
    have hPt : Tendsto (fun j => P (M (q j))) atTop (𝓝 (P L)) := by
      have ht := ((hPc.comp hMc).tendsto ⟨(z.1 : E), hpU⟩).comp hqt
      simpa [hMp, Function.comp_def] using ht
    apply support_fixed_by_projection_of_tendsto hs hPt
    filter_upwards [hlate] with j hj
    have hxL : ((a j).1 : E) ∈ (M (q j)).subspace := by
      have ht := hthrough (q j)
      simpa [q, hj] using ht
    exact gauge_support_fixed_of_differentiable hK (a j).1.property (ha j).1
      (ha j).2.1 (ha j).2.2 (M (q j)) hxL (P (M (q j))) (hP _)
  have hfiber : ∀ x : X, ∀ f g : B, (x, f) ∈ Γ → (x, g) ∈ Γ → f = g := by
    intro x f g hf hg
    apply Subtype.ext
    apply eq_of_all_plane_pullbacks hK.1
      (((hΓT hf).2).trans ((hΓT hg).2).symm) P (fun L => (hP L).1)
    · exact hfixed (x, f) hf
    · exact hfixed (x, g) hg
  have hdense : Dense {x : X | DifferentiableAt ℝ (gauge K) (x : E)} := by
    obtain ⟨C, hC⟩ := hK.2.1.2.1.lipschitz_gauge hzero
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    have hd : Dense {x : E | DifferentiableAt ℝ (gauge K) x} :=
      MeasureTheory.Measure.dense_of_ae
        (hC.ae_differentiableAt (μ := (Module.Basis.ofVectorSpace ℝ E).addHaar))
    exact hd.preimage hX.isOpenMap_subtype_val
  have hex : ∀ x : X, ∃ f : B, (x, f) ∈ Γ := by
    have hclosed : IsClosed (Prod.fst '' Γ) :=
      isClosedMap_fst_of_compactSpace Γ isClosed_closure
    have hdsub : {x : X | DifferentiableAt ℝ (gauge K) (x : E)} ⊆ Prod.fst '' Γ := by
      intro x hx
      obtain ⟨f, hf, hfx⟩ := exists_gauge_support hK.2.1 x.property
      let b : B := ⟨f, by simpa [B, mem_closedBall, dist_eq_norm] using
        gauge_support_norm_le hr hin hf⟩
      exact ⟨(x, b), subset_closure ⟨hx, hf, hfx⟩, rfl⟩
    have hall : (univ : Set X) ⊆ Prod.fst '' Γ := by
      rw [← hdense.closure_eq]
      exact closure_minimal hdsub hclosed
    intro x
    obtain ⟨⟨y, f⟩, hf, hxy⟩ := hall (mem_univ x)
    exact ⟨f, by simpa using hxy ▸ hf⟩
  choose N hN using hex
  have hgraph : IsClosed N.graph := by
    convert (show IsClosed Γ from isClosed_closure) using 1
    ext z
    change N z.1 = z.2 ↔ z ∈ Γ
    constructor
    · intro hz
      change (z.1, z.2) ∈ Γ
      rw [← hz]
      exact hN z.1
    · intro hz
      exact hfiber z.1 (N z.1) z.2 (hN z.1) hz
  have hNc : Continuous N := continuous_of_isClosed_graph hgraph
  let F : E → (E →L[ℝ] ℝ) := fun x => if hx : x ≠ 0 then N ⟨x, hx⟩ else 0
  have hFc : ContinuousOn F X := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun x : X => F x) = fun x : X => (N x : E →L[ℝ] ℝ) := by
      funext x
      simp only [F, dite_eq_left (show (x : E) ≠ 0 from x.property)]
    change Continuous (fun x : X => F x)
    rw [heq]
    exact continuous_subtype_val.comp hNc
  refine ⟨F, hFc, ?_⟩
  intro x
  by_cases hx : x ≠ 0
  · simpa [F, hx, T] using hΓT (hN ⟨x, hx⟩)
  · have hx0 : x = 0 := not_ne_iff.mp hx
    subst x
    exact ⟨fun y => by simpa [F] using gauge_nonneg (s := K) y, by simp [F]⟩

end PlaneVariation

/-- Global supporting-plane uniqueness, obtained without any smoothness premise. -/
theorem projection_supporting_plane_unique : supportingPlaneType.{u} := by
  intro E _ _ _ K hK p hp
  obtain ⟨F, hFc, hF⟩ := projection_continuous_gauge_support hK
  have hpne : p ≠ 0 := by
    intro h
    have hzero := hK.2.1.2.2.2
    have hpnot := hp.2
    exact hpnot (h ▸ hzero)
  have hopen : IsOpen {x : E | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hd : DifferentiableAt ℝ (gauge K) p :=
    (hasFDerivAt_of_continuous_support (hFc.continuousAt (hopen.mem_nhds hpne))
      (Eventually.of_forall fun x => (hF x).2)
      (Eventually.of_forall fun x => (hF x).1)).differentiableAt
  have hzero : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2
  have ha : Absorbent ℝ K := absorbent_nhds_zero hzero
  have hgp : gauge K p = 1 := (gauge_eq_one_iff_mem_frontier hK.2.1.2.1 hzero).mpr hp
  obtain ⟨f, hf, hfp⟩ := exists_normalized_support hK.2.1 hp
  refine ⟨f, ⟨hf, hfp⟩, ?_⟩
  rintro g ⟨hg, hggp⟩
  exact (normal_eq_fderiv_gauge ha hd hg hggp (hggp.trans hgp.symm)).trans
    (normal_eq_fderiv_gauge ha hd hf hfp (hfp.trans hgp.symm)).symm

/-- Continuity is a general consequence of the supporting-plane conclusion. -/
theorem projection_continuous_normal : continuousNormalType.{u} := by
  intro E _ _ _ K hK
  obtain ⟨n, hn, hnprop⟩ := continuous_unit_support_of_unique hK.2.1
    (projection_supporting_plane_unique K hK)
  let v : frontier K → E := fun p => (InnerProductSpace.toDual ℝ E).symm (n p)
  refine ⟨n, hn, hnprop, v, (InnerProductSpace.toDual ℝ E).symm.continuous.comp hn, ?_⟩
  intro p
  constructor
  · exact ((InnerProductSpace.toDual ℝ E).symm.norm_map (n p)).trans (hnprop p).2.1
  · intro x
    exact InnerProductSpace.toDual_symm_apply.symm

/-- The boundary has actual C¹ graph coordinates over its supporting direction. -/
theorem projection_boundary_local_graph : localGraphType.{u} := by
  intro E _ _ _ K hK p hp
  exact boundary_local_graph_of_unique hK.2.1 hK.1
    (projection_supporting_plane_unique K hK) hp

/-- Complete source statement, retaining all original hypotheses. -/
theorem projection_regularity : regularityType.{u} := by
  exact ⟨projection_supporting_plane_unique, projection_continuous_normal,
    projection_boundary_local_graph, projection_uniqueness, projection_continuity⟩

end ExpandedFA.HilbertCharacterization
