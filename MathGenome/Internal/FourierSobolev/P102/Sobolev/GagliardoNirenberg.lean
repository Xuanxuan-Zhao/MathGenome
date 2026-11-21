import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.GagliardoNirenberg
import MathGenome.Internal.FourierSobolev.P102.Sobolev.GagliardoNirenbergCritical
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MorreyWhole
import MathGenome.Internal.RealAnalysis.D11.Ch10.ElementaryNormInterpolation
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalEmbeddings
noncomputable section
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology
namespace P102.Sobolev.GagliardoNirenberg
open P102.U4

/-- Scalar interpolation for arbitrary a.e. measurable representatives, including
infinite endpoint exponents. -/
theorem interpolate {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure X} {f : X → 𝕜} (hf : AEStronglyMeasurable f μ)
    (s r q : ℝ≥0∞) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (heq : q⁻¹ = ENNReal.ofReal a / s + ENNReal.ofReal (1 - a) / r) :
    eLpNorm f q μ ≤ eLpNorm f s μ ^ a * eLpNorm f r μ ^ (1 - a) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let : BorelSpace 𝕜 := ⟨rfl⟩
  have h := D11.Ch10.ElementaryNormInterpolation.eLpNorm_interpolation
    μ s q r a (hf.mk f) ha ha1 heq hf.measurable_mk
  simpa only [eLpNorm_congr_ae hf.ae_eq_mk] using h

/-- Equal-exponent interpolation with zero gradient weight. -/
theorem equal_exponent {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure X} {f : X → 𝕜} {r : ℝ≥0∞} (hf : MemLp f r μ) (G : ℝ≥0∞) :
    MemLp f r μ ∧ eLpNorm f r μ ≤ (1 : ℝ≥0∞) * G ^ (0 : ℝ) *
      eLpNorm f r μ ^ (1 - (0 : ℝ)) := by
  simpa using And.intro hf (le_refl (eLpNorm f r μ))



/-- Translate the source reciprocal equation to the extended-real equation used
by Hölder. The lower bound on each exponent also handles infinity correctly. -/
theorem inverse_mix {s r q : ℝ≥0∞} (hs : 1 ≤ s) (hr : 1 ≤ r) (hq : 1 ≤ q)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (heq : q.toReal⁻¹ = a * s.toReal⁻¹ + (1 - a) * r.toReal⁻¹) :
    q⁻¹ = ENNReal.ofReal a / s + ENNReal.ofReal (1 - a) / r := by
  have hs0 : s ≠ 0 := ne_of_gt (zero_lt_one.trans_le hs)
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.inv_ne_top.mpr hq0)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top ENNReal.ofReal_ne_top hs0,
      ENNReal.div_ne_top ENNReal.ofReal_ne_top hr0⟩)).mp
  rw [ENNReal.toReal_inv, ENNReal.toReal_add
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top hs0)
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top hr0)]
  simpa only [div_eq_mul_inv, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)] using heq

/-- Interpolation on the closed weight interval. No ordering of the two
endpoint exponents is imposed, so reversed subcritical ranges are included. -/
theorem interpolate_closed {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure X} {f : X → 𝕜} (hf : AEStronglyMeasurable f μ)
    (s r q : ℝ≥0∞) (hs : 1 ≤ s) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (heq : q.toReal⁻¹ = a * s.toReal⁻¹ + (1 - a) * r.toReal⁻¹) :
    eLpNorm f q μ ≤ eLpNorm f s μ ^ a * eLpNorm f r μ ^ (1 - a) := by
  have he := inverse_mix hs hr hq ha ha1 heq
  rcases ha.eq_or_lt with rfl | ha
  · have hqr : q = r := inv_injective (by simpa using he)
    simp [hqr]
  rcases ha1.eq_or_lt with rfl | ha1
  · have hqs : q = s := inv_injective (by simpa using he)
    simp [hqs]
  exact interpolate hf s r q a ha ha1 he

/-- Interpolating a homogeneous endpoint bound yields both membership and the
multiplicative bound; finiteness is checked also at zero weights. -/
theorem interpolate_bound {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure X} {f : X → 𝕜} {G : ℝ≥0∞} (hG : G ≠ ⊤)
    (s r q : ℝ≥0∞) (hs : 1 ≤ s) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (C : ℝ≥0)
    (hf : MemLp f r μ) (hbound : eLpNorm f s μ ≤ (C : ℝ≥0∞) * G)
    (heq : q.toReal⁻¹ = a * s.toReal⁻¹ + (1 - a) * r.toReal⁻¹) :
    MemLp f q μ ∧ eLpNorm f q μ ≤
      ((C ^ a : ℝ≥0) : ℝ≥0∞) * G ^ a * eLpNorm f r μ ^ (1 - a) := by
  have hi := interpolate_closed hf.aestronglyMeasurable s r q hs hr hq a ha ha1 heq
  have hb : eLpNorm f q μ ≤ ((C ^ a : ℝ≥0) : ℝ≥0∞) *
      G ^ a * eLpNorm f r μ ^ (1 - a) := by
    calc
      _ ≤ ((C : ℝ≥0∞) * G) ^ a * eLpNorm f r μ ^ (1 - a) := by
        exact hi.trans (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hbound ha) (by positivity))
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.coe_rpow_of_nonneg _ ha]
  refine ⟨hb.trans_lt ?_, hb⟩
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.rpow_lt_top_of_nonneg ha hG))
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr ha1) hf.eLpNorm_ne_top)

/-- Complete subcritical whole-space branch, with all five frozen premises in
contract order. The weight equation itself suffices, even when r = p*. -/
theorem subcritical_conditional
    (_density : Extension.Expected.Density)
    (_extension : Extension.Expected.Extension)
    (_lipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (whole : SubcriticalEmbeddingsExpected.Whole)
    (_zero : SubcriticalEmbeddingsExpected.Zero)
    (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ≥0) (hp : 1 ≤ p) (hpd : p < d) [Fact (1 ≤ (p : ℝ≥0∞))]
    (r q : ℝ≥0∞) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (heq : Scaling d p r q a) :
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) q volume ∧
      eLpNorm (sobolevUnderlying u) q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (weakGradient u) p volume ^ a *
        eLpNorm (sobolevUnderlying u) r volume ^ (1 - a) := by
  obtain ⟨C, hC⟩ := whole.1 d hd p hp hpd
  refine ⟨C ^ a, fun u hu => ?_⟩
  obtain ⟨hg, _, hb⟩ := hC 𝕜 u
  apply interpolate_bound hg.eLpNorm_ne_top (criticalExponent d p) r q
    (by exact_mod_cast one_le_criticalExponent hp hpd) hr hq a ha ha1 C hu hb
  have hs : (criticalExponent d p : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ :=
    ExpandedFA.Sobolev.Subcritical.criticalExponent_inv hp hpd
  simpa only [Scaling, ENNReal.coe_toReal, hs] using heq

/-- The complete critical branch, in the original scaling-equation form. -/
theorem critical (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d)
    [Fact (1 ≤ (d : ℝ≥0∞))] (r q : ℝ≥0∞)
    (hr : 1 ≤ r) (hrq : r ≤ q) (hq : q ≠ ⊤)
    (a : ℝ) (heq : Scaling d d r q a) :
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 (d : ℝ≥0∞),
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) q volume ∧
      eLpNorm (sobolevUnderlying u) q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^ a *
        eLpNorm (sobolevUnderlying u) r volume ^ (1 - a) := by
  have hrfin : r ≠ ⊤ := ne_top_of_le_ne_top hq hrq
  lift r to ℝ≥0 using hrfin
  lift q to ℝ≥0 using hq
  have hr' : 1 ≤ r := by exact_mod_cast hr
  have hrq' : r ≤ q := by exact_mod_cast hrq
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans_le (by exact_mod_cast hr')
  have hqpos : (0 : ℝ) < q := hrpos.trans_le (by exact_mod_cast hrq')
  have he : (q : ℝ)⁻¹ = (1 - a) * (r : ℝ)⁻¹ := by
    simpa only [Scaling, ENNReal.coe_toReal, ENNReal.toReal_natCast, NNReal.coe_natCast, sub_self,
      mul_zero, zero_add] using heq
  have hweight : 1 - a = (r : ℝ) / q := by
    have he' := congrArg (fun t : ℝ => t * r) he
    field_simp at he' ⊢
    nlinarith
  have ha : a = 1 - (r : ℝ) / q := by linarith
  obtain ⟨C, hC⟩ := gagliardoNirenbergCritical d hd r q hr' hrq'
  exact ⟨C, fun u hu => by simpa only [ha, sub_sub_cancel] using hC 𝕜 u hu⟩



/-- The actual Euclidean weak gradient belongs to Lp on any open set. -/
theorem gradientOn_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 Ω 1 p) :
    MemLp (weakGradientOn u) p (volume.restrict (Ω : Set (Space d))) := by
  apply memLp_piLp_iff.mpr
  intro i
  exact Lp.memLp (sobolevDerivative u (firstIndex i))

/-- Each coordinate norm is controlled by the Euclidean gradient norm. -/
theorem coordinate_norm_le_gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 Ω 1 p) (i : Fin d) :
    ‖sobolevDerivative u (firstIndex i)‖ ≤
      (eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d)))).toReal := by
  have h := eLpNorm_mono_ae (p := p) (Lp.memLp (sobolevDerivative u (firstIndex i))).aestronglyMeasurable
    (Eventually.of_forall fun x => PiLp.norm_apply_le (weakGradientOn u x) i)
  have he : ENNReal.ofReal ‖sobolevDerivative u (firstIndex i)‖ ≤
      eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d))) := by
    simpa only [← Lp.enorm_def, ofReal_norm] using h
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
    ENNReal.toReal_mono (gradientOn_memLp u).eLpNorm_ne_top he

/-- The shared graph norm is bounded by a dimensional multiple of exactly the
sum norm used in the manuscript's domain inequality. -/
theorem sobolev_norm_le_full {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 Ω 1 p) :
    ‖u‖ ≤ (Fintype.card (SobolevIndex d 1) : ℝ) *
      ((eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d)))).toReal +
        ‖sobolevUnderlying u‖) := by
  classical
  rw [sobolev_norm]
  calc
    _ ≤ ∑ _ : SobolevIndex d 1,
        ((eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d)))).toReal +
          ‖sobolevUnderlying u‖) := by
      apply Finset.sum_le_sum
      intro α _
      by_cases hz : α.val = 0
      · have hα : α = zeroSobolevIndex d 1 := Subtype.ext hz
        subst α
        exact le_add_of_nonneg_left ENNReal.toReal_nonneg
      · have hcard : α.val.card = 1 := by
          have hp := α.property
          have hne : α.val.card ≠ 0 := by simpa using hz
          omega
        obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hcard
        have hα : α = firstIndex i := Subtype.ext hi
        subst α
        exact (coordinate_norm_le_gradient u i).trans (le_add_of_nonneg_right (norm_nonneg _))
    _ = _ := by simp [mul_add]

open private tuple_eLpNorm_le_sum from MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole

/-- A dimensional graph-norm bound for the gradient of an extension. -/
theorem gradient_le_graphNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    eLpNorm (weakGradient u) p volume ≤ (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  have h := tuple_eLpNorm_le_sum (d := d) (𝕜 := 𝕜) (p := p) (μ := volume) Fact.out
    (fun i => (sobolevDerivative u (firstIndex i) : Space d → 𝕜))
    (fun i => by simpa only [Opens.coe_top, Measure.restrict_univ] using (Lp.memLp (sobolevDerivative u (firstIndex i))))
  change eLpNorm (weakGradient u) p volume ≤ _ at h
  apply h.trans
  calc
    _ ≤ ∑ _ : Fin d, ENNReal.ofReal ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖sobolevDerivative u (firstIndex i)‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
      have he : eLpNorm (sobolevDerivative u (firstIndex i)) p volume =
          ENNReal.ofReal ‖sobolevDerivative u (firstIndex i)‖ := by
        simpa only [Opens.coe_top, Measure.restrict_univ, ofReal_norm] using
          (Lp.enorm_def (sobolevDerivative u (firstIndex i))).symm
      rw [he]
      exact ENNReal.ofReal_le_ofReal hn
    _ = _ := by simp [nsmul_eq_mul]

/-- Extension transfers the complete whole-space family to every bounded
Lipschitz open set. This lemma uses the original full-norm and Lr extension
bounds; it makes no additional regularity or connectedness assumption. -/
theorem domain_of_whole (extension : Extension.Expected.Extension) (whole : Whole) : Domain := by
  intro 𝕜 _ m e Ω hΩ p r q _ hr hq a ha ha1 hRange hScale
  let : Fact (1 ≤ r) := ⟨hr⟩
  obtain ⟨D, K, C, B, _, hext⟩ := extension m e Ω hΩ
  obtain ⟨E, _, hRestrict, _, hE, hEr⟩ := hext 𝕜 p
  obtain ⟨A, hA⟩ := whole 𝕜 (m + 1) (by omega) p r q hr hq a ha ha1 hRange hScale
  let N : ℝ≥0 := Fintype.card (SobolevIndex (m + 1) 1)
  let J : ℝ≥0 := (m + 1) * C p * N
  refine ⟨A * J ^ a * (B r) ^ (1 - a), fun u hu => ?_⟩
  obtain ⟨hur, hbr⟩ := hEr r u hu
  obtain ⟨huq, hbq⟩ := hA (E u) hur
  have hfg := hRestrict u
  have hmem : MemLp (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) :=
    (memLp_congr_ae hfg).mp (huq.mono_measure Measure.restrict_le_self)
  have hqbound : eLpNorm (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) ≤
      eLpNorm (sobolevUnderlying (E u)) q volume := by
    rw [← eLpNorm_congr_ae hfg]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  let F : ℝ≥0∞ := eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space (m + 1)))) +
    eLpNorm (sobolevUnderlying u) p (volume.restrict (Ω : Set (Space (m + 1))))
  have hF : F ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨(gradientOn_memLp u).eLpNorm_ne_top, (Lp.memLp (sobolevUnderlying u)).eLpNorm_ne_top⟩
  have hnorm : ENNReal.ofReal ‖u‖ ≤ (N : ℝ≥0∞) * F := by
    have h := ENNReal.ofReal_le_ofReal (sobolev_norm_le_full u)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ENNReal.toReal_nonneg (norm_nonneg _),
      ENNReal.ofReal_toReal (gradientOn_memLp u).eLpNorm_ne_top] at h
    simpa only [N, NNReal.coe_natCast, ENNReal.ofReal_natCast, ENNReal.coe_natCast, ← Lp.enorm_def, ofReal_norm, F] using h
  have hgrad : eLpNorm (weakGradient (E u)) p volume ≤ (J : ℝ≥0∞) * F := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ‖E u‖ := gradient_le_graphNorm _
      _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ((C p : ℝ≥0∞) * ENNReal.ofReal ‖u‖) := by
        gcongr
        have hn : ‖E u‖ ≤ (C p : ℝ) * ‖u‖ :=
          (E.le_opNorm u).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
        simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hn
      _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ((C p : ℝ≥0∞) * ((N : ℝ≥0∞) * F)) := by gcongr
      _ = _ := by simp only [J, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_natCast, Nat.cast_add, Nat.cast_one]; ring
  refine ⟨hmem, hqbound.trans (hbq.trans ?_)⟩
  calc
    _ ≤ (A : ℝ≥0∞) * ((J : ℝ≥0∞) * F) ^ a *
        ((B r : ℝ≥0∞) * eLpNorm (sobolevUnderlying u) r
          (volume.restrict (Ω : Set (Space (m + 1))))) ^ (1 - a) := by
      gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha,
        ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ha1)]
      simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ ha,
        ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.mpr ha1)]
      dsimp [F]
      ring


/-- The standard oriented coordinate on the one-dimensional Euclidean space. -/
def lineIsometry : ℝ ≃ₗᵢ[ℝ] Space 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- The whole-line fundamental-theorem bound for compactly supported C¹ functions. -/
theorem one_dimension_smooth {𝕜 : Type} [RCLike 𝕜] {f : Space 1 → 𝕜}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    eLpNorm f ⊤ volume ≤ eLpNorm (CriticalGN.classicalGradient f) 1 volume := by
  let g : ℝ → 𝕜 := f ∘ lineIsometry
  have hg : ContDiff ℝ 1 g := hf.comp lineIsometry.contDiff
  have hsg : HasCompactSupport g := hs.comp_homeomorph lineIsometry.toHomeomorph
  have hdg (t : ℝ) : deriv g t = fderiv ℝ f (lineIsometry t) (coordinateVector 1 0) := by
    rw [fderiv_comp_deriv _ (hf.differentiable one_ne_zero _) lineIsometry.differentiableAt]
    congr 1
    change deriv (lineIsometry.toContinuousLinearMap : ℝ → Space 1) t = _
    rw [lineIsometry.toContinuousLinearMap.deriv]
    ext i
    simp [lineIsometry, coordinateVector, EuclideanSpace.basisFun_apply, Subsingleton.elim i (0 : Fin 1)]
  have hderiv : eLpNorm (deriv g) 1 volume ≤ eLpNorm (CriticalGN.classicalGradient f) 1 volume := by
    have h := eLpNorm_mono_ae (μ := volume) (p := (1 : ℝ≥0∞)) (hg.continuous_deriv le_rfl).aestronglyMeasurable
      (g := fun t => CriticalGN.classicalGradient f (lineIsometry t))
      (Eventually.of_forall fun t => by
        rw [hdg]
        exact PiLp.norm_apply_le (CriticalGN.classicalGradient f (lineIsometry t)) 0)
    apply h.trans_eq
    exact eLpNorm_comp_measurePreserving
      (CriticalGNSmooth.classicalGradient_memLp hf hs 1).aestronglyMeasurable lineIsometry.measurePreserving
  have hgpoint (t : ℝ) : ‖g t‖ₑ ≤ eLpNorm (deriv g) 1 volume := by
    calc
      _ ≤ ∫⁻ y in Iic t, ‖deriv g y‖ₑ := HasCompactSupport.enorm_le_lintegral_Ici_deriv hg hsg t
      _ ≤ ∫⁻ y, ‖deriv g y‖ₑ := lintegral_mono' Measure.restrict_le_self (le_refl _)
      _ = _ := (eLpNorm_one_eq_lintegral_enorm (hg.continuous_deriv le_rfl).aestronglyMeasurable).symm
  have hpoint (x : Space 1) : ‖f x‖ₑ ≤ eLpNorm (CriticalGN.classicalGradient f) 1 volume := by
    have h := (hgpoint (lineIsometry.symm x)).trans hderiv
    simpa only [g, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using h
  have h := eLpNorm_le_of_ae_enorm_bound (μ := volume) (p := (⊤ : ℝ≥0∞))
    hf.continuous.aestronglyMeasurable (Eventually.of_forall hpoint)
  simpa only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, smul_eq_mul, mul_one] using h

open private represented_gradient from MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole

/-- The one-dimensional fundamental-theorem endpoint on the actual weak
Sobolev class. Whole-space density and Fatou preserve the gradient-only bound. -/
theorem one_dimension_endpoint {𝕜 : Type} [RCLike 𝕜]
    (u : U4.Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 1) :
    MemLp (sobolevUnderlying u) ⊤ volume ∧
      eLpNorm (sobolevUnderlying u) ⊤ volume ≤ eLpNorm (weakGradient u) 1 volume := by
  have hu : MemLp (sobolevUnderlying u) 1 volume := by simpa using Lp.memLp (sobolevUnderlying u)
  obtain ⟨f, w, hrep, hw, herr⟩ :=
    CriticalGNApproximation.simultaneous_density (by simp : (1 : ℝ≥0∞) ≠ ⊤) 1 le_rfl u hu
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by simp : (1 : ℝ≥0∞) ≠ 0) herr).exists_seq_tendsto_ae
  have hgnorm := CriticalGNApproximation.norm_tendsto_of_error
    (fun n => weakGradient_memLp (w n)) (weakGradient_memLp u)
    (CriticalGNApproximation.gradient_error_tendsto hw)
  have hb (n : ℕ) : eLpNorm (f n) ⊤ volume ≤ eLpNorm (weakGradient (w n)) 1 volume := by
    have h := one_dimension_smooth ((f n).contDiff.of_le (by simp)) (f n).hasCompactSupport
    unfold CriticalGN.classicalGradient at h
    rwa [← eLpNorm_congr_ae (represented_gradient (f n) (w n) (hrep n))] at h
  have hfinal := ExpandedFA.Sobolev.Subcritical.eLpNorm_le_of_ae_tendsto_bounds
    (fun n => (f (ns n)).continuous.aestronglyMeasurable)
    hu.aestronglyMeasurable hae (hgnorm.comp hns.tendsto_atTop) (fun n => hb (ns n))
  exact ⟨hfinal.trans_lt (weakGradient_memLp u).eLpNorm_lt_top, hfinal⟩

/-- All finite and infinite q in the exceptional d = p = 1 branch. -/
theorem one_dimension (𝕜 : Type) [RCLike 𝕜]
    (r q : ℝ≥0∞) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (heq : Scaling 1 1 r q a) :
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 1,
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) q volume ∧
      eLpNorm (sobolevUnderlying u) q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (weakGradient u) 1 volume ^ a *
        eLpNorm (sobolevUnderlying u) r volume ^ (1 - a) := by
  refine ⟨1, fun u hu => ?_⟩
  have hi := interpolate_bound (weakGradient_memLp u).eLpNorm_ne_top ⊤ r q
    le_top hr hq a ha ha1 1 hu (by simpa using (one_dimension_endpoint u).2)
    (by simpa [Scaling] using heq)
  simpa only [NNReal.one_rpow] using hi


/-- Pointwise estimate from the Lr average and the Hölder increment. -/
theorem holder_point_bound_measure {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (r : ℝ≥0) (hr : 1 ≤ r) (hf : MemLp f r volume)
    (β H : ℝ) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hHolder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (x : Space d) (R : ℝ) (hR : 0 < R) :
    ‖f x‖ ≤ (volume (Metric.ball x R)).toReal ^ (-(r : ℝ)⁻¹) *
      (eLpNorm f r volume).toReal + H * R ^ β := by
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans_le hr
  have hV : 0 < (volume (Metric.ball x R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hR).ne' measure_ball_lt_top.ne
  have hvp : 0 < (volume (Metric.ball x R)).toReal ^ (r : ℝ)⁻¹ := Real.rpow_pos_of_pos hV _
  by_cases hx : ‖f x‖ ≤ H * R ^ β
  · exact hx.trans (le_add_of_nonneg_left (by positivity))
  have hc : 0 < ‖f x‖ - H * R ^ β := sub_pos.mpr (lt_of_not_ge hx)
  have hb : eLpNorm (fun _ : Space d => ‖f x‖ - H * R ^ β) r
      (volume.restrict (Metric.ball x R)) ≤ eLpNorm f r volume := by
    apply (eLpNorm_mono_ae (p := (r : ℝ≥0∞)) aestronglyMeasurable_const ?_).trans
      (eLpNorm_mono_measure f Measure.restrict_le_self)
    apply ae_restrict_of_forall_mem measurableSet_ball
    intro y hy
    have hnorm : ‖x - y‖ ≤ R := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using ((Metric.mem_ball.mp hy).le)
    have hh : ‖f x - f y‖ ≤ H * R ^ β :=
      (hHolder x y).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hnorm hβ) hH)
    rw [Real.norm_eq_abs, abs_of_pos hc]
    linarith [norm_sub_norm_le (f x) (f y)]
  have hb' := ENNReal.toReal_mono hf.eLpNorm_ne_top hb
  rw [eLpNorm_const' _ hr0 ENNReal.coe_ne_top, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hc,
    Measure.restrict_apply_univ, ENNReal.coe_toReal, one_div] at hb'
  have hh : ‖f x‖ - H * R ^ β ≤
      (eLpNorm f r volume).toReal / (volume (Metric.ball x R)).toReal ^ (r : ℝ)⁻¹ :=
    (le_div_iff₀ hvp).mpr hb'
  rw [div_eq_mul_inv, ← Real.rpow_neg hV.le] at hh
  linarith



theorem holder_point_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (r : ℝ≥0) (hr : 1 ≤ r) (hf : MemLp f r volume)
    (β H : ℝ) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hHolder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (x : Space d) (R : ℝ) (hR : 0 < R) :
    ‖f x‖ ≤ (volume (Metric.ball (0 : Space d) 1)).toReal ^ (-(r : ℝ)⁻¹) *
      R ^ (-(d : ℝ) / r) * (eLpNorm f r volume).toReal + H * R ^ β := by
  have h := holder_point_bound_measure r hr hf β H hβ hH hHolder x R hR
  have he : (volume (Metric.ball x R)).toReal ^ (-(r : ℝ)⁻¹) =
      (volume (Metric.ball (0 : Space d) 1)).toReal ^ (-(r : ℝ)⁻¹) * R ^ (-(d : ℝ) / r) := by
    rw [Measure.addHaar_ball_of_pos volume x hR, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), Real.mul_rpow (by positivity) ENNReal.toReal_nonneg]
    rw [show Module.finrank ℝ (Space d) = d by simp [Space], ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    rw [mul_comm]
    congr 1
    ring
  simpa only [he] using h

/-- Exact balancing identities for the supercritical endpoint radius. -/
theorem balancing_identities {N G β s : ℝ} (hN : 0 < N) (hG : 0 < G)
    (hβ : 0 < β) (hs : 0 < s) :
    let R := (N / G) ^ (β + s)⁻¹
    N * R ^ (-s) = G ^ (s / (β + s)) * N ^ (1 - s / (β + s)) ∧
      G * R ^ β = G ^ (s / (β + s)) * N ^ (1 - s / (β + s)) := by
  let R := (N / G) ^ (β + s)⁻¹
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hN hG) _
  have ht : β + s ≠ 0 := (add_pos hβ hs).ne'
  have hlog : Real.log R = (β + s)⁻¹ * (Real.log N - Real.log G) := by
    dsimp [R]
    rw [Real.log_rpow (div_pos hN hG), Real.log_div hN.ne' hG.ne']
  constructor
  · apply Real.log_injOn_pos (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
    rw [Real.log_mul hN.ne' (Real.rpow_pos_of_pos hR _).ne', Real.log_rpow hR,
      Real.log_mul (Real.rpow_pos_of_pos hG _).ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hG, Real.log_rpow hN, hlog]
    field_simp
    ring
  · apply Real.log_injOn_pos (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
    rw [Real.log_mul hG.ne' (Real.rpow_pos_of_pos hR _).ne', Real.log_rpow hR,
      Real.log_mul (Real.rpow_pos_of_pos hG _).ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hG, Real.log_rpow hN, hlog]
    field_simp
    ring



/-- A global Hölder seminorm and a finite Lr norm control the essential supremum.
The balancing radius is explicit; zero seminorm and zero Lr norm are included. -/
theorem holder_endpoint (d : ℕ) (hd : 1 ≤ d) (r : ℝ≥0) (hr : 1 ≤ r)
    (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] (f : Space d → 𝕜),
      Continuous f → MemLp f r volume → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β) →
      MemLp f ⊤ volume ∧ eLpNorm f ⊤ volume ≤
        (C : ℝ≥0∞) * ENNReal.ofReal H ^ ((d : ℝ) / r / (β + (d : ℝ) / r)) *
          eLpNorm f r volume ^ (1 - (d : ℝ) / r / (β + (d : ℝ) / r)) := by
  have : NeZero d := ⟨by omega⟩
  let s : ℝ := (d : ℝ) / r
  have hs : 0 < s := div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd))
    (zero_lt_one.trans_le hr)
  let θ : ℝ := s / (β + s)
  have hθ : 0 < θ := div_pos hs (add_pos hβ hs)
  have hθ1 : θ < 1 := (div_lt_one (add_pos hβ hs)).mpr (lt_add_of_pos_left s hβ)
  let V : ℝ := (volume (Metric.ball (0 : Space d) 1)).toReal
  let K : ℝ := V ^ (-(r : ℝ)⁻¹) + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K.toNNReal, fun 𝕜 _ f hf hfr H hH hHolder => ?_⟩
  let N : ℝ := (eLpNorm f r volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  have hfinite : (ENNReal.ofReal K) * ENNReal.ofReal H ^ θ *
      eLpNorm f r volume ^ (1 - θ) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg hθ.le ENNReal.ofReal_ne_top))
      (ENNReal.rpow_lt_top_of_nonneg (sub_pos.mpr hθ1).le hfr.eLpNorm_ne_top)
  have finish (hb : eLpNorm f ⊤ volume ≤
      (ENNReal.ofReal K) * ENNReal.ofReal H ^ θ * eLpNorm f r volume ^ (1 - θ)) :
      MemLp f ⊤ volume ∧ eLpNorm f ⊤ volume ≤
        (ENNReal.ofReal K) * ENNReal.ofReal H ^ θ * eLpNorm f r volume ^ (1 - θ) :=
    ⟨hb.trans_lt hfinite, hb⟩
  change MemLp f ⊤ volume ∧ eLpNorm f ⊤ volume ≤
    (ENNReal.ofReal K) * ENNReal.ofReal H ^ θ * eLpNorm f r volume ^ (1 - θ)
  by_cases hn : N = 0
  · have hn' : eLpNorm f r volume = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hn).resolve_right hfr.eLpNorm_ne_top
    have hz := (eLpNorm_eq_zero_iff hr0).mp hn'
    apply finish
    rw [eLpNorm_congr_ae hz]
    simp
  by_cases hh : H = 0
  · have hc : f = fun _ => f 0 := by
      funext x
      have h := hHolder x 0
      rw [hh, zero_mul] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    have hm : MemLp (fun _ : Space d => f 0) r volume := by rwa [← hc]
    have hzero : f 0 = 0 := by
      have h := (memLp_const_iff hr0 ENNReal.coe_ne_top).mp hm
      simpa only [MeasureTheory.measure_univ_of_isAddLeftInvariant, lt_self_iff_false, or_false] using h
    apply finish
    rw [hc, hzero]
    simp
  have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hn)
  have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hh)
  let R : ℝ := (N / H) ^ (β + s)⁻¹
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hNpos hHpos) _
  obtain ⟨hbalance₁, hbalance₂⟩ := balancing_identities hNpos hHpos hβ hs
  have hpoint (x : Space d) : ‖f x‖ ≤ K * H ^ θ * N ^ (1 - θ) := by
    have h := holder_point_bound r hr hfr β H hβ.le hH hHolder x R hR
    have h₁ : N * R ^ (-s) = H ^ θ * N ^ (1 - θ) := hbalance₁
    have h₂ : H * R ^ β = H ^ θ * N ^ (1 - θ) := hbalance₂
    rw [neg_div] at h
    change ‖f x‖ ≤ V ^ (-(r : ℝ)⁻¹) * R ^ (-s) * N + H * R ^ β at h
    rw [mul_right_comm (V ^ (-(r : ℝ)⁻¹)) (R ^ (-s)) N, mul_assoc, h₁, h₂] at h
    dsimp [K]
    nlinarith [Real.rpow_nonneg hH θ, Real.rpow_nonneg hN (1 - θ)]
  have hb := eLpNorm_le_of_ae_enorm_bound (μ := volume) (p := (⊤ : ℝ≥0∞))
    hf.aestronglyMeasurable
    (Eventually.of_forall fun x => show ‖f x‖ₑ ≤ ENNReal.ofReal (K * H ^ θ * N ^ (1 - θ)) by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hpoint x))
  apply finish
  simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, smul_eq_mul, mul_one] at hb
  convert hb using 1
  rw [ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hH _)), ENNReal.ofReal_mul hK,
    ← ENNReal.ofReal_rpow_of_nonneg hH hθ.le,
    ← ENNReal.ofReal_rpow_of_nonneg hN (sub_pos.mpr hθ1).le,
    show ENNReal.ofReal N = eLpNorm f r volume from ENNReal.ofReal_toReal hfr.eLpNorm_ne_top]




/-- A positive Hölder exponent for the supercritical Sobolev range. -/
theorem morrey_exponent_pos {d : ℕ} (hd : 1 ≤ d) {p : ℝ≥0∞}
    (hdp : (d : ℝ≥0∞) < p) : 0 < 1 - (d : ℝ) / p.toReal := by
  by_cases hp : p = ⊤
  · simp [hp]
  have hdreal : (d : ℝ) < p.toReal := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_strict_mono hp hdp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hppos : 0 < p.toReal := hdpos.trans hdreal
  exact sub_pos.mpr ((div_lt_one hppos).mpr hdreal)

/-- One uniform Hölder constant for the continuous representatives, across all
u at the fixed exponent p. -/
theorem holder_representatives (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 1 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p) :
    ∃ M : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      ∃ f : Space d → 𝕜, Continuous f ∧
        (sobolevUnderlying u : Space d → 𝕜) =ᵐ[volume] f ∧
        ∀ x y, ‖f x - f y‖ ≤ (M : ℝ) * (eLpNorm (weakGradient u) p volume).toReal *
          ‖x - y‖ ^ (1 - (d : ℝ) / p.toReal) := by
  by_cases hp : p = ⊤
  · subst p
    obtain ⟨C, hC, h⟩ := MorreyWhole.infinity 𝕜 d hd
    refine ⟨⟨C, hC⟩, fun u => ?_⟩
    obtain ⟨f, hf, huf, hb, _⟩ := h u
    refine ⟨f, hf, huf, ?_⟩
    change ∀ x y, ‖f x - f y‖ ≤ C * MorreyWhole.gradientNorm u *
      ‖x - y‖ ^ (1 - (d : ℝ) / (⊤ : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_one] using hb
  · obtain ⟨C, hC, h⟩ := MorreyWhole.finite 𝕜 d hd p hdp hp
    refine ⟨⟨C, hC⟩, fun u => ?_⟩
    obtain ⟨f, hf, huf, hb, _⟩ := h u
    exact ⟨f, hf, huf, hb⟩

/-- The optimized supercritical whole-space supremum endpoint, including p=∞. -/
theorem supercritical_endpoint (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 1 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p)
    (r : ℝ≥0) (hr : 1 ≤ r) :
    let β := 1 - (d : ℝ) / p.toReal
    let θ := (d : ℝ) / r / (β + (d : ℝ) / r)
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) ⊤ volume ∧
      eLpNorm (sobolevUnderlying u) ⊤ volume ≤ (C : ℝ≥0∞) *
        eLpNorm (weakGradient u) p volume ^ θ *
        eLpNorm (sobolevUnderlying u) r volume ^ (1 - θ) := by
  dsimp only
  let β : ℝ := 1 - (d : ℝ) / p.toReal
  let θ : ℝ := (d : ℝ) / r / (β + (d : ℝ) / r)
  have hβ : 0 < β := morrey_exponent_pos hd hdp
  have hs : 0 < (d : ℝ) / r := div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd))
    (zero_lt_one.trans_le hr)
  have hθ : 0 ≤ θ := (div_pos hs (add_pos hβ hs)).le
  obtain ⟨M, hM⟩ := holder_representatives 𝕜 d hd p hdp
  obtain ⟨K, hK⟩ := holder_endpoint d hd r hr β hβ
  refine ⟨K * M ^ θ, fun u hu => ?_⟩
  obtain ⟨f, hf, huf, hb⟩ := hM u
  have hfr := (memLp_congr_ae huf).mp hu
  obtain ⟨hfin, hbf⟩ := hK 𝕜 f hf hfr
    ((M : ℝ) * (eLpNorm (weakGradient u) p volume).toReal) (by positivity) hb
  refine ⟨(memLp_congr_ae huf).mpr hfin, ?_⟩
  rw [eLpNorm_congr_ae huf]
  calc
    _ ≤ _ := hbf
    _ = _ := by
      rw [ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (weakGradient_memLp u).eLpNorm_ne_top,
        ENNReal.mul_rpow_of_nonneg _ _ hθ, ← eLpNorm_congr_ae huf]
      simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hθ]
      ring

/-- Interpolate a multiplicative supremum endpoint; the gradient weight is θt. -/
theorem interpolate_endpoint {X : Type*} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure X} {f : X → 𝕜} {G : ℝ≥0∞} (hG : G ≠ ⊤)
    (r q : ℝ≥0∞) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (θ t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (C : ℝ≥0) (hf : MemLp f r μ)
    (hb : eLpNorm f ⊤ μ ≤ (C : ℝ≥0∞) * G ^ θ * eLpNorm f r μ ^ (1 - θ))
    (heq : q.toReal⁻¹ = (1 - t) * r.toReal⁻¹) :
    MemLp f q μ ∧ eLpNorm f q μ ≤
      ((C ^ t : ℝ≥0) : ℝ≥0∞) * G ^ (θ * t) * eLpNorm f r μ ^ (1 - θ * t) := by
  have hG' : G ^ θ * eLpNorm f r μ ^ (1 - θ) ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_lt_top_of_nonneg hθ hG).ne
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ1) hf.eLpNorm_ne_top).ne
  have hi := interpolate_bound hG' ⊤ r q le_top hr hq t ht ht1 C hf
    (by simpa only [mul_assoc] using hb) (by simpa using heq)
  refine ⟨hi.1, hi.2.trans_eq ?_⟩
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc
    _ = (((C ^ t : ℝ≥0) : ℝ≥0∞) * G ^ (θ * t)) *
        (eLpNorm f r μ ^ ((1 - θ) * t) * eLpNorm f r μ ^ (1 - t)) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by linarith),
        show (1 - θ) * t + (1 - t) = 1 - θ * t by ring]




/-- Supercritical interpolation, with the source scaling equation and including
q = r, q = ∞, and p = ∞. -/
theorem supercritical (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 1 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p)
    (r q : ℝ≥0∞) (hr : 1 ≤ r) (hq : 1 ≤ q) (hrfin : r ≠ ⊤)
    (a : ℝ) (ha : 0 ≤ a) (heq : Scaling d p r q a) :
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) q volume ∧
      eLpNorm (sobolevUnderlying u) q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (weakGradient u) p volume ^ a *
        eLpNorm (sobolevUnderlying u) r volume ^ (1 - a) := by
  lift r to ℝ≥0 using hrfin
  have hr' : 1 ≤ r := by exact_mod_cast hr
  have hD : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hR : (0 : ℝ) < r := zero_lt_one.trans_le hr'
  let β := 1 - (d : ℝ) / p.toReal
  let s := (d : ℝ) / r
  let θ := s / (β + s)
  let t := a / θ
  have hβ : 0 < β := morrey_exponent_pos hd hdp
  have hs : 0 < s := div_pos hD hR
  have hθ : 0 < θ := div_pos hs (add_pos hβ hs)
  have hθ1 : θ ≤ 1 := (div_le_one (add_pos hβ hs)).mpr (by linarith)
  have ht : 0 ≤ t := div_nonneg ha hθ.le
  have hβeq : p.toReal⁻¹ - (d : ℝ)⁻¹ = -β / d := by
    dsimp [β]
    simp only [div_eq_mul_inv, neg_sub]
    have h := congrArg (fun z : ℝ => z * p.toReal⁻¹) (mul_inv_cancel₀ hD.ne')
    nlinarith
  have he : q.toReal⁻¹ = (1 - t) * (r : ℝ)⁻¹ := by
    have h : q.toReal⁻¹ = a * (-β / d) + (1 - a) * (r : ℝ)⁻¹ := by
      simpa only [Scaling, ENNReal.coe_toReal, hβeq] using heq
    rw [h]
    dsimp [t, θ, s]
    field_simp
    ring
  have ht1 : t ≤ 1 := by
    have hqnonneg : 0 ≤ q.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have hrinv : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hR
    rw [he] at hqnonneg
    nlinarith
  have haeq : θ * t = a := mul_div_cancel₀ a hθ.ne'
  obtain ⟨C, hC⟩ := supercritical_endpoint 𝕜 d hd p hdp r hr'
  refine ⟨C ^ t, fun u hu => ?_⟩
  have hb := (hC u hu).2
  have hi := interpolate_endpoint (weakGradient_memLp u).eLpNorm_ne_top r q hr hq
    θ t hθ.le hθ1 ht ht1 C hu hb (by simpa only [ENNReal.coe_toReal] using he)
  simpa only [haeq] using hi


/-- Conditional derivation of the complete whole-space interpolation family.
The five unaccepted upstream statements occur explicitly in their frozen order.
No declaration of the closed original target is made here. -/
theorem whole_conditional
    (density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension)
    (lipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (whole : SubcriticalEmbeddingsExpected.Whole)
    (zero : SubcriticalEmbeddingsExpected.Zero) : Whole := by
  intro 𝕜 _ d hd p r q _ hr hq a ha ha1 hRange hScale
  rcases hRange with ⟨hpd, _⟩ | ⟨hp, hd2, hrq, hqfin⟩ | ⟨hcase, hrfin, _⟩
  · have hpfin : p ≠ ⊤ := ne_top_of_lt hpd
    lift p to ℝ≥0 using hpfin
    have hp' : 1 ≤ p := by exact_mod_cast (Fact.out : 1 ≤ (p : ℝ≥0∞))
    have hpd' : p < d := by exact_mod_cast hpd
    have hd2 : 2 ≤ d := by
      have h : (1 : ℝ≥0) < d := hp'.trans_lt hpd'
      have h' : (1 : ℕ) < d := by exact_mod_cast h
      omega
    exact subcritical_conditional density extension lipschitz whole zero
      𝕜 d hd2 p hp' hpd' r q hr hq a ha ha1 hScale
  · subst p
    exact critical 𝕜 d hd2 r q hr hrq hqfin a hScale
  · rcases hcase with hdp | ⟨rfl, hp⟩
    · exact supercritical 𝕜 d hd p hdp r q hr hq hrfin a ha hScale
    · subst p
      exact one_dimension 𝕜 r q hr hq a ha ha1 hScale

/-- Conditional derivation of the complete bounded-Lipschitz-open-set family,
using the same five ordered premises and the proved whole-space derivation. -/
theorem domain_conditional
    (density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension)
    (lipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (whole : SubcriticalEmbeddingsExpected.Whole)
    (zero : SubcriticalEmbeddingsExpected.Zero) : Domain :=
  domain_of_whole extension (whole_conditional density extension lipschitz whole zero)

end P102.Sobolev.GagliardoNirenberg

theorem _root_.«P102».«Sobolev».«GagliardoNirenberg».«domain» : _root_.«P102».«Sobolev».«GagliardoNirenberg».«Domain» :=
  @_root_.«P102».«Sobolev».«GagliardoNirenberg».«domain_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
theorem _root_.«P102».«Sobolev».«GagliardoNirenberg».«whole» : _root_.«P102».«Sobolev».«GagliardoNirenberg».«Whole» :=
  @_root_.«P102».«Sobolev».«GagliardoNirenberg».«whole_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
