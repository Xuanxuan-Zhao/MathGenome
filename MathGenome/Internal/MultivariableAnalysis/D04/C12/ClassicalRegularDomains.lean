import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalRegularDomains
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C14.FiniteCompactPartition
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open Set Filter Topology
open scoped ContDiff BigOperators
namespace D04.ClassicalRegularDomains
open Specs.D04.C12.ClassicalRegularDomains

abbrev IsDefiningFunction := @Model.IsDefiningFunction
abbrev IsClassicalRegularDomain := @Model.IsClassicalRegularDomain
def domainClosure : domainClosureType := @domainClosureValue
def ambientOrientation : ambientOrientationType := ambientOrientationValue
def normalFromDefining : normalFromDefiningType := @normalFromDefiningValue
def outwardNormal : outwardNormalType := @outwardNormalValue
abbrev LocallyCrExtendible := @Model.LocallyCrExtendible
abbrev FiniteExtension := @Model.FiniteExtension

private theorem fderiv_gradient {n : ℕ} (f : E n → ℝ) (p v : E n) :
    fderiv ℝ f p v = inner ℝ (_root_.gradient f p) v :=
  scalarGradient_represents f p v

/-- A nonzero scalar differential has nonzero metric dual. -/
theorem gradient_ne_zero {n : ℕ} {f : E n → ℝ} {p : E n}
    (h : fderiv ℝ f p ≠ 0) : _root_.gradient f p ≠ 0 := by
  intro hz
  apply h
  ext v
  simpa [hz] using fderiv_gradient f p v

/-- The unit metric dual of a nonzero differential. -/
theorem unit_gradient_properties {n : ℕ} {f : E n → ℝ} {p : E n}
    (h : fderiv ℝ f p ≠ 0) :
    ‖normalFromDefining f p‖ = 1 ∧
    (∀ v, fderiv ℝ f p v = 0 → inner ℝ (normalFromDefining f p) v = 0) ∧
    fderiv ℝ f p (normalFromDefining f p) = ‖_root_.gradient f p‖ ∧
    0 < fderiv ℝ f p (normalFromDefining f p) := by
  have hn : 0 < ‖_root_.gradient f p‖ := norm_pos_iff.mpr (gradient_ne_zero h)
  have he : fderiv ℝ f p (normalFromDefining f p) = ‖_root_.gradient f p‖ := by
    rw [fderiv_gradient]
    change inner ℝ (_root_.gradient f p) (‖_root_.gradient f p‖⁻¹ • _root_.gradient f p) = _
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  refine ⟨?_, ?_, he, he ▸ hn⟩
  · change ‖‖_root_.gradient f p‖⁻¹ • _root_.gradient f p‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · intro v hv
    change inner ℝ (‖_root_.gradient f p‖⁻¹ • _root_.gradient f p) v = 0
    rw [real_inner_smul_left, ← fderiv_gradient, hv, mul_zero]

theorem normal_properties : normal_propertiesType := by
  intro n D U ρ p h hp hb
  exact unit_gradient_properties (h.nonzero p hp ((h.zero_level p hp).mp hb))

/-- A negative derivative at a zero forces negative values on a short positive ray. -/
private theorem negative_on_ray {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < 0 := by
  have he := hf.tendsto_slope_zero_right.eventually (gt_mem_nhds ha)
  filter_upwards [he, self_mem_nhdsWithin] with t ht hpos
  have hs : t⁻¹ * f t < 0 := by simpa [hzero] using ht
  exact (mul_neg_iff.mp hs).resolve_right (by intro h; exact (not_lt_of_ge (inv_pos.mpr hpos).le) h.1) |>.2

private theorem deriv_on_ray {n : ℕ} {f : E n → ℝ} {p : E n}
    (hf : DifferentiableAt ℝ f p) (v : E n) :
    HasDerivAt (fun t : ℝ => f (p + t • v)) (fderiv ℝ f p v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add p
  simpa using! hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)

/-- Two functions defining the same negative side cannot have differential
values of opposite signs along one vector. Only their germs are used. -/
private theorem no_opposite_sign {n : ℕ} {D U V : Set (E n)} {ρ σ : E n → ℝ}
    {p v : E n} (hρ : IsDefiningFunction D U ρ) (hσ : IsDefiningFunction D V σ)
    (hpU : p ∈ U) (hpV : p ∈ V) (hb : p ∈ frontier D)
    (hvρ : fderiv ℝ ρ p v < 0) (hvσ : 0 < fderiv ℝ σ p v) : False := by
  have hdρ : DifferentiableAt ℝ ρ p :=
    (hρ.regular.contDiffAt (hρ.isOpen.mem_nhds hpU)).differentiableAt (by simp)
  have hdσ : DifferentiableAt ℝ σ p :=
    (hσ.regular.contDiffAt (hσ.isOpen.mem_nhds hpV)).differentiableAt (by simp)
  have heρ := negative_on_ray (deriv_on_ray hdρ v) (by
    simpa using (hρ.zero_level p hpU).mp hb) hvρ
  have heσ := negative_on_ray (deriv_on_ray hdσ v).neg (by
    simp [(hσ.zero_level p hpV).mp hb]) (neg_neg_of_pos hvσ)
  have hl : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    have hc := (continuous_const.add (continuous_id.smul continuous_const) :
      Continuous (fun t : ℝ => p + t • v)).continuousAt (x := 0)
    simpa only [Pi.add_apply, zero_smul, add_zero] using! hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hu := hl.eventually (hρ.isOpen.mem_nhds hpU)
  have hv := hl.eventually (hσ.isOpen.mem_nhds hpV)
  obtain ⟨t, htρ, htσ, htU, htV⟩ := (heρ.and (heσ.and (hu.and hv))).exists
  exact (not_lt_of_ge (le_of_lt (neg_neg_iff_pos.mp htσ)))
    ((hσ.negative _ htV).mp ((hρ.negative _ htU).mpr htρ))

/-- The unit-vector difference separates two distinct unit normals. -/
theorem normal_independent : normal_independentType := by
  intro n D U V ρ σ p hρ hσ hpU hpV hb
  let a := normalFromDefining ρ p
  let b := normalFromDefining σ p
  have hnρ := (normal_properties hρ hpU hb).1
  have hnσ := (normal_properties hσ hpV hb).1
  change ‖a‖ = 1 at hnρ
  change ‖b‖ = 1 at hnσ
  have hgρ : 0 < ‖_root_.gradient ρ p‖ := norm_pos_iff.mpr
    (gradient_ne_zero (hρ.nonzero p hpU ((hρ.zero_level p hpU).mp hb)))
  have hgσ : 0 < ‖_root_.gradient σ p‖ := norm_pos_iff.mpr
    (gradient_ne_zero (hσ.nonzero p hpV ((hσ.zero_level p hpV).mp hb)))
  have ha : _root_.gradient ρ p = ‖_root_.gradient ρ p‖ • a := by
    change _root_.gradient ρ p = ‖_root_.gradient ρ p‖ • (‖_root_.gradient ρ p‖⁻¹ • _root_.gradient ρ p)
    rw [smul_smul, mul_inv_cancel₀ hgρ.ne', one_smul]
  have hb' : _root_.gradient σ p = ‖_root_.gradient σ p‖ • b := by
    change _root_.gradient σ p = ‖_root_.gradient σ p‖ • (‖_root_.gradient σ p‖⁻¹ • _root_.gradient σ p)
    rw [smul_smul, mul_inv_cancel₀ hgσ.ne', one_smul]
  by_contra hne
  have hpos : 0 < inner ℝ (a - b) (a - b) := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq]; rw [hnρ]; norm_num
  have hbb : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq]; rw [hnσ]; norm_num
  have hba : inner ℝ b a = inner ℝ a b := real_inner_comm _ _
  have hab : inner ℝ a b < 1 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, haa, hbb,
      hba] at hpos
    linarith
  apply no_opposite_sign hρ hσ hpU hpV hb (v := b - a)
  · rw [fderiv_gradient, ha, real_inner_smul_left, inner_sub_right, haa]
    exact mul_neg_of_pos_of_neg hgρ (sub_neg.mpr hab)
  · rw [fderiv_gradient, hb', real_inner_smul_left, inner_sub_right, hbb,
      hba]
    exact mul_pos hgσ (sub_pos.mpr hab)

theorem outwardNormal_formula : outwardNormal_formulaType := by
  intro n D U hD p ρ hρ hp
  have hc := (hD.defining p p.property).choose_spec.choose_spec
  exact normal_independent hc.2 hρ hc.1 hp p.property

theorem outwardNormal_unit : outwardNormal_unitType := by
  intro n D hD p
  have hc := (hD.defining p p.property).choose_spec.choose_spec
  exact (normal_properties hc.2 hc.1 p.property).1

theorem closure_compact : closure_compactType := by
  intro n D hD
  exact hD.bounded.isCompact_closure

theorem empty_domain : empty_domainType := by
  intro n hn
  exact ⟨hn, Bornology.isBounded_empty, isOpen_empty, by simp⟩

/-- Multiplication by a smooth weight supported inside the regularity domain
extends the product smoothly by zero, including at every artificial edge. -/
theorem contDiff_weighted_extension {n : ℕ} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {r : ℕ∞ω} {U : Set (E n)}
    {w : E n → ℝ} {g : E n → Y} (hU : IsOpen U)
    (hw : ContDiff ℝ r w) (hg : ContDiffOn ℝ r g U) (hs : tsupport w ⊆ U) :
    ContDiff ℝ r (fun x => w x • g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hw.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
  · have hz : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    apply (contDiffAt_const (c := (0 : Y))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [hy]

/-- A finite ambient smooth partition and a global Cʳ gluing of the supplied
local extensions. Compactness selects finitely many neighborhoods; their
cutoffs vanish near the edge of each local regularity domain. -/
theorem exists_finite_extension : exists_finite_extensionType := by
  classical
  intro n Y _ _ r hr K f hK hlocal
  choose U g hU hpU hg hagree using fun p : K => hlocal p p.property
  have hbump (p : K) := D04.EuclideanSmoothCutoffs.exists_smooth_cutoff
    {(p : E n)} (U p) isCompact_singleton (hU p) (singleton_subset_iff.mpr (hpU p))
  choose ρ hρ using hbump
  have hV (p : K) := (hρ p).2.2.2.1
  choose V hVo hpV hρone using hV
  have hpV' (p : K) : (p : E n) ∈ V p := hpV p (mem_singleton _)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpV' ⟨x, hx⟩⟩)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let p : Fin (Fintype.card I) → K := fun i => (e i).val
  obtain ⟨w, hwsm, hwnon, hwsupport, hwrange, hwone⟩ :=
    D04.FiniteCompactPartition.normalize_bumps (fun i => ρ (p i))
      (fun i => (hρ (p i)).1) (fun i x => (hρ (p i)).2.2.1 x |>.1)
  have hs i : tsupport (w i) ⊆ tsupport (ρ (p i)) := by
    simpa only [Function.id_def] using hwsupport (fun x : E n => x) i
  have hsU i : tsupport (w i) ⊆ U (p i) := (hs i).trans (hρ (p i)).2.2.2.2.2
  let F : E n → Y := fun x => ∑ i, w i x • g (p i) x
  have hF : ContDiff ℝ r F := ContDiff.sum (fun i _ =>
    contDiff_weighted_extension (hU (p i)) ((hwsm i).of_le hr) (hg (p i)) (hsU i))
  have hsum : ∀ x ∈ ⋃ q ∈ I, V q, ∑ i, w i x = 1 := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
    have hpi : p i = q := congrArg Subtype.val hi
    apply hwone
    have hone : ρ (p i) x = 1 := by rw [hpi]; exact hρone q hxq
    rw [← hone]
    exact Finset.single_le_sum (fun j _ => (hρ (p j)).2.2.1 x |>.1) (Finset.mem_univ i)
  refine ⟨F, Fintype.card I, U ∘ p, g ∘ p, w, ⋃ q ∈ I, V q,
    (fun i => hU (p i)), (fun i => hg (p i)), (fun i => hagree (p i)),
    hwsm, hwnon, ?_, isOpen_biUnion (fun q _ => hVo q), hI, hsum,
    (fun _ => rfl), hF, ?_⟩
  · intro i
    exact ⟨((hρ (p i)).2.2.2.2.1).of_isClosed_subset (isClosed_tsupport _) (hs i), hsU i⟩
  · intro x hx
    change ∑ i, w i x • g (p i) x = f x
    calc
      _ = ∑ i, w i x • f x := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hz : w i x = 0
        · simp [hz]
        · rw [hagree (p i) ⟨hx, hsU i (subset_tsupport _ hz)⟩]
      _ = (∑ i, w i x) • f x := Finset.sum_smul.symm
      _ = f x := by rw [hsum x (hI hx), one_smul]

theorem closure_extension : closure_extensionType := by
  intro n Y _ _ r hr D hD f hf
  obtain ⟨F, m, U, g, w, V, _, _, _, _, _, _, _, _, _, _, hF, he⟩ :=
    exists_finite_extension r hr _ f (closure_compact hD) hf
  exact ⟨F, hF, he⟩

end D04.ClassicalRegularDomains
