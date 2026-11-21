import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.MobiusEmbedding
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathGenome.Internal.MultivariableAnalysis.D04.C14.GraphTransitionsAndIntrinsicBoundary

noncomputable section
set_option autoImplicit false
open Set
open scoped RealInnerProductSpace
namespace D04.MobiusEmbedding
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.MobiusEmbedding.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model

abbrev phi := Specs.D04.C10.MobiusEmbedding.Model.phi
abbrev radius := Specs.D04.C10.MobiusEmbedding.Model.radius
abbrev rectangle := Specs.D04.C10.MobiusEmbedding.Model.rectangle
abbrev strip := Specs.D04.C10.MobiusEmbedding.Model.strip
abbrev du := Specs.D04.C10.MobiusEmbedding.Model.du
abbrev dv := Specs.D04.C10.MobiusEmbedding.Model.dv

theorem seam_identity : Specs.D04.C10.MobiusEmbedding.seam_identityType := by
  intro R p
  have hh : (p 0 + 2 * Real.pi) / 2 = p 0 / 2 + Real.pi := by ring
  ext i
  fin_cases i <;>
    simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi, radius,
      Specs.D04.C10.MobiusEmbedding.Model.radius, hh, Real.cos_add_pi,
      Real.sin_add_pi, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem smooth : Specs.D04.C10.MobiusEmbedding.smoothType := by
  intro R
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;>
    simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi,
      radius, Specs.D04.C10.MobiusEmbedding.Model.radius]
  all_goals fun_prop

lemma radius_pos {R a : ℝ} (haR : a < R) {p : E 2} (hp : |p 1| ≤ a) :
    0 < radius R p := by
  have h := abs_mul (p 1) (Real.cos (p 0 / 2))
  have hab : |p 1 * Real.cos (p 0 / 2)| ≤ a := by
    calc
      _ = |p 1| * |Real.cos (p 0 / 2)| := h
      _ ≤ |p 1| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ a := by simpa using hp
  have := (abs_le.mp hab).1
  dsimp [radius, Specs.D04.C10.MobiusEmbedding.Model.radius]
  linarith

lemma dv_norm (p : E 2) : ‖dv p‖ = 1 := by
  have h0 := Real.sin_sq_add_cos_sq (p 0)
  have h1 := Real.sin_sq_add_cos_sq (p 0 / 2)
  have hn : ‖dv p‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dv, Specs.D04.C10.MobiusEmbedding.Model.dv, Fin.sum_univ_succ,
      Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (Real.sin (p 0 / 2)),
      sq_nonneg (Real.cos (p 0 / 2))]
  nlinarith [norm_nonneg (dv p)]

lemma du_dv_inner (R : ℝ) (p : E 2) : ⟪du R p, dv p⟫ = 0 := by
  have h := Real.sin_sq_add_cos_sq (p 0)
  rw [PiLp.inner_apply]
  simp [du, dv, Specs.D04.C10.MobiusEmbedding.Model.du,
    Specs.D04.C10.MobiusEmbedding.Model.dv, Fin.sum_univ_succ]
  linear_combination -(p 1 / 2) * Real.sin (p 0 / 2) * Real.cos (p 0 / 2) * h

lemma du_norm_sq (R : ℝ) (p : E 2) :
    ‖du R p‖ ^ 2 = (radius R p) ^ 2 + (p 1) ^ 2 / 4 := by
  have h0 := Real.sin_sq_add_cos_sq (p 0)
  have h1 := Real.sin_sq_add_cos_sq (p 0 / 2)
  rw [EuclideanSpace.norm_sq_eq]
  simp [du, Specs.D04.C10.MobiusEmbedding.Model.du, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs]
  linear_combination
    ((p 1 / 2) ^ 2 * Real.sin (p 0 / 2) ^ 2 + radius R p ^ 2) * h0 +
      (p 1 / 2) ^ 2 * h1

/-- The derivative in its two tangent columns. -/
def derivative (R : ℝ) (p : E 2) : E 2 →L[ℝ] E 3 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight (du R p) +
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight (dv p)

lemma hasFDerivAt_phi (R : ℝ) (p : E 2) :
    HasFDerivAt (phi R) (derivative R p) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1
  have hh : HasFDerivAt (fun x : E 2 => x 0 / 2)
      ((2 : ℝ)⁻¹ • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) p := by
    simpa [div_eq_mul_inv] using h0.mul_const (2 : ℝ)⁻¹
  have hr := (h1.mul hh.cos).const_add R
  rw [← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp 2).mpr
  intro i
  fin_cases i
  · convert (hr.mul h0.cos).hasFDerivWithinAt using 1 <;>
      ext x <;> simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi,
        radius, Specs.D04.C10.MobiusEmbedding.Model.radius,
        derivative, du, dv, Specs.D04.C10.MobiusEmbedding.Model.du,
        Specs.D04.C10.MobiusEmbedding.Model.dv, ContinuousLinearMap.smulRight_apply] <;> ring
  · convert (hr.mul h0.sin).hasFDerivWithinAt using 1 <;>
      ext x <;> simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi,
        radius, Specs.D04.C10.MobiusEmbedding.Model.radius,
        derivative, du, dv, Specs.D04.C10.MobiusEmbedding.Model.du,
        Specs.D04.C10.MobiusEmbedding.Model.dv, ContinuousLinearMap.smulRight_apply] <;> ring
  · convert (h1.mul hh.sin).hasFDerivWithinAt using 1 <;>
      ext x <;> simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi,
        radius, Specs.D04.C10.MobiusEmbedding.Model.radius,
        derivative, du, dv, Specs.D04.C10.MobiusEmbedding.Model.du,
        Specs.D04.C10.MobiusEmbedding.Model.dv, ContinuousLinearMap.smulRight_apply] <;> ring

lemma derivative_columns (R : ℝ) (p : E 2) :
    fderiv ℝ (phi R) p (standardBasis 2 0) = du R p ∧
    fderiv ℝ (phi R) p (standardBasis 2 1) = dv p := by
  rw [(hasFDerivAt_phi R p).fderiv]
  constructor <;>
    simp [derivative, standardBasis, EuclideanSpace.basisFun_apply]

lemma derivative_injective {R a : ℝ} (haR : a < R) {p : E 2}
    (hp : |p 1| ≤ a) : Function.Injective (fderiv ℝ (phi R) p) := by
  rw [(hasFDerivAt_phi R p).fderiv]
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change derivative R p x = 0 at hx
  have hn : 0 < ‖du R p‖ ^ 2 := by
    rw [du_norm_sq]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (radius_pos haR hp)) (by positivity)
  have hinner := congrArg (fun y : E 3 => ⟪du R p, y⟫) hx
  have hinner' := congrArg (fun y : E 3 => ⟪dv p, y⟫) hx
  have horth := du_dv_inner R p
  have horth' : ⟪dv p, du R p⟫ = 0 := by rw [real_inner_comm, horth]
  simp [derivative, inner_add_right, inner_smul_right, horth, horth',
    real_inner_self_eq_norm_sq, dv_norm] at hinner hinner'
  have hdu : du R p ≠ 0 := by
    intro hz
    simpa [hz] using hn
  have hx0 : x 0 = 0 := hinner.resolve_right hdu
  ext j
  fin_cases j
  · exact hx0
  · exact hinner'

theorem quantitative_geometry : Specs.D04.C10.MobiusEmbedding.quantitative_geometryType := by
  intro R a _ haR p hp
  have hn : 0 < ‖du R p‖ ^ 2 := by
    rw [du_norm_sq]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (radius_pos haR hp)) (by positivity)
  exact ⟨radius_pos haR hp, (derivative_columns R p).1, (derivative_columns R p).2,
    dv_norm p, du_dv_inner R p, du_norm_sq R p, hn, derivative_injective haR hp⟩


lemma polar_radius_sq (R : ℝ) (p : E 2) :
    (phi R p 0) ^ 2 + (phi R p 1) ^ 2 = radius R p ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (p 0)
  simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi]
  linear_combination radius R p ^ 2 * h

lemma equal_image_radius {R a : ℝ} (haR : a < R) {p q : E 2}
    (hp : |p 1| ≤ a) (hq : |q 1| ≤ a) (h : phi R p = phi R q) :
    radius R p = radius R q := by
  have hsq : radius R p ^ 2 = radius R q ^ 2 := by
    rw [← polar_radius_sq, ← polar_radius_sq, h]
  have hpR := radius_pos haR hp
  have hqR := radius_pos haR hq
  nlinarith

lemma equal_image_angle {R a : ℝ} (haR : a < R) {p q : E 2}
    (hp : |p 1| ≤ a) (hq : |q 1| ≤ a) (h : phi R p = phi R q) :
    Real.cos (p 0) = Real.cos (q 0) ∧ Real.sin (p 0) = Real.sin (q 0) := by
  have hr := equal_image_radius haR hp hq h
  have hx := congrArg (fun x : E 3 => x 0) h
  have hy := congrArg (fun x : E 3 => x 1) h
  change radius R p * Real.cos (p 0) = radius R q * Real.cos (q 0) at hx
  change radius R p * Real.sin (p 0) = radius R q * Real.sin (q 0) at hy
  rw [← hr] at hx hy
  exact ⟨mul_left_cancel₀ (ne_of_gt (radius_pos haR hp)) hx,
    mul_left_cancel₀ (ne_of_gt (radius_pos haR hp)) hy⟩

lemma angle_alternatives {u w : ℝ} (hu : u ∈ Icc 0 (2 * Real.pi))
    (hw : w ∈ Icc 0 (2 * Real.pi))
    (hc : Real.cos u = Real.cos w) (hs : Real.sin u = Real.sin w) :
    u = w ∨ (u = 0 ∧ w = 2 * Real.pi) ∨ (w = 0 ∧ u = 2 * Real.pi) := by
  by_cases hneg : u - w = -(2 * Real.pi)
  · exact Or.inr (Or.inl ⟨by linarith [hu.1, hw.2], by linarith [hu.1, hw.2]⟩)
  by_cases hpos : u - w = 2 * Real.pi
  · exact Or.inr (Or.inr ⟨by linarith [hu.2, hw.1], by linarith [hu.2, hw.1]⟩)
  have h1 : -(2 * Real.pi) < u - w := by
    have : -(2 * Real.pi) ≤ u - w := by linarith [hu.1, hw.2]
    exact lt_of_le_of_ne this (Ne.symm hneg)
  have h2 : u - w < 2 * Real.pi := by
    have : u - w ≤ 2 * Real.pi := by linarith [hu.2, hw.1]
    exact lt_of_le_of_ne this hpos
  have hcos : Real.cos (u - w) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq w]
  exact Or.inl (sub_eq_zero.mp ((Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hcos))

lemma equal_image_same_angle {R a : ℝ} (haR : a < R) {p q : E 2}
    (hp : |p 1| ≤ a) (hq : |q 1| ≤ a) (h : phi R p = phi R q)
    (hu : p 0 = q 0) : p = q := by
  have hr := equal_image_radius haR hp hq h
  have hz := congrArg (fun x : E 3 => x 2) h
  change p 1 * Real.sin (p 0 / 2) = q 1 * Real.sin (q 0 / 2) at hz
  change R + p 1 * Real.cos (p 0 / 2) = R + q 1 * Real.cos (q 0 / 2) at hr
  rw [← hu] at hr hz
  have hv : p 1 = q 1 := by
    have ht := Real.sin_sq_add_cos_sq (p 0 / 2)
    linear_combination
      Real.cos (p 0 / 2) * hr + Real.sin (p 0 / 2) * hz - (p 1 - q 1) * ht
  ext j
  fin_cases j
  · exact hu
  · exact hv

lemma equal_image_endpoints {R : ℝ} {p q : E 2} (hp : p 0 = 0)
    (hq : q 0 = 2 * Real.pi) (h : phi R p = phi R q) : q 1 = -p 1 := by
  have hx := congrArg (fun x : E 3 => x 0) h
  simp [phi, Specs.D04.C10.MobiusEmbedding.Model.phi,
    radius, Specs.D04.C10.MobiusEmbedding.Model.radius, hp, hq] at hx
  linarith

lemma seam_image_eq {R : ℝ} {p q : E 2} (hp : p 0 = 0)
    (hq : q 0 = 2 * Real.pi) (hv : q 1 = -p 1) : phi R p = phi R q := by
  have he : q = WithLp.toLp 2 ![p 0 + 2 * Real.pi, -p 1] := by
    ext j
    fin_cases j <;> simp [hp, hq, hv]
  rw [he]
  exact (seam_identity R p).symm

theorem exact_identifications : Specs.D04.C10.MobiusEmbedding.exact_identificationsType := by
  intro R a _ haR p hp q hq
  constructor
  · intro h
    obtain ⟨hc, hs⟩ := equal_image_angle haR hp.2.2 hq.2.2 h
    rcases angle_alternatives ⟨hp.1, hp.2.1⟩ ⟨hq.1, hq.2.1⟩ hc hs with hu | hu | hu
    · exact Or.inl (equal_image_same_angle haR hp.2.2 hq.2.2 h hu)
    · exact Or.inr (Or.inl ⟨hu.1, hu.2, equal_image_endpoints hu.1 hu.2 h⟩)
    · exact Or.inr (Or.inr ⟨hu.1, hu.2, equal_image_endpoints hu.1 hu.2 h.symm⟩)
  · rintro (rfl | ⟨hp0, hq0, hv⟩ | ⟨hq0, hp0, hv⟩)
    · rfl
    · exact seam_image_eq hp0 hq0 hv
    · exact (seam_image_eq hq0 hp0 hv).symm

lemma rectangle_compact (a : ℝ) : IsCompact (rectangle a) := by
  let lower : Fin 2 → ℝ := ![0, -a]
  let upper : Fin 2 → ℝ := ![2 * Real.pi, a]
  have hc : IsCompact (Icc lower upper) := isCompact_Icc
  have he : rectangle a = WithLp.toLp 2 '' Icc lower upper := by
    ext p
    constructor
    · intro hp
      refine ⟨WithLp.ofLp p, ?_, rfl⟩
      constructor <;> intro j <;> fin_cases j
      · exact hp.1
      · exact (abs_le.mp hp.2.2).1
      · exact hp.2.1
      · exact (abs_le.mp hp.2.2).2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.1 0, hx.2 0, abs_le.mpr ⟨hx.1 1, hx.2 1⟩⟩
  rw [he]
  exact hc.image (PiLp.continuous_toLp 2 _)

theorem compact : Specs.D04.C10.MobiusEmbedding.compactType := by
  intro R a _ _
  exact (rectangle_compact a).image (smooth R).continuous

lemma seamSetoid_image {R a : ℝ} {p q : rectangle a}
    (h : (seamSetoid a).r p q) : phi R p.val = phi R q.val := by
  induction h with
  | rel p q h => exact seam_image_eq h.1 h.2.1 h.2.2
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def quotientMap (R a : ℝ) : Quotient (seamSetoid a) → E 3 :=
  Quotient.lift (fun p : rectangle a => phi R p.val) (fun _ _ h => seamSetoid_image h)

theorem quotient_embedding : Specs.D04.C10.MobiusEmbedding.quotient_embeddingType := by
  intro R a ha haR
  letI : CompactSpace (rectangle a) := isCompact_iff_compactSpace.mp (rectangle_compact a)
  have hc : Continuous (quotientMap R a) :=
    continuous_quot_lift _ ((smooth R).continuous.comp continuous_subtype_val)
  have hi : Function.Injective (quotientMap R a) := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q h
    apply Quotient.sound
    have he := (exact_identifications R a ha haR p.val p.property q.val q.property).mp h
    rcases he with he | he | he
    · have hpq : p = q := Subtype.ext he
      subst q
      exact Relation.EqvGen.refl p
    · exact Relation.EqvGen.rel p q he
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel q p he)
  refine ⟨quotientMap R a, hc.isClosedEmbedding hi |>.isEmbedding, ?_, fun _ => rfl⟩
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro p
    exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Quotient.mk (seamSetoid a) ⟨p, hp⟩, rfl⟩

/-- Compactness excludes other sheets once every point of the center fiber
has a neighborhood mapping into the proposed local patch. -/
lemma local_image_neighborhood (A : Set (E 2)) (h : E 2 → E 3)
    (hA : IsCompact A) (hh : Continuous h) (z : E 3) (S : Set (E 3))
    (hfiber : ∀ q ∈ A, h q = z → ∃ V : Set (E 2),
      IsOpen V ∧ q ∈ V ∧ MapsTo h (A ∩ V) S) :
    ∃ O : Set (E 3), IsOpen O ∧ z ∈ O ∧ (h '' A) ∩ O ⊆ S := by
  let C : Set (Set (E 2)) := {V | IsOpen V ∧ MapsTo h (A ∩ V) S}
  let G : Set (E 2) := ⋃₀ C
  have hG : IsOpen G := isOpen_sUnion (fun _ hV => hV.1)
  have hmaps : MapsTo h (A ∩ G) S := by
    rintro q ⟨hq, hqG⟩
    obtain ⟨V, hV, hqV⟩ := mem_sUnion.mp hqG
    exact hV.2 ⟨hq, hqV⟩
  have hbad : IsCompact (h '' (A \ G)) :=
    (hA.diff hG).image hh
  refine ⟨(h '' (A \ G))ᶜ, hbad.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨q, ⟨hq, hqG⟩, hqz⟩
    obtain ⟨V, hV, hqV, hm⟩ := hfiber q hq hqz
    exact hqG (mem_sUnion.mpr ⟨V, ⟨hV, hm⟩, hqV⟩)
  · rintro x ⟨⟨q, hq, rfl⟩, hx⟩
    apply hmaps
    refine ⟨hq, ?_⟩
    by_contra hqG
    exact hx ⟨q, ⟨hq, hqG⟩, rfl⟩

/-- Linear part of a boundary parameter change, with nonzero transverse scale. -/
def transverseEquiv (s : ℝ) (hs : s ≠ 0) : E 2 ≃L[ℝ] E 2 :=
  { toLinearEquiv :=
      { toFun := fun x => WithLp.toLp 2 ![x 0, s * x 1]
        invFun := fun x => WithLp.toLp 2 ![x 0, x 1 / s]
        left_inv := by intro x; ext i; fin_cases i <;> simp [hs]
        right_inv := by intro x; ext i; fin_cases i <;> simp [hs, mul_div_cancel₀]
        map_add' := by intro x y; ext i; fin_cases i <;> simp [mul_add]
        map_smul' := by intro c x; ext i; fin_cases i <;> simp [mul_left_comm] }
    continuous_toFun := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
      intro i
      fin_cases i <;> simp <;> fun_prop
    continuous_invFun := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
      intro i
      fin_cases i <;> simp <;> fun_prop }

lemma parameterChart_affine {a : ℝ} (ha : 0 < a) {p : E 2}
    (hp : |p 1| ≤ a) :
    ∃ (s : ℝ) (hs : s ≠ 0), ∀ x : E 2,
      parameterChart a p x = p + transverseEquiv s hs x := by
  by_cases he : |p 1| = a
  · have hpn : p 1 ≠ 0 := by intro hz; simp [hz] at he; linarith
    refine ⟨-(p 1 / a), neg_ne_zero.mpr (div_ne_zero hpn (ne_of_gt ha)), ?_⟩
    intro x
    ext i
    fin_cases i <;> simp [parameterChart, he, transverseEquiv] <;> ring
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x
    ext i
    fin_cases i <;> simp [parameterChart, he, transverseEquiv]

lemma parameter_neighborhood {R a : ℝ} (ha : 0 < a) (haR : a < R)
    {p : E 2} (hp : |p 1| ≤ a) :
    ∃ V : Set (E 2), IsOpen V ∧ (0 : E 2) ∈ V ∧
      (∀ x ∈ V, |parameterChart a p x 1| < R) ∧
      ∀ x ∈ V, x ∈ parameterSpace 2 (decide (|p 1| = a)) ↔
        |parameterChart a p x 1| ≤ a := by
  obtain ⟨s, hs, hβ⟩ := parameterChart_affine ha hp
  have hβc : Continuous (parameterChart a p) := by
    have he : parameterChart a p = fun x => p + transverseEquiv s hs x := funext hβ
    rw [he]
    fun_prop
  have hopen : IsOpen {x : E 2 | |parameterChart a p x 1| < R} :=
    isOpen_lt ((PiLp.continuous_apply 2 _ 1).comp hβc).abs continuous_const
  have hzero : parameterChart a p 0 = p := by
    rw [hβ]
    simp
  by_cases he : |p 1| = a
  · refine ⟨{x | |x 1| < a} ∩ {x | |parameterChart a p x 1| < R},
      (isOpen_lt (by fun_prop) continuous_const).inter hopen,
      ⟨by simpa using ha, by simpa [hzero, he] using haR⟩, fun _ hx => hx.2, ?_⟩
    intro x hx
    change |x 1| < a ∧ |parameterChart a p x 1| < R at hx
    simp only [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, he, decide_true, ite_true]
    change 0 ≤ x 1 ↔ _
    rcases (abs_eq (le_of_lt ha)).mp he with hv | hv
    · have hval : parameterChart a p x 1 = a - x 1 := by
        change (if |p 1| = a then p 1 * (1 - x 1 / a) else p 1 + x 1) = _
        rw [if_pos he, hv]
        field_simp
        <;> ring
      rw [hval]
      constructor <;> intro h
      · apply abs_le.mpr
        constructor <;> nlinarith [(abs_lt.mp hx.1).2]
      · nlinarith [(abs_le.mp h).2]
    · have hval : parameterChart a p x 1 = -a + x 1 := by
        change (if |p 1| = a then p 1 * (1 - x 1 / a) else p 1 + x 1) = _
        rw [if_pos he, hv]
        field_simp
        <;> ring
      rw [hval]
      constructor <;> intro h
      · apply abs_le.mpr
        constructor <;> nlinarith [(abs_lt.mp hx.1).2]
      · nlinarith [(abs_le.mp h).1]
  · refine ⟨{x | |parameterChart a p x 1| < a},
      isOpen_lt ((PiLp.continuous_apply 2 _ 1).comp hβc).abs continuous_const,
      by simpa [hzero] using lt_of_le_of_ne hp he,
      fun _ hx => hx.trans haR, ?_⟩
    intro x hx
    change |parameterChart a p x 1| < a at hx
    simp only [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, he, decide_false, Bool.false_eq_true, ite_false, mem_univ,
      true_iff]
    exact le_of_lt hx

lemma fiber_lift {R a : ℝ} (ha : 0 < a) (haR : a < R) {p q : E 2}
    (hp : p ∈ rectangle a) (hq : q ∈ rectangle a) (he : phi R q = phi R p) :
    ∃ T : E 2 → E 2, Continuous T ∧ T q = p ∧
      (∀ z, phi R (T z) = phi R z) ∧ ∀ z, |T z 1| = |z 1| := by
  rcases (exact_identifications R a ha haR q hq p hp).mp he with he | he | he
  · exact ⟨id, continuous_id, he, fun _ => rfl, fun _ => rfl⟩
  · refine ⟨(fun z => WithLp.toLp 2 ![z 0 + 2 * Real.pi, -z 1]), ?_, ?_,
      seam_identity R, ?_⟩
    · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
      intro i
      fin_cases i <;> simp <;> fun_prop
    · ext i
      fin_cases i <;> simp [he.1, he.2.1, he.2.2]
    · intro z
      simp
  · refine ⟨(fun z => WithLp.toLp 2 ![z 0 - 2 * Real.pi, -z 1]), ?_, ?_, ?_, ?_⟩
    · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
      intro i
      fin_cases i <;> simp <;> fun_prop
    · ext i
      fin_cases i <;> simp [he.1, he.2.1, he.2.2]
    · intro z
      have h := seam_identity R (WithLp.toLp 2 ![z 0 - 2 * Real.pi, -z 1])
      have hz : WithLp.toLp 2 ![z 0, z 1] = z := by
        ext i
        fin_cases i <;> rfl
      simpa [hz] using h.symm
    · intro z
      simp

lemma extended_image_mem {R a : ℝ} {z : E 2} (hz : |z 1| ≤ a)
    (hu : -(2 * Real.pi) ≤ z 0 ∧ z 0 ≤ 4 * Real.pi) : phi R z ∈ strip R a := by
  by_cases h0 : z 0 < 0
  · let t : E 2 := WithLp.toLp 2 ![z 0 + 2 * Real.pi, -z 1]
    refine ⟨t, ⟨?_, ?_, ?_⟩, seam_identity R z⟩
    · change 0 ≤ z 0 + 2 * Real.pi
      linarith [hu.1]
    · change z 0 + 2 * Real.pi ≤ 2 * Real.pi
      linarith
    · simpa [t] using hz
  · by_cases h2 : z 0 ≤ 2 * Real.pi
    · exact ⟨z, ⟨le_of_not_gt h0, h2, hz⟩, rfl⟩
    · let t : E 2 := WithLp.toLp 2 ![z 0 - 2 * Real.pi, -z 1]
      refine ⟨t, ⟨?_, ?_, ?_⟩, ?_⟩
      · change 0 ≤ z 0 - 2 * Real.pi
        linarith
      · change z 0 - 2 * Real.pi ≤ 2 * Real.pi
        linarith [hu.2]
      · simpa [t] using hz
      · have h := seam_identity R t
        have he : WithLp.toLp 2 ![t 0 + 2 * Real.pi, -t 1] = z := by
          ext i
          fin_cases i <;> simp [t]
        exact (he ▸ h).symm


theorem local_charts : Specs.D04.C10.MobiusEmbedding.local_chartsType := by
  intro R a ha haR p hp
  obtain ⟨s, hs, hβ⟩ := parameterChart_affine ha hp.2.2
  let L := transverseEquiv s hs
  let β : E 2 → E 2 := fun x => p + L x
  let α : E 2 → E 2 := fun y => L.symm (y - p)
  have hB : β = parameterChart a p := (funext hβ).symm
  have hαβ : ∀ x, α (β x) = x := by intro x; simp [α, β]
  have hβα : ∀ y, β (α y) = y := by intro y; simp [α, β]
  have hβ0 : β 0 = p := by simp [β]
  have hαp : α p = 0 := by simp [α]
  obtain ⟨V₀, hV₀, h0V₀, hbound₀, hcompat₀⟩ := parameter_neighborhood ha haR hp.2.2
  rw [← hB] at hbound₀ hcompat₀
  let A : Set (E 2) := {x | -(2 * Real.pi) < β x 0 ∧ β x 0 < 4 * Real.pi}
  have hA : IsOpen A := by
    have hb : Continuous (fun x : E 2 => β x 0) := by dsimp [β]; fun_prop
    exact (isOpen_lt continuous_const hb).inter (isOpen_lt hb continuous_const)
  let V := V₀ ∩ A
  have hV : IsOpen V := hV₀.inter hA
  have h0V : (0 : E 2) ∈ V := by
    refine ⟨h0V₀, ?_⟩
    change -(2 * Real.pi) < β 0 0 ∧ β 0 0 < 4 * Real.pi
    rw [hβ0]
    constructor <;> linarith [hp.1, hp.2.1, Real.pi_pos]
  have hbound : ∀ x ∈ V, |β x 1| < R := fun x hx => hbound₀ x hx.1
  have hcompat : ∀ x ∈ V, x ∈ parameterSpace 2 (decide (|p 1| = a)) ↔
      |β x 1| ≤ a := fun x hx => hcompat₀ x hx.1
  let f : E 2 → E 3 := phi R ∘ β
  have hfc : ContDiff ℝ 1 f :=
    ((smooth R).of_le (by norm_num)).comp (contDiff_const.add L.contDiff)
  have hreg : FullRankLocalExtension 1 V f := by
    intro x hx
    refine ⟨V, f, hV, hx, fun _ _ => rfl, hfc.contDiffOn, ?_⟩
    intro y hy
    have hFD : HasFDerivAt f ((derivative R (β y)).comp L.toContinuousLinearMap) y :=
      (hasFDerivAt_phi R (β y)).comp y (L.hasFDerivAt.const_add p)
    rw [hFD.fderiv, ← (hasFDerivAt_phi R (β y)).fderiv]
    exact (derivative_injective (hbound y hy) (le_refl _)).comp L.injective
  obtain ⟨sel, W, g, X, Y, q, hw⟩ :=
    D04.local_graph V f 0 false ⟨le_rfl, by norm_num⟩ (by omega)
      (by simp) ⟨V, hV, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩ hreg h0V
  let H : Set (E 2) := V ∩ X
  have hH : IsOpen H := hV.inter hw.inverse.1
  have h0H : (0 : E 2) ∈ H := ⟨h0V, hw.inverse.2.2.1⟩
  let P := Specs.D04.C14.LocalGraphAndAmbientInverse.Model.coordinateProjection sel
  let J : E 3 → E 2 := q ∘ P
  let O₁ : Set (E 3) := P ⁻¹' Y
  have hO₁ : IsOpen O₁ := hw.inverse.2.1.preimage P.continuous
  have hfO : MapsTo f H O₁ := by
    intro x hx
    have hmem : (P ∘ f) x ∈ (P ∘ f) '' (V ∩ X) := ⟨x, hx, rfl⟩
    rw [hw.projected_domain] at hmem
    exact hmem.1
  have hleft : LeftInvOn J f H := hw.inverse_left
  have hJc : ContinuousOn J O₁ := hw.inverse_ambient_regular.continuousOn
  let half := decide (|p 1| = a)
  let S : Set (E 3) := f '' (parameterSpace 2 half ∩ H)
  have hfiber : ∀ t ∈ rectangle a, phi R t = f 0 →
      ∃ U : Set (E 2), IsOpen U ∧ t ∈ U ∧ MapsTo (phi R) (rectangle a ∩ U) S := by
    intro t ht he
    have he' : phi R t = phi R p := by simpa [f, Function.comp_def, hβ0] using he
    obtain ⟨T, hTc, hTp, hTi, hTv⟩ := fiber_lift ha haR hp ht he'
    have hαc : Continuous α := by dsimp [α]; fun_prop
    refine ⟨(α ∘ T) ⁻¹' H, hH.preimage (hαc.comp hTc), ?_, ?_⟩
    · change α (T t) ∈ H
      simpa [hTp, hαp] using h0H
    · rintro z ⟨hz, hzH⟩
      have hxH : α (T z) ∈ H := hzH
      refine ⟨α (T z), ⟨?_, hxH⟩, ?_⟩
      · apply (hcompat _ hxH.1).mpr
        rw [hβα, hTv]
        exact hz.2.2
      · change phi R (β (α (T z))) = phi R z
        rw [hβα, hTi]
  obtain ⟨O₂, hO₂, hzO₂, hlocal⟩ := local_image_neighborhood (rectangle a) (phi R)
    (rectangle_compact a) (smooth R).continuous (f 0) S hfiber
  let O := O₂ ∩ O₁
  have hO : IsOpen O := hO₂.inter hO₁
  have hzO : f 0 ∈ O := ⟨hzO₂, hfO h0H⟩
  have htarget : (strip R a) ∩ O ⊆ S := by
    intro z hz
    exact hlocal ⟨hz.1, hz.2.1⟩
  have hmapM : MapsTo f (parameterSpace 2 half ∩ H) (strip R a) := by
    intro x hx
    have hwidth : |β x 1| ≤ a := (hcompat x hx.2.1).mp hx.1
    exact extended_image_mem hwidth ⟨hx.2.1.2.1.le, hx.2.1.2.2.le⟩
  let c : EmbeddedChart 1 2 3 (strip R a) :=
    { half := half
      half_pos := by intro _; decide
      source := (parameterSpace 2 half ∩ H) ∩ f ⁻¹' O
      source_open := ⟨H ∩ f ⁻¹' O, hH.inter (hO.preimage hfc.continuous), by
        ext x; simp only [mem_inter_iff, mem_preimage]; tauto⟩
      ambient := O
      ambient_open := hO
      toFun := f
      invFun := J
      map_source := by intro x hx; exact ⟨hmapM hx.1, hx.2⟩
      map_target := by
        intro z hz
        obtain ⟨x, hx, hfx⟩ := htarget hz
        have hJ : J z = x := by rw [← hfx]; exact hleft hx.2
        refine ⟨?_, ?_⟩
        · simpa only [hJ] using hx
        · change f (J z) ∈ O
          rw [hJ, hfx]
          exact hz.2
      left_inv := by intro x hx; exact hleft hx.1.2
      right_inv := by
        intro z hz
        obtain ⟨x, hx, hfx⟩ := htarget hz
        rw [← hfx, hleft hx.2]
      continuous_toFun := hfc.continuous.continuousOn
      continuous_invFun := hJc.mono (by intro z hz; exact hz.2.2)
      regular := by
        intro x hx
        obtain ⟨A, k, hA, hxA, he, hk, hD⟩ := hreg x hx.1.2.1
        refine ⟨A, k, hA, hxA, ?_, hk, hD⟩
        intro y hy
        exact he ⟨hy.1.1.2.1, hy.2⟩ }
  refine ⟨c, ⟨⟨⟨?_, h0H⟩, hzO⟩, ?_⟩, rfl, ?_, univ, isOpen_univ, mem_univ _, ?_⟩
  · by_cases he : |p 1| = a <;> simp [half, he, Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, Specs.D04.C14.EmbeddedManifoldCharts.Model.halfSpace]
  · intro _
    change (0 : E 2) 1 = 0
    rfl
  · exact congrArg (phi R) hβ0
  · intro x _
    change phi R (β x) = phi R (parameterChart a p x)
    rw [hB]

theorem embedded_manifold : Specs.D04.C10.MobiusEmbedding.embedded_manifoldType := by
  intro R a ha haR
  constructor
  · refine ⟨⟨le_rfl, by norm_num⟩, by omega, ?_⟩
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨c, hc, _, hcz, _⟩ := local_charts R a ha haR p hp
    exact ⟨c, 0, hc, hcz⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hpz⟩ := hz.1
      obtain ⟨c, hc, hhalf, hcz, _⟩ := local_charts R a ha haR p hp
      have hzin : c.toFun 0 ∈ intrinsicBoundary 1 2 (strip R a) := by
        rw [hcz, hpz]
        exact hz
      have hb := (D04.chart_intrinsicBoundary c ⟨le_rfl, by norm_num⟩
        (by omega) 0 hc.1).mp hzin
      have he : |p 1| = a := by
        have hh := hb.1
        rw [hhalf] at hh
        exact of_decide_eq_true hh
      exact ⟨p, ⟨hp, he⟩, hpz⟩
    · rintro ⟨p, ⟨hp, he⟩, rfl⟩
      obtain ⟨c, hc, hhalf, hcz, _⟩ := local_charts R a ha haR p hp
      refine ⟨⟨p, hp, rfl⟩, c, 0, ?_, hc.1, ?_, hcz⟩
      · rw [hhalf]
        exact decide_eq_true he
      · change (0 : E 2) 1 = 0
        rfl

end D04.MobiusEmbedding
