import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ExceptionalAddition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusCubicBiholomorphism
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The exceptional chord--tangent cases for the literal lattice cubic.
The polynomial restrictions count intersections on the actual projective lines,
including repeated finite intersections. Parity of wp and its derivative then
identifies the geometric reflection with inversion of the actual torus class. -/
noncomputable section
open Set Polynomial
open scoped Classical BigOperators
namespace D12Complex.ExceptionalAddition
open ProjectivePlaneTopology CubicFiniteCharts CubicInfinityChart TorusSurface
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open TorusCubicLocalMap (phi)

lemma finite_polynomial_factorization (b : ℂ) :
    (X : ℂ[X])^2 - C (b^2) = (X-C b)*(X-C (-b)) := by
  simp only [map_neg, map_pow]
  ring

lemma finite_polynomial_multiplicity (b c : ℂ) :
    rootMultiplicity c ((X : ℂ[X])^2-C (b^2)) =
      (if c=b then 1 else 0) + (if c=-b then 1 else 0) := by
  rw [finite_polynomial_factorization,
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]

lemma vertical_infinity_multiplicity (d : ℂ) :
    rootMultiplicity (0 : ℂ) ((X : ℂ[X])*(1-C d*X^2)) = 1 := by
  have hn : (1 : ℂ[X])-C d*X^2 ≠ 0 := by
    intro h
    have := congrArg (fun p : ℂ[X] => p.eval 0) h
    simp at this
  rw [rootMultiplicity_mul (mul_ne_zero X_ne_zero hn)]
  have he : rootMultiplicity (0 : ℂ) ((1 : ℂ[X])-C d*X^2) = 0 := by
    apply rootMultiplicity_eq_zero
    simp [Polynomial.IsRoot]
  rw [he, add_zero]
  simpa using (rootMultiplicity_X_sub_C_self (x := (0 : ℂ)))

lemma infinity_tangent_multiplicity :
    rootMultiplicity (0 : ℂ) infinityTangentPolynomial = 3 := by
  unfold infinityTangentPolynomial
  rw [rootMultiplicity_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ X_ne_zero)),
    rootMultiplicity_C, zero_add]
  simpa using (rootMultiplicity_X_sub_C_pow (0 : ℂ) 3)

theorem tangent_differential :
    Specs.D12Complex.Ch22.ExceptionalAddition.tangent_differential_type := by
  intro G H v w
  have hd (i : Fin 3) : HasDerivAt (fun t : ℂ => v i+t*w i) (w i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (w i)).const_add (v i)
  have ht := (((hd 2).pow 2 |>.mul (hd 0)).sub ((hd 1).pow 3 |>.const_mul 4) |>.add
    (((hd 1).const_mul G).mul ((hd 0).pow 2))) |>.add ((hd 0).pow 3 |>.const_mul H)
  convert ht using 1
  · ext t
    simp [homogeneousEquation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp [lineValue, tangentForm, Fin.sum_univ_succ]
    ring

theorem line_restrictions :
    Specs.D12Complex.Ch22.ExceptionalAddition.line_restrictions_type := by
  intro G H a
  constructor
  · intro t
    simp [verticalFinitePolynomial, homogeneousEquation, q]
    ring
  constructor
  · intro s
    simp [verticalInfinityPolynomial, homogeneousEquation, q]
    ring
  · intro s
    simp [infinityTangentPolynomial, homogeneousEquation]

lemma vertical_factorization (G H a b s t : ℂ) (hab : b^2=q G H a) :
    homogeneousEquation G H ![s,a*s,t] = s*(t-b*s)*(t+b*s) := by
  unfold q at hab
  simp [homogeneousEquation]
  linear_combination s^3 * hab

theorem vertical_multiplicities :
    Specs.D12Complex.Ch22.ExceptionalAddition.vertical_multiplicities_type := by
  intro G H a b hab
  constructor
  · intro c
    simpa only [verticalFinitePolynomial, ←hab] using finite_polynomial_multiplicity b c
  · exact vertical_infinity_multiplicity (q G H a)

lemma tangent_at_branch (G H a : ℂ) (ha : q G H a = 0) :
    tangentForm G H ![1,a,0] = (G-12*a^2) • verticalForm a := by
  unfold q at ha
  ext i
  fin_cases i <;> simp [tangentForm, verticalForm]
  · linear_combination -3*ha
  · ring

lemma tangent_at_infinity (G H : ℂ) :
    tangentForm G H ![0,0,1] = infinityForm := by
  ext i
  fin_cases i <;> simp [tangentForm, infinityForm]

theorem vertical_tangent :
    Specs.D12Complex.Ch22.ExceptionalAddition.vertical_tangent_type := by
  intro ω₁ ω₂ h₁ h₂ a ha
  refine ⟨g₂ ω₁ ω₂-12*a^2, ?_, tangent_at_branch _ _ a ha, ?_⟩
  · have hn := CubicFiniteCharts.cubic_derivative_ne_zero
      (Ch22.HalfPeriodValues.discriminant ω₁ ω₂ h₁ h₂) ha
    intro h
    apply hn
    linear_combination -h
  · have hm := (vertical_multiplicities (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a 0
      (by simpa only [zero_pow (by decide : 2 ≠ 0)] using ha.symm)).1 0
    simpa using hm

lemma lineValue_smul (L v : Fin 3 → ℂ) (t : ℂ) :
    lineValue L (t • v)=t*lineValue L v := by
  simp only [lineValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma onLine_projection_iff (L : Fin 3 → ℂ) (v : HomogeneousVector) :
    OnLine L (projection v) ↔ lineValue L v.val=0 := by
  constructor
  · rintro ⟨w, he, hw⟩
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ w.property v.property).mp he
    rw [← ht] at hw
    change lineValue L ((t : ℂ) • v.val)=0 at hw
    rw [lineValue_smul] at hw
    exact (mul_eq_zero.mp hw).resolve_left t.ne_zero
  · intro h
    exact ⟨v,rfl,h⟩

lemma onLine_affinePoint_iff (L : Fin 3 → ℂ) (a b : ℂ) :
    OnLine L (affinePoint a b) ↔ L 0+L 1*a+L 2*b=0 := by
  change OnLine L (projection _) ↔ _
  rw [onLine_projection_iff]
  change lineValue L ![1,a,b]=0 ↔ _
  simp [lineValue, Fin.sum_univ_succ]
  ring_nf

lemma onLine_O_iff (L : Fin 3 → ℂ) : OnLine L O ↔ L 2=0 := by
  change OnLine L (projection _) ↔ _
  rw [onLine_projection_iff]
  change lineValue L ![0,0,1]=0 ↔ _
  simp [lineValue, Fin.sum_univ_succ]

lemma vertical_affine (a x y : ℂ) :
    OnLine (verticalForm a) (affinePoint x y) ↔ x=a := by
  simp [onLine_affinePoint_iff, verticalForm]
  constructor <;> intro h <;> linear_combination h

lemma vertical_O (a : ℂ) : OnLine (verticalForm a) O := by
  simp [onLine_O_iff, verticalForm]

lemma vertical_intersections_iff (G H a b : ℂ) (hb : b^2=q G H a)
    (p : ComplexProjectivePlane) (hp : OnCubic G H p) :
    OnLine (verticalForm a) p ↔ p=affinePoint a b ∨p=affinePoint a (-b) ∨p=O := by
  by_cases hf : p∈coordinatePatch 0
  · have hcoords := affinePoint_coordinates hf
    have he := (D12Complex.CubicFiniteCharts.affine_equation G H p hf).mp hp
    constructor
    · intro hl
      rw [←hcoords, vertical_affine] at hl
      have hy : finiteY p=b ∨finiteY p= -b := by
        rw [hl, ← hb] at he
        exact sq_eq_sq_iff_eq_or_eq_neg.mp he
      rcases hy with h|h
      · exact Or.inl (by rw [←hcoords,hl,h])
      · exact Or.inr (Or.inl (by rw [←hcoords,hl,h]))
    · rintro (rfl|rfl|rfl)
      · exact (vertical_affine _ _ _).mpr rfl
      · exact (vertical_affine _ _ _).mpr rfl
      · exact vertical_O a
  · have hO := eq_O_of_not_finite G H hp hf
    subst p
    exact iff_of_true (vertical_O a) (Or.inr (Or.inr rfl))

lemma line_through_coefficients (L : Fin 3 → ℂ) (a b : ℂ) (hL : L≠0)
    (hO : OnLine L O) (hP : OnLine L (affinePoint a b)) :
    ∃ k : ℂ, k≠0 ∧ L=k • verticalForm a := by
  have h2 : L 2=0 := (onLine_O_iff L).mp hO
  have h0 : L 0= -(L 1*a) := by
    have h := (onLine_affinePoint_iff L a b).mp hP
    simp only [h2,mul_zero,add_zero] at h
    linear_combination h
  refine ⟨L 1,?_,?_⟩
  · intro h1
    apply hL
    ext i
    fin_cases i <;> simp [h0,h1,h2]
  · ext i
    fin_cases i <;> simp [verticalForm, h0,h2]

lemma infinity_line_projection (v : HomogeneousVector) :
    OnLine infinityForm (projection v) ↔ v.val 0=0 := by
  simp [onLine_projection_iff, lineValue, infinityForm, Fin.sum_univ_succ]

lemma infinity_line_iff (p : ComplexProjectivePlane) :
    OnLine infinityForm p ↔ p∉coordinatePatch 0 := by
  induction p using Projectivization.ind with | h v hv =>
  change OnLine infinityForm (projection ⟨v,hv⟩) ↔ projection ⟨v,hv⟩∉coordinatePatch 0
  rw [projection_mem_patch_iff]
  simpa using infinity_line_projection ⟨v,hv⟩

lemma infinity_intersections (G H : ℂ) (p : ComplexProjectivePlane) (hp : OnCubic G H p) :
    OnLine infinityForm p ↔ p=O := by
  rw [infinity_line_iff]
  exact (D12Complex.CubicInfinityChart.unique_infinity G H).2.2 p hp

theorem vertical_intersections :
    Specs.D12Complex.Ch22.ExceptionalAddition.vertical_intersections_type := by
  intro G H a b hab
  refine ⟨?_, fun s t => vertical_factorization G H a b s t hab, ?_⟩
  · intro h
    have := congrFun h 1
    simp [verticalForm] at this
  · exact fun p hp => vertical_intersections_iff G H a b hab p hp

theorem line_through_origin :
    Specs.D12Complex.Ch22.ExceptionalAddition.line_through_origin_type :=
  line_through_coefficients

theorem infinity_tangent :
    Specs.D12Complex.Ch22.ExceptionalAddition.infinity_tangent_type := by
  intro G H
  refine ⟨tangent_at_infinity G H, ?_, infinity_intersections G H, infinity_tangent_multiplicity⟩
  intro h
  have := congrFun h 0
  simp [infinityForm] at this

end D12Complex.ExceptionalAddition

namespace D12Complex.ExceptionalAddition.Transport
open D12Complex TorusSurface CubicFiniteCharts CubicInfinityChart
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Specs.D12Complex.Ch22.HalfPeriodValues (halfPeriod branchValue)
open _root_.D12Complex.TorusCubicLocalMap (phi)

abbrev E (ω₁ ω₂ : ℂ) := Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)

def zero {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) : E ω₁ ω₂ := e 0

lemma add_assoc {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P Q R : E ω₁ ω₂) :
    transportedAdd e (transportedAdd e P Q) R = transportedAdd e P (transportedAdd e Q R) := by
  simp [transportedAdd, _root_.add_assoc]
lemma add_comm {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P Q : E ω₁ ω₂) :
    transportedAdd e P Q = transportedAdd e Q P := by
  simp [transportedAdd, _root_.add_comm]
lemma zero_add {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P : E ω₁ ω₂) :
    transportedAdd e (zero e) P = P := by simp [transportedAdd, zero]
lemma add_zero {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P : E ω₁ ω₂) :
    transportedAdd e P (zero e) = P := by simp [transportedAdd, zero]
lemma neg_add {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P : E ω₁ ω₂) :
    transportedAdd e (transportedNeg e P) P = zero e := by simp [transportedAdd, transportedNeg, zero]
lemma add_neg {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P : E ω₁ ω₂) :
    transportedAdd e P (transportedNeg e P) = zero e := by simp [transportedAdd, transportedNeg, zero]
lemma neg_zero {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) :
    transportedNeg e (zero e) = zero e := by simp [transportedNeg, zero]
lemma neg_neg {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (P : E ω₁ ω₂) :
    transportedNeg e (transportedNeg e P) = P := by simp [transportedNeg]

lemma zero_val {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t) :
    (zero e).val = O := by
  exact (he 0).trans (_root_.D12Complex.TorusCubicLocalMap.phi_zero h₁ h₂)

lemma exists_equiv {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    ∃ e : Torus ω₁ ω₂ ≃ E ω₁ ω₂, ∀ t, (e t).val = phi ω₁ ω₂ t := by
  obtain ⟨d, S, T, h, hd, hS, hcT, hcE, hT, hh, hrest⟩ :=
    TorusCubicBiholomorphism.biholomorphism ω₁ ω₂ h₁ h₂
  exact ⟨h.toEquiv, hh⟩

lemma add_apply {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (z w : Torus ω₁ ω₂) :
    transportedAdd e (e z) (e w) = e (z + w) := by simp [transportedAdd]

lemma eq_zero_of_val {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : E ω₁ ω₂) (hP : P.val = O) : P = zero e := by
  exact Subtype.ext (hP.trans (zero_val h₁ h₂ e he).symm)

lemma origin_add {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P P0 : E ω₁ ω₂) (hP0 : P0.val = O) :
    transportedAdd e P0 P = P ∧ transportedAdd e P P0 = P := by
  rw [eq_zero_of_val h₁ h₂ e he P0 hP0]
  exact ⟨zero_add e P, add_zero e P⟩

lemma e_neg_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (t : Torus ω₁ ω₂) (x y : ℂ) (hP : (e t).val = affinePoint x y) :
    (e (-t)).val = affinePoint x (-y) := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup t
  change (e (-projection ω₁ ω₂ z)).val = _
  change (e (projection ω₁ ω₂ z)).val = _ at hP
  have hz : z ∉ lattice ω₁ ω₂ := by
    intro hz
    have ht : projection ω₁ ω₂ z = 0 := (Ch22.HalfPeriodValues.projection_zero_iff z).mpr hz
    rw [ht, he, _root_.D12Complex.TorusCubicLocalMap.phi_zero h₁ h₂] at hP
    exact O_not_mem_finitePatch (hP.symm ▸ affinePoint_mem_patch x y)
  have hnz : -z ∉ lattice ω₁ ω₂ := by simpa using hz
  have hxy : affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) =
      affinePoint x y := by
    rw [he, _root_.D12Complex.TorusCubicLocalMap.phi_finite h₁ h₂ hz] at hP
    exact hP
  have hx : weierstrassP ω₁ ω₂ z = x := by
    simpa only [finiteX_affinePoint] using congrArg finiteX hxy
  have hy : deriv (weierstrassP ω₁ ω₂) z = y := by
    simpa only [finiteY_affinePoint] using congrArg finiteY hxy
  rw [← map_neg, he, _root_.D12Complex.TorusCubicLocalMap.phi_finite h₁ h₂ hnz]
  change affinePoint (weierstrassP ω₁ ω₂ (-z)) (deriv (weierstrassP ω₁ ω₂) (-z)) = _
  have hEven : weierstrassP ω₁ ω₂ (-z) = weierstrassP ω₁ ω₂ z :=
    (Ch22.WeierstrassSeries.periodPair h₁ h₂).weierstrassP_neg z
  rw [hEven,
    TorusCubicBiholomorphism.Fibres.deriv_neg h₁ h₂ z, hx, hy]

lemma neg_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : E ω₁ ω₂) (x y : ℂ) (hP : P.val = affinePoint x y) :
    (transportedNeg e P).val = affinePoint x (-y) := by
  exact e_neg_finite h₁ h₂ e he (e.symm P) x y (by simpa using hP)

lemma vertical_add {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P Q : E ω₁ ω₂) (x y : ℂ)
    (hP : P.val = affinePoint x y) (hQ : Q.val = affinePoint x (-y)) :
    (transportedAdd e P Q).val = O := by
  have hQn : Q = transportedNeg e P :=
    Subtype.ext (hQ.trans (neg_finite h₁ h₂ e he P x y hP).symm)
  rw [hQn, add_neg]
  exact zero_val h₁ h₂ e he

lemma double_y_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : E ω₁ ω₂) (x : ℂ) (hP : P.val = affinePoint x 0) :
    transportedAdd e P P = zero e := by
  have hn : transportedNeg e P = P := by
    apply Subtype.ext
    rw [hP]
    simpa only [_root_.neg_zero] using neg_finite h₁ h₂ e he P x 0 hP
  simpa only [hn] using neg_add e P

lemma y_zero_halfPeriod {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : E ω₁ ω₂) (x : ℂ) (hP : P.val = affinePoint x 0) :
    ∃ i : Fin 3, P = e (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) := by
  have hnP : transportedNeg e P = P := by
    apply Subtype.ext
    rw [hP]
    simpa only [_root_.neg_zero] using neg_finite h₁ h₂ e he P x 0 hP
  have ht0 : e.symm P ≠ 0 := by
    intro h0
    have hh := he (e.symm P)
    simp only [e.apply_symm_apply] at hh
    rw [h0, _root_.D12Complex.TorusCubicLocalMap.phi_zero h₁ h₂] at hh
    exact O_not_mem_finitePatch ((hh.symm.trans hP).symm ▸ affinePoint_mem_patch x 0)
  have hneg : -e.symm P = e.symm P := by
    simpa only [transportedNeg, e.symm_apply_apply] using congrArg e.symm hnP
  have ht2 : (2 : ℕ) • e.symm P = 0 := by
    rw [two_nsmul]
    calc
      e.symm P + e.symm P = -e.symm P + e.symm P :=
        congrArg (· + e.symm P) hneg.symm
      _ = 0 := neg_add_cancel _
  obtain ⟨i, hi⟩ := ((Ch22.HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.2 (e.symm P)).mp ⟨ht0, ht2⟩
  exact ⟨i, (e.apply_symm_apply P).symm.trans (congrArg e hi)⟩

lemma halfPeriod_val {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (he : ∀ t, (e t).val = phi ω₁ ω₂ t) (i : Fin 3) :
    (e (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))).val =
      affinePoint (branchValue ω₁ ω₂ i) 0 := by
  have hnot := (Ch22.HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.1 i
  rw [he, _root_.D12Complex.TorusCubicLocalMap.phi_finite h₁ h₂ hnot]
  have hd := (Ch22.HalfPeriodValues.zeros ω₁ ω₂ h₁ h₂ _ hnot).mpr ⟨i, rfl⟩
  rw [hd]
  rfl

lemma halfPeriod_double {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) (i : Fin 3) :
    transportedAdd e (e (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)))
      (e (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))) = zero e := by
  have hh := ((Ch22.HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.2
    (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))).mpr ⟨i, rfl⟩
  simpa only [transportedAdd, zero, e.symm_apply_apply, two_nsmul] using congrArg e hh.2
end D12Complex.ExceptionalAddition.Transport

namespace D12Complex.ExceptionalAddition
open CubicFiniteCharts CubicInfinityChart TorusSurface
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Specs.D12Complex.Ch22.HalfPeriodValues (halfPeriod branchValue)
open _root_.D12Complex.TorusCubicLocalMap (phi)

theorem equivalence_exists : Specs.D12Complex.Ch22.ExceptionalAddition.equivalence_exists_type := by
  intro ω₁ ω₂ h₁ h₂
  exact Transport.exists_equiv h₁ h₂

theorem addition_agreement : Specs.D12Complex.Ch22.ExceptionalAddition.addition_agreement_type := by
  intro ω₁ ω₂ e he t s
  simpa only [transportedAdd, e.symm_apply_apply] using he (t+s)

theorem inverse_finite : Specs.D12Complex.Ch22.ExceptionalAddition.inverse_finite_type := by
  intro ω₁ ω₂ h₁ h₂ e he P x y hP
  refine ⟨Transport.neg_finite h₁ h₂ e he P x y hP, ?_, ?_⟩
  · exact (congrArg Subtype.val (Transport.add_neg e P)).trans (Transport.zero_val h₁ h₂ e he)
  · exact (congrArg Subtype.val (Transport.neg_add e P)).trans (Transport.zero_val h₁ h₂ e he)

theorem opposites : Specs.D12Complex.Ch22.ExceptionalAddition.opposites_type := by
  intro ω₁ ω₂ h₁ h₂ e he P Q x y hP hQ
  exact Transport.vertical_add h₁ h₂ e he P Q x y hP hQ

theorem identity : Specs.D12Complex.Ch22.ExceptionalAddition.identity_type := by
  intro ω₁ ω₂ h₁ h₂ e he P0 hP0
  exact ⟨fun P => Transport.origin_add h₁ h₂ e he P P0 hP0,
    (Transport.origin_add h₁ h₂ e he P0 P0 hP0).1⟩

theorem half_period : Specs.D12Complex.Ch22.ExceptionalAddition.half_period_type := by
  intro ω₁ ω₂ h₁ h₂ e he
  constructor
  · intro P x hP
    exact ⟨(congrArg Subtype.val (Transport.double_y_zero h₁ h₂ e he P x hP)).trans
      (Transport.zero_val h₁ h₂ e he), Transport.y_zero_halfPeriod h₁ h₂ e he P x hP⟩
  · intro i
    exact ⟨Transport.halfPeriod_val h₁ h₂ e he i,
      (congrArg Subtype.val (Transport.halfPeriod_double h₁ h₂ e i)).trans
        (Transport.zero_val h₁ h₂ e he)⟩
end D12Complex.ExceptionalAddition
