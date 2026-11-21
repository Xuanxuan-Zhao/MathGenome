import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.ChebyshevMinimax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial
namespace NumAnalysis206.Approximation.Chebyshev

abbrev t := Specs.NumAnalysis206.Approximation.Chebyshev.tValue
abbrev node := Specs.NumAnalysis206.Approximation.Chebyshev.nodeValue
abbrev uniformNorm := Specs.NumAnalysis206.Approximation.Chebyshev.normValue
abbrev monicT := Specs.NumAnalysis206.Approximation.Chebyshev.monicValue
abbrev affineT := Specs.NumAnalysis206.Approximation.Chebyshev.affineValue

theorem cosine (m : ℕ) (θ : ℝ) : (t m).eval (Real.cos θ) = Real.cos (m * θ) := by
  simp [t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue,
    Polynomial.Chebyshev.T_real_cos]

theorem degree (m : ℕ) : (t m).degree = (m : WithBot ℕ) := by
  simp [t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue]

theorem leadingCoefficient (m : ℕ) : (t m).leadingCoeff = (2 : ℝ) ^ (m - 1) := by
  simp [t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue]

lemma norm_nonneg (a b : ℝ) (p : ℝ[X]) : 0 ≤ uniformNorm a b p := _root_.norm_nonneg _

lemma abs_eval_le_norm (a b : ℝ) (p : ℝ[X]) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    |p.eval x| ≤ uniformNorm a b p := by
  exact ContinuousMap.norm_coe_le_norm
    (⟨fun x : Set.Icc a b => p.eval x,
      p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ)) ⟨x, hx⟩

lemma norm_le_iff (a b : ℝ) (p : ℝ[X]) (r : ℝ) (hr : 0 ≤ r) :
    uniformNorm a b p ≤ r ↔ ∀ x ∈ Set.Icc a b, |p.eval x| ≤ r := by
  rw [uniformNorm, Specs.NumAnalysis206.Approximation.Chebyshev.normValue,
    ContinuousMap.norm_le _ hr]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

lemma norm_C_mul (a b c : ℝ) (p : ℝ[X]) :
    uniformNorm a b (C c * p) = |c| * uniformNorm a b p := by
  change ‖(⟨_, _⟩ : C(Set.Icc a b, ℝ))‖ = _
  have he : (⟨fun x : Set.Icc a b => (C c * p).eval x,
      (C c * p).continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ)) =
      c • (⟨fun x : Set.Icc a b => p.eval x,
        p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ)) := by
    ext x
    simp
  rw [he, norm_smul, Real.norm_eq_abs]
  rfl

theorem tNorm (m : ℕ) : uniformNorm (-1) 1 (t m) = 1 := by
  apply le_antisymm
  · apply (norm_le_iff _ _ _ _ (by norm_num)).2
    intro x hx
    exact Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)
  · have h := abs_eval_le_norm (-1) 1 (t m) 1 (by norm_num)
    simpa [t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue] using h

private lemma node_eq (m j : ℕ) :
    node m j = Real.cos ((2 * j + 1) * Real.pi / (2 * m)) := by
  unfold node Specs.NumAnalysis206.Approximation.Chebyshev.nodeValue
  congr 1
  ring

theorem distinctNodes (m : ℕ) : Set.InjOn (node m) (Finset.range m) := by
  intro i hi j hj hij
  apply (Finset.range m).nodup_map_iff_injOn.mp
    (Polynomial.Chebyshev.roots_T_real_nodup m) hi hj
  simpa only [node_eq] using hij

theorem roots (m : ℕ) : (t m).roots = (Multiset.range m).map (node m) := by
  rw [t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue,
    Polynomial.Chebyshev.roots_T_real]
  simp_rw [← node_eq]
  exact Finset.image_val_of_injOn (distinctNodes m)

theorem monicRoots (m : ℕ) : (monicT m).roots = (Multiset.range m).map (node m) := by
  rw [monicT, Specs.NumAnalysis206.Approximation.Chebyshev.monicValue,
    roots_C_mul _ (by positivity), roots]

theorem scaleIdentity (m : ℕ) (hm : 1 ≤ m) :
    ((2 : ℝ) ^ (m - 1))⁻¹ = (2 : ℝ) ^ (1 - (m : ℤ)) := by
  rw [show (1 - (m : ℤ)) = -((m - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]

theorem monicProperties (m : ℕ) (_hm : 1 ≤ m) :
    (monicT m).Monic ∧ (monicT m).degree = (m : WithBot ℕ) ∧
    uniformNorm (-1) 1 (monicT m) = ((2 : ℝ) ^ (m - 1))⁻¹ := by
  have hA : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
  unfold monicT Specs.NumAnalysis206.Approximation.Chebyshev.monicValue
  refine ⟨?_, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoefficient, inv_mul_cancel₀ hA]
  · rw [degree_C_mul (inv_ne_zero hA), degree]
  · rw [norm_C_mul, tNorm, mul_one, abs_of_pos (by positivity)]

/-- Equality in the coefficient extremal theorem works also for m = 1. -/
lemma eq_monicT_of_norm_le (m : ℕ) (_hm : 1 ≤ m) (q : ℝ[X])
    (hq : q.Monic) (hd : q.degree = (m : WithBot ℕ))
    (hb : uniformNorm (-1) 1 q ≤ ((2 : ℝ) ^ (m - 1))⁻¹) : q = monicT m := by
  let A : ℝ := 2 ^ (m - 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hnd : q.natDegree = m := natDegree_eq_of_degree_eq_some hd
  have hPdeg : (C A * q).degree ≤ (m : WithBot ℕ) := by
    rw [degree_C_mul hA.ne', hd]
  have hPbnd : ∀ x ∈ Set.Icc (-1) 1, |(C A * q).eval x| ≤ 1 := by
    intro x hx
    simp only [eval_mul, eval_C, abs_mul, abs_of_pos hA]
    calc A * |q.eval x| ≤ A * A⁻¹ :=
      mul_le_mul_of_nonneg_left ((abs_eval_le_norm _ _ q x hx).trans hb) hA.le
    _ = 1 := mul_inv_cancel₀ hA.ne'
  have hcoeff : (C A * q).coeff m = (2 : ℝ) ^ (m - 1) := by
    rw [coeff_C_mul, ← hnd, coeff_natDegree, hq.leadingCoeff, mul_one]
    exact congrArg (fun n => (2 : ℝ) ^ (n - 1)) hnd.symm
  have heq := (Polynomial.Chebyshev.coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).1 hcoeff
  have hh : C A⁻¹ * (C A * q) = C A⁻¹ * t m := congrArg (C A⁻¹ * ·) heq
  rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hA.ne', C_1, one_mul] at hh
  exact hh

theorem minimax (m : ℕ) (hm : 1 ≤ m) (q : ℝ[X])
    (hq : q.Monic) (hd : q.degree = (m : WithBot ℕ)) :
    ((2 : ℝ) ^ (m - 1))⁻¹ ≤ uniformNorm (-1) 1 q ∧
    (uniformNorm (-1) 1 q ≤ ((2 : ℝ) ^ (m - 1))⁻¹ ↔ q = monicT m) := by
  have hu := eq_monicT_of_norm_le m hm q hq hd
  have hn := (monicProperties m hm).2.2
  constructor
  · by_contra h
    have he := hu (le_of_lt (lt_of_not_ge h))
    rw [he, hn] at h
    exact h le_rfl
  · exact ⟨hu, fun he => by rw [he, hn]⟩

/-- Monic transport under x = c t + d, with the leading coefficient restored. -/
def transport (c d : ℝ) (m : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (c ^ m) * p.comp (C c⁻¹ * X + C (-d / c))

lemma eval_transport (c d : ℝ) (m : ℕ) (p : ℝ[X]) (x : ℝ) :
    (transport c d m p).eval x = c ^ m * p.eval ((x - d) / c) := by
  simp only [transport, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  congr 2
  ring

lemma transport_properties (c d : ℝ) (hc : c ≠ 0) (m : ℕ) (p : ℝ[X])
    (hp : p.Monic) (hd : p.degree = (m : WithBot ℕ)) :
    (transport c d m p).Monic ∧ (transport c d m p).degree = (m : WithBot ℕ) := by
  have hn : (C c⁻¹ * X + C (-d / c) : ℝ[X]).natDegree = 1 :=
    natDegree_linear (inv_ne_zero hc)
  constructor
  · rw [transport, Monic, leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_comp (by rw [hn]; norm_num), hp.leadingCoeff,
      leadingCoeff_linear (inv_ne_zero hc), natDegree_eq_of_degree_eq_some hd]
    simp [hc]
  · rw [transport, degree_C_mul (pow_ne_zero m hc),
      degree_comp (by rw [degree_linear (inv_ne_zero hc)]; norm_num),
      degree_linear (inv_ne_zero hc), mul_one, hd]

lemma transport_inverse (c d : ℝ) (hc : c ≠ 0) (m : ℕ) (p : ℝ[X]) :
    transport c d m (transport c⁻¹ (-d / c) m p) = p := by
  apply Polynomial.funext
  intro x
  rw [eval_transport, eval_transport, ← mul_assoc, ← mul_pow]
  simp only [mul_inv_cancel₀ hc, one_pow, one_mul]
  congr 1
  field_simp
  ring

lemma norm_comp_affine (c d : ℝ) (hc : 0 < c) (a b : ℝ) (p : ℝ[X]) :
    uniformNorm (c * a + d) (c * b + d)
      (p.comp (C c⁻¹ * X + C (-d / c))) = uniformNorm a b p := by
  apply le_antisymm
  · apply (norm_le_iff _ _ _ _ (norm_nonneg _ _ _)).2
    intro x hx
    have ht : (x - d) / c ∈ Set.Icc a b := by
      constructor
      · apply (le_div_iff₀ hc).2
        nlinarith [hx.1]
      · apply (div_le_iff₀ hc).2
        nlinarith [hx.2]
    have hv : (p.comp (C c⁻¹ * X + C (-d / c))).eval x = p.eval ((x - d) / c) := by
      simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
      congr 1
      ring
    rw [hv]
    exact abs_eval_le_norm _ _ _ _ ht
  · apply (norm_le_iff _ _ _ _ (norm_nonneg _ _ _)).2
    intro x hx
    have ht : c * x + d ∈ Set.Icc (c * a + d) (c * b + d) := by
      constructor <;> nlinarith [hx.1, hx.2]
    have hh := abs_eval_le_norm _ _ (p.comp (C c⁻¹ * X + C (-d / c))) _ ht
    have hv : (p.comp (C c⁻¹ * X + C (-d / c))).eval (c * x + d) = p.eval x := by
      simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
      congr 1
      field_simp
      ring
    rwa [hv] at hh

lemma norm_transport (c d : ℝ) (hc : 0 < c) (m : ℕ) (a b : ℝ) (p : ℝ[X]) :
    uniformNorm (c * a + d) (c * b + d) (transport c d m p) =
      c ^ m * uniformNorm a b p := by
  rw [transport, norm_C_mul, abs_of_pos (pow_pos hc m), norm_comp_affine c d hc]

lemma affineT_eq_transport (a b : ℝ) (hab : a < b) (m : ℕ) :
    affineT a b m = transport ((b - a) / 2) ((a + b) / 2) m (monicT m) := by
  unfold affineT Specs.NumAnalysis206.Approximation.Chebyshev.affineValue transport
  congr 2
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

private lemma affine_endpoints (a b : ℝ) :
    (b - a) / 2 * (-1) + (a + b) / 2 = a ∧
    (b - a) / 2 * 1 + (a + b) / 2 = b := by constructor <;> ring

theorem affineProperties (a b : ℝ) (hab : a < b) (m : ℕ) (hm : 1 ≤ m) :
    (affineT a b m).Monic ∧ (affineT a b m).degree = (m : WithBot ℕ) ∧
    uniformNorm a b (affineT a b m) = ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ := by
  have hc : 0 < (b - a) / 2 := by linarith
  have hp := monicProperties m hm
  rw [affineT_eq_transport a b hab m]
  refine ⟨(transport_properties _ _ hc.ne' m _ hp.1 hp.2.1).1,
    (transport_properties _ _ hc.ne' m _ hp.1 hp.2.1).2, ?_⟩
  have hh := norm_transport ((b - a) / 2) ((a + b) / 2) hc m (-1) 1 (monicT m)
  rw [(affine_endpoints a b).1, (affine_endpoints a b).2, hp.2.2] at hh
  exact hh


lemma norm_pullback (c d : ℝ) (hc : 0 < c) (m : ℕ) (p : ℝ[X]) :
    uniformNorm (-1) 1 (transport c⁻¹ (-d / c) m p) =
      (c ^ m)⁻¹ * uniformNorm (c * (-1) + d) (c * 1 + d) p := by
  have hl : c⁻¹ * (c * (-1) + d) + -d / c = -1 := by field_simp; ring
  have hr : c⁻¹ * (c * 1 + d) + -d / c = 1 := by field_simp; ring
  have hh := norm_transport c⁻¹ (-d / c) (inv_pos.mpr hc) m
    (c * (-1) + d) (c * 1 + d) p
  simpa only [hl, hr, inv_pow] using hh

lemma eq_transport_of_norm_le (c d : ℝ) (hc : 0 < c) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ[X]) (hq : q.Monic) (hd : q.degree = (m : WithBot ℕ))
    (hb : uniformNorm (c * (-1) + d) (c * 1 + d) q ≤
      c ^ m * ((2 : ℝ) ^ (m - 1))⁻¹) :
    q = transport c d m (monicT m) := by
  let r := transport c⁻¹ (-d / c) m q
  have hp := transport_properties c⁻¹ (-d / c) (inv_ne_zero hc.ne') m q hq hd
  have hr : uniformNorm (-1) 1 r ≤ ((2 : ℝ) ^ (m - 1))⁻¹ := by
    dsimp [r]
    rw [norm_pullback c d hc]
    calc (c ^ m)⁻¹ * uniformNorm (c * (-1) + d) (c * 1 + d) q ≤
        (c ^ m)⁻¹ * (c ^ m * ((2 : ℝ) ^ (m - 1))⁻¹) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((2 : ℝ) ^ (m - 1))⁻¹ := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hc.ne'), one_mul]
  have he := eq_monicT_of_norm_le m hm r hp.1 hp.2 hr
  have hh := congrArg (transport c d m) he
  rw [show transport c d m r = q from transport_inverse c d hc.ne' m q] at hh
  exact hh

theorem affineMinimax (a b : ℝ) (hab : a < b) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ[X]) (hq : q.Monic) (hd : q.degree = (m : WithBot ℕ)) :
    ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ ≤ uniformNorm a b q ∧
    (uniformNorm a b q ≤ ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ ↔
      q = affineT a b m) := by
  have hc : 0 < (b - a) / 2 := by linarith
  have hu : uniformNorm a b q ≤ ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ →
      q = affineT a b m := by
    intro hb
    rw [affineT_eq_transport a b hab m]
    apply eq_transport_of_norm_le _ _ hc m hm q hq hd
    simpa only [(affine_endpoints a b).1, (affine_endpoints a b).2] using hb
  have hn := (affineProperties a b hab m hm).2.2
  constructor
  · by_contra h
    have he := hu (le_of_lt (lt_of_not_ge h))
    rw [he, hn] at h
    exact h le_rfl
  · exact ⟨hu, fun he => by rw [he, hn]⟩

lemma nodalPolynomial (m : ℕ) :
    monicT m = ∏ j ∈ Finset.range m, (X - C (node m j)) := by
  have hr : (t m).roots.card = (t m).natDegree := by
    rw [roots, Multiset.card_map, Multiset.card_range,
      natDegree_eq_of_degree_eq_some (degree m)]
  have ht := C_leadingCoeff_mul_prod_multiset_X_sub_C hr
  have hprod : ((t m).roots.map fun x => X - C x).prod =
      ∏ j ∈ Finset.range m, (X - C (node m j)) := by
    rw [roots, Multiset.map_map]
    rfl
  rw [leadingCoefficient, hprod] at ht
  unfold monicT Specs.NumAnalysis206.Approximation.Chebyshev.monicValue
  change C ((2 ^ (m - 1) : ℝ)⁻¹) * t m = _
  rw [← ht, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by positivity), C_1, one_mul]

lemma transport_nodalPolynomial (c d : ℝ) (hc : c ≠ 0) (m : ℕ) :
    transport c d m (monicT m) =
      ∏ j ∈ Finset.range m, (X - C (d + c * node m j)) := by
  apply Polynomial.funext
  intro x
  rw [eval_transport, nodalPolynomial]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  calc c ^ m * ∏ j ∈ Finset.range m, ((x - d) / c - node m j) =
      (∏ _j ∈ Finset.range m, c) *
        ∏ j ∈ Finset.range m, ((x - d) / c - node m j) := by simp
  _ = ∏ j ∈ Finset.range m, (c * ((x - d) / c - node m j)) :=
    Finset.prod_mul_distrib.symm
  _ = ∏ j ∈ Finset.range m, (x - (d + c * node m j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    field_simp
    ring

theorem affineNodalPolynomial (a b : ℝ) (hab : a < b) (m : ℕ) (_hm : 1 ≤ m) :
    affineT a b m = ∏ j ∈ Finset.range m,
      (X - C ((a + b) / 2 + (b - a) / 2 * node m j)) := by
  rw [affineT_eq_transport a b hab m]
  exact transport_nodalPolynomial _ _ (by linarith) m

end NumAnalysis206.Approximation.Chebyshev
