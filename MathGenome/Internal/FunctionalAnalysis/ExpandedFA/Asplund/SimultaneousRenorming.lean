import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.SimultaneousRenorming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.StrictnessPersistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.ConjugateLimits
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.NormSquareConjugate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.QuadraticSeminorms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm

noncomputable section
namespace ExpandedFA.Asplund.SimultaneousRenorming

open NormSquareConjugate QuadraticSeminormsSpec Iteration OrderLimit
open FactorFourRate StrictnessPersistence ConjugateLimits Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Changing the norm in this algebraic assertion does not change the vectors,
scalars, or any of the convexity inequalities. -/
lemma strict_square_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : V → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p) :
    SphereStrictConvex p ↔ StrictConvexOn ℝ univ (fun x => p x ^ 2) := by
  let s := P1.C01Norm.seminormOfAxioms ℝ V p hp.1
  let := P1.C01Norm.normedGroup s (fun x hx => (hp.2 x).mp hx)
  let : NormedSpace ℝ V :=
    { ‹Module ℝ V› with
      norm_smul_le := by
        intro a x
        change p (a • x) ≤ ‖a‖ * p x
        exact (hp.1.2.1 a x).le }
  exact strict_convex_square_equivalence V

lemma norm_square_properties (p : E → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p) :
    NonnegativeQuadraticConvex (fun x => p x ^ 2) :=
  seminorm_square_properties (P1.C01Norm.seminormOfAxioms ℝ E p hp.1)

lemma half_square_properties (p : E → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p) :
    NonnegativeQuadraticConvex (fun x => p x ^ 2 / 2) := by
  have h := norm_square_properties p hp
  refine ⟨fun x => by positivity, ?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := h.2.1.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    linarith
  · intro a x
    have hh := h.2.2 a x
    dsimp only at hh ⊢
    rw [hh]
    ring

lemma strict_half_square (p : E → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p)
    (hs : SphereStrictConvex p) : StrictConvexOn ℝ univ (fun x => p x ^ 2 / 2) := by
  have h := (strict_square_iff p hp).mp hs
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hh := h.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  linarith

lemma scale_equivalentNorm (p : E → ℝ) (hp : EquivalentNorm p) (c : ℝ) (hc : 0 < c) :
    EquivalentNorm (fun x => c * p x) := by
  rcases hp with ⟨hn, a, b, ha, hb, hab⟩
  refine ⟨⟨⟨fun x => mul_nonneg hc.le (hn.1.1 x), ?_, ?_⟩, ?_⟩,
    c * a, c * b, mul_pos hc ha, mul_pos hc hb, ?_⟩
  · intro r x
    change c * p (r • x) = ‖r‖ * (c * p x)
    rw [hn.1.2.1]
    ring
  · intro x y
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hn.1.2.2 x y) hc.le
  · intro x
    rw [mul_eq_zero, or_iff_right hc.ne', hn.2]
  · intro x
    constructor <;> nlinarith [(hab x).1, (hab x).2]

lemma dualNorm_normAxioms (p : E → ℝ) (hp : EquivalentNorm p) :
    P1.C01Norm.NormAxioms ℝ (dualNorm p) := by
  have hlu := dualNorm_isLUB E p hp
  refine ⟨⟨dualNorm_nonneg p hp, ?_, ?_⟩, ?_⟩
  · intro a f
    apply le_antisymm
    · apply (hlu (a • f)).2
      rintro _ ⟨x, hx, rfl⟩
      simp only [smul_apply, smul_eq_mul, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hlu f).1 ⟨x, hx, rfl⟩) (abs_nonneg a)
    · by_cases ha : a = 0
      · subst a
        simp only [_root_.norm_zero, zero_mul]
        exact dualNorm_nonneg p hp _
      · have hupper : dualNorm p f ≤ dualNorm p (a • f) / |a| := by
          apply (hlu f).2
          rintro _ ⟨x, hx, rfl⟩
          apply (le_div_iff₀ (abs_pos.mpr ha)).2
          have h := (hlu (a • f)).1 ⟨x, hx, rfl⟩
          simpa only [smul_apply, smul_eq_mul, abs_mul, mul_comm] using h
        rw [Real.norm_eq_abs]
        have hh := (le_div_iff₀ (abs_pos.mpr ha)).mp hupper
        simpa only [mul_comm] using hh
  · intro f g
    apply (hlu (f + g)).2
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_add_le (f x) (g x)).trans
      (add_le_add ((hlu f).1 ⟨x, hx, rfl⟩) ((hlu g).1 ⟨x, hx, rfl⟩))
  · intro f
    constructor
    · intro hf
      ext x
      have hx := abs_apply_le_dualNorm p hp f x
      rw [hf, zero_mul] at hx
      exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
    · intro hf
      subst f
      apply le_antisymm _ (dualNorm_nonneg p hp 0)
      apply (hlu 0).2
      rintro _ ⟨x, hx, rfl⟩
      simp

lemma dualNorm_scale (p : E → ℝ) (hp : EquivalentNorm p) (c : ℝ) (hc : 0 < c)
    (f : E →L[ℝ] ℝ) : dualNorm (fun x => c * p x) f = dualNorm p f / c := by
  have hcp := scale_equivalentNorm p hp c hc
  apply le_antisymm
  · apply (dualNorm_isLUB E _ hcp f).2
    rintro _ ⟨x, hx, rfl⟩
    have hx' : c * p x ≤ 1 := hx
    apply (le_div_iff₀ hc).2
    have h := abs_apply_le_dualNorm p hp f x
    nlinarith [dualNorm_nonneg p hp f]
  · apply (div_le_iff₀ hc).2
    apply (dualNorm_isLUB E p hp f).2
    rintro _ ⟨x, hx, rfl⟩
    have hx' : p x ≤ 1 := hx
    have hunit : c * p (c⁻¹ • x) ≤ 1 := by
      rw [hp.1.1.2.1, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
      calc c * (c⁻¹ * p x) = p x := by field_simp
           _ ≤ 1 := hx'
    have h := (dualNorm_isLUB E _ hcp f).1 ⟨c⁻¹ • x, hunit, rfl⟩
    change |f (c⁻¹ • x)| ≤ dualNorm (fun x => c * p x) f at h
    rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc] at h
    have hm := mul_le_mul_of_nonneg_left h hc.le
    have heq : c * (c⁻¹ * |f x|) = |f x| := by field_simp
    rw [heq] at hm
    simpa only [mul_comm] using hm

/-- The common continuous dual consists exactly of the linear maps bounded
for any one of the equivalent norms. Thus the supremum-defined `dualNorm p`
is taken over all continuous functionals for the topology of `p`. -/
lemma continuous_iff_norm_bound (p : E → ℝ) (hp : EquivalentNorm p) (f : E →ₗ[ℝ] ℝ) :
    Continuous f ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M * p x := by
  constructor
  · intro hf
    let g : E →L[ℝ] ℝ := ⟨f, hf⟩
    exact ⟨dualNorm p g, dualNorm_nonneg p hp g, abs_apply_le_dualNorm p hp g⟩
  · rintro ⟨M, hM, hbound⟩
    obtain ⟨a, b, ha, hb, hpb⟩ := hp.2
    have hnorm (x : E) : ‖f x‖ ≤ (M * b) * ‖x‖ := by
      rw [Real.norm_eq_abs]
      exact (hbound x).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hpb x).2 hM)
    exact (f.mkContinuous (M * b) hnorm).continuous

/-- Positive quadratic lower and upper bounds turn the common convex limit
into an equivalent norm. -/
lemma limit_norm (p r : E → ℝ) (hp : EquivalentNorm p) (hr : EquivalentNorm r)
    (h : InitialData E (fun x => p x ^ 2 / 2) (fun x => r x ^ 2 / 2)) :
    ∃ s : E → ℝ, EquivalentNorm s ∧
      ∀ x, s x ^ 2 / 2 = theta E (fun x => p x ^ 2 / 2) (fun x => r x ^ 2 / 2) x := by
  let T := theta E (fun x => p x ^ 2 / 2) (fun x => r x ^ 2 / 2)
  have hT := common_limit E _ _ h
  have hhom := theta_homogeneous E _ _ h
    (half_square_properties p hp.1).2.2 (half_square_properties r hr.1).2.2
  have hQ : NonnegativeQuadraticConvex (fun x => 2 * T x) := by
    refine ⟨fun x => mul_nonneg (by norm_num) (hT.2.2.1 x), ?_, ?_⟩
    · refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      have hh := hT.1.2 hx hy ha hb hab
      change T (a • x + b • y) ≤ a * T x + b * T y at hh
      change 2 * T (a • x + b • y) ≤ a * (2 * T x) + b * (2 * T y)
      linarith
    · intro a x
      have hh : T (a • x) = a ^ 2 * T x := hhom a x
      change 2 * T (a • x) = a ^ 2 * (2 * T x)
      rw [hh]
      ring
  let s := quadraticSqrtSeminorm hQ
  have hs2 (x : E) : s x ^ 2 = 2 * T x := Real.sq_sqrt (hQ.1 x)
  have hbounds (x : E) : r x ≤ s x ∧ s x ≤ p x := by
    have hb := theta_bounds _ _ h 0 x
    change r x ^ 2 / 2 ≤ T x ∧ T x ≤ p x ^ 2 / 2 at hb
    have hs0 := apply_nonneg s x
    have hr0 := hr.1.1.1 x
    have hp0 := hp.1.1.1 x
    constructor <;> nlinarith [hs2 x]
  obtain ⟨a, b, ha, hb, hrb⟩ := hr.2
  obtain ⟨c, d, hc, hd, hpb⟩ := hp.2
  refine ⟨s, ⟨⟨⟨fun x => apply_nonneg s x, map_smul_eq_mul s, map_add_le_add s⟩,
    ?_⟩, a, d, ha, hd, ?_⟩, ?_⟩
  · intro x
    constructor
    · intro hx
      have hn : ‖x‖ = 0 := by
        have hh := (hrb x).1.trans (hbounds x).1
        rw [hx] at hh
        nlinarith [norm_nonneg x]
      exact norm_eq_zero.mp hn
    · intro hx
      subst x
      exact map_zero s
  · intro x
    exact ⟨(hrb x).1.trans (hbounds x).1, (hbounds x).2.trans (hpb x).2⟩
  · intro x
    change s x ^ 2 / 2 = T x
    rw [hs2]
    ring

/-- The finite real representative of a continuous-dual conjugate. Its use
below is always accompanied by a proof that the conjugate is finite. -/
def realConjugate (q : E → ℝ) (f : E →L[ℝ] ℝ) : ℝ := (conjugate E q f).toReal

lemma realConjugate_coe (q : E → ℝ) (hfin : ∀ f : E →L[ℝ] ℝ, conjugate E q f < ⊤)
    (f : E →L[ℝ] ℝ) : (realConjugate q f : EReal) = conjugate E q f :=
  EReal.coe_toReal (hfin f).ne (conjugate_ne_bot E q f)

lemma realConjugate_convex (q : E → ℝ)
    (hfin : ∀ f : E →L[ℝ] ℝ, conjugate E q f < ⊤) :
    ConvexOn ℝ univ (realConjugate q) := by
  have hterm (f : E →L[ℝ] ℝ) (x : E) : f x - q x ≤ realConjugate q f := by
    apply EReal.coe_le_coe_iff.mp
    rw [realConjugate_coe q hfin, conjugate_eq]
    exact le_iSup (fun y => ((f y - q y : ℝ) : EReal)) x
  refine ⟨convex_univ, ?_⟩
  intro f _ g _ a b ha hb hab
  change realConjugate q (a • f + b • g) ≤ a * realConjugate q f + b * realConjugate q g
  apply EReal.coe_le_coe_iff.mp
  rw [realConjugate_coe q hfin, conjugate_eq]
  apply iSup_le
  intro x
  apply EReal.coe_le_coe_iff.mpr
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hf := mul_le_mul_of_nonneg_left (hterm f x) ha
  have hg := mul_le_mul_of_nonneg_left (hterm g x) hb
  nlinarith [show a * q x + b * q x = q x by rw [← add_mul, hab, one_mul]]

/-- Quadratic comparison reverses under conjugation with the same constant.
The substitution `x ↦ c⁻¹ • x` proves it without norm attainment. -/
lemma conjugate_quadratic_bound (q r : E → ℝ)
    (hq : ∀ (a : ℝ) (x : E), q (a • x) = a ^ 2 * q x)
    (c : ℝ) (hc : 0 < c) (hqr : ∀ x, q x ≤ c * r x)
    (hqfin : ∀ f : E →L[ℝ] ℝ, conjugate E q f < ⊤)
    (f : E →L[ℝ] ℝ) :
    conjugate E r f ≤ ((c * realConjugate q f : ℝ) : EReal) := by
  rw [conjugate_eq]
  apply iSup_le
  intro x
  have ht : f (c⁻¹ • x) - q (c⁻¹ • x) ≤ realConjugate q f := by
    apply EReal.coe_le_coe_iff.mp
    rw [realConjugate_coe q hqfin, conjugate_eq]
    exact le_iSup (fun y => ((f y - q y : ℝ) : EReal)) (c⁻¹ • x)
  rw [map_smul, smul_eq_mul, hq] at ht
  apply EReal.coe_le_coe_iff.mpr
  have hm := mul_le_mul_of_nonneg_left ht hc.le
  have heq : c * (c⁻¹ * f x - c⁻¹ ^ 2 * q x) = f x - q x / c := by
    field_simp
  rw [heq] at hm
  have hdiv : q x / c ≤ r x := (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hqr x)
  linarith

/-- The gap argument needs only arithmetic averaging, convexity, and the
factor-four upper error. It therefore applies directly to the conjugates. -/
lemma strict_of_arithmetic_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : ℕ → V → ℝ) (T : V → ℝ)
    (hA : ∀ n, ConvexOn ℝ univ (A n)) (hB : ∀ n, ConvexOn ℝ univ (B n))
    (hrec : ∀ n x, A (n + 1) x = (A n x + B n x) / 2)
    (C : ℝ) (hbound : ∀ n x, T x ≤ A n x ∧ A n x ≤ (1 + C / (4 : ℝ) ^ n) * T x)
    (hstrict : StrictConvexOn ℝ univ (A 0)) : StrictConvexOn ℝ univ T := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  change T (a • x + b • y) < a * T x + b * T y
  by_contra hbad
  have hgap : jensenGap T x y a b ≤ 0 := sub_nonpos.mpr (le_of_not_gt hbad)
  let d : ℕ → ℝ := fun n => (2 : ℝ) ^ n * jensenGap (A n) x y a b
  have hdmono : Monotone d := by
    apply monotone_nat_of_le_succ
    intro n
    have hq := jensenGap_nonneg (hB n) x y ha.le hb.le hab
    have heq : jensenGap (A (n + 1)) x y a b =
        (jensenGap (A n) x y a b + jensenGap (B n) x y a b) / 2 := by
      simp only [jensenGap, hrec]
      ring
    change (2 : ℝ) ^ n * _ ≤ (2 : ℝ) ^ (n + 1) * _
    rw [pow_succ, heq]
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hq]
  have hd0 : ∀ n, 0 ≤ d n := fun n => mul_nonneg (by positivity)
    (jensenGap_nonneg (hA n) x y ha.le hb.le hab)
  have hupper : ∀ n, d n ≤ (C * (a * T x + b * T y)) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hp := mul_le_mul_of_nonneg_left (hbound n x).2 ha.le
    have hq := mul_le_mul_of_nonneg_left (hbound n y).2 hb.le
    have hz := (hbound n (a • x + b • y)).1
    have hg : jensenGap (A n) x y a b ≤ C / (4 : ℝ) ^ n * (a * T x + b * T y) := by
      dsimp [jensenGap] at hgap ⊢
      nlinarith
    have hratio : (2 : ℝ) ^ n / (4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← div_pow]
      norm_num
    calc d n ≤ (2 : ℝ) ^ n * (C / (4 : ℝ) ^ n * (a * T x + b * T y)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by rw [← hratio]; ring
  have ht : Tendsto (fun n => (C * (a * T x + b * T y)) * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
      (C * (a * T x + b * T y))
  have hdlim : Tendsto d atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hd0 hupper
  have hd := hdmono.ge_of_tendsto hdlim 0
  have hs := hstrict.2 hx hy hxy ha hb hab
  change A 0 (a • x + b • y) < a * A 0 x + b * A 0 y at hs
  dsimp [d, jensenGap] at hd
  norm_num at hd
  linarith

lemma half_square_conjugate (p : E → ℝ) (hp : EquivalentNorm p) (f : E →L[ℝ] ℝ) :
    conjugate E (fun x => p x ^ 2 / 2) f = ((dualNorm p f ^ 2 / 2 : ℝ) : EReal) :=
  normSquare_conjugate E p hp f

lemma half_square_conjugate_finite (p : E → ℝ) (hp : EquivalentNorm p) :
    ∀ f : E →L[ℝ] ℝ, conjugate E (fun x => p x ^ 2 / 2) f < ⊤ := by
  intro f
  rw [half_square_conjugate p hp]
  exact EReal.coe_lt_top _

lemma realConjugate_half_square (p : E → ℝ) (hp : EquivalentNorm p) :
    realConjugate (fun x => p x ^ 2 / 2) = fun f => dualNorm p f ^ 2 / 2 := by
  funext f
  simp only [realConjugate, half_square_conjugate p hp, EReal.toReal_coe]

/-- Dual strictness follows from the conjugate arithmetic recurrence and the
primal factor-four estimate. No bidual identification is involved. -/
lemma dual_strictness (φ ψ : E → ℝ) (h : InitialData E φ ψ)
    (hφh : ∀ (a : ℝ) (x : E), φ (a • x) = a ^ 2 * φ x)
    (hψh : ∀ (a : ℝ) (x : E), ψ (a • x) = a ^ 2 * ψ x)
    (C : ℝ) (hC : 0 ≤ C) (hcomp : ∀ x, φ x ≤ (1 + C) * ψ x)
    (hfin : ∀ f : E →L[ℝ] ℝ, conjugate E ψ f < ⊤)
    (hs : StrictConvexOn ℝ univ (realConjugate ψ)) :
    StrictConvexOn ℝ univ (realConjugate (theta E φ ψ)) := by
  let T := theta E φ ψ
  let A : ℕ → (E →L[ℝ] ℝ) → ℝ := fun n => realConjugate (psi E φ ψ n)
  let B : ℕ → (E →L[ℝ] ℝ) → ℝ := fun n => realConjugate (phi E φ ψ n)
  have hψle (n : ℕ) (x : E) : ψ x ≤ psi E φ ψ n x :=
    (monotone_sequences E φ ψ h x).2 (Nat.zero_le n)
  have hψfin (n : ℕ) (f : E →L[ℝ] ℝ) : conjugate E (psi E φ ψ n) f < ⊤ :=
    lt_of_le_of_lt (conjugate_antitone _ _ (hψle n) f) (hfin f)
  have hφfin (n : ℕ) (f : E →L[ℝ] ℝ) : conjugate E (phi E φ ψ n) f < ⊤ :=
    lt_of_le_of_lt (conjugate_antitone _ _
      (fun x => (iterates_properties E φ ψ h n).2.2.2.1 x) f) (hψfin n f)
  have hTfin (f : E →L[ℝ] ℝ) : conjugate E T f < ⊤ :=
    lt_of_le_of_lt (conjugate_antitone _ _ (fun x => (theta_bounds φ ψ h 0 x).1) f) (hfin f)
  apply strict_of_arithmetic_bounds A B (realConjugate T)
    (fun n => realConjugate_convex _ (hψfin n))
    (fun n => realConjugate_convex _ (hφfin n)) ?_ C ?_ hs
  · intro n f
    have hr := psi_conjugate_recurrence E φ ψ h n f
    change conjugate E (psi E φ ψ (n + 1)) f =
      ((1 / 2 : ℝ) : EReal) * (conjugate E (phi E φ ψ n) f + conjugate E (psi E φ ψ n) f) at hr
    rw [← realConjugate_coe _ (hψfin (n + 1)),
      ← realConjugate_coe _ (hφfin n), ← realConjugate_coe _ (hψfin n),
      ← EReal.coe_add, ← EReal.coe_mul] at hr
    have he := EReal.coe_injective hr
    dsimp [A, B]
    linarith
  · intro n f
    constructor
    · apply EReal.coe_le_coe_iff.mp
      rw [realConjugate_coe _ hTfin, realConjugate_coe _ (hψfin n)]
      exact conjugate_antitone _ _ (fun x => (theta_bounds φ ψ h n x).1) f
    · have hc : 0 < 1 + C / (4 : ℝ) ^ n := by positivity
      have hq : ∀ x, T x ≤ (1 + C / (4 : ℝ) ^ n) * psi E φ ψ n x := fun x =>
        (theta_bounds φ ψ h n x).2.trans (factor_four_bound E φ ψ h hφh hψh C hC hcomp n x)
      have hb := conjugate_quadratic_bound T (psi E φ ψ n)
        (theta_homogeneous E φ ψ h hφh hψh) _ hc hq hTfin f
      apply EReal.coe_le_coe_iff.mp
      rw [realConjugate_coe _ (hψfin n)]
      exact hb

lemma strictConvex_positive_multiple {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : V → ℝ) (hq : StrictConvexOn ℝ univ q) (c : ℝ) (hc : 0 < c) :
    StrictConvexOn ℝ univ (fun x => c * q x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hh := mul_lt_mul_of_pos_left (hq.2 hx hy hxy ha hb hab) hc
  simp only [smul_eq_mul] at hh ⊢
  convert hh using 1; ring

lemma sphereStrict_of_halfSquare {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : V → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p)
    (hs : StrictConvexOn ℝ univ (fun x => p x ^ 2 / 2)) : SphereStrictConvex p := by
  apply (strict_square_iff p hp).mpr
  convert strictConvex_positive_multiple _ hs 2 (by norm_num) using 1
  ext x
  ring

/-- The combination with an ordered and quadratically comparable initial pair. -/
lemma combine_ordered_norms (p r : E → ℝ) (hp : EquivalentNorm p) (hr : EquivalentNorm r)
    (horder : ∀ x, r x ≤ p x)
    (C : ℝ) (hC : 0 ≤ C) (hcomp : ∀ x, p x ^ 2 / 2 ≤ (1 + C) * (r x ^ 2 / 2))
    (hsp : SphereStrictConvex p) (hsr : StrictConvexOn ℝ univ (fun f => dualNorm r f ^ 2 / 2)) :
    ∃ s : E → ℝ, EquivalentNorm s ∧ SphereStrictConvex s ∧ SphereStrictConvex (dualNorm s) := by
  let φ : E → ℝ := fun x => p x ^ 2 / 2
  let ψ : E → ℝ := fun x => r x ^ 2 / 2
  have h : InitialData E φ ψ := by
    refine ⟨(half_square_properties p hp.1).2.1, (half_square_properties r hr.1).2.1,
      (half_square_properties r hr.1).1, ?_, ?_, ?_⟩
    · intro x
      change r x ^ 2 / 2 ≤ p x ^ 2 / 2
      nlinarith [horder x, hr.1.1.1 x, hp.1.1.1 x]
    · change p 0 ^ 2 / 2 = 0
      rw [NormSquareConjugate.norm_zero p hp]
      norm_num
    · change r 0 ^ 2 / 2 = 0
      rw [NormSquareConjugate.norm_zero r hr]
      norm_num
  obtain ⟨s, hs, heq⟩ := limit_norm p r hp hr h
  have hEq : (fun x => s x ^ 2 / 2) = theta E φ ψ := funext heq
  have hφh := (half_square_properties p hp.1).2.2
  have hψh := (half_square_properties r hr.1).2.2
  have hsψ : StrictConvexOn ℝ univ (realConjugate ψ) := by
    change StrictConvexOn ℝ univ (realConjugate (fun x => r x ^ 2 / 2))
    rw [realConjugate_half_square r hr]
    exact hsr
  have hprimal := strictness_persistence E φ ψ h hφh hψh C hC hcomp
    (Or.inl (strict_half_square p hp.1 hsp))
  have hdual := dual_strictness φ ψ h hφh hψh C hC hcomp
    (half_square_conjugate_finite r hr) hsψ
  refine ⟨s, hs, ?_, ?_⟩
  · apply sphereStrict_of_halfSquare s hs.1
    rw [hEq]
    exact hprimal
  · apply sphereStrict_of_halfSquare (dualNorm s) (dualNorm_normAxioms s hs)
    rw [← hEq, realConjugate_half_square s hs] at hdual
    exact hdual

/-- Asplund's simultaneous renorming theorem, with the continuous dual of the
common norm topology and without a completeness assumption. -/
theorem simultaneous_renorming : Spec.SimultaneousRenorming := by
  intro E _ _ p₁ p₂ hp₁ hp₂ hs₁ hs₂
  obtain ⟨a₁, b₁, ha₁, hb₁, h₁⟩ := hp₁.2
  obtain ⟨a₂, b₂, ha₂, hb₂, h₂⟩ := hp₂.2
  let c := a₁ / b₂
  have hc : 0 < c := div_pos ha₁ hb₂
  let r : E → ℝ := fun x => c * p₂ x
  have hr : EquivalentNorm r := scale_equivalentNorm p₂ hp₂ c hc
  have horder : ∀ x, r x ≤ p₁ x := by
    intro x
    change a₁ / b₂ * p₂ x ≤ p₁ x
    have hh := mul_le_mul_of_nonneg_left (h₂ x).2 ha₁.le
    have hh' : a₁ * p₂ x / b₂ ≤ a₁ * ‖x‖ := by
      apply (div_le_iff₀ hb₂).mpr
      nlinarith
    calc a₁ / b₂ * p₂ x = a₁ * p₂ x / b₂ := by ring
         _ ≤ a₁ * ‖x‖ := hh'
         _ ≤ p₁ x := (h₁ x).1
  let K := b₁ / (c * a₂)
  have hK : 0 < K := div_pos hb₁ (mul_pos hc ha₂)
  have hratio (x : E) : p₁ x ≤ K * r x := by
    have hlo : c * a₂ * ‖x‖ ≤ r x := by
      change c * a₂ * ‖x‖ ≤ c * p₂ x
      nlinarith [(h₂ x).1]
    have hh := mul_le_mul_of_nonneg_left hlo hK.le
    have he : K * (c * a₂ * ‖x‖) = b₁ * ‖x‖ := by
      dsimp [K]
      field_simp
    rw [he] at hh
    exact (h₁ x).2.trans hh
  have hcomp (x : E) : p₁ x ^ 2 / 2 ≤ (1 + K ^ 2) * (r x ^ 2 / 2) := by
    have hh := hratio x
    have hp0 := hp₁.1.1.1 x
    have hr0 := hr.1.1.1 x
    have hsq : p₁ x ^ 2 ≤ (K * r x) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (r x)]
  have hs₂sq := strict_half_square (dualNorm p₂) (dualNorm_normAxioms p₂ hp₂) hs₂
  have hsr : StrictConvexOn ℝ univ (fun f => dualNorm r f ^ 2 / 2) := by
    have hh := strictConvex_positive_multiple _ hs₂sq (1 / c ^ 2) (by positivity)
    convert hh using 1
    ext f
    dsimp [r]
    rw [dualNorm_scale p₂ hp₂ c hc]
    field_simp
  exact combine_ordered_norms p₁ r hp₁ hr horder (K ^ 2) (sq_nonneg K) hcomp hs₁ hsr

end ExpandedFA.Asplund.SimultaneousRenorming
