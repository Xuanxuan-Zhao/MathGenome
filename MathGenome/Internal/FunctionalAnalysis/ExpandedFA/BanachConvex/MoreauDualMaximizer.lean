import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.MoreauDualMaximizer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.StrictDualSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelRockafellar
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.FieldSimp

/-! The dual stage of the Banach Moreau theorem, paper.tex:8284–8339.
Finiteness follows from separation of the closed convex epigraph. The accepted
Fenchel–Rockafellar theorem gives attained duality with the continuous shifted
quadratic. A midpoint gap proves uniqueness and uniform norm continuity on
bounded sets directly; no primal minimizer or strict convexity of X is used. -/

set_option backward.isDefEq.respectTransparency false

namespace ExpandedFA.BanachConvex.Moreau
open Set Filter P1.ExtendedConvexFunctions
open scoped Topology
local notation "val" => P1.C06Conjugates.Spec.ExtendedRealValueValue
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A proper closed convex epigraph has a continuous affine minorant.
Separating a point directly below a finite epigraph point makes the
vertical coefficient strictly positive, even when the domain has empty interior. -/
lemma exists_affine_minorant (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ), ∀ y, ((f y + c : ℝ) : WithTop ℝ) ≤ φ y := by
  obtain ⟨x₀, r, hr⟩ := (P1.ExtendedConvexFunctions.proper_iff_finite_value X φ).mp hp
  have hepc := (P1.ExtendedConvexFunctions.convex_iff_convex_epigraph X φ).mp hc
  have hepl := (P1.ExtendedConvexFunctions.lowerSemicontinuous_iff_closed_epigraph X φ).mp hl
  have hout : (x₀, r - 1) ∉ realEpigraph X φ := by
    change ¬ φ x₀ ≤ ((r - 1 : ℝ) : WithTop ℝ)
    rw [hr, WithTop.coe_le_coe]
    linarith
  obtain ⟨g, d, hlow, hupp⟩ := geometric_hahn_banach_point_closed hepc hepl hout
  let l : X →L[ℝ] ℝ := g.comp (ContinuousLinearMap.inl ℝ X ℝ)
  let b : ℝ := g (0, 1)
  have hg (y : X) (t : ℝ) : g (y, t) = l y + t * b := by
    have heq : (y, t) = (y, (0 : ℝ)) + t • ((0 : X), (1 : ℝ)) := by simp
    rw [heq, map_add, map_smul]
    rfl
  have hb : 0 < b := by
    have hu := hupp (x₀, r) (by change φ x₀ ≤ _; rw [hr])
    rw [hg] at hlow hu
    nlinarith
  refine ⟨-(b⁻¹ • l), d / b, ?_⟩
  intro y
  by_cases hy : φ y = ⊤
  · rw [hy]; exact le_top
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  have hu := hupp (y, s) (by change φ y ≤ _; rw [← hs])
  rw [hg] at hu
  rw [← hs, WithTop.coe_le_coe]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  have hd : d / b < (l y + s * b) / b := (div_lt_div_iff_of_pos_right hb).mpr hu
  rw [add_div, mul_div_cancel_right₀ _ hb.ne'] at hd
  simpa only [div_eq_mul_inv, mul_comm] using (show -(l y / b) + d / b ≤ s by linarith)

lemma quadratic_lower_bound (n : ℝ) (hn : 0 < n) (f : X →L[ℝ] ℝ)
    (x y : X) :
    f x - ‖f‖ ^ 2 / (2 * n) ≤ f y + n * ‖x - y‖ ^ 2 / 2 := by
  have heval : f (x - y) ≤ ‖f‖ * ‖x - y‖ :=
    (le_abs_self _).trans (f.le_opNorm _)
  rw [map_sub] at heval
  have hs := sq_nonneg (n * ‖x - y‖ - ‖f‖)
  have heq : (‖f‖ ^ 2 / (2 * n)) * (2 * n) = ‖f‖ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- Finiteness does not use completeness or uniform convexity. -/
lemma primal_finite (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (x : X) :
    primal φ n x = (envelope φ n x : EReal) := by
  obtain ⟨f, c, hminor⟩ := exists_affine_minorant φ hp hc hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbelow : ((f x + c - ‖f‖ ^ 2 / (2 * n) : ℝ) : EReal) ≤ primal φ n x := by
    apply le_iInf
    intro y
    calc
      _ ≤ ((f y + c + n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by linarith [quadratic_lower_bound (n : ℝ) hn' f x y])
      _ = val ((f y + c : ℝ) : WithTop ℝ) +
          ((n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) := by rw [EReal.coe_add]; rfl
      _ ≤ _ := add_le_add (WithBot.coe_le_coe.mpr (hminor y)) le_rfl
  obtain ⟨y, r, hr⟩ := (P1.ExtendedConvexFunctions.proper_iff_finite_value X φ).mp hp
  have habove : primal φ n x ≤ ((r + n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal) := by
    have h := iInf_le (fun y => val (φ y) + ((n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal)) y
    simpa only [primal, hr, show val (r : WithTop ℝ) = (r : EReal) from rfl, ← EReal.coe_add] using h
  exact (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) habove)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbelow)).symm

/-- The continuous quadratic in the Fenchel–Rockafellar pair. -/
noncomputable def kernel (n : ℕ) (x : X) : ExtendedFunction X :=
  fun y => ((n * ‖x - y‖ ^ 2 / 2 : ℝ) : WithTop ℝ)

omit [NormedSpace ℝ X] in
lemma kernel_continuous (n : ℕ) (x : X) : Continuous (kernel n x) := by
  exact WithTop.continuous_coe.comp (by fun_prop)

lemma kernel_convex (n : ℕ) (x : X) : ExtendedConvex X (kernel n x) := by
  intro y z r s a b hyr hzs ha hb hab
  have hq := halfNormSquare_convex (X := X) (x-y) (x-z)
    (‖x-y‖^2/2) (‖x-z‖^2/2) a b rfl rfl ha hb hab
  have heq : a • (x-y) + b • (x-z) = x - (a • y + b • z) := by
    calc
      _ = (a+b) • x - (a • y + b • z) := by module
      _ = _ := by rw [hab, one_smul]
  change ((‖a • (x-y) + b • (x-z)‖^2/2 : ℝ) : WithTop ℝ) ≤ _ at hq
  rw [heq, WithTop.coe_le_coe] at hq
  have hyr' : (n : ℝ) * ‖x-y‖^2/2 = r := WithTop.coe_inj.mp hyr
  have hzs' : (n : ℝ) * ‖x-z‖^2/2 = s := WithTop.coe_inj.mp hzs
  change ((n * ‖x-(a • y + b • z)‖^2/2 : ℝ) : WithTop ℝ) ≤ _
  rw [WithTop.coe_le_coe]
  have h := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)
  nlinarith

/-- The shifted quadratic conjugate. The proof uses approximate norming vectors,
via the accepted norm-square supremum lemma, and needs no norm attainment. -/
lemma kernel_conjugate (n : ℕ) (hn : 1 ≤ n) (x : X) (g : X →L[ℝ] ℝ) :
    P1.FenchelRockafellar.conjugate (kernel n x) g =
      ((g x + ‖g‖^2/(2*n) : ℝ) : EReal) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  let C := P1.FenchelRockafellar.conjugate (kernel n x) g
  have hterm (y : X) : ((g y - n * ‖x-y‖^2/2 : ℝ) : EReal) ≤ C := by
    exact le_iSup_of_le y (by rw [EReal.coe_sub]; rfl)
  have hup : C ≤ ((g x + ‖g‖^2/(2*n) : ℝ) : EReal) := by
    apply iSup_le
    intro y
    change (g y : EReal) - ((n * ‖x-y‖^2/2 : ℝ) : EReal) ≤ _
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h := quadratic_lower_bound (n : ℝ) hn' g y x
    rw [norm_sub_rev y x] at h
    linarith
  have hbot : C ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hterm x)
  have htop : C ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  have hreal : (C.toReal : EReal) = C := EReal.coe_toReal htop hbot
  have hterms : ∀ z : X, g z - ‖z‖^2/2 ≤ (n : ℝ) * (C.toReal - g x) := by
    intro z
    have h := hterm (x + (n : ℝ)⁻¹ • z)
    rw [← hreal, EReal.coe_le_coe_iff] at h
    have heq : x - (x + (n : ℝ)⁻¹ • z) = -((n : ℝ)⁻¹ • z) := by abel
    rw [map_add, map_smul, smul_eq_mul, heq, norm_neg,
      norm_smul_of_nonneg (inv_nonneg.mpr hn'.le)] at h
    have hmul := mul_le_mul_of_nonneg_left h hn'.le
    field_simp at hmul
    nlinarith
  have hnorm := Asplund.NormSquareConjugate.normSquare_le_of_forall_terms_le
    norm (reference_norm_equivalent (X := X)) g _ hterms
  rw [reference_dualNorm] at hnorm
  apply le_antisymm hup
  rw [← hreal, EReal.coe_le_coe_iff]
  have hdiv : ‖g‖^2/(2*(n:ℝ)) ≤ C.toReal - g x := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)).mpr
    nlinarith
  linarith

omit [NormedSpace ℝ X] in
lemma fr_primal_eq (φ : ExtendedFunction X) (n : ℕ) (x : X) :
    P1.FenchelRockafellar.primalValue (kernel n x) φ = primal φ n x := by
  unfold P1.FenchelRockafellar.primalValue primal
  apply iInf_congr
  intro y
  exact add_comm _ _

lemma fr_dual_eq (φ : ExtendedFunction X) (hp : Proper X φ)
    (n : ℕ) (hn : 1 ≤ n) (x : X) (f : X →L[ℝ] ℝ) :
    P1.FenchelRockafellar.dualValue (kernel n x) φ (-f) = objective φ n x f := by
  unfold P1.FenchelRockafellar.dualValue
  rw [kernel_conjugate n hn x (-f)]
  simp only [neg_neg, neg_apply, norm_neg]
  change -((-(f x) + ‖f‖^2/(2*n) : ℝ) : EReal) -
    P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = _
  by_cases ht : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = ⊤
  · simp [objective, ht]
  have hb := P1.C06Conjugates.convexConjugate_ne_bot X φ hp f
  let r := (P1.C06Conjugates.Spec.ConvexConjugateValue X φ f).toReal
  have hr : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal) :=
    (EReal.coe_toReal ht hb).symm
  simp only [objective, hr, ← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring

/-- Exact duality with attainment, before the uniqueness argument. -/
lemma primal_eq_max (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (x : X) :
    (∀ f, objective φ n x f ≤ primal φ n x) ∧
      ∃ f, objective φ n x f = primal φ n x := by
  have hv := primal_finite φ hp hc hl n hn x
  obtain ⟨y, r, hr⟩ := (P1.ExtendedConvexFunctions.proper_iff_finite_value X φ).mp hp
  have hfr : P1.FenchelRockafellar.primalValue (kernel n x) φ =
      (envelope φ n x : EReal) := by rw [fr_primal_eq, hv]
  obtain ⟨g, hg⟩ := P1.FenchelRockafellar.exists_dual_eq_of_primal_eq
    (kernel n x) φ (kernel_convex n x) hc y (by simp [kernel])
    (by simp [hr]) (kernel_continuous n x).continuousAt (envelope φ n x) hfr
  constructor
  · intro f
    rw [← fr_dual_eq φ hp n hn x f, ← fr_primal_eq]
    exact (le_iSup (fun g => P1.FenchelRockafellar.dualValue (kernel n x) φ g) (-f)).trans
      (P1.FenchelRockafellar.weak_duality _ _)
  · refine ⟨-g, ?_⟩
    have h := fr_dual_eq φ hp n hn x (-g)
    simpa only [neg_neg, hg, hv] using h.symm

lemma conjugate_real_of_objective_eq (φ : ExtendedFunction X)
    (hp : Proper X φ) (n : ℕ) (x : X) (f : X →L[ℝ] ℝ) (a : ℝ)
    (ha : objective φ n x f = (a : EReal)) :
    ∃ r : ℝ, P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal) ∧
      f x - r - ‖f‖^2/(2*n) = a := by
  have ht : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f ≠ ⊤ := by
    intro ht
    simp [objective, ht] at ha
  have hb := P1.C06Conjugates.convexConjugate_ne_bot X φ hp f
  let r := (P1.C06Conjugates.Spec.ConvexConjugateValue X φ f).toReal
  have hr : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal) :=
    (EReal.coe_toReal ht hb).symm
  refine ⟨r, hr, ?_⟩
  simpa only [objective, hr, ← EReal.coe_sub, EReal.coe_eq_coe_iff] using ha

lemma finite_conjugate_bound (φ : ExtendedFunction X)
    (f : X →L[ℝ] ℝ) (r : ℝ)
    (hr : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal))
    (y : X) (s : ℝ) (hs : φ y = (s : WithTop ℝ)) : f y - s ≤ r := by
  have h : (f y : EReal) - val (φ y) ≤
      P1.C06Conjugates.Spec.ConvexConjugateValue X φ f :=
    le_iSup (fun y => (f y : EReal) - val (φ y)) y
  rw [hr, hs] at h
  exact EReal.coe_le_coe_iff.mp (by simpa only [show val (s : WithTop ℝ) = (s : EReal) from rfl,
    ← EReal.coe_sub] using h)

/-- Convexity follows from the attained dual affine minorants. -/
lemma envelope_convex (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) : ConvexOn ℝ univ (envelope φ n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨f, hf⟩ := (primal_eq_max φ hp hc hl n hn (a • x + b • y)).2
  rw [primal_finite φ hp hc hl n hn] at hf
  obtain ⟨r, hr, heq⟩ := conjugate_real_of_objective_eq φ hp n _ f _ hf
  have hx := (primal_eq_max φ hp hc hl n hn x).1 f
  have hy := (primal_eq_max φ hp hc hl n hn y).1 f
  rw [primal_finite φ hp hc hl n hn] at hx hy
  simp only [objective, hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hx hy
  simp only [map_add, map_smul, smul_eq_mul] at heq ⊢
  calc
    envelope φ n (a • x + b • y) =
        a * f x + b * f y - (a+b) * (r + ‖f‖^2/(2*n)) := by rw [hab]; linarith
    _ = a * (f x-r-‖f‖^2/(2*n)) + b * (f y-r-‖f‖^2/(2*n)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem finite_convex : Spec.FiniteConvex := by
  intro X _ _ _ _ φ hp hc hl n hn
  exact ⟨primal_finite φ hp hc hl n hn, envelope_convex φ hp hc hl n hn⟩

/-- Finite conjugate values are convex at their midpoint. -/
lemma conjugate_midpoint (φ : ExtendedFunction X) (hp : Proper X φ)
    (f g : X →L[ℝ] ℝ) (r s : ℝ)
    (hr : P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal))
    (hs : P1.C06Conjugates.Spec.ConvexConjugateValue X φ g = (s : EReal)) :
    ∃ t : ℝ,
      P1.C06Conjugates.Spec.ConvexConjugateValue X φ ((1/2 : ℝ) • (f+g)) = (t : EReal) ∧
      2*t ≤ r+s := by
  let m := (1/2 : ℝ) • (f+g)
  have hu : P1.C06Conjugates.Spec.ConvexConjugateValue X φ m ≤ (((r+s)/2 : ℝ) : EReal) := by
    apply iSup_le
    intro y
    by_cases hy : φ y = ⊤
    · rw [hy]
      change (m y : EReal) - ⊤ ≤ _
      rw [EReal.sub_top]
      exact bot_le
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hy
    have hf := finite_conjugate_bound φ f r hr y v hv.symm
    have hg := finite_conjugate_bound φ g s hs y v hv.symm
    rw [← hv]
    change (m y : EReal) - (v : EReal) ≤ _
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    simp only [m, smul_apply, add_apply, smul_eq_mul]
    linarith
  have hb := P1.C06Conjugates.convexConjugate_ne_bot X φ hp m
  have ht := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  refine ⟨_, (EReal.coe_toReal ht hb).symm, ?_⟩
  rw [← EReal.coe_toReal ht hb, EReal.coe_le_coe_iff] at hu
  linarith

/-- The central estimate: optimality at two points controls the midpoint
convexity gap of the squared dual norm by the change in the primal point. -/
lemma maximizers_gap (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (x y : X) (f g : X →L[ℝ] ℝ)
    (hf : objective φ n x f = primal φ n x)
    (hg : objective φ n y g = primal φ n y) :
    ‖f‖^2 + ‖g‖^2 - 2 * ‖(1/2 : ℝ) • (f+g)‖^2 ≤
      (n : ℝ) * (f-g) (x-y) := by
  rw [primal_finite φ hp hc hl n hn] at hf hg
  obtain ⟨r, hr, hrf⟩ := conjugate_real_of_objective_eq φ hp n x f _ hf
  obtain ⟨s, hs, hsg⟩ := conjugate_real_of_objective_eq φ hp n y g _ hg
  obtain ⟨t, ht, hts⟩ := conjugate_midpoint φ hp f g r s hr hs
  have hx := (primal_eq_max φ hp hc hl n hn x).1 ((1/2 : ℝ) • (f+g))
  have hy := (primal_eq_max φ hp hc hl n hn y).1 ((1/2 : ℝ) • (f+g))
  rw [primal_finite φ hp hc hl n hn] at hx hy
  simp only [objective, ht, ← EReal.coe_sub, EReal.coe_le_coe_iff,
    smul_apply, add_apply, smul_eq_mul] at hx hy
  have hsum :
      (‖f‖^2/(2*n) + ‖g‖^2/(2*n) - 2*‖(1/2 : ℝ) • (f+g)‖^2/(2*n)) ≤
      (f-g) (x-y)/2 := by
    simp only [sub_apply, map_sub]
    linear_combination hx + hy - hrf - hsg + hts
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heq :
      (‖f‖^2/(2*n) + ‖g‖^2/(2*n) - 2*‖(1/2 : ℝ) • (f+g)‖^2/(2*n)) * (2*n) =
        ‖f‖^2 + ‖g‖^2 - 2*‖(1/2 : ℝ) • (f+g)‖^2 := by
    field_simp
  have h := mul_le_mul_of_nonneg_right hsum (by positivity : (0 : ℝ) ≤ 2*n)
  rw [heq] at h
  nlinarith

lemma norm_square_midpoint_strict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] (f g : E) (hne : f ≠ g) :
    0 < ‖f‖^2 + ‖g‖^2 - 2*‖(1/2 : ℝ) • (f+g)‖^2 := by
  have hnorm : ‖(1/2 : ℝ) • (f+g)‖ ≤ (‖f‖+‖g‖)/2 := by
    rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    linarith [norm_add_le f g]
  have hnon := norm_nonneg ((1/2 : ℝ) • (f+g))
  by_cases heq : ‖f‖ = ‖g‖
  · have hstrict := norm_combo_lt_of_ne (le_refl ‖f‖) (by rw [heq]) hne
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
    rw [← smul_add] at hstrict
    nlinarith [norm_nonneg f, norm_nonneg g]
  · have hsq := sq_pos_of_ne_zero (sub_ne_zero.mpr heq)
    nlinarith [sq_nonneg ((‖f‖+‖g‖)/2 - ‖(1/2 : ℝ) • (f+g)‖),
      mul_nonneg (sub_nonneg.mpr hnorm)
        (show 0 ≤ (‖f‖+‖g‖)/2 + ‖(1/2 : ℝ) • (f+g)‖ by positivity)]

lemma maximizer_unique [UniformConvexSpace (X →L[ℝ] ℝ)]
    (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (x : X) (f g : X →L[ℝ] ℝ)
    (hf : objective φ n x f = primal φ n x)
    (hg : objective φ n x g = primal φ n x) : f = g := by
  by_contra hne
  have h := maximizers_gap φ hp hc hl n hn x x f g hf hg
  simp only [sub_self, map_zero, mul_zero] at h
  exact (norm_square_midpoint_strict f g hne).not_ge h

theorem exact_dual : Spec.ExactDual := by
  intro X _ _ _ _ φ hp hc hl n hn x
  obtain ⟨hweak, f, hf⟩ := primal_eq_max φ hp hc hl n hn x
  refine ⟨le_antisymm ?_ (iSup_le hweak), f, hf, ?_⟩
  · rw [← hf]
    exact le_iSup _ f
  · intro g hg
    exact maximizer_unique φ hp hc hl n hn x g f hg hf

lemma quadratic_root_bound {t A B : ℝ} (_ht : 0 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : t^2 ≤ A*t+B) : t ≤ A+B+1 := by
  by_contra hn
  have hbig : A+B+1 < t := lt_of_not_ge hn
  have hone : 1 < t := by linarith
  have hprod := mul_pos (sub_pos.mpr hbig) (show 0 < t by linarith)
  have hBprod := mul_nonneg hB (show 0 ≤ t-1 by linarith)
  nlinarith

/-- Uniform coercivity of the dual objective as x ranges over a bounded set. -/
lemma maximizers_bounded (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (s : Set X) (hs : Bornology.IsBounded s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ∀ f : X →L[ℝ] ℝ,
      objective φ n x f = primal φ n x → ‖f‖ ≤ C := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : X)).mp hs
  let R := max R₀ 1
  have hR : 0 ≤ R := le_trans (by norm_num) (le_max_right R₀ 1)
  have hxs : ∀ x ∈ s, ‖x‖ ≤ R := fun x hx =>
    (mem_closedBall_zero_iff.mp (hR₀ hx)).trans (le_max_left _ _)
  obtain ⟨y₀, v, hv⟩ := (P1.ExtendedConvexFunctions.proper_iff_finite_value X φ).mp hp
  obtain ⟨f₀, hf₀⟩ := (primal_eq_max φ hp hc hl n hn 0).2
  rw [primal_finite φ hp hc hl n hn] at hf₀
  obtain ⟨r₀, hr₀, _⟩ := conjugate_real_of_objective_eq φ hp n 0 f₀ _ hf₀
  let A : ℝ := 2*n*(R+‖y₀‖)
  let B : ℝ := 2*n*(|v|+‖f₀‖*R+|r₀|+‖f₀‖^2/(2*n))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A+B+1, by positivity, ?_⟩
  intro x hx f hf
  rw [primal_finite φ hp hc hl n hn] at hf
  obtain ⟨r, hr, heq⟩ := conjugate_real_of_objective_eq φ hp n x f _ hf
  have hlow := (primal_eq_max φ hp hc hl n hn x).1 f₀
  rw [primal_finite φ hp hc hl n hn] at hlow
  simp only [objective, hr₀, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hlow
  have hfenchel := finite_conjugate_bound φ f r hr y₀ v hv
  have hnorm : ‖x-y₀‖ ≤ R+‖y₀‖ :=
    (norm_sub_le x y₀).trans (by linarith [hxs x hx])
  have hfbound : f x - f y₀ ≤ ‖f‖*(R+‖y₀‖) := by
    have ht := (le_abs_self (f (x-y₀))).trans (f.le_opNorm (x-y₀))
    rw [map_sub] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hf₀bound : - (‖f₀‖*R) ≤ f₀ x := by
    have ht := f₀.le_opNorm x
    rw [Real.norm_eq_abs, abs_le] at ht
    have hm := mul_le_mul_of_nonneg_left (hxs x hx) (norm_nonneg f₀)
    linarith [ht.1]
  have hq : ‖f‖^2/(2*n) ≤ ‖f‖*(R+‖y₀‖) +
      (|v|+‖f₀‖*R+|r₀|+‖f₀‖^2/(2*n)) := by
    linarith [le_abs_self v, le_abs_self r₀]
  have hn' : (0 : ℝ) < 2*n := by exact_mod_cast (show 0 < 2*n by omega)
  have hquad : ‖f‖^2 ≤ A*‖f‖+B := by
    have h := (div_le_iff₀ hn').mp hq
    dsimp [A, B]
    nlinarith
  exact quadratic_root_bound (norm_nonneg f) hA hB hquad

/-- The squared norm is uniformly convex on each bounded ball. This is
the quadratic case of the uniformly convex Young-function argument in
Bačák–Kohlenbach, J. Convex Anal. 25 (2018), Theorem 3.1 and Proposition 3.2. -/
lemma norm_square_midpoint_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [UniformConvexSpace E] (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ f g : E, ‖f‖ ≤ R → ‖g‖ ≤ R → ε ≤ ‖f-g‖ →
      η ≤ ‖f‖^2 + ‖g‖^2 - 2*‖(1/2 : ℝ) • (f+g)‖^2 := by
  obtain ⟨δ, hδ, hc⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hR)
  let d := δ*ε^2/(16*R)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd_eq : 16*R*d = δ*ε^2 := by dsimp [d]; field_simp
  let η := min (d^2/2) (δ*ε^2/8)
  have hη : 0 < η := by dsimp [η]; positivity
  have hordered : ∀ f g : E, ‖f‖ ≤ R → ‖g‖ ≤ ‖f‖ → ε ≤ ‖f-g‖ →
      η ≤ ‖f‖^2 + ‖g‖^2 - 2*‖(1/2 : ℝ) • (f+g)‖^2 := by
    intro f g hf hg hsep
    let r := ‖f‖
    let s := ‖g‖
    let u := ‖(1/2 : ℝ) • (f+g)‖
    have hr0 : 0 ≤ r := norm_nonneg f
    have hs0 : 0 ≤ s := norm_nonneg g
    have hu0 : 0 ≤ u := norm_nonneg _
    have hr : 0 < r := by
      have ht := hsep.trans (norm_sub_le f g)
      dsimp [r, s] at *
      linarith
    have hs : s ≤ r := hg
    have hf' : r ≤ R := hf
    have hεr : ε ≤ 2*r := by
      have ht := hsep.trans (norm_sub_le f g)
      dsimp [r, s] at *
      linarith
    have hunitf : ‖r⁻¹ • f‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
      change r⁻¹*r ≤ 1
      rw [inv_mul_cancel₀ hr.ne']
    have hunitg : ‖r⁻¹ • g‖ ≤ 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
      exact (inv_mul_le_one₀ hr).mpr hs
    have hunitsep : ε/R ≤ ‖r⁻¹ • f-r⁻¹ • g‖ := by
      rw [← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hr.le), ← div_eq_inv_mul]
      exact (div_le_div_of_nonneg_left hε.le hr hf').trans
        (div_le_div_of_nonneg_right hsep hr.le)
    have hsum := hc hunitf hunitg hunitsep
    rw [← smul_add, norm_smul_of_nonneg (inv_nonneg.mpr hr.le), ← div_eq_inv_mul,
      div_le_iff₀ hr] at hsum
    have hu : 2*u ≤ (2-δ)*r := by
      dsimp [u]
      rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      linarith
    have hum : u ≤ (r+s)/2 := by
      have ht := norm_add_le f g
      dsimp [u, r, s]
      rw [norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      linarith
    have hrad : (r-s)^2 ≤ 2*(r^2+s^2-2*u^2) := by
      have ht := mul_nonneg (sub_nonneg.mpr hum)
        (show 0 ≤ (r+s)/2+u by positivity)
      nlinarith
    have hdrop : δ*r^2 ≤ 2*r^2-2*u^2 := by
      have ht : (δ*r/2)*r ≤ (r-u)*(r+u) :=
        mul_le_mul (by linarith) (by linarith) hr0 (by nlinarith)
      nlinarith
    have hdiff : r^2-s^2 ≤ 2*R*(r-s) := by
      have ht := mul_le_mul_of_nonneg_left (show r+s ≤ 2*R by linarith)
        (show 0 ≤ r-s by linarith)
      nlinarith
    have hεsq : δ*ε^2 ≤ 4*δ*r^2 := by
      have ht : ε^2 ≤ 4*r^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht hδ.le]
    by_cases hlarge : d ≤ r-s
    · have hηd : η ≤ d^2/2 := min_le_left _ _
      change η ≤ r^2+s^2-2*u^2
      nlinarith [sq_nonneg (r-s-d)]
    · have hsmall : r-s < d := lt_of_not_ge hlarge
      have hηd : η ≤ δ*ε^2/8 := min_le_right _ _
      have ht := mul_lt_mul_of_pos_left hsmall hR
      change η ≤ r^2+s^2-2*u^2
      nlinarith
  refine ⟨η, hη, ?_⟩
  intro f g hf hg hsep
  rcases le_total ‖g‖ ‖f‖ with hle | hle
  · exact hordered f g hf hle hsep
  · have h := hordered g f hg hle (by simpa only [norm_sub_rev] using hsep)
    simpa only [add_comm] using h

/-- In fact the maximizing map is uniformly norm continuous on bounded sets. -/
lemma maximizer_uniformContinuousOn [UniformConvexSpace (X →L[ℝ] ℝ)]
    (φ : ExtendedFunction X)
    (hp : Proper X φ) (hc : ExtendedConvex X φ) (hl : LowerSemicontinuous X φ)
    (n : ℕ) (hn : 1 ≤ n) (S : X → (X →L[ℝ] ℝ))
    (hS : ∀ x, objective φ n x (S x) = primal φ n x)
    (s : Set X) (hs : Bornology.IsBounded s) : UniformContinuousOn S s := by
  obtain ⟨C, hC, hbound⟩ := maximizers_bounded φ hp hc hl n hn s hs
  let R := max C 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb : ∀ x ∈ s, ‖S x‖ ≤ R := fun x hx =>
    (hbound x hx (S x) (hS x)).trans (le_max_left _ _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hgap⟩ := norm_square_midpoint_gap (E := X →L[ℝ] ℝ) R ε hR hε
  refine ⟨η/(2*n*R), by positivity, ?_⟩
  intro x hx y hy hxy
  rw [dist_eq_norm] at hxy ⊢
  by_contra hnsep
  have hsep : ε ≤ ‖S x-S y‖ := le_of_not_gt hnsep
  have hlow := hgap (S x) (S y) (hb x hx) (hb y hy) hsep
  have hu := maximizers_gap φ hp hc hl n hn x y (S x) (S y) (hS x) (hS y)
  have heval : (S x-S y) (x-y) ≤ ‖S x-S y‖*‖x-y‖ :=
    (le_abs_self _).trans ((S x-S y).le_opNorm (x-y))
  have hdiff : ‖S x-S y‖ ≤ 2*R := (norm_sub_le _ _).trans (by linarith [hb x hx, hb y hy])
  have hup : (n : ℝ) * (S x-S y) (x-y) ≤ 2*n*R*‖x-y‖ := by
    have h := mul_le_mul_of_nonneg_left heval hn'.le
    have ht := mul_le_mul_of_nonneg_right hdiff (norm_nonneg (x-y))
    have ht' := mul_le_mul_of_nonneg_left ht hn'.le
    nlinarith
  have hlt := (lt_div_iff₀ (show (0 : ℝ) < 2*n*R by positivity)).mp hxy
  linarith

theorem maximizer_regularity : Spec.MaximizerRegularity := by
  intro X _ _ _ _ φ hp hc hl n hn
  choose S hS using fun x => (primal_eq_max φ hp hc hl n hn x).2
  refine ⟨S, ?_, ?_, ?_⟩
  · intro x f
    exact ⟨fun hf => maximizer_unique φ hp hc hl n hn x f (S x) hf (hS x),
      fun hf => hf ▸ hS x⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    exact (maximizer_uniformContinuousOn φ hp hc hl n hn S hS
      (Metric.closedBall x 1) Metric.isBounded_closedBall).continuousOn.continuousAt
        (Metric.closedBall_mem_nhds x zero_lt_one)
  · intro s hs
    obtain ⟨C, _, hb⟩ := maximizers_bounded φ hp hc hl n hn s hs
    apply (Metric.isBounded_iff_subset_closedBall (0 : X →L[ℝ] ℝ)).mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hb x hx (S x) (hS x))

end ExpandedFA.BanachConvex.Moreau
