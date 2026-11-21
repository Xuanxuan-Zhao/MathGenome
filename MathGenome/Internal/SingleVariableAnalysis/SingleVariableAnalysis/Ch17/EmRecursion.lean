import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EmRecursion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.BernoulliIdentities
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Monotone
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
The integral recursion in K03.17.euler_maclaurin. On each unit cell we use
Newton–Leibniz on the product of a normalized Bernoulli polynomial and a
continuous derivative extension. Finite endpoint changes identify its integral
with the periodic integrand. Integer induction glues the cells; the endpoint
identity for Bernoulli polynomials cancels internal boundaries. Factorial
linearity then recovers the source's unnormalized proper integrals.

The auxiliary integral-law record is fully constructed for the upstream real
and complex Darboux integrals. All final results use these concrete instances.
External convention comparison: NIST DLMF §2.10(i), equation 2.10.1;
the actual proof uses the supplied Bernoulli and Darboux/FTC declarations.
-/
noncomputable section
namespace SingleVariableAnalysis.EulerMaclaurin
open Set
open scoped BigOperators
open Riemann
open Specs.SingleVariableAnalysis.Ch17.EmRecursion

/-- Finite reassignment of values preserves a norm bound. -/
theorem bound_of_finite_changes {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {a b : ℝ} (s : Finset ℝ)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ M)
    (he : ∀ x ∈ Icc a b, x ∉ s → f x = g x) :
    ∃ M : ℝ, ∀ x ∈ Icc a b, ‖g x‖ ≤ M := by
  classical
  obtain ⟨M, hM⟩ := hf
  refine ⟨max M 0 + ∑ x ∈ s, ‖g x‖, fun x hx => ?_⟩
  by_cases hs : x ∈ s
  · exact (Finset.single_le_sum (fun y _ => norm_nonneg (g y)) hs).trans
      (le_add_of_nonneg_left (le_max_right _ _))
  · rw [← he x hx hs]
    exact (hM x hx).trans ((le_max_left _ _).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun y _ => norm_nonneg (g y)))))

/-- A proof device containing only ordinary integral laws. Both instances below
are constructed from the upstream proper Darboux integral, never assumed. -/
structure IntegralCalculus (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Intg : (ℝ → E) → ℝ → ℝ → Prop
  val : (f : ℝ → E) → {a b : ℝ} → Intg f a b → E
  cont : ∀ {f : ℝ → E} {a b : ℝ}, a ≤ b → ContinuousOn f (Icc a b) → Intg f a b
  change : ∀ {f g : ℝ → E} {a b : ℝ} (s : Finset ℝ),
    (∀ x ∈ Icc a b, x ∉ s → f x = g x) → ∀ hf : Intg f a b,
    ∃ hg : Intg g a b, val g hg = val f hf
  add : ∀ {f g : ℝ → E} {a b : ℝ}, ∀ hf : Intg f a b, ∀ hg : Intg g a b,
    ∃ h : Intg (fun x => f x + g x) a b,
      val _ h = val f hf + val g hg
  smul : ∀ {f : ℝ → E} {a b : ℝ} (c : ℝ), ∀ hf : Intg f a b,
    ∃ h : Intg (fun x => c • f x) a b, val _ h = c • val f hf
  join : ∀ {f : ℝ → E} {a c b : ℝ}, ∀ hl : Intg f a c, ∀ hr : Intg f c b,
    ∃ h : Intg f a b, val f h = val f hl + val f hr
  ftc : ∀ (f df : ℝ → E) {a b : ℝ}, a ≤ b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt f (df x) x) →
    ∀ h : Intg df a b, val df h = f b - f a

/-- Real instance: all fields use the bounded proper Darboux predicate. -/
def realCalculus : IntegralCalculus ℝ where
  Intg := RealIntegrable
  val := @realIntegral
  cont := fun h hc => real_continuous_integrable _ h
    (fun x hx => (relativeContinuousAt_within_iff _ _ _).mpr (hc x hx))
  change := by
    intro f g a b s he hf
    have hb := bound_of_finite_changes s
      (by simpa only [Real.norm_eq_abs] using hf.bounded.abs_bound) he
    apply real_finite_changes f g hf.bounded
      (boundedOnInterval_of_abs (by simpa only [Real.norm_eq_abs] using hb.choose_spec)) _ hf
    exact s.finite_toSet.subset (fun x hx => by
      by_contra h; exact hx.2 (he x hx.1 h))
  add := real_add_value
  smul := fun c hf => real_mul_value hf c
  join := by
    intro f a c b hl hr
    have h := hl.join hr
    exact ⟨h, (real_split f hl.ordered hr.ordered h.bounded).2 h hl hr⟩
  ftc := fun f df _ _ hab hc hd hi => real_ftc_second f df _ _ hab hc hd hi

/-- Complex instance: the same proper integral, defined by real components. -/
def complexCalculus : IntegralCalculus ℂ where
  Intg := ComplexIntegrable
  val := @complexIntegral
  cont := fun h hc => complex_continuous_integrable _ h
    (fun x hx => (relativeContinuousAt_within_iff _ _ _).mpr (hc x hx))
  change := by
    intro f g a b s he hf
    apply complex_finite_changes f g hf.norm_bound
      (bound_of_finite_changes s hf.norm_bound he) _ hf
    exact s.finite_toSet.subset (fun x hx => by
      by_contra h; exact hx.2 (he x hx.1 h))
  add := complex_add_value
  smul := by
    intro f a b c hf
    change ∃ h : ComplexIntegrable (fun x => c • f x) a b,
      complexIntegral _ h = c • complexIntegral f hf
    have heq : (fun x => c • f x) = (fun x => (c : ℂ) * f x) := by
      funext x; exact RCLike.real_smul_eq_coe_mul c (f x)
    rw [heq, RCLike.real_smul_eq_coe_mul]
    exact complex_mul_value hf (c : ℂ)
  join := by
    intro f a c b hl hr
    have h : ComplexIntegrable f a b := ⟨RealIntegrable.join hl.1 hr.1, RealIntegrable.join hl.2 hr.2⟩
    exact ⟨h, (complex_split f (RealIntegrable.ordered hl.1) (RealIntegrable.ordered hr.1) h.norm_bound).2 h hl hr⟩
  ftc := fun f df _ _ hab hc hd hi => complex_ftc_second f df _ _ hab hc hd hi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a cell, changes at its two endpoints have zero integral. -/
theorem IntegralCalculus.congr_open (C : IntegralCalculus E)
    {f g : ℝ → E} {a b : ℝ} (he : EqOn f g (Ioo a b))
    (hf : C.Intg f a b) : ∃ hg : C.Intg g a b, C.val g hg = C.val f hf := by
  classical
  apply C.change {a, b} _ hf
  intro x hx hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  exact he ⟨lt_of_le_of_ne hx.1 (Ne.symm hs.1), lt_of_le_of_ne hx.2 hs.2⟩

/-- The periodic polynomial agrees with the translated polynomial inside
an integer cell. At its upper endpoint these expressions can differ. -/
theorem fract_on_cell (k : ℤ) {x : ℝ} (hx : x ∈ Ioo (k : ℝ) ((k : ℝ) + 1)) :
    Int.fract x = x - k := by
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨hx.1.le, hx.2⟩]

/-- The normalized polynomial has derivative the preceding normalized one. -/
theorem weight_hasDerivAt (j : ℕ) (x : ℝ) :
    HasDerivAt (weight (j + 1)) (weight j x) x := by
  have h := (bernoulli_hasDerivAt j x).div_const (((j + 1).factorial : ℕ) : ℝ)
  convert h using 1
  · rfl
  · dsimp [weight]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

/-- Shifted normalized polynomial on a single closed cell. -/
theorem weight_shift_hasDerivAt (j : ℕ) (k x : ℝ) :
    HasDerivAt (fun t => weight (j + 1) (t - k)) (weight j (x - k)) x := by
  exact (weight_hasDerivAt j (x - k)).comp_sub_const x k

theorem weight_continuous (j : ℕ) : Continuous (weight j) :=
  (bernoulliPolynomial j).continuous.div_const _

theorem weight_one (x : ℝ) : weight 1 x = x - 1 / 2 := by
  dsimp [weight]
  rw [bernoulli_one]
  simp

theorem weight_endpoints (j : ℕ) (hj : 1 ≤ j) : weight (j + 1) 1 = weight (j + 1) 0 := by
  dsimp [weight]
  rw [bernoulli_endpoints (j + 1) (by omega)]


@[simp] theorem weight_zero (x : ℝ) : weight 0 x = 1 := by
  simp [weight, bernoulli_zero]

/-- Proper integrability on a cell follows from a continuous polynomial
extension; no continuity of the assigned node values is required. -/
theorem cell_integrable (C : IntegralCalculus E) (j : ℕ) (k : ℤ) (p : ℝ → E)
    (hp : ContinuousOn p (Icc (k : ℝ) ((k : ℝ) + 1))) :
    C.Intg (fun x => weight j (Int.fract x) • p x) k ((k : ℝ) + 1) := by
  have h := C.cont (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
    (((weight_continuous j).comp (continuous_id.sub (continuous_const (y := (k : ℝ))))).continuousOn.smul hp)
  exact (C.congr_open (fun x hx => by rw [fract_on_cell k hx]; rfl) h).choose

/-- Integration by parts on a unit cell, before simplifying its endpoints. -/
theorem cell_parts (C : IntegralCalculus E) (j : ℕ) (k : ℤ) (p dp : ℝ → E)
    (hp : ContinuousOn p (Icc (k : ℝ) ((k : ℝ) + 1)))
    (hdp : ContinuousOn dp (Icc (k : ℝ) ((k : ℝ) + 1)))
    (hd : ∀ x ∈ Ioo (k : ℝ) ((k : ℝ) + 1), HasDerivAt p (dp x) x) :
    ∃ hi : C.Intg (fun x => weight j (Int.fract x) • p x) k ((k : ℝ) + 1),
    ∃ hn : C.Intg (fun x => weight (j + 1) (Int.fract x) • dp x) k ((k : ℝ) + 1),
      C.val _ hi + C.val _ hn =
        weight (j + 1) 1 • p ((k : ℝ) + 1) - weight (j + 1) 0 • p k := by
  have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  let v : ℝ → E := fun x => weight j (x - k) • p x
  let w : ℝ → E := fun x => weight (j + 1) (x - k) • dp x
  have hv : C.Intg v k ((k : ℝ) + 1) := C.cont hle
    (((weight_continuous j).comp (continuous_id.sub (continuous_const (y := (k : ℝ))))).continuousOn.smul hp)
  have hw : C.Intg w k ((k : ℝ) + 1) := C.cont hle
    (((weight_continuous (j + 1)).comp (continuous_id.sub (continuous_const (y := (k : ℝ))))).continuousOn.smul hdp)
  obtain ⟨hs, hsum⟩ := C.add hv hw
  have hft := C.ftc (fun x => weight (j + 1) (x - k) • p x)
    (fun x => v x + w x) hle
    (((weight_continuous (j + 1)).comp (continuous_id.sub (continuous_const (y := (k : ℝ))))).continuousOn.smul hp)
    (fun x hx => by
      convert (weight_shift_hasDerivAt j k x).smul (hd x hx) using 1
      dsimp [v, w]; abel) hs
  obtain ⟨hi, hei⟩ := C.congr_open
    (f := v) (g := fun x => weight j (Int.fract x) • p x)
    (fun x hx => by dsimp [v]; rw [fract_on_cell k hx]) hv
  obtain ⟨hn, hen⟩ := C.congr_open
    (f := w) (g := fun x => weight (j + 1) (Int.fract x) • dp x)
    (fun x hx => by dsimp [w]; rw [fract_on_cell k hx]) hw
  refine ⟨hi, hn, ?_⟩
  rw [hei, hen, ← hsum, hft]
  simp only [add_sub_cancel_left, sub_self]

/-- The exceptional first Bernoulli polynomial gives the trapezoid error. -/
theorem unit_cell (C : IntegralCalculus E) : unitCell C.Intg (@C.val) := by
  intro k f df hf hdf hd
  obtain ⟨hi, hn, he⟩ := cell_parts C 0 k f df hf hdf hd
  simp only [weight_zero, one_smul, zero_add] at hi he
  refine ⟨hi, hn, ?_⟩
  rw [weight_one, weight_one] at he
  have he' : C.val f hi + C.val _ hn =
      (1 / 2 : ℝ) • (f k + f ((k : ℝ) + 1)) := by
    rw [he]
    module
  exact (eq_sub_of_add_eq' he').symm

/-- An interval of integer endpoints is built from its finitely many unit cells. -/
theorem glue_cells (C : IntegralCalculus E) (f : ℝ → E) (a b : ℤ) (hab : a < b)
    (hc : ∀ k : ℤ, a ≤ k → k < b → C.Intg f k ((k : ℝ) + 1)) : C.Intg f a b := by
  have haux : ∀ t : ℤ, a + 1 ≤ t →
      (∀ k : ℤ, a ≤ k → k < t → C.Intg f k ((k : ℝ) + 1)) → C.Intg f a t := by
    intro t ht
    induction t, ht using Int.leInduction with
    | base =>
      intro hc
      simpa only [Int.cast_add, Int.cast_one] using hc a le_rfl (by omega)
    | succ t ht ih =>
      intro hc
      have hl := ih (fun k hka hkt => hc k hka (by omega))
      have hr := hc t (by omega) (by omega)
      simpa only [Int.cast_add, Int.cast_one] using (C.join hl hr).choose
  exact haux b (by omega) hc

/-- Additivity plus finite induction glues a pair of cell integrals. -/
theorem glue_pair (C : IntegralCalculus E) (f g : ℝ → E) (a b : ℤ) (hab : a < b)
    (W : ℤ → E)
    (hc : ∀ k : ℤ, a ≤ k → k < b →
      ∃ hf : C.Intg f k ((k : ℝ) + 1), ∃ hg : C.Intg g k ((k : ℝ) + 1),
        C.val f hf + C.val g hg = W k) :
    ∃ hf : C.Intg f a b, ∃ hg : C.Intg g a b,
      C.val f hf + C.val g hg = ∑ k ∈ Finset.Ico a b, W k := by
  classical
  have haux : ∀ t : ℤ, a + 1 ≤ t →
      (∀ k : ℤ, a ≤ k → k < t →
        ∃ hf : C.Intg f k ((k : ℝ) + 1), ∃ hg : C.Intg g k ((k : ℝ) + 1),
          C.val f hf + C.val g hg = W k) →
      ∃ hf : C.Intg f a t, ∃ hg : C.Intg g a t,
        C.val f hf + C.val g hg = ∑ k ∈ Finset.Ico a t, W k := by
    intro t ht
    induction t, ht using Int.leInduction with
    | base =>
      intro hc
      obtain ⟨hf, hg, he⟩ := hc a le_rfl (by omega)
      refine ⟨by simpa only [Int.cast_add, Int.cast_one] using hf,
        by simpa only [Int.cast_add, Int.cast_one] using hg, ?_⟩
      have hs : Finset.Ico a (a + 1) = {a} := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      simpa only [Int.cast_add, Int.cast_one, hs, Finset.sum_singleton] using he
    | succ t ht ih =>
      intro hc
      obtain ⟨hfl, hgl, hel⟩ := ih (fun k hka hkt => hc k hka (by omega))
      obtain ⟨hfr, hgr, her⟩ := hc t (by omega) (by omega)
      obtain ⟨hf, hef⟩ := C.join hfl hfr
      obtain ⟨hg, heg⟩ := C.join hgl hgr
      refine ⟨by simpa only [Int.cast_add, Int.cast_one] using hf,
        by simpa only [Int.cast_add, Int.cast_one] using hg, ?_⟩
      simp only [Int.cast_add, Int.cast_one]
      rw [hef, heg, ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega : a ≤ t) W]
      rw [← hel, ← her]
      abel
  exact haux b (by omega) hc

omit [NormedSpace ℝ E] in
/-- Finite unit-cell boundary cancellation. -/
theorem sum_differences (p : ℤ → E) (a b : ℤ) (hab : a < b) :
    (∑ k ∈ Finset.Ico a b, (p (k + 1) - p k)) = p b - p a := by
  classical
  have haux : ∀ t : ℤ, a + 1 ≤ t →
      (∑ k ∈ Finset.Ico a t, (p (k + 1) - p k)) = p t - p a := by
    intro t ht
    induction t, ht using Int.leInduction with
    | base =>
      have hs : Finset.Ico a (a + 1) = {a} := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      simp only [hs, Finset.sum_singleton]
    | succ t ht ih =>
      rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega : a ≤ t), ih]
      abel
  exact haux b (by omega)

/-- Adding the cell endpoint halves gives precisely the source trapezoid sum. -/
theorem sum_halves (f : ℝ → E) (a b : ℤ) (hab : a < b) :
    (∑ k ∈ Finset.Ico a b, (1 / 2 : ℝ) • (f k + f ((k : ℝ) + 1))) =
      trapezoid f a b := by
  classical
  have haux : ∀ t : ℤ, a + 1 ≤ t →
      (∑ k ∈ Finset.Ico a t, (1 / 2 : ℝ) • (f k + f ((k : ℝ) + 1))) =
        trapezoid f a t := by
    intro t ht
    induction t, ht using Int.leInduction with
    | base =>
      have hs : Finset.Ico a (a + 1) = {a} := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      have ho : Finset.Ioo a (a + 1) = ∅ := by
        ext k; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
      simp only [hs, Finset.sum_singleton, trapezoid, ho, Finset.sum_empty,
        add_zero, Int.cast_add, Int.cast_one, smul_add]
    | succ t ht ih =>
      have ho : Finset.Ioo a (t + 1) = insert t (Finset.Ioo a t) := by
        ext k; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
      rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega : a ≤ t), ih]
      simp only [trapezoid, ho, Finset.sum_insert (by simp : t ∉ Finset.Ioo a t),
        Int.cast_add, Int.cast_one]
      module
  exact haux b (by omega)

/-- Each closed integer cell is contained in the full interval. -/
theorem cell_subset {a b k : ℤ} (ha : a ≤ k) (hb : k < b) :
    Icc (k : ℝ) ((k : ℝ) + 1) ⊆ Icc (a : ℝ) (b : ℝ) := by
  have hka : (a : ℝ) ≤ k := by exact_mod_cast ha
  have hkb : (k : ℝ) + 1 ≤ b := by exact_mod_cast (show k + 1 ≤ b by omega)
  exact fun x hx => ⟨hka.trans hx.1, hx.2.trans hkb⟩

/-- Interior cell points are interior to the full interval, so the within
relations of the closed derivative family give ordinary real derivatives. -/
theorem family_cell_derivative {a b k : ℤ} {n : ℕ} {f : ℝ → E} {D : ℕ → ℝ → E}
    (hD : Specs.SingleVariableAnalysis.Ch04.Higher.closedDerivativeFamilyValue n f a b D)
    (ha : a ≤ k) (hb : k < b) {j : ℕ} (hj : j < n) :
    ∀ x ∈ Ioo (k : ℝ) ((k : ℝ) + 1), HasDerivAt (D j) (D (j + 1) x) x := by
  intro x hx
  have hka : (a : ℝ) ≤ k := by exact_mod_cast ha
  have hkb : (k : ℝ) + 1 ≤ b := by exact_mod_cast (show k + 1 ≤ b by omega)
  exact (hD.2.2 j hj x ⟨hka.trans hx.1.le, hx.2.le.trans hkb⟩).hasDerivAt
    (Icc_mem_nhds (hka.trans_lt hx.1) (hx.2.trans_le hkb))

/-- All periodic integrands are properly integrable, including the highest
continuous derivative and the discontinuous first Bernoulli factor. -/
theorem periodic_integrable (C : IntegralCalculus E) (p : ℝ → E) (j : ℕ)
    (a b : ℤ) (hab : a < b) (hp : ContinuousOn p (Icc (a : ℝ) (b : ℝ))) :
    C.Intg (fun x => weight j (Int.fract x) • p x) a b :=
  glue_cells C _ a b hab (fun k ha hb =>
    cell_integrable C j k p (hp.mono (cell_subset ha hb)))

/-- The error identity and every step of the Euler–Maclaurin recursion. -/
theorem normalized_recursion_of_calculus (C : IntegralCalculus E) :
    normalizedRecursion C.Intg (@C.val) := by
  classical
  intro a b hab m hm f D hD
  have hcont (j : ℕ) (hj : j ≤ 2 * m) := hD.2.1 j hj
  have hT : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * m → C.Intg (integrand j D) a b := by
    intro j _ hj
    exact periodic_integrable C (D j) j a b hab (hcont j hj)
  obtain ⟨h0, h1, hbase⟩ := glue_pair C (D 0) (integrand 1 D) a b hab
    (fun k => (1 / 2 : ℝ) • (D 0 k + D 0 ((k : ℝ) + 1))) (by
      intro k ha hb
      obtain ⟨hi, hn, he⟩ := cell_parts C 0 k (D 0) (D 1)
        ((hcont 0 (by omega)).mono (cell_subset ha hb))
        ((hcont 1 (by omega)).mono (cell_subset ha hb))
        (family_cell_derivative hD ha hb (by omega))
      simp only [weight_zero, one_smul, zero_add] at hi he
      refine ⟨hi, hn, ?_⟩
      change C.val (D 0) hi + C.val (integrand 1 D) hn = _ at he
      rw [he, weight_one, weight_one]
      module)
  rw [sum_halves (D 0) a b hab] at hbase
  obtain ⟨hf, hvf⟩ := C.change (f := D 0) (g := f) ∅
    (fun x hx _ => hD.1 hx) h0
  have htrap : trapezoid (D 0) a b = trapezoid f a b := by
    unfold trapezoid
    have ha : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    rw [hD.1 ⟨le_rfl, ha⟩, hD.1 ⟨ha, le_rfl⟩]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    exact hD.1 ⟨by exact_mod_cast hk'.1.le, by exact_mod_cast hk'.2.le⟩
  rw [htrap, ← hvf] at hbase
  refine ⟨hf, hT, ?_, ?_⟩
  · exact (eq_sub_of_add_eq' hbase).symm
  · intro j hj hjm
    obtain ⟨hi, hn, he⟩ := glue_pair C (integrand j D) (integrand (j + 1) D) a b hab
      (fun k => weight (j + 1) 0 • (D j ((k : ℝ) + 1) - D j k)) (by
        intro k ha hb
        obtain ⟨hi, hn, he⟩ := cell_parts C j k (D j) (D (j + 1))
          ((hcont j hjm.le).mono (cell_subset ha hb))
          ((hcont (j + 1) (by omega)).mono (cell_subset ha hb))
          (family_cell_derivative hD ha hb hjm)
        refine ⟨hi, hn, ?_⟩
        change C.val (integrand j D) hi + C.val (integrand (j + 1) D) hn = _ at he
        rw [he, weight_endpoints j hj, smul_sub])
    have hsum : (∑ k ∈ Finset.Ico a b,
        weight (j + 1) 0 • (D j ((k : ℝ) + 1) - D j k)) =
        weight (j + 1) 0 • (D j b - D j a) := by
      have hs := congrArg (fun v : E => weight (j + 1) 0 • v)
        (sum_differences (fun k : ℤ => D j k) a b hab)
      simpa only [Finset.smul_sum, Int.cast_add, Int.cast_one] using hs
    rw [hsum] at he
    exact eq_sub_of_add_eq he

/-- Multiplying back by the nonzero factorial supplies the original
unnormalized proper integrand; linearity proves the value bridge. -/
theorem raw_integral (C : IntegralCalculus E) (j : ℕ) (D : ℕ → ℝ → E)
    {a b : ℝ} (hn : C.Intg (integrand j D) a b) :
    ∃ hb : C.Intg (rawIntegrand j D) a b,
      term (@C.val) j D hb = C.val (integrand j D) hn := by
  obtain ⟨hb, he⟩ := C.smul (j.factorial : ℝ) hn
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hfun : (fun x => (j.factorial : ℝ) • integrand j D x) = rawIntegrand j D := by
    funext x
    dsimp [integrand, rawIntegrand, weight]
    rw [smul_smul]
    congr 1
    field_simp
  have hb' : C.Intg (rawIntegrand j D) a b := hfun ▸ hb
  have he' : C.val (rawIntegrand j D) hb' =
      (j.factorial : ℝ) • C.val (integrand j D) hn := by
    simpa only [hfun] using he
  refine ⟨hb', ?_⟩
  change (1 / (j.factorial : ℝ)) • C.val (rawIntegrand j D) hb' = _
  rw [he', smul_smul, one_div_mul_cancel hj, one_smul]

/-- Source form: T_j = (1/j!) times the proper Bernoulli integral. -/
theorem recursion_of_calculus (C : IntegralCalculus E) : recursion C.Intg (@C.val) := by
  intro a b hab m hm f D hD
  obtain ⟨hf, hT, hfirst, hrec⟩ := normalized_recursion_of_calculus C a b hab m hm f D hD
  have hb (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ 2 * m) := raw_integral C j D (hT j hj hjm)
  let hB : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * m → C.Intg (rawIntegrand j D) a b :=
    fun j hj hjm => (hb j hj hjm).choose
  have hval (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ 2 * m) :
      term (@C.val) j D (hB j hj hjm) = C.val (integrand j D) (hT j hj hjm) :=
    (hb j hj hjm).choose_spec
  refine ⟨hf, hB, ?_, ?_⟩
  · rw [hval 1 (by omega) (by omega)]; exact hfirst
  · intro j hj hjm
    rw [hval j hj hjm.le, hval (j + 1) (by omega) (by omega)]
    exact hrec j hj hjm

/-- Node assignments are harmless without any additional bound hypothesis:
the assigned values form a finite set and hence supply their own bound. -/
theorem node_changes (C : IntegralCalculus E) : nodeChanges C.Intg (@C.val) := by
  classical
  intro a b _ f g he hf
  apply C.change ((Finset.Icc a b).image (fun k : ℤ => (k : ℝ))) _ hf
  intro x hx hs
  apply he x hx
  intro k hk h
  exact hs (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)

end SingleVariableAnalysis.EulerMaclaurin

namespace SingleVariableAnalysis
open EulerMaclaurin

theorem em_real_recursion : Specs.SingleVariableAnalysis.Ch17.EmRecursion.realRecursion :=
  recursion_of_calculus realCalculus

theorem em_complex_recursion : Specs.SingleVariableAnalysis.Ch17.EmRecursion.complexRecursion :=
  recursion_of_calculus complexCalculus

theorem em_real_unit_cell : Specs.SingleVariableAnalysis.Ch17.EmRecursion.realUnitCell :=
  unit_cell realCalculus

theorem em_complex_unit_cell : Specs.SingleVariableAnalysis.Ch17.EmRecursion.complexUnitCell :=
  unit_cell complexCalculus

theorem em_real_node_changes : Specs.SingleVariableAnalysis.Ch17.EmRecursion.realNodeChanges :=
  node_changes realCalculus

theorem em_complex_node_changes : Specs.SingleVariableAnalysis.Ch17.EmRecursion.complexNodeChanges :=
  node_changes complexCalculus

end SingleVariableAnalysis
