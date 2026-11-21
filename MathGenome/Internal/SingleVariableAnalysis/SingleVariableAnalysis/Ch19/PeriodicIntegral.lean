import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.FiniteChanges
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

noncomputable section
namespace SingleVariableAnalysis.Riemann
open Set

/-- Integral values are independent of proofs of equal endpoints. -/
theorem realIntegral_congr_endpoints {f : ℝ → ℝ} {a b c d : ℝ}
    (h : RealIntegrable f a b) (h' : RealIntegrable f c d)
    (ha : a = c) (hb : b = d) : realIntegral f h = realIntegral f h' := by
  subst c; subst d; rfl

theorem complexIntegral_congr_endpoints {f : ℝ → ℂ} {a b c d : ℝ}
    (h : ComplexIntegrable f a b) (h' : ComplexIntegrable f c d)
    (ha : a = c) (hb : b = d) : complexIntegral f h = complexIntegral f h' := by
  subst c; subst d; rfl

/-- Translation of a proper Darboux integral; no continuity of f is needed. -/
theorem real_integral_translate {f : ℝ → ℝ} {a b : ℝ} (c : ℝ)
    (hf : RealIntegrable f (a+c) (b+c)) :
    ∃ hg : RealIntegrable (fun t => f (t+c)) a b,
      realIntegral _ hg = realIntegral f hf := by
  have hab : a ≤ b := by linarith [hf.ordered]
  have hφ : C1OnInterval (fun t => t+c) (fun _ => 1) a b :=
    ⟨continuousOn_const, fun t _ => (hasDerivAt_id t |>.add_const c).hasDerivWithinAt⟩
  have hfo : OrientedRealIntegrable f (a+c) (b+c) := by
    simpa only [O.realIntegrableValue, min_eq_left hf.ordered, max_eq_right hf.ordered] using hf
  obtain ⟨hg, he⟩ := real_monotone_substitution (fun t => t+c) (fun _ => 1) f
    hab hφ (Or.inl (by intro x hx y hy hxy; dsimp; linarith)) hfo
  simp only [one_mul] at hg he
  exact ⟨hg, he.trans (oriented_real_agreement f hf.ordered hfo hf)⟩

/-- Gluing two adjacent proper intervals supplies boundedness on their union. -/
theorem real_integral_join {f : ℝ → ℝ} {a c b : ℝ}
    (hl : RealIntegrable f a c) (hr : RealIntegrable f c b) :
    ∃ h : RealIntegrable f a b,
      realIntegral f h = realIntegral f hl + realIntegral f hr := by
  obtain ⟨M, hM⟩ := hl.bounded.abs_bound
  obtain ⟨N, hN⟩ := hr.bounded.abs_bound
  have hb : BoundedOnInterval f a b := boundedOnInterval_of_abs (M := max M N) (by
    intro x hx
    rcases le_total x c with hxc | hcx
    · exact (hM x ⟨hx.1, hxc⟩).trans (le_max_left _ _)
    · exact (hN x ⟨hcx, hx.2⟩).trans (le_max_right _ _))
  have h := (real_split f hl.ordered hr.ordered hb).1.mpr ⟨hl, hr⟩
  exact ⟨h, (real_split f hl.ordered hr.ordered hb).2 h hl hr⟩

/-- Any period (including an integer multiple of a positive period) translates
an integrable interval without changing its value. -/
theorem real_integral_translate_period {f : ℝ → ℝ} {a b c : ℝ}
    (hp : Function.Periodic f c) (hf : RealIntegrable f a b) :
    ∃ hg : RealIntegrable f (a+c) (b+c),
      realIntegral f hg = realIntegral f hf := by
  have hh : RealIntegrable f ((a+c)+(-c)) ((b+c)+(-c)) := by simpa using hf
  obtain ⟨hg, he⟩ := real_integral_translate (-c) hh
  have heq : (fun t => f (t + -c)) = f := by
    funext t
    simpa only [sub_eq_add_neg] using hp.sub_eq t
  have H : ∃ hg : RealIntegrable (fun t => f (t + -c)) (a+c) (b+c),
      realIntegral _ hg = realIntegral f hf :=
        ⟨hg, he.trans (realIntegral_congr_endpoints hh hf (by ring) (by ring))⟩
  simpa only [heq] using H

/-- Split at the seam for an origin inside the reference period. -/
theorem real_integral_period_near {f : ℝ → ℝ} {T b r : ℝ}
    (_hT : 0 < T) (hp : Function.Periodic f T) (hf : RealIntegrable f b (b+T))
    (hr : r ∈ Icc b (b+T)) :
    ∃ hg : RealIntegrable f r (r+T), realIntegral f hg = realIntegral f hf := by
  have hhead := hf.subinterval le_rfl hr.1 hr.2
  have htail := hf.subinterval hr.1 hr.2 le_rfl
  obtain ⟨hshift, hshiftval⟩ := real_integral_translate_period hp hhead
  obtain ⟨hg, hval⟩ := real_integral_join htail hshift
  refine ⟨hg, ?_⟩
  have hsplit := (real_split f hr.1 hr.2 hf.bounded).2 hf hhead htail
  linarith

/-- Independence of the real origin for a positive-period Darboux integral. -/
theorem real_integral_period {f : ℝ → ℝ} {T b : ℝ}
    (hT : 0 < T) (hp : Function.Periodic f T) (hf : RealIntegrable f b (b+T))
    (a : ℝ) :
    ∃ hg : RealIntegrable f a (a+T), realIntegral f hg = realIntegral f hf := by
  let n : ℤ := ⌊(a-b)/T⌋
  let r := a - (n : ℝ)*T
  have hr : r ∈ Icc b (b+T) := by
    have h0 := Int.sub_floor_div_mul_nonneg (a-b) hT
    have h1 := Int.sub_floor_div_mul_lt (a-b) hT
    dsimp [r, n]
    constructor <;> linarith
  obtain ⟨hrf, hrv⟩ := real_integral_period_near hT hp hf hr
  have hn : Function.Periodic f ((n : ℝ)*T) := by
    simpa only [zsmul_eq_mul] using hp.zsmul n
  obtain ⟨hg, hgv⟩ := real_integral_translate_period hn hrf
  have ha : r + (n : ℝ)*T = a := by dsimp [r]; ring
  have hb : r + T + (n : ℝ)*T = a+T := by dsimp [r]; ring
  simp only [ha, hb] at hg hgv
  exact ⟨hg, hgv.trans hrv⟩

/-- Reflection reverses both the variable and the endpoint orientation. -/
theorem real_integral_reflect {f : ℝ → ℝ} {a b : ℝ} (c : ℝ)
    (hf : RealIntegrable f (c-b) (c-a)) :
    ∃ hg : RealIntegrable (fun t => f (c-t)) a b,
      realIntegral _ hg = realIntegral f hf := by
  have hab : a ≤ b := by linarith [hf.ordered]
  have hφ : C1OnInterval (fun t => c-t) (fun _ => -1) a b :=
    ⟨continuousOn_const, fun t _ => ((hasDerivAt_id t).const_sub c).hasDerivWithinAt⟩
  have hfo : OrientedRealIntegrable f (c-a) (c-b) := by
    simpa only [O.realIntegrableValue, min_eq_right hf.ordered,
      max_eq_left hf.ordered] using hf
  obtain ⟨hn, hv⟩ := real_monotone_substitution (fun t => c-t) (fun _ => -1) f
    hab hφ (Or.inr (fun _ _ _ _ h => sub_le_sub_left h c)) hfo
  simp only [neg_one_mul] at hn hv
  obtain ⟨hg, he⟩ := real_mul_value hn (-1)
  simp only [neg_one_mul, neg_neg] at hg he
  have hrev : OrientedRealIntegrable f (c-b) (c-a) := by
    simpa only [O.realIntegrableValue, min_eq_left hf.ordered,
      max_eq_right hf.ordered] using hf
  have hs := oriented_real_symmetry f (c-a) (c-b) hfo hrev
  have ha := oriented_real_agreement f hf.ordered hrev hf
  exact ⟨hg, by linarith⟩

/-- Complex translation follows componentwise from the real Darboux theorem. -/
theorem complex_integral_translate {f : ℝ → ℂ} {a b : ℝ} (c : ℝ)
    (hf : ComplexIntegrable f (a+c) (b+c)) :
    ∃ hg : ComplexIntegrable (fun t => f (t+c)) a b,
      complexIntegral _ hg = complexIntegral f hf := by
  obtain ⟨hr, hrv⟩ := real_integral_translate c hf.1
  obtain ⟨hi, hiv⟩ := real_integral_translate c hf.2
  refine ⟨⟨hr, hi⟩, ?_⟩
  apply Complex.ext
  · rw [(complexIntegral_components (fun t => f (t+c)) ⟨hr, hi⟩).1,
      (complexIntegral_components f hf).1]
    exact hrv
  · rw [(complexIntegral_components (fun t => f (t+c)) ⟨hr, hi⟩).2,
      (complexIntegral_components f hf).2]
    exact hiv

theorem complex_integral_reflect {f : ℝ → ℂ} {a b : ℝ} (c : ℝ)
    (hf : ComplexIntegrable f (c-b) (c-a)) :
    ∃ hg : ComplexIntegrable (fun t => f (c-t)) a b,
      complexIntegral _ hg = complexIntegral f hf := by
  obtain ⟨hr, hrv⟩ := real_integral_reflect c hf.1
  obtain ⟨hi, hiv⟩ := real_integral_reflect c hf.2
  refine ⟨⟨hr, hi⟩, ?_⟩
  apply Complex.ext
  · rw [(complexIntegral_components (fun t => f (c-t)) ⟨hr, hi⟩).1,
      (complexIntegral_components f hf).1]
    exact hrv
  · rw [(complexIntegral_components (fun t => f (c-t)) ⟨hr, hi⟩).2,
      (complexIntegral_components f hf).2]
    exact hiv

theorem complex_integral_period {f : ℝ → ℂ} {T b : ℝ}
    (hT : 0 < T) (hp : Function.Periodic f T) (hf : ComplexIntegrable f b (b+T))
    (a : ℝ) :
    ∃ hg : ComplexIntegrable f a (a+T), complexIntegral f hg = complexIntegral f hf := by
  obtain ⟨hr, hrv⟩ := real_integral_period hT (hp.comp Complex.re) hf.1 a
  obtain ⟨hi, hiv⟩ := real_integral_period hT (hp.comp Complex.im) hf.2 a
  refine ⟨⟨hr, hi⟩, ?_⟩
  apply Complex.ext
  · rw [(complexIntegral_components f ⟨hr, hi⟩).1,
      (complexIntegral_components f hf).1]
    exact hrv
  · rw [(complexIntegral_components f ⟨hr, hi⟩).2,
      (complexIntegral_components f hf).2]
    exact hiv

/-- Arbitrary finite assignments on a bounded interval are automatically bounded. -/
theorem norm_bound_of_finite_changes {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {a b : ℝ}
    (hb : ∃ M : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ M)
    (hs : {x | x ∈ Icc a b ∧ f x ≠ g x}.Finite) :
    ∃ M : ℝ, ∀ x ∈ Icc a b, ‖g x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨N, hN⟩ := (hs.image (fun x => ‖g x‖)).bddAbove
  refine ⟨max M N, fun x hx => ?_⟩
  by_cases he : f x = g x
  · rw [← he]
    exact (hM x hx).trans (le_max_left _ _)
  · exact (hN (mem_image_of_mem _ ⟨hx, he⟩)).trans (le_max_right _ _)

/-- No extra boundedness premise is required for a finite modification. -/
theorem real_integral_finite_changes {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hs : {x | x ∈ Icc a b ∧ f x ≠ g x}.Finite) :
    ∃ hg : RealIntegrable g a b, realIntegral g hg = realIntegral f hf := by
  have hb : ∃ M : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hf.bounded.abs_bound
  obtain ⟨M, hM⟩ := norm_bound_of_finite_changes hb hs
  have hgb : BoundedOnInterval g a b := boundedOnInterval_of_abs (by
    simpa only [Real.norm_eq_abs] using hM)
  exact real_finite_changes f g hf.bounded hgb hs hf

theorem complex_integral_finite_changes {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hs : {x | x ∈ Icc a b ∧ f x ≠ g x}.Finite) :
    ∃ hg : ComplexIntegrable g a b, complexIntegral g hg = complexIntegral f hf :=
  complex_finite_changes f g hf.norm_bound (norm_bound_of_finite_changes hf.norm_bound hs) hs hf

/-- Integrability and value of a translated periodic integrand on any period. -/
theorem real_periodic_translate :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.realPeriodicTranslation := by
  intro f T b hT hp hf a c
  obtain ⟨hh, hv⟩ := real_integral_period hT hp hf (a+c)
  have hh' : RealIntegrable f (a+c) ((a+T)+c) := by
    simpa only [add_right_comm a T c] using hh
  obtain ⟨hg, he⟩ := real_integral_translate c hh'
  exact ⟨hg, he.trans ((realIntegral_congr_endpoints hh' hh rfl (by ring)).trans hv)⟩

theorem complex_periodic_translate :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.complexPeriodicTranslation := by
  intro f T b hT hp hf a c
  obtain ⟨hh, hv⟩ := complex_integral_period hT hp hf (a+c)
  have hh' : ComplexIntegrable f (a+c) ((a+T)+c) := by
    simpa only [add_right_comm a T c] using hh
  obtain ⟨hg, he⟩ := complex_integral_translate c hh'
  exact ⟨hg, he.trans ((complexIntegral_congr_endpoints hh' hh rfl (by ring)).trans hv)⟩

/-- The variable x-t used by convolution has the same one-period integral. -/
theorem real_periodic_reflect :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.realPeriodicReflection := by
  intro f T b hT hp hf a c
  obtain ⟨hh, hv⟩ := real_integral_period hT hp hf (c-(a+T))
  have hh' : RealIntegrable f (c-(a+T)) (c-a) := by
    convert hh using 1; ring
  obtain ⟨hg, he⟩ := real_integral_reflect c hh'
  exact ⟨hg, he.trans ((realIntegral_congr_endpoints hh' hh rfl (by ring)).trans hv)⟩

theorem complex_periodic_reflect :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.complexPeriodicReflection := by
  intro f T b hT hp hf a c
  obtain ⟨hh, hv⟩ := complex_integral_period hT hp hf (c-(a+T))
  have hh' : ComplexIntegrable f (c-(a+T)) (c-a) := by
    convert hh using 1; ring
  obtain ⟨hg, he⟩ := complex_integral_reflect c hh'
  exact ⟨hg, he.trans ((complexIntegral_congr_endpoints hh' hh rfl (by ring)).trans hv)⟩

/-- Finite seam changes on the target period preserve its integrability and value. -/
theorem real_period_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.realPeriodFiniteChanges := by
  intro f T b hT hp hf g a hs
  obtain ⟨ha, hav⟩ := real_integral_period hT hp hf a
  obtain ⟨hg, hgv⟩ := real_integral_finite_changes ha hs
  exact ⟨hg, hgv.trans hav⟩

theorem complex_period_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.complexPeriodFiniteChanges := by
  intro f T b hT hp hf g a hs
  obtain ⟨ha, hav⟩ := complex_integral_period hT hp hf a
  obtain ⟨hg, hgv⟩ := complex_integral_finite_changes ha hs
  exact ⟨hg, hgv.trans hav⟩

theorem real_periodic_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.realPeriodicFiniteChanges := by
  intro f g T b hT _hpf hpg hf hs a
  obtain ⟨hgb, hgbv⟩ := real_integral_finite_changes hf hs
  obtain ⟨hga, hgav⟩ := real_integral_period hT hpg hgb a
  exact ⟨hga, hgav.trans hgbv⟩

theorem complex_periodic_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral.complexPeriodicFiniteChanges := by
  intro f g T b hT _hpf hpg hf hs a
  obtain ⟨hgb, hgbv⟩ := complex_integral_finite_changes hf hs
  obtain ⟨hga, hgav⟩ := complex_integral_period hT hpg hgb a
  exact ⟨hga, hgav.trans hgbv⟩

end SingleVariableAnalysis.Riemann
