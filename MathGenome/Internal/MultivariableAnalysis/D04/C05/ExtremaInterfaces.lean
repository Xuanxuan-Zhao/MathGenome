import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces

noncomputable section
open Set Filter Topology
namespace D04
def LocalMinimumOn : Specs.D04.C05.ExtremaInterfaces.LocalMinimumOnType :=
  Specs.D04.C05.ExtremaInterfaces.LocalMinimumOnValue

def LocalMaximumOn : Specs.D04.C05.ExtremaInterfaces.LocalMaximumOnType :=
  Specs.D04.C05.ExtremaInterfaces.LocalMaximumOnValue

def StrictLocalMinimumOn : Specs.D04.C05.ExtremaInterfaces.StrictLocalMinimumOnType :=
  Specs.D04.C05.ExtremaInterfaces.StrictLocalMinimumOnValue

def StrictLocalMaximumOn : Specs.D04.C05.ExtremaInterfaces.StrictLocalMaximumOnType :=
  Specs.D04.C05.ExtremaInterfaces.StrictLocalMaximumOnValue

def GlobalMinimumOn : Specs.D04.C05.ExtremaInterfaces.GlobalMinimumOnType :=
  Specs.D04.C05.ExtremaInterfaces.GlobalMinimumOnValue

def GlobalMaximumOn : Specs.D04.C05.ExtremaInterfaces.GlobalMaximumOnType :=
  Specs.D04.C05.ExtremaInterfaces.GlobalMaximumOnValue

def StationaryPoint : Specs.D04.C05.ExtremaInterfaces.StationaryPointType :=
  Specs.D04.C05.ExtremaInterfaces.StationaryPointValue

def CriticalPoint : Specs.D04.C05.ExtremaInterfaces.CriticalPointType :=
  Specs.D04.C05.ExtremaInterfaces.CriticalPointValue

def SaddlePoint : Specs.D04.C05.ExtremaInterfaces.SaddlePointType :=
  Specs.D04.C05.ExtremaInterfaces.SaddlePointValue

private theorem eventuallyWithin_iff_ball {n : ℕ} (S : Set (E n)) (a : E n)
    (p : E n → Prop) :
    (∀ᶠ x in 𝓝[S] a, p x) ↔ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → p x := by
  change {x | p x} ∈ 𝓝[S] a ↔ _
  rw [Metric.mem_nhdsWithin_iff]
  constructor
  · rintro ⟨r, hr, hp⟩
    exact ⟨r, hr, fun x hx h => hp ⟨by simpa [dist_eq_norm] using h, hx⟩⟩
  · rintro ⟨r, hr, hp⟩
    exact ⟨r, hr, fun x hx => hp x hx.2 (by simpa [dist_eq_norm] using hx.1)⟩

theorem localMinimumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    LocalMinimumOn S f a ↔ a ∈ S ∧ IsLocalMinOn f S a := by
  change (a ∈ S ∧ _) ↔ a ∈ S ∧ (∀ᶠ x in 𝓝[S] a, f a ≤ f x)
  rw [eventuallyWithin_iff_ball]

theorem localMaximumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    LocalMaximumOn S f a ↔ a ∈ S ∧ IsLocalMaxOn f S a := by
  change (a ∈ S ∧ _) ↔ a ∈ S ∧ (∀ᶠ x in 𝓝[S] a, f x ≤ f a)
  rw [eventuallyWithin_iff_ball]

theorem globalMinimumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    GlobalMinimumOn S f a ↔ a ∈ S ∧ IsMinOn f S a := Iff.rfl

theorem globalMaximumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    GlobalMaximumOn S f a ↔ a ∈ S ∧ IsMaxOn f S a := Iff.rfl

theorem strictLocalMinimumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    StrictLocalMinimumOn S f a ↔ a ∈ S ∧ ∀ᶠ x in 𝓝[S \ {a}] a, f a < f x := by
  rw [eventuallyWithin_iff_ball]
  change (a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → x ≠ a → f a < f x) ↔ _
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, and_imp]
  constructor
  · rintro ⟨ha, r, hr, h⟩
    exact ⟨ha, r, hr, fun x hx hne hb => h x hx hb hne⟩
  · rintro ⟨ha, r, hr, h⟩
    exact ⟨ha, r, hr, fun x hx hb hne => h x hx hne hb⟩

theorem strictLocalMaximumOn_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    StrictLocalMaximumOn S f a ↔ a ∈ S ∧ ∀ᶠ x in 𝓝[S \ {a}] a, f x < f a := by
  rw [eventuallyWithin_iff_ball]
  change (a ∈ S ∧ ∃ r > 0, ∀ x ∈ S, ‖x - a‖ < r → x ≠ a → f x < f a) ↔ _
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, and_imp]
  constructor
  · rintro ⟨ha, r, hr, h⟩
    exact ⟨ha, r, hr, fun x hx hne hb => h x hx hb hne⟩
  · rintro ⟨ha, r, hr, h⟩
    exact ⟨ha, r, hr, fun x hx hb hne => h x hx hne hb⟩

theorem localMinimumOn_univ_iff {n : ℕ} (f : E n → ℝ) (a : E n) :
    LocalMinimumOn univ f a ↔ IsLocalMin f a := by
  rw [localMinimumOn_iff]
  simp [IsLocalMinOn, IsLocalMin]

theorem localMaximumOn_univ_iff {n : ℕ} (f : E n → ℝ) (a : E n) :
    LocalMaximumOn univ f a ↔ IsLocalMax f a := by
  rw [localMaximumOn_iff]
  simp [IsLocalMaxOn, IsLocalMax]

theorem stationaryPoint_iff {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n) :
    StationaryPoint U f a ↔ IsOpen U ∧ a ∈ U ∧ DifferentiableAt ℝ f a ∧
      totalDerivative f a = 0 := by
  change HasTotalDerivative U f 0 a ↔ _
  constructor
  · intro h
    have hd := (hasTotalDerivative_iff_hasFDerivAt U f 0 a h.1 h.2.1).mp h
    exact ⟨h.1, h.2.1, hd.differentiableAt, hd.fderiv⟩
  · rintro ⟨hU, ha, hd, hz⟩
    apply (hasTotalDerivative_iff_hasFDerivAt U f 0 a hU ha).mpr
    have h := hd.hasFDerivAt
    change fderiv ℝ f a = 0 at hz
    rwa [hz] at h

theorem criticalPoint_iff {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n) :
    CriticalPoint U f a ↔ StationaryPoint U f a := Iff.rfl

theorem saddlePoint_iff_neighborhoods {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    SaddlePoint S f a ↔ a ∈ S ∧ ∀ N ∈ 𝓝 a,
      (∃ x ∈ S, x ∈ N ∧ f a < f x) ∧ (∃ x ∈ S, x ∈ N ∧ f x < f a) := by
  change (a ∈ S ∧ ∀ r > 0, _) ↔ _
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun N hN => ?_⟩
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨⟨x, hx, hxb, hxf⟩, ⟨y, hy, hyb, hyf⟩⟩ := h r hr
    exact ⟨⟨x, hx, hsub (by simpa [dist_eq_norm] using hxb), hxf⟩,
      ⟨y, hy, hsub (by simpa [dist_eq_norm] using hyb), hyf⟩⟩
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun r hr => ?_⟩
    simpa only [Metric.mem_ball, dist_eq_norm] using h (Metric.ball a r) (Metric.ball_mem_nhds a hr)

theorem saddlePoint_iff_not_extrema {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    SaddlePoint S f a ↔ a ∈ S ∧ ¬ IsLocalMinOn f S a ∧ ¬ IsLocalMaxOn f S a := by
  change (a ∈ S ∧ ∀ r > 0, _) ↔ a ∈ S ∧
    ¬ (∀ᶠ x in 𝓝[S] a, f a ≤ f x) ∧ ¬ (∀ᶠ x in 𝓝[S] a, f x ≤ f a)
  rw [eventuallyWithin_iff_ball, eventuallyWithin_iff_ball]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_, ?_⟩
    · rintro ⟨r, hr, hm⟩
      obtain ⟨x, hx, hb, hf⟩ := (h r hr).2
      exact (not_lt_of_ge (hm x hx hb)) hf
    · rintro ⟨r, hr, hm⟩
      obtain ⟨x, hx, hb, hf⟩ := (h r hr).1
      exact (not_lt_of_ge (hm x hx hb)) hf
  · classical
    rintro ⟨ha, hmin, hmax⟩
    push Not at hmin hmax
    exact ⟨ha, fun r hr => ⟨hmax r hr, hmin r hr⟩⟩

theorem isolated_strict_extrema {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S)
    (ha : IsolatedPoint S a) : StrictLocalMinimumOn S f a ∧ StrictLocalMaximumOn S f a := by
  obtain ⟨r, hr, h⟩ := ha
  constructor
  · exact ⟨a.property, r, hr, fun x hx hb hne => (hne (h x hx hb)).elim⟩
  · exact ⟨a.property, r, hr, fun x hx hb hne => (hne (h x hx hb)).elim⟩

theorem strict_extrema_are_extrema {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    (StrictLocalMinimumOn S f a → LocalMinimumOn S f a) ∧
      (StrictLocalMaximumOn S f a → LocalMaximumOn S f a) := by
  classical
  constructor
  · rintro ⟨ha, r, hr, h⟩
    refine ⟨ha, r, hr, fun x hx hb => ?_⟩
    by_cases he : x = a
    · simp [he]
    · exact (h x hx hb he).le
  · rintro ⟨ha, r, hr, h⟩
    refine ⟨ha, r, hr, fun x hx hb => ?_⟩
    by_cases he : x = a
    · simp [he]
    · exact (h x hx hb he).le

theorem global_extrema_are_local {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : E n) :
    (GlobalMinimumOn S f a → LocalMinimumOn S f a) ∧
      (GlobalMaximumOn S f a → LocalMaximumOn S f a) := by
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, 1, zero_lt_one, fun x hx _ => h x hx⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, 1, zero_lt_one, fun x hx _ => h x hx⟩

theorem extrema_dimension_zero (S : Set (E 0)) (f : E 0 → ℝ) (a : E 0) (ha : a ∈ S) :
    StrictLocalMinimumOn S f a ∧ StrictLocalMaximumOn S f a := by
  apply isolated_strict_extrema S f ⟨a, ha⟩
  refine ⟨1, zero_lt_one, fun x _ _ => ?_⟩
  exact Subsingleton.elim x a

theorem extrema_congr {n : ℕ} (S : Set (E n)) (f g : E n → ℝ) (a : E n)
    (hfg : EqOn f g S) :
    (LocalMinimumOn S f a ↔ LocalMinimumOn S g a) ∧
    (LocalMaximumOn S f a ↔ LocalMaximumOn S g a) ∧
    (StrictLocalMinimumOn S f a ↔ StrictLocalMinimumOn S g a) ∧
    (StrictLocalMaximumOn S f a ↔ StrictLocalMaximumOn S g a) ∧
    (GlobalMinimumOn S f a ↔ GlobalMinimumOn S g a) ∧
    (GlobalMaximumOn S f a ↔ GlobalMaximumOn S g a) ∧
    (SaddlePoint S f a ↔ SaddlePoint S g a) := by
  by_cases ha : a ∈ S
  · have he : f a = g a := hfg ha
    have hall : ∀ x ∈ S, f x = g x := hfg
    simp only [LocalMinimumOn, LocalMaximumOn, StrictLocalMinimumOn, StrictLocalMaximumOn,
      GlobalMinimumOn, GlobalMaximumOn, SaddlePoint,
      Specs.D04.C05.ExtremaInterfaces.LocalMinimumOnValue,
      Specs.D04.C05.ExtremaInterfaces.LocalMaximumOnValue,
      Specs.D04.C05.ExtremaInterfaces.StrictLocalMinimumOnValue,
      Specs.D04.C05.ExtremaInterfaces.StrictLocalMaximumOnValue,
      Specs.D04.C05.ExtremaInterfaces.GlobalMinimumOnValue,
      Specs.D04.C05.ExtremaInterfaces.GlobalMaximumOnValue,
      Specs.D04.C05.ExtremaInterfaces.SaddlePointValue,
      Specs.D04.C05.ExtremaInterfaces.Model.LocalMinimumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.LocalMaximumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.StrictLocalMinimumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.StrictLocalMaximumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.GlobalMinimumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.GlobalMaximumOn,
      Specs.D04.C05.ExtremaInterfaces.Model.SaddlePoint, he]
    simp (config := { contextual := true }) only [hall, ha, true_and, iff_self]
    apply forall_congr'
    intro r
    apply forall_congr'
    intro _
    apply and_congr
    all_goals
      apply exists_congr
      intro x
      apply and_congr_right
      intro hx
      rw [hall x hx]
  · have hfalse (p : Prop) : (a ∈ S ∧ p) ↔ False := by simp [ha]
    change ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧ ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧
      ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧ ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧
      ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧ ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _)) ∧
      ((a ∈ S ∧ _) ↔ (a ∈ S ∧ _))
    simp only [hfalse, iff_self, and_self]

/-- Every function on the literal feasible-set subtype admits the ambient
representation used above. The congruence theorem makes the extension immaterial. -/
theorem feasible_function_extension {n : ℕ} (S : Set (E n)) (f : S → ℝ) :
    ∃ g : E n → ℝ, ∀ x : S, g x = f x := by
  classical
  refine ⟨fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0, ?_⟩
  intro x
  simp [x.property]

theorem local_extrema_subtype_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S) :
    (LocalMinimumOn S f a ↔ IsLocalMin (fun x : S => f x) a) ∧
    (LocalMaximumOn S f a ↔ IsLocalMax (fun x : S => f x) a) := by
  rw [localMinimumOn_iff, localMaximumOn_iff]
  simp only [a.property, true_and]
  constructor
  · change (∀ᶠ x in 𝓝[S] (a : E n), f a ≤ f x) ↔ _
    rw [← map_nhds_subtype_val a]
    rfl
  · change (∀ᶠ x in 𝓝[S] (a : E n), f x ≤ f a) ↔ _
    rw [← map_nhds_subtype_val a]
    rfl

theorem global_extrema_subtype_iff {n : ℕ} (S : Set (E n)) (f : E n → ℝ) (a : S) :
    (GlobalMinimumOn S f a ↔ IsMinOn (fun x : S => f x) univ a) ∧
    (GlobalMaximumOn S f a ↔ IsMaxOn (fun x : S => f x) univ a) := by
  rw [globalMinimumOn_iff, globalMaximumOn_iff]
  simp only [a.property, true_and]
  constructor
  · change (∀ x ∈ S, f a ≤ f x) ↔ ∀ x : S, x ∈ univ → f a ≤ f x
    simp
  · change (∀ x ∈ S, f x ≤ f a) ↔ ∀ x : S, x ∈ univ → f x ≤ f a
    simp

end D04
