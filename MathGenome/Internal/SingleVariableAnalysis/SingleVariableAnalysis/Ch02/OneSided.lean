import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.RelativeLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Tactic.Linarith

/-!
# One-sided and infinite limits

K03.02.one_sided. Approach regions are nested intervals or tails, parameterized
by a positive radius/threshold. `ApproachNontrivial` requires points in every
region. Thus a one-sided limit includes accumulation on that side, and a limit
at infinity includes unboundedness in that direction. In contrast, the upstream
`RelativePuncturedLimit` by itself permits vacuous limits.

Finite-output definitions are metric and specialize to real absolute value or
complex modulus. The output-infinity predicates apply to any of the five input
approaches. Their punctured branch permits vacuity, exactly as the source
threshold definitions do; their sided and tail branches require nontriviality.
Real positive/negative divergence and complex modulus divergence remain distinct
predicates. `FiniteApproachLimit` is an explicitly nontrivial finite-limit
wrapper; ordinary punctured finite limits use `RelativePuncturedLimit`.
-/

namespace SingleVariableAnalysis

universe u

def ApproachRegion : RealApproach → ℝ → Set ℝ :=
  fun q r => match q with
  | .punctured a => {x | 0 < |x - a| ∧ |x - a| < r}
  | .right a => Set.Ioo a (a + r)
  | .left a => Set.Ioo (a - r) a
  | .posInfinity => Set.Ioi r
  | .negInfinity => Set.Iio (-r)

def ApproachNontrivial : Set ℝ → RealApproach → Prop :=
  fun E q => ∀ r : ℝ, 0 < r → ∃ x ∈ E, x ∈ ApproachRegion q r

def ApproachEventually : Set ℝ → RealApproach → (ℝ → Prop) → Prop :=
  fun E q P => ∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, x ∈ ApproachRegion q r → P x

def RightAccumulation : Set ℝ → ℝ → Prop :=
  fun E a => ApproachNontrivial E (.right a)

def LeftAccumulation : Set ℝ → ℝ → Prop :=
  fun E a => ApproachNontrivial E (.left a)

def DomainUnboundedAbove : Set ℝ → Prop :=
  fun E => ApproachNontrivial E .posInfinity

def DomainUnboundedBelow : Set ℝ → Prop :=
  fun E => ApproachNontrivial E .negInfinity

/-- Source domain requirements: punctured limits may be vacuous; one-sided
limits require side accumulation, and infinite-input limits require the
corresponding directional unboundedness. -/
def ApproachAdmissible : Set ℝ → RealApproach → Prop :=
  fun E q => match q with
  | .punctured _ => True
  | .right a => RightAccumulation E a
  | .left a => LeftAccumulation E a
  | .posInfinity => DomainUnboundedAbove E
  | .negInfinity => DomainUnboundedBelow E

def FiniteApproachLimit : {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → RealApproach → Y → Prop :=
  fun f E q L => ApproachNontrivial E q ∧
    ∀ ε : ℝ, 0 < ε → ApproachEventually E q (fun x => dist (f x) L < ε)

def RightRelativeLimit : {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → ℝ → Y → Prop :=
  fun f E a L => FiniteApproachLimit f E (.right a) L

def LeftRelativeLimit : {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → ℝ → Y → Prop :=
  fun f E a L => FiniteApproachLimit f E (.left a) L

def LimitAtPosInfinity : {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → Y → Prop :=
  fun f E L => FiniteApproachLimit f E .posInfinity L

def LimitAtNegInfinity : {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → Y → Prop :=
  fun f E L => FiniteApproachLimit f E .negInfinity L

def RealLimitToPosInfinity : (ℝ → ℝ) → Set ℝ → RealApproach → Prop :=
  fun f E q => ApproachAdmissible E q ∧ ∀ B : ℝ, ApproachEventually E q (fun x => B < f x)

def RealLimitToNegInfinity : (ℝ → ℝ) → Set ℝ → RealApproach → Prop :=
  fun f E q => ApproachAdmissible E q ∧ ∀ B : ℝ, ApproachEventually E q (fun x => f x < B)

def ComplexModulusLimitToInfinity : (ℝ → ℂ) → Set ℝ → RealApproach → Prop :=
  fun f E q => ApproachAdmissible E q ∧ ∀ B : ℝ, ApproachEventually E q (fun x => B < ‖f x‖)

/-- No accumulation assumption is attached to the punctured threshold condition. -/
theorem realLimitToPosInfinity_punctured_iff (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ) :
    RealLimitToPosInfinity f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → B < f x := by
  simp only [RealLimitToPosInfinity, ApproachAdmissible, true_and,
    ApproachEventually, ApproachRegion, Set.mem_ofPred_eq]

theorem realLimitToNegInfinity_punctured_iff (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ) :
    RealLimitToNegInfinity f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → f x < B := by
  simp only [RealLimitToNegInfinity, ApproachAdmissible, true_and,
    ApproachEventually, ApproachRegion, Set.mem_ofPred_eq]

theorem complexModulusLimitToInfinity_punctured_iff
    (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ) :
    ComplexModulusLimitToInfinity f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → B < ‖f x‖ := by
  simp only [ComplexModulusLimitToInfinity, ApproachAdmissible, true_and,
    ApproachEventually, ApproachRegion, Set.mem_ofPred_eq]

/-- On a singleton punctured at its only point, all threshold conditions are
vacuous, even for constant zero functions. -/
theorem infiniteOutputLimits_singleton (f : ℝ → ℝ) (g : ℝ → ℂ) (a : ℝ) :
    RealLimitToPosInfinity f {a} (.punctured a) ∧
      RealLimitToNegInfinity f {a} (.punctured a) ∧
      ComplexModulusLimitToInfinity g {a} (.punctured a) := by
  have h (P : ℝ → Prop) : ApproachEventually {a} (.punctured a) P := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hp
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    change 0 < |a - a| ∧ |a - a| < 1 at hp
    simp at hp
  exact ⟨⟨True.intro, fun B => h (fun x => B < f x)⟩,
    ⟨True.intro, fun B => h (fun x => f x < B)⟩,
    ⟨True.intro, fun B => h (fun x => B < ‖g x‖)⟩⟩

theorem rightAccumulation_iff :
    ∀ (E : Set ℝ) (a : ℝ), RightAccumulation E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, a < x ∧ x < a + δ := by
  intros; rfl

theorem leftAccumulation_iff :
    ∀ (E : Set ℝ) (a : ℝ), LeftAccumulation E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, a - δ < x ∧ x < a := by
  intros; rfl

theorem domainUnboundedAbove_iff :
    ∀ E : Set ℝ, DomainUnboundedAbove E ↔
    ∀ B : ℝ, ∃ x ∈ E, B < x := by
  intro E
  constructor
  · intro h B
    obtain ⟨x, hx, hgt⟩ := h (max 1 B) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact ⟨x, hx, lt_of_le_of_lt (le_max_right _ _) hgt⟩
  · intro h r _
    exact h r

theorem domainUnboundedBelow_iff :
    ∀ E : Set ℝ, DomainUnboundedBelow E ↔
    ∀ B : ℝ, ∃ x ∈ E, x < B := by
  intro E
  constructor
  · intro h B
    obtain ⟨x, hx, hlt⟩ := h (max 1 (-B)) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    refine ⟨x, hx, ?_⟩
    have hbound := le_max_right (1 : ℝ) (-B)
    change x < -(max 1 (-B)) at hlt
    linarith
  · intro h r _
    exact h (-r)

theorem domainUnboundedAbove_not_bddAbove :
    ∀ E : Set ℝ,
    DomainUnboundedAbove E ↔ ¬ BddAbove E := by
  intro E
  rw [domainUnboundedAbove_iff, not_bddAbove_iff]

theorem domainUnboundedBelow_not_bddBelow :
    ∀ E : Set ℝ,
    DomainUnboundedBelow E ↔ ¬ BddBelow E := by
  intro E
  rw [domainUnboundedBelow_iff, not_bddBelow_iff]

theorem rightAccumulation_domain_iff :
    ∀ (E : Set ℝ) (a : ℝ),
    RightAccumulation E a ↔ DomainAccumulation (E ∩ Set.Ioi a) a := by
  intro E a
  rw [rightAccumulation_iff, real_domainAccumulation_iff]
  constructor
  · intro h δ hδ
    obtain ⟨x, hx, ha, hd⟩ := h δ hδ
    refine ⟨x, ⟨hx, ha⟩, ?_, ?_⟩ <;> rw [abs_of_pos (sub_pos.mpr ha)] <;> linarith
  · intro h δ hδ
    obtain ⟨x, ⟨hx, ha⟩, _, hd⟩ := h δ hδ
    refine ⟨x, hx, ha, ?_⟩
    rw [abs_of_pos (sub_pos.mpr ha)] at hd
    linarith

theorem leftAccumulation_domain_iff :
    ∀ (E : Set ℝ) (a : ℝ),
    LeftAccumulation E a ↔ DomainAccumulation (E ∩ Set.Iio a) a := by
  intro E a
  rw [leftAccumulation_iff, real_domainAccumulation_iff]
  constructor
  · intro h δ hδ
    obtain ⟨x, hx, hd, ha⟩ := h δ hδ
    refine ⟨x, ⟨hx, ha⟩, ?_, ?_⟩ <;> rw [abs_of_neg (sub_neg.mpr ha)] <;> linarith
  · intro h δ hδ
    obtain ⟨x, ⟨hx, ha⟩, _, hd⟩ := h δ hδ
    refine ⟨x, hx, ?_, ha⟩
    rw [abs_of_neg (sub_neg.mpr ha)] at hd
    linarith

theorem rightRelativeLimit_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    RightRelativeLimit f E a L ↔ RightAccumulation E a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, a < x → x < a + δ → dist (f x) L < ε := by
  intros Y _ f E a L
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hd, hb⟩ := h ε hε
    exact ⟨δ, hd, fun x hx hax hxd => hb x hx ⟨hax, hxd⟩⟩
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hd, hb⟩ := h ε hε
    exact ⟨δ, hd, fun x hx hxd => hb x hx hxd.1 hxd.2⟩

theorem leftRelativeLimit_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    LeftRelativeLimit f E a L ↔ LeftAccumulation E a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, a - δ < x → x < a → dist (f x) L < ε := by
  intros Y _ f E a L
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hd, hb⟩ := h ε hε
    exact ⟨δ, hd, fun x hx hdx hxa => hb x hx ⟨hdx, hxa⟩⟩
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hd, hb⟩ := h ε hε
    exact ⟨δ, hd, fun x hx hxd => hb x hx hxd.1 hxd.2⟩

theorem rightRelativeLimit_relative_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    RightRelativeLimit f E a L ↔ RightAccumulation E a ∧
      RelativePuncturedLimit f (E ∩ Set.Ioi a) a L := by
  intro Y _ f E a L
  rw [rightRelativeLimit_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h ε hε
    obtain ⟨δ, hd, hb⟩ := h ε hε
    refine ⟨δ, hd, fun x hx _ hxd => hb x hx.1 hx.2 ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hx.2)] at hxd
    linarith
  · intro h ε hε
    obtain ⟨δ, hd, hb⟩ := h ε hε
    refine ⟨δ, hd, fun x hx hax hxd => hb x ⟨hx, hax⟩ ?_ ?_⟩
    all_goals rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]; linarith

theorem leftRelativeLimit_relative_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    LeftRelativeLimit f E a L ↔ LeftAccumulation E a ∧
      RelativePuncturedLimit f (E ∩ Set.Iio a) a L := by
  intro Y _ f E a L
  rw [leftRelativeLimit_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h ε hε
    obtain ⟨δ, hd, hb⟩ := h ε hε
    refine ⟨δ, hd, fun x hx _ hxd => hb x hx.1 ?_ hx.2⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hx.2)] at hxd
    linarith
  · intro h ε hε
    obtain ⟨δ, hd, hb⟩ := h ε hε
    refine ⟨δ, hd, fun x hx hdx hxa => hb x ⟨hx, hxa⟩ ?_ ?_⟩
    all_goals rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hxa)]; linarith

theorem limitAtPosInfinity_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    LimitAtPosInfinity f E L ↔ DomainUnboundedAbove E ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, A < x → dist (f x) L < ε := by
  intros; rfl

theorem limitAtNegInfinity_iff :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    LimitAtNegInfinity f E L ↔ DomainUnboundedBelow E ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, x < -A → dist (f x) L < ε := by
  intros; rfl

theorem real_finiteApproachLimit_iff :
    ∀ (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ),
    FiniteApproachLimit f E q L ↔ ApproachNontrivial E q ∧
      ∀ ε : ℝ, 0 < ε → ApproachEventually E q (fun x => |f x - L| < ε) := by
  intros
  simp only [FiniteApproachLimit, Real.dist_eq]

theorem complex_finiteApproachLimit_iff :
    ∀ (f : ℝ → ℂ) (E : Set ℝ) (q : RealApproach) (L : ℂ),
    FiniteApproachLimit f E q L ↔ ApproachNontrivial E q ∧
      ∀ ε : ℝ, 0 < ε → ApproachEventually E q (fun x => ‖f x - L‖ < ε) := by
  intros
  simp only [FiniteApproachLimit, dist_eq_norm]

theorem relativePuncturedLimit_iff_one_sided :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    RightAccumulation E a → LeftAccumulation E a →
      (RelativePuncturedLimit f E a L ↔
        RightRelativeLimit f E a L ∧ LeftRelativeLimit f E a L) := by
  intro Y _ f E a L hr hl
  rw [rightRelativeLimit_iff, leftRelativeLimit_iff]
  constructor
  · intro h
    constructor
    · refine ⟨hr, fun ε hε => ?_⟩
      obtain ⟨δ, hd, hb⟩ := h ε hε
      refine ⟨δ, hd, fun x hx hax hxd => hb x hx ?_ ?_⟩
      all_goals rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hax)]; linarith
    · refine ⟨hl, fun ε hε => ?_⟩
      obtain ⟨δ, hd, hb⟩ := h ε hε
      refine ⟨δ, hd, fun x hx hdx hxa => hb x hx ?_ ?_⟩
      all_goals rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hxa)]; linarith
  · rintro ⟨⟨_, hR⟩, ⟨_, hL⟩⟩ ε hε
    obtain ⟨δR, hδR, hbR⟩ := hR ε hε
    obtain ⟨δL, hδL, hbL⟩ := hL ε hε
    refine ⟨min δR δL, lt_min hδR hδL, fun x hx hp hd => ?_⟩
    rw [Real.dist_eq] at hp hd
    have hne : x ≠ a := sub_ne_zero.mp (abs_pos.mp hp)
    rcases lt_or_gt_of_ne hne with hxa | hax
    · apply hbL x hx _ hxa
      have hb := (abs_lt.mp (lt_of_lt_of_le hd (min_le_right _ _))).1
      linarith
    · apply hbR x hx hax
      have hb := (abs_lt.mp (lt_of_lt_of_le hd (min_le_left _ _))).2
      linarith

theorem finiteLimit_exists_iff_one_sided_agree :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ),
    RightAccumulation E a → LeftAccumulation E a →
      ((∃ L : Y, RelativePuncturedLimit f E a L) ↔
        ∃ L : Y, RightRelativeLimit f E a L ∧ LeftRelativeLimit f E a L) := by
  intro Y _ f E a hr hl
  exact exists_congr fun L => relativePuncturedLimit_iff_one_sided f E a L hr hl

theorem positiveDomain_zero_right_accumulation :
    RightAccumulation (Set.Ioi (0 : ℝ)) 0 := by
  rw [rightAccumulation_iff]
  intro δ hδ
  exact ⟨δ / 2, half_pos hδ, half_pos hδ, by linarith⟩

theorem positiveDomain_zero_not_left_accumulation :
    ¬ LeftAccumulation (Set.Ioi (0 : ℝ)) 0 := by
  rw [leftAccumulation_iff]
  intro h
  obtain ⟨x, hx, _, hneg⟩ := h 1 zero_lt_one
  exact (not_lt_of_gt hx) hneg

theorem positiveDomain_zero_relative_iff_right :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (L : Y),
    RelativePuncturedLimit f (Set.Ioi 0) 0 L ↔
      RightRelativeLimit f (Set.Ioi 0) 0 L := by
  intro Y _ f L
  rw [rightRelativeLimit_relative_iff]
  simp only [Set.inter_self, positiveDomain_zero_right_accumulation, true_and]

theorem positiveDomain_zero_no_left_limit :
    ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (L : Y),
    ¬ LeftRelativeLimit f (Set.Ioi 0) 0 L := by
  intro Y _ f L h
  exact positiveDomain_zero_not_left_accumulation h.1

end SingleVariableAnalysis
