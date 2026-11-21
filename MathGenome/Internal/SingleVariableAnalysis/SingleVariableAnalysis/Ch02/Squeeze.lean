import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Squeeze

/-!
# Comparison along a common approach

K03.02.squeeze. The proofs intersect the neighborhoods of eventual estimates
with epsilon neighborhoods of the limits. Finite approaches use minima of
radii; infinite input approaches use maxima of thresholds. Order preservation
uses an approach point in this intersection, hence needs nontriviality.

The finite-point metric results cover both ℝ and ℂ domains, including the
upstream convention allowing vacuous punctured limits. The common RealApproach
results cover both sides and both infinities with the upstream nontriviality
requirements. The real/complex error corollaries identify dist with the actual
absolute value/complex norm; no nonnegativity hypothesis on the majorant is added.
-/
namespace SingleVariableAnalysis

universe u v

private theorem real_dist_squeeze {f g h L ε : ℝ}
    (ho : f ≤ g ∧ g ≤ h) (hf : dist f L < ε) (hh : dist h L < ε) :
    dist g L < ε := by
  rw [Real.dist_eq] at hf hh ⊢
  obtain ⟨hf₁, _⟩ := abs_lt.mp hf
  obtain ⟨_, hh₂⟩ := abs_lt.mp hh
  apply abs_lt.mpr
  constructor <;> linarith [ho.1, ho.2]

/-- Eventual assertions can be imposed simultaneously for any source approach. -/
theorem approachEventually_and {E : Set ℝ} {q : RealApproach} {P Q : ℝ → Prop}
    (hP : ApproachEventually E q P) (hQ : ApproachEventually E q Q) :
    ApproachEventually E q (fun x => P x ∧ Q x) := by
  obtain ⟨r, hr, hP⟩ := hP
  obtain ⟨s, hs, hQ⟩ := hQ
  cases q with
  | punctured a =>
    refine ⟨min r s, lt_min hr hs, fun x hx h => ?_⟩
    exact ⟨hP x hx ⟨h.1, h.2.trans_le (min_le_left _ _)⟩,
      hQ x hx ⟨h.1, h.2.trans_le (min_le_right _ _)⟩⟩
  | right a =>
    refine ⟨min r s, lt_min hr hs, fun x hx h => ?_⟩
    exact ⟨hP x hx ⟨h.1, h.2.trans_le (add_le_add (le_refl a) (min_le_left r s))⟩,
      hQ x hx ⟨h.1, h.2.trans_le (add_le_add (le_refl a) (min_le_right r s))⟩⟩
  | left a =>
    refine ⟨min r s, lt_min hr hs, fun x hx h => ?_⟩
    exact ⟨hP x hx ⟨lt_of_le_of_lt (sub_le_sub_left (min_le_left _ _) _) h.1, h.2⟩,
      hQ x hx ⟨lt_of_le_of_lt (sub_le_sub_left (min_le_right _ _) _) h.1, h.2⟩⟩
  | posInfinity =>
    refine ⟨max r s, hr.trans_le (le_max_left _ _), fun x hx h => ?_⟩
    exact ⟨hP x hx (lt_of_le_of_lt (le_max_left r s) h),
      hQ x hx (lt_of_le_of_lt (le_max_right r s) h)⟩
  | negInfinity =>
    refine ⟨max r s, hr.trans_le (le_max_left _ _), fun x hx h => ?_⟩
    exact ⟨hP x hx (lt_of_lt_of_le h (neg_le_neg (le_max_left r s))),
      hQ x hx (lt_of_lt_of_le h (neg_le_neg (le_max_right r s)))⟩

theorem relativePuncturedLimit_squeeze {X : Type u} [MetricSpace X]
    (f g h : X → ℝ) (E : Set X) (a : X) (L : ℝ)
    (ho : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      f x ≤ g x ∧ g x ≤ h x)
    (hf : RelativePuncturedLimit f E a L) (hh : RelativePuncturedLimit h E a L) :
    RelativePuncturedLimit g E a L := by
  intro ε hε
  obtain ⟨r, hr, ho⟩ := ho
  obtain ⟨s, hs, hf⟩ := hf ε hε
  obtain ⟨t, ht, hh⟩ := hh ε hε
  refine ⟨min r (min s t), lt_min hr (lt_min hs ht), fun x hx hp hd => ?_⟩
  have hxr := hd.trans_le (min_le_left _ _)
  have hxs := hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxt := hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact real_dist_squeeze (ho x hx hp hxr) (hf x hx hp hxs) (hh x hx hp hxt)

theorem relativePuncturedLimit_of_dist_le {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y) (v : X → ℝ)
    (hb : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      dist (f x) L ≤ v x)
    (hv : RelativePuncturedLimit v E a 0) : RelativePuncturedLimit f E a L := by
  intro ε hε
  obtain ⟨r, hr, hb⟩ := hb
  obtain ⟨s, hs, hv⟩ := hv ε hε
  refine ⟨min r s, lt_min hr hs, fun x hx hp hd => ?_⟩
  have hsmall := hv x hx hp (hd.trans_le (min_le_right _ _))
  rw [Real.dist_eq, sub_zero] at hsmall
  exact (hb x hx hp (hd.trans_le (min_le_left _ _))).trans_lt
    ((le_abs_self _).trans_lt hsmall)

theorem relativePuncturedLimit_of_abs_le {X : Type u} [MetricSpace X]
    (f : X → ℝ) (E : Set X) (a : X) (L : ℝ) (v : X → ℝ)
    (hb : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      |f x - L| ≤ v x)
    (hv : RelativePuncturedLimit v E a 0) : RelativePuncturedLimit f E a L := by
  apply relativePuncturedLimit_of_dist_le f E a L v _ hv
  simpa only [Real.dist_eq] using hb

theorem relativePuncturedLimit_of_norm_le {X : Type u} [MetricSpace X]
    (f : X → ℂ) (E : Set X) (a : X) (L : ℂ) (v : X → ℝ)
    (hb : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      ‖f x - L‖ ≤ v x)
    (hv : RelativePuncturedLimit v E a 0) : RelativePuncturedLimit f E a L := by
  apply relativePuncturedLimit_of_dist_le f E a L v _ hv
  simpa only [dist_eq_norm] using hb

theorem relativePuncturedLimit_le_of_eventually_le {X : Type u} [MetricSpace X]
    (f g : X → ℝ) (E : Set X) (a : X) (A B : ℝ)
    (ha : DomainAccumulation E a)
    (ho : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ → f x ≤ g x)
    (hf : RelativePuncturedLimit f E a A) (hg : RelativePuncturedLimit g E a B) :
    A ≤ B := by
  by_contra hn
  have hp : 0 < (A - B) / 3 := by linarith
  obtain ⟨r, hr, ho⟩ := ho
  obtain ⟨s, hs, hf⟩ := hf _ hp
  obtain ⟨t, ht, hg⟩ := hg _ hp
  obtain ⟨x, hx, hxa, hd⟩ := ha (min r (min s t)) (lt_min hr (lt_min hs ht))
  have hle := ho x hx hxa (hd.trans_le (min_le_left _ _))
  have hF := hf x hx hxa (hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hG := hg x hx hxa (hd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  rw [Real.dist_eq] at hF hG
  have hFlo := (abs_lt.mp hF).1
  have hGhi := (abs_lt.mp hG).2
  linarith

theorem finiteApproachLimit_squeeze
    (f g h : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ)
    (ho : ApproachEventually E q (fun x => f x ≤ g x ∧ g x ≤ h x))
    (hf : FiniteApproachLimit f E q L) (hh : FiniteApproachLimit h E q L) :
    FiniteApproachLimit g E q L := by
  refine ⟨hf.1, fun ε hε => ?_⟩
  obtain ⟨r, hr, hb⟩ := approachEventually_and ho
    (approachEventually_and (hf.2 ε hε) (hh.2 ε hε))
  exact ⟨r, hr, fun x hx hd =>
    real_dist_squeeze (hb x hx hd).1 (hb x hx hd).2.1 (hb x hx hd).2.2⟩

theorem finiteApproachLimit_of_dist_le {Y : Type u} [MetricSpace Y]
    (f : ℝ → Y) (E : Set ℝ) (q : RealApproach) (L : Y) (v : ℝ → ℝ)
    (hb : ApproachEventually E q (fun x => dist (f x) L ≤ v x))
    (hv : FiniteApproachLimit v E q 0) : FiniteApproachLimit f E q L := by
  refine ⟨hv.1, fun ε hε => ?_⟩
  obtain ⟨r, hr, h⟩ := approachEventually_and hb (hv.2 ε hε)
  refine ⟨r, hr, fun x hx hd => ?_⟩
  have hsmall := (h x hx hd).2
  rw [Real.dist_eq, sub_zero] at hsmall
  exact (h x hx hd).1.trans_lt ((le_abs_self _).trans_lt hsmall)

theorem finiteApproachLimit_of_abs_le
    (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ) (v : ℝ → ℝ)
    (hb : ApproachEventually E q (fun x => |f x - L| ≤ v x))
    (hv : FiniteApproachLimit v E q 0) : FiniteApproachLimit f E q L := by
  apply finiteApproachLimit_of_dist_le f E q L v _ hv
  simpa only [Real.dist_eq] using hb

theorem finiteApproachLimit_of_norm_le
    (f : ℝ → ℂ) (E : Set ℝ) (q : RealApproach) (L : ℂ) (v : ℝ → ℝ)
    (hb : ApproachEventually E q (fun x => ‖f x - L‖ ≤ v x))
    (hv : FiniteApproachLimit v E q 0) : FiniteApproachLimit f E q L := by
  apply finiteApproachLimit_of_dist_le f E q L v _ hv
  simpa only [dist_eq_norm] using hb

theorem finiteApproachLimit_le_of_eventually_le
    (f g : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (A B : ℝ)
    (ho : ApproachEventually E q (fun x => f x ≤ g x))
    (hf : FiniteApproachLimit f E q A) (hg : FiniteApproachLimit g E q B) :
    A ≤ B := by
  by_contra hn
  have hp : 0 < (A - B) / 3 := by linarith
  obtain ⟨r, hr, hb⟩ := approachEventually_and ho
    (approachEventually_and (hf.2 _ hp) (hg.2 _ hp))
  obtain ⟨x, hx, hd⟩ := hf.1 r hr
  have hle := (hb x hx hd).1
  have hF := (hb x hx hd).2.1
  have hG := (hb x hx hd).2.2
  rw [Real.dist_eq] at hF hG
  have hFlo := (abs_lt.mp hF).1
  have hGhi := (abs_lt.mp hG).2
  linarith

end SingleVariableAnalysis
