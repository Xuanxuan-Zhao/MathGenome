import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-! Uniform convergence of improper Darboux integrals, K03.14.uniform_improper.
The only completeness argument concerns scalar values. Proper splitting turns
integrals over tails into differences of truncations. No bound on the integrand,
absolute integrability or nonempty parameter set is used.
-/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
namespace U
export Specs.SingleVariableAnalysis.Ch14.UniformImproper
  (rightFamilyRegularValue leftFamilyRegularValue rightUniformHasIntegralValue
   leftUniformHasIntegralValue rightUniformConvergesValue leftUniformConvergesValue
   rightUniformCauchyValue leftUniformCauchyValue rightUniformErrorValue leftUniformErrorValue
   independentUniformConvergesValue)
end U
open Specs.SingleVariableAnalysis.Ch14.UniformImproper
open scoped ENNReal
universe u v w

noncomputable abbrev RightFamilyRegular := @U.rightFamilyRegularValue
noncomputable abbrev LeftFamilyRegular := @U.leftFamilyRegularValue
noncomputable abbrev RightUniformHasIntegral := @U.rightUniformHasIntegralValue
noncomputable abbrev LeftUniformHasIntegral := @U.leftUniformHasIntegralValue
noncomputable abbrev RightUniformConverges := @U.rightUniformConvergesValue
noncomputable abbrev LeftUniformConverges := @U.leftUniformConvergesValue
noncomputable abbrev RightUniformCauchy := @U.rightUniformCauchyValue
noncomputable abbrev LeftUniformCauchy := @U.leftUniformCauchyValue
noncomputable abbrev RightUniformError := @U.rightUniformErrorValue
noncomputable abbrev LeftUniformError := @U.leftUniformErrorValue
noncomputable abbrev IndependentUniformConverges := @U.independentUniformConvergesValue

/-- The scalar cofinal Cauchy criterion, with a single threshold for all parameters.
The index order may be reversed to treat a left endpoint. -/
theorem exists_uniform_cofinal_limit_iff {α : Type v} {T : Type u} {Y : Type w}
    [LinearOrder α] [MetricSpace Y] [CompleteSpace Y] (H : α → T → Y)
    (hne : Nonempty α) (hmore : ∀ r : α, ∃ s, r < s) :
    (∃ F : T → Y, ∀ ε : ℝ, 0 < ε → ∃ r : α,
      ∀ R : α, r < R → ∀ t : T, dist (H R t) (F t) < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ t : T, ∀ R S : α,
      r < R → R < S → dist (H S t) (H R t) < ε) := by
  constructor
  · rintro ⟨F, hF⟩ ε hε
    obtain ⟨r, hr⟩ := hF (ε / 2) (half_pos hε)
    refine ⟨r, fun t R S hrR hRS => ?_⟩
    calc
      dist (H S t) (H R t) ≤ dist (H S t) (F t) + dist (H R t) (F t) :=
        dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hr S (hrR.trans hRS) t) (hr R hrR t)
      _ = ε := add_halves ε
  · intro hc
    have hp : ∀ t : T, ∃ L : Y, ∀ ε : ℝ, 0 < ε → ∃ r : α,
        ∀ R : α, r < R → dist (H R t) L < ε := by
      intro t
      apply (exists_cofinal_limit_iff (fun R => H R t) hne hmore).mpr
      intro ε hε
      obtain ⟨r, hr⟩ := hc ε hε
      exact ⟨r, hr t⟩
    choose F hF using hp
    refine ⟨F, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨r, fun R hrR t => ?_⟩
    obtain ⟨s, hs⟩ := hF t (ε / 2) (half_pos hε)
    obtain ⟨S, hS⟩ := hmore (max R s)
    have hRS : R < S := (le_max_left _ _).trans_lt hS
    have hsS : s < S := (le_max_right _ _).trans_lt hS
    calc
      dist (H R t) (F t) ≤ dist (H R t) (H S t) + dist (H S t) (F t) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add
        (by simpa only [dist_comm] using hr t R S hrR hRS) (hs S hsS)
      _ = ε := add_halves ε

private theorem scalar_complete_uniform (k : ScalarKind) : CompleteSpace (S.scalarValue k) := by
  cases k with
  | real => exact inferInstanceAs (CompleteSpace ℝ)
  | complex => exact inferInstanceAs (CompleteSpace ℂ)

/-- Nonemptiness depends on the interval, never on the parameter set. -/
private theorem right_indices_exist {a : ℝ} {b : WithTop ℝ}
    (hab : (a : WithTop ℝ) < b) : Nonempty (RightIndex a b) := by
  cases b using WithTop.recTopCoe with
  | top => exact ⟨⟨a + 1, lt_add_one _, WithTop.coe_lt_top _⟩⟩
  | coe b =>
    obtain ⟨r, har, hrb⟩ := exists_between (WithTop.coe_lt_coe.mp hab)
    exact ⟨⟨r, har, WithTop.coe_lt_coe.mpr hrb⟩⟩

private theorem left_indices_exist {a : WithBot ℝ} {b : ℝ}
    (hab : a < (b : WithBot ℝ)) : Nonempty (LeftIndex a b) := by
  cases a using WithBot.recBotCoe with
  | bot => exact ⟨⟨b - 1, WithBot.bot_lt_coe _, sub_one_lt _⟩⟩
  | coe a =>
    obtain ⟨r, har, hrb⟩ := exists_between (WithBot.coe_lt_coe.mp hab)
    exact ⟨⟨r, WithBot.coe_lt_coe.mpr har, hrb⟩⟩

theorem right_uniform_cauchy_criterion : rightUniformCauchyCriterion.{u} := by
  intro k T f a b h
  let : CompleteSpace (S.scalarValue k) := scalar_complete_uniform k
  have hc := exists_uniform_cofinal_limit_iff
    (fun R t => RightTruncation k (fun x => f x t) a b (h.2 t) R)
    (right_indices_exist h.1) (fun r => by
      obtain ⟨s, hrs, _⟩ := right_later r r
      exact ⟨s, hrs⟩)
  change (∃ F : T → S.scalarValue k, ∃ h' : RightFamilyRegular k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ R : RightIndex a b,
      r.val < R.val → ∀ t : T,
        dist (RightTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔ _
  rw [show (∃ F : T → S.scalarValue k, ∃ h' : RightFamilyRegular k T f a b,
      ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ R : RightIndex a b,
        r.val < R.val → ∀ t : T,
          dist (RightTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔
    (∃ F : T → S.scalarValue k, ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ R : RightIndex a b,
      r < R → ∀ t : T,
        dist (RightTruncation k (fun x => f x t) a b (h.2 t) R) (F t) < ε) from
    ⟨fun ⟨F, _, hF⟩ => ⟨F, hF⟩, fun ⟨F, hF⟩ => ⟨F, h, hF⟩⟩, hc]
  constructor
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun t R S hrR hRS => ?_⟩
    obtain ⟨ht, heq⟩ := right_tail_difference k (fun x => f x t) a b (h.2 t) R S hRS
    refine ⟨ht, ?_⟩
    rw [heq]
    simpa only [dist_eq_norm] using hr t R S hrR hRS
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun t R S hrR hRS => ?_⟩
    obtain ⟨ht, heq⟩ := right_tail_difference k (fun x => f x t) a b (h.2 t) R S hRS
    obtain ⟨_, hlt⟩ := hr t R S hrR hRS
    rw [dist_eq_norm, ← heq]
    exact hlt

theorem left_uniform_cauchy_criterion : leftUniformCauchyCriterion.{u} := by
  intro k T f a b h
  let : CompleteSpace (S.scalarValue k) := scalar_complete_uniform k
  have hc := exists_uniform_cofinal_limit_iff (α := OrderDual (LeftIndex a b))
    (fun R t => LeftTruncation k (fun x => f x t) a b (h.2 t) R)
    (left_indices_exist h.1) (fun r => by
      obtain ⟨s, hsr, _⟩ := left_earlier r r
      exact ⟨s, hsr⟩)
  change (∃ F : T → S.scalarValue k, ∃ h' : LeftFamilyRegular k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ R : LeftIndex a b,
      R.val < r.val → ∀ t : T,
        dist (LeftTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔ _
  rw [show (∃ F : T → S.scalarValue k, ∃ h' : LeftFamilyRegular k T f a b,
      ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ R : LeftIndex a b,
        R.val < r.val → ∀ t : T,
          dist (LeftTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔
    (∃ F : T → S.scalarValue k, ∀ ε : ℝ, 0 < ε → ∃ r : OrderDual (LeftIndex a b),
      ∀ R : OrderDual (LeftIndex a b), r < R → ∀ t : T,
        dist (LeftTruncation k (fun x => f x t) a b (h.2 t) R) (F t) < ε) from
    ⟨fun ⟨F, _, hF⟩ => ⟨F, hF⟩, fun ⟨F, hF⟩ => ⟨F, h, hF⟩⟩, hc]
  constructor
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun t R S hRS hSr => ?_⟩
    obtain ⟨ht, heq⟩ := left_tail_difference k (fun x => f x t) a b (h.2 t) R S hRS
    refine ⟨ht, ?_⟩
    rw [heq]
    simpa only [dist_eq_norm] using hr t S R hSr hRS
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun t S R hSr hRS => ?_⟩
    obtain ⟨ht, heq⟩ := left_tail_difference k (fun x => f x t) a b (h.2 t) R S hRS
    obtain ⟨_, hlt⟩ := hr t R S hRS hSr
    rw [dist_eq_norm, ← heq]
    exact hlt

theorem right_infinite_uniform_cauchy_criterion : rightInfiniteCauchyCriterion.{u} := by
  intro k T f a h
  rw [right_uniform_cauchy_criterion k T f a ⊤ h]
  constructor
  · intro hc ε hε
    obtain ⟨r, hr⟩ := hc ε hε
    refine ⟨r.val + 1, by linarith [r.property.1], fun t R S hrR hRS => ?_⟩
    rcases hRS.eq_or_lt with rfl | hRS
    · refine ⟨integrable_degenerate k (fun x => f x t) R, ?_⟩
      have hz : I.scalarIntegralValue k (fun x => f x t)
          (integrable_degenerate k (fun x => f x t) R) = (0 : S.scalarValue k) := by
        cases k <;> exact integral_degenerate _ _ _ _
      rw [hz, norm_zero]
      exact hε
    · let Ri : RightIndex a ⊤ := ⟨R, by linarith [r.property.1], WithTop.coe_lt_top _⟩
      let Si : RightIndex a ⊤ := ⟨S, Ri.property.1.trans hRS, WithTop.coe_lt_top _⟩
      exact hr t Ri Si (by dsimp [Ri]; linarith) hRS
  · intro hc ε hε
    obtain ⟨R₀, haR, hR⟩ := hc ε hε
    refine ⟨⟨R₀, haR, WithTop.coe_lt_top _⟩, fun t R S hrR hRS => ?_⟩
    exact hR t R.val S.val hrR.le hRS.le

theorem right_uniform_pointwise : rightUniformPointwise.{u} := by
  rintro k T f a b F ⟨h, hF⟩ t
  refine ⟨h.2 t, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hF ε hε
  exact ⟨r, fun R hrR => hr R hrR t⟩

theorem left_uniform_pointwise : leftUniformPointwise.{u} := by
  rintro k T f a b F ⟨h, hF⟩ t
  refine ⟨h.2 t, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hF ε hε
  exact ⟨r, fun R hRr => hr R hRr t⟩

theorem right_uniform_empty : rightUniformEmpty.{u} := by
  intro k T _ f a b F hab
  refine ⟨⟨hab, fun t => isEmptyElim t⟩, fun ε _ => ?_⟩
  exact ⟨Classical.choice (right_indices_exist hab), fun _ _ t => isEmptyElim t⟩

theorem left_uniform_empty : leftUniformEmpty.{u} := by
  intro k T _ f a b F hab
  refine ⟨⟨hab, fun t => isEmptyElim t⟩, fun ε _ => ?_⟩
  exact ⟨Classical.choice (left_indices_exist hab), fun _ _ t => isEmptyElim t⟩

/-- Taking an extended supremum of errors preserves uniform convergence.
Using half the tolerance avoids assuming that the supremum is attained. -/
private theorem uniform_cofinal_sup_iff {α : Type v} {T : Type u} [LT α]
    (D : α → T → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ R : α, r < R → ∀ t : T, D R t < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ R : α, r < R →
      (⨆ t : T, ENNReal.ofReal (D R t)) < ENNReal.ofReal ε) := by
  constructor
  · intro h ε hε
    obtain ⟨r, hr⟩ := h (ε / 2) (half_pos hε)
    refine ⟨r, fun R hrR => ?_⟩
    exact (iSup_le (fun t => ENNReal.ofReal_le_ofReal (hr R hrR t).le)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))
  · intro h ε hε
    obtain ⟨r, hr⟩ := h ε hε
    refine ⟨r, fun R hrR t => ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp ((le_iSup (fun t =>
      ENNReal.ofReal (D R t)) t).trans_lt (hr R hrR))

theorem right_uniform_sup_criterion : rightUniformSupCriterion.{u} := by
  intro k T f a b h F
  change (∃ h' : RightFamilyRegular k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ R : RightIndex a b,
      r.val < R.val → ∀ t : T,
        dist (RightTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔ _
  constructor
  · rintro ⟨_, hF⟩
    exact (uniform_cofinal_sup_iff (fun R t =>
      dist (RightTruncation k (fun x => f x t) a b (h.2 t) R) (F t))).mp hF
  · intro hF
    exact ⟨h, (uniform_cofinal_sup_iff (fun R t =>
      dist (RightTruncation k (fun x => f x t) a b (h.2 t) R) (F t))).mpr hF⟩

theorem left_uniform_sup_criterion : leftUniformSupCriterion.{u} := by
  intro k T f a b h F
  change (∃ h' : LeftFamilyRegular k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ R : LeftIndex a b,
      R.val < r.val → ∀ t : T,
        dist (LeftTruncation k (fun x => f x t) a b (h'.2 t) R) (F t) < ε) ↔ _
  constructor
  · rintro ⟨_, hF⟩
    exact (uniform_cofinal_sup_iff (α := OrderDual (LeftIndex a b)) (fun R t =>
      dist (LeftTruncation k (fun x => f x t) a b (h.2 t) R) (F t))).mp hF
  · intro hF
    exact ⟨h, (uniform_cofinal_sup_iff (α := OrderDual (LeftIndex a b)) (fun R t =>
      dist (LeftTruncation k (fun x => f x t) a b (h.2 t) R) (F t))).mpr hF⟩

theorem right_uniform_error_empty : rightUniformErrorEmpty.{u} := by
  intro k T _ f a b h F R
  exact iSup_of_empty _

theorem left_uniform_error_empty : leftUniformErrorEmpty.{u} := by
  intro k T _ f a b h F R
  exact iSup_of_empty _

theorem independent_uniform_cauchy_criterion : independentUniformCauchyCriterion.{u} := by
  intro k T n E h
  have he : ∀ j, (match E j with
      | .right f a b => U.rightUniformConvergesValue k T f a b
      | .left f a b => U.leftUniformConvergesValue k T f a b) ↔
    (match E j with
      | .right f a b => U.rightUniformCauchyValue k T f a b
      | .left f a b => U.leftUniformCauchyValue k T f a b) := by
    intro j
    have hj := h j
    cases he : E j with
    | right f a b =>
      simp only [he] at hj ⊢
      exact right_uniform_cauchy_criterion k T f a b hj
    | left f a b =>
      simp only [he] at hj ⊢
      exact left_uniform_cauchy_criterion k T f a b hj
  exact forall_congr' he

end SingleVariableAnalysis.Riemann.Improper
