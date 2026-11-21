import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntervalImages
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.InverseContinuity
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! K03.03.inverse_continuity. An order isomorphism between intervals with their
induced topologies is a homeomorphism. For decreasing maps we dualize the image
order, preserving its topology. No compactness or nonemptiness is assumed. -/
noncomputable section
namespace SingleVariableAnalysis

/-- The given function identifies its interval domain homeomorphically with its image. -/
theorem continuous_monotone_homeomorph (f : ℝ → ℝ) (I : Set ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) :
    RealInterval (f '' I) ∧ ∃ e : I ≃ₜ (f '' I), ∀ x : I, (e x : ℝ) = f x := by
  have hJ := continuous_real_interval_image f I hI hf
  let : Set.OrdConnected I := (realInterval_iff_ordConnected I).mp hI
  let : Set.OrdConnected (f '' I) := (realInterval_iff_ordConnected _).mp hJ
  let F : I → (f '' I) := fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩
  have hs : Function.Surjective F := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨hJ, ?_⟩
  rcases hm with hm | hm
  · have hmono : StrictMono F := fun x y hxy => hm x.property y.property hxy
    let e := hmono.orderIsoOfSurjective F hs
    exact ⟨e.toHomeomorph, fun _ => rfl⟩
  · have hmono : StrictMono (β := OrderDual (f '' I)) F :=
      fun x y hxy => hm x.property y.property hxy
    let e := StrictMono.orderIsoOfSurjective (β := OrderDual (f '' I)) F hmono hs
    exact ⟨{ toEquiv := e.toEquiv
             continuous_toFun := e.continuous
             continuous_invFun := e.symm.continuous }, fun _ => rfl⟩

/-- Bijectivity and both inverse identities, with continuity on the entire image. -/
theorem continuous_monotone_inverse (f : ℝ → ℝ) (I : Set ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) :
    Set.BijOn f I (f '' I) ∧ RealInterval (f '' I) ∧
      ∃ g : (f '' I) → I, Continuous g ∧
        (∀ x : I, g ⟨f x, ⟨x, x.property, rfl⟩⟩ = x) ∧
        (∀ y : (f '' I), f (g y) = (y : ℝ)) := by
  obtain ⟨hJ, e, he⟩ := continuous_monotone_homeomorph f I hI hf hm
  have hex (x : I) : e x = ⟨f x, ⟨x, x.property, rfl⟩⟩ := Subtype.ext (he x)
  refine ⟨⟨fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩, hJ, e.symm,
    e.symm.continuous, ?_, ?_⟩
  · intro x hx y hy hxy
    have hh : e (⟨x, hx⟩ : I) = e ⟨y, hy⟩ :=
      Subtype.ext (by simpa only [he] using hxy)
    exact congrArg Subtype.val (e.injective hh)
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · intro x
    rw [← hex x, e.symm_apply_apply]
  · intro y
    rw [← he, e.apply_symm_apply]

def disconnectedDomain : Set ℝ := Set.Ico 0 1 ∪ {2}
def disconnectedMap (x : ℝ) : ℝ := if x < 1 then x else 1
def disconnectedInverse (y : ℝ) : ℝ := if y < 1 then y else 2

private theorem disconnected_domain_cases {x : ℝ} (hx : x ∈ disconnectedDomain) :
    (0 ≤ x ∧ x < 1) ∨ x = 2 := by
  simpa only [disconnectedDomain, Set.mem_union, Set.mem_Ico,
    Set.mem_singleton_iff] using hx

private theorem disconnected_map_continuous : RelativeContinuous disconnectedMap disconnectedDomain := by
  intro x hx
  rcases disconnected_domain_cases hx with hx | rfl
  · intro ε hε
    refine ⟨min ε (1 - x), lt_min hε (by linarith [hx.2]), ?_⟩
    intro y _ hy
    have hyε := lt_of_lt_of_le hy (min_le_left ε (1 - x))
    have hyδ := lt_of_lt_of_le hy (min_le_right ε (1 - x))
    have hy1 : y < 1 := by
      rw [Real.dist_eq] at hyδ
      have := (abs_lt.mp hyδ).2
      linarith
    simpa only [disconnectedMap, ite_eq_left hx.2, ite_eq_left hy1] using hyε
  · apply relativeContinuousAt_of_isolating_ball disconnectedMap disconnectedDomain ⟨2, hx⟩
    refine ⟨1, by norm_num, ?_⟩
    intro y hy hd
    rcases disconnected_domain_cases hy with hy | hy
    · rw [Real.dist_eq] at hd
      have := (abs_lt.mp hd).1
      linarith [hy.2]
    · exact hy

private theorem disconnected_map_strictMono : StrictMonoOn disconnectedMap disconnectedDomain := by
  intro x hx y hy hxy
  rcases disconnected_domain_cases hx with hx | rfl <;>
    rcases disconnected_domain_cases hy with hy | rfl
  · simpa only [disconnectedMap, ite_eq_left hx.2, ite_eq_left hy.2] using hxy
  · simpa only [disconnectedMap, ite_eq_left hx.2, show ¬ (2 : ℝ) < 1 by norm_num,
      ite_false] using hx.2
  · linarith [hy.2]
  · linarith

private theorem disconnected_map_image :
    disconnectedMap '' disconnectedDomain = Set.Icc 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases disconnected_domain_cases hx with hx | rfl
    · simpa only [disconnectedMap, ite_eq_left hx.2, Set.mem_Icc] using ⟨hx.1, hx.2.le⟩
    · norm_num [disconnectedMap]
  · intro hy
    by_cases hy1 : y < 1
    · exact ⟨y, Or.inl ⟨hy.1, hy1⟩, by simp [disconnectedMap, hy1]⟩
    · have hyEq : y = 1 := le_antisymm hy.2 (le_of_not_gt hy1)
      subst y
      exact ⟨2, Or.inr rfl, by norm_num [disconnectedMap]⟩

private theorem disconnected_inverse_mapsTo :
    Set.MapsTo disconnectedInverse (Set.Icc 0 1) disconnectedDomain := by
  intro y hy
  by_cases hy1 : y < 1
  · simpa only [disconnectedInverse, ite_eq_left hy1] using
      (show y ∈ disconnectedDomain from Or.inl ⟨hy.1, hy1⟩)
  · simp only [disconnectedInverse, ite_eq_right hy1]
    exact Or.inr rfl

private theorem disconnected_inverse_left :
    ∀ x ∈ disconnectedDomain, disconnectedInverse (disconnectedMap x) = x := by
  intro x hx
  rcases disconnected_domain_cases hx with hx | rfl
  · simp [disconnectedMap, disconnectedInverse, hx.2]
  · norm_num [disconnectedMap, disconnectedInverse]

private theorem disconnected_inverse_right :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, disconnectedMap (disconnectedInverse y) = y := by
  intro y hy
  by_cases hy1 : y < 1
  · simp [disconnectedMap, disconnectedInverse, hy1]
  · have hyEq : y = 1 := le_antisymm hy.2 (le_of_not_gt hy1)
    subst y
    norm_num [disconnectedMap, disconnectedInverse]

/-- The jump in the inverse occurs at the included endpoint y = 1. -/
private theorem disconnected_inverse_not_continuous :
    ¬ RelativeContinuousAt disconnectedInverse (Set.Icc 0 1) 1 := by
  intro h
  obtain ⟨δ, hδ, hb⟩ := h (1 / 2) (by norm_num)
  let t : ℝ := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have hy : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hd : dist (1 - t) (1 : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith
  have he := hb (1 - t) hy hd
  rw [disconnectedInverse, ite_eq_left (by linarith : 1 - t < 1),
    disconnectedInverse, ite_eq_right (by norm_num : ¬ (1 : ℝ) < 1),
    Real.dist_eq, abs_of_neg (by linarith : 1 - t - 2 < 0)] at he
  linarith

/-- The manuscript's exact domain, map, image and two-sided inverse, with
failure of inverse continuity at the upper endpoint. -/
theorem disconnected_inverse_counterexample :
    ¬ RealInterval disconnectedDomain ∧
    RelativeContinuous disconnectedMap disconnectedDomain ∧
    StrictMonoOn disconnectedMap disconnectedDomain ∧
    disconnectedMap '' disconnectedDomain = Set.Icc 0 1 ∧
    Set.MapsTo disconnectedInverse (Set.Icc 0 1) disconnectedDomain ∧
    (∀ x ∈ disconnectedDomain, disconnectedInverse (disconnectedMap x) = x) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1, disconnectedMap (disconnectedInverse y) = y) ∧
    ¬ RelativeContinuousAt disconnectedInverse (Set.Icc 0 1) 1 := by
  refine ⟨?_, disconnected_map_continuous, disconnected_map_strictMono,
    disconnected_map_image, disconnected_inverse_mapsTo, disconnected_inverse_left,
    disconnected_inverse_right, disconnected_inverse_not_continuous⟩
  intro hI
  have h0 : (0 : ℝ) ∈ disconnectedDomain := Or.inl ⟨le_rfl, by norm_num⟩
  have h2 : (2 : ℝ) ∈ disconnectedDomain := Or.inr rfl
  have h1 := disconnected_domain_cases (hI h0 h2 (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 2))
  rcases h1 with h1 | h1 <;> norm_num at h1

end SingleVariableAnalysis
