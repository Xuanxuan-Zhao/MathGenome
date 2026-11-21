import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.BanachFullConeExactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.UniformSplitBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.KreinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelMoreauLcs
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.InfimalConvolution.BanachFullConeExactness

open Set Filter Topology
open ExpandedFA.P1 ExtendedConvexFunctions
open Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two conjugates are bounded below by their finite-point tests. -/
lemma split_test_le (φ ψ : ExtendedFunction E) (f g : E →L[ℝ] ℝ)
    (x y : E) (r s : ℝ) (hx : φ x = (r : WithTop ℝ))
    (hy : ψ y = (s : WithTop ℝ)) :
    (((f - g) x - r + (g y - s) : ℝ) : EReal) ≤
      conjugateSplitCost E φ ψ f g := by
  have hφ : (((f - g) x - r : ℝ) : EReal) ≤
      C06Conjugates.convexConjugate E φ (f - g) := by
    calc
      _ = ((f - g) x : EReal) - C06Conjugates.extendedRealValue (φ x) := by rw [hx]; rfl
      _ ≤ _ := le_iSup (fun z : E => ((f - g) z : EReal) -
        C06Conjugates.extendedRealValue (φ z)) x
  have hψ : ((g y - s : ℝ) : EReal) ≤ C06Conjugates.convexConjugate E ψ g := by
    calc
      _ = (g y : EReal) - C06Conjugates.extendedRealValue (ψ y) := by rw [hy]; rfl
      _ ≤ _ := le_iSup (fun z : E => (g z : EReal) -
        C06Conjugates.extendedRealValue (ψ z)) y
  exact (EReal.coe_add _ _).le.trans (add_le_add hφ hψ)

/-- A real sublevel of the split cost is an intersection of affine half spaces.
This avoids any continuity assertion about addition at infinite EReal values. -/
lemma split_cost_le_iff (φ ψ : ExtendedFunction E)
    (hp : Proper E φ) (hq : Proper E ψ) (f g : E →L[ℝ] ℝ) (α : ℝ) :
    conjugateSplitCost E φ ψ f g ≤ (α : EReal) ↔
      ∀ (x y : E) (r s : ℝ), φ x = (r : WithTop ℝ) → ψ y = (s : WithTop ℝ) →
        (f - g) x - r + (g y - s) ≤ α := by
  constructor
  · intro h x y r s hx hy
    exact EReal.coe_le_coe_iff.mp ((split_test_le φ ψ f g x y r s hx hy).trans h)
  · intro h
    obtain ⟨y, s, hy⟩ := (proper_iff_finite_value E ψ).mp hq
    have hbound : C06Conjugates.convexConjugate E φ (f - g) ≤
        ((α - (g y - s) : ℝ) : EReal) := by
      apply (FenchelMoreauLcs.convexConjugate_le_real_iff φ (f - g) _).mpr
      intro x r hx
      linarith [h x y r s hx hy]
    have hne := C06Conjugates.convexConjugate_ne_bot E φ hp (f - g)
    have hnt := ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound
    -- Exclude the possible bottom before extracting the real value.
    have hfin : ∃ a : ℝ, C06Conjugates.convexConjugate E φ (f - g) = (a : EReal) := by
      lift C06Conjugates.convexConjugate E φ (f - g) to ℝ using ⟨hnt, hne⟩ with a ha
      exact ⟨a, rfl⟩
    obtain ⟨a, ha⟩ := hfin
    have hψ : C06Conjugates.convexConjugate E ψ g ≤ ((α - a : ℝ) : EReal) := by
      apply (FenchelMoreauLcs.convexConjugate_le_real_iff ψ g _).mpr
      intro z t hz
      have hφ : C06Conjugates.convexConjugate E φ (f - g) ≤
          ((α - (g z - t) : ℝ) : EReal) := by
        apply (FenchelMoreauLcs.convexConjugate_le_real_iff φ (f - g) _).mpr
        intro x r hx
        linarith [h x z r t hx hz]
      rw [ha, EReal.coe_le_coe_iff] at hφ
      linarith
    unfold conjugateSplitCost
    rw [ha]
    calc
      _ ≤ (a : EReal) + ((α - a : ℝ) : EReal) := add_le_add le_rfl hψ
      _ = (α : EReal) := by rw [← EReal.coe_add]; congr 1; ring

/-- Proper conjugates give a finite lower test for every split. -/
lemma split_cost_ne_bot (φ ψ : ExtendedFunction E)
    (hp : Proper E φ) (hq : Proper E ψ) (f g : E →L[ℝ] ℝ) :
    conjugateSplitCost E φ ψ f g ≠ ⊥ := by
  obtain ⟨x, r, hx⟩ := (proper_iff_finite_value E φ).mp hp
  obtain ⟨y, s, hy⟩ := (proper_iff_finite_value E ψ).mp hq
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
    (split_test_le φ ψ f g x y r s hx hy)

/-- Closedness in any parameter space on which every evaluation is continuous. -/
lemma split_sublevel_isClosed {X : Type*} [TopologicalSpace X]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (f g : X → (E →L[ℝ] ℝ))
    (hf : ∀ x : E, Continuous (fun z => f z x))
    (hg : ∀ x : E, Continuous (fun z => g z x)) (α : ℝ) :
    IsClosed {z : X | conjugateSplitCost E φ ψ (f z) (g z) ≤ (α : EReal)} := by
  have heq : {z : X | conjugateSplitCost E φ ψ (f z) (g z) ≤ (α : EReal)} =
      ⋂ (x : E) (y : E) (r : ℝ) (s : ℝ) (_ : φ x = (r : WithTop ℝ))
        (_ : ψ y = (s : WithTop ℝ)),
        {z : X | (f z - g z) x - r + (g z y - s) ≤ α} := by
    ext z
    simp only [mem_ofPred_eq, mem_iInter]
    exact split_cost_le_iff φ ψ hp hq (f z) (g z) α
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_iInter fun r => isClosed_iInter fun s =>
    isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le (((hf x).sub (hg x)).sub continuous_const |>.add
      ((hg y).sub continuous_const)) continuous_const

/-- Lower semicontinuity with values in the full extended real line. -/
lemma split_cost_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (f g : X → (E →L[ℝ] ℝ))
    (hf : ∀ x : E, Continuous (fun z => f z x))
    (hg : ∀ x : E, Continuous (fun z => g z x)) :
    _root_.LowerSemicontinuous (fun z => conjugateSplitCost E φ ψ (f z) (g z)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro α
  induction α using EReal.rec with
  | bot =>
    have heq : {z : X | conjugateSplitCost E φ ψ (f z) (g z) ≤ ⊥} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, le_bot_iff, mem_empty_iff_false, iff_false]
      exact split_cost_ne_bot φ ψ hp hq (f z) (g z)
    change IsClosed {z : X | conjugateSplitCost E φ ψ (f z) (g z) ≤ ⊥}
    rw [heq]
    exact isClosed_empty
  | coe α => exact split_sublevel_isClosed φ ψ hp hq f g hf hg α
  | top => simp

/-- Full-cone boundedness and Alaoglu give compactness of every split sublevel. -/
lemma split_sublevel_isCompact [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ)
    (f : E →L[ℝ] ℝ) (α : ℝ) :
    @IsCompact _ (C12WeakStar.Spec.WeakStarTopologyValue ℝ E)
      {g : E →L[ℝ] ℝ | conjugateSplitCost E φ ψ f g ≤ (α : EReal)} := by
  have hb := UniformSplitBounds.bounded_split_sublevel φ ψ hcone {f}
    Bornology.isBounded_singleton α
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  let : TopologicalSpace (E →L[ℝ] ℝ) := C12WeakStar.Spec.WeakStarTopologyValue ℝ E
  have hs : IsClosed {g : E →L[ℝ] ℝ | conjugateSplitCost E φ ψ f g ≤ (α : EReal)} :=
    split_sublevel_isClosed φ ψ hp hq (fun _ => f) id
      (fun _ => continuous_const) (fun x => KreinSmulian.weakStar_evaluation_continuous x) α
  have hc : IsCompact {g : E →L[ℝ] ℝ | ‖g‖ ≤ max R 0} := by
    simpa only [sub_zero] using
      C13Alaoglu.weakStar_closedBall_isCompact ℝ E 0 (max R 0) (le_max_right R 0)
  exact hc.of_isClosed_subset hs (fun g hg =>
    (hR g ⟨f, mem_singleton f, hg⟩).trans (le_max_left R 0))

/-- Every finite infimum is attained, with no reflexivity assumption.
At +∞ every split has value +∞, so an equality witness also exists there. -/
theorem exists_minimizing_split [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) (f : E →L[ℝ] ℝ) :
    ∃ g : E →L[ℝ] ℝ,
      conjugateSplitCost E φ ψ f g = infimalConvolution E φ ψ f := by
  by_cases ht : infimalConvolution E φ ψ f = ⊤
  · exact ⟨0, top_le_iff.mp (ht ▸ iInf_le (conjugateSplitCost E φ ψ f) 0) |>.trans ht.symm⟩
  have hi : (⨅ g, conjugateSplitCost E φ ψ f g) < ⊤ := lt_top_iff_ne_top.mpr ht
  obtain ⟨g₀, hg₀⟩ := iInf_lt_iff.mp hi
  have hnb := split_cost_ne_bot φ ψ hp hq f g₀
  lift conjugateSplitCost E φ ψ f g₀ to ℝ using ⟨hg₀.ne, hnb⟩ with α hα
  let : TopologicalSpace (E →L[ℝ] ℝ) := C12WeakStar.Spec.WeakStarTopologyValue ℝ E
  have hl := split_cost_lowerSemicontinuous φ ψ hp hq (fun _ => f) id
    (fun _ => continuous_const) (fun x => KreinSmulian.weakStar_evaluation_continuous x)
  have hc := split_sublevel_isCompact φ ψ hp hq hcone f α
  obtain ⟨g, hg, hmin⟩ := (hl.lowerSemicontinuousOn _).exists_isMinOn
    (show {g | conjugateSplitCost E φ ψ f g ≤ (α : EReal)}.Nonempty from ⟨g₀, hα.ge⟩) hc
  refine ⟨g, le_antisymm (le_iInf fun k => ?_) (iInf_le _ g)⟩
  by_cases hk : conjugateSplitCost E φ ψ f k ≤ (α : EReal)
  · exact hmin hk
  · exact hg.trans (le_of_not_ge hk)

/-- The source's finite-value assertion, with all original hypotheses. -/
theorem finite_value_attainment : Spec.FiniteValueAttainment := by
  intro E _ _ _ φ ψ h f r hr
  obtain ⟨g, hg⟩ := exists_minimizing_split φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 f
  exact ⟨g, hg.trans hr⟩

/-- Combining splits combines their real upper bounds. -/
lemma split_cost_convex_bound (φ ψ : ExtendedFunction E)
    (hp : Proper E φ) (hq : Proper E ψ)
    (f₁ f₂ g₁ g₂ : E →L[ℝ] ℝ) (α β a b : ℝ)
    (h₁ : conjugateSplitCost E φ ψ f₁ g₁ ≤ (α : EReal))
    (h₂ : conjugateSplitCost E φ ψ f₂ g₂ ≤ (β : EReal))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    conjugateSplitCost E φ ψ (a • f₁ + b • f₂) (a • g₁ + b • g₂) ≤
      ((a * α + b * β : ℝ) : EReal) := by
  apply (split_cost_le_iff φ ψ hp hq _ _ _).mpr
  intro x y r s hx hy
  have ht₁ := (split_cost_le_iff φ ψ hp hq f₁ g₁ α).mp h₁ x y r s hx hy
  have ht₂ := (split_cost_le_iff φ ψ hp hq f₂ g₂ β).mp h₂ x y r s hx hy
  have heq : (a • f₁ + b • f₂ - (a • g₁ + b • g₂)) x - r +
      ((a • g₁ + b • g₂) y - s) =
      a * ((f₁ - g₁) x - r + (g₁ y - s)) +
      b * ((f₂ - g₂) x - r + (g₂ y - s)) := by
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun c => c * r) hab, congrArg (fun c => c * s) hab]
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left ht₁ ha) (mul_le_mul_of_nonneg_left ht₂ hb)

/-- Every sublevel of h is convex; the minimizing splits justify the
non-strict inequality at the boundary. -/
lemma infimal_sublevel_convex [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) (α : ℝ) :
    Convex ℝ {f : E →L[ℝ] ℝ | infimalConvolution E φ ψ f ≤ (α : EReal)} := by
  intro f₁ h₁ f₂ h₂ a b ha hb hab
  obtain ⟨g₁, hg₁⟩ := exists_minimizing_split φ ψ hp hq hcone f₁
  obtain ⟨g₂, hg₂⟩ := exists_minimizing_split φ ψ hp hq hcone f₂
  have hcost := split_cost_convex_bound φ ψ hp hq f₁ f₂ g₁ g₂ α α a b
    (hg₁.le.trans h₁) (hg₂.le.trans h₂) ha hb hab
  have heq : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  rw [heq] at hcost
  exact (iInf_le _ (a • g₁ + b • g₂)).trans hcost

/-- On each bounded total-dual ball, the value sublevel is the compact
projection of a closed subset of two Alaoglu balls. -/
lemma infimal_sublevel_ball_isClosed [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) (α R : ℝ) (hR : 0 ≤ R) :
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue ℝ E)
      ({f : E →L[ℝ] ℝ | infimalConvolution E φ ψ f ≤ (α : EReal)} ∩
        {f : E →L[ℝ] ℝ | ‖f‖ ≤ R}) := by
  let B : Set (E →L[ℝ] ℝ) := {f | ‖f‖ ≤ R}
  have hB : Bornology.IsBounded B :=
    isBounded_iff_forall_norm_le.mpr ⟨R, fun _ h => h⟩
  have hb := UniformSplitBounds.bounded_split_sublevel φ ψ hcone B hB α
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  let : TopologicalSpace (E →L[ℝ] ℝ) := C12WeakStar.Spec.WeakStarTopologyValue ℝ E
  have he : IsEmbedding (StrongDual.toWeakDual : (E →L[ℝ] ℝ) → WeakDual ℝ E) :=
    ⟨⟨C12WeakStar.weakStarTopology_native ℝ E⟩, StrongDual.toWeakDual.injective⟩
  let : T2Space (E →L[ℝ] ℝ) := he.t2Space
  have hCB : IsCompact B := by
    simpa only [B, sub_zero] using C13Alaoglu.weakStar_closedBall_isCompact ℝ E 0 R hR
  have hCM : IsCompact {g : E →L[ℝ] ℝ | ‖g‖ ≤ max M 0} := by
    simpa only [sub_zero] using C13Alaoglu.weakStar_closedBall_isCompact
      ℝ E 0 (max M 0) (le_max_right M 0)
  have hs : IsClosed {p : (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) |
      conjugateSplitCost E φ ψ p.1 p.2 ≤ (α : EReal)} :=
    split_sublevel_isClosed φ ψ hp hq Prod.fst Prod.snd
      (fun x => (KreinSmulian.weakStar_evaluation_continuous x).comp continuous_fst)
      (fun x => (KreinSmulian.weakStar_evaluation_continuous x).comp continuous_snd) α
  have hc := (hCB.prod hCM).inter_right hs
  have himage : Prod.fst ''
      ((B ×ˢ {g : E →L[ℝ] ℝ | ‖g‖ ≤ max M 0}) ∩
        {p | conjugateSplitCost E φ ψ p.1 p.2 ≤ (α : EReal)}) =
      {f : E →L[ℝ] ℝ | infimalConvolution E φ ψ f ≤ (α : EReal)} ∩ B := by
    ext f
    constructor
    · rintro ⟨⟨k, g⟩, ⟨⟨hk, _⟩, hcost⟩, rfl⟩
      exact ⟨(iInf_le (conjugateSplitCost E φ ψ k) g).trans hcost, hk⟩
    · rintro ⟨hf, hfB⟩
      obtain ⟨g, hg⟩ := exists_minimizing_split φ ψ hp hq hcone f
      have hcost := hg.le.trans hf
      have hgb : ‖g‖ ≤ max M 0 :=
        (hM g ⟨f, hfB, hcost⟩).trans (le_max_left M 0)
      exact ⟨(f, g), ⟨⟨hfB, hgb⟩, hcost⟩, rfl⟩
  rw [← himage]
  exact (hc.image continuous_fst).isClosed

/-- Krein–Šmulian applied to the convex real sublevels gives weak-star lsc
of the full value function. This is equivalent to the epigraph formulation. -/
theorem weakStar_lower_semicontinuity : Spec.WeakStarLowerSemicontinuity := by
  intro E _ _ _ φ ψ h α
  have hc := h.2.2.2.2.2.2.2
  apply (KreinSmulian.convex_closed_criterion ℝ E _
    (infimal_sublevel_convex φ ψ h.1 h.2.1 hc α)).mpr
  intro R hR
  exact infimal_sublevel_ball_isClosed φ ψ h.1 h.2.1 hc α R hR.le

/-- An affine minorant makes the conjugate finite somewhere. -/
lemma exists_finite_conjugate (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ) :
    ∃ (f : E →L[ℝ] ℝ) (r : ℝ), C06Conjugates.convexConjugate E φ f = (r : EReal) := by
  obtain ⟨f, c, hm⟩ := FenchelMoreauLcs.exists_continuous_affine_minorant φ hp hc hl
  have hbound : C06Conjugates.convexConjugate E φ f ≤ ((-c : ℝ) : EReal) := by
    apply (FenchelMoreauLcs.convexConjugate_le_real_iff φ f _).mpr
    intro x r hr
    have hx : f x + c ≤ r := WithTop.coe_le_coe.mp (hr ▸ hm x)
    linarith
  have hnt := ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound
  have hnb := C06Conjugates.convexConjugate_ne_bot E φ hp f
  exact ⟨f, _, (EReal.coe_toReal hnt hnb).symm⟩

/-- Discarding bottom in the codomain does not change any conjugate value. -/
def conjugateAsWithTop (φ : ExtendedFunction E) (hp : Proper E φ) :
    ExtendedFunction (E →L[ℝ] ℝ) := fun f =>
  (C06Conjugates.convexConjugate E φ f).unbot
    (C06Conjugates.convexConjugate_ne_bot E φ hp f)

@[simp]
lemma coe_conjugateAsWithTop (φ : ExtendedFunction E) (hp : Proper E φ)
    (f : E →L[ℝ] ℝ) :
    C06Conjugates.extendedRealValue (conjugateAsWithTop φ hp f) =
      C06Conjugates.convexConjugate E φ f := WithBot.coe_unbot _ _

lemma conjugateAsWithTop_proper (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ) :
    Proper (E →L[ℝ] ℝ) (conjugateAsWithTop φ hp) := by
  obtain ⟨f, r, hr⟩ := exists_finite_conjugate φ hp hc hl
  apply (proper_iff_finite_value _ _).mpr
  exact ⟨f, r, (WithBot.unbot_eq_iff _).mpr hr⟩

lemma conjugateAsWithTop_conjugate (φ : ExtendedFunction E) (hp : Proper E φ) (x : E) :
    C06Conjugates.convexConjugate (E →L[ℝ] ℝ) (conjugateAsWithTop φ hp)
      (ContinuousLinearMap.apply ℝ ℝ x) = C06Conjugates.convexBiconjugate E φ x := by
  unfold C06Conjugates.convexConjugate C06Conjugates.convexBiconjugate
  simp only [coe_conjugateAsWithTop]
  rfl

/-- Applying the affine-half-space calculation a second time, now to the
conjugates, identifies every evaluation minorant of h with a primal test. -/
lemma evaluation_minorant_primal_bound (φ ψ : ExtendedFunction E)
    (hp : Proper E φ) (hq : Proper E ψ)
    (hc : ExtendedConvex E φ) (hd : ExtendedConvex E ψ)
    (hl : LowerSemicontinuous E φ) (hk : LowerSemicontinuous E ψ)
    (x : E) (c : ℝ)
    (hm : ∀ f g : E →L[ℝ] ℝ,
      ((f x + c : ℝ) : EReal) ≤ conjugateSplitCost E φ ψ f g) :
    φ x + ψ x ≤ ((-c : ℝ) : WithTop ℝ) := by
  let J : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ x
  have hb : conjugateSplitCost (E →L[ℝ] ℝ)
      (conjugateAsWithTop φ hp) (conjugateAsWithTop ψ hq) (J + J) J ≤
      ((-c : ℝ) : EReal) := by
    apply (split_cost_le_iff _ _ (conjugateAsWithTop_proper φ hp hc hl)
      (conjugateAsWithTop_proper ψ hq hd hk) _ _ _).mpr
    intro a b r s ha hb
    have hA : C06Conjugates.convexConjugate E φ a = (r : EReal) :=
      (WithBot.unbot_eq_iff _).mp ha
    have hB : C06Conjugates.convexConjugate E ψ b = (s : EReal) :=
      (WithBot.unbot_eq_iff _).mp hb
    have hh := hm (a + b) b
    simp only [conjugateSplitCost, add_sub_cancel_right, hA, hB, ← EReal.coe_add,
      EReal.coe_le_coe_iff, add_apply] at hh
    have he : a x - r + (b x - s) ≤ -c := by linarith
    simpa only [J, ContinuousLinearMap.apply_apply, add_sub_cancel_right] using he
  unfold conjugateSplitCost at hb
  rw [add_sub_cancel_right] at hb
  change C06Conjugates.convexConjugate _ (conjugateAsWithTop φ hp)
    (ContinuousLinearMap.apply ℝ ℝ x) +
    C06Conjugates.convexConjugate _ (conjugateAsWithTop ψ hq)
      (ContinuousLinearMap.apply ℝ ℝ x) ≤ _ at hb
  have hφ : C06Conjugates.convexBiconjugate E φ x =
      C06Conjugates.extendedRealValue (φ x) := FenchelMoreauLcs.fenchel_moreau E φ hp hc hl x
  have hψ : C06Conjugates.convexBiconjugate E ψ x =
      C06Conjugates.extendedRealValue (ψ x) := FenchelMoreauLcs.fenchel_moreau E ψ hq hd hk x
  rw [conjugateAsWithTop_conjugate, conjugateAsWithTop_conjugate, hφ, hψ] at hb
  exact WithBot.coe_le_coe.mp hb

lemma infimal_ne_bot [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) (f : E →L[ℝ] ℝ) :
    infimalConvolution E φ ψ f ≠ ⊥ := by
  obtain ⟨g, hg⟩ := exists_minimizing_split φ ψ hp hq hcone f
  exact hg ▸ split_cost_ne_bot φ ψ hp hq f g

/-- The half-extended representative used only when applying LCS separation. -/
def infimalAsWithTop [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) : ExtendedFunction (WeakDual ℝ E) :=
  fun f => (infimalConvolution E φ ψ (WeakDual.toStrongDual f)).unbot
    (infimal_ne_bot φ ψ hp hq hcone _)

@[simp]
lemma coe_infimalAsWithTop [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) (f : WeakDual ℝ E) :
    C06Conjugates.extendedRealValue (infimalAsWithTop φ ψ hp hq hcone f) =
      infimalConvolution E φ ψ (WeakDual.toStrongDual f) := WithBot.coe_unbot _ _

lemma infimalAsWithTop_convex [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (hcone : domainDifferenceCone E φ ψ = univ) :
    ExtendedConvex (WeakDual ℝ E) (infimalAsWithTop φ ψ hp hq hcone) := by
  intro f k r s a b hf hk ha hb hab
  have hfr : infimalConvolution E φ ψ (WeakDual.toStrongDual f) = (r : EReal) :=
    (WithBot.unbot_eq_iff _).mp hf
  have hks : infimalConvolution E φ ψ (WeakDual.toStrongDual k) = (s : EReal) :=
    (WithBot.unbot_eq_iff _).mp hk
  obtain ⟨g₁, hg₁⟩ := exists_minimizing_split φ ψ hp hq hcone (WeakDual.toStrongDual f)
  obtain ⟨g₂, hg₂⟩ := exists_minimizing_split φ ψ hp hq hcone (WeakDual.toStrongDual k)
  have hc := split_cost_convex_bound φ ψ hp hq _ _ g₁ g₂ r s a b
    ((hg₁.trans hfr).le) ((hg₂.trans hks).le) ha hb hab
  apply (WithBot.unbot_le_iff _).mpr
  exact (iInf_le _ (a • g₁ + b • g₂)).trans hc

lemma infimalAsWithTop_lsc [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (h : Spec.Hypotheses E φ ψ) :
    LowerSemicontinuous (WeakDual ℝ E)
      (infimalAsWithTop φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2) := by
  intro r
  have hc := weakStar_lower_semicontinuity E φ ψ h r
  have htop := C12WeakStar.weakStarTopology_native ℝ E
  change _ = TopologicalSpace.induced id (instTopologicalSpaceWeakDual ℝ E) at htop
  rw [induced_id] at htop
  rw [htop] at hc
  change @IsClosed (WeakDual ℝ E) (instTopologicalSpaceWeakDual ℝ E)
    {f | infimalConvolution E φ ψ (WeakDual.toStrongDual f) ≤ (r : EReal)} at hc
  have heq : {f : WeakDual ℝ E | infimalAsWithTop φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 f ≤
      (r : WithTop ℝ)} =
      {f | infimalConvolution E φ ψ (WeakDual.toStrongDual f) ≤ (r : EReal)} := by
    ext f
    change (infimalConvolution E φ ψ (WeakDual.toStrongDual f)).unbot _ ≤
      (r : WithTop ℝ) ↔ infimalConvolution E φ ψ (WeakDual.toStrongDual f) ≤ (r : EReal)
    exact WithBot.unbot_le_iff _
  rw [heq]
  exact hc

lemma infimalAsWithTop_proper [CompleteSpace E]
    (φ ψ : ExtendedFunction E) (h : Spec.Hypotheses E φ ψ) :
    Proper (WeakDual ℝ E) (infimalAsWithTop φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2) := by
  obtain ⟨a, r, ha⟩ := exists_finite_conjugate φ h.1 h.2.2.1 h.2.2.2.2.1
  obtain ⟨b, s, hb⟩ := exists_finite_conjugate ψ h.2.1 h.2.2.2.1 h.2.2.2.2.2.1
  have hi : infimalConvolution E φ ψ (a + b) ≤ ((r + s : ℝ) : EReal) := by
    calc
      _ ≤ conjugateSplitCost E φ ψ (a + b) b := iInf_le _ b
      _ = _ := by simp only [conjugateSplitCost, add_sub_cancel_right, ha, hb, EReal.coe_add]
  refine ⟨StrongDual.toWeakDual (a + b), ?_⟩
  exact ne_top_of_le_ne_top WithTop.coe_ne_top ((WithBot.unbot_le_iff _).mpr hi)

/-- Weak duality, at every total functional including infinite values. -/
lemma sum_conjugate_le_infimal (φ ψ : ExtendedFunction E) (f : E →L[ℝ] ℝ) :
    C06Conjugates.convexConjugate E (fun x => φ x + ψ x) f ≤
      infimalConvolution E φ ψ f := by
  apply le_iInf
  intro g
  apply iSup_le
  intro x
  change (f x : EReal) - C06Conjugates.extendedRealValue (φ x + ψ x) ≤ _
  by_cases hx : φ x = ⊤
  · rw [hx, top_add]
    change (f x : EReal) - ⊤ ≤ _
    rw [EReal.sub_top]
    exact bot_le
  by_cases hy : ψ x = ⊤
  · rw [hy, add_top]
    change (f x : EReal) - ⊤ ≤ _
    rw [EReal.sub_top]
    exact bot_le
  obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
  obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x).mp hy
  have hh := split_test_le φ ψ f g x x r s hr hs
  convert hh using 1
  rw [hr, hs, ← WithTop.coe_add]
  change ((f x - (r + s) : ℝ) : EReal) = _
  congr 1
  simp only [sub_apply]
  ring

/-- Full Banach exactness from weak-star separation and Fenchel–Moreau. -/
theorem exact_conjugate_formula : Spec.ExactConjugateFormula := by
  intro E _ _ _ φ ψ h f
  have hcone := h.2.2.2.2.2.2.2
  apply le_antisymm _ (sum_conjugate_le_infimal φ ψ f)
  by_contra hn
  obtain ⟨t, hsum, hth⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  let H := infimalAsWithTop φ ψ h.1 h.2.1 hcone
  have htH : (t : WithTop ℝ) < H (StrongDual.toWeakDual f) := by
    apply (WithBot.lt_unbot_iff _).mpr
    exact hth
  let : LocallyConvexSpace ℝ (WeakDual ℝ E) :=
    (WeakDual.withSeminorms ℝ E).toLocallyConvexSpace
  obtain ⟨m, c, hm, htc⟩ := FenchelMoreauLcs.continuous_affine_minorant_above H
    (infimalAsWithTop_proper φ ψ h) (infimalAsWithTop_convex φ ψ h.1 h.2.1 hcone)
    (infimalAsWithTop_lsc φ ψ h) (StrongDual.toWeakDual f) t htH
  obtain ⟨x, hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℝ E) m
  have heval (k : WeakDual ℝ E) : m k = k x := by
    exact congrArg (fun L : WeakDual ℝ E →L[ℝ] ℝ => L k) hx.symm
  have hminor : ∀ k g : E →L[ℝ] ℝ,
      ((k x + c : ℝ) : EReal) ≤ conjugateSplitCost E φ ψ k g := by
    intro k g
    have hh := hm (StrongDual.toWeakDual k)
    have hh' : ((k x + c : ℝ) : EReal) ≤ infimalConvolution E φ ψ k := by
      have he : ((m (StrongDual.toWeakDual k) + c : ℝ) : EReal) ≤
          C06Conjugates.extendedRealValue (H (StrongDual.toWeakDual k)) :=
        WithBot.coe_le_coe.mpr hh
      change ((m (StrongDual.toWeakDual k) + c : ℝ) : EReal) ≤
        C06Conjugates.extendedRealValue (infimalAsWithTop φ ψ h.1 h.2.1 hcone
          (StrongDual.toWeakDual k)) at he
      rw [coe_infimalAsWithTop] at he
      simpa only [heval, StrongDual.toWeakDual_apply, StrongDual.toStrongDual_toWeakDual] using he
    exact hh'.trans (iInf_le _ g)
  have hprim := evaluation_minorant_primal_bound φ ψ h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 x c hminor
  obtain ⟨u, hu, hub⟩ := WithTop.le_coe_iff.mp hprim
  have htest : ((f x + c : ℝ) : EReal) ≤
      C06Conjugates.convexConjugate E (fun y => φ y + ψ y) f := by
    calc
      _ ≤ ((f x - u : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
      _ = (f x : EReal) - C06Conjugates.extendedRealValue (φ x + ψ x) := by rw [hu]; rfl
      _ ≤ _ := le_iSup (fun y => (f y : EReal) -
        C06Conjugates.extendedRealValue (φ y + ψ y)) x
  rw [heval] at htc
  exact (not_lt_of_ge htest) (hsum.trans (EReal.coe_lt_coe_iff.mpr htc))

/-- Properness includes exclusion of −∞ at every total functional. -/
theorem proper_infimal_convolution : Spec.ProperInfimalConvolution := by
  intro E _ _ _ φ ψ h
  refine ⟨infimal_ne_bot φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2, ?_⟩
  obtain ⟨f, r, hr⟩ := (proper_iff_finite_value _ _).mp (infimalAsWithTop_proper φ ψ h)
  exact ⟨WeakDual.toStrongDual f, r, (WithBot.unbot_eq_iff _).mp hr⟩

/-- Exactness gives the domain sum without taking either closure. -/
theorem exact_domain_sum : Spec.ExactDomainSum := by
  intro E _ _ _ φ ψ h f
  change C06Conjugates.convexConjugate E (fun x => φ x + ψ x) f < ⊤ ↔
    ∃ a b : E →L[ℝ] ℝ, f = a + b ∧
      C06Conjugates.convexConjugate E φ a < ⊤ ∧
      C06Conjugates.convexConjugate E ψ b < ⊤
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := exists_minimizing_split φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 f
    have hcost : conjugateSplitCost E φ ψ f g < ⊤ := by
      rw [hg]
      exact (exact_conjugate_formula E φ ψ h f).le.trans_lt hf
    have hfinite := (EReal.add_ne_top_iff_ne_top₂
      (C06Conjugates.convexConjugate_ne_bot E φ h.1 (f - g))
      (C06Conjugates.convexConjugate_ne_bot E ψ h.2.1 g)).mp hcost.ne
    exact ⟨f - g, g, (sub_add_cancel f g).symm,
      lt_top_iff_ne_top.mpr hfinite.1, lt_top_iff_ne_top.mpr hfinite.2⟩
  · rintro ⟨a, b, rfl, ha, hb⟩
    have hcost : conjugateSplitCost E φ ψ (a + b) b < ⊤ := by
      unfold conjugateSplitCost
      rw [add_sub_cancel_right]
      exact lt_top_iff_ne_top.mpr (EReal.add_ne_top ha.ne hb.ne)
    exact (sum_conjugate_le_infimal φ ψ (a + b)).trans_lt
      ((iInf_le (conjugateSplitCost E φ ψ (a + b)) b).trans_lt hcost)

/-- Negation interchanges the full extended infimum and supremum. -/
lemma ereal_neg_iInf {I : Sort*} (F : I → EReal) :
    -(⨅ i, F i) = ⨆ i, -F i := EReal.negOrderIso.map_iInf F

lemma conjugate_zero (φ : ExtendedFunction E) :
    C06Conjugates.convexConjugate E φ (0 : E →L[ℝ] ℝ) =
      -(⨅ x : E, C06Conjugates.extendedRealValue (φ x)) := by
  change (⨆ x : E, (0 : EReal) - C06Conjugates.extendedRealValue (φ x)) = _
  simp only [zero_sub]
  exact (ereal_neg_iInf _).symm

/-- Negating the cost causes no indeterminate infinity arithmetic because
both conjugates are never bottom. -/
lemma neg_split_cost_zero (φ ψ : ExtendedFunction E) (hp : Proper E φ) (hq : Proper E ψ)
    (g : E →L[ℝ] ℝ) :
    -conjugateSplitCost E φ ψ 0 g =
      -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g := by
  unfold conjugateSplitCost
  rw [zero_sub]
  exact EReal.neg_add (.inl (C06Conjugates.convexConjugate_ne_bot E φ hp (-g)))
    (.inr (C06Conjugates.convexConjugate_ne_bot E ψ hq g))

/-- At f=0, exactness gives the complete extended-real primal–dual
identity, and finite-value attainment gives a maximizing dual functional. -/
theorem primal_dual_identity : Spec.PrimalDualIdentity := by
  intro E _ _ _ φ ψ h
  let p := ⨅ x : E, C06Conjugates.extendedRealValue (φ x + ψ x)
  have hzero : infimalConvolution E φ ψ (0 : E →L[ℝ] ℝ) = -p := by
    exact (exact_conjugate_formula E φ ψ h 0).trans (conjugate_zero _)
  have hdual : (⨆ g : E →L[ℝ] ℝ,
      -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g) = p := by
    calc
      _ = ⨆ g : E →L[ℝ] ℝ, -conjugateSplitCost E φ ψ 0 g := by
        congr 1
        funext g
        exact (neg_split_cost_zero φ ψ h.1 h.2.1 g).symm
      _ = -infimalConvolution E φ ψ 0 := (ereal_neg_iInf _).symm
      _ = p := by rw [hzero, neg_neg]
  refine ⟨?_, hdual.symm, ?_⟩
  · obtain ⟨x, hx, hy⟩ := h.2.2.2.2.2.2.1
    obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
    obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x).mp hy
    have hi : p ≤ ((r + s : ℝ) : EReal) := by
      calc
        _ ≤ C06Conjugates.extendedRealValue (φ x + ψ x) := iInf_le _ x
        _ = _ := by rw [hr, hs, ← WithTop.coe_add]; rfl
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hi
  · intro r hr
    obtain ⟨g, hg⟩ := exists_minimizing_split φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 0
    refine ⟨g, ?_⟩
    change -C06Conjugates.convexConjugate E φ (-g) - C06Conjugates.convexConjugate E ψ g = _
    rw [← neg_split_cost_zero φ ψ h.1 h.2.1 g, hg, hzero, neg_neg]
    exact hr

/-- The real epigraph of the original value function is convex. -/
theorem convex_infimal_epigraph : Spec.ConvexInfimalEpigraph := by
  intro E _ _ _ φ ψ h
  rintro ⟨f, t⟩ ht ⟨k, u⟩ hu a b ha hb hab
  obtain ⟨g₁, hg₁⟩ := exists_minimizing_split φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 f
  obtain ⟨g₂, hg₂⟩ := exists_minimizing_split φ ψ h.1 h.2.1 h.2.2.2.2.2.2.2 k
  have hc := split_cost_convex_bound φ ψ h.1 h.2.1 f k g₁ g₂ t u a b
    (hg₁.le.trans ht) (hg₂.le.trans hu) ha hb hab
  exact (iInf_le (conjugateSplitCost E φ ψ (a • f + b • k)) (a • g₁ + b • g₂)).trans hc

end ExpandedFA.InfimalConvolution.BanachFullConeExactness
