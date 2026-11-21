import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.InvariantMeans
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.MarkovKakutani
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 400000

namespace ExpandedFA.PartV.InvariantMeans
open Set
attribute [local instance] Classical.propDecidable
open scoped Topology
universe u v

section Scalars
variable {𝕜 : Type v} [RCLike 𝕜]

lemma nonnegScalar_zero : NonnegScalar (0 : 𝕜) := by simp [NonnegScalar]
lemma nonnegScalar_one : NonnegScalar (1 : 𝕜) := by simp [NonnegScalar]
lemma NonnegScalar.add {z w : 𝕜} (hz : NonnegScalar z) (hw : NonnegScalar w) :
    NonnegScalar (z + w) := by
  exact ⟨by simpa using add_nonneg hz.1 hw.1, by simp [hz.2, hw.2]⟩
lemma NonnegScalar.smul {z : 𝕜} (hz : NonnegScalar z) {r : ℝ} (hr : 0 ≤ r) :
    NonnegScalar (r • z) := by
  exact ⟨by simpa [RCLike.smul_re] using mul_nonneg hr hz.1,
    by simp [RCLike.smul_im, hz.2]⟩
lemma isClosed_nonnegScalar : IsClosed {z : 𝕜 | NonnegScalar z} :=
  (isClosed_le continuous_const RCLike.continuous_re).inter
    (isClosed_eq RCLike.continuous_im continuous_const)
end Scalars

section MeanConstruction
variable (G : Type u) [CommGroup G] (𝕜 : Type v) [RCLike 𝕜]

/-- The closed scalar tests defining the state space. -/
def stateTests : Set (WeakDual 𝕜 (BoundedFunction G 𝕜)) :=
  {L | L (constant G 1) = 1 ∧
    ∀ f : BoundedFunction G 𝕜, (∀ x, NonnegScalar (f x)) → NonnegScalar (L f)}

def states : Set (WeakDual 𝕜 (BoundedFunction G 𝕜)) :=
  {L | ‖L.toStrongDual‖ ≤ 1} ∩ stateTests G 𝕜

lemma stateTests_closed : IsClosed (stateTests G 𝕜) := by
  have he : stateTests G 𝕜 =
      {L | L (constant G 1) = 1} ∩
        ⋂ (f : BoundedFunction G 𝕜), ⋂ (_ : ∀ x, NonnegScalar (f x)),
          {L | NonnegScalar (L f)} := by
    ext L
    simp [stateTests]
  rw [he]
  exact (isClosed_eq (WeakDual.eval_continuous _) continuous_const).inter
    (isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_nonnegScalar.preimage (WeakDual.eval_continuous f))

lemma states_compact : IsCompact (states G 𝕜) := by
  have hc := WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 (BoundedFunction G 𝕜)) 1
  have he : {L : WeakDual 𝕜 (BoundedFunction G 𝕜) | ‖L.toStrongDual‖ ≤ 1} =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 := by
    ext L
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [states, he]
  exact hc.inter_right (stateTests_closed G 𝕜)

lemma states_nonempty : (states G 𝕜).Nonempty := by
  letI : TopologicalSpace G := ⊥
  let ev : BoundedFunction G 𝕜 →L[𝕜] 𝕜 := BoundedContinuousFunction.evalCLM 𝕜 (1 : G)
  refine ⟨StrongDual.toWeakDual ev, ?_, ?_, ?_⟩
  · exact ev.opNorm_le_bound zero_le_one (fun f => by
      simpa [ev] using BoundedContinuousFunction.norm_coe_le_norm f (1 : G))
  · rfl
  · intro f hf
    exact hf 1

lemma states_convex : Convex ℝ (states G 𝕜) := by
  intro L hL M hM a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change ‖a • L.toStrongDual + b • M.toStrongDual‖ ≤ 1
    calc
      _ ≤ ‖a • L.toStrongDual‖ + ‖b • M.toStrongDual‖ := norm_add_le _ _
      _ = a * ‖L.toStrongDual‖ + b * ‖M.toStrongDual‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hL.1 ha) (mul_le_mul_of_nonneg_left hM.1 hb)
      _ = 1 := by linarith
  · change a • L (constant G 1) + b • M (constant G 1) = 1
    rw [hL.2.1, hM.2.1, ← add_smul, hab, one_smul]
  · intro f hf
    change NonnegScalar (a • L f + b • M f)
    exact ((hL.2.2 f hf).smul ha).add ((hM.2.2 f hf).smul hb)

noncomputable def translationCLM (g : G) :
    BoundedFunction G 𝕜 →L[𝕜] BoundedFunction G 𝕜 := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜
    ⟨fun x => g * x, continuous_of_discreteTopology⟩

noncomputable def translateDual (g : G) (L : WeakDual 𝕜 (BoundedFunction G 𝕜)) :
    WeakDual 𝕜 (BoundedFunction G 𝕜) :=
  StrongDual.toWeakDual (L.toStrongDual.comp (translationCLM G 𝕜 g))

lemma translateDual_apply (g : G) (L : WeakDual 𝕜 (BoundedFunction G 𝕜))
    (f : BoundedFunction G 𝕜) : translateDual G 𝕜 g L f = L (translate g f) := rfl

lemma translateDual_continuous (g : G) : Continuous (translateDual G 𝕜 g) :=
  WeakDual.continuous_of_continuous_eval fun f => WeakDual.eval_continuous (translate g f)

lemma translateDual_maps (g : G) : MapsTo (translateDual G 𝕜 g) (states G 𝕜) (states G 𝕜) := by
  letI : TopologicalSpace G := ⊥
  intro L hL
  refine ⟨?_, ?_, ?_⟩
  · change ‖(translateDual G 𝕜 g L).toStrongDual‖ ≤ 1
    apply (translateDual G 𝕜 g L).toStrongDual.opNorm_le_bound zero_le_one
    intro f
    calc
      ‖translateDual G 𝕜 g L f‖ ≤ ‖L.toStrongDual‖ * ‖translate g f‖ :=
        L.toStrongDual.le_opNorm _
      _ ≤ 1 * ‖translate g f‖ := mul_le_mul_of_nonneg_right hL.1 (norm_nonneg _)
      _ ≤ 1 * ‖f‖ := by
        exact mul_le_mul_of_nonneg_left
          (BoundedContinuousFunction.norm_compContinuous_le f _) zero_le_one
  · have he : translate g (constant G (1 : 𝕜)) = constant G 1 := by
      apply BoundedContinuousFunction.ext
      intro x
      rfl
    change L (translate g (constant G 1)) = 1
    rw [he]
    exact hL.2.1
  · intro f hf
    exact hL.2.2 _ (fun x => hf (g * x))

lemma translateDual_affine (g : G) :
    MarkovKakutaniSpec.AffineOn (states G 𝕜) (translateDual G 𝕜 g) := by
  intro L _ M _ a b _ _ _
  letI : TopologicalSpace G := ⊥
  apply DFunLike.ext
  intro f
  rfl

lemma translateDual_commute (g h : G) (L : WeakDual 𝕜 (BoundedFunction G 𝕜)) :
    translateDual G 𝕜 g (translateDual G 𝕜 h L) =
      translateDual G 𝕜 h (translateDual G 𝕜 g L) := by
  letI : TopologicalSpace G := ⊥
  apply DFunLike.ext
  intro f
  simp only [translateDual_apply]
  congr 1
  apply BoundedContinuousFunction.ext
  intro x
  change f (g * (h * x)) = f (h * (g * x))
  rw [mul_left_comm]

/-- The mean is a common fixed point of the transposed translations. -/
theorem abelian_invariant_mean : Spec.AbelianMean.{u, v} := by
  intro G _ 𝕜 _
  letI : TopologicalSpace G := ⊥
  have hne : (states G 𝕜).Nonempty := states_nonempty G 𝕜
  have hcompact : IsCompact (states G 𝕜) := states_compact G 𝕜
  have hconv : Convex ℝ (states G 𝕜) := states_convex G 𝕜
  have mk := ExpandedFA.PartV.markov_kakutani (WeakDual 𝕜 (BoundedFunction G 𝕜))
  have mk₁ := mk (states G 𝕜) hne hcompact hconv
  have mk₂ := mk₁ G (translateDual G 𝕜)
  have mk₃ := mk₂ (fun g => (translateDual_continuous G 𝕜 g).continuousOn)
  have mk₄ := mk₃ (translateDual_maps G 𝕜)
  have mk₅ := mk₄ (translateDual_affine G 𝕜)
  obtain ⟨L, hL, hfix⟩ := mk₅ (fun g h L _ => translateDual_commute G 𝕜 g h L)
  refine ⟨L.toStrongDual, hL.2.2, hL.2.1, ?_, le_antisymm hL.1 ?_⟩
  · intro g f
    exact congrArg (fun M : WeakDual 𝕜 (BoundedFunction G 𝕜) => M f) (hfix g)
  · have he := L.toStrongDual.le_opNorm (constant G (1 : 𝕜))
    simp only [WeakDual.toStrongDual_apply] at he
    rw [hL.2.1] at he
    have hn : ‖constant G (1 : 𝕜)‖ = 1 := by
      exact (BoundedContinuousFunction.norm_const_eq _).trans norm_one
    simpa [hn] using he
end MeanConstruction
section Probabilities
variable {G : Type u} [Group G] {𝕜 : Type v} [RCLike 𝕜]

@[simp] lemma indicator_apply (A : Set G) (x : G) :
    indicator G 𝕜 A x = if x ∈ A then 1 else 0 := by
  rfl

lemma indicator_nonneg (A : Set G) (x : G) : NonnegScalar (indicator G 𝕜 A x) := by
  classical
  rw [indicator_apply]
  split_ifs
  · exact nonnegScalar_one
  · exact nonnegScalar_zero

lemma indicator_empty : indicator G 𝕜 ∅ = 0 := by
  letI : TopologicalSpace G := ⊥
  ext x
  simp

lemma indicator_univ : indicator G 𝕜 univ = constant G 1 := by
  letI : TopologicalSpace G := ⊥
  ext x
  simp [constant]

lemma indicator_union (A B : Set G) (h : Disjoint A B) :
    indicator G 𝕜 (A ∪ B) = indicator G 𝕜 A + indicator G 𝕜 B := by
  classical
  letI : TopologicalSpace G := ⊥
  ext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
  · exact (Set.disjoint_left.mp h ha hb).elim
  all_goals simp [ha, hb]

lemma indicator_translate (g : G) (A : Set G) :
    indicator G 𝕜 ((fun x => g * x) '' A) = translate g⁻¹ (indicator G 𝕜 A) := by
  classical
  letI : TopologicalSpace G := ⊥
  ext x
  have hm : x ∈ (fun x => g * x) '' A ↔ g⁻¹ * x ∈ A := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨g⁻¹ * x, h, by simp⟩
  change (if x ∈ (fun x => g * x) '' A then (1 : 𝕜) else 0) =
    if g⁻¹ * x ∈ A then 1 else 0
  rw [hm]

/-- Evaluating the mean on indicators gives finite additivity on the power set. -/
theorem probability_from_mean : Spec.ProbabilityFromMean.{u, v} := by
  intro G _ 𝕜 _ L hL
  let m : Set G → ℝ := fun A => RCLike.re (L (indicator G 𝕜 A))
  refine ⟨m, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro A
    exact (hL.1 _ (indicator_nonneg A)).1
  · simp [m, indicator_empty]
  · simp [m, indicator_univ, hL.2.1]
  · intro A B h
    simp [m, indicator_union A B h, map_add]
  · intro g A
    simp only [m, indicator_translate, hL.2.2.1]
  · intro A
    apply RCLike.ext
    · simp [m]
    · simpa using (hL.1 _ (indicator_nonneg A)).2

theorem abelian_invariant_probability : Spec.AbelianProbability.{u} := by
  intro G _
  obtain ⟨L, hL⟩ := abelian_invariant_mean G ℝ
  obtain ⟨m, hm, _⟩ := probability_from_mean G ℝ L hL
  exact ⟨m, hm⟩
end Probabilities
section FreeGroupCounterexample
open FreeGroup

/-- The four initial-letter classes of nonidentity reduced words. -/
def initialClass (a b : Bool) : Set (FreeGroup Bool) :=
  {x | x.toWord.head? = some (a, b)}

lemma initialClass_disjoint {a b c d : Bool} (h : (a, b) ≠ (c, d)) :
    Disjoint (initialClass a b) (initialClass c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact h (Option.some.inj (hx.symm.trans hy))

lemma initialClass_not_one (a b : Bool) : (1 : FreeGroup Bool) ∉ initialClass a b := by
  simp [initialClass]

lemma initialClass_mul_iff (a : Bool) (x : FreeGroup Bool) :
    of a * x ∈ initialClass a true ↔ x ∉ initialClass a false := by
  change (of a * x).toWord.head? = some (a, true) ↔
    x.toWord.head? ≠ some (a, false)
  rw [show of a = mk [(a, true)] from rfl, toWord_mk_mul_eq]
  simp only [Bool.not_true]
  by_cases hx : x.toWord.head? = some (a, false)
  · rw [if_pos hx]
    have ht : x.toWord = (a, false) :: x.toWord.tail :=
      List.eq_cons_of_mem_head? hx
    have hn : x.toWord.tail.head? ≠ some (a, true) := by
      intro he
      have ht' : x.toWord.tail = (a, true) :: x.toWord.tail.tail :=
        List.eq_cons_of_mem_head? he
      exact FreeGroup.reduce.not (L₁ := x.toWord) (L₂ := []) (L₃ := x.toWord.tail.tail) (x := a) (b := false)
        (by simpa only [reduce_toWord, List.nil_append, Bool.not_false] using ht.trans (congrArg ((a, false) :: ·) ht'))
    exact iff_of_false hn (not_not_intro hx)
  · simp [hx]

lemma initialClass_image_complement (a : Bool) :
    (fun x : FreeGroup Bool => of a * x) '' (initialClass a false)ᶜ =
      initialClass a true := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (initialClass_mul_iff a y).mpr hy
  · intro hx
    refine ⟨(of a)⁻¹ * x, ?_, by simp⟩
    apply (initialClass_mul_iff a _).mp
    simpa using hx

lemma initialClass_partition :
    ({1} : Set (FreeGroup Bool)) ∪
      ((initialClass false true ∪ initialClass false false) ∪
        (initialClass true true ∪ initialClass true false)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  cases hw : x.toWord with
  | nil =>
    have hx : x = 1 := toWord_injective (by simpa using hw)
    simp [hx]
  | cons p t =>
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> simp [initialClass, hw]

/-- Singleton mass zero, shown using the disjoint translate of the nonnegative
powers of one free generator. Only finite additivity is used. -/
lemma freeGroup_singleton_mass_zero (m : Set (FreeGroup Bool) → ℝ)
    (hm : IsInvariantProbability m) : m {1} = 0 := by
  let a : FreeGroup Bool := of false
  let P : Set (FreeGroup Bool) := range (fun n : ℕ => a ^ n)
  let Q : Set (FreeGroup Bool) := (fun x => a * x) '' P
  have hQ : Q = range (fun n : ℕ => a ^ (n + 1)) := by
    ext x
    simp only [Q, P, mem_image, mem_range]
    constructor
    · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by simp [pow_succ']⟩
    · rintro ⟨n, rfl⟩
      exact ⟨a ^ n, ⟨n, rfl⟩, by simp [pow_succ']⟩
  have hdis : Disjoint ({1} : Set (FreeGroup Bool)) Q := by
    rw [Set.disjoint_singleton_left, hQ]
    rintro ⟨n, hn⟩
    have hlen := congrArg (fun x : FreeGroup Bool => x.toWord.length) hn
    simp [a] at hlen
  have he : ({1} : Set (FreeGroup Bool)) ∪ Q = P := by
    rw [hQ]
    ext x
    simp only [mem_union, mem_singleton_iff, P, mem_range]
    constructor
    · rintro (rfl | ⟨n, rfl⟩)
      · exact ⟨0, pow_zero _⟩
      · exact ⟨n + 1, rfl⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => simp
      | succ n => exact Or.inr ⟨n, rfl⟩
  have hadd := hm.2.2.2.1 {1} Q hdis
  have hinv := hm.2.2.2.2 a P
  change m Q = m P at hinv
  rw [he] at hadd
  linarith

/-- The two complementary cancellation identities assign mass one to each
pair of initial-letter classes; all four together have mass one. -/
theorem freeGroup_no_invariant_probability : Spec.FreeGroupNoProbability := by
  rintro ⟨m, hm⟩
  have hsingle := freeGroup_singleton_mass_zero m hm
  have hpair (a : Bool) : m (initialClass a true) + m (initialClass a false) = 1 := by
    have hcomp := hm.2.2.2.1 (initialClass a false)ᶜ (initialClass a false)
      (disjoint_compl_left)
    rw [Set.compl_union_self, hm.2.2.1] at hcomp
    have hi := hm.2.2.2.2 (of a) (initialClass a false)ᶜ
    rw [initialClass_image_complement] at hi
    linarith
  let A := initialClass false true ∪ initialClass false false
  let B := initialClass true true ∪ initialClass true false
  have hdA : Disjoint (initialClass false true) (initialClass false false) :=
    initialClass_disjoint (by decide)
  have hdB : Disjoint (initialClass true true) (initialClass true false) :=
    initialClass_disjoint (by decide)
  have hdAB : Disjoint A B := by
    exact (initialClass_disjoint (a := false) (b := true) (c := true) (d := true) (by decide)).union_right
      (initialClass_disjoint (by decide)) |>.union_left
        ((initialClass_disjoint (by decide)).union_right (initialClass_disjoint (by decide)))
  have hd1 : Disjoint ({1} : Set (FreeGroup Bool)) (A ∪ B) := by
    rw [Set.disjoint_singleton_left]
    simp [A, B, initialClass_not_one]
  have hA : m A = 1 := (hm.2.2.2.1 _ _ hdA).trans (hpair false)
  have hB : m B = 1 := (hm.2.2.2.1 _ _ hdB).trans (hpair true)
  have hab := hm.2.2.2.1 A B hdAB
  have htotal := hm.2.2.2.1 {1} (A ∪ B) hd1
  rw [show ({1} : Set (FreeGroup Bool)) ∪ (A ∪ B) = univ from initialClass_partition,
    hm.2.2.1, hsingle, hab, hA, hB] at htotal
  norm_num at htotal

theorem freeGroup_no_invariant_mean : Spec.FreeGroupNoMean.{v} := by
  intro 𝕜 _
  rintro ⟨L, hL⟩
  obtain ⟨m, hm, _⟩ := probability_from_mean (FreeGroup Bool) 𝕜 L hL
  exact freeGroup_no_invariant_probability ⟨m, hm⟩
end FreeGroupCounterexample
end ExpandedFA.PartV.InvariantMeans
