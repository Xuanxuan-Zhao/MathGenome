import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ConvexOperations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set
universe u v w
namespace VariationalNotes.ConvexAnalysis
namespace Operations

def perspective {X : Type u} [AddCommGroup X] [Module ℝ X]
    (f : X → WithTop ℝ) (p : X × ℝ) : WithTop ℝ := Specs.Operations.perspective f p
def indicator {X : Type u} (C : Set X) (x : X) : WithTop ℝ :=
  Specs.Operations.indicator C x
def IsInfProjection {X : Type u} {Y : Type v}
    (F : X × Y → WithTop ℝ) (v : X → WithTop ℝ) : Prop :=
  Specs.Operations.IsInfProjection F v
def hyperbolaSet : Set (ℝ × ℝ) := Specs.Operations.hyperbolaSet

private theorem weight_mono {a : ℝ} (ha : 0 ≤ a) {r s : WithTop ℝ} (h : r ≤ s) :
    Specs.weightedValue a r ≤ Specs.weightedValue a s := by
  rcases eq_or_lt_of_le ha with ha | ha
  · subst a; simp [Specs.weightedValue]
  · exact (WithTop.mul_right_strictMono (WithTop.coe_pos.mpr ha)
      WithTop.coe_ne_top).monotone h

private def weightHom (a : ℝ) : WithTop ℝ →+ WithTop ℝ where
  toFun := Specs.weightedValue a
  map_zero' := mul_zero _
  map_add' r s := by
    by_cases ha : a = 0
    · subst a; simp [Specs.weightedValue]
    · induction r using WithTop.recTopCoe <;>
        induction s using WithTop.recTopCoe <;>
        simp [Specs.weightedValue, WithTop.mul_top, ha, ← WithTop.coe_mul,
          ← WithTop.coe_add, mul_add]

private theorem weight_sum {ι : Type v} (a : ℝ) (I : Finset ι) (r : ι → WithTop ℝ) :
    Specs.weightedValue a (∑ i ∈ I, r i) = ∑ i ∈ I, Specs.weightedValue a (r i) :=
  map_sum (weightHom a) r I

private theorem weight_add (a : ℝ) (r s : WithTop ℝ) :
    Specs.weightedValue a (r+s) = Specs.weightedValue a r + Specs.weightedValue a s :=
  (weightHom a).map_add r s

/-- The two-point inequality with the manuscript's zero-times-infinity convention. -/
theorem convex_inequality {X : Type u} [AddCommGroup X] [Module ℝ X]
    {f : X → WithTop ℝ} (hf : Specs.IsConvex f) (x y : X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    f (a • x + b • y) ≤ Specs.weightedValue a (f x) + Specs.weightedValue b (f y) := by
  by_cases ha0 : a = 0
  · subst a
    have : b = 1 := by linarith
    subst b
    simp [Specs.weightedValue]
  by_cases hb0 : b = 0
  · subst b
    have : a = 1 := by linarith
    subst a
    simp [Specs.weightedValue]
  by_cases hx : f x = ⊤
  · rw [hx, weight_conventions.2.1 a (lt_of_le_of_ne ha (Ne.symm ha0)), top_add]
    exact le_top
  by_cases hy : f y = ⊤
  · rw [hy, weight_conventions.2.1 b (lt_of_le_of_ne hb (Ne.symm hb0)), add_top]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [← hr, ← hs]
  exact (convex_iff_twoPoint f).mp hf x y r s hr.symm hs.symm a b ha hb hab

theorem convex_of_inequality {X : Type u} [AddCommGroup X] [Module ℝ X]
    {f : X → WithTop ℝ}
    (h : ∀ (x y : X) (a b : ℝ), 0 ≤ a → 0 ≤ b → a+b=1 →
      f (a • x + b • y) ≤ Specs.weightedValue a (f x) + Specs.weightedValue b (f y)) :
    Specs.IsConvex f := by
  apply (convex_iff_twoPoint f).mpr
  intro x y r s hx hy a b ha hb hab
  simpa only [hx, hy, Specs.weightedValue, ← WithTop.coe_mul, ← WithTop.coe_add]
    using h x y a b ha hb hab

theorem convex_positive_sum : Specs.Operations.convex_positive_sum.{u,v} := by
  intro X ι _ _ I w f hw hf
  apply convex_of_inequality
  intro x y a b ha hb hab
  calc
    _ ≤ ∑ i ∈ I, Specs.weightedValue (w i)
        (Specs.weightedValue a (f i x) + Specs.weightedValue b (f i y)) :=
      Finset.sum_le_sum (fun i hi => weight_mono (hw i hi).le
        (convex_inequality (hf i hi) x y ha hb hab))
    _ = _ := by
      simp only [weight_add, Finset.sum_add_distrib, weight_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      all_goals dsimp [Specs.weightedValue]; ac_rfl

theorem convex_supremum : Specs.Operations.convex_supremum.{u,v} := by
  intro X ι _ _ f g hf hg p hp q hq a b ha hb hab
  apply (hg _).2
  rintro _ ⟨i, rfl⟩
  exact hf i ((hg p.1).1 (mem_range_self i) |>.trans hp)
    ((hg q.1).1 (mem_range_self i) |>.trans hq) ha hb hab

theorem convex_ereal_supremum : Specs.Operations.convex_ereal_supremum.{u,v} := by
  intro X ι _ _ f hf p hp q hq a b ha hb hab
  change (⨆ i, Specs.toEReal (f i (a • p+b • q).1)) ≤ ((a • p+b • q).2 : EReal)
  apply iSup_le
  intro i
  apply WithBot.coe_le_coe.mpr
  have hp' : Specs.toEReal (f i p.1) ≤ (p.2 : EReal) := (le_iSup (fun i => Specs.toEReal (f i p.1)) i).trans hp
  have hq' : Specs.toEReal (f i q.1) ≤ (q.2 : EReal) := (le_iSup (fun i => Specs.toEReal (f i q.1)) i).trans hq
  exact hf i (WithBot.coe_le_coe.mp hp') (WithBot.coe_le_coe.mp hq') ha hb hab

theorem convex_affine_pullback : Specs.Operations.convex_affine_pullback.{u,v} := by
  intro X Y _ _ _ _ f A hf p hp q hq a b ha hb hab
  have h := hf (show (A p.1,p.2) ∈ Specs.epigraph f from hp)
    (show (A q.1,q.2) ∈ Specs.epigraph f from hq) ha hb hab
  change f (A (a • p.1 + b • q.1)) ≤ _
  have hA : A (a • p.1 + b • q.1) = a • A p.1 + b • A q.1 := by
    rw [A.decomp]
    simp only [Pi.add_apply, map_add, map_smul, smul_add]
    have hc : a • A 0 + b • A 0 = A 0 := by rw [← add_smul, hab, one_smul]
    calc
      _ = (a • A.linear p.1 + b • A.linear q.1) + (a • A 0 + b • A 0) :=
        congrArg (fun z => (a • A.linear p.1 + b • A.linear q.1) + z) hc.symm
      _ = _ := by abel
  rw [hA]
  exact h

theorem lsc_supremum : Specs.Operations.lsc_supremum.{u,v} := by
  intro X ι _ f g hf hg a
  have heq : {x | (a : WithTop ℝ) < g x} = ⋃ i, {x | (a : WithTop ℝ) < f i x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    exact (lt_isLUB_iff (hg x)).trans (by simp)
  rw [heq]
  exact isOpen_iUnion (fun i => hf i a)

theorem lsc_ereal_supremum : Specs.Operations.lsc_ereal_supremum.{u,v} := by
  intro X ι _ f hf a
  have heq : {x | (a : EReal) < ⨆ i, Specs.toEReal (f i x)} =
      ⋃ i, {x | (a : WithTop ℝ) < f i x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, lt_iSup_iff]
    change (∃ i, ((a : WithTop ℝ) : WithBot (WithTop ℝ)) <
      (f i x : WithBot (WithTop ℝ))) ↔ _
    simp only [WithBot.coe_lt_coe]
  rw [heq]
  exact isOpen_iUnion (fun i => hf i a)

theorem lsc_continuous_affine_pullback :
    Specs.Operations.lsc_continuous_affine_pullback.{u,v} := by
  intro X Y _ _ _ _ _ _ f A hA hf a
  exact (hf a).preimage hA

private theorem lsc_ereal_iff {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ) :
    Specs.IsLowerSemicontinuous f ↔ LowerSemicontinuous (fun x => Specs.toEReal (f x)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  constructor
  · intro hf a
    induction a using EReal.rec with
    | bot =>
      have heq : (fun x => Specs.toEReal (f x)) ⁻¹' Ioi (⊥ : EReal) = univ := by
        ext x
        exact iff_true_intro (WithBot.bot_lt_coe (f x))
      rw [heq]
      exact isOpen_univ
    | top =>
      have heq : (fun x => Specs.toEReal (f x)) ⁻¹' Ioi (⊤ : EReal) = ∅ := by
        ext x; exact iff_false_intro (show ¬ (⊤ : EReal) < Specs.toEReal (f x) from not_top_lt)
      rw [heq]
      exact isOpen_empty
    | coe a =>
      change IsOpen {x | ((a : WithTop ℝ) : WithBot (WithTop ℝ)) < (f x : WithBot (WithTop ℝ))}
      simpa only [WithBot.coe_lt_coe] using hf a
  · intro hf a
    have h := hf (a : EReal)
    change IsOpen {x | ((a : WithTop ℝ) : WithBot (WithTop ℝ)) < (f x : WithBot (WithTop ℝ))} at h
    simpa only [WithBot.coe_lt_coe] using h

private theorem lsc_add {X : Type u} [TopologicalSpace X] {f g : X → WithTop ℝ}
    (hf : Specs.IsLowerSemicontinuous f) (hg : Specs.IsLowerSemicontinuous g) :
    Specs.IsLowerSemicontinuous (fun x => f x + g x) := by
  apply (lsc_ereal_iff _).mpr
  have hadd (r s : WithTop ℝ) : Specs.toEReal (r+s) = Specs.toEReal r + Specs.toEReal s :=
    toEReal_add r s
  simp only [hadd]
  exact ((lsc_ereal_iff f).mp hf).add' ((lsc_ereal_iff g).mp hg)
    (fun x => EReal.continuousAt_add (Or.inr (WithBot.coe_ne_bot))
      (Or.inl (WithBot.coe_ne_bot)))

private theorem lsc_weight {X : Type u} [TopologicalSpace X] {f : X → WithTop ℝ}
    (hf : Specs.IsLowerSemicontinuous f) {w : ℝ} (hw : 0 < w) :
    Specs.IsLowerSemicontinuous (fun x => Specs.weightedValue w (f x)) := by
  intro a
  have heq : {x | (a : WithTop ℝ) < Specs.weightedValue w (f x)} =
      {x | ((a/w : ℝ) : WithTop ℝ) < f x} := by
    ext x
    simp only [mem_ofPred_eq]
    induction f x using WithTop.recTopCoe with
    | top => simp [Specs.weightedValue, WithTop.mul_top, ne_of_gt hw]
    | coe r =>
      change ((a : WithTop ℝ) < ((w*r : ℝ) : WithTop ℝ)) ↔
        (((a/w : ℝ) : WithTop ℝ) < (r : WithTop ℝ))
      simp only [WithTop.coe_lt_coe]
      rw [div_lt_iff₀ hw, mul_comm]
  rw [heq]
  exact hf (a/w)

theorem lsc_positive_sum : Specs.Operations.lsc_positive_sum.{u,v} := by
  intro X ι _ I w f hw hf
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (lowerSemicontinuous_iff_native _).mpr lowerSemicontinuous_const
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact lsc_add
      (lsc_weight (hf i (Finset.mem_insert_self i I)) (hw i (Finset.mem_insert_self i I)))
      (ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem glb_ereal {ι : Type v} (f : ι → WithTop ℝ) (g : WithTop ℝ) :
    IsGLB (range f) g ↔ Specs.toEReal g = ⨅ i, Specs.toEReal (f i) := by
  constructor
  · intro h
    apply le_antisymm
    · exact le_iInf (fun i => WithBot.coe_le_coe.mpr (h.1 (mem_range_self i)))
    · generalize heq : (⨅ i, Specs.toEReal (f i)) = r
      induction r using EReal.rec with
      | bot => exact bot_le
      | top =>
        apply WithBot.coe_le_coe.mpr
        apply h.2
        rintro _ ⟨i, rfl⟩
        apply WithBot.coe_le_coe.mp
        change (⊤ : EReal) ≤ Specs.toEReal (f i)
        rw [← heq]
        exact iInf_le (fun i => Specs.toEReal (f i)) i
      | coe r =>
        apply WithBot.coe_le_coe.mpr
        apply h.2
        rintro _ ⟨i, rfl⟩
        apply WithBot.coe_le_coe.mp
        change (r : EReal) ≤ Specs.toEReal (f i)
        rw [← heq]
        exact iInf_le (fun i => Specs.toEReal (f i)) i
  · intro h
    constructor
    · rintro _ ⟨i, rfl⟩
      apply WithBot.coe_le_coe.mp
      change Specs.toEReal g ≤ Specs.toEReal (f i)
      rw [h]
      exact iInf_le (fun i => Specs.toEReal (f i)) i
    · intro r hr
      apply WithBot.coe_le_coe.mp
      change Specs.toEReal r ≤ Specs.toEReal g
      rw [h]
      exact le_iInf (fun i => WithBot.coe_le_coe.mpr (hr (mem_range_self i)))

theorem infProjection_iff_ereal : Specs.Operations.infProjection_iff_ereal.{u,v} := by
  intro X Y F v
  exact forall_congr' (fun x => glb_ereal (fun y => F (x,y)) (v x))

private theorem lub_ereal {ι : Type v} (f : ι → WithTop ℝ) (g : WithTop ℝ) :
    IsLUB (range f) g ↔ Specs.toEReal g = ⨆ i, Specs.toEReal (f i) := by
  constructor
  · intro h
    apply le_antisymm
    · generalize heq : (⨆ i, Specs.toEReal (f i)) = r
      induction r using EReal.rec with
      | top => exact le_top
      | bot =>
        obtain ⟨t, ht⟩ := exists_lt g
        obtain ⟨_, ⟨i, rfl⟩, _⟩ := (lt_isLUB_iff h).mp ht
        have hle := le_iSup (fun i => Specs.toEReal (f i)) i
        rw [heq] at hle
        exact False.elim (WithBot.not_coe_le_bot _ hle)
      | coe r =>
        apply WithBot.coe_le_coe.mpr
        apply h.2
        rintro _ ⟨i, rfl⟩
        apply WithBot.coe_le_coe.mp
        change Specs.toEReal (f i) ≤ (r : EReal)
        rw [← heq]
        exact le_iSup (fun i => Specs.toEReal (f i)) i
    · exact iSup_le (fun i => WithBot.coe_le_coe.mpr (h.1 (mem_range_self i)))
  · intro h
    constructor
    · rintro _ ⟨i, rfl⟩
      apply WithBot.coe_le_coe.mp
      change Specs.toEReal (f i) ≤ Specs.toEReal g
      rw [h]
      exact le_iSup (fun i => Specs.toEReal (f i)) i
    · intro r hr
      apply WithBot.coe_le_coe.mp
      change Specs.toEReal g ≤ Specs.toEReal r
      rw [h]
      exact iSup_le (fun i => WithBot.coe_le_coe.mpr (hr (mem_range_self i)))

theorem supremum_iff_ereal : Specs.Operations.supremum_iff_ereal.{u,v} := by
  intro X ι f g
  exact forall_congr' (fun x => lub_ereal (fun i => f i x) (g x))

/-- The epsilon approximation uses the actual greatest lower bound, so it does
not assume that the infimum is attained. -/
theorem convex_infProjection : Specs.Operations.convex_infProjection.{u,v} := by
  intro X Y _ _ _ _ F v hF hv _
  apply (convex_iff_twoPoint v).mpr
  intro x y r s hx hy a b ha hb hab
  apply WithTop.le_of_forall_lt_iff_le.mp
  intro c hc
  have hc' : a*r+b*s < c := WithTop.coe_lt_coe.mp hc
  let ε := (c-(a*r+b*s))/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hxε : v x < ((r+ε : ℝ) : WithTop ℝ) := by
    rw [hx]; exact WithTop.coe_lt_coe.mpr (by linarith)
  have hyε : v y < ((s+ε : ℝ) : WithTop ℝ) := by
    rw [hy]; exact WithTop.coe_lt_coe.mpr (by linarith)
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (isGLB_lt_iff (hv x)).mp hxε
  obtain ⟨_, ⟨v', rfl⟩, hv'⟩ := (isGLB_lt_iff (hv y)).mp hyε
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hu.ne_top
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv'.ne_top
  have hp' : p ≤ r+ε := by rw [← hp] at hu; exact (WithTop.coe_lt_coe.mp hu).le
  have hq' : q ≤ s+ε := by rw [← hq] at hv'; exact (WithTop.coe_lt_coe.mp hv').le
  calc
    v (a • x+b • y) ≤ F (a • (x,u)+b • (y,v')) :=
      (hv _).1 ⟨a • u+b • v', rfl⟩
    _ ≤ ((a*p+b*q : ℝ) : WithTop ℝ) :=
      (convex_iff_twoPoint F).mp hF (x,u) (y,v') p q hp.symm hq.symm a b ha hb hab
    _ ≤ ((a*(r+ε)+b*(s+ε) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (add_le_add (mul_le_mul_of_nonneg_left hp' ha)
        (mul_le_mul_of_nonneg_left hq' hb))
    _ ≤ (c : WithTop ℝ) := by
      apply WithTop.coe_le_coe.mpr
      have heq : a*(r+ε)+b*(s+ε) = a*r+b*s+(a+b)*ε := by ring
      rw [heq, hab, one_mul]
      dsimp [ε]
      linarith

private theorem perspective_bound {X : Type u} [AddCommGroup X] [Module ℝ X]
    (f : X → WithTop ℝ) (p : X × ℝ) (r : ℝ)
    (h : Specs.Operations.perspective f p ≤ (r : WithTop ℝ)) :
    0 < p.2 ∧ f (p.2⁻¹ • p.1) ≤ ((r/p.2 : ℝ) : WithTop ℝ) := by
  have ht : 0 < p.2 := by
    by_contra ht
    simp [Specs.Operations.perspective, ht] at h
  refine ⟨ht, ?_⟩
  have heq : Specs.weightedValue p.2 ((r/p.2 : ℝ) : WithTop ℝ) = (r : WithTop ℝ) := by
    change ((p.2*(r/p.2) : ℝ) : WithTop ℝ) = _
    rw [mul_div_cancel₀ _ (ne_of_gt ht)]
  apply (WithTop.mul_right_strictMono (WithTop.coe_pos.mpr ht) WithTop.coe_ne_top).le_iff_le.mp
  change Specs.weightedValue p.2 (f (p.2⁻¹ • p.1)) ≤
    Specs.weightedValue p.2 ((r/p.2 : ℝ) : WithTop ℝ)
  rw [heq]
  simpa only [Specs.Operations.perspective, ite_eq_left ht] using h

theorem convex_perspective : Specs.Operations.convex_perspective.{u} := by
  intro X _ _ f hf p hp q hq a b ha hb hab
  obtain ⟨hp0, hp'⟩ := perspective_bound f p.1 p.2 hp
  obtain ⟨hq0, hq'⟩ := perspective_bound f q.1 q.2 hq
  let t := a*p.1.2+b*q.1.2
  have ht : 0 < t := by
    rcases eq_or_lt_of_le ha with ha | ha
    · have hb1 : b = 1 := by linarith
      dsimp [t]; rw [← ha, hb1]; simpa using hq0
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hp0) (mul_nonneg hb hq0.le)
  have hn : a*p.1.2/t+b*q.1.2/t=1 := by
    rw [← add_div]; exact div_self (ne_of_gt ht)
  have hc := hf (show (p.1.2⁻¹ • p.1.1,p.2/p.1.2) ∈ Specs.epigraph f from hp')
    (show (q.1.2⁻¹ • q.1.1,q.2/q.1.2) ∈ Specs.epigraph f from hq')
    (div_nonneg (mul_nonneg ha hp0.le) ht.le)
    (div_nonneg (mul_nonneg hb hq0.le) ht.le) hn
  have hpoints : t⁻¹ • (a • p.1.1+b • q.1.1) =
      (a*p.1.2/t) • (p.1.2⁻¹ • p.1.1) + (b*q.1.2/t) • (q.1.2⁻¹ • q.1.1) := by
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  change Specs.Operations.perspective f (a • p.1+b • q.1) ≤
    ((a*p.2+b*q.2 : ℝ) : WithTop ℝ)
  change (if 0 < t then Specs.weightedValue t (f (t⁻¹ • (a • p.1.1+b • q.1.1))) else ⊤) ≤ _
  rw [ite_eq_left ht, hpoints]
  have h := weight_mono ht.le hc
  refine h.trans_eq ?_
  change ((t*((a*p.1.2/t)*(p.2/p.1.2)+(b*q.1.2/t)*(q.2/q.1.2)) : ℝ) : WithTop ℝ) = _
  congr 1
  field_simp

private theorem indicator_sublevel {X : Type u} (C : Set X) (a : ℝ) :
    Specs.sublevel (Specs.Operations.indicator C) a = if 0 ≤ a then C else ∅ := by
  classical
  ext x
  by_cases hx : x ∈ C <;> by_cases ha : 0 ≤ a <;>
    simp [Specs.sublevel, Specs.Operations.indicator, hx, ha,
      show (0 : WithTop ℝ) ≤ (a : WithTop ℝ) ↔ 0 ≤ a from WithTop.coe_le_coe]

private theorem indicator_convex {X : Type u} [AddCommGroup X] [Module ℝ X]
    {C : Set X} (hC : Convex ℝ C) : Specs.IsConvex (Specs.Operations.indicator C) := by
  apply (convex_iff_twoPoint _).mpr
  intro x y r s hx hy a b ha hb hab
  have hxC : x ∈ C := by
    by_contra hn
    simp [Specs.Operations.indicator, hn] at hx
  have hyC : y ∈ C := by
    by_contra hn
    simp [Specs.Operations.indicator, hn] at hy
  have hr : r = 0 := by simpa [Specs.Operations.indicator, hxC, eq_comm] using hx
  have hs : s = 0 := by simpa [Specs.Operations.indicator, hyC, eq_comm] using hy
  simp [Specs.Operations.indicator, hC hxC hyC ha hb hab, hr, hs]

private theorem indicator_lsc {X : Type u} [TopologicalSpace X]
    {C : Set X} (hC : IsClosed C) : Specs.IsLowerSemicontinuous (Specs.Operations.indicator C) := by
  apply (lowerSemicontinuous_iff_closed_sublevels _).mpr
  intro a
  rw [indicator_sublevel]
  split_ifs
  · exact hC
  · exact isClosed_empty

private theorem positive_ray_indicator_not_lscAt :
    ¬ LowerSemicontinuousAt (Specs.Operations.indicator (Ioi (0 : ℝ))) 0 := by
  intro h
  have hmem : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]; exact (show (0 : ℝ) ≤ 0 from le_refl _)
  have hfreq : ∃ᶠ y in nhds (0 : ℝ), Specs.Operations.indicator (Ioi (0 : ℝ)) y ≤ 0 :=
    (mem_closure_iff_frequently.mp hmem).mono (fun y hy => by
      simp [Specs.Operations.indicator, hy])
  have hle := h.frequently 0 hfreq
  simp [Specs.Operations.indicator] at hle

private theorem positive_ray_indicator_not_lsc :
    ¬ Specs.IsLowerSemicontinuous (Specs.Operations.indicator (Ioi (0 : ℝ))) := by
  intro h
  have hclosed := (lowerSemicontinuous_iff_closed_sublevels _).mp h 0
  rw [indicator_sublevel, ite_eq_left (le_refl (0 : ℝ))] at hclosed
  have hmem : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact (show (0 : ℝ) ≤ 0 from le_refl _)
  rw [hclosed.closure_eq] at hmem
  exact (lt_irrefl (0 : ℝ)) hmem

private theorem hyperbolaSet_description :
    Specs.Operations.hyperbolaSet = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 1 ≤ p.1*p.2} := by
  ext p
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx.le, (inv_pos.mpr hx).le.trans hy, ?_⟩
    have h := mul_le_mul_of_nonneg_left hy hx.le
    rwa [mul_inv_cancel₀ (ne_of_gt hx)] at h
  · rintro ⟨hx, hy, hxy⟩
    have hx' : 0 < p.1 := by
      rcases eq_or_lt_of_le hx with hx | hx
      · rw [← hx, zero_mul] at hxy; norm_num at hxy
      · exact hx
    refine ⟨hx', ?_⟩
    apply (mul_le_mul_iff_right₀ hx').mp
    simpa [inv_mul_cancel₀ (ne_of_gt hx'), mul_inv_cancel₀ (ne_of_gt hx'), mul_comm] using hxy

private theorem hyperbolaSet_closed : IsClosed Specs.Operations.hyperbolaSet := by
  rw [hyperbolaSet_description]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.mul continuous_snd)))

private theorem inv_convex_bound {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)⁻¹ ≤ a*x⁻¹+b*y⁻¹ := by
  have ht : 0 < a*x+b*y := by
    rcases eq_or_lt_of_le ha with ha | ha
    · have hb1 : b = 1 := by linarith
      rw [← ha, hb1]; simpa using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb hy.le)
  have hid : a*x⁻¹+b*y⁻¹-(a*x+b*y)⁻¹ = a*b*(x-y)^2/(x*y*(a*x+b*y)) := by
    have hb' : b = 1-a := by linarith
    rw [hb']
    have ht' : a*x+(1-a)*y ≠ 0 := by rw [← hb']; exact ne_of_gt ht
    field_simp [ne_of_gt hx, ne_of_gt hy, ht']
    ring
  have hnonneg : 0 ≤ a*b*(x-y)^2/(x*y*(a*x+b*y)) := by positivity
  linarith

private theorem hyperbolaSet_convex : Convex ℝ Specs.Operations.hyperbolaSet := by
  intro p hp q hq a b ha hb hab
  change 0 < a*p.1+b*q.1 ∧ (a*p.1+b*q.1)⁻¹ ≤ a*p.2+b*q.2
  have ht : 0 < a*p.1+b*q.1 := by
    rcases eq_or_lt_of_le ha with ha | ha
    · have hb1 : b = 1 := by linarith
      rw [← ha, hb1]; simpa using hq.1
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hp.1) (mul_nonneg hb hq.1.le)
  exact ⟨ht, (inv_convex_bound hp.1 hq.1 ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left hp.2 ha) (mul_le_mul_of_nonneg_left hq.2 hb))⟩

theorem perspective_zero_counterexample : Specs.Operations.perspective_zero_counterexample := by
  let f : ℝ → WithTop ℝ := fun _ => 0
  have hf : Specs.IsConvex f := convex_of_inequality (by
    intro x y a b ha hb hab
    simp [f, Specs.weightedValue])
  refine ⟨⟨0, by simp⟩, hf,
    (lowerSemicontinuous_iff_native f).mpr lowerSemicontinuous_const, ?_,
    convex_perspective f hf, ?_, ?_⟩
  · intro x t
    simp [Specs.Operations.perspective, Specs.weightedValue]
  · intro h
    apply positive_ray_indicator_not_lsc
    intro a
    have hpre := (h a).preimage (continuous_const.prodMk continuous_id :
      Continuous (fun t : ℝ => ((0 : ℝ),t)))
    simpa [Specs.Operations.perspective, Specs.Operations.indicator, Specs.weightedValue, f]
      using hpre
  · intro x h
    apply positive_ray_indicator_not_lscAt
    change LowerSemicontinuousAt (fun t : ℝ => Specs.Operations.indicator (Ioi (0 : ℝ)) t) 0
    have hpre := h.comp ((continuous_const.prodMk continuous_id :
      Continuous (fun t : ℝ => (x,t))).continuousAt)
    simpa [Function.comp_def, Specs.Operations.perspective,
      Specs.Operations.indicator, Specs.weightedValue, f] using hpre

private theorem hyperbolaSet_projection :
    Specs.Operations.IsInfProjection (Specs.Operations.indicator Specs.Operations.hyperbolaSet)
      (Specs.Operations.indicator (Ioi (0 : ℝ))) := by
  intro x
  by_cases hx : 0 < x
  · change IsGLB _ (if x ∈ Ioi (0 : ℝ) then 0 else ⊤)
    simp only [mem_Ioi, ite_eq_left hx]
    constructor
    · rintro _ ⟨y, rfl⟩
      dsimp [Specs.Operations.indicator]
      split_ifs <;> simp
    · intro r hr
      have h := hr (mem_range_self x⁻¹)
      simpa [Specs.Operations.indicator, Specs.Operations.hyperbolaSet, hx] using h
  · change IsGLB _ (if x ∈ Ioi (0 : ℝ) then 0 else ⊤)
    simp only [mem_Ioi, ite_eq_right hx]
    constructor
    · rintro _ ⟨y, rfl⟩
      simp [Specs.Operations.indicator, Specs.Operations.hyperbolaSet, hx]
    · intro r hr
      exact le_top

theorem infProjection_counterexample : Specs.Operations.infProjection_counterexample := by
  have hF : Specs.IsConvex (Specs.Operations.indicator Specs.Operations.hyperbolaSet) :=
    indicator_convex hyperbolaSet_convex
  have hproper : Specs.Proper (Specs.Operations.indicator Specs.Operations.hyperbolaSet) :=
    ⟨(1,1), by norm_num [Specs.Operations.indicator, Specs.Operations.hyperbolaSet]⟩
  have hvproper : Specs.Proper (Specs.Operations.indicator (Ioi (0 : ℝ))) :=
    ⟨1, by norm_num [Specs.Operations.indicator]⟩
  exact ⟨hyperbolaSet_closed, hyperbolaSet_convex, hproper, hF,
    indicator_lsc hyperbolaSet_closed, hyperbolaSet_projection, hvproper,
    convex_infProjection _ _ hF hyperbolaSet_projection hvproper,
    positive_ray_indicator_not_lsc, positive_ray_indicator_not_lscAt⟩

end Operations
end VariationalNotes.ConvexAnalysis
