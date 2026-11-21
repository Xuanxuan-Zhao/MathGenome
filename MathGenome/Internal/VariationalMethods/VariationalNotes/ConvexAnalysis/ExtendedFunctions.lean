import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions

noncomputable section
open Set
universe u v
namespace VariationalNotes.ConvexAnalysis

def Proper {X : Type u} (f : X → WithTop ℝ) : Prop := Specs.Proper f
def effectiveDomain {X : Type u} (f : X → WithTop ℝ) : Set X := Specs.effectiveDomain f
def epigraph {X : Type u} (f : X → WithTop ℝ) : Set (X × ℝ) := Specs.epigraph f
def sublevel {X : Type u} (f : X → WithTop ℝ) (a : ℝ) : Set X := Specs.sublevel f a
def IsConvex {X : Type u} [AddCommGroup X] [Module ℝ X] (f : X → WithTop ℝ) : Prop := Specs.IsConvex f
def IsLowerSemicontinuous {X : Type u} [TopologicalSpace X] (f : X → WithTop ℝ) : Prop :=
  Specs.IsLowerSemicontinuous f
def weightedValue (a : ℝ) (r : WithTop ℝ) : WithTop ℝ := Specs.weightedValue a r
def toEReal (r : WithTop ℝ) : EReal := Specs.toEReal r

theorem mem_domain_iff : Specs.mem_domain_iff.{u} := by
  intro X f x
  change f x < ⊤ ↔ _
  simpa only [eq_comm] using (WithTop.lt_top_iff_ne_top.trans WithTop.ne_top_iff_exists :
    f x < ⊤ ↔ ∃ r : ℝ, (r : WithTop ℝ) = f x)

theorem proper_iff_exists_real : Specs.proper_iff_exists_real.{u} := by
  intro X f
  exact exists_congr (fun x => mem_domain_iff f x)

theorem weight_conventions : Specs.weight_conventions := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro r
    exact zero_mul r
  · intro a ha
    change (a : WithTop ℝ) * ⊤ = ⊤
    rw [WithTop.mul_top']
    simp [ne_of_gt ha]

theorem convex_iff_twoPoint : Specs.convex_iff_twoPoint.{u} := by
  intro X _ _ f
  constructor
  · intro h x y r s hx hy a b ha hb hab
    exact h (show (x,r) ∈ Specs.epigraph f from hx.le)
      (show (y,s) ∈ Specs.epigraph f from hy.le) ha hb hab
  · intro h p hp q hq a b ha hb hab
    have hp' : f p.1 ≤ (p.2 : WithTop ℝ) := hp
    have hq' : f q.1 ≤ (q.2 : WithTop ℝ) := hq
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hp')
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hq')
    have hpr : r ≤ p.2 := WithTop.coe_le_coe.mp (hr.le.trans hp')
    have hqs : s ≤ q.2 := WithTop.coe_le_coe.mp (hs.le.trans hq')
    exact (h p.1 q.1 r s hr.symm hs.symm a b ha hb hab).trans
      (WithTop.coe_le_coe.mpr (add_le_add (mul_le_mul_of_nonneg_left hpr ha)
        (mul_le_mul_of_nonneg_left hqs hb)))

theorem finite_jensen : Specs.finite_jensen.{u,v} := by
  intro X ι _ _ f hf I w p r hw hsum hbound
  have h := hf.sum_mem (z := fun i => (p i, r i)) hw hsum
    (fun i hi => hbound i hi)
  simpa only [Specs.epigraph, mem_ofPred_eq, Prod.fst_sum, Prod.snd_sum,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h

theorem jensen : Specs.jensen.{u,v} := by
  intro X ι _ _ f hf I w p hw hsum
  classical
  by_cases ht : ∃ i ∈ I, 0 < w i ∧ f (p i) = ⊤
  · obtain ⟨i, hi, hwi, hfi⟩ := ht
    have hterm : Specs.weightedValue (w i) (f (p i)) = ⊤ := by
      rw [hfi]
      exact weight_conventions.2.1 (w i) hwi
    rw [WithTop.sum_eq_top.mpr ⟨i, hi, hterm⟩]
    exact le_top
  · let J := I.filter (fun i => w i ≠ 0)
    let r : ι → ℝ := fun i => (f (p i)).untopD 0
    have hr (i : ι) (hi : i ∈ J) : f (p i) = (r i : WithTop ℝ) := by
      have hi' := Finset.mem_filter.mp hi
      have hpos : 0 < w i := lt_of_le_of_ne (hw i hi'.1) (Ne.symm hi'.2)
      have hfinite : f (p i) ≠ ⊤ := fun h => ht ⟨i, hi'.1, hpos, h⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hfinite
      dsimp [r]
      rw [← ha, WithTop.untopD_coe]
    have hsum' : (∑ i ∈ J, w i) = 1 := by
      dsimp [J]
      rw [Finset.sum_filter_ne_zero]
      exact hsum
    have hpoints : (∑ i ∈ J, w i • p i) = ∑ i ∈ I, w i • p i := by
      apply Finset.sum_filter_of_ne
      intro i _ hne hzero
      exact hne (by simp [hzero])
    have hvalues : (∑ i ∈ J, Specs.weightedValue (w i) (f (p i))) =
        ∑ i ∈ I, Specs.weightedValue (w i) (f (p i)) := by
      apply Finset.sum_filter_of_ne
      intro i _ hne hzero
      exact hne (by simp [Specs.weightedValue, hzero])
    have h := finite_jensen f hf J w p r
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hsum' (fun i hi => (hr i hi).le)
    rw [hpoints] at h
    rw [← hvalues]
    convert h using 1
    rw [WithTop.coe_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hr i hi]
    rfl

theorem lowerSemicontinuous_iff_native : Specs.lowerSemicontinuous_iff_native.{u} := by
  intro X _ f
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  constructor
  · intro h a
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe a => exact h a
  · intro h a
    exact h a

theorem lowerSemicontinuous_iff_closed_sublevels :
    Specs.lowerSemicontinuous_iff_closed_sublevels.{u} := by
  intro X _ f
  change (∀ a : ℝ, IsOpen {x | (a : WithTop ℝ) < f x}) ↔ _
  simp only [← isOpen_compl_iff, Specs.sublevel, compl_ofPred, not_le]

theorem lowerSemicontinuous_iff_closed_epigraph :
    Specs.lowerSemicontinuous_iff_closed_epigraph.{u} := by
  intro X _ f
  constructor
  · intro h
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hlt : (p.2 : WithTop ℝ) < f p.1 := lt_of_not_ge hp
    obtain ⟨r, hpr, hrf⟩ := WithTop.lt_iff_exists_coe_btwn.mp hlt
    have hpr' : p.2 < r := WithTop.coe_lt_coe.mp hpr
    have hopen := (h r).prod (isOpen_Iio : IsOpen (Iio r))
    have hp_mem : p ∈ ({x | (r : WithTop ℝ) < f x} ×ˢ Iio r) := ⟨hrf, hpr'⟩
    apply Filter.mem_of_superset (hopen.mem_nhds hp_mem)
    intro q hq hqepi
    have hqr : (q.2 : WithTop ℝ) < (r : WithTop ℝ) := WithTop.coe_lt_coe.mpr hq.2
    exact (hqr.trans hq.1).not_ge hqepi
  · intro h
    apply (lowerSemicontinuous_iff_closed_sublevels f).mpr
    intro a
    exact h.preimage (continuous_id.prodMk continuous_const)

theorem toEReal_conventions : Specs.toEReal_conventions := by
  refine ⟨fun _ => rfl, rfl, fun _ => WithBot.coe_ne_bot, ?_, ?_⟩
  · intro v
    change v ≠ (⊥ : WithBot (WithTop ℝ)) ↔ _
    exact WithBot.ne_bot_iff_exists
  · intro r s
    exact WithBot.coe_le_coe

theorem toEReal_add : Specs.toEReal_add := by
  intro r s
  induction r using WithTop.recTopCoe <;>
    induction s using WithTop.recTopCoe <;> rfl

theorem toEReal_weightedValue : Specs.toEReal_weightedValue := by
  intro a r ha
  induction r using WithTop.recTopCoe with
  | top =>
    rcases eq_or_lt_of_le ha with ha | ha
    · subst a
      rw [weight_conventions.1]
      exact (EReal.zero_mul ⊤).symm
    · rw [weight_conventions.2.1 a ha]
      exact (EReal.coe_mul_top_of_pos ha).symm
  | coe r => rfl

end VariationalNotes.ConvexAnalysis
