import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.LabelledCycles
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Classes.SumProduct
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Group.TypeTags.Finite
import Lean.Elab.Tactic.Omega

/-! Nonempty labelled cycles, paper.tex p204:W22 (first assertion).
The canonical model consists of decorated partitions with enumerated blocks,
quotiented by the cyclic shift action. Length parameter `k` means `k + 1`.
-/
noncomputable section
universe u v w r
open scoped BigOperators
namespace FiniteCombinatorics.Classes.LabelledCycles
open Specs.FiniteCombinatorics.Classes.LabelledCycles

abbrev OrderedTuples := orderedTuplesValue
abbrev rotate := rotationValue
abbrev CycleObjects := cycleObjectsValue
abbrev AllCycles := allCyclesValue
abbrev cycleCount := cycleCountValue
abbrev allCycleCount := allCycleCountValue
abbrev cycleEGF {R : Type r} [CommRing R] [Algebra ℚ R] := cycleEGFValue (R := R)
abbrev allCycleEGF {R : Type r} [CommRing R] [Algebra ℚ R] := allCycleEGFValue (R := R)
abbrev cycleSum {R : Type r} [CommRing R] [Algebra ℚ R] := cycleSumValue (R := R)

@[simp] theorem smul_rotate (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (a : Multiplicative (ZMod (k+1)))
    (x : OrderedTuples A k S) : a • x = rotate A k S a.toAdd x := rfl

@[simp] theorem coeff_cycleEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k n : ℕ) :
    PowerSeries.coeff n (cycleEGF (R := R) A k) =
      (cycleCount A k n : R) * algebraMap ℚ R ((n.factorial : ℚ)⁻¹) :=
  Series.coeff_egf _ n

@[simp] theorem coeff_allCycleEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (n : ℕ) :
    PowerSeries.coeff n (allCycleEGF (R := R) A) =
      (allCycleCount A n : R) * algebraMap ℚ R ((n.factorial : ℚ)⁻¹) :=
  Series.coeff_egf _ n

instance orderedTuples_finite (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Finite (OrderedTuples A k S) := by
  classical
  letI := Fintype.ofFinite S
  unfold OrderedTuples orderedTuplesValue
  haveI : Finite (Specs.FiniteCombinatorics.Classes.componentObjectsValue A S) :=
    labelledComponentObjects_finite A S
  infer_instance

instance cycleObjects_finite (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Finite (CycleObjects A k S) :=
  Quotient.finite _

instance allCycles_finite (A : LabelledClass.{u,v}) (S : Type u) [Finite S] :
    Finite (AllCycles A S) := by
  unfold AllCycles allCyclesValue
  infer_instance

/-- Nonempty disjoint blocks force the length bound, independently of `A`. -/
theorem length_bound (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (h : Nonempty (OrderedTuples A k S)) :
    k+1 ≤ Nat.card S := by
  classical
  letI := Fintype.ofFinite S
  rcases h with ⟨⟨D, e⟩⟩
  have hc : k+1 = D.1.parts.card := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using Nat.card_congr e
  rw [hc, Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact D.1.card_parts_le_card

theorem cycle_length_bound (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (h : Nonempty (CycleObjects A k S)) :
    k+1 ≤ Nat.card S := by
  rcases h with ⟨x⟩
  exact length_bound A k S ⟨x.out⟩

theorem cycleCount_above (A : LabelledClass.{u,v}) (k n : ℕ)
    (h : n < k+1) : cycleCount A k n = 0 := by
  haveI : IsEmpty (CycleObjects A k (StandardLabels.{u} n)) :=
    ⟨fun x => (not_le_of_gt h) (by
      simpa only [card_standardLabels] using
        cycle_length_bound A k (StandardLabels.{u} n) ⟨x⟩)⟩
  exact Nat.card_of_isEmpty

/-- Equality in the quotient is exactly equality up to rotation. -/
theorem quotient_rotations (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (x y : OrderedTuples A k S) :
    (Quotient.mk _ x : CycleObjects A k S) = Quotient.mk _ y ↔
      ∃ a : ZMod (k+1), rotate A k S a x = y := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a.toAdd, ?_⟩
    have h : a⁻¹ • x = y := by rw [← ha, inv_smul_smul]
    simpa only [smul_rotate, toAdd_inv] using h
  · rintro ⟨a, ha⟩
    change (Multiplicative.ofAdd a) • x = y at ha
    refine ⟨Multiplicative.ofAdd (-a), ?_⟩
    have h : (Multiplicative.ofAdd a)⁻¹ • y = x := by rw [← ha, inv_smul_smul]
    simpa only [ofAdd_neg] using h

/-- A shift fixing a tuple fixes its block enumeration, hence is zero. -/
theorem rotation_free (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (a : ZMod (k+1)) (x : OrderedTuples A k S)
    (h : rotate A k S a x = x) : a = 0 := by
  classical
  rcases x with ⟨D, e⟩
  have he : (Equiv.addLeft a).trans e = e := eq_of_heq (Sigma.mk.inj h).2
  have hz := congrArg (fun f : ZMod (k+1) ≃ D.1.parts => f 0) he
  simpa using e.injective hz

instance rotation_isCancelSMul (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] :
    IsCancelSMul (Multiplicative (ZMod (k+1))) (OrderedTuples A k S) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro a x h
  have ha := rotation_free A k S a.toAdd x h
  exact congrArg Multiplicative.ofAdd ha

/-- Each orbit has precisely `k+1` representatives. -/
theorem orbit_cardinality (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] :
    Nat.card (OrderedTuples A k S) = (k+1) * Nat.card (CycleObjects A k S) := by
  classical
  let G := Multiplicative (ZMod (k+1))
  let X := OrderedTuples A k S
  letI : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite (CycleObjects A k S)
  have he := MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X
  have hc := Nat.card_congr he
  simp only [IsCancelSMul.stabilizer_eq_bot] at hc
  rw [Nat.card_sigma] at hc
  simp only [Nat.card_congr (QuotientGroup.quotientEquivSelf G)] at hc
  simpa [G, X, CycleObjects, cycleObjectsValue, Nat.card_eq_fintype_card,
    ZMod.card, mul_comm] using hc

theorem allCycles_count (A : LabelledClass.{u,v}) (n : ℕ) :
    allCycleCount A n = ∑ k ∈ Finset.range n, cycleCount A k n := by
  unfold allCycleCount allCycleCountValue allCyclesValue
  rw [card_standardLabels, Nat.card_sigma]
  exact Fin.sum_univ_eq_sum_range (fun k => cycleCount A k n) n

theorem emptyCycle_count (A : LabelledClass.{u,v}) : allCycleCount A 0 = 0 := by
  simp [allCycles_count]

/-- The formal sum is locally finite: degrees below the exponent vanish. -/
theorem coeff_pow_eq_zero {R : Type r} [CommRing R]
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = 0)
    {n j : ℕ} (hj : n < j) : PowerSeries.coeff n (F ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hj)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j hF)

private theorem logarithm_term {R : Type r} [CommRing R] [Algebra ℚ R]
    (F : PowerSeries R) (n k : ℕ) :
    PowerSeries.coeff (k+1) (PowerSeries.log R) *
        PowerSeries.coeff n ((-F) ^ (k+1)) =
      -(algebraMap ℚ R ((k+1 : ℚ)⁻¹) * PowerSeries.coeff n (F ^ (k+1))) := by
  have hp : (-F) ^ (k+1) = (-1 : R) ^ (k+1) • F ^ (k+1) := by
    rw [← smul_pow]
    simp
  have hs : (-1 : R) ^ (k+1) * (-1 : R) ^ (k+1) = 1 := by
    rw [← mul_pow]
    simp
  rw [PowerSeries.coeff_log, ite_eq_right (by omega), div_eq_mul_inv, map_mul,
    map_pow, map_neg, map_one, hp, PowerSeries.coeff_smul, smul_eq_mul, pow_succ]
  calc
    _ = -(((-1 : R) ^ (k+1) * (-1 : R) ^ (k+1)) *
        (algebraMap ℚ R ((↑(k+1) : ℚ)⁻¹) * PowerSeries.coeff n (F ^ (k+1)))) := by
          push_cast
          ring
    _ = _ := by rw [hs]; simp

/-- The coefficientwise sum agrees with the standard formal logarithm.
This uses no convergence assumptions and allows every commutative ℚ-algebra. -/
theorem formalLogarithm {R : Type r} [CommRing R] [Algebra ℚ R]
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = 0) :
    cycleSum F = -PowerSeries.logOf (1 - F) := by
  classical
  have hneg : PowerSeries.constantCoeff (-F) = 0 := by simp [hF]
  have he : (1 - F) - 1 = -F := by ring
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.logOf_eq, he, map_neg, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero hneg)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n+1)) (by
    intro j hj
    by_contra hn
    have hjn : n < j := by
      have : ¬j < n+1 := by simpa only [Finset.mem_coe, Finset.mem_range] using hn
      omega
    have hz := coeff_pow_eq_zero (-F) hneg hjn
    exact hj (by simp [hz]))]
  rw [Finset.sum_range_succ', PowerSeries.coeff_log]
  simp only [ite_true, zero_mul, add_zero, smul_eq_mul, logarithm_term,
    Finset.sum_neg_distrib, neg_neg, cycleSum, cycleSumValue, PowerSeries.coeff_mk]

/-- Conversion of the ordered-tuple EGF into the cycle EGF using the free action. -/
theorem cycleEGF_of_orderedEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k : ℕ)
    (hOrdered : Series.egf (fun n =>
      (Nat.card (OrderedTuples A k (StandardLabels.{u} n)) : R)) = A.egf ^ (k+1)) :
    cycleEGF (R := R) A k =
      algebraMap ℚ R ((k+1 : ℚ)⁻¹) • A.egf ^ (k+1) := by
  rw [← hOrdered]
  apply PowerSeries.ext
  intro n
  have hc : (Nat.card (OrderedTuples A k (StandardLabels.{u} n)) : R) =
      (k+1 : R) * (cycleCount A k n : R) := by
    have h := orbit_cardinality A k (StandardLabels.{u} n)
    change Nat.card (OrderedTuples A k (StandardLabels.{u} n)) =
      (k+1) * cycleCount A k n at h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun m : ℕ => (m : R)) h
  have hinv : algebraMap ℚ R ((k+1 : ℚ)⁻¹) * (k+1 : R) = 1 := by
    have hk : (k+1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simpa using congrArg (algebraMap ℚ R) (inv_mul_cancel₀ hk)
  rw [coeff_cycleEGF, PowerSeries.coeff_smul, Series.coeff_egf, smul_eq_mul]
  rw [hc]
  simp only [← mul_assoc, hinv, one_mul]

/-- Once the fixed-length terms are known, the finite sum of actual cycle
counts gives the coefficientwise infinite cycle sum. -/
theorem allCycleEGF_of_cycleEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v})
    (hCycle : ∀ k, cycleEGF (R := R) A k =
      algebraMap ℚ R ((k+1 : ℚ)⁻¹) • A.egf ^ (k+1)) :
    allCycleEGF (R := R) A = cycleSum A.egf := by
  classical
  apply PowerSeries.ext
  intro n
  rw [coeff_allCycleEGF, allCycles_count, Nat.cast_sum, Finset.sum_mul]
  simp only [← coeff_cycleEGF]
  simp only [hCycle, PowerSeries.coeff_smul, smul_eq_mul, cycleSum, cycleSumValue,
    PowerSeries.coeff_mk]

theorem positive_constantCoeff {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0))) :
    PowerSeries.constantCoeff (A.egf (R := R)) = 0 := by
  letI := hA
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LabelledClass.count]

/-- Binomial convolution of actual tuple counts gives their product EGFs. -/
theorem orderedEGF_of_count_recurrence {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v})
    (hbase : ∀ n, Nat.card (OrderedTuples A 0 (StandardLabels.{u} n)) = A.count n)
    (hstep : ∀ k n, Nat.card (OrderedTuples A (k+1) (StandardLabels.{u} n)) =
      ∑ i ∈ Finset.range (n+1), Nat.choose n i * A.count i *
        Nat.card (OrderedTuples A k (StandardLabels.{u} (n-i)))) :
    ∀ k, Series.egf (fun n =>
      (Nat.card (OrderedTuples A k (StandardLabels.{u} n)) : R)) = A.egf ^ (k+1) := by
  intro k
  induction k with
  | zero => simp only [hbase, zero_add, pow_one, LabelledClass.egf]
  | succ k ih =>
    rw [pow_succ', ← ih, LabelledClass.egf, Series.egf_mul]
    congr 1
    funext n
    simp only [hstep, Nat.cast_sum, Nat.cast_mul]

/-- Assemble the cycle logarithm formula from the fixed-length tuple EGFs. -/
theorem cycleLogarithm_of_orderedEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0)))
    (hOrdered : ∀ k, Series.egf (fun n =>
      (Nat.card (OrderedTuples A k (StandardLabels.{u} n)) : R)) = A.egf ^ (k+1)) :
    allCycleEGF (R := R) A = -PowerSeries.logOf (1 - A.egf) := by
  rw [allCycleEGF_of_cycleEGF A (fun k => cycleEGF_of_orderedEGF A k (hOrdered k))]
  exact formalLogarithm A.egf (positive_constantCoeff A hA)

/-! For counting, list each decorated block explicitly. The ambient label type
is kept fixed, even when passing to a subset of the labels. -/
private abbrev BlockEntry (A : LabelledClass.{u,v}) (S : Type u) [Finite S] :=
  (b : Finset S) × A.Obj ↥b

private def ValidBlocks {A : LabelledClass.{u,v}} {S : Type u} [Finite S]
    {I : Type*} (t : Finset S) (f : I → BlockEntry A S) : Prop :=
  (∀ i, (f i).1.Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (f i).1 (f j).1) ∧
  (∀ x, x ∈ t ↔ ∃ i, x ∈ (f i).1)

private def BlockTuple (A : LabelledClass.{u,v}) (m : ℕ)
    {S : Type u} [Finite S] (t : Finset S) :=
  {f : Fin m → BlockEntry A S // ValidBlocks t f}


private instance blockTuple_finite (A : LabelledClass.{u,v}) (m : ℕ)
    {S : Type u} [Finite S] (t : Finset S) : Finite (BlockTuple A m t) := by
  classical
  unfold BlockTuple BlockEntry
  infer_instance

private theorem blocks_injective {A : LabelledClass.{u,v}} {S : Type u} [Finite S]
    {I : Type*} {t : Finset S} {f : I → BlockEntry A S} (h : ValidBlocks t f) :
    Function.Injective (fun i => (f i).1) := by
  classical
  intro i j hij
  by_contra hn
  obtain ⟨x, hx⟩ := h.1 i
  exact Finset.disjoint_left.mp (h.2.1 i j hn) hx (by simpa only [hij] using hx)

private def orderedBlocks (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : OrderedTuples A k S →
      (by classical letI := Fintype.ofFinite S; exact BlockTuple A (k+1) (Finset.univ : Finset S)) := by
  classical
  letI := Fintype.ofFinite S
  intro x
  let e := (ZMod.finEquiv (k+1)).toEquiv.trans x.2
  refine ⟨fun i => ⟨(e i).val, x.1.2 (e i)⟩, ?_⟩
  refine ⟨fun i => x.1.1.nonempty_of_mem_parts (e i).property, ?_, ?_⟩
  · intro i j hij
    exact x.1.1.disjoint (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))
  · intro a
    constructor
    · intro _
      obtain ⟨b, hb, hab⟩ := x.1.1.exists_mem (Finset.mem_univ a)
      obtain ⟨i, hi⟩ := e.surjective ⟨b, hb⟩
      exact ⟨i, by simpa [hi] using hab⟩
    · intro _
      exact Finset.mem_univ a

private theorem orderedBlocks_injective (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Function.Injective (orderedBlocks A k S) := by
  classical
  letI := Fintype.ofFinite S
  rintro ⟨⟨P, a⟩, e⟩ ⟨⟨Q, b⟩, f⟩ h
  have hentry (i : Fin (k+1)) :
      (⟨(e ((ZMod.finEquiv (k+1)) i)).val, a (e ((ZMod.finEquiv (k+1)) i))⟩ : BlockEntry A S) =
      ⟨(f ((ZMod.finEquiv (k+1)) i)).val, b (f ((ZMod.finEquiv (k+1)) i))⟩ :=
    congrFun (congrArg Subtype.val h) i
  have hpart : P = Q := by
    ext c
    constructor
    · intro hc
      obtain ⟨i, hi⟩ := ((ZMod.finEquiv (k+1)).toEquiv.trans e).surjective ⟨c, hc⟩
      have hv := congrArg Sigma.fst (hentry i)
      dsimp only at hv
      have hv' : (e ((ZMod.finEquiv (k+1)) i)).val = c := congrArg Subtype.val hi
      rw [← hv', hv]
      exact (f _).property
    · intro hc
      obtain ⟨i, hi⟩ := ((ZMod.finEquiv (k+1)).toEquiv.trans f).surjective ⟨c, hc⟩
      have hv := congrArg Sigma.fst (hentry i)
      dsimp only at hv
      have hv' : (f ((ZMod.finEquiv (k+1)) i)).val = c := congrArg Subtype.val hi
      rw [← hv', ← hv]
      exact (e _).property
  subst Q
  have hef : e = f := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    obtain ⟨i, rfl⟩ := (ZMod.finEquiv (k+1)).surjective z
    exact congrArg Sigma.fst (hentry i)
  subst f
  have hab : a = b := by
    funext c
    obtain ⟨i, rfl⟩ := ((ZMod.finEquiv (k+1)).toEquiv.trans e).surjective c
    exact eq_of_heq (Sigma.mk.inj (hentry i)).2
  subst b
  rfl

private theorem orderedBlocks_surjective (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Function.Surjective (orderedBlocks A k S) := by
  classical
  letI := Fintype.ofFinite S
  rintro ⟨f, hf⟩
  let parts := Finset.univ.image (fun i => (f i).1)
  let P : Finpartition (Finset.univ : Finset S) := Finpartition.ofExistsUnique parts
    (fun _ _ => Finset.subset_univ _) (by
      intro x hx
      obtain ⟨i, hi⟩ := (hf.2.2 x).mp hx
      refine ⟨(f i).1, ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩, ?_⟩
      rintro c ⟨hc, hxc⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
      by_cases hij : j = i
      · subst j; rfl
      · exact False.elim (Finset.disjoint_left.mp (hf.2.1 j i hij) hxc hi)) (by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact (hf.1 i).ne_empty hi)
  let e : Fin (k+1) ≃ P.parts := Equiv.ofBijective
    (fun i => ⟨(f i).1, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j h => blocks_injective hf (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨i, rfl⟩⟩
  let a : (c : P.parts) → A.Obj ↥c.val := fun c =>
    cast (congrArg (fun b : Finset S => A.Obj ↥b)
      (congrArg Subtype.val (e.apply_symm_apply c))) (f (e.symm c)).2
  refine ⟨⟨⟨P, a⟩, (ZMod.finEquiv (k+1)).toEquiv.symm.trans e⟩, ?_⟩
  apply Subtype.ext
  funext i
  change (⟨(e i).val, a (e i)⟩ : BlockEntry A S) = f i
  apply Sigma.ext
  · rfl
  · dsimp only [a]
    exact (cast_heq _ _).trans ((Sigma.mk.inj (congrArg f (e.symm_apply_apply i))).2)

private def orderedBlocksEquiv (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : OrderedTuples A k S ≃
      (by classical letI := Fintype.ofFinite S; exact BlockTuple A (k+1) (Finset.univ : Finset S)) :=
  Equiv.ofBijective _ ⟨orderedBlocks_injective A k S, orderedBlocks_surjective A k S⟩

private def blockUncons (A : LabelledClass.{u,v}) (m : ℕ)
    {S : Type u} [Finite S] [DecidableEq S] (t : Finset S) : BlockTuple A (m+1) t →
      (b : {b : Finset S // b ⊆ t ∧ b.Nonempty}) ×
        (A.Obj ↥b.val × BlockTuple A m (t \ b.val)) := by
  classical
  rintro ⟨f, hf⟩
  refine ⟨⟨(f 0).1, ?_, hf.1 0⟩, (f 0).2, ⟨Fin.tail f, ?_⟩⟩
  · intro x hx
    exact (hf.2.2 x).mpr ⟨0, hx⟩
  · refine ⟨fun i => hf.1 i.succ, ?_, ?_⟩
    · intro i j hij
      exact hf.2.1 i.succ j.succ (fun h => hij (Fin.succ_injective _ h))
    · intro x
      constructor
      · intro hx
        obtain ⟨hxt, hxb⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨i, hi⟩ := (hf.2.2 x).mp hxt
        refine Fin.cases ?_ (fun j hj => ⟨j, hj⟩) i hi
        intro h
        exact False.elim (hxb h)
      · rintro ⟨i, hi⟩
        refine Finset.mem_sdiff.mpr ⟨(hf.2.2 x).mpr ⟨i.succ, hi⟩, ?_⟩
        intro hx
        exact Finset.disjoint_left.mp (hf.2.1 0 i.succ (Fin.succ_ne_zero i).symm) hx hi

private def blockCons (A : LabelledClass.{u,v}) (m : ℕ)
    {S : Type u} [Finite S] [DecidableEq S] (t : Finset S) :
      ((b : {b : Finset S // b ⊆ t ∧ b.Nonempty}) ×
        (A.Obj ↥b.val × BlockTuple A m (t \ b.val))) → BlockTuple A (m+1) t := by
  classical
  rintro ⟨b, a, f, hf⟩
  refine ⟨Fin.cons ⟨b.val, a⟩ f, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Fin.cases b.property.2 (fun j => hf.1 j) i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      exact False.elim (hij rfl)
    · intro _
      apply Finset.disjoint_left.mpr
      intro x hxb hxf
      exact (Finset.mem_sdiff.mp ((hf.2.2 x).mpr ⟨_, hxf⟩)).2 hxb
    · intro _
      apply Finset.disjoint_left.mpr
      intro x hxf hxb
      exact (Finset.mem_sdiff.mp ((hf.2.2 x).mpr ⟨_, hxf⟩)).2 hxb
    · intro hij
      exact hf.2.1 i j (fun h => hij (congrArg Fin.succ h))
  · intro x
    constructor
    · intro hxt
      by_cases hxb : x ∈ b.val
      · exact ⟨0, hxb⟩
      · obtain ⟨i, hi⟩ := (hf.2.2 x).mp (Finset.mem_sdiff.mpr ⟨hxt, hxb⟩)
        exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      refine Fin.cases ?_ (fun j hj => ?_) i hi
      · intro hx
        exact b.property.1 hx
      · exact (Finset.mem_sdiff.mp ((hf.2.2 x).mpr ⟨j, hj⟩)).1

private def blockSuccEquiv (A : LabelledClass.{u,v}) (m : ℕ)
    {S : Type u} [Finite S] [DecidableEq S] (t : Finset S) : BlockTuple A (m+1) t ≃
      (b : {b : Finset S // b ⊆ t ∧ b.Nonempty}) ×
        (A.Obj ↥b.val × BlockTuple A m (t \ b.val)) where
  toFun := blockUncons A m t
  invFun := blockCons A m t
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    exact Fin.cons_self_tail f
  right_inv := by
    rintro ⟨⟨b, hb⟩, a, f, hf⟩
    rfl


private theorem blockTuple_zero_card (A : LabelledClass.{u,v})
    {S : Type u} [Finite S] (t : Finset S) :
    Nat.card (BlockTuple A 0 t) = (by classical exact if t = ∅ then 1 else 0) := by
  classical
  by_cases ht : t = ∅
  · subst t
    rw [ite_eq_left rfl]
    haveI : Subsingleton (BlockTuple A 0 (∅ : Finset S)) :=
      ⟨fun x y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    apply Nat.card_of_subsingleton
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simp [ValidBlocks]
  · rw [ite_eq_right ht]
    haveI : IsEmpty (BlockTuple A 0 t) := ⟨fun f => ht (by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _⟩ := (f.property.2.2 x).mp hx
      exact Fin.elim0 i)⟩
    exact Nat.card_of_isEmpty


/-- Auxiliary binomial convolution coefficients; the cardinality lemma below
identifies them with actual decorated block tuples. -/
private def tupleCount (A : LabelledClass.{u,v}) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | m+1, n => ∑ i ∈ Finset.range (n+1), Nat.choose n i * A.count i * tupleCount A m (n-i)

private theorem tuple_card (A : LabelledClass.{u,v})
    (hA : IsEmpty (A.Obj (StandardLabels.{u} 0)))
    {S : Type u} [Finite S] [DecidableEq S]
    (T : ℕ → Finset S → Type w) [∀ m t, Finite (T m t)]
    (hzero : ∀ t, Nat.card (T 0 t) = if t = ∅ then 1 else 0)
    (hrec : ∀ m t, T (m+1) t ≃
       ((b : {b : Finset S // b ⊆ t ∧ b.Nonempty}) ×
        (A.Obj ↥b.val × T m (t \ b.val)))) :
    ∀ m t, Nat.card (T m t) = tupleCount A m t.card := by
  classical
  letI := Fintype.ofFinite S
  letI := hA
  have hA0 : A.count 0 = 0 := Nat.card_of_isEmpty
  intro m
  induction m with
  | zero =>
    intro t
    simpa only [tupleCount, Finset.card_eq_zero] using hzero t
  | succ m ih =>
    intro t
    rw [Nat.card_congr (hrec m t), Nat.card_sigma]
    simp only [Nat.card_prod, A.card_on_labels, Nat.card_eq_fintype_card, Fintype.card_coe, ih]
    have hs : (∑ b : {b : Finset S // b ⊆ t ∧ b.Nonempty},
        A.count b.val.card * tupleCount A m (t \ b.val).card) =
        ∑ b : {b : Finset S // b ⊆ t ∧ b.Nonempty},
        A.count b.val.card * tupleCount A m (t.card-b.val.card) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.card_sdiff_of_subset b.property.1]
    rw [hs]
    rw [← Finset.sum_subtype (t.powerset.filter Finset.Nonempty)
      (by intro b; simp only [Finset.mem_filter, Finset.mem_powerset])
      (fun b => A.count b.card * tupleCount A m (t.card - b.card))]
    rw [Finset.sum_subset (Finset.filter_subset Finset.Nonempty t.powerset) (by
      intro b hb hbn
      have he : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (by
        intro hbne
        exact hbn (Finset.mem_filter.mpr ⟨hb, hbne⟩))
      simp [he, hA0])]
    simpa only [tupleCount, nsmul_eq_mul, Nat.cast_id, mul_assoc] using
      Finset.sum_powerset_apply_card (fun i => A.count i * tupleCount A m (t.card-i))

private theorem tupleCount_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) :
    ∀ m, FiniteCombinatorics.Series.egf (fun n => (tupleCount A m n : R)) = A.egf ^ m := by
  intro m
  induction m with
  | zero =>
    apply PowerSeries.ext
    intro n
    simp only [pow_zero, FiniteCombinatorics.Series.coeff_egf, tupleCount, PowerSeries.coeff_one]
    split_ifs with h
    · subst n
      simp
    · simp
  | succ m ih =>
    rw [pow_succ', ← ih, LabelledClass.egf, FiniteCombinatorics.Series.egf_mul]
    congr 1
    funext n
    simp only [tupleCount, Nat.cast_sum, Nat.cast_mul]


/-- Ordered tuples of actual labelled components have the product EGF. -/
theorem ordered_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0))) (k : ℕ) :
    Series.egf (fun n =>
      (Nat.card (OrderedTuples A k (StandardLabels.{u} n)) : R)) = A.egf ^ (k+1) := by
  classical
  have hc (n : ℕ) : Nat.card (OrderedTuples A k (StandardLabels.{u} n)) =
      tupleCount A (k+1) n := by
    letI : Fintype (StandardLabels.{u} n) := Fintype.ofFinite _
    letI : DecidableEq (StandardLabels.{u} n) := Classical.decEq _
    rw [Nat.card_congr (orderedBlocksEquiv A k (StandardLabels.{u} n))]
    have h := tuple_card A hA (S := StandardLabels.{u} n)
      (fun m t => BlockTuple A m t) (fun t => blockTuple_zero_card A t)
      (fun m t => blockSuccEquiv A m t)
      (k+1) (Finset.univ : Finset (StandardLabels.{u} n))
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, card_standardLabels] using h
  simp_rw [hc]
  exact tupleCount_egf A (k+1)

/-- The free rotation action divides the fixed-length product EGF by its length. -/
theorem cycle_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0))) (k : ℕ) :
    cycleEGF (R := R) A k =
      algebraMap ℚ R ((k+1 : ℚ)⁻¹) • A.egf ^ (k+1) :=
  cycleEGF_of_orderedEGF A k (ordered_egf A hA k)

/-- All positive-length cycles give the coefficientwise locally finite cycle sum. -/
theorem allCycle_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0))) :
    allCycleEGF (R := R) A = cycleSum A.egf :=
  allCycleEGF_of_cycleEGF A (cycle_egf A hA)

/-- The EGF of nonempty labelled cycles is `-log(1-A)`. -/
theorem cycle_logarithm {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (hA : IsEmpty (A.Obj (StandardLabels.{u} 0))) :
    allCycleEGF (R := R) A = -PowerSeries.logOf (1 - A.egf) := by
  rw [allCycle_egf A hA]
  exact formalLogarithm A.egf (positive_constantCoeff A hA)

end FiniteCombinatorics.Classes.LabelledCycles
