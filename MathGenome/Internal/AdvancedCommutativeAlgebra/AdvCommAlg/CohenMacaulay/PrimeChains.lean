import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.HeightAndGrade
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.PrimeChains
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.OrderIsoNat

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u
namespace AdvCommAlg.CohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Catenarity of prime intervals, with saturated chains represented by
finite series of covering relations. -/
def Catenary (R : Type u) [CommRing R] : Prop := Specs.CatenaryValue R

private lemma coheight_eq_one_of_covBy_top {α : Type*} [PartialOrder α] [OrderTop α]
    {a : α} (h : a ⋖ ⊤) : Order.coheight a = 1 := by
  apply le_antisymm
  · rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup_le fun b => iSup_le fun hab => ?_
    have hb : b = ⊤ := (h.eq_or_eq hab.le le_top).resolve_left hab.ne'
    simp [hb]
  · simpa using Order.coheight_add_one_le h.lt

/-- The local dimension formula only needs CM at the local ring itself. -/
lemma prime_height_add_quotient_dimension_of_local [IsLocalRing R]
    (hCM : LocalCohenMacaulay R R) (p : PrimeSpectrum R) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim R := by
  have h := dimension_eq_localized_add_dim R hCM p (self_mem_support p)
  rw [dimension, Module.supportDim_self_eq_ringKrullDim] at h
  rw [dimension, Module.supportDim_eq_of_equiv (localizedSelfEquiv p),
    Module.supportDim_self_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)] at h
  exact h.symm

/-- A saturated inclusion of primes raises height by exactly one. -/
theorem height_add_one_of_covBy (hCM : CohenMacaulayRing R) (p q : PrimeSpectrum R)
    (hpq : p ⋖ q) : p.asIdeal.height + 1 = q.asIdeal.height := by
  let A := Localization.AtPrime q.asIdeal
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso A q.asIdeal
  let P : PrimeSpectrum A := e.symm ⟨p, hpq.le⟩
  have hP : (e P).1 = p := congrArg Subtype.val (e.apply_symm_apply ⟨p, hpq.le⟩)
  have htop : (e (⊤ : PrimeSpectrum A)).1 = q := by
    have := e.map_top
    exact congrArg Subtype.val this
  have hcov : P ⋖ ⊤ := by
    apply covBy_of_eq_or_eq
    · apply e.lt_iff_lt.mp
      change (e P).1 < (e ⊤).1
      rw [hP, htop]
      exact hpq.lt
    · intro b hPb hb
      have he := hpq.eq_or_eq (show p ≤ (e b).1 by
          have hh : (e P).1 ≤ (e b).1 := e.monotone hPb
          rw [hP] at hh
          exact hh)
        (show (e b).1 ≤ q from (e b).2)
      rcases he with he | he
      · left
        apply e.injective
        exact Subtype.ext (he.trans hP.symm)
      · right
        apply e.injective
        exact Subtype.ext (he.trans htop.symm)
  have hdim : ringKrullDim (A ⧸ P.asIdeal) = (1 : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient]
    change Order.krullDim (Set.Ici P) = _
    rw [← Order.coheight_eq_krullDim_Ici]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (coheight_eq_one_of_covBy_top hcov)
  have hPI : P.asIdeal.under R = p.asIdeal := congrArg PrimeSpectrum.asIdeal hP
  have hheight : P.asIdeal.height = p.asIdeal.height := by
    rw [← IsLocalization.height_under q.asIdeal.primeCompl P.asIdeal, hPI]
  have h := prime_height_add_quotient_dimension_of_local (hCM q) P
  rw [hdim, hheight, IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal A,
    ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_inj] at h
  exact h

/-- Summing the unit height increments along a saturated chain. -/
theorem saturated_chain_length (hCM : CohenMacaulayRing R) (c : Specs.PrimeChain R) :
    (c.length : ℕ∞) + c.head.asIdeal.height = c.last.asIdeal.height := by
  induction c using RelSeries.inductionOn with
  | singleton p => simp
  | cons c p hpc ih =>
    rw [RelSeries.cons_length, RelSeries.head_cons, RelSeries.last_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm 1, height_add_one_of_covBy hCM p c.head hpc]
    exact ih

/-- Prime intervals have finite dimension even when the whole ring does not. -/
lemma finiteDimensional_prime_interval (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    FiniteDimensionalOrder (Set.Icc p q) := by
  letI : Nonempty (Set.Icc p q) := ⟨⟨p, le_rfl, hpq⟩⟩
  apply Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
  constructor
  · exact Order.krullDim_ne_bot_iff.mpr inferInstance
  · have hd := Order.krullDim_le_of_strictMono
      (fun a : Set.Icc p q => (⟨a.1, a.2.2⟩ : Set.Iic q)) (fun _ _ h => h)
    rw [← Order.height_eq_krullDim_Iic, ← PrimeSpectrum.height_eq_orderHeight] at hd
    exact (hd.trans_lt (WithBot.coe_lt_coe.mpr
      (lt_top_iff_ne_top.mpr (Ideal.height_ne_top q.isPrime.ne_top)))).ne

/-- There is a finite saturated chain between any two comparable primes. -/
lemma exists_saturated_prime_chain (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    ∃ c : Specs.PrimeChain R, c.head = p ∧ c.last = q := by
  letI := finiteDimensional_prime_interval p q hpq
  letI : WellFoundedLT (Set.Icc p q) :=
    SetRel.IsWellFounded.of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
  letI : WellFoundedGT (Set.Icc p q) :=
    SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
  obtain ⟨a, ha0, n, han, ha⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
      (show (⟨p, le_rfl, hpq⟩ : Set.Icc p q) ≤ ⟨q, hpq, le_rfl⟩ from hpq)
  have hc : (Set.range (OrderEmbedding.subtype (· ∈ Set.Icc p q))).OrdConnected := by
    have hr : Set.range (OrderEmbedding.subtype (· ∈ Set.Icc p q)) = Set.Icc p q := by
      ext x
      simp
    rw [hr]
    infer_instance
  let c : Specs.PrimeChain R := ⟨n, fun i => (a i).1,
    fun i => by
      change (a i.val).1 ⋖ (a (i.val + 1)).1
      exact CovBy.image (OrderEmbedding.subtype (· ∈ Set.Icc p q)) (ha i i.isLt) hc⟩
  exact ⟨c, congrArg Subtype.val ha0, congrArg Subtype.val han⟩

/-- Every prime interval has a saturated chain and all such chains have the
same length. This includes the zero-length interval. -/
theorem catenary (hCM : CohenMacaulayRing R) : Catenary R := by
  constructor
  · intro p q hpq S hS
    letI := finiteDimensional_prime_interval p q hpq
    letI : WellFoundedLT (Set.Icc p q) :=
      SetRel.IsWellFounded.of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
    letI : WellFoundedGT (Set.Icc p q) :=
      SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : Set.Icc p q × Set.Icc p q | a < b}
    exact hS.lt_of_le.finite_of_wellFoundedLT_of_wellFoundedGT
  · intro p q hpq
    obtain ⟨c, hcp, hcq⟩ := exists_saturated_prime_chain p q hpq
    refine ⟨c, hcp, hcq, ?_⟩
    intro d hdp hdq
    have hc := saturated_chain_length hCM c
    have hd := saturated_chain_length hCM d
    rw [hcp, hcq] at hc
    rw [hdp, hdq] at hd
    have hfin := Ideal.height_ne_top p.isPrime.ne_top
    apply Nat.cast_injective (R := ℕ∞)
    exact le_antisymm ((ENat.add_le_add_iff_right hfin).mp (hd.trans hc.symm).le)
      ((ENat.add_le_add_iff_right hfin).mp (hc.trans hd.symm).le)

/-- A maximal chain in a finite-dimensional order admits a finite saturated
increasing enumeration. No finiteness of the ambient set is needed. -/
private lemma enumerate_maximal_chain {α : Type*} [PartialOrder α] [OrderTop α]
    [FiniteDimensionalOrder α] (S : Set α) (hS : IsMaxChain (· ≤ ·) S) :
    ∃ c : RelSeries {(a, b) : α × α | a ⋖ b},
      Set.range c = S ∧ IsMin c.head ∧ c.last = ⊤ := by
  classical
  letI : WellFoundedLT α :=
    SetRel.IsWellFounded.of_finiteDimensional {(a, b) : α × α | a < b}
  letI : WellFoundedGT α :=
    SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : α × α | a < b}
  have hfin := hS.isChain.lt_of_le.finite_of_wellFoundedLT_of_wellFoundedGT
  letI : Fintype S := hfin.fintype
  letI : Nonempty S := ⟨⟨⊤, hS.top_mem⟩⟩
  letI : LinearOrder S := hS.isChain.lt_of_le.linearOrder
  let n := Fintype.card S - 1
  have hcard : Fintype.card S = n + 1 :=
    (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)).symm
  let e : Fin (n + 1) ≃o S := monoEquivOfFin S hcard
  have hstep (i : Fin n) : (e i.castSucc).1 ⋖ (e i.succ).1 := by
    apply covBy_of_eq_or_eq
    · exact e.strictMono Fin.castSucc_lt_succ
    · intro x hl hr
      have hx : x ∈ S := by
        have hinsert : IsChain (· ≤ ·) (insert x S) := by
          apply hS.isChain.insert
          intro y hy _
          obtain ⟨j, hj⟩ := e.surjective ⟨y, hy⟩
          have hji : j ≤ i.castSucc ∨ i.succ ≤ j := by
            change j.val ≤ i.val ∨ i.val + 1 ≤ j.val
            omega
          rcases hji with hji | hji
          · exact Or.inr ((show (e j).1 ≤ (e i.castSucc).1 from e.monotone hji).trans hl |>
              fun h => by simpa only [hj] using h)
          · exact Or.inl (hr.trans (show (e i.succ).1 ≤ (e j).1 from e.monotone hji) |>
              fun h => by simpa only [hj] using h)
        rw [hS.2 hinsert (Set.subset_insert x S)]
        exact Set.mem_insert x S
      obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
      have hlj : i.castSucc ≤ j := e.le_iff_le.mp (by rw [hj]; exact hl)
      have hjr : j ≤ i.succ := e.le_iff_le.mp (by rw [hj]; exact hr)
      have hjcases : j = i.castSucc ∨ j = i.succ := by
        have hlv : i.val ≤ j.val := hlj
        have hrv : j.val ≤ i.val + 1 := hjr
        have : j.val = i.val ∨ j.val = i.val + 1 := by omega
        exact this.imp Fin.ext Fin.ext
      rcases hjcases with rfl | rfl
      · exact Or.inl (congrArg Subtype.val hj).symm
      · exact Or.inr (congrArg Subtype.val hj).symm
  let c : RelSeries {(a, b) : α × α | a ⋖ b} := ⟨n, fun i => (e i).1, hstep⟩
  have hrange : Set.range c = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨c, hrange, ?_, ?_⟩
  · intro x hx
    have hxS : x ∈ S := by
      have hinsert : IsChain (· ≤ ·) (insert x S) := by
        apply hS.isChain.insert
        intro y hy _
        obtain ⟨j, hj⟩ := e.surjective ⟨y, hy⟩
        exact Or.inl (hx.trans (show c.head ≤ (e j).1 from e.monotone (Fin.zero_le j)) |>
          fun h => by simpa only [hj] using h)
      rw [hS.2 hinsert (Set.subset_insert x S)]
      exact Set.mem_insert x S
    obtain ⟨j, hj⟩ := e.surjective ⟨x, hxS⟩
    have hh : c.head ≤ (e j).1 := e.monotone (Fin.zero_le j)
    simpa only [hj] using hh
  · obtain ⟨j, hj⟩ := e.surjective ⟨⊤, hS.top_mem⟩
    apply top_unique
    have hh : (e j).1 ≤ c.last := e.monotone (Fin.le_last j)
    simpa only [hj] using hh

/-- Arbitrary maximal prime chain sets in a local CM ring are finite,
start at a minimal prime, end at the maximal ideal, and have length dim R. -/
theorem maximal_chain_local [IsLocalRing R] (hCM : CohenMacaulayRing R)
    (S : Set (PrimeSpectrum R)) (hS : IsMaxChain (· ≤ ·) S) :
    ∃ c : Specs.PrimeChain R, Set.range c = S ∧ IsMin c.head ∧
      c.last.asIdeal = IsLocalRing.maximalIdeal R ∧
      (c.length : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨c, hrange, hmin, hlast⟩ := enumerate_maximal_chain S hS
  refine ⟨c, hrange, hmin, ?_, ?_⟩
  · exact congrArg PrimeSpectrum.asIdeal hlast
  · have h := saturated_chain_length hCM c
    have hzero : c.head.asIdeal.height = 0 := by
      rw [PrimeSpectrum.height_eq_orderHeight]
      exact Order.height_eq_zero.mpr hmin
    rw [hzero, add_zero, hlast] at h
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) h

end AdvCommAlg.CohenMacaulay
