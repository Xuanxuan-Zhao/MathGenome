import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.AdjointNilpotence
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.SimpleHighestWeight
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.IntegrableHighestWeight
import Mathlib.Algebra.Lie.Sl2

/-! Integrability of the canonical contragredient simple highest-weight quotient. -/

namespace LieNotes.Contragredient.IntegrableHighestWeight

open CartanQuotient
open SimpleHighestWeight (L)
open Specs.LieNotes.Contragredient.VermaModules (IsHighestVector IsWeightCharacter cartanAction lowerWeight)
open Specs.LieNotes.Contragredient.IntegrableHighestWeight (RankOneIdentity IntegrabilityCriterion)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U scalarModule)
open UniversalEnvelopingAlgebra (ι)

noncomputable section

universe u v w

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

private theorem positive_eq_lieSpan (R : Realization A H) :
    positive R = LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (e R)) := by
  change (LieSubalgebra.lieSpan ℂ (Presentation.Algebra R)
    (Set.range (Presentation.e R))).map (quotientMap R) = _
  rw [LieSubalgebra.map_lieSpan, ← Set.range_comp]
  rfl

private theorem e_mem_positive (R : Realization A H) (i : I) : e R i ∈ positive R := by
  rw [positive_eq_lieSpan]
  exact LieSubalgebra.subset_lieSpan (Set.mem_range_self i)

private theorem simpleTriple (hA : IsGeneralizedCartanMatrix A) (R : Realization A H) (i : I) :
    IsSl2Triple (cartan R (R.h i)) (e R i) (f R i) := by
  classical
  have hii : R.α i (R.h i) = 2 := by simp [R.pairing, hA.1 i]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    exact R.h_independent.ne_zero i (cartan_injective R (hz.trans (map_zero _).symm))
  · simpa using (definingRelations R).e_f i i
  · rw [(definingRelations R).cartan_e, hii, two_smul, two_nsmul]
  · rw [(definingRelations R).cartan_f, hii, two_smul, two_nsmul]

section Modules

variable {G : Type*} [LieRing G] [LieAlgebra ℂ G]
  {V : Type w} [AddCommGroup V] [Module (U G) V]

/-- The commutator relation on any module over the enveloping algebra. -/
private theorem commute_action (x y : G) (z : V) :
    ι ℂ x • (ι ℂ y • z) = ι ℂ ⁅x, y⁆ • z + ι ℂ y • (ι ℂ x • z) := by
  rw [← mul_smul, ← mul_smul, ← add_smul]
  congr 1
  exact sub_eq_iff_eq_add.mp (((ι ℂ).map_lie x y).symm)

variable [Module ℂ V] [IsScalarTower ℂ (U G) V]

private theorem raising_lowering_power {h e f : G} (t : IsSl2Triple h e f)
    {z : V} {c : ℂ} (hh : ι ℂ h • z = c • z) (he : ι ℂ e • z = 0) (n : ℕ) :
    ι ℂ e • ((ι ℂ f) ^ (n + 1) • z) =
      (((n : ℂ) + 1) * (c - (n : ℂ))) • ((ι ℂ f) ^ n • z) := by
  by_cases hz : z = 0
  · simp [hz]
  letI : LieRingModule (U G) V := LieRingModule.ofAssociativeModule
  letI : LieModule ℂ (U G) V := LieModule.ofAssociativeModule
  letI : LieRingModule G V := LieRingModule.compLieHom V (ι ℂ)
  letI : LieModule ℂ G V := LieModule.compLieHom V (ι ℂ)
  have hprim : t.HasPrimitiveVectorWith z c := ⟨hz, hh, he⟩
  have hend : LieModule.toEnd ℂ G V f = Algebra.lsmul ℂ ℂ V (ι ℂ f) := rfl
  have hp := hprim.lie_e_pow_succ_toEnd_f n
  simp only [hend, ← map_pow (Algebra.lsmul ℂ ℂ V), Algebra.lsmul_apply] at hp
  exact hp

end Modules

private theorem simple_raising_lowering (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (Λ : Module.Dual ℂ H)
    {V : Type w} [AddCommGroup V] [Module (U (Algebra R)) V]
    [Module ℂ V] [IsScalarTower ℂ (U (Algebra R)) V]
    {z : V} (hz : IsHighestVector R Λ z) (i : I) (n : ℕ) :
    ι ℂ (e R i) • ((ι ℂ (f R i)) ^ (n + 1) • z) =
      (((n : ℂ) + 1) * (Λ (R.h i) - (n : ℂ))) • ((ι ℂ (f R i)) ^ n • z) :=
  raising_lowering_power (simpleTriple hA R i) (hz.1 (R.h i)) (hz.2 ⟨_, e_mem_positive R i⟩) n

theorem rankOneIdentity : RankOneIdentity.{u, v, w} := by
  intro I A H _ _ _ hA R Λ V _ _
  letI : Module ℂ V := scalarModule (B := U (Algebra R)) V
  letI : IsScalarTower ℂ (U (Algebra R)) V :=
    IsScalarTower.of_algebraMap_smul (A := U (Algebra R)) fun _ _ ↦ rfl
  intro z hz i n
  exact simple_raising_lowering hA R Λ hz i n

section SingularVectors

variable (R : Realization A H) (Λ : Module.Dual ℂ H)
  (hχ : ∃! χ, IsWeightCharacter R Λ χ)

private theorem positive_kills_of_simple {V : Type w} [AddCommGroup V] [Module (U (Algebra R)) V]
    [Module ℂ V] [IsScalarTower ℂ (U (Algebra R)) V] (z : V)
    (hz : ∀ i, ι ℂ (e R i) • z = 0) {x : Algebra R} (hx : x ∈ positive R) :
    ι ℂ x • z = 0 := by
  rw [positive_eq_lieSpan] at hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hz i
  | zero => rw [map_zero, zero_smul]
  | add y t _ _ hy ht => rw [map_add, add_smul, hy, ht, add_zero]
  | smul c y _ hy => rw [map_smul, smul_assoc, hy, smul_zero]
  | lie y t _ _ hy ht =>
    have h := commute_action y t z
    simpa only [hy, ht, smul_zero, add_zero, eq_comm] using h

private theorem cartan_lowering_power {V : Type w} [AddCommGroup V] [Module (U (Algebra R)) V]
    [Module ℂ V] [IsScalarTower ℂ (U (Algebra R)) V] {z : V}
    (hz : IsHighestVector R Λ z) (i : I) (h : H) (n : ℕ) :
    ι ℂ (cartan R h) • ((ι ℂ (f R i)) ^ n • z) =
      (Λ h - (n : ℂ) * R.α i h) • ((ι ℂ (f R i)) ^ n • z) := by
  induction n with
  | zero => simpa using hz.1 h
  | succ n ih =>
    rw [pow_succ', mul_smul, commute_action, (definingRelations R).cartan_f, map_neg, map_smul,
      neg_smul, smul_assoc, ih, smul_comm (ι ℂ (f R i)) (Λ h - (n : ℂ) * R.α i h),
      ← neg_smul, ← add_smul]
    congr 1
    push_cast
    ring

private theorem other_raising_lowering_power {V : Type w} [AddCommGroup V]
    [Module (U (Algebra R)) V] {z : V} {j i : I} (hji : j ≠ i)
    (hz : ι ℂ (e R j) • z = 0) (n : ℕ) :
    ι ℂ (e R j) • ((ι ℂ (f R i)) ^ n • z) = 0 := by
  classical
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [pow_succ', mul_smul, commute_action, (definingRelations R).e_f, ite_eq_right hji,
      map_zero, zero_smul, ih, smul_zero, add_zero]

/-- A nonzero shift down a simple root cannot be followed by a further nonnegative
root combination back to the original weight. -/
private theorem not_mem_lowerWeight_range (i : I) {n : ℕ} (hn : 0 < n) :
    Λ ∉ Set.range (lowerWeight R (Λ - (n : ℂ) • R.α i)) := by
  classical
  rintro ⟨m, hm⟩
  let q : Q I := m.mapRange (fun k : ℕ ↦ (k : ℤ)) rfl
  have hsum : Λ - ((n : ℂ) • R.α i + R.rootWeight q) = Λ - 0 := by
    rw [← sub_sub, sub_zero]
    exact hm
  have hzero : R.rootWeight (Finsupp.single i (n : ℤ) + q) = 0 := by
    rw [map_add, Realization.rootWeight_single, Int.cast_natCast]
    exact sub_right_inj.mp hsum
  have heq : Finsupp.single i (n : ℤ) + q = 0 :=
    Realization.rootWeight_injective R (hzero.trans (map_zero _).symm)
  have hi := congrArg (fun p : Q I ↦ p i) heq
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply, q,
    Finsupp.mapRange_apply] at hi
  omega

/-- An image of a Verma module whose weights miss the original top is a proper submodule. -/
private theorem lower_highest_mem_radical (μ : Module.Dual ℂ H)
    (hμΛ : Λ ∉ Set.range (lowerWeight R μ)) (z : VermaModules.Verma R Λ hχ)
    (hz : IsHighestVector R μ z) : z ∈ SimpleHighestWeight.radical R Λ hχ := by
  classical
  let V := VermaModules.Verma R Λ hχ
  let hμ := VermaModules.weightCharacterExists R μ
  have hz' : letI := scalarModule (B := U (Algebra R)) V; IsHighestVector R μ z := by
    constructor
    · intro h
      change ι ℂ (cartan R h) • z = algebraMap ℂ (U (Algebra R)) (μ h) • z
      rw [algebraMap_smul]
      exact hz.1 h
    · exact hz.2
  obtain ⟨φ, hφ, _⟩ := (VermaModules.highestWeightUniversal R μ hμ).2 V z hz'
  let W := VermaModules.weightSpaceAt R Λ hχ
  let W' := VermaModules.weightSpaceAt R μ hμ
  let lower := ⨆ ν, ⨆ (_ : ν ≠ Λ), W ν
  let φℂ := φ.restrictScalars ℂ
  have hmap (ν : Module.Dual ℂ H) : (W' ν).map φℂ ≤ W ν := by
    rintro _ ⟨y, hy, rfl⟩
    apply (VermaModules.mem_weightSpaceAt R Λ hχ).mpr
    intro h
    have hyh := (VermaModules.mem_weightSpaceAt R μ hμ).mp hy h
    simpa only [φℂ, LinearMap.restrictScalars_apply, map_smul, φ.map_smul_of_tower] using
      congrArg φ hyh
  have hrange : LinearMap.range φℂ ≤ lower := by
    rw [← Submodule.map_top, ← (VermaModules.weightDecomposition R μ hμ).submodule_iSup_eq_top,
      Submodule.map_iSup]
    refine iSup_le fun ν ↦ ?_
    by_cases hν : ν = Λ
    · subst ν
      change (W' Λ).map φℂ ≤ lower
      rw [show W' Λ = ⊥ from VermaModules.weightSupport R μ hμ Λ hμΛ, Submodule.map_bot]
      exact bot_le
    · exact (hmap ν).trans (le_iSup_of_le ν (le_iSup_of_le hν le_rfl))
  have hproper : LinearMap.range φ ≠ ⊤ := by
    intro hsurj
    let v := VermaModules.top R Λ hχ
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hsurj v
    have hl : v ∈ lower := hrange ⟨y, hy⟩
    have ht : v ∈ W Λ :=
      (VermaModules.mem_weightSpaceAt R Λ hχ).mpr (VermaModules.top_isHighest R Λ hχ).1
    have hd : Disjoint (W Λ) lower := weightSpace_iSupIndep (cartanAction R V) Λ
    exact (VermaModules.topWeightSpace R Λ hχ).1 (Submodule.disjoint_def.mp hd v ht hl)
  exact (SimpleHighestWeight.radicalIsGreatest R Λ hχ).2 hproper ⟨_, hφ⟩

private theorem lowering_power_mem_radical (hA : IsGeneralizedCartanMatrix A) (i : I)
    (m : ℕ) (hm : Λ (R.h i) = (m : ℂ)) :
    (ι ℂ (f R i)) ^ (m + 1) • VermaModules.top R Λ hχ ∈
      SimpleHighestWeight.radical R Λ hχ := by
  let v := VermaModules.top R Λ hχ
  let z := (ι ℂ (f R i)) ^ (m + 1) • v
  let μ := Λ - ((m + 1 : ℕ) : ℂ) • R.α i
  have hv : IsHighestVector R Λ v := VermaModules.top_isHighest R Λ hχ
  have hz : IsHighestVector R μ z := by
    constructor
    · intro h
      exact cartan_lowering_power R Λ hv i h (m + 1)
    · intro x
      apply positive_kills_of_simple R z _ x.property
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [hm, sub_self, mul_zero, zero_smul] using
          simple_raising_lowering hA R Λ hv i m
      · exact other_raising_lowering_power R hji (hv.2 ⟨_, e_mem_positive R j⟩) (m + 1)
  exact lower_highest_mem_radical R Λ hχ μ (not_mem_lowerWeight_range R Λ i (Nat.succ_pos m)) z hz

end SingularVectors

section LocalNilpotence

variable {G : Type*} [LieRing G] [LieAlgebra ℂ G]
  {V : Type w} [AddCommGroup V] [Module (U G) V]

/-- A sum of annihilating exponents suffices for a Lie generator acting on a vector. -/
private theorem power_smul_action (x : G) :
    ∀ (p n : ℕ) (y : G) (z : V), (LieAlgebra.ad ℂ G x ^ p) y = 0 →
      (ι ℂ x) ^ n • z = 0 → (ι ℂ x) ^ (p + n) • (ι ℂ y • z) = 0 := by
  intro p
  induction p with
  | zero =>
    intro n y z hy _
    have : y = 0 := by simpa using hy
    subst y
    simp
  | succ p ihp =>
    intro n
    induction n with
    | zero =>
      intro y z _ hz
      have : z = 0 := by simpa using hz
      subst z
      simp
    | succ n ihn =>
      intro y z hy hz
      have hy' : (LieAlgebra.ad ℂ G x ^ p) ⁅x, y⁆ = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using hy
      have hz' : (ι ℂ x) ^ n • (ι ℂ x • z) = 0 := by
        simpa only [pow_succ, mul_smul] using hz
      rw [Nat.add_succ, pow_succ, mul_smul, commute_action, smul_add]
      have hleft : (ι ℂ x) ^ (p.succ + n) • (ι ℂ ⁅x, y⁆ • z) = 0 := by
        simpa only [Nat.succ_add, Nat.add_succ] using ihp (n + 1) ⁅x, y⁆ z hy' hz
      rw [hleft, ihn y (ι ℂ x • z) hy hz', add_zero]

private theorem pow_smul_zero_of_le (a : U G) (z : V) {m n : ℕ}
    (hz : a ^ m • z = 0) (hmn : m ≤ n) : a ^ n • z = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m k, pow_add, mul_smul, hz, smul_zero]

/-- The vectors killed by some power of `x` are stable under the enveloping action. -/
private theorem locally_nilpotent_on_cyclic (x : G)
    (hx : ∀ y : G, ∃ n : ℕ, (LieAlgebra.ad ℂ G x ^ n) y = 0)
    (v : V) (hv : ∃ n : ℕ, (ι ℂ x) ^ n • v = 0)
    (hcyc : ∀ z : V, ∃ a : U G, a • v = z)
    (z : V) : ∃ n : ℕ, (ι ℂ x) ^ n • z = 0 := by
  let a : U G := ι ℂ x
  have hstable (b : U G) : ∀ {y : V}, (∃ n : ℕ, a ^ n • y = 0) →
      ∃ n : ℕ, a ^ n • (b • y) = 0 := by
    induction b using Shared.Lie.enveloping_induction ℂ G with
    | scalar c =>
      rintro y ⟨n, hn⟩
      exact ⟨n, by rw [← mul_smul, ← Algebra.commutes, mul_smul, hn, smul_zero]⟩
    | generator t =>
      rintro y ⟨n, hn⟩
      obtain ⟨p, hp⟩ := hx t
      exact ⟨p + n, power_smul_action x p n t y hp hn⟩
    | mul p q hp hq =>
      intro y hy
      rw [mul_smul]
      exact hp (hq hy)
    | add p q hp hq =>
      intro y hy
      obtain ⟨m, hm⟩ := hp hy
      obtain ⟨n, hn⟩ := hq hy
      refine ⟨m + n, ?_⟩
      rw [add_smul, smul_add, pow_smul_zero_of_le a _ hm (Nat.le_add_right m n),
        pow_smul_zero_of_le a _ hn (Nat.le_add_left n m), add_zero]
  obtain ⟨b, rfl⟩ := hcyc z
  exact hstable b hv

end LocalNilpotence

theorem integrabilityCriterion : IntegrabilityCriterion.{u, v} := by
  intro I A H _ _ _ hA R Λ hχ
  let v := SimpleHighestWeight.top R Λ hχ
  obtain ⟨hv₀, hv⟩ := SimpleHighestWeight.topHighest R Λ hχ
  constructor
  · rintro ⟨_, hf⟩ i
    obtain ⟨n, hn, hs⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
      (p := fun n ↦ (ι ℂ (f R i)) ^ n • v = 0) (by simpa using hv₀) (hf i v)
    have he := simple_raising_lowering hA R Λ hv i n
    change (ι ℂ (f R i)) ^ n • SimpleHighestWeight.top R Λ hχ ≠ 0 at hn
    change (ι ℂ (f R i)) ^ (n + 1) • SimpleHighestWeight.top R Λ hχ = 0 at hs
    rw [hs, smul_zero, eq_comm, smul_eq_zero_iff_left hn, mul_eq_zero, sub_eq_zero] at he
    exact ⟨n, he.resolve_left (Nat.cast_add_one_ne_zero n)⟩
  · intro h
    let q := SimpleHighestWeight.quotientMap R Λ hχ
    have hcyc (z : L R Λ hχ) : ∃ b : U (Algebra R), b • v = z := by
      obtain ⟨y, hy⟩ := (SimpleHighestWeight.radical R Λ hχ).mkQ_surjective z
      obtain ⟨b, hb⟩ := VermaModules.top_cyclic R Λ hχ y
      refine ⟨b, ?_⟩
      change b • q (VermaModules.top R Λ hχ) = z
      rw [← map_smul, hb]
      exact hy
    constructor
    · intro i z
      exact locally_nilpotent_on_cyclic (e R i)
        (AdjointNilpotence.ad_e_locally_nilpotent hA R i) v
        ⟨1, by simpa only [pow_one] using hv.2 ⟨_, e_mem_positive R i⟩⟩ hcyc z
    · intro i z
      obtain ⟨m, hm⟩ := h i
      have hzero : q ((ι ℂ (f R i)) ^ (m + 1) • VermaModules.top R Λ hχ) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (lowering_power_mem_radical R Λ hχ hA i m hm)
      rw [map_smul] at hzero
      exact locally_nilpotent_on_cyclic (f R i)
        (AdjointNilpotence.ad_f_locally_nilpotent hA R i) v ⟨m + 1, hzero⟩ hcyc z

end

end LieNotes.Contragredient.IntegrableHighestWeight
