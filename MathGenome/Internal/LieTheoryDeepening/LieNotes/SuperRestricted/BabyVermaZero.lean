import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaZero
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaQuotients
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Order.Interval.Finset.Fin

/-! The simple quotients of the zero-character baby Verma modules. -/

namespace LieNotes.SuperRestricted.BabyVermaZero

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaZero
open private ambient_pbw from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaInduction
open scoped BigOperators Polynomial

universe u w

abbrev tail : tailType.{u} := @tailValue

abbrev simpleQuotient : simpleQuotientType.{u} := @simpleQuotientValue

private theorem finCast_injective {k : Type u} [Field k] {p : ℕ} [CharP k p] :
    Function.Injective (fun m : Fin p => (m.val : k)) :=
  fun a b h => Fin.ext (CharP.natCast_injOn_Iio (R := k) p a.isLt b.isLt h)

theorem primeFieldRoots : primeFieldRootsType.{u} := by
  classical
  intro k _ p _ hp a
  let : NeZero p := ⟨by omega⟩
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let castFin : Fin p ↪ k := ⟨_, finCast_injective⟩
  let S := Finset.univ.map castFin
  let q : k[X] := Polynomial.X ^ p - Polynomial.X
  have hq : q ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : k[X] => f.coeff p) hz
    have h1 : p ≠ 1 := by omega
    simp [q, Polynomial.coeff_X, Ne.symm h1] at hh
  have hpow (a : ℕ) : (a : k) ^ p = (a : k) := map_natCast (frobenius k p) a
  have hroots : q.roots = S.val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero _ _ hq
    · intro x hx
      obtain ⟨m, _, rfl⟩ := Finset.mem_map.mp hx
      simp [q, castFin, hpow]
    · have hdeg : q.natDegree ≤ p := by
        simpa [q, max_eq_left (show 1 ≤ p by omega)] using
          (Polynomial.natDegree_sub_le (Polynomial.X ^ p : k[X]) Polynomial.X)
      simpa [S] using hdeg
  constructor
  · intro ha
    have hm : a ∈ q.roots := (Polynomial.mem_roots hq).mpr (by simpa [q] using ha)
    rw [hroots] at hm
    obtain ⟨m, _, hm⟩ := Finset.mem_map.mp (Finset.mem_def.mpr hm)
    exact ⟨m, hm.symm, fun n hn => finCast_injective (hn.symm.trans hm.symm)⟩
  · rintro ⟨m, rfl, _⟩
    rw [hpow, sub_self]

section BabyVerma

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
  {j : BorelAlgebra Q 0 →ₐ[k] ZeroAmbient P} {θ : BorelAlgebra Q 0 →ₐ[k] k}

local notation "A" => ZeroAmbient P
local notation "Z" => BabyVerma j θ
local notation "eₐ" => generator P 0 (E k)
local notation "fₐ" => generator P 0 (F k)
local notation "hₐ" => generator P 0 (H k)

private theorem tail_restrictScalars
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : ZeroBasisActions b m) :
    (tailValue b m).restrictScalars k = Submodule.span k (Set.range fun i : Set.Ioi m => b i) := by
  obtain ⟨hv, hh, he₀, he, hf, hf₀⟩ := hb
  let S : Submodule k Z := Submodule.span k (Set.range fun i : Set.Ioi m => b i)
  have gen_mem (i : Fin p) (hi : m < i) : b i ∈ S :=
    Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hgen (i : Fin p) (hi : m < i) : hₐ • b i ∈ S := by
    rw [hh]
    exact S.smul_mem _ (gen_mem i hi)
  have egen (i : Fin p) (hi : m < i) : eₐ • b i ∈ S := by
    have hi' : m.val < i.val := hi
    let r : Fin p := ⟨i.val - 1, by omega⟩
    rw [he i r (by dsimp [r]; omega)]
    by_cases hr : m < r
    · exact S.smul_mem _ (gen_mem r hr)
    · have hv' : i.val = m.val + 1 := by
        have : ¬ m.val < r.val := hr
        dsimp [r] at this
        omega
      rw [hv', Nat.cast_add, Nat.cast_one, sub_add_eq_add_sub, add_comm (m.val : k) 1]
      simp
  have fgen (i : Fin p) (hi : m < i) : fₐ • b i ∈ S := by
    by_cases hlast : i.val + 1 = p
    · rw [hf₀ i hlast]
      exact S.zero_mem
    · let r : Fin p := ⟨i.val + 1, by omega⟩
      rw [hf i r rfl]
      exact gen_mem r (Nat.lt_succ_of_lt hi)
  have extend (a : A) (ha : ∀ i : Fin p, m < i → a • b i ∈ S) :
      ∀ x ∈ S, a • x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ha i i.property
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact S.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_comm a c x]
      exact S.smul_mem c hx
  have pow_stable (a : A) (ha : ∀ x ∈ S, a • x ∈ S) (n : ℕ) :
      ∀ x ∈ S, a ^ n • x ∈ S := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [pow_succ', mul_smul]
      exact ha _ (ih x hx)
  -- Stability under the generators extends to all reduced PBW monomials.
  obtain ⟨d, hd⟩ := ambient_pbw (P := P) 0
  have stable (a : A) (x : Z) (hx : x ∈ S) : a • x ∈ S := by
    rw [← d.sum_equivFun a, Finset.sum_smul]
    apply Submodule.sum_mem S
    intro r _
    rw [smul_assoc, hd, mul_smul, mul_smul]
    exact S.smul_mem _ (pow_stable fₐ (extend fₐ fgen) _ _
      (pow_stable hₐ (extend hₐ hgen) _ _ (pow_stable eₐ (extend eₐ egen) _ _ hx)))
  let T : Submodule A Z :=
    { carrier := S
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      smul_mem' := stable }
  have hle : tailValue b m ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact gen_mem i i.property
  refine le_antisymm (fun x hx => hle hx) (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem basis_mem_of_coord_ne_zero (hp : 2 < p)
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : ZeroBasisActions b m)
    {N : Submodule A Z} {x : Z} (hx : x ∈ N) (i : Fin p) (hi : b.repr x i ≠ 0) :
    b i ∈ N := by
  classical
  let μ (r : Fin p) : k := (m.val : k) - 2 * (r.val : k)
  have htwo : (2 : k) ≠ 0 := by
    simpa using (show ((2 : ℕ) : k) ≠ (0 : ℕ) from fun hh =>
      (by omega : (2 : ℕ) ≠ 0) (CharP.natCast_injOn_Iio (R := k) p hp
        (Nat.zero_lt_of_lt hp) hh))
  have hμ : Function.Injective μ := by
    intro r s hrs
    exact finCast_injective (mul_left_cancel₀ htwo (sub_right_inj.mp hrs))
  -- Evaluation at the Cartan generator kills every other weight component.
  let q : k[X] := ∏ r ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (μ r))
  have hqi : q.eval (μ i) ≠ 0 := by
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun r hr => sub_ne_zero.mpr
      (fun h => (Finset.mem_erase.mp hr).1 (hμ h).symm))
  have hqr (r : Fin p) (hr : r ≠ i) : q.eval (μ r) = 0 := by
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) (sub_self _)
  let action : A →ₐ[k] Module.End k Z := Algebra.lsmul k k Z
  have hproj : (Polynomial.aeval (action hₐ) q) x ∈ N := by
    rw [Polynomial.aeval_algHom_apply]
    exact N.smul_mem (Polynomial.aeval hₐ q) hx
  have hval : (Polynomial.aeval (action hₐ) q) x =
      (b.repr x i * q.eval (μ i)) • b i := by
    conv_lhs => arg 2; rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    have weight_action (r : Fin p) : (action hₐ) (b r) = μ r • b r := hb.2.1 r
    simp_rw [Module.End.aeval_apply_of_mem_apply_eq_smul (p := q) (weight_action _), smul_smul]
    exact Finset.sum_eq_single i (fun r _ hr => by rw [hqr r hr, mul_zero, zero_smul])
      (fun h => (h (Finset.mem_univ i)).elim)
  rw [hval] at hproj
  exact ((N.restrictScalars k).smul_mem_iff (mul_ne_zero hi hqi)).mp hproj

private theorem eq_top_of_basis_mem
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : ZeroBasisActions b m)
    {N : Submodule A Z} {i : Fin p} (hi : i ≤ m) (hbi : b i ∈ N) : N = ⊤ := by
  obtain ⟨hv, _, _, he, _, _⟩ := hb
  let z : Fin p := ⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩
  have lower (n : ℕ) : ∀ r : Fin p, r.val = n → r ≤ m → b r ∈ N → b z ∈ N := by
    induction n with
    | zero =>
      intro r hr _ hbr
      rwa [show r = z from Fin.ext hr] at hbr
    | succ n ih =>
      intro r hr hrm hbr
      let s : Fin p := ⟨n, by omega⟩
      apply ih s rfl (show s.val ≤ m.val by have : r.val ≤ m.val := hrm; dsimp [s]; omega)
      have hcoef : (r.val : k) * ((m.val : k) - (r.val : k) + 1) ≠ 0 := by
        apply mul_ne_zero
        · intro hz
          have : r = z := finCast_injective (by simpa [z] using hz)
          have hz' := congrArg Fin.val this
          dsimp [z] at hz'
          omega
        · have hrm' : r.val ≤ m.val := hrm
          have hle : m.val - r.val + 1 < p := by omega
          have hcast : (((m.val - r.val + 1 : ℕ) : k)) ≠ 0 := by
            intro hz
            have heq : m.val - r.val + 1 = 0 :=
              CharP.natCast_injOn_Iio (R := k) p hle z.isLt (by simpa using hz)
            omega
          simpa [Nat.cast_add, Nat.cast_sub hrm'] using hcast
      have hm := N.smul_mem eₐ hbr
      rw [he r s hr] at hm
      exact ((N.restrictScalars k).smul_mem_iff hcoef).mp hm
  have hz := lower i.val i rfl hi hbi
  have hhighest : highest j θ ∈ N := by simpa [hv, z] using hz
  have hall (r : Fin p) : b r ∈ N := by rw [hv]; exact N.smul_mem _ hhighest
  apply (Submodule.restrictScalars_eq_top_iff k A Z).mp
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)

private theorem le_tail_of_ne_top (hp : 2 < p)
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : ZeroBasisActions b m)
    (N : Submodule A Z) (hN : N ≠ ⊤) : N ≤ tailValue b m := by
  classical
  intro x hx
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : m < i
  · exact ((tailValue b m).restrictScalars k).smul_mem _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · have hc : b.repr x i = 0 := by
      by_contra hn
      exact hN (eq_top_of_basis_mem hb (le_of_not_gt hi) (basis_mem_of_coord_ne_zero hp hb hx i hn))
    simp [hc]

private theorem tail_properties (hp : 2 < p)
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : ZeroBasisActions b m) :
    TailQuotientProperties b m := by
  classical
  let T := tailValue b m
  have hspan := tail_restrictScalars hb
  have hdim : Module.finrank k (simpleQuotientValue b m) = m.val + 1 := by
    let : Module.Finite k Z := Module.Finite.of_basis b
    change Module.finrank k (Z ⧸ T) = _
    rw [Submodule.finrank_quotient]
    have ht : Module.finrank k T = p - 1 - m.val := by
      change Module.finrank k (T.restrictScalars k) = _
      have hind : LinearIndependent k (fun i : Set.Ioi m => b i) :=
        b.linearIndependent.comp _ Subtype.val_injective
      rw [hspan, finrank_span_eq_card hind, Fintype.card_Ioi, Fin.card_Ioi]
    rw [ht, Module.finrank_eq_card_basis b, Fintype.card_fin]
    have := m.isLt
    omega
  have hproper : T ≠ ⊤ := by
    intro ht
    have hzero : Module.finrank k (Z ⧸ T) = 0 := by
      rw [ht]
      exact Module.finrank_zero_of_subsingleton
    change Module.finrank k (Z ⧸ T) = m.val + 1 at hdim
    omega
  have hmax := le_tail_of_ne_top hp hb
  refine ⟨hspan, ?_, hmax, ?_, hdim⟩
  · intro hm
    apply (Submodule.restrictScalars_eq_bot_iff k A Z).mp
    rw [hspan]
    have hS : Set.range (fun i : Set.Ioi m => b i) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨i, _⟩
      have h₁ : m.val < i.val.val := i.property
      have h₂ := i.val.isLt
      omega
    rw [hS, Submodule.span_empty]
  · apply isSimpleModule_iff_isCoatom.mpr
    exact ⟨hproper, fun N hN => by
      by_contra hn
      exact (not_lt_of_ge (hmax N hn)) hN⟩

private theorem unique_simple_quotient
    {b : Module.Basis (Fin p) k Z} {m : Fin p} (hb : TailQuotientProperties b m)
    {V : Type w} [AddCommGroup V] [Module A V] [IsSimpleModule A V]
    (f : Z →ₗ[A] V) (hf : Function.Surjective f) :
    ∃ e : simpleQuotientValue b m ≃ₗ[A] V, ∀ x, e ((tailValue b m).mkQ x) = f x := by
  have hker := f.isCoatom_ker_of_surjective hf
  have ht := isSimpleModule_iff_isCoatom.mp hb.2.2.2.1
  have h := eq_of_le_of_not_lt (hb.2.2.1 _ hker.1)
    (fun hlt => ht.1 (hker.2 _ hlt))
  refine ⟨(Submodule.quotEquivOfEq _ _ h.symm).trans (f.quotKerEquivOfSurjective hf), ?_⟩
  intro x
  exact f.quotKerEquivOfSurjective_apply_mk hf x

end BabyVerma

theorem babyVermaZero : babyVermaZeroType.{u, w} := by
  classical
  intro k _ _ p _ hp
  let : NeZero p := ⟨by omega⟩
  intro P hP
  obtain ⟨Q, j, hQ, hj, hinj, _, θ', hθ', hsurj⟩ :=
    BabyVermaQuotients.babyVermaQuotients.{u, w} hp P hP 0 (by simp)
  let W := {a : k // a ^ p - a = (0 : Model k →ₗ[k] k) (H k) ^ p}
  let root (m : Fin p) : W := ⟨m.val, by
    simpa [NeZero.ne p] using (primeFieldRoots hp (m.val : k)).mpr
      ⟨m, rfl, fun n h => finCast_injective h.symm⟩⟩
  let θ (m : Fin p) := θ' (root m)
  let b (m : Fin p) : Module.Basis (Fin p) k (BabyVerma j (θ m)) :=
    Classical.choose (hθ' (root m)).2.1
  have hacts (m : Fin p) : ZeroBasisActions (b m) m := by
    have h := Classical.choose_spec (hθ' (root m)).2.1
    simpa [ZeroBasisActions, b, θ, root, NeZero.ne p] using h
  have htail (m : Fin p) : TailQuotientProperties (b m) m := tail_properties hp (hacts m)
  have hdistinct (m n : Fin p)
      (h : Nonempty (simpleQuotientValue (b m) m ≃ₗ[ZeroAmbient P] simpleQuotientValue (b n) n)) :
      m = n := by
    obtain ⟨e⟩ := h
    have he := (e.restrictScalars k).finrank_eq
    rw [(htail m).2.2.2.2, (htail n).2.2.2.2] at he
    exact Fin.ext (by omega)
  refine ⟨Q, j, hQ, hj, hinj, θ, b, fun m => ⟨(hθ' (root m)).1, hacts m, htail m⟩, hdistinct, ?_⟩
  intro V _ _ _
  have hu (m : Fin p) (f : BabyVerma j (θ m) →ₗ[ZeroAmbient P] V)
      (hf : Function.Surjective f) :=
    unique_simple_quotient (htail m) f hf
  refine ⟨hu, ?_⟩
  obtain ⟨a, f, hf⟩ := hsurj V
  have ha : a.val ^ p - a.val = 0 := by simpa [NeZero.ne p] using a.property
  obtain ⟨m, hm, _⟩ := (primeFieldRoots hp a.val).mp ha
  have hr : a = root m := Subtype.ext hm
  subst a
  obtain ⟨iso, _⟩ := hu m f hf
  refine ⟨m, ⟨iso⟩, ?_⟩
  rintro n ⟨e⟩
  exact hdistinct n m ⟨e.trans iso.symm⟩

end LieNotes.SuperRestricted.BabyVermaZero
