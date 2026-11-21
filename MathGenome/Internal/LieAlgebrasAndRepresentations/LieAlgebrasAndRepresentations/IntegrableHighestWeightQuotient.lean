import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient

open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open UniversalEnvelopingAlgebra (ι)
open LieModule (toEnd)
open scoped Classical TensorProduct

open private highestVector_mem_weight tensorClass_eq_smul from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

universe u

abbrev relationSubmodule := @relationSubmodule_value
abbrev quotient := @quotient_value
abbrev rankOne := @rankOne_value

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

section Verma

variable [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
variable (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)

local notation "M" => induced_value H φ χ
local notation "v₀" => highestVector_value H φ χ

local instance : LieRingModule L M := inducedLieRingModule H φ χ
local instance : LieModule ℂ L M := inducedLieModule H φ χ

variable {lam : Module.Dual ℂ H} (hd : IsDominant H φ lam)
variable {e f : simple H φ → L}

theorem simpleCoordinate_eq (i : simple H φ) :
    lam (coroots H φ i) = (simpleCoordinate H φ hd i : ℂ) :=
  Classical.choose_spec (show ∃ n : ℕ, lam (coroots H φ i) = (n : ℂ) from hd i)

private theorem highest_killed (hχ : IsWeightCharacter H φ lam χ)
    (he : ∀ i, e i ∈ rootSpace H i.val) (i : simple H φ) :
    ⁅e i, v₀⁆ = 0 := by
  let ep : positive_value H φ := ⟨e i, LieSubalgebra.subset_lieSpan
    ⟨i.val, i.property.1.2, he i⟩⟩
  let eb := LieSubalgebra.inclusion (show positive_value H φ ≤ borel_value H φ from le_sup_right) ep
  have hι : envelopingMap (borel_value H φ).incl (ι ℂ eb) = ι ℂ (e i) :=
    UniversalEnvelopingAlgebra.lift_ι_apply _ _ _
  change ι ℂ (e i) • v₀ = 0
  rw [← hι, ← tensorClass_eq_smul]
  have hh := VermaModules.tensor_balanced H φ χ 1 (ι ℂ eb) 1
  rw [one_mul, mul_one] at hh
  rw [hh, hχ.2 ep]
  change (balance H φ χ).mkQ (_ ⊗ₜ[ℂ] (0 : ℂ)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

private theorem power_smul_eq (x : L) (n : ℕ) (m : M) :
    (ι ℂ x) ^ n • m = (toEnd ℂ L M x ^ n) m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_smul, Module.End.mul_apply, ih]
    rfl

private theorem pow_shift {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule L V] [LieModule ℂ L V] {a μ : Module.Dual ℂ H} {x : L} {v : V}
    (hx : x ∈ rootSpace H a) (hv : v ∈ weightSpace_value V H μ) (n : ℕ) :
    (toEnd ℂ L V x ^ n) v ∈ weightSpace_value V H (μ + n • a) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]
    exact HighestWeight.root_action V H a (μ + n • a) x _ hx ih

variable [H.IsCartanSubalgebra]

private theorem coroot_eval (hss : IsSemisimple_value ℂ L) (i : simple H φ) :
    i.val (coroots H φ i) = 2 := by
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  change i.val (killingCoroot H i.val) = 2
  rw [killingCoroot_pairing hss H hH]
  exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH i.val i.property.1.1)

theorem isSl2Triple (hss : IsSemisimple_value ℂ L) (hef : Normalized H φ e f)
    (i : simple H φ) : IsSl2Triple (coroots H φ i : L) (e i) (f i) where
  h_ne_zero := by
    intro hzero
    have hzero' : coroots H φ i = 0 := Subtype.ext hzero
    have h := coroot_eval H φ hss i
    rw [hzero', map_zero] at h
    norm_num at h
  lie_e_f := (hef i).2.2.2.2
  lie_h_e_nsmul := by
    rw [(mem_rootSpace H i.val (e i)).mp (hef i).1 (coroots H φ i), coroot_eval H φ hss i]
    simp only [two_smul]
  lie_h_f_nsmul := by
    rw [(mem_rootSpace H (-i.val) (f i)).mp (hef i).2.1 (coroots H φ i),
      LinearMap.neg_apply, coroot_eval H φ hss i]
    simp only [two_smul, neg_smul]

end Verma

section LocalActions

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

private theorem pow_apply_zero_of_le (A : Module.End ℂ V) {x : V} {m n : ℕ}
    (hm : (A ^ m) x = 0) (hmn : m ≤ n) : (A ^ n) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m d, pow_add, Module.End.mul_apply, hm, map_zero]

/-- A locally nilpotent vector for `x` stays locally nilpotent after applying
`y` if a power of `ad x` kills `y`. -/
private theorem pow_lie_eq_zero (x y : L) (v : V) (k n : ℕ)
    (hy : (LieAlgebra.ad ℂ L x ^ k) y = 0)
    (hv : (toEnd ℂ L V x ^ n) v = 0) :
    (toEnd ℂ L V x ^ (k + n)) ⁅y, v⁆ = 0 := by
  induction k generalizing y v n with
  | zero =>
    have : y = 0 := by simpa using hy
    simp [this]
  | succ k ihk =>
    induction n generalizing v with
    | zero =>
      have : v = 0 := by simpa using hv
      simp [this]
    | succ n ihn =>
      rw [show k + 1 + (n + 1) = k + 1 + n + 1 by omega, pow_succ, Module.End.mul_apply, LieModule.toEnd_apply_apply, leibniz_lie, map_add]
      have hy' : (LieAlgebra.ad ℂ L x ^ k) ⁅x, y⁆ = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using hy
      have hv' : (toEnd ℂ L V x ^ n) ⁅x, v⁆ = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, LieModule.toEnd_apply_apply] using hv
      have hfirst := ihk ⁅x, y⁆ v (n + 1) hy' hv
      rw [show k + (n + 1) = k + 1 + n by omega] at hfirst
      rw [hfirst, ihn ⁅x, v⁆ hv', add_zero]

private def nilpotentVectors (x : L) (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) :
    LieSubmodule ℂ L V where
  carrier := {v | ∃ n : ℕ, (toEnd ℂ L V x ^ n) v = 0}
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro v w ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by
      rw [map_add, pow_apply_zero_of_le _ ha (le_max_left _ _),
        pow_apply_zero_of_le _ hb (le_max_right _ _), add_zero]⟩
  smul_mem' := by
    rintro c v ⟨a, ha⟩
    exact ⟨a, by rw [map_smul, ha, smul_zero]⟩
  lie_mem := by
    rintro y v ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hx
    exact ⟨k + n, pow_lie_eq_zero x y v k n (by simp [hk]) hn⟩

private theorem rankOne_weightVector {h e f : L} (t : IsSl2Triple h e f)
    (v : V) (μ : ℂ) (hv : ⁅h, v⁆ = μ • v)
    (he : ∀ w : V, ∃ n : ℕ, (toEnd ℂ L V e ^ n) w = 0)
    (hf : ∀ w : V, ∃ n : ℕ, (toEnd ℂ L V f ^ n) w = 0) :
    ∃ S : LieSubmodule ℂ (t.toLieSubalgebra ℂ) V, v ∈ S ∧ FiniteDimensional ℂ S := by
  classical
  let E := toEnd ℂ L V e
  let F := toEnd ℂ L V f
  let word (p : ℕ × ℕ) := (F ^ p.1) ((E ^ p.2) v)
  let P := Submodule.span ℂ (Set.range word)
  have hword (a b : ℕ) : word (a, b) ∈ P := Submodule.subset_span ⟨(a, b), rfl⟩
  have hF (w : V) (hw : w ∈ P) : ⁅f, w⁆ ∈ P := by
    refine (Submodule.span_le.mpr ?_ : P ≤ P.comap F) hw
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change F (word (a, b)) ∈ P
    have h := hword (a + 1) b
    simpa only [word, pow_succ', Module.End.mul_apply] using h
  have hH (w : V) (hw : w ∈ P) : ⁅h, w⁆ ∈ P := by
    refine (Submodule.span_le.mpr ?_ : P ≤ P.comap (toEnd ℂ L V h)) hw
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change ⁅h, word (a, b)⁆ ∈ P
    have hE := t.lie_h_pow_toEnd_e hv b
    change ⁅h, (E ^ b) v⁆ = _ at hE
    have hneg : ⁅-h, (E ^ b) v⁆ = -(μ + 2 * (b : ℂ)) • (E ^ b) v := by
      rw [neg_lie, hE, neg_smul]
    have hFE := t.symm.lie_h_pow_toEnd_e hneg a
    change ⁅-h, word (a, b)⁆ = _ at hFE
    rw [neg_lie] at hFE
    rw [← neg_neg ⁅h, word (a, b)⁆, hFE, ← neg_smul]
    exact P.smul_mem _ (hword a b)
  -- The commutator moves a raising operator past a lowering factor.
  have hEword (a b : ℕ) : ⁅e, word (a, b)⁆ ∈ P := by
    induction a with
    | zero =>
      simpa only [word, pow_zero, Module.End.one_apply, pow_succ', Module.End.mul_apply,
        E, LieModule.toEnd_apply_apply] using hword 0 (b + 1)
    | succ a ih =>
      change ⁅e, (F ^ (a + 1)) ((E ^ b) v)⁆ ∈ P
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply, leibniz_lie, t.lie_e_f]
      exact P.add_mem (hH _ (hword a b)) (hF _ ih)
  have hE (w : V) (hw : w ∈ P) : ⁅e, w⁆ ∈ P := by
    refine (Submodule.span_le.mpr ?_ : P ≤ P.comap E) hw
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact hEword a b
  let S : LieSubmodule ℂ (t.toLieSubalgebra ℂ) V :=
    { P with
      lie_mem := fun {x w} hw => by
        obtain ⟨a, b, c, hxyz⟩ := (IsSl2Triple.mem_toLieSubalgebra_iff (R := ℂ)).mp x.property
        change ⁅(x : L), w⁆ ∈ P
        rw [hxyz, t.lie_e_f]
        simp only [add_lie, smul_lie]
        exact P.add_mem (P.add_mem (P.smul_mem a (hE w hw)) (P.smul_mem b (hF w hw)))
          (P.smul_mem c (hH w hw)) }
  refine ⟨S, ?_, ?_⟩
  · change v ∈ P
    simpa [word] using hword 0 0
  · -- The raising bound leaves only finitely many vectors to lower.
    obtain ⟨B, hB⟩ := he v
    choose A hA using fun b : Fin B => hf ((E ^ (b : ℕ)) v)
    let bounded (p : Σ b : Fin B, Fin (A b)) := word (p.2.val, p.1.val)
    apply Module.Finite.span_of_finite
    refine ((Set.finite_range bounded).insert 0).subset ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    by_cases hb : b < B
    · let b' : Fin B := ⟨b, hb⟩
      by_cases ha : a < A b'
      · exact Set.mem_insert_of_mem _ ⟨⟨b', ⟨a, ha⟩⟩, rfl⟩
      · have hz : word (a, b) = 0 := pow_apply_zero_of_le F (hA b') (Nat.le_of_not_gt ha)
        rw [hz]
        exact Set.mem_insert _ _
    · have hz : (E ^ b) v = 0 := pow_apply_zero_of_le E hB (Nat.le_of_not_gt hb)
      change (F ^ a) ((E ^ b) v) ∈ _
      rw [hz, map_zero]
      exact Set.mem_insert _ _

private theorem rankOne_allVectors (H : LieSubalgebra ℂ L) {h : H} {e f : L}
    (t : IsSl2Triple (h : L) e f) [DecidableEq (Module.Dual ℂ H)]
    (hW : DirectSum.IsInternal (weightSpace_value V H))
    (he : ∀ w : V, ∃ n : ℕ, (toEnd ℂ L V e ^ n) w = 0)
    (hf : ∀ w : V, ∃ n : ℕ, (toEnd ℂ L V f ^ n) w = 0)
    (v : V) : ∃ S : LieSubmodule ℂ (t.toLieSubalgebra ℂ) V, v ∈ S ∧ FiniteDimensional ℂ S := by
  let K := t.toLieSubalgebra ℂ
  let D : Submodule ℂ V :=
    { carrier := {w | ∃ S : LieSubmodule ℂ K V, w ∈ S ∧ FiniteDimensional ℂ S}
      zero_mem' := ⟨⊥, zero_mem _, by
        change FiniteDimensional ℂ (⊥ : Submodule ℂ V)
        infer_instance⟩
      add_mem' := by
        rintro x y ⟨S, hx, hS⟩ ⟨T, hy, hT⟩
        refine ⟨S ⊔ T, (S ⊔ T).add_mem
          ((show S ≤ S ⊔ T from le_sup_left) hx) ((show T ≤ S ⊔ T from le_sup_right) hy), ?_⟩
        change FiniteDimensional ℂ (S ⊔ T).toSubmodule
        rw [LieSubmodule.sup_toSubmodule]
        haveI : FiniteDimensional ℂ S.toSubmodule := hS
        haveI : FiniteDimensional ℂ T.toSubmodule := hT
        infer_instance
      smul_mem' := by
        rintro c x ⟨S, hx, hS⟩
        exact ⟨S, S.smul_mem c hx, hS⟩ }
  have hD : (⨆ μ, weightSpace_value V H μ) ≤ D := iSup_le fun μ w hw =>
    rankOne_weightVector t w (μ h) ((HighestWeight.mem_weightSpace V H μ w).mp hw h) he hf
  rw [hW.submodule_iSup_eq_top] at hD
  exact hD (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))

end LocalActions


section Quotient

variable [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)
variable (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
variable {lam : Module.Dual ℂ H} (hd : IsDominant H φ lam)
variable {e f : simple H φ → L}

local notation "M" => induced_value H φ χ
local notation "v₀" => highestVector_value H φ χ
local notation "N" => relationSubmodule_value H φ χ hd f
local notation "Q" => quotient_value H φ χ hd f
local notation "q" => LieSubmodule.Quotient.mk' N
local notation "vQ" => highestClass H φ χ hd f

local instance : LieRingModule L M := inducedLieRingModule H φ χ
local instance : LieModule ℂ L M := inducedLieModule H φ χ

private theorem enveloping_mem (S : LieSubmodule ℂ L M) (a : U L) (w : M) (hw : w ∈ S) :
    a • w ∈ S := by
  induction a using _root_.Shared.Lie.enveloping_induction ℂ L generalizing w with
  | scalar c =>
    rw [algebraMap_smul]
    exact S.smul_mem c hw
  | generator x => exact S.lie_mem (x := x) hw
  | mul a b ha hb =>
    rw [mul_smul]
    exact ha _ (hb _ hw)
  | add a b ha hb =>
    rw [add_smul]
    exact S.add_mem (ha _ hw) (hb _ hw)

private theorem map_weight {V V' : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V]
    [LieModule ℂ L V] [AddCommGroup V'] [Module ℂ V'] [LieRingModule L V'] [LieModule ℂ L V']
    (g : V →ₗ⁅ℂ,L⁆ V') (μ : Module.Dual ℂ H) {w : V}
    (hw : w ∈ weightSpace_value V H μ) : g w ∈ weightSpace_value V' H μ := by
  apply (HighestWeight.mem_weightSpace V' H μ _).mpr
  intro h
  rw [← g.map_lie, (HighestWeight.mem_weightSpace V H μ w).mp hw h, map_smul]

private theorem cone_nonneg {a : Module.Dual ℂ H}
    (ha : a ∈ positiveRootCone_value (fun i : simple H φ => i.val)) : 0 ≤ φ a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact i.property.1.2.le
  | zero => simp
  | add a b ha hb h₁ h₂ =>
    rw [map_add]
    exact add_nonneg h₁ h₂
  | smul n a ha h =>
    rw [map_nsmul]
    exact nsmul_nonneg h _

private theorem singular (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hχ : IsWeightCharacter H φ lam χ) (hef : Normalized H φ e f) (i j : simple H φ) :
    ⁅e j, (ι ℂ (f i)) ^ (simpleCoordinate H φ hd i + 1) • v₀⁆ = 0 := by
  classical
  rw [power_smul_eq]
  have he₀ := highest_killed H φ χ hχ (fun i => (hef i).1)
  by_cases hij : j = i
  · subst j
    let t := isSl2Triple H φ hss hef i
    obtain ⟨_, _, hv₀⟩ := VermaModules.induced_free hss H φ hφ χ
    have hh := (HighestWeight.mem_weightSpace M H lam v₀).mp
      (highestVector_mem_weight H φ χ lam hχ) (coroots H φ i)
    have hp : IsSl2Triple.HasPrimitiveVectorWith t v₀ (simpleCoordinate H φ hd i : ℂ) :=
      ⟨hv₀, (simpleCoordinate_eq H φ hd i) ▸ hh, he₀ i⟩
    simpa using hp.lie_e_pow_succ_toEnd_f (simpleCoordinate H φ hd i)
  · have hH := RealRootSpace.cartan_isMaximalToral hss H
    obtain ⟨_, _, hrel, _, _⟩ := _root_.LieAlgebrasAndRepresentations.serre_relations
      hss H hH φ hφ e f hef
    have hx : ⁅e j, f i⁆ = 0 := by simpa [hij] using (hrel j i).2.2.2
    generalize simpleCoordinate H φ hd i + 1 = n
    induction n with
    | zero => simpa using he₀ j
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply, leibniz_lie, hx, ih]
      simp

private theorem highest_line (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hχ : IsWeightCharacter H φ lam χ) (hef : Normalized H φ e f) :
    vQ ≠ 0 ∧ weightSpace_value Q H lam = ℂ ∙ vQ ∧
      DirectSum.IsInternal (weightSpace_value Q H) := by
  classical
  let W := weightSpace_value M H
  have hW := VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ
  let p : M →ₗ[ℂ] W lam :=
    (DirectSum.component ℂ (Module.Dual ℂ H) (fun μ => W μ) lam).comp
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW.1).symm.toLinearMap
  have hp (μ : Module.Dual ℂ H) {w : M} (hw : w ∈ W μ) (hne : μ ≠ lam) :
      p w = 0 := hW.1.ofBijective_coeLinearMap_of_mem_ne hne hw
  let low (i : simple H φ) := lam - (simpleCoordinate H φ hd i + 1) • i.val
  let relation (i : simple H φ) := (ι ℂ (f i)) ^ (simpleCoordinate H φ hd i + 1) • v₀
  have hlow (i : simple H φ) : φ (low i) < φ lam := by
    change φ (lam - (simpleCoordinate H φ hd i + 1) • i.val) < φ lam
    rw [map_sub, map_nsmul, sub_lt_self_iff]
    exact nsmul_pos i.property.1.2 (by omega)
  have hwrel (i : simple H φ) : relation i ∈ W (low i) := by
    change (ι ℂ (f i)) ^ (simpleCoordinate H φ hd i + 1) • v₀ ∈ W (low i)
    rw [power_smul_eq]
    simpa only [low, sub_eq_add_neg, smul_neg] using
      pow_shift H (hef i).2.1 (highestVector_mem_weight H φ χ lam hχ)
        (simpleCoordinate H φ hd i + 1)
  -- Each relation vector is the image of a lower-weight Verma highest vector.
  choose χ' hχ' using fun i : simple H φ =>
    (VermaModules.character_existsUnique hss H φ hφ (low i)).exists
  let M' (i : simple H φ) := induced_value H φ (χ' i)
  letI ring' (i : simple H φ) : LieRingModule L (M' i) := inducedLieRingModule H φ (χ' i)
  letI lie' (i : simple H φ) : LieModule ℂ L (M' i) := inducedLieModule H φ (χ' i)
  have hmorph (i : simple H φ) : ∃ g : M' i →ₗ⁅ℂ,L⁆ M,
      g (highestVector_value H φ (χ' i)) = relation i :=
    (VermaWeightsUniversal.verma_universal hss H φ hφ (low i) (χ' i) (hχ' i)
      e (fun j => ⟨(hef j).1, (hef j).2.2.1⟩) M (relation i)
      ((HighestWeight.mem_weightSpace M H (low i) _).mp (hwrel i))
      (singular H φ χ hd hss hφ hχ hef i)).1.exists
  choose g hg using hmorph
  -- The top-weight projection kills each of these images.
  have hrange (i : simple H φ) : (g i).range.toSubmodule ≤ LinearMap.ker p := by
    change LinearMap.range (g i).toLinearMap ≤ LinearMap.ker p
    rw [LinearMap.range_le_iff_comap]
    have hVi := VermaWeightsUniversal.verma_weights hss H φ hφ (low i) (χ' i) (hχ' i)
    rw [eq_top_iff, ← hVi.1.submodule_iSup_eq_top]
    refine iSup_le ?_
    intro μ w hw
    change p (g i w) = 0
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hne : weightSpace_value (M' i) H μ ≠ ⊥ := by
        intro hbot
        change w ∈ weightSpace_value (M' i) H μ at hw
        rw [hbot] at hw
        exact hw0 (by simpa using hw)
      have hcone := (hVi.2.2.1 μ).mp hne
      have hnn := cone_nonneg H φ hcone
      have hμ : μ ≠ lam := by
        intro heq
        rw [heq, map_sub] at hnn
        linarith [hlow i]
      exact hp μ (map_weight H (g i) μ hw) hμ
  let S : LieSubmodule ℂ L M := ⨆ i, (g i).range
  have hS : S.toSubmodule ≤ LinearMap.ker p := by
    rw [show S.toSubmodule = ⨆ i, (g i).range.toSubmodule from LieSubmodule.iSup_toSubmodule _]
    exact iSup_le hrange
  have hNS : (N).toSubmodule ≤ S.toSubmodule := by
    intro w hw
    change w ∈ Submodule.span (U L) (Set.range relation) at hw
    change w ∈ S
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact (le_iSup (fun i => (g i).range) i) ⟨_, hg i⟩
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => exact enveloping_mem H φ χ S a x hx
  have hv₀ := highestVector_mem_weight H φ χ lam hχ
  have hvQ : vQ ≠ 0 := by
    intro hz
    have hvN : v₀ ∈ N := (LieSubmodule.Quotient.mk_eq_zero N).mp hz
    have hpv : p v₀ = 0 := hS (hNS hvN)
    have hpid : p v₀ = ⟨v₀, hv₀⟩ := hW.1.ofBijective_coeLinearMap_of_mem hv₀
    obtain ⟨_, _, hne⟩ := VermaModules.induced_free hss H φ hφ χ
    exact hne (congrArg Subtype.val (hpid.symm.trans hpv))
  haveI : IsLieAbelian H := (RealRootSpace.cartan_isMaximalToral hss H).1.1
  have hquot := WeightSubmodules.weight_submodules ((N).restr H) hW.1
  refine ⟨hvQ, ?_, hquot.2.1⟩
  have hmap : weightSpace_value Q H lam = (W lam).map (q).toLinearMap := by
    apply le_antisymm
    · intro w hw
      obtain ⟨E, hE⟩ := hquot.2.2 lam
      obtain ⟨z, hz⟩ := E.surjective ⟨w, hw⟩
      obtain ⟨x, rfl⟩ := (((N).restr H).toSubmodule.comap (W lam).subtype).mkQ_surjective z
      refine ⟨x, x.property, ?_⟩
      exact (hE x).symm.trans (congrArg Subtype.val hz)
    · rintro w ⟨v, hvm, rfl⟩
      exact map_weight H q lam hvm
  rw [hmap]
  change (weightSpace_value M H lam).map (q).toLinearMap = ℂ ∙ vQ
  rw [hW.2.2.2, Submodule.map_span, Set.image_singleton]
  rfl

private theorem locallyNilpotent_on_quotient (x : L)
    (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) (hcyc : ∀ S : LieSubmodule ℂ L Q,
      vQ ∈ S → S = ⊤) (n : ℕ) (hn : (toEnd ℂ L Q x ^ n) vQ = 0) (w : Q) :
    ∃ k : ℕ, (toEnd ℂ L Q x ^ k) w = 0 := by
  let S : LieSubmodule ℂ L Q := nilpotentVectors x hx
  have htop := hcyc S ⟨n, hn⟩
  have hw : w ∈ S := by rw [htop]; trivial
  exact hw

theorem rankOne_eq (hss : IsSemisimple_value ℂ L) (hef : Normalized H φ e f)
    (i : simple H φ) :
    rankOne_value H φ e f i = (isSl2Triple H φ hss hef i).toLieSubalgebra ℂ := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    exact Submodule.subset_span
  · exact LieSubalgebra.submodule_span_le_lieSpan

end Quotient

theorem quotient_integrable : quotient_integrable_type.{u} := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ hd e f hef
  dsimp only
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let M := induced_value H φ χ
  let v₀ := highestVector_value H φ χ
  let N := relationSubmodule_value H φ χ hd f
  let Q := quotient_value H φ χ hd f
  let q := LieSubmodule.Quotient.mk' N
  let vQ := highestClass H φ χ hd f
  obtain ⟨hne, hline, hW⟩ := highest_line H φ χ hd hss hφ hχ hef
  obtain ⟨E, hE, _⟩ := VermaModules.induced_free hss H φ hφ χ
  have hcyc (S : LieSubmodule ℂ L Q) (hv : vQ ∈ S) : S = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N w
    obtain ⟨a, rfl⟩ := E.surjective m
    rw [hE]
    exact enveloping_mem H φ χ (S.comap q) _ v₀ hv
  have hqpow (x : L) (n : ℕ) (m : M) :
      q ((ι ℂ x) ^ n • m) = (toEnd ℂ L Q x ^ n) (q m) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ', mul_smul, Module.End.mul_apply, ← ih]
      exact q.map_lie x _
  have hloc (i : simple H φ) :
      (∀ w : Q, ∃ a : ℕ, (toEnd ℂ L Q (e i) ^ a) w = 0) ∧
      (∀ w : Q, ∃ b : ℕ, (toEnd ℂ L Q (f i) ^ b) w = 0) := by
    have hH := RealRootSpace.cartan_isMaximalToral hss H
    obtain ⟨hEad, hFad, _⟩ := RootStrings.reflection_lift hss H hH i.val i.property.1.1
      (e i) (f i) (hef i).1 (hef i).2.1 (hef i).2.2.2.2
    constructor
    · apply locallyNilpotent_on_quotient H φ χ hd (e i) hEad hcyc 1
      rw [← hqpow, pow_one]
      change q ⁅e i, v₀⁆ = 0
      rw [highest_killed H φ χ hχ (fun j => (hef j).1) i, map_zero]
    · apply locallyNilpotent_on_quotient H φ χ hd (f i) hFad hcyc
        (simpleCoordinate H φ hd i + 1)
      rw [← hqpow]
      apply (LieSubmodule.Quotient.mk_eq_zero N).mpr
      change (ι ℂ (f i)) ^ (simpleCoordinate H φ hd i + 1) • v₀ ∈
        Submodule.span (U L) (Set.range fun j =>
          (ι ℂ (f j)) ^ (simpleCoordinate H φ hd j + 1) • v₀)
      exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨hne, hline, hW, ?_, ?_⟩
  · intro i w
    obtain ⟨a, ha⟩ := (hloc i).1 w
    obtain ⟨b, hb⟩ := (hloc i).2 w
    exact ⟨a, b, ha, hb⟩
  · intro i w
    let P (K : LieSubalgebra ℂ L) : Prop :=
      ∃ S : LieSubmodule ℂ K Q, w ∈ S ∧ FiniteDimensional ℂ S
    change P (rankOne_value H φ e f i)
    rw [rankOne_eq H φ hss hef i]
    exact rankOne_allVectors H (isSl2Triple H φ hss hef i) hW (hloc i).1 (hloc i).2 w

end LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
