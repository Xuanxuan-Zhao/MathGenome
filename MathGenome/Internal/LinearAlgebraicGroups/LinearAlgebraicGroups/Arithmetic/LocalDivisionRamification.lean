import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.SimpleRing.Congr
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree

noncomputable section

open scoped WithZero
open ValuativeRel WithZero RM03.CSA

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification

universe u v z

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]
  {κ : Type z} [Field κ] [Algebra (BaseResidue F) κ] {w : Valuation B ℤᵐ⁰} {n : ℕ}

private theorem normalized_surjective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (normalizedValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    (valuation_surjective (K := K))

private theorem normalized_le (a b : F) :
    normalizedValuation F a ≤ normalizedValuation F b ↔ valuation F a ≤ valuation F b :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.le_iff_le

private theorem normalized_mem (a : F) : normalizedValuation F a ≤ 1 ↔ a ∈ Integers F := by
  rw [← map_one (normalizedValuation F), normalized_le, map_one]
  rfl

private theorem residue_zero (a : Integers F) :
    IsLocalRing.residue _ a = 0 ↔ normalizedValuation F (a : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  change valuation F (a : F) < 1 ↔ e (valuation F (a : F)) < 1
  rw [← map_one e]
  exact e.toOrderIso.lt_iff_lt.symm

private def scalarInteger (r : IntegralReduction (F := F) n w κ) : Integers F →+* w.integer :=
  ((algebraMap F B).comp (valuation F).valuationSubring.subtype).codRestrict w.integer (by
    intro a
    change w (algebraMap F B (a : F)) ≤ 1
    rw [r.scalar_value]
    exact pow_le_one₀ zero_le ((normalized_mem _).2 a.2))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem subfield_degree_le (hB : IsCentralSimple F B) {L : Type*}
    [Field L] [Algebra F L] (i : L →ₐ[F] B) : Module.finrank F L ≤ degree F B := by
  let : FiniteDimensional F B := hB.2.2
  let e : L ≃ₐ[F] i.range := AlgEquiv.ofInjective i i.injective
  have hsimple : IsSimpleRing i.range := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  let C := Subalgebra.centralizer F (i.range : Set B)
  have hle : i.range ≤ C := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hx
    exact (Commute.all b a).map i
  have hdim : Module.finrank F i.range ≤ Module.finrank F C := by
    have hsub : i.range.toSubmodule ≤ C.toSubmodule := hle
    exact Submodule.finrank_mono hsub
  have hmul := (centralizer_simple_and_finrank hB i.range hsimple).2
  change Module.finrank F i.range * Module.finrank F C = Module.finrank F B at hmul
  rw [finrank_eq_degree_sq hB] at hmul
  have hsq : Module.finrank F i.range ^ 2 ≤ degree F B ^ 2 := by
    rw [pow_two, ← hmul]
    exact Nat.mul_le_mul_left _ hdim
  rw [e.toLinearEquiv.finrank_eq]
  exact (Nat.pow_le_pow_iff_left (by decide)).1 hsq

/-- A lift of a multiplicative generator of the residue field lies in a
commutative subfield, whose integral elements then surject onto the residue field. -/
private theorem exists_subfield_onto [Finite κ] (hB : IsCentralSimple F B)
    (r : IntegralReduction (F := F) n w κ) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L), FiniteDimensional F L ∧
      ∃ i : L →ₐ[F] B, ∀ z : κ, ∃ (a : L) (x : w.integer),
        i a = (x : B) ∧ r.reduction x = z := by
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator κˣ _ _
  obtain ⟨x, hx⟩ := r.onto (α : κ)
  have hval : w (x : B) = 1 := by
    refine le_antisymm x.2 (le_of_not_gt fun hlt => ?_)
    exact α.ne_zero (hx.symm.trans ((r.ker x).2 hlt))
  have hx₀ : (x : B) ≠ 0 := by
    intro he
    simp [he] at hval
  let u : w.integerˣ :=
    { val := x
      inv := ⟨(x : B)⁻¹, by
        change w (x : B)⁻¹ ≤ 1
        rw [w.map_inv, hval, inv_one]⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hx₀)
      inv_val := Subtype.ext (inv_mul_cancel₀ hx₀) }
  let : FiniteDimensional F B := hB.2.2
  let L := Algebra.adjoin F ({(x : B)} : Set B)
  let : CommRing L :=
    { (inferInstance : Ring L) with
      mul_comm := fun a b => Subtype.ext <| (Algebra.commute_of_mem_adjoin_singleton_of_commute
        b.2 (Algebra.commute_of_mem_adjoin_self a.2).symm).eq }
  let : Field L := fieldOfFiniteDimensional F L
  let i : L →ₐ[F] B := L.val
  let y : L := ⟨x, Algebra.self_mem_adjoin_singleton F (x : B)⟩
  have hy₀ : y ≠ 0 := fun he => hx₀ (congrArg i he |>.trans (map_zero i))
  let v := Units.mk0 y hy₀
  let j := w.integer.subtype
  have he : Units.map i.toMonoidHom v = Units.map j.toMonoidHom u := Units.ext rfl
  have hρ : Units.map r.reduction.toMonoidHom u = α := Units.ext hx
  refine ⟨L, inferInstance, inferInstance, inferInstance, i, fun z => ?_⟩
  by_cases hz : z = 0
  · exact ⟨0, 0, map_zero _, by simp [hz]⟩
  obtain ⟨m, hm⟩ := hα (Units.mk0 z hz)
  have h1 : i (↑(v ^ m) : L) = (↑(↑(u ^ m) : w.integer) : B) := by
    have H := congrArg (fun b : Bˣ => (b : B)) (congrArg (fun b : Bˣ => b ^ m) he)
    rw [← map_zpow, ← map_zpow] at H
    exact H
  have h2 : r.reduction (↑(u ^ m) : w.integer) = z := by
    have H := congrArg (fun b : κˣ => (b : κ))
      ((map_zpow (Units.map r.reduction.toMonoidHom) u m).trans
        ((congrArg (fun b : κˣ => b ^ m) hρ).trans hm))
    exact H
  exact ⟨(v ^ m : Lˣ), (u ^ m : w.integerˣ), h1, h2⟩

/-- Lifts of independent residue classes have no cancellation at the largest
coefficient value. This also detects the integral coordinates of the lifts. -/
private theorem value_sum_of_residue_independent
    (r : IntegralReduction (F := F) n w κ) {ι : Type*} [Fintype ι] (x : ι → w.integer)
    (hind : LinearIndependent (BaseResidue F) (fun j => r.reduction (x j)))
    (g : ι → F) (k : ι) (hk₀ : g k ≠ 0)
    (hmax : ∀ j, valuation F (g j) ≤ valuation F (g k)) :
    w (∑ j, g j • (x j : B)) = normalizedValuation F (g k) ^ n := by
  classical
  let vf := valuation F
  let c : ι → Integers F := fun j =>
    ⟨(g k)⁻¹ * g j, by
      change vf ((g k)⁻¹ * g j) ≤ 1
      rw [map_mul, vf.map_inv, inv_mul_le_iff₀ (zero_lt_iff.mpr ((map_ne_zero vf).2 hk₀)), mul_one]
      exact hmax j⟩
  have hc : c k = 1 := Subtype.ext (inv_mul_cancel₀ hk₀)
  let y : w.integer := ∑ j, scalarInteger r (c j) * x j
  have hred : r.reduction y ≠ 0 := by
    intro hy
    change r.reduction (∑ j, scalarInteger r (c j) * x j) = 0 at hy
    rw [map_sum] at hy
    simp_rw [map_mul, r.scalar_reduction (c _) (scalarInteger r (c _)) rfl,
      ← Algebra.smul_def] at hy
    have hz := (Fintype.linearIndependent_iff.mp hind _ hy) k
    rw [hc, map_one] at hz
    exact one_ne_zero hz
  have hy : w (y : B) = 1 := le_antisymm y.2 (le_of_not_gt (fun h => hred ((r.ker y).2 h)))
  have he : g k • (y : B) = ∑ j, g j • (x j : B) := by
    change g k • w.integer.subtype (∑ j, scalarInteger r (c j) * x j) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change g k • (algebraMap F B ((g k)⁻¹ * g j) * (x j : B)) = _
    rw [← Algebra.smul_def, smul_smul, ← mul_assoc, mul_inv_cancel₀ hk₀, one_mul]
  rw [← he, Algebra.smul_def, map_mul, r.scalar_value, hy, mul_one]

private theorem independent_lifts (r : IntegralReduction (F := F) n w κ) {ι : Type*} [Fintype ι]
    (x : ι → w.integer)
    (hind : LinearIndependent (BaseResidue F) (fun j => r.reduction (x j))) :
    LinearIndependent F (fun j => (x j : B)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  by_contra hj
  have : Nonempty ι := ⟨j⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup (α := ValueGroupWithZero F)
    (Finset.univ : Finset ι) Finset.univ_nonempty (fun t => valuation F (g t))
  have hmax (t : ι) : valuation F (g t) ≤ valuation F (g k) := by
    rw [← hk]
    exact Finset.le_sup (s := Finset.univ) (f := fun t : ι => valuation F (g t)) (Finset.mem_univ t)
  have hk₀ : g k ≠ 0 := by
    intro he
    have H := hmax j
    rw [he, map_zero] at H
    exact (not_le_of_gt (zero_lt_iff.mpr ((map_ne_zero (valuation F)).2 hj))) H
  have hv := value_sum_of_residue_independent r x hind g k hk₀ hmax
  rw [hg, map_zero] at hv
  exact (pow_ne_zero _ ((map_ne_zero (normalizedValuation F)).2 hk₀)) hv.symm

private theorem residue_degree_bound [Finite κ] (hB : IsCentralSimple F B)
    (r : IntegralReduction (F := F) (degree F B) w κ) :
    Module.finrank (BaseResidue F) κ ≤ degree F B := by
  classical
  let : FiniteDimensional (BaseResidue F) κ := Module.Finite.of_finite
  let b := Module.finBasis (BaseResidue F) κ
  obtain ⟨L, hL, hAlg, hd, i, hsurj⟩ := exists_subfield_onto hB r
  let := hL
  let := hAlg
  let := hd
  choose a x hx hres using fun j => hsurj (b j)
  have hlin : LinearIndependent F (fun j => (x j : B)) := by
    apply independent_lifts r
    simp_rw [hres]
    exact b.linearIndependent
  have hlina : LinearIndependent F a := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    apply Fintype.linearIndependent_iff.mp hlin g
    have H := congrArg i.toLinearMap hg
    rw [map_sum, map_zero] at H
    simp_rw [map_smul, AlgHom.toLinearMap_apply, hx] at H
    exact H
  simpa using hlina.fintype_card_le_finrank.trans (subfield_degree_le hB i)


private def depth (j : ℕ) : ℤᵐ⁰ := exp (-(j : ℤ))

private theorem depth_one_lt_one : depth 1 < 1 := by
  change exp (-1 : ℤ) < exp 0
  simp

private theorem lt_depth_iff (a : ℤᵐ⁰) (j : ℕ) :
    a < depth j ↔ a ≤ depth (j + 1) := by
  induction a using WithZero.expRecOn with
  | zero => simp [depth]
  | exp m =>
    simp only [depth, exp_lt_exp, exp_le_exp]
    omega

/-- One residue digit cancels the term at the current depth. An unattained
depth needs no digit. -/
private theorem cancel_digit (r : IntegralReduction (F := F) n w κ)
    (lift : κ → w.integer) (hlift : ∀ a, r.reduction (lift a) = a)
    (j : ℕ) (t x : B) (ht : w t = depth j) (hx : w x ≤ depth j) :
    ∃ a, w (x - t * (lift a : B)) ≤ depth (j + 1) := by
  have ht₀ : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    exact exp_ne_zero ht.symm
  let y : w.integer := ⟨t⁻¹ * x, by
    change w (t⁻¹ * x) ≤ 1
    rw [map_mul, w.map_inv, inv_mul_le_iff₀ (zero_lt_iff.mpr ((map_ne_zero w).2 ht₀)), mul_one, ht]
    exact hx⟩
  let a := r.reduction y
  have ha : w ((y - lift a : w.integer) : B) < 1 := (r.ker _).1 (by simp [a, hlift])
  refine ⟨a, ?_⟩
  have he : t * ((y - lift a : w.integer) : B) = x - t * (lift a : B) := by
    change t * (t⁻¹ * x - (lift a : B)) = _
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ ht₀, one_mul]
  rw [← he, map_mul, ht, ← lt_depth_iff]
  simpa only [mul_one] using mul_lt_mul_of_pos_left ha (by simp [depth])

/-- The lattice coordinates reduced modulo a base uniformizer. -/
private def latticeReduction
    (b : Module.Basis (Fin (Module.finrank F B)) F B)
    (hb : ∀ x, x ∈ w.integer ↔ ∀ i, b.equivFun x i ∈ Integers F)
    (x : w.integer) (i : Fin (Module.finrank F B)) : BaseResidue F :=
  IsLocalRing.residue _ ⟨_, (hb (x : B)).1 x.2 i⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem latticeReduction_surjective
    (b : Module.Basis (Fin (Module.finrank F B)) F B)
    (hb : ∀ x, x ∈ w.integer ↔ ∀ i, b.equivFun x i ∈ Integers F) :
    Function.Surjective (latticeReduction (w := w) b hb) := by
  classical
  intro a
  choose c hc using fun j => IsLocalRing.residue_surjective (R := Integers F) (a j)
  let y : B := b.equivFun.symm (fun j => (c j : F))
  have hy : b.equivFun y = fun j => (c j : F) := b.equivFun.apply_symm_apply _
  refine ⟨⟨y, (hb y).2 (fun j => by rw [congrFun hy j]; exact (c j).2)⟩, ?_⟩
  ext j
  change IsLocalRing.residue _ (⟨b.equivFun y j, _⟩ : Integers F) = a j
  rw [show (⟨b.equivFun y j, _⟩ : Integers F) = c j from Subtype.ext (congrFun hy j), hc]

private theorem latticeReduction_eq (r : IntegralReduction (F := F) n w κ)
    (b : Module.Basis (Fin (Module.finrank F B)) F B)
    (hb : ∀ x, x ∈ w.integer ↔ ∀ i, b.equivFun x i ∈ Integers F)
    (x y : w.integer) (hxy : w ((x : B) - y) ≤ depth n) :
    latticeReduction (w := w) b hb x = latticeReduction (w := w) b hb y := by
  obtain ⟨π, hπ⟩ := normalized_surjective F (depth 1)
  have hπ₀ : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hπn : normalizedValuation F π ^ n = depth n := by
    rw [hπ]
    simp [depth, ← WithZero.exp_nsmul]
  have h : π⁻¹ • ((x : B) - y) ∈ w.integer := by
    change w (π⁻¹ • ((x : B) - y)) ≤ 1
    rw [Algebra.smul_def, map_mul, r.scalar_value, map_inv₀, inv_pow,
      inv_mul_le_iff₀ (by rw [hπn]; simp [depth]), mul_one, hπn]
    exact hxy
  ext j
  have hj := (hb _).1 h j
  let a : Integers F := ⟨_, (hb (x : B)).1 x.2 j⟩
  let c : Integers F := ⟨_, (hb (y : B)).1 y.2 j⟩
  change IsLocalRing.residue _ a = IsLocalRing.residue _ c
  rw [← sub_eq_zero, ← map_sub, residue_zero]
  have hd : ((a - c : Integers F) : F) =
      π * b.equivFun (π⁻¹ • ((x : B) - y)) j := by
    change b.equivFun (x : B) j - b.equivFun (y : B) j = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hπ₀, one_mul, map_sub,
      Pi.sub_apply]
  rw [hd, map_mul, hπ]
  exact (mul_le_of_le_one_right' ((normalized_mem _).2 hj)).trans_lt
    depth_one_lt_one

/-- Count residues of the integer lattice by successively cancelling deeper
terms. The number of indices that can contribute is at most the degree. -/
private theorem lattice_card_bound [Finite κ] (r : IntegralReduction (F := F) n w κ) :
    Nat.card (BaseResidue F) ^ Module.finrank F B ≤
      Nat.card κ ^ Nat.card {j : Fin n // ∃ t : B, w t = depth j} := by
  classical
  let A := {j : Fin n // ∃ t : B, w t = depth j}
  let t : A → B := fun j => j.2.choose
  have ht (j : A) : w (t j) = depth j := j.2.choose_spec
  let lift : κ → w.integer := fun a => (r.onto a).choose
  have hlift (a : κ) : r.reduction (lift a) = a := (r.onto a).choose_spec
  let aindex (j : ℕ) (hj : j < n ∧ ∃ x : B, w x = depth j) : A := ⟨⟨j, hj.1⟩, hj.2⟩
  have term_mem (j : A) (a : κ) : t j * (lift a : B) ∈ w.integer := by
    change w (t j * (lift a : B)) ≤ 1
    rw [map_mul, ht]
    exact (mul_le_of_le_one_right' (lift a).2).trans (by
      change exp (-(j.1.val : ℤ)) ≤ exp 0
      simp)
  let term (c : A → κ) (j : ℕ) : w.integer :=
    if hj : j < n ∧ ∃ x : B, w x = depth j then
      ⟨t (aindex j hj) * (lift (c (aindex j hj)) : B), term_mem _ _⟩ else 0
  let approximation (c : A → κ) (k : ℕ) : w.integer := ∑ j ∈ Finset.range k, term c j
  have step (c : A → κ) (k : ℕ) : approximation c (k + 1) = approximation c k + term c k :=
    Finset.sum_range_succ _ _
  have approx (x : w.integer) (k : ℕ) (hk : k ≤ n) :
      ∃ c : A → κ, w ((x : B) - (approximation c k : B)) ≤ depth k := by
    induction k with
    | zero =>
      refine ⟨fun _ => 0, ?_⟩
      have he : approximation (fun _ => 0) 0 = 0 := Finset.sum_range_zero _
      rw [he]
      change w ((x : B) - 0) ≤ 1
      rw [sub_zero]
      exact x.2
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih (Nat.le_of_succ_le hk)
      by_cases he : ∃ a : B, w a = depth k
      · have hact : k < n ∧ ∃ a : B, w a = depth k := ⟨hk, he⟩
        let j := aindex k hact
        obtain ⟨a, ha⟩ := cancel_digit r lift hlift k (t j)
          ((x : B) - (approximation c k : B)) (ht j) hc
        let c' := Function.update c j a
        have hprev : approximation c' k = approximation c k := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases h : l < n ∧ ∃ a : B, w a = depth l
          · have hne : aindex l h ≠ j := by
              intro hh
              exact (Finset.mem_range.mp hl).ne (congrArg (fun z : A => z.1.val) hh)
            simp only [term, dite_eq_left h, c', Function.update_of_ne hne]
          · simp only [term, dite_eq_right h]
        refine ⟨c', ?_⟩
        have hterm : term c' k = ⟨t j * (lift a : B), term_mem j a⟩ := by
          simp only [term, dite_eq_left hact, ← show j = aindex k hact from rfl, c', Function.update_self]
        rw [step]
        rw [hprev, hterm]
        change w ((x : B) - ((approximation c k : B) + t j * (lift a : B))) ≤ depth (k + 1)
        rwa [← sub_sub]
      · refine ⟨c, ?_⟩
        have hterm : term c k = 0 := dite_eq_right (fun h => he h.2)
        rw [step]
        rw [hterm, add_zero, ← lt_depth_iff]
        exact lt_of_le_of_ne hc (fun eq => he ⟨_, eq⟩)
  obtain ⟨b, hb⟩ := r.lattice
  let f : (A → κ) → Fin (Module.finrank F B) → BaseResidue F :=
    fun c => latticeReduction (w := w) b hb (approximation c n)
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨x, rfl⟩ := latticeReduction_surjective (w := w) b hb d
    obtain ⟨c, hc⟩ := approx x n le_rfl
    exact ⟨c, (latticeReduction_eq r b hb x (approximation c n) hc).symm⟩
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_surjective f hf

private theorem division_value_surjective_of_uniformizer
    (h : ∃ t : B, w t = depth 1) : Function.Surjective w := by
  obtain ⟨t, ht⟩ := h
  intro a
  induction a using WithZero.expRecOn with
  | zero => exact ⟨0, map_zero _⟩
  | exp j =>
    refine ⟨t ^ (-j), ?_⟩
    rw [map_zpow₀, ht, depth, ← exp_zsmul]
    congr 1
    simp

private theorem division_degrees [Finite κ] (hB : IsCentralSimple F B)
    (r : IntegralReduction (F := F) (degree F B) w κ) :
    Function.Surjective w ∧ Module.finrank (BaseResidue F) κ = degree F B := by
  classical
  let n := degree F B
  let f := Module.finrank (BaseResidue F) κ
  let q := Nat.card (BaseResidue F)
  let A := {j : Fin n // ∃ t : B, w t = depth j}
  let : FiniteDimensional (BaseResidue F) κ := Module.Finite.of_finite
  have hn : 0 < n := degree_pos hB
  let : Finite (BaseResidue F) := (localField_properties F).2.1
  have hq : 1 < q := Finite.one_lt_card
  have hf : f ≤ n := residue_degree_bound hB r
  have hA : Nat.card A ≤ n := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective (fun j : A => j.1) Subtype.val_injective
  have h := lattice_card_bound r
  have hκ : Nat.card κ = q ^ f := Module.natCard_eq_pow_finrank (K := BaseResidue F)
  rw [finrank_eq_degree_sq hB, hκ, ← pow_mul] at h
  change q ^ n ^ 2 ≤ q ^ (f * Nat.card A) at h
  have hprod := (Nat.pow_le_pow_iff_right hq).1 h
  have hfe : f = n := by
    by_contra hne
    have hlt := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hf hne) hn
    rw [← pow_two] at hlt
    exact (not_lt_of_ge hprod) (lt_of_le_of_lt (Nat.mul_le_mul_left f hA) hlt)
  have hAe : Nat.card A = n := by
    rw [hfe, pow_two] at hprod
    exact le_antisymm hA (Nat.le_of_mul_le_mul_left hprod hn)
  refine ⟨division_value_surjective_of_uniformizer ?_, hfe⟩
  by_cases hn₁ : n = 1
  · obtain ⟨a, ha⟩ := normalized_surjective F (depth 1)
    exact ⟨algebraMap F B a, by rw [r.scalar_value, ← show n = degree F B from rfl, hn₁, pow_one, ha]⟩
  · have h1n : 1 < n := by omega
    let j : Fin n := ⟨1, h1n⟩
    by_contra hnone
    have hlt := Fintype.card_subtype_lt (p := fun k : Fin n => ∃ t : B, w t = depth k) (x := j) hnone
    rw [Fintype.card_eq_nat_card, Fintype.card_fin] at hlt
    exact (ne_of_lt hlt) hAe


private theorem subfield_values [Finite κ] (hB : IsCentralSimple F B)
    (r : IntegralReduction (F := F) (degree F B) w κ)
    (hf : Module.finrank (BaseResidue F) κ = degree F B)
    {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L] (i : L →ₐ[F] B)
    (honto : ∀ z : κ, ∃ (a : L) (x : w.integer), i a = (x : B) ∧ r.reduction x = z) :
    Module.finrank F L = degree F B ∧
      ∀ a : L, ∃ c : F, w (i a) = w (algebraMap F B c) := by
  classical
  let : FiniteDimensional (BaseResidue F) κ := Module.Finite.of_finite
  let b := Module.finBasis (BaseResidue F) κ
  choose a x hx hres using fun j => honto (b j)
  have hind : LinearIndependent (BaseResidue F) (fun j => r.reduction (x j)) := by
    simp_rw [hres]
    exact b.linearIndependent
  have hlin : LinearIndependent F (fun j => (x j : B)) := independent_lifts r x hind
  have hlina : LinearIndependent F a := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    apply Fintype.linearIndependent_iff.mp hlin g
    have H := congrArg i.toLinearMap hg
    rw [map_sum, map_zero] at H
    simp_rw [map_smul, AlgHom.toLinearMap_apply, hx] at H
    exact H
  have hd : Module.finrank F L = degree F B := by
    apply le_antisymm (subfield_degree_le hB i)
    simpa [hf] using hlina.fintype_card_le_finrank
  let bL := basisOfLinearIndependentOfCardEqFinrank' a hlina (by simp [hf, hd])
  have hbL (j) : bL j = a j := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  have hsum (y : L) : i y = ∑ j, bL.equivFun y j • (x j : B) := by
    have H := congrArg i.toLinearMap (bL.sum_repr y)
    rw [map_sum] at H
    simp_rw [map_smul, AlgHom.toLinearMap_apply, hbL, hx] at H
    exact H.symm
  refine ⟨hd, fun y => ?_⟩
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let g := bL.equivFun y
  have hgn : g ≠ 0 := fun h => hy (bL.equivFun.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ 0 := by
    by_contra! h
    exact hgn (funext h)
  have : Nonempty (Fin (Module.finrank (BaseResidue F) κ)) := ⟨j⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup (α := ValueGroupWithZero F) Finset.univ
    Finset.univ_nonempty (fun t => valuation F (g t))
  have hmax (t : Fin (Module.finrank (BaseResidue F) κ)) :
      valuation F (g t) ≤ valuation F (g k) := by
    rw [← hk]
    exact Finset.le_sup (s := Finset.univ) (f := fun t => valuation F (g t)) (Finset.mem_univ t)
  have hk₀ : g k ≠ 0 := by
    intro he
    have H := hmax j
    rw [he, map_zero] at H
    exact (not_le_of_gt (zero_lt_iff.mpr ((map_ne_zero (valuation F)).2 hj))) H
  exact ⟨g k, (congrArg w (hsum y)).trans
    ((value_sum_of_residue_independent r x hind g k hk₀ hmax).trans (r.scalar_value _).symm)⟩

private theorem extension_of_comap (r : IntegralReduction (F := F) n w κ) (hn : n ≠ 0)
    {L : Type*} [Field L] [Algebra F L] (i : L →ₐ[F] B) :
    @ValuativeExtension F L _ _ _ (.ofValuation (w.comap i.toRingHom)) _ := by
  refine @ValuativeExtension.mk F L _ _ _ (.ofValuation (w.comap i.toRingHom)) _ (fun x y => ?_)
  change w (i (algebraMap F L x)) ≤ w (i (algebraMap F L y)) ↔ _
  rw [i.commutes, i.commutes, r.scalar_value, r.scalar_value,
    pow_le_pow_iff_left₀ zero_le zero_le hn, normalized_le, (valuation F).vle_iff_le]

private theorem comparison_of_valuative_rel {L : Type*} [Field L] [rL : ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (s : Valuation L ℤᵐ⁰)
    (hs : ValuativeRel.ofValuation s = rL) (a b : L) :
    normalizedValuation L a ≤ normalizedValuation L b ↔ s a ≤ s b := by
  rw [normalized_le, ← (valuation L).vle_iff_le]
  change @ValuativeRel.vle L _ rL a b ↔ _
  rw [← hs]
  rfl

private theorem normalized_base_of_unramified {L : Type*} [Field L] [Algebra F L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hc : ∀ a b : F, normalizedValuation L (algebraMap F L a) ≤
      normalizedValuation L (algebraMap F L b) ↔ normalizedValuation F a ≤ normalizedValuation F b)
    (hs : Function.Surjective (fun a => normalizedValuation L (algebraMap F L a))) (a : F) :
    normalizedValuation L (algebraMap F L a) = normalizedValuation F a := by
  let f := (normalizedValuation L).comap (algebraMap F L)
  let g := normalizedValuation F
  change f a = g a
  have hle (c d : F) : f c ≤ f d ↔ g c ≤ g d := hc c d
  have hlt (c d : F) : f c < f d ↔ g c < g d := by
    simp only [lt_iff_not_ge, hle]
  obtain ⟨π, hπ⟩ := normalized_surjective F (depth 1)
  have hπ' : g π = depth 1 := hπ
  have hπf : f π = depth 1 := by
    have h₁ : f π ≤ depth 1 := by
      apply (lt_depth_iff _ 0).1
      change f π < 1
      rw [← map_one f, hlt, map_one, hπ']
      exact depth_one_lt_one
    obtain ⟨t, ht⟩ := hs (depth 1)
    have ht' : f t = depth 1 := ht
    have ht₀ : g t < 1 := by
      rw [← map_one g, ← hlt, map_one, ht']
      exact depth_one_lt_one
    have h₂ : depth 1 ≤ f π := by
      rw [← ht', hle, hπ']
      exact (lt_depth_iff (g t) 0).1 ht₀
    exact le_antisymm h₁ h₂
  generalize ha : g a = γ
  induction γ using WithZero.expRecOn with
  | zero =>
    have : a = 0 := (map_eq_zero g).mp ha
    simp [this]
  | exp z =>
    have hpow : depth 1 ^ (-z) = exp z := by
      rw [depth, ← exp_zsmul]
      simp
    have hg : g a = g (π ^ (-z)) := by rw [ha, map_zpow₀, hπ', hpow]
    have hfa : f a = f (π ^ (-z)) := le_antisymm ((hle _ _).2 hg.le) ((hle _ _).2 hg.ge)
    rw [hfa, map_zpow₀, hπf, hpow]

private theorem unramified_values (r : IntegralReduction (F := F) n w κ) (hn : n ≠ 0)
    {L : Type*} [Field L] [Algebra F L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (i : L →ₐ[F] B)
    (hs : ValuativeRel.ofValuation (w.comap i.toRingHom) = (inferInstance : ValuativeRel L))
    (hvalues : ∀ a : L, ∃ c : F, w (i a) = w (algebraMap F B c)) :
    (∀ a : F, normalizedValuation L (algebraMap F L a) = normalizedValuation F a) ∧
    ∀ a : L, w (i a) = normalizedValuation L a ^ n := by
  have hle (a b : L) : normalizedValuation L a ≤ normalizedValuation L b ↔
      w (i a) ≤ w (i b) := comparison_of_valuative_rel (w.comap i.toRingHom) hs a b
  have hval (a : L) (b : F) (h : w (i a) = w (algebraMap F B b)) :
      normalizedValuation L a = normalizedValuation L (algebraMap F L b) := by
    have he : w (i a) = w (i (algebraMap F L b)) := by rw [i.commutes, h]
    exact le_antisymm ((hle _ _).2 he.le) ((hle _ _).2 he.ge)
  have hbase := normalized_base_of_unramified (L := L) (F := F) (by
      intro a b
      rw [hle, i.commutes, i.commutes, r.scalar_value, r.scalar_value,
        pow_le_pow_iff_left₀ zero_le zero_le hn]) (by
      intro γ
      obtain ⟨a, ha⟩ := normalized_surjective L γ
      obtain ⟨b, hb⟩ := hvalues a
      exact ⟨b, (hval a b hb).symm.trans ha⟩)
  refine ⟨hbase, fun a => ?_⟩
  obtain ⟨b, hb⟩ := hvalues a
  rw [hb, r.scalar_value, hval a b hb, hbase]


open Polynomial

/-- Lift all the coefficients below the leading coefficient, which is kept equal to one. -/
private theorem lift_monic {R k : Type*} [CommRing R] [Field k] (f : R →+* k)
    (hf : Function.Surjective f) (p : k[X]) (hp : p.Monic) :
    ∃ q : R[X], q.Monic ∧ q.map f = p := by
  classical
  choose c hc using fun j : Fin p.natDegree => hf (p.coeff j)
  let q : R[X] := X ^ p.natDegree + ofFn p.natDegree c
  refine ⟨q, monic_X_pow_add (ofFn_degree_lt _), ?_⟩
  ext j
  rw [coeff_map]
  change f ((X ^ p.natDegree + ofFn p.natDegree c).coeff j) = _
  rw [coeff_add, coeff_X_pow]
  rcases lt_trichotomy j p.natDegree with h | h | h
  · rw [ite_eq_right h.ne, zero_add, ofFn_coeff_eq_val_of_lt _ h, hc]
  · subst j
    rw [ite_eq_left rfl, ofFn_coeff_eq_zero_of_ge _ le_rfl, add_zero, map_one, hp.coeff_natDegree]
  · rw [ite_eq_right h.ne', ofFn_coeff_eq_zero_of_ge _ h.le, zero_add, map_zero,
      coeff_eq_zero_of_natDegree_lt h]

private def reductionEquiv {R k : Type*} [CommRing R] [IsLocalRing R] [Field k]
    (q : R →+* k) (hq : Function.Surjective q) : IsLocalRing.ResidueField R ≃+* k := by
  let f : IsLocalRing.ResidueField R →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) q
    (fun a ha => RingHom.mem_ker.mp ((IsLocalRing.ker_eq_maximalIdeal q hq).symm ▸ ha))
  exact RingEquiv.ofBijective f ⟨f.injective, fun z => by
    obtain ⟨a, ha⟩ := hq z
    exact ⟨IsLocalRing.residue _ a, ha⟩⟩

private theorem reductionEquiv_apply {R k : Type*} [CommRing R] [IsLocalRing R] [Field k]
    (q : R →+* k) (hq : Function.Surjective q) (a : R) :
    reductionEquiv q hq (IsLocalRing.residue _ a) = q a := rfl

private theorem lift_simple_root {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (q : Integers L →+* κ) (hq : Function.Surjective q)
    (p : (Integers L)[X]) (hp : p.Monic) (a : κ)
    (ha : p.eval₂ q a = 0) (hd : p.derivative.eval₂ q a ≠ 0) :
    ∃ x : Integers L, p.eval x = 0 ∧ q x = a := by
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup (G := L)
  let : IsAdicComplete (IsLocalRing.maximalIdeal (Integers L)) (Integers L) :=
    IsNonarchimedeanLocalField.instIsAdicCompleteSubtypeMemSubringIntegerValueGroupWithZeroValuationMaximalIdeal L
  have hH : HenselianRing (Integers L) (IsLocalRing.maximalIdeal (Integers L)) :=
    IsAdicComplete.henselianRing _ _
  obtain ⟨x, rfl⟩ := hq a
  have hker := IsLocalRing.ker_eq_maximalIdeal q hq
  have hx : p.eval x ∈ IsLocalRing.maximalIdeal (Integers L) := by
    rw [← hker, RingHom.mem_ker, ← eval₂_at_apply]
    exact ha
  have hu : IsUnit (IsLocalRing.residue (Integers L) (p.derivative.eval x)) := by
    apply isUnit_iff_ne_zero.mpr
    intro he
    rw [eval₂_at_apply] at hd
    exact hd ((reductionEquiv_apply q hq _).symm.trans (by rw [he, map_zero]))
  obtain ⟨y, hy, hyx⟩ := hH.is_henselian p hp x hx hu
  refine ⟨y, hy, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at hyx
  exact hyx

private def integerAut {L : Type*} [Field L] [Algebra F L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hval : ∀ (σ : L ≃ₐ[F] L) (a : L), normalizedValuation L (σ a) = normalizedValuation L a)
    (σ : L ≃ₐ[F] L) : Integers L ≃+* Integers L where
  toFun a := ⟨σ (a : L), (normalized_mem _).1 (by rw [hval]; exact (normalized_mem _).2 a.2)⟩
  invFun a := ⟨σ.symm (a : L), (normalized_mem _).1 (by rw [hval]; exact (normalized_mem _).2 a.2)⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply (a : L))
  right_inv a := Subtype.ext (σ.apply_symm_apply (a : L))
  map_mul' a b := Subtype.ext (map_mul σ (a : L) (b : L))
  map_add' a b := Subtype.ext (map_add σ (a : L) (b : L))

private def reductionAction {L : Type*} [Field L] [Algebra F L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (q : Integers L →+* κ) (hq : Function.Surjective q)
    (j : Integers F →+* Integers L) (hj : ∀ a, (j a : L) = algebraMap F L (a : F))
    (hscalar : ∀ a, q (j a) = algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a))
    (hval : ∀ (σ : L ≃ₐ[F] L) (a : L), normalizedValuation L (σ a) = normalizedValuation L a) :
    (L ≃ₐ[F] L) →* (κ ≃ₐ[BaseResidue F] κ) := by
  let e := reductionEquiv q hq
  let f (σ : L ≃ₐ[F] L) : κ ≃+* κ :=
    (e.symm.trans (IsLocalRing.ResidueField.mapEquiv (integerAut hval σ))).trans e
  have hf (σ : L ≃ₐ[F] L) (a : Integers L) : f σ (q a) = q (integerAut hval σ a) := by
    rw [← reductionEquiv_apply q hq a]
    change e (IsLocalRing.ResidueField.mapEquiv (integerAut hval σ)
      (e.symm (e (IsLocalRing.residue _ a)))) = _
    simp only [RingEquiv.symm_apply_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    exact reductionEquiv_apply q hq _
  let g (σ : L ≃ₐ[F] L) : κ ≃ₐ[BaseResidue F] κ :=
    { f σ with
      commutes' := by
        intro c
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := Integers F) c
        change f σ (algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a)) = _
        rw [← hscalar, hf]
        congr 1
        apply Subtype.ext
        change σ (j a : L) = (j a : L)
        rw [hj, σ.commutes] }
  refine
    { toFun := g
      map_one' := ?_
      map_mul' := ?_ }
  · ext c
    obtain ⟨a, rfl⟩ := hq c
    change f 1 (q a) = q a
    rw [hf]
    rfl
  · intro σ τ
    ext c
    obtain ⟨a, rfl⟩ := hq c
    change f (σ * τ) (q a) = f σ (f τ (q a))
    rw [hf, hf, hf]
    rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem reductionAction_apply {L : Type*} [Field L] [Algebra F L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (q : Integers L →+* κ) (hq : Function.Surjective q)
    (j : Integers F →+* Integers L) (hj : ∀ a, (j a : L) = algebraMap F L (a : F))
    (hscalar : ∀ a, q (j a) = algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a))
    (hval : ∀ (σ : L ≃ₐ[F] L) (a : L), normalizedValuation L (σ a) = normalizedValuation L a)
    (σ : L ≃ₐ[F] L) (a b : Integers L) (hb : (b : L) = σ (a : L)) :
    reductionAction q hq j hj hscalar hval σ (q a) = q b := by
  let e := reductionEquiv q hq
  rw [← reductionEquiv_apply q hq a]
  change e (IsLocalRing.ResidueField.mapEquiv (integerAut hval σ)
    (e.symm (e (IsLocalRing.residue _ a)))) = _
  simp only [RingEquiv.symm_apply_apply, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [reductionEquiv_apply]
  exact congrArg q (Subtype.ext hb.symm)


/-- An automorphism of the residue field lifts by sending a Hensel generator
to the unique simple root with the prescribed reduction. -/
private theorem reductionAction_surjective [Finite κ] {L : Type*} [Field L] [Algebra F L]
    [FiniteDimensional F L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (q : Integers L →+* κ) (hq : Function.Surjective q)
    (j : Integers F →+* Integers L) (hj : ∀ a, (j a : L) = algebraMap F L (a : F))
    (hscalar : ∀ a, q (j a) = algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a))
    (hval : ∀ (σ : L ≃ₐ[F] L) (a : L), normalizedValuation L (σ a) = normalizedValuation L a)
    (hdim : Module.finrank F L = Module.finrank (BaseResidue F) κ) :
    Function.Surjective (reductionAction q hq j hj hscalar hval) := by
  let k := BaseResidue F
  let : FiniteDimensional k κ := Module.Finite.of_finite
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top k κ
  let m := minpoly k α
  have hαint : IsIntegral k α := Algebra.IsIntegral.isIntegral _
  have hm : m.Monic := minpoly.monic hαint
  have hmdim : m.natDegree = Module.finrank k κ :=
    ((PowerBasis.ofAdjoinSimpleEqTop_dim hαint hα).symm.trans
      (PowerBasis.finrank (PowerBasis.ofAdjoinSimpleEqTop hαint hα)).symm)
  obtain ⟨p, hp, hred⟩ := lift_monic (IsLocalRing.residue (Integers F))
    IsLocalRing.residue_surjective m hm
  let pL : (Integers L)[X] := p.map j
  have hpL : pL.Monic := hp.map j
  have hcomp : q.comp j = (algebraMap k κ).comp (IsLocalRing.residue (Integers F)) :=
    RingHom.ext hscalar
  have hpLred : pL.map q = m.map (algebraMap k κ) := by
    rw [show pL = p.map j from rfl, map_map, hcomp, ← map_map, hred]
  have hs : m.Separable := Algebra.IsSeparable.isSeparable k α
  have lift (γ : κ) (hγ : aeval γ m = 0) :
      ∃ a : Integers L, pL.eval a = 0 ∧ q a = γ := by
    refine lift_simple_root q hq pL hpL γ ?_ ?_
    · rwa [eval₂_eq_eval_map, hpLred, ← eval₂_eq_eval_map, ← aeval_def]
    · rw [eval₂_eq_eval_map, ← derivative_map, hpLred, derivative_map, ← eval₂_eq_eval_map,
        ← aeval_def]
      exact hs.aeval_derivative_ne_zero hγ
  obtain ⟨a, ha, haq⟩ := lift α (minpoly.aeval k α)
  let pF : F[X] := p.map (algebraMap (Integers F) F)
  have hpF : pF.Monic := hp.map _
  have hirr : Irreducible pF := (hp.irreducible_iff_irreducible_map_fraction_map (K := F)).1
    (Monic.irreducible_of_irreducible_map (IsLocalRing.residue (Integers F)) p hp
      (hred.symm ▸ minpoly.irreducible hαint))
  have hroot (x : Integers L) (hx : pL.eval x = 0) : aeval (x : L) pF = 0 := by
    have h := congrArg (fun z : Integers L => (z : L)) hx
    change (Integers L).subtype (pL.eval x) = (Integers L).subtype 0 at h
    rw [← eval₂_at_apply, map_zero] at h
    change pL.eval₂ (Integers L).subtype (x : L) = 0 at h
    rw [aeval_def, eval₂_map]
    rw [show pL = p.map j from rfl, eval₂_map] at h
    have he : (algebraMap F L).comp (algebraMap (Integers F) F) = (Integers L).subtype.comp j :=
      RingHom.ext (fun c => (hj c).symm)
    rwa [he]
  have hmin : minpoly F (a : L) = pF :=
    (minpoly.eq_of_irreducible_of_monic hirr (hroot a ha) hpF).symm
  have haint : IsIntegral F (a : L) := Algebra.IsIntegral.isIntegral _
  have hgen : IntermediateField.adjoin F ({(a : L)} : Set L) = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_le le_top
    rw [IntermediateField.adjoin.finrank haint, hmin, show pF = p.map _ from rfl,
      hp.natDegree_map, ← hp.natDegree_map (IsLocalRing.residue (Integers F)), hred, hmdim]
    simpa only [IntermediateField.topEquiv.toLinearEquiv.finrank_eq] using hdim.le
  let pb := PowerBasis.ofAdjoinSimpleEqTop haint hgen
  have hbgen : pb.gen = (a : L) := PowerBasis.ofAdjoinSimpleEqTop_gen haint hgen
  intro τ
  have hτ : aeval (τ α) m = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨b, hb, hbq⟩ := lift (τ α) hτ
  let σ₀ : L →ₐ[F] L := pb.lift (b : L) (by rw [hbgen, hmin]; exact hroot b hb)
  let σ := AlgEquiv.ofBijective σ₀ σ₀.bijective
  have hσ : (b : L) = σ (a : L) := by
    change (b : L) = σ₀ (a : L)
    rw [← hbgen, PowerBasis.lift_gen]
  refine ⟨σ, ?_⟩
  apply AlgEquiv.coe_toAlgHom_injective
  let pbκ := PowerBasis.ofAdjoinSimpleEqTop hαint hα
  apply pbκ.algHom_ext
  change reductionAction q hq j hj hscalar hval σ pbκ.gen = τ pbκ.gen
  rw [PowerBasis.ofAdjoinSimpleEqTop_gen, ← haq, reductionAction_apply q hq j hj hscalar hval σ a b hσ,
    haq, hbq]

private theorem value_of_automorphism {L : Type*} [Field L] [Algebra F L] [rL : ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hbase : ∀ a : F, normalizedValuation L (algebraMap F L a) = normalizedValuation F a)
    (huniq : ∀ s : ValuativeRel L, @ValuativeExtension F L _ _ _ s _ → s = rL)
    (σ : L ≃ₐ[F] L) (a : L) : normalizedValuation L (σ a) = normalizedValuation L a := by
  let s : Valuation L ℤᵐ⁰ := (normalizedValuation L).comap σ.toRingHom
  have hex : @ValuativeExtension F L _ _ _ (.ofValuation s) _ := by
    refine @ValuativeExtension.mk F L _ _ _ (.ofValuation s) _ (fun x y => ?_)
    change normalizedValuation L (σ (algebraMap F L x)) ≤
      normalizedValuation L (σ (algebraMap F L y)) ↔ _
    rw [σ.commutes, σ.commutes, hbase, hbase, normalized_le, (valuation F).vle_iff_le]
  obtain ⟨c, hc⟩ := normalized_surjective F (normalizedValuation L a)
  have hcL : normalizedValuation L (algebraMap F L c) = normalizedValuation L a :=
    (hbase c).trans hc
  have hle (x y : L) : normalizedValuation L x ≤ normalizedValuation L y ↔ s x ≤ s y :=
    comparison_of_valuative_rel s (huniq _ hex) x y
  change s a = _
  rw [← hcL]
  have hfix : s (algebraMap F L c) = normalizedValuation L (algebraMap F L c) := by
    change normalizedValuation L (σ (algebraMap F L c)) = _
    rw [σ.commutes]
  rw [← hfix]
  exact le_antisymm ((hle _ _).1 hcL.ge) ((hle _ _).1 hcL.le)


private theorem unramified_subfield [Finite κ] (hB : IsCentralSimple F B)
    (r : IntegralReduction (F := F) (degree F B) w κ)
    (hf : Module.finrank (BaseResidue F) κ = degree F B) :
    Nonempty (UnramifiedSubfield r) := by
  classical
  let n := degree F B
  have hn : n ≠ 0 := (degree_pos hB).ne'
  obtain ⟨L, hL, hAlg, hfinite, i, honto⟩ := exists_subfield_onto hB r
  let := hL
  let := hAlg
  let := hfinite
  obtain ⟨hd, hvalues⟩ := subfield_values hB r hf i honto
  obtain ⟨rL, T, _, hlocal, _, _, huniq⟩ := finiteExtension_localField (K := F) (L := L)
  let := rL
  let := T
  let := hlocal
  obtain ⟨hbase, hrestrict⟩ := unramified_values r hn i (huniq _ (extension_of_comap r hn i)) hvalues
  let j : Integers F →+* Integers L :=
    ((algebraMap F L).comp (Integers F).subtype).codRestrict (Integers L).toSubring (by
      intro a
      change algebraMap F L (a : F) ∈ Integers L
      rw [← normalized_mem, hbase]
      exact (normalized_mem _).2 a.2)
  have hj (a : Integers F) : (j a : L) = algebraMap F L (a : F) := rfl
  let iO : Integers L →+* w.integer :=
    (i.toRingHom.comp (Integers L).subtype).codRestrict w.integer (by
      intro a
      change w (i (a : L)) ≤ 1
      rw [hrestrict]
      exact pow_le_one₀ zero_le ((normalized_mem _).2 a.2))
  let q := r.reduction.comp iO
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, x, hx, hred⟩ := honto z
    have ha : a ∈ Integers L := by
      have hv : w (i a) ≤ 1 := hx ▸ x.2
      rw [hrestrict, ← one_pow n] at hv
      exact (normalized_mem _).1 ((pow_le_pow_iff_left₀ zero_le zero_le hn).1 hv)
    refine ⟨⟨a, ha⟩, ?_⟩
    change r.reduction (iO ⟨a, ha⟩) = z
    rw [show iO ⟨a, ha⟩ = x from Subtype.ext hx, hred]
  have hscalar (a : Integers F) : q (j a) = algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a) :=
    r.scalar_reduction a (iO (j a)) (i.commutes _)
  let hval := value_of_automorphism hbase huniq
  let act := reductionAction q hq j hj hscalar hval
  have hact : Function.Surjective act := reductionAction_surjective q hq j hj hscalar hval (hd.trans hf.symm)
  let : FiniteDimensional (BaseResidue F) κ := Module.Finite.of_finite
  have hcardκ : Nat.card (κ ≃ₐ[BaseResidue F] κ) = n :=
    (IsGalois.card_aut_eq_finrank (BaseResidue F) κ).trans hf
  have hcard : Nat.card (L ≃ₐ[F] L) = n := by
    apply le_antisymm
    · rw [← Fintype.card_eq_nat_card]
      exact AlgEquiv.card_le.trans_eq hd
    · rw [← hcardκ]
      exact Nat.card_le_card_of_surjective act hact
  let aut := MulEquiv.ofBijective act ((Fintype.bijective_iff_surjective_and_card _).2
    ⟨hact, by rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, hcardκ]⟩)
  let vL := normalizedValuation L
  let fromNorm : vL.valuationSubring →+* Integers L :=
    vL.valuationSubring.subtype.codRestrict (Integers L).toSubring
      (fun a => (normalized_mem _).1 a.2)
  have hfrom : Function.Surjective fromNorm := fun a => ⟨⟨(a : L), (normalized_mem _).2 a.2⟩, rfl⟩
  let qN := q.comp fromNorm
  have hqN : Function.Surjective qN := hq.comp hfrom
  refine ⟨
    { L := L
      fieldL := hL
      algebraL := hAlg
      embed := i
      degree := hd
      galois := IsGalois.of_card_aut_eq_finrank F L (hcard.trans hd.symm)
      cyclic := aut.isCyclic.mpr inferInstance
      residue_separable := inferInstance
      vL := vL
      onto_vL := normalized_surjective L
      base_value := hbase
      restrict_value := hrestrict
      residueEquiv := reductionEquiv qN hqN
      residue_eq := ?_
      residue_scalar := ?_
      autEquiv := aut
      value_aut := hval
      residue_aut := ?_ }⟩
  · intro a x hx
    rw [reductionEquiv_apply]
    change r.reduction (iO (fromNorm a)) = r.reduction x
    exact congrArg r.reduction (Subtype.ext hx.symm)
  · intro a b hb
    rw [reductionEquiv_apply]
    exact r.scalar_reduction a (iO (fromNorm b)) (by
      change i (b : L) = _
      rw [hb, i.commutes])
  · intro σ a b hb
    rw [reductionEquiv_apply, reductionEquiv_apply]
    exact reductionAction_apply q hq j hj hscalar hval σ (fromNorm a) (fromNorm b) hb

/-- The normalized division value group and residue degree are both maximal,
and reduction identifies the Galois group of the embedded unramified field. -/
theorem ramification : Ramification.{u, v, z} := by
  intro F _ _ _ _ B _ _ hB κ _ _ _ w r
  obtain ⟨hs, hf⟩ := division_degrees hB r
  exact ⟨hs, hf, unramified_subfield hB r hf⟩

end LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
