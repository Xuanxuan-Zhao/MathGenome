import MathGenome.Internal.Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

universe u v w
noncomputable section
namespace D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
open Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
open scoped Pointwise

theorem primaryMembership : PrimaryMembership.{u, v} := by
  intro R _ p M _ _ x
  rw [Submodule.mem_torsion'_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hx⟩
    obtain ⟨n, rfl⟩ := ha
    exact ⟨n, hx⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨p ^ n, ⟨n, rfl⟩⟩, hn⟩

section General
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem smul_zero_of_dvd {a b : R} (h : a ∣ b) {x : M} (hx : a • x = 0) :
    b • x = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_smul, hx, smul_zero]

theorem quotient_annihilated (d : R) (x : R ⧸ Ideal.span {d}) : d • x = 0 := by
  change Ideal.Quotient.mk _ d * x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d)), zero_mul]

theorem eq_zero_of_coprime {a b : R} (h : IsCoprime a b) {x : M}
    (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  obtain ⟨u, v, huv⟩ := h
  calc
    x = (1 : R) • x := (one_smul R x).symm
    _ = (u * a + v * b) • x := by rw [huv]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, ha, hb, smul_zero, smul_zero, add_zero]

/-- Restriction of an isomorphism to the intrinsic primary submodules. -/
def primaryEquiv (p : R) (E : M ≃ₗ[R] N) : primary R p M ≃ₗ[R] primary R p N where
  toFun x := ⟨E x, by
    obtain ⟨n, hn⟩ := (primaryMembership R p M x).mp x.property
    exact (primaryMembership R p N _).mpr ⟨n, by rw [← map_smul, hn, map_zero]⟩⟩
  invFun x := ⟨E.symm x, by
    obtain ⟨n, hn⟩ := (primaryMembership R p N x).mp x.property
    exact (primaryMembership R p M _).mpr ⟨n, by rw [← map_smul, hn, map_zero]⟩⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x)
  right_inv x := Subtype.ext (E.apply_symm_apply x)
  map_add' x y := Subtype.ext (E.map_add x y)
  map_smul' a x := Subtype.ext (E.map_smul a x)

/-- Restriction of an isomorphism to scalar images. -/
def powerEquiv (p : R) (n : ℕ) (E : M ≃ₗ[R] N) :
    powerImage p n M ≃ₗ[R] powerImage p n N where
  toFun x := ⟨E x, by
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp x.property
    exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
      ⟨E y, Submodule.mem_top, by rw [← map_smul, hy]⟩⟩
  invFun x := ⟨E.symm x, by
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp x.property
    exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
      ⟨E.symm y, Submodule.mem_top, by rw [← map_smul, hy]⟩⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x)
  right_inv x := Subtype.ext (E.apply_symm_apply x)
  map_add' x y := Subtype.ext (E.map_add x y)
  map_smul' a x := Subtype.ext (E.map_smul a x)

/-- Quotients by pM are naturally linear over R/(p). -/
def modScalarEquiv (p : R) (E : M ≃ₗ[R] N) :
    (M ⧸ p • (⊤ : Submodule R M)) ≃ₗ[R ⧸ Ideal.span {p}]
      (N ⧸ p • (⊤ : Submodule R N)) := by
  have h : (p • (⊤ : Submodule R M)).map E.toLinearMap =
      p • (⊤ : Submodule R N) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hy
      exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
        ⟨E z, Submodule.mem_top, (E.map_smul p z).symm⟩
    · intro hx
      obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hx
      exact ⟨p • E.symm z, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top,
        by simp⟩
  let F := Submodule.Quotient.equiv _ _ E h
  exact { F.toAddEquiv with
    map_smul' := by
      rintro ⟨a⟩ x
      change F (a • x) = a • F x
      exact F.map_smul a x }

def gradedEquiv (p : R) (n : ℕ) (E : M ≃ₗ[R] N) :
    gradedPiece p n M ≃ₗ[R ⧸ Ideal.span {p}] gradedPiece p n N :=
  modScalarEquiv p (powerEquiv p n E)

end General

section PID
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem primaryCoordinates : PrimaryCoordinates.{u, v} := by
  intro R _ _ _ M _ _ _ r t q e hq E p hp x
  rw [primaryMembership]
  constructor
  · rintro ⟨n, hn⟩
    have hE : p ^ n • E x = 0 := by rw [← map_smul, hn, map_zero]
    constructor
    · funext i
      have hi := congrArg (fun z => z.1 i) hE
      exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ hp.ne_zero)
    · intro i hi
      have hcop : IsCoprime p (q i) :=
        (hp.isCoprime_or_dvd (q i)).resolve_right
          (fun hd => hi (hp.associated_of_dvd (hq i).1.irreducible hd))
      exact eq_zero_of_coprime hcop.pow
        (congrArg (fun z => z.2 i) hE) (quotient_annihilated _ _)
  · rintro ⟨hfree, hcoord⟩
    let n := ∑ i : Fin t, e i
    refine ⟨n, E.injective ?_⟩
    rw [map_smul, map_zero]
    apply Prod.ext
    · simp [hfree]
    · funext i
      by_cases hi : Associated p (q i)
      · have he : e i ≤ n := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
        exact smul_zero_of_dvd ((hi.pow_pow).symm.dvd.trans (pow_dvd_pow p he))
          (quotient_annihilated _ _)
      · simp [hcoord i hi]

end PID

theorem layerInvariant : LayerInvariant.{u, v, w} := by
  intro R _ _ _ M _ _ N _ _ E p hp k
  exact ⟨gradedEquiv p (k - 1) (primaryEquiv p E)⟩

section Products
variable {R : Type u} [CommRing R]
variable {ι : Type*} [Fintype ι]
variable (A : ι → Type v) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- Scalar images commute with finite products, including the empty product. -/
def powerPiEquiv (p : R) (n : ℕ) :
    powerImage p n (∀ i, A i) ≃ₗ[R] (∀ i, powerImage p n (A i)) where
  toFun x i := ⟨x.val i, by
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp x.property
    exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
      ⟨y i, Submodule.mem_top, congrFun hy i⟩⟩
  invFun x := ⟨fun i => (x i).val, by
    classical
    have h (i : ι) : ∃ y : A i, p ^ n • y = (x i).val := by
      obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp (x i).property
      exact ⟨y, hy⟩
    exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
      ⟨fun i => (h i).choose, Submodule.mem_top, funext fun i => (h i).choose_spec⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

def modScalarPiEquiv (p : R) :
    ((∀ i, A i) ⧸ p • (⊤ : Submodule R (∀ i, A i))) ≃ₗ[R ⧸ Ideal.span {p}]
      (∀ i, A i ⧸ p • (⊤ : Submodule R (A i))) := by
  classical
  have h : p • (⊤ : Submodule R (∀ i, A i)) =
      Submodule.pi Set.univ (fun i => p • (⊤ : Submodule R (A i))) := by
    ext x
    simp only [Submodule.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hx i
      obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
        ⟨y i, Submodule.mem_top, congrFun hy i⟩
    · intro hx
      have h (i : ι) : ∃ y : A i, p • y = x i := by
        obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp (hx i)
        exact ⟨y, hy⟩
      exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
        ⟨fun i => (h i).choose, Submodule.mem_top, funext fun i => (h i).choose_spec⟩
  let F := (Submodule.quotEquivOfEq _ _ h).trans
    (Submodule.quotientPi (fun i => p • (⊤ : Submodule R (A i))))
  exact { F.toAddEquiv with
    map_smul' := by
      rintro ⟨a⟩ x
      change F (a • x) = a • F x
      exact F.map_smul a x }

def gradedPiEquiv (p : R) (n : ℕ) :
    gradedPiece p n (∀ i, A i) ≃ₗ[R ⧸ Ideal.span {p}] (∀ i, gradedPiece p n (A i)) :=
  (modScalarEquiv p (powerPiEquiv A p n)).trans
    (modScalarPiEquiv (fun i => powerImage p n (A i)) p)

end Products

section PrimaryProduct
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {r t : ℕ} (q : Fin t → R) (e : Fin t → ℕ)
variable (hq : ∀ i, Prime (q i) ∧ 0 < e i)
variable (E : M ≃ₗ[R] ((Fin r → R) × (∀ i, R ⧸ Ideal.span {q i ^ e i})))
variable (p : R) (hp : Irreducible p)

/-- Selecting precisely the p-primary coordinates gives the actual primary part. -/
def primaryProductEquiv :
    primary R p M ≃ₗ[R] (∀ i : {i : Fin t // Associated p (q i)},
      R ⧸ Ideal.span {q i.val ^ e i.val}) := by
  classical
  let extend (y : ∀ i : {i : Fin t // Associated p (q i)},
      R ⧸ Ideal.span {q i.val ^ e i.val}) :
      ((Fin r → R) × (∀ i, R ⧸ Ideal.span {q i ^ e i})) :=
    (0, fun i => if h : Associated p (q i) then y ⟨i, h⟩ else 0)
  exact
    { toFun := fun x i => (E x).2 i.val
      invFun := fun y => ⟨E.symm (extend y), by
        apply (primaryCoordinates R M r t q e hq E p hp _).mpr
        simp only [E.apply_symm_apply, extend]
        exact ⟨trivial, fun i hi => dite_eq_right hi⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply E.injective
        rw [E.apply_symm_apply]
        have hx := (primaryCoordinates R M r t q e hq E p hp x).mp x.property
        apply Prod.ext hx.1.symm
        funext i
        by_cases hi : Associated p (q i)
        · simp [extend, hi]
        · simpa [extend, hi] using (hx.2 i hi).symm
      right_inv := by
        intro y
        funext i
        simp [extend, i.property]
      map_add' := by
        intro x y
        funext i
        exact congrArg (fun z => z.2 i.val) (E.map_add x y)
      map_smul' := by
        intro a x
        funext i
        exact congrArg (fun z => z.2 i.val) (E.map_smul a x) }

/-- Associated prime bases define the same cyclic modules; no normalization
of primes or hypothesis on the chosen representative is needed. -/
def primaryPowerEquiv :
    primary R p M ≃ₗ[R] (∀ i : {i : Fin t // Associated p (q i)},
      R ⧸ Ideal.span {p ^ e i.val}) :=
  (primaryProductEquiv q e hq E p hp).trans
    (LinearEquiv.piCongrRight fun i => Submodule.quotEquivOfEq _ _
      (Ideal.span_singleton_eq_span_singleton.mpr ((i.property.pow_pow).symm)))

end PrimaryProduct

section Cyclic
variable {R : Type u} [CommRing R]

/-- The standard generator of p^n(R/(p^e)). -/
def cyclicGenerator (p : R) (n e : ℕ) : powerImage p n (R ⧸ Ideal.span {p ^ e}) :=
  ⟨p ^ n • (1 : R ⧸ Ideal.span {p ^ e}),
    Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩

def cyclicLayerMap (p : R) (n e : ℕ) : R →ₗ[R] gradedPiece p n (R ⧸ Ideal.span {p ^ e}) :=
  (p • (⊤ : Submodule R (powerImage p n (R ⧸ Ideal.span {p ^ e})))).mkQ.comp
    (LinearMap.toSpanSingleton R _ (cyclicGenerator p n e))

theorem cyclicGenerator_spans (p : R) (n e : ℕ)
    (x : powerImage p n (R ⧸ Ideal.span {p ^ e})) :
    ∃ a : R, a • cyclicGenerator p n e = x := by
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp x.property
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, Subtype.ext ?_⟩
  change a • (p ^ n • (1 : R ⧸ Ideal.span {p ^ e})) = x.val
  simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hy

theorem cyclicLayerMap_surjective (p : R) (n e : ℕ) :
    Function.Surjective (cyclicLayerMap p n e) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, rfl⟩ := cyclicGenerator_spans p n e y
  exact ⟨a, rfl⟩

theorem cyclicLayerMap_eq_zero [IsDomain R] {p : R} (hp : Irreducible p)
    (n e : ℕ) (hn : n < e) (a : R) :
    cyclicLayerMap p n e a = 0 ↔ p ∣ a := by
  change Submodule.Quotient.mk (a • cyclicGenerator p n e) = 0 ↔ p ∣ a
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro ha
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp ha
    obtain ⟨b, rfl⟩ := cyclicGenerator_spans p n e y
    have h : p • (b • (p ^ n • (1 : R ⧸ Ideal.span {p ^ e}))) =
        a • (p ^ n • (1 : R ⧸ Ideal.span {p ^ e})) := congrArg Subtype.val hy
    have hq : Ideal.Quotient.mk (Ideal.span {p ^ e}) (p ^ n * (p * b - a)) = 0 := by
      have hm : p • (b • (p ^ n • (1 : R ⧸ Ideal.span {p ^ e}))) -
          a • (p ^ n • (1 : R ⧸ Ideal.span {p ^ e})) = 0 := sub_eq_zero.mpr h
      simpa [Algebra.smul_def, map_mul, map_sub, mul_comm, mul_left_comm, mul_assoc,
        mul_sub] using hm
    have hd : p ^ e ∣ p ^ n * (p * b - a) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq)
    have hd' := (pow_dvd_pow p (show n + 1 ≤ e by omega)).trans hd
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)] at hd'
    have hd'' := dvd_sub (dvd_mul_right p b) hd'
    simpa only [sub_sub_cancel] using hd''
  · rintro ⟨b, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists ..).mpr
      ⟨b • cyclicGenerator p n e, Submodule.mem_top, by rw [mul_smul]⟩

/-- Each nonvanishing cyclic graded layer is the residue field itself. -/
def cyclicLayerEquiv [IsDomain R] {p : R} (hp : Irreducible p)
    (n e : ℕ) (hn : n < e) :
    (R ⧸ Ideal.span {p}) ≃ₗ[R ⧸ Ideal.span {p}]
      gradedPiece p n (R ⧸ Ideal.span {p ^ e}) := by
  let f := cyclicLayerMap p n e
  have hf : f.ker = Ideal.span {p} := by
    ext a
    exact (cyclicLayerMap_eq_zero hp n e hn a).trans Ideal.mem_span_singleton.symm
  let F := (Submodule.quotEquivOfEq _ _ hf.symm).trans
    (f.quotKerEquivOfSurjective (cyclicLayerMap_surjective p n e))
  exact { F.toAddEquiv with
    map_smul' := by
      rintro ⟨a⟩ x
      change F (a • x) = a • F x
      exact F.map_smul a x }

theorem cyclicPower_eq_bot (p : R) (n e : ℕ) (he : e ≤ n) :
    powerImage p n (R ⧸ Ideal.span {p ^ e}) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hx
  exact smul_zero_of_dvd (pow_dvd_pow p he) (quotient_annihilated _ _)

end Cyclic

section Dimension
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {p : R}

theorem cyclicLayer_finite (hp : Irreducible p) (n e : ℕ) :
    let := residueField p hp
    Module.Finite (R ⧸ Ideal.span {p}) (gradedPiece p n (R ⧸ Ideal.span {p ^ e})) := by
  let := residueField p hp
  by_cases hn : n < e
  · exact Module.Finite.equiv (cyclicLayerEquiv hp n e hn)
  · have h : Subsingleton (powerImage p n (R ⧸ Ideal.span {p ^ e})) := by
      rw [cyclicPower_eq_bot p n e (by omega)]
      infer_instance
    infer_instance

theorem cyclicLayer_finrank (hp : Irreducible p) (n e : ℕ) :
    let := residueField p hp
    Module.finrank (R ⧸ Ideal.span {p}) (gradedPiece p n (R ⧸ Ideal.span {p ^ e})) =
      if n < e then 1 else 0 := by
  let := residueField p hp
  split_ifs with hn
  · exact (cyclicLayerEquiv hp n e hn).finrank_eq.symm.trans (Module.finrank_self _)
  · have h : Subsingleton (powerImage p n (R ⧸ Ideal.span {p ^ e})) := by
      rw [cyclicPower_eq_bot p n e (by omega)]
      infer_instance
    exact Module.finrank_zero_of_subsingleton

end Dimension

/-- The dimension of the intrinsic layer counts the surviving elementary divisors. -/
theorem layerDimension : LayerDimension.{u, v} := by
  classical
  intro R _ _ _ M _ _ _ r t q e hq E p hp k hk
  let := residueField p hp
  let J := {i : Fin t // Associated p (q i)}
  let A (i : J) := R ⧸ Ideal.span {p ^ e i.val}
  let F := (gradedEquiv p (k - 1) (primaryPowerEquiv q e hq E p hp)).trans
    (gradedPiEquiv A p (k - 1))
  have (i : J) : Module.Finite (R ⧸ Ideal.span {p}) (gradedPiece p (k - 1) (A i)) :=
    cyclicLayer_finite hp (k - 1) (e i.val)
  refine ⟨Module.Finite.equiv F.symm, ?_⟩
  calc
    Module.finrank (R ⧸ Ideal.span {p}) (primaryLayer p k M) =
        Module.finrank (R ⧸ Ideal.span {p}) (∀ i : J, gradedPiece p (k - 1) (A i)) :=
      F.finrank_eq
    _ = ∑ i : J, Module.finrank (R ⧸ Ideal.span {p}) (gradedPiece p (k - 1) (A i)) :=
      Module.finrank_pi_fintype _
    _ = ∑ i : J, if k ≤ e i.val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [cyclicLayer_finrank hp]
      split_ifs <;> omega
    _ = Fintype.card {i : J // k ≤ e i.val} := by
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = Nat.card {i : Fin t // Associated p (q i) ∧ k ≤ e i} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun i : Fin t => Associated p (q i)) (fun i => k ≤ e i))

/-- Subtracting consecutive layer dimensions recovers every positive exponent
multiplicity. Natural subtraction is exact because the threshold sets decrease. -/
theorem exponentMultiplicity : ExponentMultiplicity.{u, v} := by
  classical
  intro R _ _ _ M _ _ _ r t q e hq E p hp k hk
  let := residueField p hp
  rw [(layerDimension R M r t q e hq E p hp k hk).2,
    (layerDimension R M r t q e hq E p hp (k + 1) (by omega)).2]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun i : Fin t => Associated p (q i) ∧ k ≤ e i)) =
      (Finset.univ.filter (fun i : Fin t => Associated p (q i) ∧ k + 1 ≤ e i)) ∪
      (Finset.univ.filter (fun i : Fin t => Associated p (q i) ∧ e i = k)) := by
    ext i
    by_cases hi : Associated p (q i)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hi]
      omega
    · simp [hi]
  have hd : Disjoint
      (Finset.univ.filter (fun i : Fin t => Associated p (q i) ∧ k + 1 ≤ e i))
      (Finset.univ.filter (fun i : Fin t => Associated p (q i) ∧ e i = k)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  rw [h, Finset.card_union_of_disjoint hd]
  omega

/-- Multiplication by p on the n-th image is exactly the next image, after
inclusion into the original module. -/
theorem powerImage_step_map {R : Type u} [CommRing R] (p : R) (n : ℕ)
    (N : Type v) [AddCommGroup N] [Module R N] :
    (p • (⊤ : Submodule R (powerImage p n N))).map (powerImage p n N).subtype =
      powerImage p (n + 1) N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hy
    obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp z.property
    apply (Submodule.mem_smul_pointwise_iff_exists ..).mpr
    refine ⟨w, Submodule.mem_top, ?_⟩
    change p ^ (n + 1) • w = p • z.val
    rw [pow_succ', mul_smul, hw]
  · intro hx
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists ..).mp hx
    let z : powerImage p n N :=
      ⟨p ^ n • y, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩
    refine ⟨p • z, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top, ?_⟩
    change p • (p ^ n • y) = p ^ (n + 1) • y
    rw [pow_succ', mul_smul]

theorem layerDenominator : LayerDenominator.{u, v} := by
  intro R _ p M _ _ k hk
  simpa only [Nat.sub_add_cancel hk] using
    powerImage_step_map p (k - 1) (primary R p M)

/-- The definition agrees with the paper's version inside the torsion submodule. -/
theorem primary_le_torsion {R : Type u} [CommRing R] [IsDomain R] {p : R}
    (hp : p ≠ 0) (M : Type v) [AddCommGroup M] [Module R M] :
    primary R p M ≤ Submodule.torsion R M := by
  intro x hx
  obtain ⟨n, hn⟩ := (primaryMembership R p M x).mp hx
  exact (Submodule.mem_torsion_iff x).mpr
    ⟨⟨p ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hp)⟩, hn⟩

theorem directSumLayerDimension : DirectSumLayerDimension.{u, v} := by
  intro R _ _ _ M _ _ _ r t q e hq E p hp k hk
  let U := DirectSum.linearEquivFunOnFintype R (Fin t)
    (fun i => R ⧸ Ideal.span {q i ^ e i})
  exact layerDimension R M r t q e hq
    (E.trans ((LinearEquiv.refl R _).prodCongr U)) p hp k hk

end D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
