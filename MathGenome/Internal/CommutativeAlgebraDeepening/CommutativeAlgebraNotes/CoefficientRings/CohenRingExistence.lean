import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.DiscreteValuationResidueAdjunction
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Order.Zorn
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open scoped Padic
open Function

universe u v

private theorem uniformizer_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {t : R} (ht : maximalIdeal R = Ideal.span {t}) : t ≠ 0 :=
  fun h ↦ IsDiscreteValuationRing.not_a_field R <| by
    rw [ht, h, Ideal.span_singleton_eq_bot.mpr rfl]

private theorem exists_unit_mul_pow_of_isHausdorff {R : Type*} [CommRing R] [IsLocalRing R]
    [IsHausdorff (maximalIdeal R) R] {t : R} (ht : maximalIdeal R = Ideal.span {t})
    {x : R} (hx : x ≠ 0) : ∃ (n : ℕ) (u : Rˣ), x = (u : R) * t ^ n := by
  classical
  have h : ∃ n : ℕ, ¬ t ^ n ∣ x := by
    by_contra! hn
    apply hx
    apply (inferInstance : IsHausdorff (maximalIdeal R) R).haus'
    intro n
    simpa [SModEq.zero, ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hn n
  let n := Nat.find h
  have hn : ¬ t ^ n ∣ x := Nat.find_spec h
  have hnpos : 0 < n := by
    by_contra! h0
    have : n = 0 := Nat.eq_zero_of_le_zero h0
    exact hn (by simp [this])
  obtain ⟨m, hmn⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have hd : t ^ m ∣ x := by
    by_contra hm
    exact (Nat.find_min h (show m < n by rw [hmn]; exact Nat.lt_succ_self _)) hm
  obtain ⟨y, rfl⟩ := hd
  have hy : IsUnit y := by
    by_contra hny
    have hym : y ∈ maximalIdeal R := hny
    rw [ht, Ideal.mem_span_singleton] at hym
    obtain ⟨z, rfl⟩ := hym
    apply hn
    refine ⟨z, ?_⟩
    rw [hmn, pow_succ, mul_assoc]
  exact ⟨m, hy.unit, by rw [hy.unit_spec, mul_comm]⟩

private theorem isDomain_of_unit_mul_pow {R : Type*} [CommRing R] [Nontrivial R] {t : R}
    (hreg : ∀ y : R, t * y = 0 → y = 0)
    (hfactor : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), x = (u : R) * t ^ n) :
    IsDomain R := by
  have hpow (n : ℕ) (y : R) : t ^ n * y = 0 → y = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact fun h ↦ ih (hreg _ h)
  let : NoZeroDivisors R := ⟨fun {x y} hxy ↦ or_iff_not_imp_left.mpr fun hx ↦ by
    obtain ⟨n, u, rfl⟩ := hfactor x hx
    apply hpow n
    rwa [mul_assoc, Units.mul_right_eq_zero] at hxy⟩
  exact NoZeroDivisors.to_isDomain R

private theorem dvr_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t : R} (ht : t ≠ 0) (hm : maximalIdeal R = Ideal.span {t})
    (hfactor : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), x = (u : R) * t ^ n) :
    IsDiscreteValuationRing R := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨t, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ht hm, ?_⟩
  intro x hx
  obtain ⟨n, u, hu⟩ := hfactor x hx
  exact ⟨n, u, (mul_comm _ _).trans hu.symm⟩

private theorem completeDVR {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CharZero R] (p : ℕ) (k : Type v) [Field k]
    (hp : maximalIdeal R = Ideal.span {(p : R)}) (e : ResidueField R ≃+* k) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
      CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
        maximalIdeal Λ = Ideal.span {(p : Λ)} ∧ Nonempty (ResidueField Λ ≃+* k) := by
  let A := AdicCompletion (maximalIdeal R) R
  let f : R →+* A := algebraMap R A
  have hm : maximalIdeal A = Ideal.span {(p : A)} := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    change (maximalIdeal R).map f = _
    refine (congrArg (Ideal.map f) hp).trans ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hf : Function.Injective f := AdicCompletion.of_injective (maximalIdeal R) R
  have tp : (p : R) ≠ 0 := uniformizer_ne_zero hp
  have hreg (y : A) (hy : (p : A) * y = 0) : y = 0 := by
    apply (smul_eq_zero.mp (show (p : R) • y = 0 by simpa [Algebra.smul_def] using hy)).resolve_left tp
  have hfactor (x : A) (hx : x ≠ 0) :=
    exists_unit_mul_pow_of_isHausdorff hm hx
  let : IsDomain A := isDomain_of_unit_mul_pow hreg hfactor
  have hpA : (p : A) ≠ 0 := by
    intro h
    exact tp (hf (by simpa using h))
  let : IsDiscreteValuationRing A := dvr_of_unit_mul_pow hpA hm hfactor
  let E := RingEquiv.ofBijective (ResidueField.map f) (AdicCompletion.residueField_map_bijective R)
  exact ⟨A, inferInstance, inferInstance, inferInstance, charZero_of_injective_ringHom hf,
    inferInstance, hm, ⟨E.symm.trans e⟩⟩

private abbrev DigitStreams (k : Type u) := ℕ → k

/-- An ambient set with room to extend any embedding of a stage. -/
private abbrev StageSpace (k : Type u) := Set (DigitStreams k) × DigitStreams k

/-- Choosing a representative of each residue class gives an injective digit encoding. -/
private noncomputable def digitEmbedding {R k : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k] {t : R} (hm : maximalIdeal R = Ideal.span {t})
    (r : R →+* k) (hr : RingHom.ker r = maximalIdeal R) : R ↪ DigitStreams k := by
  classical
  let rep : k → R := invFun r
  have hd (x : R) : t ∣ x - rep (r x) := by
    apply Ideal.mem_span_singleton.mp
    have hrep : r (rep (r x)) = r x := invFun_eq (f := (r : R → k)) ⟨x, rfl⟩
    rw [← hm, ← hr, RingHom.mem_ker, map_sub, hrep, sub_self]
  let digitTail (x : R) : R := (hd x).choose
  have ht (x : R) : x - rep (r x) = t * digitTail x := (hd x).choose_spec
  refine ⟨fun x n ↦ r ((digitTail^[n]) x), ?_⟩
  intro x y h
  have hdif (a b : R) (hab : r a = r b) : a - b = t * (digitTail a - digitTail b) := by
    rw [mul_sub, ← ht, ← ht, hab, sub_sub_sub_cancel_right]
  have hn (n : ℕ) : x - y = t ^ n * ((digitTail^[n]) x - (digitTail^[n]) y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, pow_succ, mul_assoc, Function.iterate_succ_apply', Function.iterate_succ_apply']
      congr 1
      exact hdif _ _ (congrFun h n)
  apply sub_eq_zero.mp
  apply (inferInstance : IsHausdorff (maximalIdeal R) R).haus'
  intro n
  have hdiv : t ^ n ∣ x - y := ⟨_, hn n⟩
  simpa [SModEq.zero, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hdiv

/-- An injection into the ambient set extends along an injection between two stages. -/
private theorem extendStageEmbedding {R S k : Type*} (f : R ↪ S) (e : R ↪ StageSpace k)
    (c : S ↪ DigitStreams k) :
    ∃ E : S ↪ StageSpace k, ∀ x, E (f x) = e x := by
  classical
  let d : R ↪ DigitStreams k := f.trans c
  let first : DigitStreams k → Set (DigitStreams k) := fun y ↦
    if h : y ∈ Set.range d then (e h.choose).1 else ∅
  have hfirst (x : R) : first (d x) = (e x).1 := by
    have h : d x ∈ Set.range d := ⟨x, rfl⟩
    rw [show first (d x) = (e h.choose).1 from dite_eq_left h, d.injective h.choose_spec]
  obtain ⟨U, hU⟩ : ∃ U, ∀ y, first y ≠ U := by
    simpa only [Surjective, not_forall, not_exists] using Function.cantor_surjective first
  have hU' (x : R) : (e x).1 ≠ U := by rw [← hfirst]; exact hU _
  let g (y : S) : StageSpace k := if h : y ∈ Set.range f then e h.choose else (U, c y)
  have hg (x : R) : g (f x) = e x := by
    have h : f x ∈ Set.range f := ⟨x, rfl⟩
    rw [show g (f x) = e h.choose from dite_eq_left h, f.injective h.choose_spec]
  refine ⟨⟨g, ?_⟩, hg⟩
  intro x y hexy
  by_cases hx : x ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range f
    · obtain ⟨b, rfl⟩ := hy
      exact congrArg f (e.injective ((hg a).symm.trans (hexy.trans (hg b))))
    · rw [hg, show g y = (U, c y) from dite_eq_right hy] at hexy
      exact (hU' a (congrArg Prod.fst hexy)).elim
  · by_cases hy : y ∈ Set.range f
    · obtain ⟨b, rfl⟩ := hy
      rw [show g x = (U, c x) from dite_eq_right hx, hg] at hexy
      exact (hU' b (congrArg Prod.fst hexy.symm)).elim
    · rw [show g x = (U, c x) from dite_eq_right hx, show g y = (U, c y) from dite_eq_right hy] at hexy
      exact c.injective (congrArg Prod.snd hexy)

/-- A DVR whose residue field is embedded in the prescribed field.
The set embedding makes transition maps between any two fixed stages unique. -/
private structure CohenStage (p : ℕ) (k : Type u) [Field k] where
  carrier : Type u
  [ring : CommRing carrier]
  [domain : IsDomain carrier]
  [dvr : IsDiscreteValuationRing carrier]
  uniformizer : maximalIdeal carrier = Ideal.span {(p : carrier)}
  reduction : carrier →+* k
  ker_reduction : RingHom.ker reduction = maximalIdeal carrier
  embedding : carrier ↪ StageSpace k

namespace CohenStage

attribute [local instance] CohenStage.ring CohenStage.domain CohenStage.dvr

variable {p : ℕ} {k : Type u} [Field k]

/-- Put a ring into the universe of the residue field by transporting its structure
to the range of its embedding. -/
private noncomputable def ofEmbedding {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hm : maximalIdeal R = Ideal.span {(p : R)})
    (r : R →+* k) (hr : RingHom.ker r = maximalIdeal R) (e : R ↪ StageSpace k) :
    Σ B : CohenStage p k, R ≃+* B.carrier := by
  let B := Set.range (e : R → StageSpace k)
  let eqv : B ≃ R := (Equiv.ofInjective e e.injective).symm
  letI : CommRing B := eqv.commRing
  let E : B ≃+* R := eqv.ringEquiv
  letI : IsDomain B := E.injective.isDomain E
  letI : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm
  have hmB : maximalIdeal B = Ideal.span {(p : B)} := by
    rw [← map_ringEquiv_maximalIdeal E.symm, hm]
    change (Ideal.span {(p : R)}).map E.symm.toRingHom = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  letI : IsLocalHom E.toRingHom := IsLocalHom.of_surjective _ E.surjective
  have hrB : RingHom.ker (r.comp E.toRingHom) = maximalIdeal B := by
    rw [← RingHom.comap_ker, hr, maximalIdeal_comap]
  exact ⟨⟨B, hmB, r.comp E.toRingHom, hrB, ⟨Subtype.val, Subtype.val_injective⟩⟩, E.symm⟩

instance : Preorder (CohenStage p k) where
  le A B := ∃ f : A.carrier →+* B.carrier,
    (∀ x, B.embedding (f x) = A.embedding x) ∧ B.reduction.comp f = A.reduction
  le_refl A := ⟨RingHom.id _, fun _ ↦ rfl, rfl⟩
  le_trans := by
    rintro A B C ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    exact ⟨g.comp f, fun x ↦ (hg (f x)).trans (hf x), by
      rw [← RingHom.comp_assoc, hg', hf']⟩

private noncomputable def transition {A B : CohenStage p k} (h : A ≤ B) :
    A.carrier →+* B.carrier := h.choose

private theorem transition_embedding {A B : CohenStage p k} (h : A ≤ B) (x : A.carrier) :
    B.embedding (transition h x) = A.embedding x := h.choose_spec.1 x

private theorem transition_reduction {A B : CohenStage p k} (h : A ≤ B) (x : A.carrier) :
    B.reduction (transition h x) = A.reduction x :=
  RingHom.congr_fun h.choose_spec.2 x

private theorem transition_injective {A B : CohenStage p k} (h : A ≤ B) :
    Function.Injective (transition h) := fun x y hxy ↦
  A.embedding.injective ((transition_embedding h x).symm.trans ((congrArg B.embedding hxy).trans
    (transition_embedding h y)))

/-- A nonempty chain has an upper bound given by its directed limit. -/
private theorem chain_bddAbove [CharP k p] (c : Set (CohenStage p k))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) : BddAbove c := by
  classical
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun i j ↦ by
    obtain ⟨m, hm, him, hjm⟩ := hc.directedOn i.1 i.2 j.1 j.2
    exact ⟨⟨m, hm⟩, him, hjm⟩⟩
  let F (i : c) := i.1.carrier
  let f (i j : c) (h : i ≤ j) : F i →+* F j := transition h
  let : DirectedSystem F (f · · ·) :=
    { map_self := fun {i} x ↦ i.1.embedding.injective (transition_embedding (le_refl i.1) x)
      map_map := fun {m j i} hij hjm x ↦ m.1.embedding.injective (by
        change m.1.embedding (transition hjm (transition hij x)) =
          m.1.embedding (transition (hij.trans hjm) x)
        rw [transition_embedding, transition_embedding, transition_embedding]) }
  let L := DirectLimit F f
  let incl (i : c) : F i →+* L := DirectLimit.Ring.of F f i
  have hincl (i : c) : Function.Injective (incl i) :=
    DirectLimit.mk_injective f (fun _ _ h ↦ transition_injective h) i
  let r : L →+* k := DirectLimit.Ring.lift F f k (fun i ↦ i.1.reduction)
    (fun _ _ h x ↦ transition_reduction h x)
  let emb : L ↪ StageSpace k :=
    ⟨DirectLimit.lift f (fun i x ↦ i.1.embedding x)
      (fun _ _ h x ↦ (transition_embedding h x).symm),
      DirectLimit.lift_injective f _ _ (fun i ↦ i.1.embedding.injective)⟩
  let : Nontrivial L := r.domain_nontrivial
  have hp0 : r (p : L) = 0 := by rw [map_natCast, CharP.cast_eq_zero k p]
  have hreg (y : L) (hy : (p : L) * y = 0) : y = 0 := by
    obtain ⟨i, z, rfl⟩ := DirectLimit.exists_eq_mk f y
    change (p : L) * incl i z = 0 at hy
    rw [← map_natCast (incl i) p, ← map_mul, ← map_zero (incl i)] at hy
    have hz := (mul_eq_zero.mp (hincl i hy)).resolve_left (uniformizer_ne_zero i.1.uniformizer)
    change incl i z = 0
    rw [hz, map_zero]
  have hfactor (x : L) (hx : x ≠ 0) : ∃ (n : ℕ) (u : Lˣ), x = (u : L) * (p : L) ^ n := by
    obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
    change incl i y ≠ 0 at hx
    have hy : y ≠ 0 := fun h ↦ hx (by rw [h, map_zero])
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr i.1.uniformizer)
    refine ⟨n, Units.map (incl i).toMonoidHom u, ?_⟩
    change incl i y = incl i (u : F i) * (p : L) ^ n
    rw [hu, map_mul, map_pow, map_natCast (incl i) p]
  let : IsDomain L := isDomain_of_unit_mul_pow hreg hfactor
  have hunit (x : L) : IsUnit x ↔ r x ≠ 0 := by
    refine ⟨fun hx ↦ (hx.map r).ne_zero, ?_⟩
    obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
    intro hy
    change i.1.reduction y ≠ 0 at hy
    have hy' : y ∉ maximalIdeal (F i) := by
      rw [← i.1.ker_reduction, RingHom.mem_ker]
      exact hy
    exact (not_not.mp hy').map (incl i)
  let : IsLocalRing L := IsLocalRing.of_nonunits_add fun x y hx hy ↦ by
    change ¬IsUnit x at hx
    change ¬IsUnit y at hy
    change ¬IsUnit (x + y)
    rw [hunit, not_not] at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  have hker : RingHom.ker r = maximalIdeal L := by
    ext x
    change r x = 0 ↔ ¬IsUnit x
    rw [hunit, not_not]
  have hm : maximalIdeal L = Ideal.span {(p : L)} := by
    rw [← hker]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    refine ⟨?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
      intro hx
      change i.1.reduction y = 0 at hx
      have hy : y ∈ RingHom.ker i.1.reduction := hx
      rw [i.1.ker_reduction, i.1.uniformizer, Ideal.mem_span_singleton] at hy
      change (p : L) ∣ incl i y
      rw [← map_natCast (incl i) p]
      exact map_dvd (incl i) hy
    · rintro ⟨y, rfl⟩
      rw [map_mul, hp0, zero_mul]
  have hpL : (p : L) ≠ 0 := fun h ↦ one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  let : IsDiscreteValuationRing L := dvr_of_unit_mul_pow hpL hm hfactor
  let B := ofEmbedding hm r hker emb
  refine ⟨B.1, fun i hi ↦ ⟨B.2.toRingHom.comp (incl ⟨i, hi⟩), ?_, ?_⟩⟩
  · intro x
    rfl
  · apply RingHom.ext
    intro x
    change r (B.2.symm (B.2 (incl ⟨i, hi⟩ x))) = i.reduction x
    rw [RingEquiv.symm_apply_apply]
    rfl

/-- Adjoin a representative of the specified element to the residue field. -/
private theorem exists_extension [CharP k p] (hp : p.Prime) (A : CohenStage p k) (a : k) :
    ∃ B : CohenStage p k, A ≤ B ∧ a ∈ Set.range B.reduction := by
  let φ : ResidueField A.carrier →+* k :=
    Ideal.Quotient.lift _ A.reduction A.ker_reduction.ge
  let K := φ.fieldRange
  let e₀ : ResidueField A.carrier ≃+* K := φ.rangeRestrictFieldEquiv
  let : CharP K p := K.subtype.charP K.subtype_injective p
  let Q := IntermediateField.adjoin K ({a} : Set k)
  let b : Q := ⟨a, IntermediateField.subset_adjoin K _ (Set.mem_singleton a)⟩
  have hb : IntermediateField.adjoin K ({b} : Set Q) = ⊤ := by
    apply IntermediateField.map_injective Q.val
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    change Q = (⊤ : IntermediateField K Q).map Q.val
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, IntermediateField.mem_top, rfl⟩
    · rintro ⟨y, _, rfl⟩
      exact y.property
  obtain ⟨D, _, _, _, f, _, hf, hm, eD, hcompat⟩ :=
    discreteValuationResidueAdjunction p hp A.carrier A.uniformizer K e₀ Q b hb
  let iQ : Q →+* k := Q.val.toRingHom
  let s := iQ.comp eD.toRingHom
  let r : D →+* k := s.comp (residue D)
  have hr : RingHom.ker r = maximalIdeal D := by
    rw [RingHom.ker_comp_of_injective _ s.injective, ker_residue]
  obtain ⟨E, hE⟩ := extendStageEmbedding ⟨f, hf⟩ A.embedding (digitEmbedding hm r hr)
  let B : CohenStage p k := ⟨D, hm, r, hr, E⟩
  refine ⟨B, ⟨f, hE, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro x
    change iQ (eD (residue D (f x))) = A.reduction x
    rw [← ResidueField.map_residue]
    have h := RingHom.congr_fun hcompat (residue A.carrier x)
    change eD (ResidueField.map f (residue A.carrier x)) =
      algebraMap K Q (e₀ (residue A.carrier x)) at h
    rw [h]
    rfl
  · obtain ⟨x, hx⟩ := residue_surjective (eD.symm b)
    refine ⟨x, ?_⟩
    change iQ (eD (residue D x)) = a
    rw [hx, RingEquiv.apply_symm_apply]
    rfl

/-- The initial stage has residue field the prime subfield of `k`. -/
private noncomputable def padicStage [CharP k p] [Fact p.Prime] :
    Σ A : CohenStage p k, ℤ_[p] ≃+* A.carrier := by
  let r : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod
  have hr : RingHom.ker r = maximalIdeal ℤ_[p] := by
    rw [RingHom.ker_comp_of_injective _ (ZMod.castHom_injective k), PadicInt.ker_toZMod]
  let d := digitEmbedding PadicInt.maximalIdeal_eq_span_p r hr
  exact ofEmbedding PadicInt.maximalIdeal_eq_span_p r hr
    ⟨fun x ↦ (∅, d x), fun _ _ h ↦ d.injective (congrArg Prod.snd h)⟩

end CohenStage

attribute [local instance] CohenStage.ring CohenStage.domain CohenStage.dvr

/-- Existence of a complete Cohen ring of characteristic zero with prescribed residue field. -/
theorem cohenRingExistence : Specs.cohenRingExistenceType := by
  classical
  intro p hp k _ _
  let : Fact p.Prime := ⟨hp⟩
  let initial : Σ A : CohenStage p k, ℤ_[p] ≃+* A.carrier := CohenStage.padicStage
  obtain ⟨A, hinit, hmax⟩ := zorn_le_nonempty₀ (Set.univ : Set (CohenStage p k))
    (fun c _ hc y hy ↦ by
      obtain ⟨B, hB⟩ := CohenStage.chain_bddAbove c hc ⟨y, hy⟩
      exact ⟨B, Set.mem_univ B, hB⟩)
    initial.1 (Set.mem_univ _)
  have hsurj : Function.Surjective A.reduction := by
    intro a
    obtain ⟨B, hAB, y, hy⟩ := CohenStage.exists_extension hp A a
    have hBA : B ≤ A := hmax.le_of_ge (Set.mem_univ B) hAB
    exact ⟨CohenStage.transition hBA y, (CohenStage.transition_reduction hBA y).trans hy⟩
  let g : ℤ_[p] →+* A.carrier := (CohenStage.transition hinit).comp initial.2.toRingHom
  have hg : Function.Injective g := (CohenStage.transition_injective hinit).comp initial.2.injective
  have : CharZero A.carrier := charZero_of_injective_ringHom (f := g) hg
  let e : ResidueField A.carrier ≃+* k :=
    (Ideal.quotEquivOfEq A.ker_reduction.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  exact completeDVR p k A.uniformizer e

end CommutativeAlgebraNotes.CoefficientRings
