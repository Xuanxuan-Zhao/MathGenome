import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorGaloisCorrespondence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RankOneMultiplicativeGroup
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.PV

open scoped Matrix Polynomial LaurentPolynomial
open Matrix (GeneralLinearGroup)
open private matrixAutomorphism_spec from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
open private finiteType_of_generatedByMatrix from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing

private theorem coe_det_fin_one {S : Type*} [CommRing S] (g : GL (Fin 1) S) :
    (g.det : S) = g 0 0 :=
  Matrix.det_fin_one g.val

private theorem det_fin_one_injective (S : Type*) [CommRing S] :
    Function.Injective (GeneralLinearGroup.det : GL (Fin 1) S → Sˣ) := by
  intro g h he
  apply Units.ext
  funext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simpa only [coe_det_fin_one] using
    congrArg Units.val he

open MatrixGroupCoordinates.Specs in
private theorem finite_of_proper_zeroLocus (C : Type*) [Field C]
    (G : Subgroup (GL (Fin 1) C)) (relations : Set (CoordinatePolynomial C 1))
    (hG : (G : Set (GL (Fin 1) C)) = zeroLocus relations)
    (hproper : G ≠ ⊤) : Finite G := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 1) C, g ∉ G := by
    by_contra! hall
    exact hproper (eq_top_iff.mpr fun g _ => hall g)
  change g ∉ (G : Set (GL (Fin 1) C)) at hg
  rw [hG] at hg
  change ¬ (∀ p ∈ relations, evalAt (C := C) g p = 0) at hg
  push Not at hg
  obtain ⟨p, hp, hpg⟩ := hg
  let coordinates : CoordinateVariable 1 → C[T;T⁻¹] :=
    Sum.elim (fun _ => LaurentPolynomial.T 1) (fun _ => LaurentPolynomial.T (-1))
  let f := MvPolynomial.eval₂Hom LaurentPolynomial.C coordinates p
  have heval (x : GL (Fin 1) C) :
      LaurentPolynomial.eval₂ (RingHom.id C) x.det f = evalAt (C := C) x p := by
    change (LaurentPolynomial.eval₂ (RingHom.id C) x.det).comp
      (MvPolynomial.eval₂Hom LaurentPolynomial.C coordinates) p = _
    rw [MvPolynomial.comp_eval₂Hom]
    have hc : (LaurentPolynomial.eval₂ (RingHom.id C) x.det).comp LaurentPolynomial.C =
        RingHom.id C := by ext r; simp
    rw [hc]
    change MvPolynomial.eval₂Hom (RingHom.id C) _ p =
      MvPolynomial.eval₂Hom (RingHom.id C)
        (Sum.elim (fun ij : Fin 1 × Fin 1 => x ij.1 ij.2) (fun _ : Unit => inverseDeterminant x)) p
    congr 2
    funext i
    cases i with
    | inl ij =>
      obtain ⟨i, j⟩ := ij
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [coordinates]
    | inr i => simp [coordinates, inverseDeterminant]
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow f
  have hevalq (x : GL (Fin 1) C) :
      q.eval (x.det : C) = evalAt (C := C) x p * (x.det : C) ^ n := by
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id C) x.det) hq
    simpa only [LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id, map_mul, heval,
      LaurentPolynomial.eval₂_T_n] using he
  have hqzero : q ≠ 0 := by
    intro hz
    exact (mul_ne_zero hpg (pow_ne_zero n g.det.ne_zero))
      ((hevalq g).symm.trans (by simp [hz]))
  have : Finite {x : C // q.IsRoot x} := q.finite_setOfPred_isRoot hqzero
  let embed (x : G) : {x : C // q.IsRoot x} := ⟨((x.val).det : C), by
    have hx : x.val ∈ zeroLocus relations := hG ▸ x.property
    change q.eval _ = 0
    rw [hevalq, hx p hp, zero_mul]⟩
  exact Finite.of_injective embed fun x y h =>
    Subtype.ext (det_fin_one_injective C (Units.ext (congrArg Subtype.val h)))

private theorem subgroup_le_rootsOfUnity_card {C : Type*} [Field C]
    (H : Subgroup Cˣ) : H ≤ rootsOfUnity (Nat.card H) C := by
  intro x hx
  rw [mem_rootsOfUnity]
  exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))

private theorem finite_subgroup_eq_rootsOfUnity {C : Type*} [Field C] [CharZero C]
    [IsAlgClosed C] (H : Subgroup Cˣ) [Finite H] :
    H = rootsOfUnity (Nat.card H) C := by
  have hm : 0 < Nat.card H := Nat.card_pos
  let : NeZero (Nat.card H) := ⟨hm.ne'⟩
  let : NeZero ((Nat.card H : ℕ) : C) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have hle := subgroup_le_rootsOfUnity_card H
  have hcard := HasEnoughRootsOfUnity.natCard_rootsOfUnity C (Nat.card H)
  have hsurj := (Nat.bijective_iff_injective_and_card (Subgroup.inclusion hle)).mpr
    ⟨Subgroup.inclusion_injective hle, hcard.symm⟩ |>.2
  refine le_antisymm hle ?_
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : y.val = x := congrArg Subtype.val hy
  exact hxy ▸ y.property

private theorem operator_pow_of_solution {kind : OperatorKind} {S : Type*} [CommRing S]
    (T : Specs.operator kind S) (a z : S) (hz : Specs.apply T z = a * z)
    (m : ℕ) (hm : 0 < m) :
    Specs.apply T (z ^ m) =
      match kind with
      | .differential => (m : S) * a * z ^ m
      | .difference => a ^ m * z ^ m := by
  cases kind with
  | differential =>
    let d := Specs.toDerivation T
    change d z = a * z at hz
    change d (z ^ m) = _
    rw [d.leibniz_pow, hz, nsmul_eq_mul, smul_eq_mul]
    calc
      (m : S) * (z ^ (m - 1) * (a * z)) = (m : S) * a * (z ^ (m - 1) * z) := by ring
      _ = (m : S) * a * z ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm]
  | difference =>
    let s := Specs.toRingEquiv T
    change s z = a * z at hz
    change s (z ^ m) = _
    rw [map_pow, hz, mul_pow]

/-- The quotient of two unit solutions of the same scalar equation is constant. -/
private theorem isConstant_unit_ratio {kind : OperatorKind} {S : Type*} [CommRing S]
    (T : Specs.operator kind S) (a : S) (u v : Sˣ)
    (hu : Specs.apply T (u : S) = a * u) (hv : Specs.apply T (v : S) = a * v) :
    Specs.isConstant T ((u * v⁻¹ : Sˣ) : S) := by
  let w := u * v⁻¹
  have hw : (w : S) * (v : S) = (u : S) := congrArg Units.val (inv_mul_cancel_right u v)
  cases kind with
  | differential =>
    let d := Specs.toDerivation T
    change d (u : S) = _ at hu
    change d (v : S) = _ at hv
    change d (w : S) = 0
    have h := congrArg d hw
    rw [d.leibniz, hv, hu, ← hw] at h
    simp only [smul_eq_mul] at h
    apply v.mul_left_inj.mp
    linear_combination h
  | difference =>
    let s := Specs.toRingEquiv T
    change s (u : S) = _ at hu
    change s (v : S) = _ at hv
    change s (w : S) = (w : S)
    have h := congrArg s hw
    rw [map_mul, hu, ← hw] at h
    apply (IsUnit.mul_left_inj (v.isUnit.map s)).mp
    simpa only [hv, mul_left_comm (w : S) a (v : S), mul_assoc] using h


/-- The rank-one Picard–Vessiot group and the criterion for its finite order. -/
theorem rankOneMultiplicativeGroup.{u, v} : Specs.rankOneMultiplicativeGroup.{u, v} := by
  classical
  intro kind K R _ _ _ δ A E T Y hbase hpv hY
  let Q := Specs.totalQuotientRing R
  let : Algebra K Q := Algebra.compHom Q (algebraMap K R)
  let C := Specs.constantSubfield δ
  let G := Specs.matrixGaloisGroup δ E Y
  let H := G.map GeneralLinearGroup.det
  let y := Units.map (algebraMap R Q).toMonoidHom Y.det
  let a := Specs.coefficientMatrix A 0 0
  let coefficient (m : ℕ) : K := match kind with
    | .differential => (m : K) * a
    | .difference => a ^ m
  let hasSolution (m : ℕ) : Prop :=
    ∃ b : Kˣ, Specs.apply δ (b : K) = coefficient m * (b : K)
  let inBase (m : ℕ) : Prop :=
    ∃ b : Kˣ, algebraMap K Q (b : K) = ((y ^ m : Qˣ) : Q)
  let fixed (m : ℕ) : Prop :=
    ((y ^ m : Qˣ) : Q) ∈ Specs.matrixFixedSubalgebra δ E Y (Set.univ : Set G)
  suffices
      (H = ⊤ ∨ ∃ m : ℕ, 0 < m ∧ H = rootsOfUnity m C) ∧
      (∀ m : ℕ, 0 < m →
        (H ≤ rootsOfUnity m C ↔ fixed m) ∧ (fixed m ↔ inBase m) ∧
          (inBase m ↔ hasSolution m)) ∧
      (Finite G ↔ ∃ m : ℕ, 0 < m ∧ hasSolution m) ∧
      (Finite G → IsLeast {m : ℕ | 0 < m ∧ hasSolution m} (Nat.card G)) by
    cases kind <;> exact this
  let : CharZero K := hbase.1
  let : IsAlgClosed C := hbase.2
  have hKR : Specs.isExtension δ E := hpv.1.1
  have hRQ : Specs.isExtension E T := hpv.2
  have hi : Function.Injective (algebraMap K Q) := hRQ.2.comp hKR.2
  let : Nontrivial Q := hi.nontrivial
  have hKQ : Specs.commutes δ T (algebraMap K Q) :=
    fun k => (congrArg (algebraMap R Q) (hKR.1 k)).trans (hRQ.1 _)
  let ι : C →+* Q := (algebraMap K Q).comp C.subtype
  have hι : Function.Injective ι := hi.comp Subtype.val_injective
  have hact (g : G) :
      Specs.matrixFractionAutomorphism δ E Y g (y : Q) = (y : Q) * ι (g.val.det : C) := by
    let τ := (Specs.matrixAutomorphism δ E Y g).val
    let j : C →+* R := (algebraMap K R).comp C.subtype
    have hg : GeneralLinearGroup.map τ.toRingHom Y = Y * GeneralLinearGroup.map j g.val :=
      matrixAutomorphism_spec Y g
    have hdet := congrArg GeneralLinearGroup.det hg
    rw [GeneralLinearGroup.map_det, map_mul, GeneralLinearGroup.map_det] at hdet
    change IsFractionRing.ringEquivOfRingEquiv τ.toRingEquiv (algebraMap R Q (Y.det : R)) =
      algebraMap R Q (Y.det : R) * algebraMap R Q (j (g.val.det : C))
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, ← map_mul]
    exact congrArg (fun z : Rˣ => algebraMap R Q (z : R)) hdet
  have hfixed (m : ℕ) : H ≤ rootsOfUnity m C ↔ fixed m := by
    change _ ↔ ∀ g ∈ (Set.univ : Set G),
      Specs.matrixFractionAutomorphism δ E Y g ((y : Q) ^ m) = (y : Q) ^ m
    have htest (g : G) :
        Specs.matrixFractionAutomorphism δ E Y g ((y : Q) ^ m) = (y : Q) ^ m ↔
          g.val.det ∈ rootsOfUnity m C := by
      rw [map_pow, hact, mul_pow]
      change ((y ^ m : Qˣ) : Q) * ι (g.val.det : C) ^ m = ((y ^ m : Qˣ) : Q) ↔ _
      rw [(y ^ m).isUnit.mul_eq_left, ← map_pow, ← map_one ι, hι.eq_iff, mem_rootsOfUnity]
      change ((g.val.det ^ m : Cˣ) : C) = ((1 : Cˣ) : C) ↔ g.val.det ^ m = 1
      exact (Units.val_injective : Function.Injective (Units.val : Cˣ → C)).eq_iff
    constructor
    · intro h g _
      exact (htest g).mpr (h (Subgroup.apply_coe_mem_map GeneralLinearGroup.det G g))
    · intro h x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      exact (htest ⟨g, hg⟩).mp (h ⟨g, hg⟩ (Set.mem_univ _))
  have hbot := (operatorGaloisCorrespondence δ A E T Y hbase hpv hY).2.2.2
  have hfixedBase (m : ℕ) : fixed m ↔ inBase m := by
    change ((y ^ m : Qˣ) : Q) ∈ Specs.matrixFixedSubalgebra δ E Y (Set.univ : Set G) ↔ _
    rw [hbot]
    change (∃ b : K, algebraMap K Q b = ((y ^ m : Qˣ) : Q)) ↔ inBase m
    constructor
    · rintro ⟨b, hb⟩
      have hb0 : b ≠ 0 := by
        intro h
        exact (y ^ m).ne_zero (by simpa [h] using hb.symm)
      exact ⟨Units.mk0 b hb0, hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨(b : K), hb⟩
  have hy : Specs.apply T (y : Q) = algebraMap K Q a * (y : Q) := by
    have hx := congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) hY
    change Specs.apply E (Y 0 0) =
      ∑ j : Fin 1, algebraMap K R (Specs.coefficientMatrix A 0 j) * Y j 0 at hx
    rw [Fin.sum_univ_one] at hx
    change Specs.apply T (algebraMap R Q (Y.det : R)) =
      algebraMap R Q (algebraMap K R a) * algebraMap R Q (Y.det : R)
    rw [coe_det_fin_one, ← hRQ.1, hx, map_mul]
  have hypow (m : ℕ) (hm : 0 < m) : Specs.apply T ((y ^ m : Qˣ) : Q) =
      algebraMap K Q (coefficient m) * ((y ^ m : Qˣ) : Q) := by
    simp only [Units.val_pow_eq_pow_val]
    rw [operator_pow_of_solution T _ _ hy m hm]
    cases kind <;> simp only [coefficient, map_mul, map_pow, map_natCast, mul_assoc]
  obtain ⟨Y₀, _, hgen⟩ := hpv.1.2.2
  let : Algebra.FiniteType K R := finiteType_of_generatedByMatrix hgen
  have hconstant := (Operator.constants_finiteType_fractionRing δ E T hbase
    hpv.1.2.1 hKR.1 hRQ.1).2
  have hbaseSolution (m : ℕ) (hm : 0 < m) : inBase m ↔ hasSolution m := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hi ?_⟩
      rw [hKQ, hb, hypow m hm, map_mul, hb]
    · rintro ⟨b, hb⟩
      let v := Units.map (algebraMap K Q).toMonoidHom b
      have hv : Specs.apply T (v : Q) = algebraMap K Q (coefficient m) * (v : Q) := by
        change Specs.apply T (algebraMap K Q (b : K)) = _
        rw [← hKQ, hb, map_mul]
        rfl
      let w := y ^ m * v⁻¹
      have hw := isConstant_unit_ratio T (algebraMap K Q (coefficient m)) (y ^ m) v (hypow m hm) hv
      have hmem : (w : Q) ∈ Specs.constantSubring T :=
        (Operator.mem_constantSubring T _).mpr hw
      obtain ⟨c, hc⟩ := hconstant ⟨(w : Q), hmem⟩
      have hc' : algebraMap K Q (c : K) = (w : Q) := congrArg Subtype.val hc
      have hc0 : (c : K) ≠ 0 := by
        intro h
        exact w.ne_zero (by simpa [h] using hc'.symm)
      refine ⟨Units.mk0 (c : K) hc0 * b, ?_⟩
      change algebraMap K Q ((c : K) * (b : K)) = _
      rw [map_mul, hc']
      exact congrArg Units.val (inv_mul_cancel_right (y ^ m) v)
  have eqv (m : ℕ) (hm : 0 < m) : H ≤ rootsOfUnity m C ↔ hasSolution m :=
    (hfixed m).trans ((hfixedBase m).trans (hbaseSolution m hm))
  let e : G ≃* H := G.equivMapOfInjective _ (det_fin_one_injective C)
  have hcard : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
  have hfiniteOrder (h : Finite G) : H = rootsOfUnity (Nat.card G) C := by
    have : Finite H := Finite.of_equiv G e.toEquiv
    rw [hcard]
    exact finite_subgroup_eq_rootsOfUnity H
  have hleCard (m : ℕ) (hm : 0 < m) (hle : H ≤ rootsOfUnity m C) : Nat.card G ≤ m := by
    let : NeZero m := ⟨hm.ne'⟩
    exact (Nat.card_le_card_of_injective ((Subgroup.inclusion hle).comp e.toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp e.injective)).trans (card_rootsOfUnity C m)
  refine ⟨?_, fun m hm => ⟨hfixed m, hfixedBase m, hbaseSolution m hm⟩, ?_, ?_⟩
  · by_cases h : H = ⊤
    · exact Or.inl h
    · have hG : G ≠ ⊤ := by
        intro hg
        apply h
        rw [show H = G.map GeneralLinearGroup.det from rfl, hg,
          Subgroup.map_top_of_surjective _ GeneralLinearGroup.det_surjective]
      have : Finite G := finite_of_proper_zeroLocus C G (Specs.tensorRatioRelations δ Y)
        (galoisCoordinateAlgebra δ A E Y hbase hpv.1 hY).1 hG
      exact Or.inr ⟨Nat.card G, Nat.card_pos, hfiniteOrder inferInstance⟩
  · constructor
    · intro h
      have hm : 0 < Nat.card G := Nat.card_pos
      exact ⟨Nat.card G, hm, (eqv _ hm).mp (le_of_eq (hfiniteOrder h))⟩
    · rintro ⟨m, hm, hb⟩
      let : NeZero m := ⟨hm.ne'⟩
      let hle := (eqv m hm).mpr hb
      exact Finite.of_injective ((Subgroup.inclusion hle).comp e.toMonoidHom)
        ((Subgroup.inclusion_injective hle).comp e.injective)
  · intro h
    have hm : 0 < Nat.card G := Nat.card_pos
    refine ⟨⟨hm, (eqv _ hm).mp (le_of_eq (hfiniteOrder h))⟩, ?_⟩
    rintro m ⟨hm, hb⟩
    exact hleCard m hm ((eqv m hm).mpr hb)

end GaloisFormalization.PV
