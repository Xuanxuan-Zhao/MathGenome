import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateFixedRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RationalInvariantSeparation
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorGaloisCorrespondence
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.PV

open scoped Matrix MatrixGroupCoordinates.Specs nonZeroDivisors

open private finiteType_of_generatedByMatrix stable_range_of_commutes from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing

private theorem field_hasInnerInverse {Q : Type*} [CommRing Q] (h : IsField Q) (x : Q) :
    ∃ y, x * (x * y) = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
    exact ⟨y, by rw [hy, mul_one]⟩

private theorem regularElementsAreUnits_of_fixed {K Q G : Type*}
    [Field K] [CommRing Q] [Algebra K Q]
    (F : Subalgebra K Q) (act : G → Q ≃+* Q) (S : Set G)
    (hfix : ∀ x : Q, x ∈ F ↔ ∀ g ∈ S, act g x = x)
    (hQ : ∀ x : Q, ∃ y, x * (x * y) = x) :
    ProjectionKernels.RegularElementsAreUnits F := by
  intro x hx
  let a : Q := x
  have ha := (hfix a).mp x.property
  obtain ⟨b, hb⟩ := hQ a
  -- The complementary idempotent is intrinsic to a, so it is fixed.
  have hproduct (c : Q) (hc : a * (a * c) = a) : a * c = a * b := by
    calc
      a * c = (a * (a * b)) * c := by rw [hb]
      _ = (a * (a * c)) * b := by ac_rfl
      _ = a * b := by rw [hc]
  have hmem : 1 - a * b ∈ F := (hfix _).mpr fun g hg => by
    have hb' : a * (a * act g b) = a := by
      simpa only [map_mul, ha g hg] using congrArg (act g) hb
    rw [map_sub, map_one, map_mul, ha g hg, hproduct _ hb']
  let z : F := ⟨1 - a * b, hmem⟩
  have haz : x * z = 0 := by
    apply Subtype.ext
    change a * (1 - a * b) = 0
    rw [mul_sub, mul_one, hb, sub_self]
  have hz : (1 : Q) - a * b = 0 :=
    congrArg Subtype.val (mem_nonZeroDivisors_iff_left.mp hx z haz)
  have hab : a * b = 1 := (sub_eq_zero.mp hz).symm
  have hunit : IsUnit a := .of_mul_eq_one b hab
  have hbmem : b ∈ F := (hfix b).mpr fun g hg => by
    apply hunit.mul_left_cancel
    have hmap := congrArg (act g) hab
    rw [map_mul, ha g hg, map_one] at hmap
    exact hmap.trans hab.symm
  exact .of_mul_eq_one ⟨b, hbmem⟩ (Subtype.ext hab)

private theorem isStable_of_fixed {kind : OperatorKind} {Q G : Type*} [CommRing Q]
    (T : Specs.operator kind Q) (act : G → Q ≃+* Q)
    (hact : ∀ g, Specs.commutes T T (act g)) (S : Set G) :
    Specs.isStable T {x | ∀ g ∈ S, act g x = x} := by
  have forward {x : Q} (hx : ∀ g ∈ S, act g x = x) :
      ∀ g ∈ S, act g (Specs.apply T x) = Specs.apply T x := by
    intro g hg
    exact (hact g x).trans (congrArg (Specs.apply T) (hx g hg))
  cases kind with
  | differential => exact fun _ hx => forward hx
  | difference =>
    refine ⟨fun _ hx => forward hx, ?_⟩
    intro x hx g hg
    have h : Operator.Commutes (kind := .difference) T T (act g) := hact g
    exact (h.difference_symm x).trans (congrArg (Specs.toRingEquiv T).symm (hx g hg))

/-- Closed subgroups and intermediate operator total rings correspond by taking
fixed subalgebras and pointwise stabilizers. -/
theorem operatorGaloisCorrespondence.{u, v} :
    Specs.operatorGaloisCorrespondence.{u, v} := by
  classical
  intro kind K R _ _ _ n δ A E T Y hbase hpv hY
  let Q := Specs.totalQuotientRing R
  let G := Specs.matrixGaloisGroup δ E Y
  let act : G → Q ≃+* Q := Specs.matrixFractionAutomorphism δ E Y
  let fixed (H : Subgroup G) : Subalgebra K Q :=
    Specs.matrixFixedSubalgebra δ E Y (H : Set G)
  let ClosedSubgroups := {H : Subgroup G // IsClosed (H : Set G)}
  let IntermediateTotalRings := {F : Subalgebra K Q // Specs.isIntermediateTotalRing T F}
  let : CharZero K := hbase.1
  have hsimple := hpv.1.2.1
  obtain ⟨Y₀, _, hgen⟩ := hpv.1.2.2
  let : Algebra.FiniteType K R := finiteType_of_generatedByMatrix hgen
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have hfield : kind = .differential → IsField Q := by
    intro h
    subst kind
    let : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ K)
    exact (Operator.simpleDifferentialFractionField (K := Q) E hsimple).2
  have hinner : ∀ x : Q, ∃ y, x * (x * y) = x := by
    cases kind with
    | differential => exact field_hasInnerInverse (hfield rfl)
    | difference =>
      obtain ⟨_, _, _, hfields, _, _, _, eQ, _⟩ :=
        simpleDifferenceFractionComponents (K := Q) (Specs.toRingEquiv E)
          (Specs.toRingEquiv T) hsimple hpv.2.1
      intro x
      choose y hy using fun i => field_hasInnerInverse (hfields i) (eQ x i)
      refine ⟨eQ.symm y, eQ.injective ?_⟩
      rw [map_mul, map_mul, eQ.apply_symm_apply]
      exact funext hy
  have hact (g : G) : Specs.commutes T T (act g) := by
    obtain ⟨e, he, _⟩ := galoisTotalRingAction δ A E Y T hbase hpv.1 hY hpv.2.1
    change Specs.commutes T T (Specs.matrixFractionAutomorphism δ E Y g)
    rw [← he g]
    exact (e g).property
  have hfixed (H : Subgroup G) : Specs.isIntermediateTotalRing T (fixed H) :=
    ⟨isStable_of_fixed T act hact (H : Set G),
      regularElementsAreUnits_of_fixed (fixed H) act (H : Set G) (fun _ => Iff.rfl) hinner⟩
  have hrelative (F : IntermediateTotalRings) :=
    intermediateFixedRing δ A E T Y hbase hpv hY F.val F.property
  let stabilizer (F : IntermediateTotalRings) : ClosedSubgroups := by
    let J := Classical.choose (hrelative F).1
    have hJ := (Classical.choose_spec (hrelative F).1).2
    exact ⟨J.comap G.subtype, hJ.preimage continuous_subtype_val⟩
  have hstabilizer (F : IntermediateTotalRings) :
      ((stabilizer F).val : Set G) = Specs.relativeStabilizer δ E Y F.val := by
    let pullback (s : Set (GL (Fin n) (Specs.constantSubfield δ))) : Set G :=
      Subtype.val ⁻¹' s
    exact (congrArg pullback (Classical.choose_spec (hrelative F).1).1).trans
      (Set.preimage_image_eq _ Subtype.val_injective)
  let toFixed (H : ClosedSubgroups) : IntermediateTotalRingsᵒᵈ :=
    OrderDual.toDual ⟨fixed H.val, hfixed H.val⟩
  let toStabilizer (F : IntermediateTotalRingsᵒᵈ) : ClosedSubgroups :=
    stabilizer (OrderDual.ofDual F)
  have leftInv (H : ClosedSubgroups) : toStabilizer (toFixed H) = H := by
    apply Subtype.ext
    apply SetLike.coe_injective
    rw [hstabilizer (OrderDual.ofDual (toFixed H))]
    ext g
    constructor
    · intro hg
      by_contra hnot
      obtain ⟨q, hq, hmove⟩ :=
        rationalInvariantSeparation δ A E Y hbase hpv.1 hY H.val H.property g hnot
      exact hmove (hg ⟨q, fun h hh => hq ⟨h, hh⟩⟩)
    · intro hg q
      exact q.property g hg
  have rightInv (F : IntermediateTotalRingsᵒᵈ) : toFixed (toStabilizer F) = F := by
    apply Subtype.ext
    change Specs.matrixFixedSubalgebra δ E Y ((stabilizer (OrderDual.ofDual F)).val : Set G) =
      (OrderDual.ofDual F).val
    rw [hstabilizer]
    exact (hrelative (OrderDual.ofDual F)).2
  let bijection : ClosedSubgroups ≃ IntermediateTotalRingsᵒᵈ :=
    ⟨toFixed, toStabilizer, leftInv, rightInv⟩
  have hforward : Monotone bijection := by
    intro H J h x hx g hg
    exact hx g (h hg)
  have hbackward : Monotone bijection.symm := by
    intro F F' h g hg
    change g ∈ ((stabilizer (OrderDual.ofDual F'))).val
    rw [← SetLike.mem_coe, hstabilizer]
    change g ∈ ((stabilizer (OrderDual.ofDual F))).val at hg
    rw [← SetLike.mem_coe, hstabilizer] at hg
    intro x
    exact hg ⟨x, h x.property⟩
  let correspondence := bijection.toOrderIso hforward hbackward
  refine ⟨hfixed, ⟨correspondence, (fun _ => rfl), hstabilizer⟩, ?_, ?_⟩
  · intro h
    refine ⟨hfield h, fun F => and_congr_right fun _ => ?_⟩
    constructor
    · intro hF
      let : Field Q := (hfield h).toField
      exact ProjectionKernels.subring_isField_of_regular_isUnit F.toSubring hF
    · intro hF x hx
      let : Field F := hF.toField
      exact isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero hx)
  · have hbaseExtension : Operator.IsExtension (R := K) (S := Q) δ T :=
      IsPicardVessiotTotalExtension.isExtension (A := A) (E := E) hpv
    let : Nontrivial Q := hbaseExtension.2.nontrivial
    have hbot : Specs.isIntermediateTotalRing T (⊥ : Subalgebra K Q) := by
      constructor
      · change Specs.isStable T (Set.range (algebraMap K Q))
        exact stable_range_of_commutes hbaseExtension.1
      · intro x hx
        let e := Algebra.botEquivOfInjective hbaseExtension.2
        have hx' : e x ≠ 0 := fun h => nonZeroDivisors.ne_zero hx
          (e.injective (h.trans (map_zero e).symm))
        have hu := (isUnit_iff_ne_zero.mpr hx').map e.symm.toRingHom
        change IsUnit (e.symm (e x)) at hu
        rwa [e.symm_apply_apply] at hu
    have hstabBot :
        Specs.relativeStabilizer δ E Y (⊥ : Subalgebra K Q) = (Set.univ : Set G) := by
      apply Set.eq_univ_of_forall
      intro g x
      have hle : (⊥ : Subalgebra K Q) ≤
          Specs.matrixFixedSubalgebra δ E Y (Set.univ : Set G) := bot_le
      exact (hle x.property) g (Set.mem_univ _)
    rw [← hstabBot]
    exact (hrelative ⟨⊥, hbot⟩).2

end GaloisFormalization.PV
