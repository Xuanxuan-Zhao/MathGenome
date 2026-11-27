import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.AlgebraicElementsAndOrbits
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorGaloisCorrespondence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.MatrixGroupIdentityComponent
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Ring.Action.End

namespace GaloisFormalization.PV

open scoped Matrix MatrixGroupCoordinates.Specs
open MatrixGroupIdentityComponent.Specs (identityComponent)
open MatrixGroupIdentityComponent (identityComponent_le_of_closed_finiteIndex)
open Polynomial MulAction

private theorem minpoly_of_fixed
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] (F : Subalgebra K L)
    (hF : ∀ z : L, z ∈ F ↔ ∀ h ∈ H, h • z = z)
    (hbase : ∀ z : L, (∀ g : G, g • z = z) → z ∈ Set.range (algebraMap K L))
    (x : F) :
    IsIntegral K (x : L) ∧ (minpoly K (x : L)).natDegree ≤ H.index ∧
      ((minpoly K (x : L)).map (algebraMap K F)).Splits := by
  classical
  let S := stabilizer G (x : L)
  have hHS : H ≤ S := fun h hh => (hF x).mp x.property h hh
  let : S.FiniteIndex := Subgroup.finiteIndex_of_le hHS
  let : Fintype (G ⧸ S) := Fintype.ofFinite _
  let r (q : G ⧸ S) : L := ofQuotientStabilizer G (x : L) q
  have hr (q : G ⧸ S) : r q ∈ F := by
    induction q using QuotientGroup.induction_on with
    | _ g =>
      change g • (x : L) ∈ F
      refine (hF _).mpr fun h hh => ?_
      have hc : g⁻¹ * h * g ∈ H := by
        simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem h hh g⁻¹
      calc
        h • (g • (x : L)) = g • ((g⁻¹ * h * g) • (x : L)) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
        _ = g • (x : L) := by rw [(hF x).mp x.property _ hc]
  let p : L[X] := ∏ q : G ⧸ S, (X - C (r q))
  have hp : p.Monic := monic_prod_X_sub_C r Finset.univ
  have hinvariant (g : G) : g • p = p := by
    unfold p
    simp only [Finset.smul_prod', smul_sub, smul_X, smul_C]
    refine Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun q => ?_
    unfold r
    rw [ofQuotientStabilizer_smul]
  obtain ⟨pK, hpK⟩ := (mem_lifts (f := algebraMap K L) p).mp
    ((lifts_iff_coeff_lifts (f := algebraMap K L) p).mpr fun j =>
      hbase _ fun g => by rw [← coeff_smul, hinvariant])
  have hmonic : pK.Monic := monic_map_iff.mp (hpK.symm ▸ hp)
  have hroot : aeval (x : L) pK = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hpK, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk (1 : G))) ?_
    change (X - C ((1 : G) • (x : L))).eval (x : L) = 0
    simp
  have hx : IsIntegral K (x : L) := ⟨pK, hmonic, hroot⟩
  have hdegree : pK.natDegree = S.index := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K L), hpK]
    change (∏ q : G ⧸ S, (X - C (r q))).natDegree = Nat.card (G ⧸ S)
    rw [natDegree_prod_of_monic _ _ (fun q _ => monic_X_sub_C (r q)), Nat.card_eq_fintype_card]
    simp
  let rF (q : G ⧸ S) : F := ⟨r q, hr q⟩
  have hpF : pK.map (algebraMap K F) = ∏ q : G ⧸ S, (X - C (rF q)) := by
    apply map_injective (f := (F.val : F →+* L)) Subtype.val_injective
    rw [map_map, F.val.comp_algebraMap, hpK, Polynomial.map_prod]
    simp [p, rF]
  have hdvd := minpoly.dvd K (x : L) hroot
  refine ⟨hx, ?_, ?_⟩
  · exact ((minpoly.monic hx).natDegree_le_of_dvd hmonic.ne_zero hdvd).trans
      (hdegree.trans_le (Subgroup.index_antitone hHS))
  · have hsplit : (pK.map (algebraMap K F)).Splits := by
      rw [hpF]
      exact Splits.prod fun q _ => Splits.X_sub_C (rF q)
    exact hsplit.of_dvd (hmonic.map _).ne_zero (Polynomial.map_dvd _ hdvd)

/-- The identity-component fixed subalgebra is the algebraic part of the
differential Picard–Vessiot extension, with split minimal polynomials of
degree at most the component index. -/
theorem algebraicElementsAndOrbits.{u, v} : Specs.algebraicElementsAndOrbits.{u, v} := by
  classical
  intro K R _ _ _ n δ A E T Y hbase hpv hY
  let Q := Specs.totalQuotientRing R
  let G := Specs.matrixGaloisGroup δ E Y
  let H := identityComponent G
  let fixed (J : Subgroup G) : Subalgebra K Q :=
    Specs.matrixFixedSubalgebra δ E Y (J : Set G)
  obtain ⟨hfixed, ⟨corr, _, hstabilizer⟩, hfield, hbot⟩ :=
    operatorGaloisCorrespondence δ A E T Y hbase hpv hY
  have hQ : IsField Q := (hfield rfl).1
  refine ⟨hQ, ?_⟩
  let : Field Q := hQ.toField
  obtain ⟨act, hact⟩ : ∃ act : G →* RingAut Q,
      ∀ g, act g = Specs.matrixFractionAutomorphism δ E Y g := by
    let : Algebra K (Specs.totalQuotientRing R) := Algebra.compHom _ (algebraMap K R)
    obtain ⟨e, he, _⟩ := galoisTotalRingAction δ A E Y T hbase hpv.1 hY hpv.2.1
    exact ⟨{ toFun := fun g => (e g).val.toRingEquiv
             map_one' := congrArg (fun a => a.val.toRingEquiv) (map_one e)
             map_mul' := fun g h => congrArg (fun a => a.val.toRingEquiv) (map_mul e g h) }, he⟩
  let : MulSemiringAction G Q := MulSemiringAction.compHom Q act
  have hsmul (g : G) (x : Q) : g • x = Specs.matrixFractionAutomorphism δ E Y g x :=
    DFunLike.congr_fun (hact g) x
  have hmem (J : Subgroup G) (x : Q) : x ∈ fixed J ↔ ∀ g ∈ J, g • x = x := by
    change (∀ g ∈ (J : Set G), Specs.matrixFractionAutomorphism δ E Y g x = x) ↔ _
    simp only [hsmul, SetLike.mem_coe]
  have hbaseRange (x : Q) (hx : ∀ g : G, g • x = x) : x ∈ Set.range (algebraMap K Q) := by
    change x ∈ (⊥ : Subalgebra K Q)
    rw [← hbot]
    exact fun g _ => (hsmul g x).symm.trans (hx g)
  have hpolynomial (x : fixed H) :=
    minpoly_of_fixed H (fixed H) (hmem H) hbaseRange x
  refine ⟨le_antisymm ?_ ?_, fun x => (hpolynomial x).2⟩
  · intro x hx
    exact (mem_algebraicClosure_iff').mpr (hpolynomial ⟨x, hx⟩).1
  · intro x hx
    have hxInt : IsIntegral K x := (mem_algebraicClosure_iff').mp hx
    let baseAut (g : G) : Q ≃ₐ[K] Q :=
      AlgEquiv.ofRingEquiv (f := act g) fun k => by
        rw [hact]
        exact (Specs.matrixFixedSubalgebra δ E Y Set.univ).algebraMap_mem k g (Set.mem_univ g)
    have horbit : (orbit G x).Finite := ((minpoly K x).rootSet_finite Q).subset (by
      rintro y ⟨g, rfl⟩
      exact ((minpoly.monic hxInt).mem_rootSet).mpr
        (minpoly.aeval_algHom K (baseAut g).toAlgHom x))
    let S := stabilizer G x
    let : S.FiniteIndex := ⟨by
      change (stabilizer G x).index ≠ 0
      rw [index_stabilizer]
      exact Set.ncard_ne_zero_of_mem (mem_orbit_self x) horbit⟩
    -- Since `x` belongs to `Q^S`, its stabilizer is the pointwise stabilizer of `Q^S`.
    let B := fixed S
    have hxB : x ∈ B := (hmem S x).mpr fun g hg => hg
    let J := corr.symm (OrderDual.toDual ⟨B, hfixed S⟩)
    have hJ : (J.val : Set G) = (S : Set G) := by
      rw [hstabilizer]
      ext g
      constructor
      · intro hg
        exact (hsmul g x).trans (hg ⟨x, hxB⟩)
      · intro hg y
        exact (hsmul g y).symm.trans ((hmem S y).mp y.property g hg)
    have hclosed : IsClosed (S : Set G) := hJ ▸ J.property
    exact (hmem H x).mpr fun g hg =>
      identityComponent_le_of_closed_finiteIndex S hclosed hg

end GaloisFormalization.PV
