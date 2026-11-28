import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.CartanMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.IntegralMultiplicity
import Batteries.Tactic.OpenPrivate

/-! Brauer reciprocity and the Cartan matrix. -/

namespace RepTheorySurvey.Modular

universe uG uO uK uI uV uM uN

open IsLocalRing (ResidueField)
open CompositionMultiplicity (GroundFinite multiplicity)
open scoped BigOperators

open private ordinaryRestriction ordinaryRestriction_add_of_exact
  characterFormula exists_brauer_basis
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
open private simpleBrauerCharacter from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerCharacterBasis

set_option backward.isDefEq.respectTransparency false

private theorem ordinaryRestriction_congr
    {G : Type uG} [Group G] {p : ℕ} {K : Type uK} [Field K]
    {M : Type uM} [AddCommGroup M] [Module (MonoidAlgebra K G) M] [GroundFinite K G M]
    {N : Type uN} [AddCommGroup N] [Module (MonoidAlgebra K G) N] [GroundFinite K G N]
    (e : M ≃ₗ[MonoidAlgebra K G] N) :
    ordinaryRestriction (G := G) (K := K) (p := p) M =
      ordinaryRestriction (G := G) (K := K) (p := p) N := by
  let R := MonoidAlgebra K G
  let E : RestrictScalars K R M ≃ₗ[K] RestrictScalars K R N :=
    { toAddEquiv := (RestrictScalars.addEquiv K R M).trans
        (e.toAddEquiv.trans (RestrictScalars.addEquiv K R N).symm)
      map_smul' := fun a x => e.map_smul (algebraMap K R a) x }
  funext c
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  have h : E.conj (moduleRepresentation K G M g.val) = moduleRepresentation K G N g.val := by
    ext x
    change e (moduleRepresentation K G M g.val (e.symm x)) =
      moduleRepresentation K G N g.val x
    simp only [← Representation.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply]
    let y := RestrictScalars.addEquiv K R N x
    change e (MonoidAlgebra.of K G g.val • e.symm y) = MonoidAlgebra.of K G g.val • y
    rw [e.map_smul, e.apply_symm_apply]
  change LinearMap.trace K _ (moduleRepresentation K G M g.val) =
    LinearMap.trace K _ (moduleRepresentation K G N g.val)
  rw [← h, LinearMap.trace_conj']

private noncomputable def restrictedCharacter
    {G : Type uG} [Group G] {K : Type uK} [Field K] (p : ℕ) :
    CompositionMultiplicity.AdditiveCharacter.{uV} K G (PRegularConjClasses G p → K) :=
  CompositionMultiplicity.AdditiveCharacter.ofExact
    (fun M _ _ _ => ordinaryRestriction (p := p) M)
    (fun f g hf hg hex => ordinaryRestriction_add_of_exact (p := p) f g hf hg hex)

private theorem decompositionMultiplicity_eq_coordinate
    {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)
    {r : ℕ} (S : Fin r → ModuleCat.{uO} (MonoidAlgebra (ResidueField O) G))
    (hS : IsSimpleRepresentativeFamily S) (b : Module.Basis (Fin r) K (PRegularConjClasses G p → K))
    (hb : ∀ i, b i = simpleBrauerCharacter system S hS i)
    (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra K G) M] [GroundFinite K G M]
    (i : Fin r) :
    b.repr (ordinaryRestriction (p := p) M) i = (decompositionMultiplicity system M (S i) : K) := by
  have h := characterFormula.{uG, uO, uK, uM, 0, 0} system S hS M
  simp_rw [← hb] at h
  rw [h, b.repr_sum_self]

/-- Projective covers, reciprocity, and the Cartan matrix for the chosen lifts. -/
theorem cartanMatrix_formula : MR09Spec.cartanMatrixFormula.{uG, uO, uK, uI, uV} := by
  classical
  intro G _ _ p O _ _ _ K _ _ system r d split hd ι _ V hV eBar e heBar he hred
    q hrank hother A S P PK D C
  have hrecip (χ : ι) (i : Fin r) : multiplicity K G (PK i) (V χ) = D χ i := by
    let := hV.simple χ
    have hr : (q (MR01Spec.reductionValue O G (e i)) i).rank = 1 := hred i ▸ hrank i
    have ho (j : Fin r) (hj : j ≠ i) : q (MR01Spec.reductionValue O G (e i)) j = 0 :=
      hred i ▸ hother i j hj
    exact brauer_reciprocity system split hd i (e i) (he i) hr ho (V χ)
  refine ⟨fun i => modular_projective_cover split hd i (eBar i) (heBar i) (hrank i) (hother i),
    hrecip, ?_⟩
  let k := ResidueField O
  let R := MonoidAlgebra K G
  let : CharZero K := system.charZero
  have hS : IsSimpleRepresentativeFamily S := modular_column_family hd split
  obtain ⟨b, hb⟩ := exists_brauer_basis system S hS
  ext i j
  change multiplicity k G (P j) (S i) = ∑ χ, D χ i * D χ j
  let : GroundFinite K G R := CompositionMultiplicity.groundFinite_groupAlgebra
  let : GroundFinite K G (PK j) :=
    CompositionMultiplicity.groundFinite_of_injective (PK j).subtype Subtype.val_injective
  -- Put the ordinary left ideal in the carrier universe of the simple representatives.
  let M := ULift.{max uO uV} (PK j)
  let E : PK j ≃ₗ[R] M := ULift.moduleEquiv.symm
  let : GroundFinite K G M :=
    CompositionMultiplicity.groundFinite_of_surjective E.toLinearMap E.surjective
  let (χ : ι) : IsSimpleModule R (V χ) := hV.simple χ
  let (χ : ι) : GroundFinite K G (V χ) := CompositionMultiplicity.groundFinite_of_simple
  let : IsSimpleModule A (S i) := hS.simple i
  obtain ⟨L, _, ⟨f⟩⟩ := exists_principalIdeal_stableLattice system (e j) (he j)
  let : GroundFinite k G (MR04LatticeSpec.nativeReduction L) :=
    MR04Spec.nativeReductionFinite (PK j) L
  have f' : MR04LatticeSpec.nativeReduction L ≃ₗ[A] P j :=
    f.trans (LinearEquiv.ofEq _ _
      (congrArg (fun a : A => (MR09CoversSpec.principalLeftIdealValue a : Submodule A A)) (hred j)))
  have hC : decompositionMultiplicity system (PK j) (S i) = multiplicity k G (P j) (S i) := by
    exact (decompositionMultiplicity_eq_lattice system (PK j) (S i) L).trans
      (CompositionMultiplicity.multiplicity_congr f' (LinearEquiv.refl A (S i)))
  have hV' : CompositionMultiplicity.SimpleRepresentatives (F := K) (G := G)
      (fun χ => (V χ : Type (max uO uK uG uV))) :=
    ⟨hV.simple, fun h => hV.eq_of_iso h, fun W _ _ hW => hV.exhaustive (ModuleCat.of R W) hW⟩
  have hchar := CompositionMultiplicity.character_eq_sum (restrictedCharacter (K := K) (G := G) p)
    M (fun χ => (V χ : Type (max uO uK uG uV))) hV'
  change ordinaryRestriction (p := p) M =
    ∑ χ, multiplicity K G M (V χ) • ordinaryRestriction (p := p) (V χ) at hchar
  have hmult (χ : ι) : multiplicity K G M (V χ) = D χ j :=
    (CompositionMultiplicity.multiplicity_congr E (LinearEquiv.refl R (V χ))).symm.trans (hrecip χ j)
  simp_rw [hmult] at hchar
  apply Nat.cast_injective (R := K)
  calc
    _ = b.repr (ordinaryRestriction (p := p) (PK j)) i :=
      (congrArg (fun n : ℕ => (n : K)) hC).symm.trans
        (decompositionMultiplicity_eq_coordinate system S hS b hb (PK j) i).symm
    _ = b.coord i (ordinaryRestriction (p := p) M) :=
      congrArg (b.coord i) (ordinaryRestriction_congr (p := p) E)
    _ = _ := by
      rw [hchar, map_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [map_nsmul, nsmul_eq_mul, Nat.cast_mul]
      change (D χ j : K) * b.repr (ordinaryRestriction (p := p) (V χ)) i = _
      rw [decompositionMultiplicity_eq_coordinate system S hS b hb (V χ) i]
      exact mul_comm _ _

end RepTheorySurvey.Modular
