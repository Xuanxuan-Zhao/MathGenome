import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.IntegralBlockLifting
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.BlockReduction

/-! Compatibility of the decomposition coefficients with integral block lifting. -/

namespace RepTheorySurvey.Modular

open IsLocalRing (ResidueField)
open CompositionMultiplicity (GroundFinite)

set_option backward.isDefEq.respectTransparency false

/-- Acting on a stable lattice by an integral group-algebra element agrees with
acting on the ambient ordinary module by its image. -/
theorem nativeLattice_algebra_apply : MR08Spec.latticeAlgebraAction := by
  intro O _ K _ _ G _ V _ _ L a
  let _ : Module O (RestrictScalars K (MonoidAlgebra K G) V) := Module.restrictScalars O K _
  let _ : IsScalarTower O K (RestrictScalars K (MonoidAlgebra K G) V) :=
    IsScalarTower.restrictScalars O K _
  intro x
  let e := RestrictScalars.addEquiv K (MonoidAlgebra K G) V
  change e ((integralLatticeAction O L).asAlgebraHom a x).val =
    groupAlgebraToFractionField O K G a • e x.val
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have hmap : groupAlgebraToFractionField O K G (MonoidAlgebra.of O G g) =
        MonoidAlgebra.of K G g := by
      simp [groupAlgebraToFractionField, MonoidAlgebra.of_apply]
    rw [hmap, Representation.asAlgebraHom_of]
    change e (Representation.ofModule (k := K) (G := G) V g x.val) = _
    simp only [Representation.ofModule, MonoidAlgebra.lift_symm_apply,
      RestrictScalars.lsmul_apply_apply, MonoidAlgebra.of_apply, e, AddEquiv.apply_symm_apply]
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, ha, hc]
  | smul r a ha =>
    have hmap : groupAlgebraToFractionField O K G (r • a) =
        algebraMap O K r • groupAlgebraToFractionField O K G a := by
      simp [Algebra.smul_def, groupAlgebraToFractionField, MonoidAlgebra.coe_algebraMap]
    rw [hmap, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Algebra.smul_def, mul_smul]
    change algebraMap K (MonoidAlgebra K G) (algebraMap O K r) •
      e ((integralLatticeAction O L).asAlgebraHom a x).val = _
    rw [ha]

/-- The reduction of every stable lattice belongs to the residual block if the
lift of that block acts as identity on the ambient ordinary module. -/
theorem block_belongsTo_reduction : MR08Spec.blockActsOnReduction := by
  intro O _ _ K _ _ G _ V _ _ b bResidue hred hV L
  let _ : Module O (RestrictScalars K (MonoidAlgebra K G) V) := Module.restrictScalars O K _
  let _ : IsScalarTower O K (RestrictScalars K (MonoidAlgebra K G) V) :=
    IsScalarTower.restrictScalars O K _
  let σ := integralLatticeAction O L
  change ∀ q : ResidueQuotient O L.carrier,
    (residueRepresentation σ).asAlgebraHom bResidue.element q = q
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (IsLocalRing.maximalIdeal O • (⊤ : Submodule O L.carrier)) q
  change (residueRepresentation σ).asAlgebraHom bResidue.element (reduce x) = reduce x
  rw [← hred, residueRepresentation_algebra_reduce σ b.element x]
  have hx : σ.asAlgebraHom b.element x = x :=
    Subtype.ext ((nativeLattice_algebra_apply L b.element x).trans (hV x.val))
  rw [hx]

/-- The decomposition coefficient of an ordinary simple is zero at every
modular simple outside the block corresponding to its integral block. -/
theorem decompositionMultiplicity_eq_zero_of_not_belongsTo :
    MR08Spec.decompositionMultiplicityZero := by
  intro G _ _ p O _ _ _ K _ _ system V _ _ _ S _ _ _ b bResidue hred hV hS
  let _ : GroundFinite K G V := CompositionMultiplicity.groundFinite_of_simple
  let _ : Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V) :=
    ‹GroundFinite K G V›
  obtain ⟨L⟩ := exists_nativeStableLattice system V
  let M := NativeStableLattice.reduction L
  have hM : bResidue.BelongsTo M := block_belongsTo_reduction b bResidue hred hV L
  refine (decompositionMultiplicity_eq_lattice system V S L).trans ?_
  change CompositionMultiplicity.multiplicity (ResidueField O) G M S = 0
  let _ : GroundFinite (ResidueField O) G M := NativeStableLattice.finite_reduction V L
  obtain ⟨s⟩ := CompositionMultiplicity.exists_completeSeries
    (F := ResidueField O) (G := G) M
  by_contra hne
  obtain ⟨j, ⟨e⟩⟩ :=
    (CompositionMultiplicity.multiplicity_pos_iff s).mp (Nat.pos_of_ne_zero hne)
  apply hS
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [← e.map_smul]
  apply congrArg e
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, show bResidue.element • x = x from Subtype.ext (hM x.val)]

end RepTheorySurvey.Modular
