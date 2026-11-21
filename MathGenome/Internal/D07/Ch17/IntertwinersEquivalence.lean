import MathGenome.Internal.D07.Ch17.Definition
import MathGenome.Internal.Specs.D07.Ch17.IntertwinersEquivalence

/-!
Intertwiners and representation equivalence for arbitrary groups and vector
spaces. Finite bases enter only when passing to matrices. The unit matrix in
simultaneous_conjugacy is one witness for the entire representation.
-/
namespace D07.Ch17.IntertwinersEquivalence

universe u v w x y t z

noncomputable section

theorem intertwiner_characterization :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinerCharacterization.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T
  constructor
  · intro h g
    exact LinearMap.ext (h.isIntertwining g)
  · intro h
    exact ⟨fun g v => LinearMap.congr_fun (h g) v⟩

theorem intertwiners_zero :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinersZero.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ
  exact ⟨by intros; simp⟩

theorem intertwiners_add :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinersAdd.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ S T hS hT
  exact ⟨by intro g v; simp [hS.isIntertwining, hT.isIntertwining]⟩

theorem intertwiners_smul :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinersSmul.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ T a hT
  exact ⟨by intro g v; simp [hT.isIntertwining]⟩

theorem intertwiner_identity :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinerIdentity.{u,v,w} := by
  intro K G V _ _ _ _ ρ
  exact ⟨fun _ _ => rfl⟩

theorem intertwiner_composition :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinerComposition.{u,v,w,x,y} := by
  intro K G V W U _ _ _ _ _ _ _ _ ρ σ τ S T hS hT
  exact ⟨by intro g v; simp [hT.isIntertwining, hS.isIntertwining]⟩

theorem intertwiner_inverse :
    Specs.D07.Ch17.IntertwinersEquivalence.IntertwinerInverse.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ e h
  constructor
  intro g v
  apply e.injective
  simpa using (h.isIntertwining g (e.symm v)).symm

theorem bijective_intertwiner_equivalence :
    Specs.D07.Ch17.IntertwinersEquivalence.BijectiveIntertwinerEquivalence.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearMap, ⟨e.toIntertwiningMap.isIntertwining⟩, e.toLinearEquiv.bijective⟩
  · rintro ⟨T, hT, hbij⟩
    let e := LinearEquiv.ofBijective T hbij
    exact ⟨Representation.Equiv.mk e
      ((intertwiner_characterization K G V W ρ σ T).mp hT)⟩

theorem equivalence_laws :
    Specs.D07.Ch17.IntertwinersEquivalence.EquivalenceLaws.{u,v,w,x,y} := by
  intro K G V W U _ _ _ _ _ _ _ _ ρ σ τ
  refine ⟨⟨Representation.Equiv.refl ρ⟩, ?_, ?_⟩
  · rintro ⟨e⟩
    exact ⟨e.symm⟩
  · rintro ⟨e⟩ ⟨f⟩
    exact ⟨e.trans f⟩

theorem equivalence_relation :
    Specs.D07.Ch17.IntertwinersEquivalence.EquivalenceRelation.{u,v,w} := by
  intro K G V _ _ _ _
  exact ⟨fun ρ => ⟨Representation.Equiv.refl ρ⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

theorem matrix_equality :
    Specs.D07.Ch17.IntertwinersEquivalence.MatrixEquality.{u,w,x,t,z} := by
  intro K V W _ _ _ _ _ ι κ _ _ _ _ b c S T
  exact (LinearMap.toMatrix b c).injective.eq_iff.symm

theorem matrix_intertwining :
    Specs.D07.Ch17.IntertwinersEquivalence.MatrixIntertwining.{u,v,w,x,t,z} := by
  intro K G V W _ _ _ _ _ _ ι κ _ _ _ _ b c ρ σ T
  rw [intertwiner_characterization K G V W ρ σ T]
  constructor
  · intro h g
    simpa only [LinearMap.toMatrix_comp b b c, LinearMap.toMatrix_comp b c c]
      using congrArg (LinearMap.toMatrix b c) (h g)
  · intro h g
    apply (LinearMap.toMatrix b c).injective
    simpa only [LinearMap.toMatrix_comp b b c, LinearMap.toMatrix_comp b c c] using h g

section Matrices

variable {K : Type u} {V : Type w} {W : Type x} {ι : Type t}
  [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
  [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (c : Module.Basis ι K W)

/-- The matrix of an isomorphism is a unit, whose inverse is the matrix of
its inverse map, even when the chosen bases are empty. -/
def linearEquivMatrixUnit (e : V ≃ₗ[K] W) : Matrix.GeneralLinearGroup ι K where
  val := LinearMap.toMatrix b c e.toLinearMap
  inv := LinearMap.toMatrix c b e.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix_comp c b c]
    simp [LinearMap.toMatrix_id]
  inv_val := by
    rw [← LinearMap.toMatrix_comp b c b]
    simp [LinearMap.toMatrix_id]

/-- Conversely, transport an invertible coordinate matrix to the original spaces. -/
def matrixUnitLinearEquiv (P : Matrix.GeneralLinearGroup ι K) : V ≃ₗ[K] W :=
  Matrix.toLinOfInv b c P.val_inv P.inv_val

@[simp] theorem toMatrix_matrixUnitLinearEquiv (P : Matrix.GeneralLinearGroup ι K) :
    LinearMap.toMatrix b c (matrixUnitLinearEquiv b c P).toLinearMap =
      (P : Matrix ι ι K) :=
  LinearMap.toMatrix_toLin b c P

end Matrices

theorem matrix_invertibility :
    Specs.D07.Ch17.IntertwinersEquivalence.MatrixInvertibility.{u,v,w,x,t} := by
  intro K G V W _ _ _ _ _ _ ι _ _ b c T
  constructor
  · intro h
    exact (linearEquivMatrixUnit b c (LinearEquiv.ofBijective T h)).isUnit
  · rintro ⟨P, hP⟩
    have he : (matrixUnitLinearEquiv b c P).toLinearMap = T := by
      apply (LinearMap.toMatrix b c).injective
      simpa using hP
    rw [← he]
    exact (matrixUnitLinearEquiv b c P).bijective

theorem matrix_conjugacy :
    Specs.D07.Ch17.IntertwinersEquivalence.MatrixConjugacy.{u,v,w,x,t} := by
  intro K G V W _ _ _ _ _ _ ι _ _ b c ρ σ e
  rw [matrix_intertwining K G V W ι ι b c ρ σ e.toLinearMap]
  let P := linearEquivMatrixUnit b c e
  change (∀ g, (P : Matrix ι ι K) * _ = _ * (P : Matrix ι ι K)) ↔
    ∀ g, _ = (P : Matrix ι ι K) * _ * (↑(P⁻¹) : Matrix ι ι K)
  constructor
  · intro h g
    rw [h g, mul_assoc, P.mul_inv, mul_one]
  · intro h g
    rw [h g, mul_assoc, mul_assoc, P.inv_mul, mul_one]

theorem simultaneous_conjugacy :
    Specs.D07.Ch17.IntertwinersEquivalence.SimultaneousConjugacy.{u,v,w,x,t} := by
  intro K G V W _ _ _ _ _ _ ι _ _ b c ρ σ
  constructor
  · rintro ⟨e⟩
    refine ⟨linearEquivMatrixUnit b c e.toLinearEquiv, ?_⟩
    exact (matrix_conjugacy K G V W ι b c ρ σ e.toLinearEquiv).mp
      ⟨e.toIntertwiningMap.isIntertwining⟩
  · rintro ⟨P, hP⟩
    let e := matrixUnitLinearEquiv b c P
    have hT : ρ.IsIntertwiningMap σ e.toLinearMap := by
      apply (matrix_intertwining K G V W ι ι b c ρ σ e.toLinearMap).mpr
      intro g
      rw [toMatrix_matrixUnitLinearEquiv, hP g]
      rw [mul_assoc, mul_assoc, P.inv_mul, mul_one]
    exact (bijective_intertwiner_equivalence K G V W ρ σ).mpr
      ⟨e.toLinearMap, hT, e.bijective⟩

theorem different_dimensions :
    Specs.D07.Ch17.IntertwinersEquivalence.DifferentDimensions.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ _ _ ρ σ hdim ⟨e⟩
  exact hdim e.toLinearEquiv.finrank_eq

end

end D07.Ch17.IntertwinersEquivalence
