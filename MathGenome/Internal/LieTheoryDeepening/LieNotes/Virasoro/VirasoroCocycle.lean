import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.WittAlgebra
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroCocycle

/-! The Virasoro cocycle and canonical central extension of the Witt algebra. -/

noncomputable section

open LieModule.Cohomology

namespace LieNotes.Virasoro

local notation "W" => Witt.W
local notation "κ" => VirasoroSpec.centralCoefficient

/-- The bilinear form defining the `z`-valued Virasoro cocycle. -/
def omegaForm : VirasoroSpec.CocycleFormType := VirasoroSpec.cocycleForm

theorem omegaForm_modes {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (z : Z) (m n : ℤ) : omegaForm z (Witt.L m) (Witt.L n) = κ m n • z := by
  have h (i : ℤ) : (-WittSpec.evaluation) (Witt.L i) = VirasoroSpec.shiftedLaurentBasis i := by
    change -(Witt.L i (LaurentPolynomial.T 1)) = _
    rw [Witt.L_apply_t, neg_neg, VirasoroSpec.shiftedLaurentBasis, Module.Basis.reindex_apply,
      AddMonoidAlgebra.basis_apply]
    rfl
  simp only [omegaForm, VirasoroSpec.cocycleForm, LinearMap.comp_apply, LinearMap.compl₂_apply, h,
    Module.Basis.constr_basis]

private theorem coefficient_skew (m n : ℤ) : κ m n = -κ n m := by
  by_cases h : m + n = 0
  · have hn : n = -m := by omega
    subst n
    simp only [VirasoroSpec.centralCoefficient, add_neg_cancel, neg_add_cancel, ite_true,
      Int.cast_neg]
    ring
  · have hn : n + m ≠ 0 := by omega
    simp [VirasoroSpec.centralCoefficient, h, hn]

private theorem omegaForm_skew {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (z : Z) :
    omegaForm z = -(omegaForm z).flip := by
  apply LinearMap.ext_basis Witt.basis Witt.basis
  intro m n
  simp only [Witt.basis_apply, LinearMap.neg_apply, LinearMap.flip_apply, omegaForm_modes]
  rw [← neg_smul, coefficient_skew m n]

theorem omegaForm_alternating {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (z : Z) (x : W) : omegaForm z x x = 0 := by
  have h := congrArg (fun f : W →ₗ[ℂ] W →ₗ[ℂ] Z => f x x) (omegaForm_skew z)
  change omegaForm z x x = -omegaForm z x x at h
  have hz : (2 : ℂ) • omegaForm z x x = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem coefficient_cyclic (m n u : ℤ) :
    ((m : ℂ) - (n : ℂ)) * κ (m + n) u +
      ((n : ℂ) - (u : ℂ)) * κ (n + u) m +
      ((u : ℂ) - (m : ℂ)) * κ (u + m) n = 0 := by
  by_cases h : m + n + u = 0
  · have h' : n + u + m = 0 := by omega
    have h'' : u + m + n = 0 := by omega
    simp only [VirasoroSpec.centralCoefficient, h, h', h'', ite_true]
    have hu : u = -(m + n) := by omega
    rw [hu]
    push_cast
    ring
  · have h' : n + u + m ≠ 0 := by omega
    have h'' : u + m + n ≠ 0 := by omega
    simp [VirasoroSpec.centralCoefficient, h, h', h'']

/-- The alternating bilinear form before imposing the cocycle condition. -/
private def omegaCochain {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (z : Z) : twoCochain ℂ W Z :=
  ⟨omegaForm z, omegaForm_alternating z⟩

/-- The Virasoro cocycle for any complex vector space with trivial action. -/
def omega {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    [LieRingModule W Z] [LieModule ℂ W Z] [LieModule.IsTrivial W Z]
    (z : Z) : twoCocycle ℂ W Z := by
  refine ⟨omegaCochain z, (mem_twoCocycle_iff ℂ W Z _).mpr ?_⟩
  apply Witt.basis.ext
  intro m
  apply Witt.basis.ext
  intro n
  apply Witt.basis.ext
  intro u
  simp only [Witt.basis_apply, d₂₃_apply, trivial_lie_zero, sub_self, add_zero,
    zero_sub, LinearMap.zero_apply, ← twoCochain_val_apply, omegaCochain, Witt.lie_L,
    LinearMap.map_smul, LinearMap.smul_apply, omegaForm_modes, smul_smul]
  have he : κ (m + u) n = κ (u + m) n := by rw [add_comm m u]
  rw [he, ← neg_smul, ← add_smul, ← sub_smul]
  have hc := coefficient_cyclic m n u
  rw [show -(((m : ℂ) - (n : ℂ)) * κ (m + n) u) +
       ((m : ℂ) - (u : ℂ)) * κ (u + m) n -
       ((n : ℂ) - (u : ℂ)) * κ (n + u) m =
       -(((m : ℂ) - (n : ℂ)) * κ (m + n) u +
        ((n : ℂ) - (u : ℂ)) * κ (n + u) m +
        ((u : ℂ) - (m : ℂ)) * κ (u + m) n) by ring, hc, neg_zero, zero_smul]

@[simp]
theorem omega_modes {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    [LieRingModule W Z] [LieModule ℂ W Z] [LieModule.IsTrivial W Z]
    (z : Z) (m n : ℤ) : (omega z).val (Witt.L m) (Witt.L n) = κ m n • z :=
  omegaForm_modes z m n

theorem exists_omega : VirasoroSpec.BundledCocycleExists :=
  fun z => ⟨omega z, rfl⟩

private theorem omegaForm_leibniz {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (z : Z) (x y u : W) :
    omegaForm z x ⁅y, u⁆ = omegaForm z ⁅x, y⁆ u + omegaForm z y ⁅x, u⁆ := by
  let z₀ : TrivialLieModule ℂ W Z := z
  exact (mem_twoCocycle_iff_of_trivial ℂ W _ (omega z₀).val).mp (omega z₀).property x y u

/-- The cyclic cocycle identity with the bracket in the first argument. -/
theorem omegaForm_cyclic {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (z : Z) (x y u : W) :
    omegaForm z ⁅x, y⁆ u + omegaForm z ⁅y, u⁆ x + omegaForm z ⁅u, x⁆ y = 0 := by
  have skew (a b : W) : -omegaForm z a b = omegaForm z b a :=
    twoCochain_skew (omegaCochain z) a b
  rw [← skew x ⁅y, u⁆, ← lie_skew u x, map_neg]
  rw [omegaForm_leibniz z x y u]
  rw [LinearMap.neg_apply, skew ⁅x, u⁆ y]
  abel

theorem coboundary_apply_trivial : VirasoroSpec.CoboundaryOnTrivialCoefficients :=
  fun φ x y => d₁₂_apply_apply_ofTrivial ℂ W _ φ x y

/-- The Virasoro algebra, with one complex central coordinate. -/
abbrev Vir : Type := VirasoroSpec.Vir

namespace Vir

/-- The linear identification with the Witt algebra and its central line. -/
def coordinates : VirasoroSpec.CoordinatesType := VirasoroSpec.coordinates

/-- The lifted Witt mode with central coordinate zero. -/
def L (m : ℤ) : Vir := VirasoroSpec.mode m

/-- The distinguished central generator. -/
def C : Vir := VirasoroSpec.central

private theorem bracket_coordinates (x y : Vir) :
    coordinates (VirasoroSpec.bracket x y) =
      (⁅(coordinates x).1, (coordinates y).1⁆, omegaForm (1 : ℂ) (coordinates x).1 (coordinates y).1) :=
  VirasoroSpec.coordinates.apply_symm_apply _

instance : LieRing Vir where
  toAddCommGroup := inferInstanceAs (AddCommGroup VirasoroSpec.Vir)
  bracket := VirasoroSpec.bracket
  add_lie x y z := by
    apply coordinates.injective
    simp [bracket_coordinates, LieRing.add_lie]
  lie_add x y z := by
    apply coordinates.injective
    simp [bracket_coordinates, LieRing.lie_add]
  lie_self x := by
    apply coordinates.injective
    simp [bracket_coordinates, omegaForm_alternating]
  leibniz_lie x y z := by
    apply coordinates.injective
    simp only [bracket_coordinates, map_add, Prod.mk_add_mk]
    rw [LieRing.leibniz_lie, omegaForm_leibniz]

instance : LieAlgebra ℂ Vir where
  toModule := inferInstanceAs (Module ℂ VirasoroSpec.Vir)
  lie_smul a x y := by
    apply coordinates.injective
    change coordinates (VirasoroSpec.bracket x (a • y)) =
      a • coordinates (VirasoroSpec.bracket x y)
    simp [bracket_coordinates]
    exact LieAlgebra.lie_smul (R := ℂ) (L := W) a (coordinates x).1 (coordinates y).1

/-- The bracket on the direct sum of the two vector spaces. -/
theorem coordinates_lie (x y : Vir) :
    coordinates ⁅x, y⁆ =
      (⁅(coordinates x).1, (coordinates y).1⁆, omegaForm (1 : ℂ) (coordinates x).1 (coordinates y).1) :=
  bracket_coordinates x y

@[simp]
theorem coordinates_L (m : ℤ) : coordinates (L m) = (Witt.L m, 0) := rfl

@[simp]
theorem coordinates_C : coordinates C = (0, 1) := rfl

theorem lie_L (m n : ℤ) :
    ⁅L m, L n⁆ = ((m : ℂ) - (n : ℂ)) • L (m + n) + κ m n • C := by
  apply coordinates.injective
  simp [coordinates_lie, Witt.lie_L, omegaForm_modes]

@[simp]
theorem lie_C (x : Vir) : ⁅C, x⁆ = 0 := by
  apply coordinates.injective
  simp [coordinates_lie]
  exact zero_lie (L := W) (M := W) (coordinates x).1

/-- The quotient Lie map forgetting the central coordinate. -/
def proj : Vir →ₗ⁅ℂ⁆ W where
  toLinearMap := VirasoroSpec.ProjectionOnCoordinates
  map_lie' := by
    intro x y
    exact congrArg Prod.fst (coordinates_lie x y)

theorem proj_toLinearMap : proj.toLinearMap = VirasoroSpec.ProjectionOnCoordinates := rfl

@[simp]
theorem proj_apply (x : Vir) : proj x = (coordinates x).1 := rfl

@[simp]
theorem proj_L (m : ℤ) : proj (L m) = Witt.L m := rfl

@[simp]
theorem proj_C : proj C = 0 := rfl

theorem proj_surjective : Function.Surjective proj :=
  fun x => ⟨coordinates.symm (x, 0), by simp⟩

theorem proj_eq_zero_iff (x : Vir) : proj x = 0 ↔ ∃ a : ℂ, x = a • C := by
  constructor
  · intro h
    refine ⟨(coordinates x).2, coordinates.injective ?_⟩
    change (coordinates x).1 = 0 at h
    rw [map_smul, coordinates_C]
    exact Prod.ext (by simpa using h) (by simp)
  · rintro ⟨a, rfl⟩
    simp [proj_apply]

theorem C_ne_zero : C ≠ 0 := by
  intro h
  have hs := congrArg (fun x => (coordinates x).2) h
  simp at hs

theorem canonicalLieProjection : VirasoroSpec.CanonicalLieProjection :=
  ⟨inferInstance, inferInstance, proj, proj_apply, fun _ _ => rfl⟩

end Vir
end LieNotes.Virasoro
