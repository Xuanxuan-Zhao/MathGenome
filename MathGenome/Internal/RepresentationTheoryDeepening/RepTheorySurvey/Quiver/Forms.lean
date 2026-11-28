import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.AcyclicFiniteness
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring

/-! The matrix of the polarization of the Tits form. -/

open CategoryTheory
open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.Forms

abbrev DimensionVector := FormsSpec.DimensionVector
noncomputable abbrev unitVector := @FormsSpec.unitVector
noncomputable abbrev projectiveAt.{u, v, w} := @FormsSpec.projectiveAt.{u, v, w}
abbrev FiniteRepresentation.{u, v, w, d} := FormsSpec.FiniteRepresentation.{u, v, w, d}
noncomputable abbrev dimensionVector.{u, v, w, d} := @FormsSpec.dimensionVector.{u, v, w, d}
noncomputable abbrev vertexSimple.{u, v, w, d} := @FormsSpec.vertexSimple.{u, v, w, d}
abbrev IndecomposableRepresentation.{u, v, w, d} := FormsSpec.IndecomposableRepresentation.{u, v, w, d}
abbrev RepresentationClass.{u, v, w, d} := FormsSpec.RepresentationClass.{u, v, w, d}
abbrev IndecomposableClass.{u, v, w, d} := FormsSpec.IndecomposableClass.{u, v, w, d}
abbrev FiniteRepresentationType.{u, v, w, d} := FormsSpec.FiniteRepresentationType.{u, v, w, d}
abbrev eulerForm := @FormsSpec.eulerForm
abbrev titsForm := @FormsSpec.titsForm
noncomputable abbrev edgeMultiplicity := @FormsSpec.edgeMultiplicity
noncomputable abbrev polarizationMatrix := @FormsSpec.polarizationMatrix
abbrev PositiveDefinite := FormsSpec.PositiveDefinite

universe u v w d r

theorem mem_projectiveAt : FormsSpec.ProjectiveAtMembership.{u, v, w} := by
  intro k Q _ _ _ i x
  exact Submodule.mem_span_singleton

section VertexSimple

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q]

@[simp]
theorem vertexSimple_vertex_self (i : Q) :
    RM03.QuiverRepresentation.vertex (vertexSimple.{u, v, w, d} k i) i =
      ModuleCat.of k (ULift.{d} k) := by
  simp [FormsSpec.vertexSimple]

theorem vertexSimple_vertex_of_ne {i j : Q} (h : j ≠ i) :
    RM03.QuiverRepresentation.vertex (vertexSimple.{u, v, w, d} k i) j =
      ModuleCat.of k PUnit.{max w d + 1} := by
  simp [FormsSpec.vertexSimple, h]

@[simp]
theorem vertexSimple_arrow (i : Q) {j l : Q} (a : j ⟶ l) :
    RM03.QuiverRepresentation.arrow (vertexSimple.{u, v, w, d} k i) a = 0 :=
  RM03.QuiverRepresentation.arrow_ofArrows _ _ a

end VertexSimple

theorem finite_vertexSimple : FormsSpec.FiniteAtVertexSimple.{u, v, w, d} := by
  intro k Q _ _ i j
  change (fun M : ModuleCat.{max w d} k => Module.Finite k M)
    (RM03.QuiverRepresentation.vertex (vertexSimple k i) j)
  by_cases h : j = i
  · subst j
    rw [vertexSimple_vertex_self]
    infer_instance
  · rw [vertexSimple_vertex_of_ne k h]
    infer_instance

theorem dimensionVector_vertexSimple : FormsSpec.VertexSimpleDimension.{u, v, w, d} := by
  classical
  intro k Q _ _ i h
  funext j
  change (fun M : ModuleCat.{max w d} k => (Module.finrank k M : ℤ))
    (RM03.QuiverRepresentation.vertex (vertexSimple k i) j) = unitVector i j
  by_cases hij : j = i
  · subst j
    rw [vertexSimple_vertex_self]
    simp [FormsSpec.unitVector]
  · rw [vertexSimple_vertex_of_ne k hij]
    simp [FormsSpec.unitVector, hij, Module.finrank_zero_of_subsingleton]

theorem vertexSimple_isSimple : FormsSpec.VertexSimpleIsSimple.{u, v, w, d} := by
  intro k Q _ _ i
  constructor
  intro Y f _
  have hi : Simple ((vertexSimple.{u, v, w, d} k i).obj (i : Paths Q)) := by
    apply simple_of_finrank_eq_one (k := k)
    change (fun M : ModuleCat.{max w d} k => Module.finrank k M)
      (RM03.QuiverRepresentation.vertex (vertexSimple k i) i) = 1
    rw [vertexSimple_vertex_self]
    simp
  have hj (j : Q) (h : j ≠ i) :
      Limits.IsZero ((vertexSimple.{u, v, w, d} k i).obj (j : Paths Q)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change (fun M : ModuleCat.{max w d} k => Subsingleton M)
      (RM03.QuiverRepresentation.vertex (vertexSimple k i) j)
    rw [vertexSimple_vertex_of_ne k h]
    infer_instance
  have componentMono (j : Paths Q) : Mono (f.app j) :=
    (NatTrans.mono_iff_mono_app f).mp inferInstance j
  have : Mono (f.app (i : Paths Q)) := componentMono i
  constructor
  · intro hf hfzero
    have : IsIso (f.app (i : Paths Q)) := (NatTrans.isIso_iff_isIso_app f).mp hf i
    exact (Simple.mono_isIso_iff_nonzero (f.app (i : Paths Q))).mp this
      (by rw [hfzero]; rfl)
  · intro hf
    apply (NatTrans.isIso_iff_isIso_app f).mpr
    intro j
    by_cases h : j = (i : Paths Q)
    · subst j
      apply isIso_of_mono_of_nonzero
      intro hz
      apply hf
      apply NatTrans.ext
      funext j
      by_cases h : j = (i : Paths Q)
      · subst j
        exact hz
      · exact (hj j h).eq_of_tgt _ _
    · have hz := hj j h
      have hs := ModuleCat.isZero_iff_subsingleton.mp hz
      have hf_inj := (ModuleCat.mono_iff_injective (f.app j)).mp (componentMono j)
      exact (ModuleCat.isZero_iff_subsingleton.mpr
        ⟨fun x y => hf_inj (hs.elim _ _)⟩).isIso hz (f.app j)

theorem finite_of_retract : FormsSpec.FiniteRetract.{u, v, w, d} := by
  intro k Q _ _ V W f g h hV i
  have : FiniteDimensional k (RM03.QuiverRepresentation.vertex V i) := hV i
  apply FiniteDimensional.of_injective (RM03.QuiverRepresentation.component f i)
  apply Function.LeftInverse.injective (g := RM03.QuiverRepresentation.component g i)
  intro x
  have hi := congrArg (fun f => RM03.QuiverRepresentation.component f i) h
  exact LinearMap.congr_fun hi x

theorem dimensionVector_iso : FormsSpec.DimensionVectorIso.{u, v, w, d} := by
  intro k Q _ _ V W iso
  funext i
  exact congrArg (fun n : ℕ => (n : ℤ)) (iso.app (i : Paths Q)).toLinearEquiv.finrank_eq

theorem noLoop : FormsSpec.NoLoop.{u, v} := by
  intro Q _ h i
  exact ⟨fun a => h (RM03.hasOrientedCycle_iff_exists_closed_path.mpr
    ⟨i, a.toPath, by simp⟩)⟩

section Forms

variable {Q : Type u} [Quiver.{v} Q]
variable {R : Type r} [CommRing R]

theorem edgeMultiplicity_comm (i j : Q) : edgeMultiplicity i j = edgeMultiplicity j i :=
  Nat.add_comm _ _

@[simp]
theorem edgeMultiplicity_self (h : ¬ RM03.HasOrientedCycle Q) (i : Q) :
    edgeMultiplicity i i = 0 := by
  have := noLoop h i
  simp [FormsSpec.edgeMultiplicity]

@[simp]
theorem polarizationMatrix_apply_self (R : Type r) [CommRing R] (i : Q) :
    polarizationMatrix R i i = 2 := by
  simp [FormsSpec.polarizationMatrix]

theorem polarizationMatrix_apply_of_ne {i j : Q} (h : i ≠ j) :
    polarizationMatrix R i j = -(edgeMultiplicity i j : R) := by
  simp [FormsSpec.polarizationMatrix, h]

theorem polarizationMatrix_transpose : FormsSpec.SymmetricPolarizationMatrix.{u, v, r} := by
  intro Q _ R _
  ext i j
  change polarizationMatrix R j i = polarizationMatrix R i j
  by_cases h : i = j
  · subst j
    rfl
  · rw [polarizationMatrix_apply_of_ne h, polarizationMatrix_apply_of_ne (Ne.symm h),
      edgeMultiplicity_comm i j]

variable [Fintype Q] [Fintype (RM03.Arrow Q)]

/-- Regroup the arrow sum by the ordered pair of endpoints. -/
private theorem sum_arrows_by_endpoints (f : Q → Q → R) :
    (∑ a : RM03.Arrow Q, f a.1 a.2.1) =
      ∑ i : Q, ∑ j : Q, (Nat.card (i ⟶ j) : R) * f i j := by
  classical
  have arrowsFinite (i j : Q) : Finite (i ⟶ j) :=
    Finite.of_injective (fun a : i ⟶ j => (⟨i, j, a⟩ : RM03.Arrow Q))
      (by
        intro a b h
        have h' := @sigma_mk_injective Q (fun i => Σ j : Q, i ⟶ j) i _ _ h
        exact @sigma_mk_injective Q (fun j => i ⟶ j) j a b h')
  let (i j : Q) : Fintype (i ⟶ j) := @Fintype.ofFinite _ (arrowsFinite i j)
  calc
    _ = @Finset.sum _ _ _ (@Finset.univ _ Sigma.instFintype) (fun a : RM03.Arrow Q => f a.1 a.2.1) :=
      congrArg (fun inst : Fintype (RM03.Arrow Q) =>
        ∑ a ∈ @Finset.univ _ inst, f a.1 a.2.1) (Subsingleton.elim _ _)
    _ = ∑ i : Q, ∑ a : (Σ j : Q, i ⟶ j), f i a.1 :=
      Fintype.sum_sigma (fun a : RM03.Arrow Q => f a.1 a.2.1)
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_sigma' (fun j (_ : i ⟶ j) => f i j)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem eulerForm_add_swap_eq_pairing (h : ¬ RM03.HasOrientedCycle Q) (x y : Q → R) :
    eulerForm x y + eulerForm y x = x ⬝ᵥ (polarizationMatrix R *ᵥ y) := by
  classical
  have hentry (i j : Q) :
      x i * (polarizationMatrix R i j * y j) =
        (if j = i then x i * y i + y i * x i else 0) -
          (Nat.card (i ⟶ j) : R) * (x i * y j) -
          (Nat.card (j ⟶ i) : R) * (y j * x i) := by
    by_cases hij : i = j
    · subst j
      have := noLoop h i
      simp only [polarizationMatrix_apply_self, ite_true, Nat.card_of_isEmpty,
        Nat.cast_zero, zero_mul, sub_zero]
      ring
    · rw [polarizationMatrix_apply_of_ne hij, ite_eq_right (Ne.symm hij)]
      dsimp [edgeMultiplicity, FormsSpec.edgeMultiplicity]
      push_cast
      ring
  calc
    eulerForm x y + eulerForm y x =
        (∑ i, (x i * y i + y i * x i)) -
          (∑ i, ∑ j, (Nat.card (i ⟶ j) : R) * (x i * y j)) -
          ∑ i, ∑ j, (Nat.card (i ⟶ j) : R) * (y i * x j) := by
      simp only [eulerForm, FormsSpec.eulerForm, Finset.sum_add_distrib]
      rw [sum_arrows_by_endpoints (fun i j => x i * y j),
        sum_arrows_by_endpoints (fun i j => y i * x j)]
      ring
    _ = x ⬝ᵥ (polarizationMatrix R *ᵥ y) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hentry, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [Finset.sum_comm (f := fun i j => (Nat.card (j ⟶ i) : R) * (y j * x i))]

theorem titsForm_polarization (h : ¬ RM03.HasOrientedCycle Q) (x y : Q → R) :
    titsForm (x + y) - titsForm x - titsForm y = x ⬝ᵥ (polarizationMatrix R *ᵥ y) := by
  rw [← eulerForm_add_swap_eq_pairing h]
  simp only [titsForm, FormsSpec.titsForm, eulerForm, FormsSpec.eulerForm, Pi.add_apply,
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem real_titsForm_intCast : FormsSpec.RealTitsFormOfInt.{u, v} := by
  intro Q _ _ _ x
  simp [FormsSpec.titsForm, FormsSpec.eulerForm, Int.cast_sub, Int.cast_mul, Int.cast_sum]

theorem integral_polarization : FormsSpec.IntegralPolarization.{u, v} :=
  fun h x y => titsForm_polarization h x y

theorem real_quadratic_matrix : FormsSpec.RealQuadraticMatrix.{u, v} := by
  intro Q _ _ _ h x
  rw [← eulerForm_add_swap_eq_pairing h, show FormsSpec.titsForm x = eulerForm x x from rfl, two_mul]

end Forms

end RepTheorySurvey.Quiver.Forms
