import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.QuotSMulTop

namespace CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution

open ExteriorTensorProduct IsLocalRing
open scoped ExteriorTensorProduct TensorProduct

noncomputable section

variable (V : Type*) [CommRing V] [IsLocalRing V]

/-- Reduce every coefficient of a formal power series to the residue field. -/
abbrev reduce (σ : Type*) : MvPowerSeries σ V →+* MvPowerSeries σ (ResidueField V) :=
  MvPowerSeries.map (residue V)

scoped instance seriesReductionAlgebra (σ : Type*) :
    Algebra (MvPowerSeries σ V) (MvPowerSeries σ (ResidueField V)) :=
  (reduce V σ).toAlgebra

/-- Reduction of scalars in a module over a formal power series ring. -/
abbrev Fibre (σ : Type*) (M : Type*) [AddCommGroup M] [Module (MvPowerSeries σ V) M] :=
  MvPowerSeries σ (ResidueField V) ⊗[MvPowerSeries σ V] M

/-- The canonical map into the special fibre. -/
abbrev fibreMk (σ : Type*) {M : Type*} [AddCommGroup M] [Module (MvPowerSeries σ V) M]
    (m : M) : Fibre V σ M :=
  1 ⊗ₜ[MvPowerSeries σ V] m

namespace Spec

def ReductionRing : Prop :=
  ∀ (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (π : V), Irreducible π → ∀ (σ : Type*),
    Function.Surjective (reduce V σ) ∧
      RingHom.ker (reduce V σ) = Ideal.span {MvPowerSeries.C π}

def FibreQuotient : Prop :=
  ∀ (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (π : V), Irreducible π → ∀ (σ : Type*) (M : Type*)
    [AddCommGroup M] [Module (MvPowerSeries σ V) M],
    ∃ e : QuotSMulTop (MvPowerSeries.C π : MvPowerSeries σ V) M ≃ₗ[MvPowerSeries σ V] Fibre V σ M,
      ∀ m, e (Submodule.Quotient.mk m) = fibreMk V σ m

def ExteriorFibre : Prop :=
  ∀ (V : Type*) [CommRing V] [IsLocalRing V] (a b : ℕ)
    (M N : Type*) [AddCommGroup M] [Module (X V a) M]
    [AddCommGroup N] [Module (Y V b) N],
    let k := ResidueField V
    let T := ExteriorTensorProduct.Spec.productValue V a b M N
    ∃ e : Fibre V (Fin a ⊕ YIndex b) T ≃ₗ[S k a b]
      ExteriorTensorProduct.Spec.productValue k a b (Fibre V (Fin a) M) (Fibre V (YIndex b) N),
      ∀ (s : S V a b) (m : M) (n : N),
        e (fibreMk V (Fin a ⊕ YIndex b) ((s ⊗ₜ[X V a] m) ⊗ₜ[Y V b] n)) =
          ((reduce V _ s) ⊗ₜ[X k a] fibreMk V (Fin a) m) ⊗ₜ[Y k b] fibreMk V (YIndex b) n

def SpecialFibre : Prop :=
  ∀ (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (π : V), Irreducible π → ∀ (a b : ℕ) (M N : Type*)
    [AddCommGroup M] [Module (X V a) M] [AddCommGroup N] [Module (Y V b) N],
    let σ := Fin a ⊕ YIndex b
    let T := ExteriorTensorProduct.Spec.productValue V a b M N
    let Tk := ExteriorTensorProduct.Spec.productValue (ResidueField V) a b
      (Fibre V (Fin a) M) (Fibre V (YIndex b) N)
    letI : Module (S V a b) Tk := Module.compHom Tk (reduce V σ)
    ∃ e : QuotSMulTop (MvPowerSeries.C π : S V a b) T ≃ₗ[S V a b] Tk,
      ∀ (s : S V a b) (m : M) (n : N),
        e (Submodule.Quotient.mk ((s ⊗ₜ[X V a] m) ⊗ₜ[Y V b] n)) =
          ((reduce V σ s) ⊗ₜ[X (ResidueField V) a] fibreMk V (Fin a) m)
            ⊗ₜ[Y (ResidueField V) b] fibreMk V (YIndex b) n

def UniformizerInjective : Prop :=
  ∀ (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (π : V), Irreducible π → ∀ (a : ℕ) (M N : Type*)
    [AddCommGroup M] [Module (X V a) M] [Module.Finite (X V a) M] [Nontrivial M]
    [AddCommGroup N] [Module (Y V a) N] [Module.Finite (Y V a) N] [Nontrivial N],
    Function.Injective (fun m : M => (MvPowerSeries.C π : X V a) • m) →
    Function.Injective (fun n : N => (MvPowerSeries.C π : Y V a) • n) →
    Function.Injective (fun t : ExteriorTensorProduct.Spec.productValue V a a M N =>
      (MvPowerSeries.C π : S V a a) • t)

def DiagonalUniformizerInjective : Prop :=
  ∀ (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (π : V), Irreducible π → ∀ (a : ℕ) (M N : Type*)
    [AddCommGroup M] [Module (X V a) M] [Module.Finite (X V a) M] [Nontrivial M]
    [AddCommGroup N] [Module (X V a) N] [Module.Finite (X V a) N] [Nontrivial N],
    Function.Injective (fun m : M => (MvPowerSeries.C π : X V a) • m) →
    Function.Injective (fun n : N => (MvPowerSeries.C π : X V a) • n) →
    Function.Injective (fun t : ExteriorTensorProduct.Spec.diagonalValue V a M N =>
      (MvPowerSeries.C π : S V a a) • t)

end Spec

section Complexes

open CategoryTheory CategoryTheory.Limits

universe u v w

local notation "down" => ComplexShape.down ℤ

variable (D : Type u) [CommRing D] (a b : ℕ)

abbrev exteriorModule (M : ModuleCat.{v} (X D a)) (N : ModuleCat.{w} (Y D b)) :
    ModuleCat.{max u v w} (S D a b) :=
  ModuleCat.of _ (ExteriorTensorProduct.Spec.productValue D a b M N)

abbrev exteriorHom {M M' : ModuleCat.{v} (X D a)} {N N' : ModuleCat.{w} (Y D b)}
    (f : M ⟶ M') (g : N ⟶ N') : exteriorModule D a b M N ⟶ exteriorModule D a b M' N' :=
  ModuleCat.ofHom (ExteriorTensorProduct.Spec.mapValue f.hom g.hom)

theorem exteriorHom_comp
    {M M' M'' : ModuleCat.{v} (X D a)} {N N' N'' : ModuleCat.{w} (Y D b)}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    exteriorHom D a b (f ≫ f') (g ≫ g') = exteriorHom D a b f g ≫ exteriorHom D a b f' g' := by
  apply ModuleCat.hom_ext
  simp only [exteriorHom, ModuleCat.hom_ofHom, ModuleCat.hom_comp,
    ExteriorTensorProduct.Spec.mapValue, LinearMap.baseChange_comp,
    TensorProduct.AlgebraTensorModule.map_comp]

@[simp]
theorem exteriorHom_id (M : ModuleCat.{v} (X D a)) (N : ModuleCat.{w} (Y D b)) :
    exteriorHom D a b (𝟙 M) (𝟙 N) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  simp [ExteriorTensorProduct.Spec.mapValue]

@[simp]
theorem exteriorHom_zero_left
    {M M' : ModuleCat.{v} (X D a)} {N N' : ModuleCat.{w} (Y D b)} (g : N ⟶ N') :
    exteriorHom D a b (0 : M ⟶ M') g = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  simp [ExteriorTensorProduct.Spec.mapValue]

@[simp]
theorem exteriorHom_zero_right
    {M M' : ModuleCat.{v} (X D a)} {N N' : ModuleCat.{w} (Y D b)} (f : M ⟶ M') :
    exteriorHom D a b f (0 : N ⟶ N') = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  simp [ExteriorTensorProduct.Spec.mapValue]

/-- The unsigned double complex with exterior tensor terms. The signed total uses
the first differential and the second differential multiplied by the alternating sign. -/
def exteriorBicomplex (P : ChainComplex (ModuleCat.{v} (X D a)) ℤ)
    (Q : ChainComplex (ModuleCat.{w} (Y D b)) ℤ) :
    HomologicalComplex₂ (ModuleCat.{max u v w} (S D a b)) down down :=
  HomologicalComplex₂.ofGradedObject down down
    (fun ij => exteriorModule D a b (P.X ij.1) (Q.X ij.2))
    (fun i i' j => exteriorHom D a b (P.d i i') (𝟙 (Q.X j)))
    (fun i j j' => exteriorHom D a b (𝟙 (P.X i)) (Q.d j j'))
    (fun i i' h j => by rw [P.shape i i' h]; simp)
    (fun i j j' h => by rw [Q.shape j j' h]; simp)
    (fun i i' i'' j => by rw [← exteriorHom_comp, P.d_comp_d]; simp)
    (fun i j j' j'' => by rw [← exteriorHom_comp, Q.d_comp_d]; simp)
    (fun i i' j j' => by simp only [← exteriorHom_comp, Category.comp_id, Category.id_comp])

/-- The signed homological total of the exterior tensor double complex. -/
abbrev exteriorTotal (P : ChainComplex (ModuleCat.{v} (X D a)) ℤ)
    (Q : ChainComplex (ModuleCat.{w} (Y D b)) ℤ) :
    ChainComplex (ModuleCat.{max u v w} (S D a b)) ℤ :=
  (exteriorBicomplex D a b P Q).total down

/-- A bounded nonnegative finite free resolution, with its degree-zero augmentation. -/
structure IsFiniteFreeResolution {R : Type u} [CommRing R]
    {M : ModuleCat.{v} R} (P : ChainComplex (ModuleCat.{v} R) ℤ) (e : P.X 0 ⟶ M) : Prop where
  free : ∀ i, Module.Free R (P.X i)
  finite : ∀ i, Module.Finite R (P.X i)
  nonnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i)
  bounded : ∃ b : ℕ, ∀ i : ℤ, (b : ℤ) < i → IsZero (P.X i)
  exact_pos : ∀ i : ℤ, 0 < i → Function.Exact (P.d (i + 1) i).hom (P.d i (i - 1)).hom
  exact_zero : Function.Exact (P.d 1 0).hom e.hom
  surjective : Function.Surjective e.hom

instance reduceScalars_preservesZero (V : Type u) [CommRing V] [IsLocalRing V] (σ : Type) :
    (ModuleCat.extendScalars.{u,u,v} (reduce V σ)).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_zero

/-- Reduction by the coefficient map on chain complexes. -/
abbrev reduceComplex (V : Type u) [CommRing V] [IsLocalRing V] (σ : Type)
    (P : ChainComplex (ModuleCat.{v} (MvPowerSeries σ V)) ℤ) :
    ChainComplex (ModuleCat.{max u v} (MvPowerSeries σ (ResidueField V))) ℤ :=
  ((ModuleCat.extendScalars.{u,u,v} (reduce V σ)).mapHomologicalComplex down).obj P

namespace Spec

def ExteriorResolution : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] (π : V), Irreducible π → ∀ (a : ℕ)
    (M : ModuleCat.{v} (X V a)) (N : ModuleCat.{w} (Y V a))
    [Module.Finite (X V a) M] [Module.Finite (Y V a) N] [Nontrivial M] [Nontrivial N],
    Function.Injective (fun m : M => (MvPowerSeries.C π : X V a) • m) →
    Function.Injective (fun n : N => (MvPowerSeries.C π : Y V a) • n) →
    ∀ (P : ChainComplex (ModuleCat.{v} (X V a)) ℤ)
      (Q : ChainComplex (ModuleCat.{w} (Y V a)) ℤ)
      (eP : P.X 0 ⟶ M) (eQ : Q.X 0 ⟶ N),
      IsFiniteFreeResolution P eP → IsFiniteFreeResolution Q eQ →
      ∃ e : (exteriorTotal V a a P Q).X 0 ⟶ exteriorModule V a a M N,
        IsFiniteFreeResolution (exteriorTotal V a a P Q) e ∧
        (exteriorBicomplex V a a P Q).ιTotal down 0 0 0 (by rfl) ≫ e = exteriorHom V a a eP eQ ∧
        Nonempty ((exteriorTotal V a a P Q).homology 0 ≅ exteriorModule V a a M N)

def ReducedExteriorComplex : Prop :=
  ∀ (V : Type u) [CommRing V] [IsLocalRing V] (a b : ℕ)
    (P : ChainComplex (ModuleCat.{v} (X V a)) ℤ)
    (Q : ChainComplex (ModuleCat.{w} (Y V b)) ℤ),
    Nonempty (reduceComplex V (Fin a ⊕ YIndex b) (exteriorTotal V a b P Q) ≅
      exteriorTotal (ResidueField V) a b
        (reduceComplex V (Fin a) P) (reduceComplex V (YIndex b) Q))

def ReducedResolution : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (π : V), Irreducible π → ∀ (σ : Type) (M : ModuleCat.{v} (MvPowerSeries σ V)),
    Function.Injective (fun m : M => (MvPowerSeries.C π : MvPowerSeries σ V) • m) →
    ∀ (P : ChainComplex (ModuleCat.{v} (MvPowerSeries σ V)) ℤ)
      (e : P.X 0 ⟶ M),
      IsFiniteFreeResolution P e →
      IsFiniteFreeResolution (reduceComplex V σ P) ((ModuleCat.extendScalars.{u,u,v} (reduce V σ)).map e)

end Spec

end Complexes

end

end CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution
