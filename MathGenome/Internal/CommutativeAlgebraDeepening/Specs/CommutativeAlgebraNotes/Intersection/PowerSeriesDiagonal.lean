import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Additive

noncomputable section

open CategoryTheory
open MvPowerSeries
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal

open ExteriorTensorProduct (Y S includeX includeY xToY)
open scoped ExteriorTensorProduct

universe u v w

variable (D : Type u) [CommRing D] (d : ℕ)

abbrev Index (d : ℕ) := Fin d ⊕ ExteriorTensorProduct.YIndex d

abbrev leftVar (i : Fin d) : S D d d := MvPowerSeries.X (Sum.inl i)
abbrev rightVar (i : Fin d) : S D d d := MvPowerSeries.X (Sum.inr (ULift.up i))

/-- The elements defining the diagonal, in the order of the left variables. -/
abbrev difference (i : Fin d) : S D d d := leftVar D d i - rightVar D d i

abbrev diagonalIdeal : Ideal (S D d d) := Ideal.span (Set.range (difference D d))

/-- Identify corresponding variables of the two copies. -/
noncomputable abbrev identify : S D d d →ₐ[D] ExteriorTensorProduct.X D d :=
  MvPowerSeries.rename (Sum.elim id ULift.down : Index d → Fin d)

abbrev translateFamily (add : Bool) : Index d → S D d d
  | .inl i => if add then leftVar D d i + rightVar D d i else difference D d i
  | .inr j => MvPowerSeries.X (Sum.inr j)

theorem translateFamily_constantCoeff (add : Bool) (i : Index d) :
    constantCoeff (translateFamily D d add i) = 0 := by
  cases i <;> cases add <;> simp [translateFamily, difference, leftVar, rightVar]

/-- Substitute z + y or x - y on the left variables, respectively. -/
noncomputable abbrev translate (add : Bool) : S D d d →ₐ[D] S D d d :=
  substAlgHom (hasSubst_of_constantCoeff_zero (translateFamily_constantCoeff D d add))

abbrev R := ExteriorTensorProduct.X D d

/-- The scalar action of the joint ring on the diagonal ring. -/
scoped instance diagonalAlgebra : Algebra (S D d d) (R D d) :=
  (identify D d).toRingHom.toAlgebra

/-- Restrict an ordinary module over the diagonal ring to the joint ring. -/
abbrev restrictDiagonal : ModuleCat (R D d) ⥤ ModuleCat (S D d d) :=
  ModuleCat.restrictScalars (identify D d).toRingHom

/-- The degreewise quotient by the diagonal ideal. -/
abbrev diagonalReduction (T : Type v) [AddCommGroup T] [Module (S D d d) T] :=
  T ⧸ (diagonalIdeal D d • ⊤ : Submodule (S D d d) T)

section Complexes

open ExteriorTensorProduct (toY)

variable {D d}

/-- The exterior product of two modules over the two copies of the diagonal ring. -/
abbrev exteriorPair (M N : ModuleCat.{u} (R D d)) : ModuleCat.{u} (S D d d) :=
  ModuleCat.of _ (ExteriorTensorProduct.Spec.diagonalValue D d M N)

abbrev exteriorPairMap {M M' N N' : ModuleCat.{u} (R D d)}
    (f : M ⟶ M') (g : N ⟶ N') : exteriorPair M N ⟶ exteriorPair M' N' :=
  ModuleCat.ofHom (ExteriorTensorProduct.Spec.mapValue f.hom
    (ExteriorTensorProduct.Spec.onYMapValue g.hom))

theorem exteriorPair_hom_ext {M N : ModuleCat.{u} (R D d)} {A : ModuleCat.{u} (S D d d)}
    {f g : exteriorPair M N ⟶ A}
    (h : ∀ (s : S D d d) (m : M) (n : N),
      f ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] toY n) =
        g ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] toY n)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x n =>
    induction x using TensorProduct.inductionOn with
    | tmul s m => exact h s m n
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

theorem exteriorPairMap_id (M N : ModuleCat.{u} (R D d)) :
    exteriorPairMap (𝟙 M) (𝟙 N) = 𝟙 (exteriorPair M N) :=
  exteriorPair_hom_ext fun _ _ _ => rfl

theorem exteriorPairMap_comp {M₀ M₁ M₂ N₀ N₁ N₂ : ModuleCat.{u} (R D d)}
    (f : M₀ ⟶ M₁) (f' : M₁ ⟶ M₂) (g : N₀ ⟶ N₁) (g' : N₁ ⟶ N₂) :
    exteriorPairMap (f ≫ f') (g ≫ g') = exteriorPairMap f g ≫ exteriorPairMap f' g' :=
  exteriorPair_hom_ext fun _ _ _ => rfl

theorem exteriorPairMap_zero_left {M M' N N' : ModuleCat.{u} (R D d)} (g : N ⟶ N') :
    exteriorPairMap (0 : M ⟶ M') g = 0 :=
  exteriorPair_hom_ext fun s _ n => by
    change (s ⊗ₜ[R D d] (0 : M')) ⊗ₜ[Y D d] toY (g n) = 0
    simp

theorem exteriorPairMap_zero_right {M M' N N' : ModuleCat.{u} (R D d)} (f : M ⟶ M') :
    exteriorPairMap f (0 : N ⟶ N') = 0 :=
  exteriorPair_hom_ext fun s m _ => by
    change (s ⊗ₜ[R D d] f m) ⊗ₜ[Y D d] (0 : ExteriorTensorProduct.OnY N') = 0
    simp

variable (D d)

/-- The ordinary exterior product, functorial in both arguments. -/
def exteriorBifunctor : ModuleCat.{u} (R D d) ⥤ ModuleCat.{u} (R D d) ⥤
    ModuleCat.{u} (S D d d) where
  obj M :=
    { obj := exteriorPair M
      map g := exteriorPairMap (𝟙 M) g
      map_id := exteriorPairMap_id M
      map_comp g g' := by rw [← exteriorPairMap_comp, Category.id_comp] }
  map f :=
    { app N := exteriorPairMap f (𝟙 N)
      naturality N N' g := by
        dsimp
        rw [← exteriorPairMap_comp, ← exteriorPairMap_comp] }
  map_id M := NatTrans.ext (funext (exteriorPairMap_id M))
  map_comp f f' := NatTrans.ext (funext fun N => by
    change exteriorPairMap (f ≫ f') (𝟙 N) =
      exteriorPairMap f (𝟙 N) ≫ exteriorPairMap f' (𝟙 N)
    rw [← exteriorPairMap_comp, Category.id_comp])

instance : (exteriorBifunctor D d).PreservesZeroMorphisms where
  map_zero _ _ := NatTrans.ext (funext fun _ => exteriorPairMap_zero_left _)

instance (M : ModuleCat.{u} (R D d)) :
    ((exteriorBifunctor D d).obj M).PreservesZeroMorphisms where
  map_zero _ _ := exteriorPairMap_zero_right _

/-- Extension along the diagonal quotient, represented using its identified ring R. -/
abbrev extendDiagonal : ModuleCat.{u} (S D d d) ⥤ ModuleCat.{u} (R D d) :=
  ModuleCat.extendScalars (identify D d).toRingHom

/-- A simple tensor in a module extended along the diagonal. -/
abbrev extendDiagonalTmul (U : ModuleCat.{u} (S D d d)) (r : R D d) (x : U) :
    (extendDiagonal D d).obj U :=
  show R D d ⊗[S D d d] U from r ⊗ₜ[S D d d] x

/-- The signed chain total is also defined for integer homological indices. -/
scoped instance downIntTensorSigns : (ComplexShape.down ℤ).TensorSigns where
  ε' := MonoidHom.mk' (fun i => i.toAdd.negOnePow) Int.negOnePow_add
  rel_add p q r h := by
    change q + 1 = p at h
    change q + r + 1 = p + r
    omega
  add_rel p q r h := by
    change q + 1 = p at h
    change r + q + 1 = r + p
    omega
  ε'_succ p q h := by
    change q + 1 = p at h
    change q.negOnePow = -p.negOnePow
    rw [← h, Int.negOnePow_succ, neg_neg]

variable {ι : Type} {c : ComplexShape ι}

abbrev exteriorBicomplex (P Q : HomologicalComplex (ModuleCat.{u} (R D d)) c) :=
  (((exteriorBifunctor D d).mapBifunctorHomologicalComplex c c).obj P).obj Q

abbrev ordinaryBicomplex (P Q : HomologicalComplex (ModuleCat.{u} (R D d)) c) :=
  (((MonoidalCategory.tensoringLeft (ModuleCat.{u} (R D d))).mapBifunctorHomologicalComplex c c).obj P).obj Q

end Complexes

namespace Spec

/-- The two explicit substitutions are mutually inverse on all power series. -/
def CoordinateChange : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ),
    Function.LeftInverse (translate D d false) (translate D d true) ∧
    Function.RightInverse (translate D d false) (translate D d true)

def IdentifyCopies : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ),
    (identify D d).comp (includeX D d d) = AlgHom.id D (ExteriorTensorProduct.X D d) ∧
    (identify D d).comp (includeY D d d) = (xToY D d).symm.toAlgHom

/-- The power-series map identifying the two copies is the quotient map by the diagonal. -/
def IdentifyKernel : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ),
    RingHom.ker (identify D d).toRingHom = diagonalIdeal D d

def DiagonalRegular : Prop :=
  ∀ (D : Type u) [CommRing D] [Nontrivial D] (d : ℕ),
    RingTheory.Sequence.IsRegular (S D d d) (List.ofFn (difference D d))

open scoped PowerSeriesDiagonal

def QuotientPresentation : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ),
    ∃ e : (S D d d ⧸ diagonalIdeal D d) ≃ₐ[D] R D d,
      ∀ s : S D d d, e (Ideal.Quotient.mk _ s) = identify D d s

/-- The module quotient by the diagonal ideal is extension to the diagonal ring. -/
def ReductionBaseChange : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ) (T : Type v)
    [AddCommGroup T] [Module (S D d d) T],
    ∃ e : diagonalReduction D d T ≃ₗ[S D d d] (R D d ⊗[S D d d] T),
      ∀ t : T, e (Submodule.Quotient.mk t) = 1 ⊗ₜ[S D d d] t

def TensorBaseChange : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (R D d) M] [AddCommGroup N] [Module (R D d) N],
    ∃ e : (R D d ⊗[S D d d] ExteriorTensorProduct.Spec.diagonalValue D d M N)
        ≃ₗ[R D d] (M ⊗[R D d] N),
      ∀ (r : R D d) (s : S D d d) (m : M) (n : N),
        e (r ⊗ₜ[S D d d] ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n)) =
          (r * identify D d s) • (m ⊗ₜ[R D d] n)

set_option backward.isDefEq.respectTransparency false in
def TensorQuotient : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (R D d) M] [AddCommGroup N] [Module (R D d) N],
    ∃ e : diagonalReduction D d (ExteriorTensorProduct.Spec.diagonalValue D d M N)
        ≃ₗ[S D d d] ↥((restrictDiagonal D d).obj (ModuleCat.of _ (M ⊗[R D d] N))),
      ∀ (s : S D d d) (m : M) (n : N),
        e (Submodule.Quotient.mk ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n)) =
          (identify D d s • (m ⊗ₜ[R D d] n) : M ⊗[R D d] N)

/-- The signed total of the exterior bicomplex after degreewise extension of scalars. -/
def TotalBaseChange : Prop :=
  ∀ (D : Type u) [CommRing D] (d : ℕ)
    {ι : Type} [AddMonoid ι] [DecidableEq ι] (c : ComplexShape ι) [c.TensorSigns]
    (P Q : HomologicalComplex (ModuleCat.{u} (R D d)) c),
    let K := exteriorBicomplex D d P Q
    let L := ordinaryBicomplex D d P Q
    let F := extendDiagonal D d
    ∃ e : (F.mapHomologicalComplex c).obj (K.total c) ≅ L.total c,
      ∀ (i j k : ι) (h : ComplexShape.π c c c (i, j) = k)
        (r : R D d) (s : S D d d) (m : P.X i) (n : Q.X j),
        (F.map (K.ιTotal c i j k h) ≫ e.hom.f k)
          (extendDiagonalTmul D d ((K.X i).X j) r
            ((s ⊗ₜ[R D d] m) ⊗ₜ[Y D d] ExteriorTensorProduct.toY n)) =
          L.ιTotal c i j k h (show (L.X i).X j from
            (r * identify D d s) • (m ⊗ₜ[R D d] n))

end Spec
end CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
