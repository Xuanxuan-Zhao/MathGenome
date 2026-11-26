import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Basic

/-!
The ordinary tensor construction in I07 and I11. The right variables use a type copy so
that the two algebra structures into the joint power-series ring can coexist, even for
the same number of variables.
-/

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct

universe u v w v' w'

abbrev YIndex (b : ℕ) := ULift.{0} (Fin b)

abbrev X (D : Type u) (a : ℕ) := MvPowerSeries (Fin a) D
abbrev Y (D : Type u) (b : ℕ) := MvPowerSeries (YIndex b) D
abbrev S (D : Type u) (a b : ℕ) := MvPowerSeries (Fin a ⊕ YIndex b) D

variable (D : Type u) [CommRing D] (a b : ℕ)

/-- Inclusion of the left variables. -/
noncomputable abbrev includeX : X D a →ₐ[D] S D a b :=
  MvPowerSeries.rename Sum.inl

/-- Inclusion of the right variables. -/
noncomputable abbrev includeY : Y D b →ₐ[D] S D a b :=
  MvPowerSeries.rename Sum.inr

noncomputable scoped instance xAlgebra : Algebra (X D a) (S D a b) :=
  (includeX D a b).toRingHom.toAlgebra

noncomputable scoped instance yAlgebra : Algebra (Y D b) (S D a b) :=
  (includeY D a b).toRingHom.toAlgebra

scoped instance xScalarTower : IsScalarTower D (X D a) (S D a b) :=
  IsScalarTower.of_algebraMap_eq fun r => ((includeX D a b).commutes r).symm

scoped instance yScalarTower : IsScalarTower D (Y D b) (S D a b) :=
  IsScalarTower.of_algebraMap_eq fun r => ((includeY D a b).commutes r).symm

/-- Rename the variables of the diagonal ring from the left to the right copy. -/
noncomputable abbrev xToY : X D a ≃ₐ[D] Y D a :=
  MvPowerSeries.renameEquiv D Equiv.ulift.symm

/-- Forget the type copy on the right variables of the joint ring. -/
noncomputable abbrev jointEquiv :
    S D a b ≃ₐ[D] MvPowerSeries (Fin a ⊕ Fin b) D :=
  MvPowerSeries.renameEquiv D (Equiv.sumCongr (Equiv.refl (Fin a)) Equiv.ulift)

/-- The underlying additive group of the second diagonal module. -/
def OnY (N : Type w) := N

instance [AddCommGroup N] : AddCommGroup (OnY N) :=
  inferInstanceAs (AddCommGroup N)

noncomputable instance [AddCommGroup N] [Module (X D a) N] : Module (Y D a) (OnY N) :=
  show Module (Y D a) N from Module.compHom N (xToY D a).symm.toRingHom

/-- The identity on the underlying group of a module written in the right variables. -/
def toY {N : Type w} (n : N) : OnY N := n

namespace Spec

def JointEquivIncludeX : Prop :=
  ∀ (D : Type u) [CommRing D] (a b : ℕ) (f : X D a),
    jointEquiv D a b (includeX D a b f) =
      MvPowerSeries.rename (R := D) (Sum.inl : Fin a → Fin a ⊕ Fin b) f

def JointEquivIncludeY : Prop :=
  ∀ (D : Type u) [CommRing D] (a b : ℕ) (f : X D b),
    jointEquiv D a b (includeY D a b (xToY D b f)) =
      MvPowerSeries.rename (R := D) (Sum.inr : Fin b → Fin a ⊕ Fin b) f

set_option linter.checkUnivs false in
abbrev ProductType :=
  ∀ (D : Type u) [CommRing D] (a b : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N],
    Type (max u v w)

noncomputable abbrev productValue : ProductType.{u, v, w} :=
  fun D _ a b M N _ _ _ _ => (S D a b ⊗[X D a] M) ⊗[Y D b] N

set_option linter.checkUnivs false in
abbrev DiagonalType :=
  ∀ (D : Type u) [CommRing D] (a : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (X D a) N],
    Type (max u v w)

noncomputable abbrev diagonalValue : DiagonalType.{u, v, w} :=
  fun D _ a M N _ _ _ _ => (S D a a ⊗[X D a] M) ⊗[Y D a] OnY N

def SmulTmul : Prop :=
  ∀ (D : Type u) [CommRing D] (a b : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    (r s : S D a b) (m : M) (n : N),
    r • ((s ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n : productValue D a b M N) =
      ((r * s) ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n

set_option linter.checkUnivs false in
abbrev MapType :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N'],
    (M →ₗ[X D a] M') → (N →ₗ[Y D b] N') →
      productValue D a b M N →ₗ[S D a b] productValue D a b M' N'

noncomputable abbrev mapValue : MapType.{u, v, w, v', w'} :=
  fun {D} _ {a b} {_ _} _ _ _ _ {_ _} _ _ _ _ f g =>
    TensorProduct.AlgebraTensorModule.map (f.baseChange (S D a b)) g

def MapTmul : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N']
    (f : M →ₗ[X D a] M') (g : N →ₗ[Y D b] N') (s : S D a b) (m : M) (n : N),
    mapValue f g ((s ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n) =
      (s ⊗ₜ[X D a] f m) ⊗ₜ[Y D b] g n

def MapId : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N],
    mapValue (LinearMap.id : M →ₗ[X D a] M) (LinearMap.id : N →ₗ[Y D b] N) = LinearMap.id

def MapComp : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N']
    {M'' : Type*} {N'' : Type*}
    [AddCommGroup M''] [Module (X D a) M''] [AddCommGroup N''] [Module (Y D b) N'']
    (f₁ : M →ₗ[X D a] M') (f₂ : M' →ₗ[X D a] M'')
    (g₁ : N →ₗ[Y D b] N') (g₂ : N' →ₗ[Y D b] N''),
    mapValue (f₂.comp f₁) (g₂.comp g₁) = (mapValue f₂ g₂).comp (mapValue f₁ g₁)

def MapAddLeft : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N']
    (f₁ f₂ : M →ₗ[X D a] M') (g : N →ₗ[Y D b] N'),
    mapValue (f₁ + f₂) g = mapValue f₁ g + mapValue f₂ g

def MapAddRight : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N']
    (f : M →ₗ[X D a] M') (g₁ g₂ : N →ₗ[Y D b] N'),
    mapValue f (g₁ + g₂) = mapValue f g₁ + mapValue f g₂

def SpanPairs : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    {ι κ : Type*} (m : ι → M) (n : κ → N),
    Submodule.span (X D a) (Set.range m) = ⊤ →
    Submodule.span (Y D b) (Set.range n) = ⊤ →
    Submodule.span (S D a b)
      (Set.range (fun p : ι × κ =>
        (((1 : S D a b) ⊗ₜ[X D a] m p.1) ⊗ₜ[Y D b] n p.2 :
          productValue D a b M N))) = ⊤

def FiniteProduct : Prop :=
  ∀ {D : Type u} [CommRing D] {a b : ℕ} {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (X D a) M] [AddCommGroup N] [Module (Y D b) N]
    [Module.Finite (X D a) M] [Module.Finite (Y D b) N],
    Module.Finite (S D a b) (productValue D a b M N)

def TransportSmul : Prop :=
  ∀ {D : Type u} [CommRing D] {a : ℕ} {N : Type w} [AddCommGroup N] [Module (X D a) N]
    (r : X D a) (n : N), toY (r • n) = xToY D a r • toY n

def TransportBijective : Prop :=
  ∀ {N : Type w}, Function.Bijective (toY : N → OnY N)

def FiniteTransport : Prop :=
  ∀ {D : Type u} [CommRing D] {a : ℕ} {N : Type w} [AddCommGroup N] [Module (X D a) N]
    [Module.Finite (X D a) N], Module.Finite (Y D a) (OnY N)

set_option linter.checkUnivs false in
abbrev OnYMapType :=
  ∀ {D : Type u} [CommRing D] {a : ℕ} {N : Type w}
    [AddCommGroup N] [Module (X D a) N] {N' : Type w'}
    [AddCommGroup N'] [Module (X D a) N'],
    (N →ₗ[X D a] N') → (OnY N →ₗ[Y D a] OnY N')

noncomputable abbrev onYMapValue : OnYMapType.{u, w, w'} :=
  fun {D} _ {a} {_} _ _ {_} _ _ f =>
    { toFun := fun n => f n
      map_add' := f.map_add
      map_smul' := fun r => f.map_smul ((xToY D a).symm r) }

end Spec

end CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
