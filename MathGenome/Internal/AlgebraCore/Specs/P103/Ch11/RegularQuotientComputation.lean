import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.Module.Opposite

/-! The two-term computation of paper.tex 2779–2790.
The quotient is the module quotient by the image of multiplication by r.
No nontriviality hypothesis on the ring or quotient is imposed. -/
namespace P103.Specs.Ch11.RegularQuotientComputation
open CategoryTheory
open P103.Specs.Ch10.ProjectiveResolutions
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v

section TwoTerm
variable {S : Type u} [Ring S] {M : Type v} [AddCommGroup M] [Module S M]

def term (M : Type v) [AddCommGroup M] [Module S M] : ℕ → ModuleCat.{v} S
  | 0 => ModuleCat.of S M
  | 1 => ModuleCat.of S M
  | _ + 2 => ModuleCat.of S (PUnit.{v+1})

def differential (d : M →ₗ[S] M) : ∀ n, term (S := S) M (n+1) ⟶ term (S := S) M n
  | 0 => ModuleCat.ofHom d
  | _ + 1 => 0

def twoTerm (d : M →ₗ[S] M) : ChainComplex (ModuleCat.{v} S) ℕ :=
  ChainComplex.of (term M) (differential d) (by
    intro n
    cases n with
    | zero => ext x; exact map_zero d
    | succ n => rfl)

@[simp] theorem twoTerm_d (d : M →ₗ[S] M) (n : ℕ) :
    (twoTerm d).d (n+1) n = differential d n := by simp only [twoTerm, ChainComplex.of_d]

end TwoTerm

variable {R : Type u} [CommRing R]
/-- Multiplication by r, as a map of left modules. -/
def multiply (r : R) : R →ₗ[R] R := r • LinearMap.id
/-- The same map on the right regular module. -/
def rightMultiply (r : R) : R →ₗ[Rᵐᵒᵖ] R where
  toFun a := r * a
  map_add' _ _ := mul_add _ _ _
  map_smul' s a := by
    change r * (a * s.unop) = (r * a) * s.unop
    exact (mul_assoc _ _ _).symm

abbrev Quotient (r : R) := R ⧸ LinearMap.range (multiply r)

/-- The right and left quotients have literally the same additive relation. -/
instance quotientRightModule (r : R) : Module Rᵐᵒᵖ (Quotient r) :=
  inferInstanceAs (Module Rᵐᵒᵖ (R ⧸ LinearMap.range (rightMultiply r)))

abbrev leftComplex (r : R) := twoTerm (multiply r)
abbrev rightComplex (r : R) := twoTerm (rightMultiply r)

/-- The annihilator and the quotient of the coefficient module. -/
def scalar (r : R) (B : Type v) [AddCommGroup B] [Module R B] : B →ₗ[R] B :=
  r • LinearMap.id
abbrev Torsion (r : R) (B : Type v) [AddCommGroup B] [Module R B] :=
  LinearMap.ker (scalar r B)
abbrev Modulo (r : R) (B : Type v) [AddCommGroup B] [Module R B] :=
  B ⧸ LinearMap.range (scalar r B)

/-- Hom cohomology of the displayed complex. Its interpretation as Ext is
certified by `RegularComputation.left_model` and the free resolution. -/
abbrev Ext (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (homComplex (leftComplex r) B) n
abbrev Tor (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (tensorComplex (rightComplex r) B) n

def extCoefficients (r : R) (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} ℤ where
  obj B := ModuleCat.of ℤ (Ext r B n)
  map g := ModuleCat.ofHom (homologyMap (homPostMap (leftComplex r) g.hom) n)
  map_id B := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    rfl
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    rfl

instance (r : R) (n : ℕ) : (extCoefficients.{u,v} r n).Additive where
  map_add := by
    intro B B' g h
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    change homologyClass _ n _ = homologyClass _ n _ + homologyClass _ n _
    rw [← map_add]
    rfl

theorem tensorMap_id (A : Type*) (B : Type*) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module R B] :
    tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (LinearMap.id : B →ₗ[R] B) = LinearMap.id := by
  apply tensor_hom_ext
  intro a b
  rfl

theorem tensorSecond_comp (A : Type*) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B B' B'' : Type*} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] [AddCommGroup B''] [Module R B'']
    (g : B →ₗ[R] B') (h : B' →ₗ[R] B'') :
    tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (h.comp g) =
      (tensorMap LinearMap.id h).comp (tensorMap LinearMap.id g) := by
  apply tensor_hom_ext
  intro a b
  rfl

def torCoefficients (r : R) (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} ℤ where
  obj B := ModuleCat.of ℤ (Tor r B n)
  map g := ModuleCat.ofHom (homologyMap (tensorSecondMap (rightComplex r) g.hom) n)
  map_id B := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    exact LinearMap.congr_fun (tensorMap_id ((rightComplex r).X n) B) z.val
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    exact LinearMap.congr_fun (tensorSecond_comp ((rightComplex r).X n) g.hom h.hom) z.val

instance (r : R) (n : ℕ) : (torCoefficients.{u,v} r n).Additive where
  map_add := by
    intro B B' g h
    apply ModuleCat.hom_ext
    apply (cycleBoundaries _ n).quot_hom_ext
    intro z
    change homologyClass _ n _ = homologyClass _ n _ + homologyClass _ n _
    rw [← map_add]
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    apply LinearMap.congr_fun (show
      tensorMap (LinearMap.id : _ →ₗ[Rᵐᵒᵖ] _) (g + h).hom =
        tensorMap LinearMap.id g.hom + tensorMap LinearMap.id h.hom from ?_) z.val
    apply tensor_hom_ext
    intro a b
    change P103.BalancedTensor.tmul R a (g.hom b + h.hom b) =
      P103.BalancedTensor.tmul R a (g.hom b) + P103.BalancedTensor.tmul R a (h.hom b)
    simp [P103.BalancedTensor.tmul, TensorProduct.tmul_add]

/-- These are the usual scalar actions, induced by coefficient multiplication. -/
instance extModule (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :
    Module R (Ext r B n) := coefficientModule (extCoefficients r n) (ModuleCat.of R B)
instance torModule (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :
    Module R (Tor r B n) := coefficientModule (torCoefficients r n) (ModuleCat.of R B)

def torsionMap (r : R) {B B' : Type v} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] (g : B →ₗ[R] B') : Torsion r B →ₗ[R] Torsion r B' :=
  (g.comp (Torsion r B).subtype).codRestrict _ (by
    intro b
    change r • g b.val = 0
    rw [← g.map_smul]
    exact (congrArg g b.property).trans (map_zero g))

def moduloMap (r : R) {B B' : Type v} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] (g : B →ₗ[R] B') : Modulo r B →ₗ[R] Modulo r B' :=
  (LinearMap.range (scalar r B)).mapQ (LinearMap.range (scalar r B')) g (by
    rintro _ ⟨b, rfl⟩
    exact ⟨g b, (g.map_smul r b).symm⟩)

/-- Linear identifications in both degrees, with their coefficient diagrams. -/
structure ExtComputation (r : R) where
  zero : ∀ B : ModuleCat.{v} R, Ext r B 0 ≃ₗ[R] Torsion r B
  one : ∀ B : ModuleCat.{v} R, Ext r B 1 ≃ₗ[R] Modulo r B
  zero_natural : ∀ {B B' : ModuleCat.{v} R} (g : B ⟶ B') x,
    zero B' (((extCoefficients r 0).map g).hom x) = torsionMap r g.hom (zero B x)
  one_natural : ∀ {B B' : ModuleCat.{v} R} (g : B ⟶ B') x,
    one B' (((extCoefficients r 1).map g).hom x) = moduloMap r g.hom (one B x)
  higher : ∀ (B : ModuleCat.{v} R) (n : ℕ), Subsingleton (Ext r B (n+2))

structure TorComputation (r : R) where
  zero : ∀ B : ModuleCat.{v} R, Tor r B 0 ≃ₗ[R] Modulo r B
  one : ∀ B : ModuleCat.{v} R, Tor r B 1 ≃ₗ[R] Torsion r B
  zero_natural : ∀ {B B' : ModuleCat.{v} R} (g : B ⟶ B') x,
    zero B' (((torCoefficients r 0).map g).hom x) = moduloMap r g.hom (zero B x)
  one_natural : ∀ {B B' : ModuleCat.{v} R} (g : B ⟶ B') x,
    one B' (((torCoefficients r 1).map g).hom x) = torsionMap r g.hom (one B x)
  higher : ∀ (B : ModuleCat.{v} R) (n : ℕ), Subsingleton (Tor r B (n+2))

def free_resolutionType : Prop :=
  ∀ (R : Type u) [CommRing R] (r : R), Function.Injective (multiply r) →
    (∃ P : Resolution R (Quotient r), P.complex = leftComplex r ∧
      HEq P.ε (LinearMap.range (multiply r)).mkQ ∧ P.IsFree) ∧
    (∃ P : Resolution Rᵐᵒᵖ (Quotient r), P.complex = rightComplex r ∧
      HEq P.ε (LinearMap.range (rightMultiply r)).mkQ ∧ P.IsFree)

def ext_computationType : Prop :=
  ∀ (R : Type u) [CommRing R] (r : R), Function.Injective (multiply r) →
    Nonempty (ExtComputation.{u,v} r)
def tor_computationType : Prop :=
  ∀ (R : Type u) [CommRing R] (r : R), Function.Injective (multiply r) →
    Nonempty (TorComputation.{u,v} r)

/-- The computed complexes are the upstream Ext/Tor resolution models of the
same quotient module, with their actual augmentations and free terms. -/
structure RegularComputation (r : R) where
  left : Resolution R (Quotient r)
  left_shape : left.complex = leftComplex r
  left_augmentation : HEq left.ε (LinearMap.range (multiply r)).mkQ
  left_free : left.IsFree
  left_model : ∀ (B : ModuleCat.{v} R) n,
    ExtWith left B n = Ext r B n
  right : Resolution Rᵐᵒᵖ (Quotient r)
  right_shape : right.complex = rightComplex r
  right_augmentation : HEq right.ε (LinearMap.range (rightMultiply r)).mkQ
  right_free : right.IsFree
  right_model : ∀ (B : ModuleCat.{v} R) n,
    TorWith right B n = Tor r B n
  ext : ExtComputation.{u,v} r
  tor : TorComputation.{u,v} r

def regular_computationType : Prop :=
  ∀ (R : Type u) [CommRing R] (r : R), Function.Injective (multiply r) →
    Nonempty (RegularComputation.{u,v} r)

/-- A nonzero kernel prevents exactness at the leftmost R. -/
def not_resolutionType : Prop :=
  ∀ (R : Type u) [CommRing R] (r : R), (∃ a : R, a ≠ 0 ∧ r * a = 0) →
    ¬ ∃ P : Resolution R (Quotient r), P.complex = leftComplex r

end
end P103.Specs.Ch11.RegularQuotientComputation
