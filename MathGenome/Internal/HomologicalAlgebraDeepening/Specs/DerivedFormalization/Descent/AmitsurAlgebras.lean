import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-! The ordered tensor powers and maps of the augmented Amitsur diagram. -/

open CategoryTheory
open scoped BigOperators TensorProduct

namespace AmitsurAlgebrasSpec

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- The count is the number of factors. Degree `p` of the Amitsur diagram uses count `p + 1`. -/
abbrev tensorPower (n : ℕ) := ⨂[A] _ : Fin n, B

abbrev degree (p : ℕ) := tensorPower A B (p + 1)

noncomputable def factor {n : ℕ} (i : Fin n) : B →ₐ[A] tensorPower A B n :=
  PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin n ↦ B) i

variable {A B}

/-- The canonical map out of the tensor power specified by its maps on all factors. -/
noncomputable def liftFactors {n : ℕ} {D : Type*} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) : tensorPower A B n →ₐ[A] D :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra A (Fin n) D).compLinearMap fun i ↦ (f i).toLinearMap)
    (by simp)
    (by intro x y; simp [Finset.prod_mul_distrib])

/-- An old factor at `i` maps into the target factor at `f i`. -/
noncomputable def map {m n : ℕ} (f : Fin m → Fin n) :
    tensorPower A B m →ₐ[A] tensorPower A B n :=
  liftFactors fun i ↦ factor A B (f i)

noncomputable def coface {p : ℕ} (i : Fin (p + 2)) : degree A B p →ₐ[A] degree A B (p + 1) :=
  map i.succAbove

noncomputable def codegeneracy {p : ℕ} (i : Fin (p + 1)) :
    degree A B (p + 1) →ₐ[A] degree A B p :=
  map i.predAbove

variable (A B)

/-- The unit map from the augmented term into an arbitrary tensor power. -/
noncomputable def unit (n : ℕ) : A →ₐ[A] tensorPower A B n :=
  Algebra.ofId A _

noncomputable def augmentation : A →ₐ[A] degree A B 0 :=
  unit A B 1

private theorem map_on_factor {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) (b : B) :
    map f (factor A B i b) = factor A B (f i) b := by
  let x : Fin m → B := Pi.mulSingle (M := fun _ ↦ B) i b
  change PiTensorProduct.lift _ (PiTensorProduct.tprod A x) = _
  rw [PiTensorProduct.lift.tprod]
  change (∏ j, factor A B (f j) (x j)) = _
  rw [Finset.prod_eq_single i]
  · simp [x]
  · intro j _ h
    simp [x, Pi.mulSingle_eq_of_ne h]
  · simp

/-- The expected functor on the nonempty finite ordinals. -/
noncomputable def diagram : SimplexCategory ⥤ CommAlgCat.{max u v} A where
  obj p := CommAlgCat.of A (degree A B p.len)
  map f := CommAlgCat.ofHom (map f.toOrderHom)
  map_id p := by
    apply CommAlgCat.hom_ext
    apply PiTensorProduct.algHom_ext
    intro i
    refine AlgHom.ext fun b ↦ ?_
    exact map_on_factor A B id i b
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply PiTensorProduct.algHom_ext
    intro i
    refine AlgHom.ext fun b ↦ ?_
    change map (g.toOrderHom ∘ f.toOrderHom) (factor A B i b) =
      map g.toOrderHom (map f.toOrderHom (factor A B i b))
    simp only [map_on_factor, Function.comp_apply]

/-- The empty ordinal maps to the base algebra, with its unit maps to all degrees. -/
noncomputable def augmentedDiagram : AugmentedSimplexCategory ⥤ CommAlgCat.{max u v} A :=
  WithInitial.lift (Z := CommAlgCat.of A (ULift.{v} A)) (diagram A B)
    (fun p ↦ CommAlgCat.ofHom ((unit A B (p.len + 1)).comp ULift.algEquiv.toAlgHom))
    (fun _ _ f ↦ by
      apply CommAlgCat.hom_ext
      change ((map f.toOrderHom).comp (unit A B _)).comp ULift.algEquiv.toAlgHom =
        (unit A B _).comp ULift.algEquiv.toAlgHom
      congr 1
      exact Subsingleton.elim _ _)

section

-- The ambient sort of a closed type combines its independently bound universes.
set_option linter.checkUnivs false

private def declarationType {T : Sort w} (_ : T) := T

def TensorPowerType := declarationType (@tensorPower.{u, v})
def DegreeType := declarationType (@degree.{u, v})
def FactorType := declarationType (@factor.{u, v})
def LiftFactorsType := declarationType (@liftFactors.{u, v, w})
def MapType := declarationType (@map.{u, v})
def CofaceType := declarationType (@coface.{u, v})
def CodegeneracyType := declarationType (@codegeneracy.{u, v})
def UnitType := declarationType (@unit.{u, v})
def AugmentationType := declarationType (@augmentation.{u, v})
def DiagramType := declarationType (@diagram.{u, v})
def AugmentedDiagramType := declarationType (@augmentedDiagram.{u, v})

end

def liftFactors_tprod : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
      (f : Fin n → B →ₐ[A] D) (x : Fin n → B),
      liftFactors f (PiTensorProduct.tprod A x) = ∏ i, f i (x i)

def hom_ext : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
      {f g : tensorPower A B n →ₐ[A] D},
      (∀ i, f.comp (factor A B i) = g.comp (factor A B i)) → f = g

def liftFactors_comp_factor : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
      (f : Fin n → B →ₐ[A] D) (i : Fin n),
      (liftFactors f).comp (factor A B i) = f i

def map_comp_factor : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {m n : ℕ} (f : Fin m → Fin n) (i : Fin m),
      (map f).comp (factor A B i) = factor A B (f i)

def map_tprod : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {m n : ℕ} (f : Fin m → Fin n) (x : Fin m → B),
      map f (PiTensorProduct.tprod A x) =
        PiTensorProduct.tprod A (fun j ↦ ∏ i ∈ Finset.univ.filter (fun i ↦ f i = j), x i)

def coface_tprod : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {p : ℕ} (i : Fin (p + 2)) (x : Fin (p + 1) → B),
      coface i (PiTensorProduct.tprod A x) = PiTensorProduct.tprod A (i.insertNth 1 x)

def codegeneracy_tprod : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {p : ℕ} (i : Fin (p + 1)) (x : Fin (p + 2) → B),
      codegeneracy i (PiTensorProduct.tprod A x) =
        PiTensorProduct.tprod A (i.castSucc.contractNth (· * ·) x)

def map_id : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ (n : ℕ), map (id : Fin n → Fin n) = AlgHom.id A (tensorPower A B n)

def map_comp : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ {l m n : ℕ} (f : Fin l → Fin m) (g : Fin m → Fin n),
      map (g ∘ f) = (map g).comp (map f : tensorPower A B l →ₐ[A] _)

def map_comp_unit : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ {m n : ℕ} (f : Fin m → Fin n),
      (map f).comp (unit A B m) = unit A B n

/-- Two ordered insertions in the form used by the alternating coface differential. -/
def coface_comp_coface : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ {p : ℕ} {i j : Fin (p + 2)}, i ≤ j →
      (coface j.succ).comp (coface i) = (coface i.castSucc).comp (coface j :
        degree A B p →ₐ[A] degree A B (p + 1))

def coface_comp_augmentation : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ i : Fin 2, (coface i).comp (augmentation A B) = unit A B 2

/-- A functor on the augmented simplex category with the stated objects and maps.
The lift of the augmentation object allows independent universes for the rings. -/
def IsOrderedAugmentedDiagram
    (F : AugmentedSimplexCategory ⥤ CommAlgCat.{max u v} A) : Prop :=
  F.obj WithInitial.star = CommAlgCat.of A (ULift.{v} A) ∧
    (∀ p : SimplexCategory, F.obj (WithInitial.of p) = CommAlgCat.of A (degree A B p.len)) ∧
    (∀ {p q : SimplexCategory} (f : p ⟶ q),
      HEq (F.map (AugmentedSimplexCategory.inclusion.map f))
        (CommAlgCat.ofHom (map f.toOrderHom :
          degree A B p.len →ₐ[A] degree A B q.len))) ∧
    (∀ p : SimplexCategory, HEq (F.map (WithInitial.homTo p))
      (CommAlgCat.ofHom ((unit A B (p.len + 1)).comp
        (ULift.algEquiv : ULift.{v} A ≃ₐ[A] A).toAlgHom)))

def orderedAugmentedDiagram : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ F, IsOrderedAugmentedDiagram A B F

def emptyPower : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : tensorPower A B 0 ≃ₐ[A] A, e.symm.toAlgHom = unit A B 0

def onePower : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : degree A B 0 ≃ₐ[A] B,
      e.symm.toAlgHom = factor A B 0 ∧ e.toAlgHom.comp (augmentation A B) = Algebra.ofId A B

def appendPowers : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ m n : ℕ, ∃ e : tensorPower A B m ⊗[A] tensorPower A B n ≃ₐ[A] tensorPower A B (m + n),
      ∀ x y, e (x ⊗ₜ[A] y) = map (Fin.castAdd n) x * map (Fin.natAdd m) y

/-- Base change preserves the labeled factors and every map of factor positions. -/
def baseChangePowers : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ (S : Type w) [CommRing S] [Algebra A S],
      ∃ e : ∀ n : ℕ, S ⊗[A] tensorPower A B n ≃ₐ[S] tensorPower S (S ⊗[A] B) n,
        (∀ {n : ℕ} (i : Fin n) (s : S) (b : B),
          e n (s ⊗ₜ[A] factor A B i b) = factor S (S ⊗[A] B) i (s ⊗ₜ[A] b)) ∧
        (∀ {m n : ℕ} (f : Fin m → Fin n),
          (e n).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id S S) (map f)) =
            (map f).comp (e m).toAlgHom)

end AmitsurAlgebrasSpec
