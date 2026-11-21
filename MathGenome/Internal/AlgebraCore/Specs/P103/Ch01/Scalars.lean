import Mathlib.Algebra.Algebra.Hom

/-! Interfaces for paper.tex, Definition 1.3 and its following paragraph.
Rings and modules may be zero; only the algebra base is commutative. -/
namespace P103.Scalars

universe u v w t

section Algebra
variable {k : Type u} {A : Type v} [CommRing k] [Ring A]

/-- The structure map with its central codomain retained. -/
def centerMap (a : Algebra k A) : k →+* Subring.center A := by
  letI := a
  exact
    { toFun := fun r => ⟨algebraMap k A r,
        Subring.mem_center_iff.mpr (fun x => (Algebra.commutes r x).symm)⟩
      map_one' := Subtype.ext (map_one (algebraMap k A))
      map_mul' := fun r s => Subtype.ext (map_mul (algebraMap k A) r s)
      map_zero' := Subtype.ext (map_zero (algebraMap k A))
      map_add' := fun r s => Subtype.ext (map_add (algebraMap k A) r s) }

/-- A central unital ring map acts by left multiplication. -/
abbrev algebraOfCenter (f : k →+* Subring.center A) : Algebra k A :=
  ((Subring.center A).subtype.comp f).toAlgebra' (fun r x =>
    (Subring.mem_center_iff.mp (f r).property x).symm)

/-- A module structure on the additive group of the given ring, for which
multiplication is linear separately in both variables. Additivity in both
variables and the associative unital multiplication are already ring laws. -/
structure CompatibleModule (k : Type u) (A : Type v) [CommRing k] [Ring A] where
  module : Module k A
  left_linear : letI := module; ∀ (r : k) (x y : A), (r • x) * y = r • (x * y)
  right_linear : letI := module; ∀ (r : k) (x y : A), x * (r • y) = r • (x * y)

/-- Forget a central algebra structure to its module and bilinear product. -/
def compatibleModule (a : Algebra k A) : CompatibleModule k A := by
  letI := a
  exact ⟨Algebra.toModule, Algebra.smul_mul_assoc, Algebra.mul_smul_comm⟩

/-- Recover the algebra structure map as `r ↦ r • 1`. -/
abbrev algebraOfModule (b : CompatibleModule k A) : Algebra k A := by
  letI := b.module
  exact Algebra.ofModule b.left_linear b.right_linear

end Algebra

section Morphisms
variable {k : Type u} {A : Type v} {B : Type w}
variable [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- Ring maps compatible with the two central structure maps. -/
def CompatibleRingHom :=
  { f : A →+* B // ∀ r : k, f (algebraMap k A r) = algebraMap k B r }

def ringHomOfAlgHom (f : A →ₐ[k] B) : CompatibleRingHom (k := k) (A := A) (B := B) :=
  ⟨f.toRingHom, f.commutes⟩

def algHomOfRingHom (f : CompatibleRingHom (k := k) (A := A) (B := B)) : A →ₐ[k] B :=
  { f.val with commutes' := f.property }

end Morphisms

section Restriction
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (u : R →+* S) (M : Type w) [AddCommGroup M] [Module S M]

/-- Restriction uses any unital ring map, with no centrality assumption. -/
abbrev restrictModule : Module R M := Module.compHom M u

variable {M} {N : Type t} [AddCommGroup N] [Module S N]

/-- A linear map on restricted modules is the original additive map. -/
def restrictLinearMap (f : M →ₗ[S] N) :
    letI := restrictModule u M
    letI := restrictModule u N
    M →ₗ[R] N :=
  letI := restrictModule u M
  letI := restrictModule u N
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun r x => f.map_smul (u r) x }

end Restriction

namespace Spec

/-- The type of the central-map construction; `algebraOfCenter` is its
independent expected value. -/
def algebraFromCentralMapType :=
  ∀ {k : Type u} {A : Type v} [CommRing k] [Ring A],
    (k →+* Subring.center A) → Algebra k A

/-- Both inverse identities and the specified scalar formula. -/
def centerIdentification (k : Type u) (A : Type v) [CommRing k] [Ring A] : Prop :=
  (∀ a : Algebra k A, algebraOfCenter (centerMap a) = a) ∧
  (∀ f : k →+* Subring.center A, centerMap (algebraOfCenter f) = f) ∧
  (∀ (f : k →+* Subring.center A) (r : k) (x : A),
    letI := algebraOfCenter f
    r • x = (f r : A) * x) ∧
  (∀ (a : Algebra k A) (r : k),
    (centerMap a r : A) = (letI := a; r • (1 : A)))

/-- The module description is equivalent, with the recovered central map `r • 1`. -/
def moduleIdentification (k : Type u) (A : Type v) [CommRing k] [Ring A] : Prop :=
  (∀ a : Algebra k A, algebraOfModule (compatibleModule a) = a) ∧
  (∀ b : CompatibleModule k A, compatibleModule (algebraOfModule b) = b) ∧
  (∀ (b : CompatibleModule k A) (r : k),
    (centerMap (algebraOfModule b) r : A) = (letI := b.module; r • (1 : A))) ∧
  (∀ (b : CompatibleModule k A) (r : k) (x : A),
    letI := b.module
    (r • (1 : A)) * x = x * (r • (1 : A)))

/-- The same morphism convention in the ring and module descriptions. -/
def morphismIdentification (k : Type u) (A : Type v) (B : Type w)
    [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] : Prop :=
  (∀ f : A →ₐ[k] B, algHomOfRingHom (ringHomOfAlgHom f) = f) ∧
  (∀ f : CompatibleRingHom (k := k) (A := A) (B := B),
    ringHomOfAlgHom (algHomOfRingHom f) = f) ∧
  (∀ f : A →+* B,
    (∀ r : k, f (algebraMap k A r) = algebraMap k B r) ↔
    (∀ (r : k) (x : A), f (r • x) = r • f x))

/-- All six module action laws are certified by the resulting `Module`; this
also specifies the action itself for every, possibly noncommutative, ring map. -/
def restrictionAction (R : Type u) (S : Type v) (M : Type w)
    [Ring R] [Ring S] [AddCommGroup M] [Module S M] : Prop :=
  ∀ (u : R →+* S) (r : R) (x : M),
    (letI := restrictModule u M; r • x) = u r • x

/-- Restriction on maps preserves their values, identities, and composition. -/
def restrictionMaps (R : Type u) (S : Type v)
    (M : Type w) (N : Type t) (P : Type*)
    [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P] : Prop :=
  ∀ u : R →+* S,
    (∀ (f : M →ₗ[S] N) (x : M), restrictLinearMap u f x = f x) ∧
    ((letI := restrictModule u M
      restrictLinearMap u (LinearMap.id : M →ₗ[S] M)) =
      (letI := restrictModule u M; (LinearMap.id : M →ₗ[R] M))) ∧
    (∀ (f : M →ₗ[S] N) (g : N →ₗ[S] P),
      restrictLinearMap u (g.comp f) =
      (letI := restrictModule u M
       letI := restrictModule u N
       letI := restrictModule u P
       (restrictLinearMap u g).comp (restrictLinearMap u f)))

/-- Restriction along identity and composite ring maps agrees with iterated
restriction, including the entire module structure. -/
def restrictionComposition (R : Type u) (S : Type v) (T : Type t) (M : Type w)
    [Ring R] [Ring S] [Ring T] [AddCommGroup M] [Module T M] : Prop :=
  (restrictModule (RingHom.id T) M = (inferInstance : Module T M)) ∧
  (∀ (u : R →+* S) (v : S →+* T),
    restrictModule (v.comp u) M =
    (letI := restrictModule v M; restrictModule u M))


/- The binding declarations below quantify over all objects and instances;
these are full proposition types, independent of the implementation. -/
def centerIdentificationType : Prop :=
  ∀ (k : Type u) (A : Type v) [CommRing k] [Ring A], centerIdentification k A

def moduleIdentificationType : Prop :=
  ∀ (k : Type u) (A : Type v) [CommRing k] [Ring A], moduleIdentification k A

def morphismIdentificationType : Prop :=
  ∀ (k : Type u) (A : Type v) (B : Type w)
    [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B],
    morphismIdentification k A B

def restrictionActionType : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [Ring R] [Ring S] [AddCommGroup M] [Module S M], restrictionAction R S M

def restrictionMapsType : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w) (N : Type t) (P : Type*)
    [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P], restrictionMaps R S M N P

def restrictionCompositionType : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type t) (M : Type w)
    [Ring R] [Ring S] [Ring T] [AddCommGroup M] [Module T M],
    restrictionComposition R S T M

end Spec
end P103.Scalars
