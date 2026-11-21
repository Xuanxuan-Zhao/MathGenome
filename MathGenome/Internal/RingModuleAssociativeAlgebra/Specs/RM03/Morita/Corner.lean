import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
The corner and its modules for an idempotent in a unital ring.
A right module over a ring is a left module over its opposite ring.
-/

universe u v

namespace RM03.Morita

open MulOpposite

/-- An element of the ambient ring together with its idempotence equation. -/
abbrev Idempotent (R : Type u) [Ring R] := {e : R // IsIdempotentElem e}

variable {R : Type u} [Ring R]

/-- The inclusion into the ambient ring preserves the non-unital operations. -/
def cornerSubring (e : Idempotent R) : NonUnitalSubring R where
  carrier := {a | e.val * a = a ∧ a * e.val = a}
  zero_mem' := ⟨mul_zero _, zero_mul _⟩
  add_mem' ha hb := ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  neg_mem' ha := ⟨by rw [mul_neg, ha.1], by rw [neg_mul, ha.2]⟩
  mul_mem' ha hb := ⟨by rw [← mul_assoc, ha.1], by rw [mul_assoc, hb.2]⟩

/-- The ring (eRe) with identity (e). -/
abbrev Corner (e : Idempotent R) := ↥(cornerSubring e)

instance cornerRing (e : Idempotent R) : Ring (Corner e) where
  __ := (inferInstance : NonUnitalRing ↥(cornerSubring e))
  one := ⟨e.val, e.property, e.property⟩
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

@[simp] theorem corner_one_val (e : Idempotent R) : (1 : Corner e).val = e.val := rfl
@[simp] theorem corner_mul_val {e : Idempotent R} (a b : Corner e) :
    (a * b).val = a.val * b.val := rfl

/-- The right ideal (eR) in the regular right module. -/
def rightIdeal (e : Idempotent R) : Submodule Rᵐᵒᵖ R where
  carrier := {x | e.val * x = x}
  zero_mem' := mul_zero _
  add_mem' {x y} hx hy := by
    change e.val * (x + y) = x + y
    rw [mul_add, hx, hy]
  smul_mem' r x hx := by
    change e.val * (x * r.unop) = x * r.unop
    rw [← mul_assoc, hx]

/-- The left ideal (Re) in the regular left module. -/
def leftIdeal (e : Idempotent R) : Submodule R R where
  carrier := {x | x * e.val = x}
  zero_mem' := zero_mul _
  add_mem' {x y} hx hy := by
    change (x + y) * e.val = x + y
    rw [add_mul, hx, hy]
  smul_mem' r x hx := by
    change (r * x) * e.val = r * x
    rw [mul_assoc, hx]

/-- The element (e) of (eR). -/
def rightGenerator (e : Idempotent R) : rightIdeal e := ⟨e.val, e.property⟩

/-- The element (e) of (Re). -/
def leftGenerator (e : Idempotent R) : leftIdeal e := ⟨e.val, e.property⟩

/-- (eR) is a left (eRe)-module by multiplication in (R). -/
instance rightIdealCornerModule (e : Idempotent R) : Module (Corner e) (rightIdeal e) where
  smul a x := ⟨a.val * x.val, by
    change e.val * (a.val * x.val) = a.val * x.val
    rw [← mul_assoc, a.property.1]⟩
  one_smul x := Subtype.ext x.property
  mul_smul a b x := Subtype.ext (mul_assoc a.val b.val x.val)
  smul_zero a := Subtype.ext (mul_zero a.val)
  smul_add a x y := Subtype.ext (mul_add a.val x.val y.val)
  add_smul a b x := Subtype.ext (add_mul a.val b.val x.val)
  zero_smul x := Subtype.ext (zero_mul x.val)

/-- (Re) is a right (eRe)-module by multiplication in (R). -/
instance leftIdealCornerModule (e : Idempotent R) : Module (Corner e)ᵐᵒᵖ (leftIdeal e) where
  smul a x := ⟨x.val * a.unop.val, by
    change (x.val * a.unop.val) * e.val = x.val * a.unop.val
    rw [mul_assoc, a.unop.property.2]⟩
  one_smul x := Subtype.ext x.property
  mul_smul a b x := Subtype.ext (mul_assoc x.val b.unop.val a.unop.val).symm
  smul_zero a := Subtype.ext (zero_mul a.unop.val)
  smul_add a x y := Subtype.ext (add_mul x.val y.val a.unop.val)
  add_smul a b x := Subtype.ext (mul_add x.val a.unop.val b.unop.val)
  zero_smul x := Subtype.ext (mul_zero x.val)

@[simp] theorem rightIdeal_corner_smul_val {e : Idempotent R} (a : Corner e)
    (x : rightIdeal e) : (a • x).val = a.val * x.val := rfl

@[simp] theorem rightIdeal_op_smul_val {e : Idempotent R} (r : Rᵐᵒᵖ)
    (x : rightIdeal e) : (r • x).val = x.val * r.unop := rfl

@[simp] theorem leftIdeal_corner_smul_val {e : Idempotent R} (a : (Corner e)ᵐᵒᵖ)
    (x : leftIdeal e) : (a • x).val = x.val * a.unop.val := rfl

@[simp] theorem leftIdeal_smul_val {e : Idempotent R} (r : R)
    (x : leftIdeal e) : (r • x).val = r * x.val := rfl

instance rightIdealBimodule (e : Idempotent R) : SMulCommClass (Corner e) Rᵐᵒᵖ (rightIdeal e) where
  smul_comm a r x := Subtype.ext (mul_assoc a.val x.val r.unop).symm

instance rightIdealBimoduleSymm (e : Idempotent R) :
    SMulCommClass Rᵐᵒᵖ (Corner e) (rightIdeal e) :=
  SMulCommClass.symm _ _ _

instance leftIdealBimodule (e : Idempotent R) : SMulCommClass R (Corner e)ᵐᵒᵖ (leftIdeal e) where
  smul_comm r a x := Subtype.ext (mul_assoc r x.val a.unop.val).symm

instance leftIdealBimoduleSymm (e : Idempotent R) :
    SMulCommClass (Corner e)ᵐᵒᵖ R (leftIdeal e) :=
  SMulCommClass.symm _ _ _

/-- The idempotent gives a unital map into the endomorphisms of (eR). -/
def cornerToEnd (e : Idempotent R) : Corner e →+* Module.End Rᵐᵒᵖ (rightIdeal e) where
  toFun a :=
    { toFun := fun x => a • x
      map_add' := smul_add a
      map_smul' := smul_comm a }
  map_zero' := LinearMap.ext (zero_smul (Corner e))
  map_add' a b := LinearMap.ext (add_smul a b)
  map_one' := LinearMap.ext (one_smul (Corner e))
  map_mul' a b := LinearMap.ext (mul_smul a b)

section ModuleCorner

variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The fixed points of right multiplication by (e), equivalently (Me). -/
def moduleCorner (e : Idempotent R) : AddSubgroup M where
  carrier := {m | op e.val • m = m}
  zero_mem' := smul_zero _
  add_mem' {m n} hm hn := by
    change op e.val • (m + n) = m + n
    rw [smul_add, hm, hn]
  neg_mem' {m} hm := by
    change op e.val • (-m) = -m
    rw [smul_neg, hm]

/-- Right multiplication by (e) as an additive map into (Me). -/
def toModuleCorner (e : Idempotent R) : M →+ moduleCorner (M := M) e where
  toFun m := ⟨op e.val • m, by
    change op e.val • (op e.val • m) = op e.val • m
    rw [← mul_smul, ← op_mul, e.property.eq]⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' m n := Subtype.ext (smul_add _ m n)

instance moduleCornerModule (e : Idempotent R) :
    Module (Corner e)ᵐᵒᵖ (moduleCorner (M := M) e) where
  smul a m := ⟨op a.unop.val • m.val, by
    change op e.val • (op a.unop.val • m.val) = op a.unop.val • m.val
    rw [← mul_smul, ← op_mul, a.unop.property.2]⟩
  one_smul m := Subtype.ext m.property
  mul_smul a b m := Subtype.ext (mul_smul (op a.unop.val) (op b.unop.val) m.val)
  smul_zero a := Subtype.ext (smul_zero (op a.unop.val))
  smul_add a m n := Subtype.ext (smul_add (op a.unop.val) m.val n.val)
  add_smul a b m := Subtype.ext (add_smul (op a.unop.val) (op b.unop.val) m.val)
  zero_smul m := Subtype.ext (zero_smul Rᵐᵒᵖ m.val)

@[simp] theorem moduleCorner_smul_val {e : Idempotent R} (a : (Corner e)ᵐᵒᵖ)
    (m : moduleCorner (M := M) e) : (a • m).val = op a.unop.val • m.val := rfl

variable {N : Type*} [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Restriction of a right (R)-linear map to the images of multiplication by (e). -/
def restrictToCorner (e : Idempotent R) (f : M →ₗ[Rᵐᵒᵖ] N) :
    moduleCorner (M := M) e →ₗ[(Corner e)ᵐᵒᵖ] moduleCorner (M := N) e where
  toFun m := ⟨f m.val, by
    change op e.val • f m.val = f m.val
    rw [← f.map_smul, m.property]⟩
  map_add' m n := Subtype.ext (f.map_add m.val n.val)
  map_smul' a m := Subtype.ext (f.map_smul (op a.unop.val) m.val)

@[simp] theorem restrictToCorner_val (e : Idempotent R) (f : M →ₗ[Rᵐᵒᵖ] N)
    (m : moduleCorner (M := M) e) : (restrictToCorner e f m).val = f m.val := rfl

end ModuleCorner

namespace CornerSpec

open CategoryTheory

-- The ring and module universe levels are independent.
set_option linter.checkUnivs false in
def cornerFunctorType : Type _ :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} (Corner e)ᵐᵒᵖ

/-- The corner functor on all right modules, with the restriction maps on morphisms. -/
def cornerFunctorValue : cornerFunctorType.{u, v} :=
  fun e =>
    { obj := fun M => ModuleCat.of (Corner e)ᵐᵒᵖ (moduleCorner (M := M) e)
      map := fun f => ModuleCat.ofHom (restrictToCorner e f.hom)
      map_id := fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
      map_comp := fun _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }

def carriersType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    (∀ x : R, x ∈ rightIdeal e ↔ ∃ r : R, e.val * r = x) ∧
    (∀ x : R, x ∈ leftIdeal e ↔ ∃ r : R, r * e.val = x) ∧
    (∀ x : R, x ∈ cornerSubring e ↔ ∃ r : R, e.val * r * e.val = x)

def moduleCornerImageType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R) (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M],
    (moduleCorner (M := M) e : Set M) = Set.range (fun m : M => op e.val • m)

def finiteProjectiveType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    Module.Finite Rᵐᵒᵖ (rightIdeal e) ∧ Module.Projective Rᵐᵒᵖ (rightIdeal e)

def cornerEndomorphismsType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R),
    ∃ φ : Corner e ≃+* Module.End Rᵐᵒᵖ (rightIdeal e),
      (∀ (a : Corner e) (x : rightIdeal e), (φ a x).val = a.val * x.val) ∧
      (∀ f : Module.End Rᵐᵒᵖ (rightIdeal e),
        (φ.symm f).val = (f (rightGenerator e)).val)

end CornerSpec
end RM03.Morita
