import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.Specs.D07.Ch01.HomomorphismDefinition

/-!
Homomorphisms and preservation of identity and inverses, as in
`K07.01.homomorphism_definition`. All groups, including the trivial group,
are allowed, and the source and target may lie in different universes.
-/

namespace D07.Ch01.HomomorphismDefinition

universe u v

/-- A group homomorphism uses the canonical bundled monoid homomorphism. -/
abbrev GroupHom (G : Type u) (H : Type v) [Group G] [Group H] :
    Type (max u v) := G →* H

/-- The source definition for an ordinary, unbundled function. -/
def IsMultiplicative (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G → H) : Prop := ∀ x y : G, f (x * y) = f x * f y

theorem hom_multiplicative (G : Type u) (H : Type v) [Group G] [Group H]
    (f : GroupHom G H) : IsMultiplicative G H f :=
  fun x y => f.map_mul x y

theorem map_one_of_multiplicative (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G → H) (h : IsMultiplicative G H f) : f 1 = 1 := by
  apply ElementaryGroupLaws.left_cancellation H (f 1)
  calc
    f 1 * f 1 = f (1 * 1) := (h 1 1).symm
    _ = f 1 := congrArg f (one_mul 1)
    _ = f 1 * 1 := (mul_one (f 1)).symm

theorem map_inv_of_multiplicative (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G → H) (h : IsMultiplicative G H f) (x : G) :
    f (x⁻¹) = (f x)⁻¹ := by
  have h_one := map_one_of_multiplicative G H f h
  have h_inverse : f x * f (x⁻¹) = 1 ∧ f (x⁻¹) * f x = 1 := by
    constructor
    · calc
        f x * f (x⁻¹) = f (x * x⁻¹) := (h x (x⁻¹)).symm
        _ = f 1 := congrArg f (mul_inv_cancel x)
        _ = 1 := h_one
    · calc
        f (x⁻¹) * f x = f (x⁻¹ * x) := (h (x⁻¹) x).symm
        _ = f 1 := congrArg f (inv_mul_cancel x)
        _ = 1 := h_one
  exact (ElementaryGroupLaws.inverse_unique H (f x)).unique h_inverse
    ⟨mul_inv_cancel (f x), inv_mul_cancel (f x)⟩

theorem multiplicative_iff_bundled (G : Type u) (H : Type v)
    [Group G] [Group H] (f : G → H) :
    IsMultiplicative G H f ↔ ∃ F : GroupHom G H, (F : G → H) = f := by
  constructor
  · intro h
    let F : GroupHom G H :=
      { toFun := f
        map_mul' := h
        map_one' := map_one_of_multiplicative G H f h }
    exact ⟨F, rfl⟩
  · rintro ⟨F, rfl⟩
    exact hom_multiplicative G H F

/-- The source's monoid caveat: the constant-zero map on the multiplicative
monoid of natural numbers preserves products but does not preserve one. -/
theorem monoid_counterexample :
    ∃ f : ℕ → ℕ, (∀ x y : ℕ, f (x * y) = f x * f y) ∧ f 1 ≠ 1 :=
  ⟨fun _ => 0, (fun _ _ => (Nat.zero_mul 0).symm), Nat.zero_ne_one⟩

end D07.Ch01.HomomorphismDefinition
