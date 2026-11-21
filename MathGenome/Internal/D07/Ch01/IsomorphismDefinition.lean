import MathGenome.Internal.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch01.IsomorphismDefinition

/-!
Isomorphisms and their inverses (`K07.01.isomorphism_definition`).
All group structures are arbitrary; no finiteness, commutativity, or
nontriviality hypothesis is imposed. Carriers may inhabit different universes.
-/

namespace D07.Ch01.IsomorphismDefinition

universe u v w

/-- The canonical bundled group isomorphism. -/
abbrev GroupIso (G : Type u) (H : Type v) [Group G] [Group H] :
    Type (max u v) := G ≃* H

/-- A homomorphism is an isomorphism exactly when it is bijective. -/
def IsIsomorphism (G : Type u) (H : Type v) [Group G] [Group H]
    (f : HomomorphismDefinition.GroupHom G H) : Prop := Function.Bijective f

/-- Existence of an isomorphism, the assertion denoted by `G ≅ H`. -/
def Isomorphic (G : Type u) (H : Type v) [Group G] [Group H] : Prop :=
  Nonempty (GroupIso G H)

theorem isomorphism_iff_bundled (G : Type u) (H : Type v) [Group G] [Group H]
    (f : HomomorphismDefinition.GroupHom G H) :
    IsIsomorphism G H f ↔ ∃ e : GroupIso G H, e.toMonoidHom = f := by
  constructor
  · intro hf
    exact ⟨MulEquiv.ofBijective f hf, MonoidHom.ext (fun _ => rfl)⟩
  · rintro ⟨e, he⟩
    change Function.Bijective f
    rw [← he]
    exact e.bijective

theorem isomorphism_iff_homomorphic_inverse (G : Type u) (H : Type v)
    [Group G] [Group H] (f : HomomorphismDefinition.GroupHom G H) :
    IsIsomorphism G H f ↔
      ∃ g : HomomorphismDefinition.GroupHom H G,
        (∀ x : G, g (f x) = x) ∧ (∀ y : H, f (g y) = y) := by
  constructor
  · intro hf
    let e : GroupIso G H := MulEquiv.ofBijective f hf
    exact ⟨e.symm.toMonoidHom, e.symm_apply_apply, e.apply_symm_apply⟩
  · rintro ⟨g, hleft, hright⟩
    constructor
    · intro x y hxy
      calc
        x = g (f x) := (hleft x).symm
        _ = g (f y) := congrArg g hxy
        _ = y := hleft y
    · intro y
      exact ⟨g y, hright y⟩

theorem isomorphic_iff_bijective_hom (G : Type u) (H : Type v)
    [Group G] [Group H] :
    Isomorphic G H ↔
      ∃ f : HomomorphismDefinition.GroupHom G H, Function.Bijective f := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toMonoidHom, e.bijective⟩
  · rintro ⟨f, hf⟩
    exact ⟨MulEquiv.ofBijective f hf⟩

theorem isomorphic_refl (G : Type u) [Group G] : Isomorphic G G :=
  ⟨MulEquiv.refl G⟩

theorem isomorphic_symm (G : Type u) (H : Type v) [Group G] [Group H]
    (h : Isomorphic G H) : Isomorphic H G := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem isomorphic_trans (G : Type u) (H : Type v) (K : Type w)
    [Group G] [Group H] [Group K] (hGH : Isomorphic G H) (hHK : Isomorphic H K) :
    Isomorphic G K := by
  rcases hGH with ⟨e⟩
  rcases hHK with ⟨d⟩
  exact ⟨e.trans d⟩

end D07.Ch01.IsomorphismDefinition
