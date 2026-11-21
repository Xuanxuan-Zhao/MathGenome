import MathGenome.Internal.Specs.D07.Ch08.RingHomomorphism

/-!
# Unital ring homomorphisms and equivalences

K07.08.ring_homomorphism (paper.tex:1283–1294). The characterization
first checks that `RingHom` represents exactly the source's three laws.
`RingEquiv` then represents bijective homomorphisms, with a two-sided
inverse preserving addition, multiplication, and one. No commutativity or
nontriviality is imposed except in the stated zero-map boundary case.
-/

universe u v w

namespace D07.Ch08.RingHomomorphism

open Specs.D07.Ch08.RingHomomorphism

theorem homomorphismCharacterization : HomomorphismCharacterization.{u, v} := by
  intro R S _ _ f
  constructor
  · intro h
    let φ : R →+* S := RingHom.mk'
      { toFun := f, map_one' := h.map_one, map_mul' := h.map_mul } h.map_add
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.map_add, φ.map_mul, φ.map_one⟩

theorem mapZero : MapZero.{u, v} := by
  intro R S _ _ f
  exact f.map_zero

theorem mapNeg : MapNeg.{u, v} := by
  intro R S _ _ f a
  exact map_neg f a

theorem mapIntegerMultiplesOfOne : MapIntegerMultiplesOfOne.{u, v} := by
  intro R S _ _ f n
  simpa only [map_one] using map_zsmul f n (1 : R)

theorem composition : Composition.{u, v, w} := by
  intro R S T _ _ _ f g hf hg
  exact {
    map_add := fun a b => by
      change g (f (a + b)) = g (f a) + g (f b)
      rw [hf.map_add, hg.map_add]
    map_mul := fun a b => by
      change g (f (a * b)) = g (f a) * g (f b)
      rw [hf.map_mul, hg.map_mul]
    map_one := by
      change g (f 1) = 1
      rw [hf.map_one, hg.map_one] }

theorem isomorphismCharacterization : IsomorphismCharacterization.{u, v} := by
  intro R S _ _ f
  constructor
  · intro hf
    exact ⟨RingEquiv.ofBijective f hf, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.bijective

theorem inverseHomomorphism : InverseHomomorphism.{u, v} := by
  intro R S _ _ f g hleft hright
  let ψ : S →+* R := f.inverse g hleft hright
  exact ⟨ψ.map_add, ψ.map_mul, ψ.map_one⟩

theorem isomorphismInverse : IsomorphismInverse.{u, v} := by
  intro R S _ _ e
  exact ⟨⟨e.symm.map_add, e.symm.map_mul, e.symm.map_one⟩,
    e.symm_apply_apply, e.apply_symm_apply⟩

theorem zeroMapNotUnital : ZeroMapNotUnital.{u, v} := by
  intro R S _ _ _ _ h
  exact zero_ne_one h.map_one

end D07.Ch08.RingHomomorphism
