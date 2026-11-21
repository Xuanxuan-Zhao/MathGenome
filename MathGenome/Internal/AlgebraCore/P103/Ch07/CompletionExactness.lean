import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionExactness
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Finiteness.Small

/-! Completion preserves short exact sequences of finite modules.
Mathlib proves exactness directly by Artin–Rees and compatible Cauchy lifts,
so no additional inverse-limit exactness hypothesis is needed.
-/

universe u v w z v' w' z'

namespace P103.Ch07.CompletionExactness

/-- Transport short exactness along an isomorphism of sequences. -/
private theorem transport_short_exact
    {R : Type u} [CommRing R]
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    {C : Type z} [AddCommGroup C] [Module R C]
    {A' : Type v'} [AddCommGroup A'] [Module R A']
    {B' : Type w'} [AddCommGroup B'] [Module R B']
    {C' : Type z'} [AddCommGroup C'] [Module R C']
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'}
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hg : g'.comp eB.toLinearMap = eC.toLinearMap.comp g)
    (h : Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g) :
    Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g' := by
  have hf_apply (a : A) : f' (eA a) = eB (f a) := DFunLike.congr_fun hf a
  have hg_apply (b : B) : g' (eB b) = eC (g b) := DFunLike.congr_fun hg b
  refine ⟨?_, Function.Exact.of_ladder_linearEquiv_of_exact hf hg h.2.1, ?_⟩
  · intro a₁ a₂ ha
    obtain ⟨x₁, rfl⟩ := eA.surjective a₁
    obtain ⟨x₂, rfl⟩ := eA.surjective a₂
    exact congrArg eA (h.1 (eB.injective (by simpa only [hf_apply] using ha)))
  · intro c
    obtain ⟨x, rfl⟩ := eC.surjective c
    obtain ⟨b, rfl⟩ := h.2.2 x
    exact ⟨eB b, hg_apply b⟩

/-- Theorem 7.4, exactness part, for the shared canonical completion maps.
The library exactness theorem puts all modules in the ring's universe.
Finite modules are small in that universe; shrinking them and transporting
along the induced completion equivalences removes that representation
restriction without adding any mathematical assumption. -/
theorem short_exact : P103.Specs.Ch07.CompletionExactness.short_exactType.{u, v, w, z} := by
  intro R _ _ I A _ _ _ B _ _ _ C _ _ _ f g hf hfg hg
  let : Small.{u} A := Module.Finite.small R A
  let : Small.{u} B := Module.Finite.small R B
  let : Small.{u} C := Module.Finite.small R C
  let eA := Shrink.linearEquiv.{u} R A
  let eB := Shrink.linearEquiv.{u} R B
  let eC := Shrink.linearEquiv.{u} R C
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  let g' := eC.symm.toLinearMap.comp (g.comp eB.toLinearMap)
  have hf' : f.comp eA.toLinearMap = eB.toLinearMap.comp f' := by
    ext x
    simp [f']
  have hg' : g.comp eB.toLinearMap = eC.toLinearMap.comp g' := by
    ext x
    simp [g']
  have hsmall : Function.Injective f' ∧ Function.Exact f' g' ∧
      Function.Surjective g' :=
    transport_short_exact eA.symm eB.symm eC.symm
      (by ext x; simp [f']) (by ext x; simp [g']) ⟨hf, hfg, hg⟩
  have hcomplete : Function.Injective (AdicCompletion.map I f') ∧
      Function.Exact (AdicCompletion.map I f') (AdicCompletion.map I g') ∧
      Function.Surjective (AdicCompletion.map I g') :=
    ⟨AdicCompletion.map_injective I hsmall.1,
      AdicCompletion.map_exact hsmall.1 hsmall.2.1 hsmall.2.2,
      AdicCompletion.map_surjective I hsmall.2.2⟩
  apply transport_short_exact (AdicCompletion.congr I eA)
    (AdicCompletion.congr I eB) (AdicCompletion.congr I eC) _ _ hcomplete
  · change (AdicCompletion.map I f).comp (AdicCompletion.map I eA.toLinearMap) =
      (AdicCompletion.map I eB.toLinearMap).comp (AdicCompletion.map I f')
    rw [AdicCompletion.map_comp, AdicCompletion.map_comp, hf']
  · change (AdicCompletion.map I g).comp (AdicCompletion.map I eB.toLinearMap) =
      (AdicCompletion.map I eC.toLinearMap).comp (AdicCompletion.map I g')
    rw [AdicCompletion.map_comp, AdicCompletion.map_comp, hg']

end P103.Ch07.CompletionExactness
