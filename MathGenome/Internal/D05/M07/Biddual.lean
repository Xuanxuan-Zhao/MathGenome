import MathGenome.Internal.Specs.D05.M07.Biddual
import MathGenome.Internal.D05.M07.DualBasis
import MathGenome.Internal.D05.M03.EqualDimension

/-! K05.07.biddual: canonical evaluation, finite biduality, and naturality. -/

namespace D05.M07.Biddual

/-- This map uses no basis or finite-dimensional hypothesis. Both linearities
are bundled in the existing evaluation map on algebraic duals. -/
abbrev evaluation (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    V →ₗ[K] Module.Dual K (Module.Dual K V) :=
  Module.Dual.eval K V

theorem evaluation_apply : Specs.D05.M07.Biddual.evaluation_apply := by
  intro K V _ _ _ x f
  rfl

theorem evaluation_unique : Specs.D05.M07.Biddual.evaluation_unique := by
  intro K V _ _ _ J hJ
  ext x f
  exact hJ x f

/-- Test equality on the coordinate functionals of a finite basis. This proof
is independent of the unrestricted choice-based variant below. -/
theorem evaluation_injective_finite : Specs.D05.M07.Biddual.evaluation_injective_finite := by
  intro K V _ _ _ _ x y h
  let b := Module.finBasis K V
  exact b.ext_elem fun i => congrArg (fun F => F (b.coord i)) h

theorem biddual_dimension : Specs.D05.M07.Biddual.biddual_dimension := by
  intro K V _ _ _ _
  obtain ⟨hdual, hdim⟩ := D05.M07.DualBasis.dual_dimension (K := K) (V := V)
  letI := hdual
  obtain ⟨hbidual, hbdim⟩ :=
    D05.M07.DualBasis.dual_dimension (K := K) (V := Module.Dual K V)
  exact ⟨hbidual, hbdim.trans hdim⟩

/-- Expand f in the dual basis and apply F. Commutativity of K matches
F's expansion with evaluation on the proposed preimage. -/
theorem explicit_preimage : Specs.D05.M07.Biddual.explicit_preimage := by
  intro K V I _ _ _ _ b F
  ext f
  change f (∑ i, F (b.coord i) • b i) = F f
  have hF := congrArg (fun g : Module.Dual K V => F g)
    (D05.M07.DualBasis.functional_expansion b f)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using hF.symm

/-- Injectivity and equality of finite dimensions imply surjectivity.
The explicit_preimage theorem gives the independent coordinate description. -/
theorem evaluation_bijective : Specs.D05.M07.Biddual.evaluation_bijective := by
  intro K V _ _ _ _
  obtain ⟨hfinite, hdim⟩ := biddual_dimension (K := K) (V := V)
  letI := hfinite
  have hinj := evaluation_injective_finite (K := K) (V := V)
  exact ⟨hinj, (D05.M03.EqualDimension.equal_dimension
    (Module.Dual.eval K V) hdim.symm).1.mp hinj⟩

/-- Bundle the proved bijection, retaining its evaluation formula. -/
theorem canonical_isomorphism : Specs.D05.M07.Biddual.canonical_isomorphism := by
  intro K V _ _ _ _
  let e := LinearEquiv.ofBijective (Module.Dual.eval K V)
    (evaluation_bijective (K := K) (V := V))
  refine ⟨e, fun _ _ => rfl, ?_⟩
  intro e' he'
  apply LinearEquiv.toLinearMap_injective
  exact evaluation_unique e'.toLinearMap he'

theorem inverse_formula : Specs.D05.M07.Biddual.inverse_formula := by
  intro K V I _ _ _ _ b e he F
  apply e.injective
  rw [e.apply_symm_apply]
  have hmap := evaluation_unique e.toLinearMap he
  change F = e.toLinearMap (∑ i, F (b.coord i) • b i)
  rw [hmap, explicit_preimage b F]

/-- On x and f, both sides are exactly f(Tx). -/
theorem naturality : Specs.D05.M07.Biddual.naturality := by
  intro K V W _ _ _ _ _ T
  ext x f
  rfl

/-- Choosing a basis here uses classical unrestricted basis extension (Zorn).
No surjectivity or finite-dimensional assumption is made in this variant. -/
theorem evaluation_injective : Specs.D05.M07.Biddual.evaluation_injective := by
  intro K V _ _ _
  exact (Module.Free.chooseBasis K V).eval_injective

end D05.M07.Biddual
