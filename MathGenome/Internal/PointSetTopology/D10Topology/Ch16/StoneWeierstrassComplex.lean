import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.StoneWeierstrassComplex
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Complex Stone--Weierstrass, `paper.tex`, chapter 16.

We apply Mathlib's proved compact-domain star-subalgebra theorem. The
conversion below retains exactly the original carrier: its unit comes from
`IsUnital`, scalar constants from scalar closure, and its star closure from
pointwise conjugation invariance. Point separation is transferred explicitly.
Finally the chapter 16 bridge identifies norm closure with uniform closure.
Neither this conversion nor the library theorem requires a nonempty domain.
-/

noncomputable section
open Set
universe u

namespace D10Topology.Ch16

/-- Equip a unital conjugation-invariant complex function algebra with its
star-subalgebra structure, without enlarging its underlying set. -/
def complexStarSubalgebra {X : Type u} [TopologicalSpace X]
    (A : ComplexFunctionAlgebra X) (hunit : IsUnital A)
    (hconj : ConjugationInvariant (A : Set C(X, ℂ))) :
    StarSubalgebra ℂ C(X, ℂ) where
  carrier := A
  zero_mem' := A.zero_mem
  add_mem' := A.add_mem
  one_mem' := hunit
  mul_mem' := A.mul_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact A.smul_mem c hunit
  star_mem' := hconj _

theorem stone_weierstrass_complex_closure :
    Specs.D10Topology.Ch16.StoneWeierstrassComplex.stone_weierstrass_complex_closure := by
  intro X _ _ _ A hunit hsep hconj
  let B := complexStarSubalgebra A hunit hconj
  have hB : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfx⟩ := hsep x y hxy
    exact ⟨f, ⟨f, hf, rfl⟩, hfx⟩
  have hclosure :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hB
  rw [uniformClosure_eq_norm_closure]
  change (B.topologicalClosure : Set C(X, ℂ)) = Set.univ
  rw [hclosure]
  rfl

theorem stone_weierstrass_complex :
    Specs.D10Topology.Ch16.StoneWeierstrassComplex.stone_weierstrass_complex := by
  intro X _ _ _ A hunit hsep hconj f ε hε
  have hf : f ∈ uniformClosure (A : Set C(X, ℂ)) := by
    change f ∈ Specs.D10Topology.Ch16.SupNormAlgebras.uniformClosure (A : Set C(X, ℂ))
    rw [stone_weierstrass_complex_closure A hunit hsep hconj]
    trivial
  exact (mem_uniformClosure_iff (A : Set C(X, ℂ)) f).mp hf ε hε

end D10Topology.Ch16
