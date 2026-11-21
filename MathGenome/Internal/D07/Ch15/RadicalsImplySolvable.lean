import MathGenome.Internal.Specs.D07.Ch15.RadicalsImplySolvable
import MathGenome.Internal.D07.Ch15.RadicalsImplySolvableNormalRadicalGroup

/-!
Radicals force solvability in arbitrary characteristic.

The upstream tower comparison puts each element of a finite radical tower
in Mathlib's radical-closed intermediate field. Mathlib's characteristic-free
Abel–Ruffini theorem gives the minimal-polynomial and irreducible cases.
For an arbitrary polynomial we induct on its irreducible factorization:
each irreducible factor has a root in the specified closure, that root is a
root of the original polynomial, and multiplication preserves solvability
of polynomial Galois groups. This retains inseparable and repeated factors.
-/

universe u v
namespace D07.Ch15.RadicalsImplySolvable
open Polynomial Specs.D07.Ch15.RadicalDefinition
open Specs.D07.Ch15.RadicalsImplySolvable

theorem radical_mem_solvableByRad
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] {a : Ω}
    (ha : solvableByRadicalsValue K Ω a) : a ∈ solvableByRad K Ω := by
  obtain ⟨E, hE, ha⟩ := ha
  exact RadicalsImplySolvableNormalRadicalGroup.tower_in_solvableByRad K Ω E hE ha

theorem radical_minpoly_group : RadicalMinpolyGroup.{u, v} := by
  intro K Ω _ _ _ _ a ha
  exact isSolvable_gal_minpoly (radical_mem_solvableByRad K Ω ha)

theorem irreducible_radical_root_group : IrreducibleRadicalRootGroup.{u, v} := by
  intro K Ω _ _ _ _ f a hf hroot ha
  exact isSolvable_gal_of_irreducible (radical_mem_solvableByRad K Ω ha) hf hroot

theorem all_radical_roots_group : AllRadicalRootsGroup.{u, v} := by
  intro K Ω _ _ _ _ _ f
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact fun _ => gal_zero_isSolvable
  | unit f hf =>
      intro _
      obtain ⟨c, _, rfl⟩ := Polynomial.isUnit_iff.mp hf
      exact gal_C_isSolvable c
  | mul f q _ hq ih =>
      intro hroots
      have hfgal : Group.IsSolvable f.Gal := ih fun a ha =>
        hroots a (by rw [map_mul, ha, mul_zero])
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (q.map (algebraMap K Ω)) (by
        rw [degree_map]
        exact ne_of_gt (degree_pos_of_irreducible hq))
      have haq : aeval a q = 0 := by
        simpa only [IsRoot.def, eval_map_algebraMap] using ha
      have harad : solvableByRadicalsValue K Ω a :=
        hroots a (by rw [map_mul, haq, zero_mul])
      exact gal_mul_isSolvable (irreducible_radical_root_group K Ω q a hq haq harad) hfgal

end D07.Ch15.RadicalsImplySolvable
