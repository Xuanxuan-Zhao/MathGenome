import MathGenome.Internal.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition
import MathGenome.Internal.D07.Ch17.MaschkeProjection
import MathGenome.Internal.Specs.D07.Ch17.CompleteReducibility

/-!
Finite-dimensional complete reducibility (paper.tex:4852–4861).
Maschke gives invariant complements, and the finite-dimensional
semisimplicity theorem gives irreducible summands. The canonical addition
map identifies their external sum equivariantly with the original space.
-/
namespace D07.Ch17.CompleteReducibility

universe u v w

open Specs.D07.Ch17.CompleteReducibility

theorem semisimplicity : Semisimplicity.{u, v, w} := by
  intro K G V _ _ _ _ _ hm ρ U
  obtain ⟨W, hW, hc⟩ := MaschkeProjection.invariant_complement K G V hm ρ
    U.toSubmodule (fun g _ hx => U.apply_mem_toSubmodule g hx)
  exact ⟨⟨W, fun g _ hx => hW g _ hx⟩, hc⟩

theorem internal_decomposition : InternalDecomposition.{u, v, w} := by
  intro K G V _ _ _ _ _ _ hm ρ
  obtain ⟨n, U, hU, hi⟩ :=
    (IrreducibleDefinitionFiniteSemisimpleDecomposition.finite_semisimple_decomposition
      K G V ρ).mp (semisimplicity K G V hm ρ)
  exact ⟨n, U, fun i =>
    (IrreducibleDefinitionFiniteSemisimpleDecomposition.atom_iff_irreducible (U i)).mp
      (hU i), hi⟩

theorem equivariant_decomposition : EquivariantDecomposition.{u, v, w} := by
  intro K G V _ _ _ _ _ _ hm ρ
  exact IrreducibleDefinitionFiniteSemisimpleDecomposition.equivariant_decomposition
    K G V ρ (semisimplicity K G V hm ρ)

theorem empty_decomposition : EmptyDecomposition.{u, v, w} := by
  intro K G V _ _ _ _ _ ρ
  obtain ⟨U, _, hi⟩ :=
    (IrreducibleDefinitionFiniteSemisimpleDecomposition.zero_space K G V ρ).2
  let e := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun i => (U i).toSubmodule)) hi
  refine ⟨U, Representation.Equiv.mk e ?_, fun i => Fin.elim0 i, hi, fun _ => rfl⟩
  intro g
  exact LinearMap.ext
    ((IrreducibleDefinitionFiniteSemisimpleDecomposition.addition_intertwining U).isIntertwining g)

end D07.Ch17.CompleteReducibility
