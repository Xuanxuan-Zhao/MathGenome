import MathGenome.Internal.Specs.D07.Ch15.ExplicitS5Quintic
import MathGenome.Internal.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
import MathGenome.Internal.D07.Ch15.RadicalsImplySolvable
import MathGenome.Internal.D07.Ch15.SolvableGroups

/-!
The prerequisite identifies the Galois group of X^5 - 6X + 3 with S₅.
Transporting solvability along this isomorphism would contradict the
nonsolvability of S₅. Since this polynomial is irreducible, a single root in
a finite radical tower would force its Galois group to be solvable. Thus no
root in any specified algebraic overfield is expressible by radicals over ℚ.
-/

universe u

namespace D07.Ch15.ExplicitS5Quintic

open Specs.D07.Ch15.ExplicitS5Quintic
open Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup (quintic)

theorem galois_group_S5 : GaloisGroupS5 :=
  ExplicitS5QuinticQuinticRealRootsAndGroup.galois_group_S5

theorem galois_group_not_solvable : GaloisGroupNotSolvable := by
  intro h
  obtain ⟨e⟩ := galois_group_S5
  let : Group.IsSolvable quintic.Gal := h
  exact SolvableGroups.symmetric_five_not_solvable
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem no_radical_root : NoRadicalRoot.{u} := by
  intro Ω _ _ _ a ha hrad
  exact galois_group_not_solvable
    (RadicalsImplySolvable.irreducible_radical_root_group ℚ Ω quintic a
      ExplicitS5QuinticQuinticRealRootsAndGroup.irreducibility ha hrad)

theorem explicit_S5_quintic : FullConclusion.{u} :=
  ⟨galois_group_S5, no_radical_root⟩

end D07.Ch15.ExplicitS5Quintic
