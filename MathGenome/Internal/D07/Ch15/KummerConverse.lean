import MathGenome.Internal.Specs.D07.Ch15.KummerConverse
import MathGenome.Internal.D07.Ch15.RootsUnity
import Mathlib.FieldTheory.KummerExtension

/-!
K07.15.kummer_converse. The roots-of-unity theorem gives a primitive root
in the algebraic closure. The source's containment hypothesis descends it
to K, preserving its exact order under the injective structure map.
Mathlib's cyclic-extension theorem then constructs the radical generator
using an eigenvector of a generator of the Galois group. Its minimal
polynomial argument uses the independence of field embeddings, and its
fixed-field argument shows that the generator's n-th power lies in K.
If the resulting generator is zero, its generated field is the base, so
replacing it by 1 supplies the required nonzero generator as well.
-/

namespace D07.Ch15.KummerConverse

universe u v

open Specs.D07.Ch15.KummerConverse

theorem cyclic_extension_is_radical : CyclicExtensionIsRadical.{u, v} := by
  intro K L _ _ _ _ _ _ n hdegree hchar hμ
  have hn : 0 < n := hdegree ▸ Module.finrank_pos
  obtain ⟨ζ, hζ⟩ := RootsUnity.primitive_root_exists K (AlgebraicClosure K) n hn hchar
  obtain ⟨a, ha⟩ := hμ ζ hζ.pow_eq_one
  have ha_root : IsPrimitiveRoot a n := by
    rw [← ha] at hζ
    exact hζ.of_map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroots : (primitiveRoots (Module.finrank K L) K).Nonempty := by
    rw [hdegree]
    exact ⟨a, (mem_primitiveRoots hn).mpr ha_root⟩
  obtain ⟨u, hpower, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hroots
  by_cases hu : u = 0
  · refine ⟨1, one_ne_zero, ?_, 1, ?_⟩
    · rw [IntermediateField.adjoin_one]
      simpa only [hu, IntermediateField.adjoin_zero] using hgen
    · simp
  · obtain ⟨b, hb⟩ := hpower
    exact ⟨u, hu, hgen, b, by simpa only [hdegree] using hb.symm⟩

end D07.Ch15.KummerConverse
