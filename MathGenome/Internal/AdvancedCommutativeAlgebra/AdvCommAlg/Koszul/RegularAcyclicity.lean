import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.RegularAcyclicity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Construction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Cone
import Mathlib.Data.List.Induction

/-! RK-07: higher Koszul homology of a weakly regular sequence vanishes.
Induction appends one entry, using the cone long exact sequence. -/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The empty-list complex has zero homology in every positive degree. -/
theorem empty_homology_subsingleton (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology M ([] : List R) q) := by
  have := coefficientComplex_vanish M ([] : List R) q (by simpa using hq)
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨a, ha, rfl⟩ := chainClass_surjective (coefficientComplex M []) q z
  apply (chainClass_eq_zero_iff _ q a ha).mpr
  exact ⟨0, by simpa using (Subsingleton.elim (0 : (coefficientComplex M []).X q) a)⟩

/-- The last regularity condition is injectivity on the preceding H₀. -/
theorem append_homology_zero_injective (x : List R) (y : R)
    (h : RegularSequence.WeaklyRegular M (x ++ [y])) :
    Function.Injective (homologyScalar (coefficientComplex M x) y 0).hom := by
  have hy := (RingTheory.Sequence.isWeaklyRegular_append_iff M x [y]).mp h |>.2
  have hi := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ y).mp hy
  have hi' : Function.Injective (fun z : M ⧸ listSubmodule M x => y • z) := hi
  intro a b hab
  change y • a = y • b at hab
  apply (homologyZeroEquiv M x).injective
  apply hi'
  simpa only [map_smul] using congrArg (homologyZeroEquiv M x) hab

/-- Acyclicity for arbitrary coefficient modules and arbitrary commutative rings. -/
theorem weaklyRegular_acyclic (x : List R)
    (hx : RegularSequence.WeaklyRegular M x) (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology M x q) := by
  induction x using List.reverseRecOn generalizing q with
  | nil => exact empty_homology_subsingleton M q hq
  | append_singleton x y ih =>
    have hx' := (RingTheory.Sequence.isWeaklyRegular_append_iff M x [y]).mp hx |>.1
    obtain ⟨S⟩ := append_long_exact_sequence M x y
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    have : Subsingleton ((coefficientComplex M x).homology (n+1)) :=
      ih hx' (n+1) (by omega)
    have hinj : Function.Injective (homologyScalar (coefficientComplex M x) y n).hom := by
      cases n with
      | zero => exact append_homology_zero_injective M x y hx
      | succ n =>
        have : Subsingleton ((coefficientComplex M x).homology (n+1)) :=
          ih hx' (n+1) (by omega)
        exact fun _ _ _ => Subsingleton.elim _ _
    apply subsingleton_of_forall_eq 0
    intro z
    have hz : (S.projection n).hom z = 0 := by
      apply hinj
      simpa only [map_zero] using (S.exact_projection_multiply n).apply_apply_eq_zero z
    obtain ⟨a, ha⟩ := (S.exact_inclusion_projection n z).mp hz
    rw [← ha, Subsingleton.elim a 0, map_zero]

end AdvCommAlg.Koszul
