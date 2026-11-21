import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! LA-B05-Radical. All fields are allowed. Finite dimension is used to
ensure that the sum of all solvable ideals is solvable. The radical quotient
has no nonzero solvable ideals by lifting an ideal and applying LA-A02's
solvable-extension theorem. The source definition of semisimplicity is used,
including the zero algebra. -/

universe u v w
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]

/-- The sum of all solvable ideals. -/
def radical : LieIdeal k L := LieAlgebra.radical k L

/-- Semisimplicity as defined in the source: the solvable radical vanishes. -/
def IsSemisimple : Prop := radical k L = ⊥

theorem radical_eq_sum :
    radical k L = sSup {I : LieIdeal k L | LieAlgebra.IsSolvable I} := rfl

theorem radical_solvable [FiniteDimensional k L] :
    LieAlgebra.IsSolvable (radical k L) :=
  LieAlgebra.radicalIsSolvable k L

variable {k L}

theorem solvable_ideal_le_radical (I : LieIdeal k L) (hI : LieAlgebra.IsSolvable I) :
    I ≤ radical k L := le_sSup hI

/-- An extension formulation for a homomorphism, derived from LA-A02 and LA-A01. -/
theorem solvable_of_solvable_kernel {H : Type w} [LieRing H] [LieAlgebra k H]
    (f : L →ₗ⁅k⁆ H) (hker : LieAlgebra.IsSolvable f.ker)
    (hH : LieAlgebra.IsSolvable H) : LieAlgebra.IsSolvable L := by
  have hrange := solvable_subalgebra f.range hH
  have hquot : LieAlgebra.IsSolvable (L ⧸ f.ker) :=
    (LieAlgebra.solvable_iff_equiv_solvable (first_isomorphism f)).mpr hrange
  exact solvable_extension f.ker hker hquot

variable (k L)

theorem quotient_no_solvable_ideal [FiniteDimensional k L]
    (J : LieIdeal k (L ⧸ radical k L)) (hJ : LieAlgebra.IsSolvable J) : J = ⊥ := by
  obtain ⟨q, _, hq, hqker⟩ := quotient_projection (radical k L)
  let P : LieIdeal k L := J.comap q
  let f : P →ₗ⁅k⁆ J :=
    { (q.toLinearMap.comp P.incl.toLinearMap).codRestrict J.toSubmodule
        (fun x => x.property) with
      map_lie' := by intros; apply Subtype.ext; exact q.map_lie _ _ }
  have hker_mem (x : f.ker) : (x.val.val : L) ∈ radical k L := by
    have hx : f x.val = 0 := LieHom.mem_ker.mp x.property
    have hxker : (x.val.val : L) ∈ q.ker := LieHom.mem_ker.mpr
      (congrArg (fun z : J => (z : L ⧸ radical k L)) hx)
    exact (le_of_eq hqker) hxker
  let g : f.ker →ₗ⁅k⁆ radical k L :=
    { (P.incl.toLinearMap.comp f.ker.incl.toLinearMap).codRestrict
        (radical k L).toSubmodule hker_mem with
      map_lie' := by intros; rfl }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : radical k L => (z : L)) hxy
  have hrad : LieAlgebra.IsSolvable (radical k L) := radical_solvable k L
  have hker : LieAlgebra.IsSolvable f.ker := hg.lieAlgebra_isSolvable
  have hP : LieAlgebra.IsSolvable P := solvable_of_solvable_kernel f hker hJ
  have hle : P ≤ radical k L := solvable_ideal_le_radical P hP
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨x, rfl⟩ := hq y
  have hx : x ∈ P := hy
  have hxzero : q x = 0 := LieHom.mem_ker.mp (by rw [hqker]; exact hle hx)
  simpa only [LieSubmodule.mem_bot] using hxzero

theorem semisimple_iff : IsSemisimple k L ↔ radical k L = ⊥ := Iff.rfl

theorem semisimple_iff_no_solvable_ideals :
    IsSemisimple k L ↔ ∀ I : LieIdeal k L, LieAlgebra.IsSolvable I → I = ⊥ := by
  change sSup {I : LieIdeal k L | LieAlgebra.IsSolvable I} = ⊥ ↔ _
  exact sSup_eq_bot

theorem semisimple_of_subsingleton [Subsingleton L] : IsSemisimple k L := by
  apply le_bot_iff.mp
  intro x _
  simpa only [LieSubmodule.mem_bot] using (Subsingleton.elim x 0)

theorem quotient_semisimple [FiniteDimensional k L] :
    IsSemisimple k (L ⧸ radical k L) :=
  (semisimple_iff_no_solvable_ideals k _).mpr (quotient_no_solvable_ideal k L)

end LieAlgebrasAndRepresentations
