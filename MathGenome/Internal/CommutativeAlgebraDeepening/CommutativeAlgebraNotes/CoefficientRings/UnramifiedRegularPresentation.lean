import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.UnramifiedRegularPresentation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingMap
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open scoped nonZeroDivisors

private theorem exists_maximalIdeal_generators_containing
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {d : ℕ} (hd : ringKrullDim R = (d : WithBot ℕ∞)) (a : maximalIdeal R)
    (ha : (a : R) ∉ maximalIdeal R ^ 2) :
    0 < d ∧ ∃ x : Fin (d - 1) → maximalIdeal R,
      Ideal.span (insert (a : R) (Set.range fun i => (x i : R))) = maximalIdeal R := by
  classical
  let m := maximalIdeal R
  let k := ResidueField R
  let v := m.toCotangent a
  have hv : v ≠ 0 := fun h => ha ((m.toCotangent_eq_zero a).mp h)
  have hvind : LinearIndepOn k id {v} := LinearIndepOn.singleton hv
  let ι := hvind.extend (Set.subset_univ _)
  let b : Module.Basis ι k (CotangentSpace R) := Module.Basis.extend hvind
  let j : ι := ⟨v, Module.Basis.subset_extend hvind (Set.mem_singleton v)⟩
  have hj : b j = v := Module.Basis.extend_apply_self hvind j
  have : Finite ι := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  have dim_eq : Module.finrank k (CotangentSpace R) = d := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := R)).mp inferInstance
    rw [hd] at h
    exact_mod_cast h
  have card_eq : Fintype.card ι = d := (Module.finrank_eq_card_basis b).symm.trans dim_eq
  have : Nonempty ι := ⟨j⟩
  have hdpos : 0 < d := card_eq ▸ Fintype.card_pos
  have hsize : (d - 1) + 1 = d := by omega
  -- The designated vector has index `none`, and the remaining indices form `Fin (d - 1)`.
  let e := Fintype.equivFinOfCardEq (card_eq.trans hsize.symm)
  let b' := b.reindex (e.trans (finSuccEquiv' (e j)))
  have hbnone : b' none = v := by simpa [b'] using hj
  choose x hx using fun i : Fin (d - 1) => m.toCotangent_surjective (b' (some i))
  refine ⟨hdpos, x, ?_⟩
  have himage : m.toCotangent '' insert a (Set.range x) = Set.range b' := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with rfl | ⟨i, rfl⟩
      · exact ⟨none, hbnone⟩
      · exact ⟨some i, (hx i).symm⟩
    · rintro ⟨_ | i, rfl⟩
      · exact ⟨a, Set.mem_insert _ _, hbnone.symm⟩
      · exact ⟨x i, Set.mem_insert_of_mem _ (Set.mem_range_self i), hx i⟩
  have hspan : Submodule.span R (insert a (Set.range x)) = ⊤ := by
    apply CotangentSpace.span_image_eq_top_iff.mp
    rw [himage, b'.span_eq]
  have hmap := congrArg (Submodule.map m.subtype) hspan
  rw [Submodule.map_span, Set.image_insert_eq, ← Set.range_comp,
    Submodule.map_top, Submodule.range_subtype, Ideal.submodule_span_eq] at hmap
  exact hmap

/-- A complete unramified regular local ring in mixed characteristic is a
power-series ring over a Cohen DVR, compatibly with reduction to the residue field. -/
theorem unramifiedRegularPresentation : Specs.unramifiedRegularPresentationType := by
  intro R _ _ _ _ p d hp _ hd hunram
  have : Fact p.Prime := ⟨hp⟩
  have hpR : (p : R) ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [map_natCast] using CharP.cast_eq_zero (ResidueField R) p
  obtain ⟨hdpos, x, hx⟩ := exists_maximalIdeal_generators_containing hd ⟨p, hpR⟩ hunram
  obtain ⟨Λ, _, _, _, hchar, hcomplete, hgen, ⟨e⟩⟩ :=
    cohenRingExistence p hp (ResidueField R)
  let := hcomplete
  let ep := (Ideal.quotEquivOfEq hgen.symm).trans e
  obtain ⟨φ, hφ, hφcont, hφres, -, -⟩ :=
    cohenRingMap R Λ p hgen.symm ep
  let := hφ
  have hφresidue (a : Λ) : residue R (φ a) = e (residue Λ a) := by
    have heq := DFunLike.congr_fun hφres a
    change residue R (φ a) = ep (Ideal.Quotient.mk _ a) at heq
    exact heq
  have hφmap : ResidueField.map φ = e.toRingHom := by
    ext z
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact hφresidue a
  let s := d - 1
  let S := MvPowerSeries (Fin s) Λ
  have hpΛ : Irreducible (p : Λ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hgen
  obtain ⟨hdom, hreg, hcomp, -, hdim, -, -, -⟩ :=
    CompleteRegularPowerSeries.overCompleteDVR Λ (p : Λ) hpΛ s
  have : IsDomain S := hdom
  have : IsRegularLocalRing S := hreg
  have : IsAdicComplete (maximalIdeal S) S := hcomp
  obtain ⟨F, hF, -, hC, -, hFres, hFresidue, hFmap⟩ :=
    PowerSeriesEvaluation.evaluation Λ R φ (hφmap.symm ▸ e.bijective) s
      (fun i => (x i : R)) (fun i => (x i).property)
  let := hF
  have hmax : (maximalIdeal S).map F = maximalIdeal R := by
    rw [hFmap, hgen, Ideal.map_span, Set.image_singleton, map_natCast,
      ← Ideal.span_insert]
    exact hx
  let : Algebra S R := F.toAlgebra
  have hsurj : Function.Surjective F :=
    surjectiveOfMaximalIdealAndResidue (A := S) (B := R) hmax hFres.2
  have hdimS : ringKrullDim S = (d : WithBot ℕ∞) := by
    change ringKrullDim S = _ at hdim
    have hsize : s + 1 = d := by dsimp [s]; omega
    rwa [hsize] at hdim
  -- A nonzero kernel element in the domain would force a drop in dimension.
  have hinj : Function.Injective F := by
    apply (RingHom.injective_iff_ker_eq_bot F).2
    apply le_antisymm _ bot_le
    intro r hr
    by_contra hne
    have hr₀ : r ≠ 0 := by simpa using hne
    have h := ringKrullDim_succ_le_of_surjective F hsurj
      (mem_nonZeroDivisors_of_ne_zero hr₀) (RingHom.mem_ker.mp hr)
    rw [hd, hdimS, ← Nat.cast_one, ← Nat.cast_add] at h
    exact (Nat.not_succ_le_self d) (by exact_mod_cast h)
  let E := RingEquiv.ofBijective F ⟨hinj, hsurj⟩
  refine ⟨hdpos, Λ, inferInstance, inferInstance, inferInstance, hchar, hcomplete,
    hgen, e, φ, hφ, hφcont, hφresidue, E, hC, ?_⟩
  intro f
  change residue R (F f) = _
  simpa only [ResidueField.map_residue, hφresidue] using hFresidue f

end CommutativeAlgebraNotes.CoefficientRings
