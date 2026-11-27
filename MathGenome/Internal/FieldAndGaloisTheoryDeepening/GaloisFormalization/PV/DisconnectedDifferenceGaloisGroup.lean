import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.DisconnectedDifferenceRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.DisconnectedDifferenceGaloisGroup
import Mathlib.Topology.Connected.Clopen

import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
namespace GaloisFormalization.PV.DisconnectedDifference

open scoped Matrix MatrixGroupCoordinates.Specs
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates.Specs (CoordinatePolynomial evalAt evaluationPrime)

universe u

private noncomputable def swapAutomorphism {C : Type u} [Field C] (q : Cˣ) :
    Specs.operatorAutomorphisms (RatFunc C) (Specs.DisconnectedDifference.productOperator q) :=
  ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl), fun _ => rfl⟩

private theorem rankOne_ext {A : Type*} [CommRing A] {g h : GL (Fin 1) A}
    (he : g 0 0 = h 0 0) : g = h :=
  GeneralLinearGroup.ext fun i j => by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact he

private theorem rankOne_mul_entry {A : Type*} [CommRing A] (g h : GL (Fin 1) A) :
    (g * h) 0 0 = g 0 0 * h 0 0 := by
  change ((g : Matrix (Fin 1) (Fin 1) A) * (h : Matrix (Fin 1) (Fin 1) A)) 0 0 = _
  rw [Matrix.mul_apply, Fin.sum_univ_one]

private theorem rankOne_one_entry {A : Type*} [CommRing A] :
    (1 : GL (Fin 1) A) 0 0 = 1 := Matrix.one_apply_eq _

private theorem rankOne_neg_one_entry {A : Type*} [CommRing A] :
    (-1 : GL (Fin 1) A) 0 0 = -1 := by
  change -((1 : GL (Fin 1) A) 0 0) = -1
  rw [rankOne_one_entry]

private theorem rankOne_isClosed_singleton {A : Type*} [Field A] (a : GL (Fin 1) A) :
    IsClosed ({a} : Set (GL (Fin 1) A)) := by
  let p : CoordinatePolynomial A 1 := MvPolynomial.X (Sum.inl (0, 0)) - MvPolynomial.C (a 0 0)
  rw [isClosed_induced_iff]
  refine ⟨PrimeSpectrum.zeroLocus {p}, PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
  ext g
  rw [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    Set.mem_singleton_iff]
  change (evalAt (C := A) g p = 0) ↔ g = a
  have hp : evalAt (C := A) g p = g 0 0 - a 0 0 := by
    simp [p, evalAt]
  rw [hp, sub_eq_zero]
  exact ⟨rankOne_ext, fun h => h ▸ rfl⟩

private theorem rankOne_two_point_disconnected {A : Type*} [Field A] [CharZero A]
    (G : Subgroup (GL (Fin 1) A)) (hm : ∀ g, g ∈ G ↔ g = 1 ∨ g = -1) :
    ¬ ConnectedSpace G := by
  let p : G := 1
  let m : G := ⟨-1, (hm _).2 (Or.inr rfl)⟩
  have hpm : p ≠ m := by
    intro h
    have he := congrArg (fun g : G => g.val 0 0) h
    change (1 : GL (Fin 1) A) 0 0 = (-1 : GL (Fin 1) A) 0 0 at he
    rw [rankOne_one_entry, rankOne_neg_one_entry] at he
    exact one_ne_zero (CharZero.neg_eq_self_iff.mp he.symm)
  have hclosed (g : G) : IsClosed ({g} : Set G) := by
    convert (rankOne_isClosed_singleton g.val).preimage
      (continuous_subtype_val : Continuous (Subtype.val : G → GL (Fin 1) A)) using 1
    ext x
    exact ⟨fun h => congrArg Subtype.val h, Subtype.ext⟩
  have hcompl : ({p} : Set G)ᶜ = {m} := by
    ext g
    change g ≠ p ↔ g = m
    constructor
    · intro h
      rcases (hm _).1 g.property with hg | hg
      · exact (h (Subtype.ext hg)).elim
      · exact Subtype.ext hg
    · rintro rfl
      exact hpm.symm
  have hclopen : IsClopen ({p} : Set G) :=
    ⟨hclosed p, isClosed_compl_iff.mp (hcompl ▸ hclosed m)⟩
  intro hc
  rcases (connectedSpace_iff_clopen.mp hc).2 _ hclopen with h | h
  · have hp : p ∈ ({p} : Set G) := rfl
    rw [h] at hp
    exact hp
  · have hmem : m ∈ ({p} : Set G) := h.symm ▸ Set.mem_univ m
    exact hpm.symm hmem

/-- The two constant multipliers and their action for the disconnected difference example. -/
theorem disconnectedGaloisGroup_conditional
    (_ : Specs.galoisChangeFundamentalMatrix.{u, u})
    (_ : Specs.galoisCoordinateAlgebra.{u, u})
    (_ : Specs.galoisEvaluation.{u, u})
    (ringAction : Specs.galoisRingAction.{u, u})
    (_ : Specs.galoisTotalRingAction.{u, u}) :
    Specs.DisconnectedDifference.disconnectedGaloisGroup.{u} := by
  intro C _ _ _ q hq
  let k := RatFunc C
  let R := Specs.DisconnectedDifference.quotientRing C
  let δ := Specs.rationalDilationOperator q
  let uRoot := Specs.DisconnectedDifference.quotientRoot C
  obtain ⟨hbase, _⟩ := productPicardVessiot q hq
  obtain ⟨E, φ, hcomm, heval, hroot, _, _, hsq, _, hPV, Y, hY, hfund, _⟩ :=
    quotientPresentation q hq
  let G := Specs.matrixGaloisGroup δ E Y
  let constMap : Specs.constantSubfield δ →+* R :=
    (algebraMap k R).comp (Specs.constantSubfield δ).subtype
  have hconst : Function.Injective constMap := by
    intro a b hab
    apply Subtype.ext
    have hf := congrArg (fun x : R => (φ x).1) hab
    change (φ (algebraMap k R (a : k))).1 = (φ (algebraMap k R (b : k))).1 at hf
    rw [φ.commutes, φ.commutes] at hf
    exact hf
  let swap := (φ.trans (swapAutomorphism q).val).trans φ.symm
  have hswap_apply (x : R) : φ (swap x) = (φ x).swap := φ.apply_symm_apply _
  have hφ (x : R) : φ (Specs.apply E x) =
      Specs.apply (Specs.DisconnectedDifference.productOperator q) (φ x) := hcomm x
  have hswap_comm : Specs.commutes E E swap := by
    intro x
    apply φ.injective
    rw [hswap_apply, hφ x, hφ (swap x), hswap_apply]
    exact (swapAutomorphism q).property (φ x)
  let s : Specs.operatorAutomorphisms k E := ⟨swap, hswap_comm⟩
  have hswap_root : swap uRoot = -uRoot := by
    apply φ.injective
    rw [hswap_apply, map_neg, hroot]
    exact Prod.ext rfl (neg_neg (1 : k)).symm
  obtain ⟨e, he, huniq⟩ :=
    ringAction δ (Specs.DisconnectedDifference.negativeSystem C) E Y hbase hPV hfund
  have hswap : GeneralLinearGroup.map s.val.toRingHom Y =
      Y * GeneralLinearGroup.map constMap (-1 : GL (Fin 1) (Specs.constantSubfield δ)) := by
    apply rankOne_ext
    rw [GeneralLinearGroup.map_apply, rankOne_mul_entry, GeneralLinearGroup.map_apply,
      rankOne_neg_one_entry, map_neg, map_one, mul_neg_one]
    change swap (Y.val 0 0) = -(Y.val 0 0)
    rw [hY]
    exact hswap_root
  have hmem (g : GL (Fin 1) (Specs.constantSubfield δ)) :
      g ∈ G ↔ g = 1 ∨ g = -1 := by
    constructor
    · rintro ⟨τ, hτ⟩
      have h := congrArg (fun Z : GL (Fin 1) R => Z 0 0) hτ
      change (GeneralLinearGroup.map τ.val.toRingHom Y) 0 0 =
        (Y * GeneralLinearGroup.map constMap g) 0 0 at h
      rw [GeneralLinearGroup.map_apply, rankOne_mul_entry, GeneralLinearGroup.map_apply] at h
      have hu : (Y 0 0) ^ 2 = 1 := by
        rw [hY]
        exact hsq
      have hsquare : (constMap (g 0 0)) ^ 2 = 1 := by
        have hh := congrArg (fun z : R => z ^ 2) h
        change (τ.val (Y 0 0)) ^ 2 = _ at hh
        rw [← map_pow, hu, map_one, mul_pow, hu, one_mul] at hh
        exact hh.symm
      have hsquare' : (g 0 0) ^ 2 = 1 := by
        apply hconst
        rwa [map_pow, map_one]
      rcases (sq_eq_one_iff.mp hsquare') with hg | hg
      · exact Or.inl (rankOne_ext (hg.trans rankOne_one_entry.symm))
      · exact Or.inr (rankOne_ext (hg.trans rankOne_neg_one_entry.symm))
    · rintro (rfl | rfl)
      · exact G.one_mem
      · exact ⟨s, hswap⟩
  have hpos (g : G) (hg : g.val = 1) : ∀ x : R,
      (Specs.matrixAutomorphism δ E Y g).val x = x := by
    have heg : e g = 1 := (huniq g 1).2 (by
      change GeneralLinearGroup.map (RingHom.id R) Y = Y * GeneralLinearGroup.map constMap g.val
      rw [hg]
      simp)
    rw [he] at heg
    rw [heg]
    exact fun _ => rfl
  have hneg (g : G) (hg : g.val = -1) : ∀ x : R,
      (Specs.matrixAutomorphism δ E Y g).val x = swap x := by
    have heg : e g = s := (huniq g s).2 (by
      change GeneralLinearGroup.map s.val.toRingHom Y = Y * GeneralLinearGroup.map constMap g.val
      rw [hg]
      exact hswap)
    rw [he] at heg
    rw [heg]
    exact fun _ => rfl
  have hfixed (x : R) :
      (∀ g : G, (Specs.matrixAutomorphism δ E Y g).val x = x) ↔
        x ∈ Set.range (algebraMap k R) := by
    constructor
    · intro hx
      let m : G := ⟨-1, (hmem _).2 (Or.inr rfl)⟩
      have h := (hswap_apply x).symm.trans (congrArg φ ((hneg m rfl x).symm.trans (hx m)))
      refine ⟨(φ x).1, φ.injective ?_⟩
      rw [φ.commutes]
      exact Prod.ext rfl (congrArg Prod.fst h).symm
    · rintro ⟨a, rfl⟩ g
      exact (Specs.matrixAutomorphism δ E Y g).val.commutes a
  refine ⟨E, φ, Y, hcomm, heval, hY, hfund, hmem, ?_, hfixed, ?_,
    rankOne_two_point_disconnected G hmem⟩
  · intro g
    exact ⟨hpos g, fun hg =>
      ⟨fun x => (congrArg φ (hneg g hg x)).trans (hswap_apply x),
        (hneg g hg uRoot).trans hswap_root⟩⟩
  · let Q := Specs.totalQuotientRing R
    let ι := algebraMap R Q
    obtain ⟨hi, hs⟩ := quotientTotal C
    have hfrac (g : G) (x : R) :
        Specs.matrixFractionAutomorphism δ E Y g (ι x) =
          ι ((Specs.matrixAutomorphism δ E Y g).val x) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (Specs.matrixAutomorphism δ E Y g).val.toRingEquiv x
    intro z
    obtain ⟨x, rfl⟩ := hs z
    change (∀ g : G, Specs.matrixFractionAutomorphism δ E Y g (ι x) = ι x) ↔
      ι x ∈ Set.range (ι.comp (algebraMap k R))
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := (hfixed x).1 fun g => hi ((hfrac g x).symm.trans (hz g))
      exact ⟨a, congrArg ι ha⟩
    · rintro ⟨a, ha⟩ g
      have hx := (hfixed x).2 ⟨a, hi ha⟩ g
      exact (hfrac g x).trans (congrArg ι hx)

end GaloisFormalization.PV.DisconnectedDifference

universe v8_closure_2551d6ea9f0f70e4_u0
theorem _root_.«GaloisFormalization».«PV».«DisconnectedDifference».«disconnectedGaloisGroup» : _root_.«GaloisFormalization».«PV».«Specs».«DisconnectedDifference».«disconnectedGaloisGroup».{v8_closure_2551d6ea9f0f70e4_u0} :=
  @_root_.«GaloisFormalization».«PV».«DisconnectedDifference».«disconnectedGaloisGroup_conditional».{v8_closure_2551d6ea9f0f70e4_u0} (@_root_.«GaloisFormalization».«PV».«galoisChangeFundamentalMatrix».{v8_closure_2551d6ea9f0f70e4_u0, v8_closure_2551d6ea9f0f70e4_u0}) (@_root_.«GaloisFormalization».«PV».«galoisCoordinateAlgebra».{v8_closure_2551d6ea9f0f70e4_u0, v8_closure_2551d6ea9f0f70e4_u0}) (@_root_.«GaloisFormalization».«PV».«galoisEvaluation».{v8_closure_2551d6ea9f0f70e4_u0, v8_closure_2551d6ea9f0f70e4_u0}) (@_root_.«GaloisFormalization».«PV».«galoisRingAction».{v8_closure_2551d6ea9f0f70e4_u0, v8_closure_2551d6ea9f0f70e4_u0}) (@_root_.«GaloisFormalization».«PV».«galoisTotalRingAction».{v8_closure_2551d6ea9f0f70e4_u0, v8_closure_2551d6ea9f0f70e4_u0})
