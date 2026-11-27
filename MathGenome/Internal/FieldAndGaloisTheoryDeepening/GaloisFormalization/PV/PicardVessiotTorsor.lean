import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeResiduesAndPoints
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.MatrixGroupCoordinates
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

namespace GaloisFormalization.PV

noncomputable section

abbrev operatorAutomorphisms := @Specs.operatorAutomorphisms
abbrev matrixGaloisGroup := @Specs.matrixGaloisGroup
abbrev matrixAutomorphism := @Specs.matrixAutomorphism
abbrev matrixFractionAutomorphism := @Specs.matrixFractionAutomorphism
abbrev tensorRatioRelations := @Specs.tensorRatioRelations

open scoped Matrix TensorProduct nonZeroDivisors
open Matrix (GeneralLinearGroup)
open LinearSystem (determinantInverse)
open Algebra.TensorProduct (includeLeftRingHom includeRight lift)

open private determinantInverse_map matrixGeneratedSubalgebra_le_iff
  matrixGeneratedSubalgebra_mul_le finiteType_of_matrixGenerated
  matrixGeneratedSubalgebra_of_fundamental fundamental_map hasConstantField_of_finiteType from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor
open private constantsIn fixesConstantMatrices map_mul_automorphisms from
  MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

universe u v

set_option backward.isDefEq.respectTransparency false

private theorem mapGL_injective {S T : Type*} [CommRing S] [CommRing T]
    {n : ℕ} (f : S →+* T) (hf : Function.Injective f) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) f) := by
  intro X Y h
  apply Units.ext
  ext i j
  exact hf (congrArg (fun Z : GL (Fin n) T => Z.val i j) h)

section MatrixGeneration

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] {n : ℕ}

/-- A map of a matrix-generated algebra is determined by the image of the matrix. -/
private theorem algHom_eq_of_matrix {Y : GL (Fin n) R}
    (hgen : matrixGeneratedSubalgebra K Y = ⊤) {f g : R →ₐ[K] S}
    (h : GeneralLinearGroup.map f.toRingHom Y = GeneralLinearGroup.map g.toRingHom Y) :
    f = g := by
  apply AlgHom.equalizer_eq_top.mp
  apply top_unique
  rw [← hgen]
  refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ?_, ?_⟩
  · exact congrArg (fun Z : GL (Fin n) S => Z.val i j) h
  · exact (determinantInverse_map f.toRingHom Y).symm.trans
      ((congrArg determinantInverse h).trans (determinantInverse_map g.toRingHom Y))

/-- A base-matrix multiple of an image matrix has all its coordinates in the image algebra. -/
private theorem matrixGeneratedSubalgebra_image_le_range (f : R →ₐ[K] S)
    (Y : GL (Fin n) R) (b : GL (Fin n) K) :
    matrixGeneratedSubalgebra K
      (GeneralLinearGroup.map f.toRingHom Y * GeneralLinearGroup.map (algebraMap K S) b)
      ≤ f.range := by
  apply matrixGeneratedSubalgebra_mul_le
  · refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ⟨Y.val i j, rfl⟩, ?_⟩
    rw [determinantInverse_map]
    exact ⟨_, rfl⟩
  · refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨fun i j => ?_, ?_⟩
    · exact f.range.algebraMap_mem (b.val i j)
    · rw [determinantInverse_map]
      exact f.range.algebraMap_mem _

end MatrixGeneration

section MatrixActions

variable {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
  [Algebra K R] {n : ℕ}
  {δ : OperatorField kind K} {E : Operator kind R} {A : LinearSystem kind K n}

private theorem baseConstantMultiplier {S : Type*} [CommRing S] [Algebra K S]
    {F : Operator kind S} (hk : δ.IsBaseField) (he : δ.IsExtension F)
    (hC : Function.Bijective
      (Operator.RingHom.mapConstants (D := δ) (E := F) ⟨algebraMap K S, he.1⟩))
    {Y W : GL (Fin n) S} (hY : A.IsFundamental F Y) (hW : A.IsFundamental F W) :
    ∃ b : GL (Fin n) δ.constantSubfield,
      W = Y * GeneralLinearGroup.map (constantsIn δ) b := by
  obtain ⟨B, hB, _⟩ := A.fundamentalRightMultiplier δ hk F he Y W hY hW
  let c : δ.constantSubfield ≃+* F.constantSubring :=
    RingEquiv.ofBijective _ hC
  let b := GeneralLinearGroup.map c.symm.toRingHom B
  refine ⟨b, hB.trans ?_⟩
  congr 1
  have hc : (constantsIn δ (R := S)).comp c.symm.toRingHom = F.constantSubring.subtype := by
    ext x
    exact congrArg Subtype.val (c.apply_symm_apply x)
  rw [← hc]
  rfl

private theorem matrixAutomorphism_spec (Y : GL (Fin n) R)
    (g : matrixGaloisGroup δ E Y) :
    GeneralLinearGroup.map (matrixAutomorphism δ E Y g).val.toRingHom Y =
      Y * GeneralLinearGroup.map (constantsIn δ) g.val :=
  Classical.choose_spec g.property

private theorem matrixAutomorphism_eq (Y : GL (Fin n) R)
    (hgen : matrixGeneratedSubalgebra K Y = ⊤) (g : matrixGaloisGroup δ E Y)
    (τ : operatorAutomorphisms K E) :
    matrixAutomorphism δ E Y g = τ ↔
      GeneralLinearGroup.map τ.val.toRingHom Y =
        Y * GeneralLinearGroup.map (constantsIn δ) g.val := by
  constructor
  · rintro rfl
    exact matrixAutomorphism_spec Y g
  · intro h
    apply Subtype.ext
    apply AlgEquiv.coe_toAlgHom_injective
    exact algHom_eq_of_matrix hgen ((matrixAutomorphism_spec Y g).trans h.symm)

/-- The matrix group acts by operator automorphisms, with group multiplication
corresponding to composition in the same order. -/
theorem galoisRingAction : Specs.galoisRingAction.{u, v} := by
  intro kind K _ R _ _ n δ A E Y hk hpv hY
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  let G := matrixGaloisGroup δ E Y
  let α : G → operatorAutomorphisms K E := matrixAutomorphism δ E Y
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv Y hY
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  have hbij : Function.Bijective α := by
    constructor
    · intro g h hEq
      apply Subtype.ext
      apply mapGL_injective (constantsIn δ)
        (hpv.1.2.comp (Operator.constantSubfieldEmbedding_injective δ))
      apply mul_left_cancel (a := Y)
      rw [← matrixAutomorphism_spec Y g, ← matrixAutomorphism_spec Y h]
      exact congrArg (fun τ : operatorAutomorphisms K E =>
        GeneralLinearGroup.map τ.val.toRingHom Y) hEq
    · intro τ
      have hc := Operator.constants_finiteType δ E hk hpv.2.1 hpv.1.1
      obtain ⟨g, hg⟩ := baseConstantMultiplier hk hpv.1 hc hY
        (fundamental_map τ.val.toAlgHom τ.property hY)
      exact ⟨⟨g, ⟨τ, hg⟩⟩, (matrixAutomorphism_eq Y hgen _ τ).2 hg⟩
  let e : G ≃* operatorAutomorphisms K E :=
    { Equiv.ofBijective α hbij with
      map_mul' := fun g h => (matrixAutomorphism_eq Y hgen (g * h) _).2 (by
        change GeneralLinearGroup.map ((α g).val * (α h).val).toRingHom Y =
          Y * GeneralLinearGroup.map (constantsIn δ) (g.val * h.val)
        rw [map_mul_automorphisms, matrixAutomorphism_spec, map_mul,
          matrixAutomorphism_spec, fixesConstantMatrices δ (α g).val h.val, map_mul, mul_assoc]) }
  exact ⟨e, fun _ => rfl, matrixAutomorphism_eq Y hgen⟩

/-- Replacing the fundamental matrix conjugates the matrix of each automorphism. -/
theorem galoisChangeFundamentalMatrix : Specs.galoisChangeFundamentalMatrix.{u, v} := by
  intro kind K _ R _ _ n δ A E Y Y' hk hpv hY hY'
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  change A.IsFundamental E Y' at hY'
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv Y hY
  have hgen' := matrixGeneratedSubalgebra_of_fundamental hk hpv Y' hY'
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  refine ⟨baseConstantMultiplier hk hpv.1
    (Operator.constants_finiteType δ E hk hpv.2.1 hpv.1.1) hY hY', ?_⟩
  intro b hb
  have hconj (g : GL (Fin n) (Specs.constantSubfield δ)) (τ : operatorAutomorphisms K E) :
      GeneralLinearGroup.map τ.val.toRingHom Y' =
          Y' * GeneralLinearGroup.map (constantsIn δ) (b⁻¹ * g * b) ↔
        GeneralLinearGroup.map τ.val.toRingHom Y =
          Y * GeneralLinearGroup.map (constantsIn δ) g := by
    rw [hb, map_mul, fixesConstantMatrices δ τ.val b]
    simp only [map_mul, map_inv]
    let bR := GeneralLinearGroup.map (constantsIn δ (R := R)) b
    let gR := GeneralLinearGroup.map (constantsIn δ (R := R)) g
    change GeneralLinearGroup.map τ.val.toRingHom Y * bR =
      (Y * bR) * ((bR⁻¹ * gR) * bR) ↔ GeneralLinearGroup.map τ.val.toRingHom Y = Y * gR
    have hc : (Y * bR) * ((bR⁻¹ * gR) * bR) = (Y * gR) * bR := by simp [mul_assoc]
    rw [hc, mul_right_cancel_iff]
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · change (∃ τ : operatorAutomorphisms K E, _) ↔ ∃ τ : operatorAutomorphisms K E, _
    exact exists_congr (hconj g)
  · exact (matrixAutomorphism_eq Y' hgen' ⟨_, hg⟩ _).2
      ((hconj g.val _).2 (matrixAutomorphism_spec Y g))

end MatrixActions

section Localization

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] {n : ℕ}

private theorem range_le_of_image_matrix {Y : GL (Fin n) R}
    (hgen : matrixGeneratedSubalgebra K Y = ⊤) (f g : R →ₐ[K] S)
    (b : GL (Fin n) K)
    (h : GeneralLinearGroup.map f.toRingHom Y =
      GeneralLinearGroup.map g.toRingHom Y * GeneralLinearGroup.map (algebraMap K S) b) :
    f.range ≤ g.range := by
  have hmem := matrixGeneratedSubalgebra_image_le_range g Y b
  rw [← h] at hmem
  obtain ⟨he, hd⟩ := (matrixGeneratedSubalgebra_le_iff _ _).1 hmem
  have hle : matrixGeneratedSubalgebra K Y ≤ g.range.comap f := by
    refine (matrixGeneratedSubalgebra_le_iff _ _).2 ⟨he, ?_⟩
    rw [determinantInverse_map] at hd
    exact hd
  rw [hgen] at hle
  rintro _ ⟨x, rfl⟩
  exact hle (show x ∈ (⊤ : Subalgebra K R) from trivial)

private theorem range_eq_of_image_matrix {Y : GL (Fin n) R}
    (hgen : matrixGeneratedSubalgebra K Y = ⊤) (f g : R →ₐ[K] S)
    (b : GL (Fin n) K)
    (h : GeneralLinearGroup.map f.toRingHom Y =
      GeneralLinearGroup.map g.toRingHom Y * GeneralLinearGroup.map (algebraMap K S) b) :
    f.range = g.range :=
  le_antisymm (range_le_of_image_matrix hgen f g b h)
    (range_le_of_image_matrix hgen g f b⁻¹ (by
      rw [map_inv]
      exact eq_mul_inv_iff_mul_eq.2 h.symm))

omit [Algebra K R] in
private theorem localizationAlgEquiv_ext {Q : Type*} [CommRing Q] [Algebra R Q]
    [IsFractionRing R Q] [Algebra K Q] {τ υ : Q ≃ₐ[K] Q}
    (h : ∀ r, τ (algebraMap R Q r) = υ (algebraMap R Q r)) : τ = υ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext R⁰
  exact RingHom.ext h

end Localization

set_option maxHeartbeats 800000 in
/-- Extension to the total ring of fractions is invertible by restriction, since
an automorphism of the localization preserves the generated subalgebra. -/
theorem galoisTotalRingAction : Specs.galoisTotalRingAction.{u, v} := by
  intro kind K _ R _ _ n δ A E Y F hk hpv hY hF
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  change Operator kind (TotalQuotientRing R) at F
  change E.IsAlgebra F at hF
  let Q := TotalQuotientRing R
  let G := matrixGaloisGroup δ E Y
  let : Algebra K Q := Algebra.compHom Q (algebraMap K R)
  let i : R →ₐ[K] Q := { algebraMap R Q with commutes' := fun _ => rfl }
  have hi : Function.Injective i := IsFractionRing.injective R Q
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv Y hY
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  obtain ⟨α, hα, _⟩ := galoisRingAction δ A E Y hk hpv hY
  let extend : operatorAutomorphisms K E → operatorAutomorphisms K F := fun τ =>
    ⟨AlgEquiv.ofRingEquiv (f := Operator.fractionRingEquiv τ.val.toRingEquiv) (fun k => by
        change Operator.fractionRingEquiv τ.val.toRingEquiv
          (algebraMap R Q (algebraMap K R k)) = algebraMap R Q (algebraMap K R k)
        rw [Operator.fractionRingEquiv_algebraMap]
        exact congrArg (algebraMap R Q) (τ.val.commutes k)),
      Operator.fractionRingEquiv_commutes ⟨τ.val.toRingEquiv, τ.property⟩ hF hF⟩
  have hext (τ : operatorAutomorphisms K E) (r : R) :
      (extend τ).val (i r) = i (τ.val r) :=
    Operator.fractionRingEquiv_algebraMap τ.val.toRingEquiv r
  have hbij : Function.Bijective extend := by
    constructor
    · intro τ υ h
      apply Subtype.ext
      ext r
      apply hi
      rw [← hext, ← hext, h]
    · intro τ
      let j : R →ₐ[K] Q := τ.val.toAlgHom.comp i
      have hj : Function.Injective j := τ.val.injective.comp hi
      have hδF : δ.IsExtension F :=
        ⟨hF.comp hpv.1.1, hi.comp hpv.1.2⟩
      let W := GeneralLinearGroup.map i.toRingHom Y
      have hW : A.IsFundamental F W := fundamental_map i hF hY
      have hC := Operator.constants_finiteType_fractionRing δ E F hk hpv.2.1 hpv.1.1 hF
      obtain ⟨b, hb⟩ := baseConstantMultiplier hk hδF hC hW
        (fundamental_map τ.val.toAlgHom τ.property hW)
      let bK := GeneralLinearGroup.map δ.constantSubfield.subtype b
      have hrange : j.range = i.range := range_eq_of_image_matrix hgen j i bK hb
      let a := AlgEquiv.ofInjective j hj
      let c := AlgEquiv.ofInjective i hi
      let ψ := a.trans ((Subalgebra.equivOfEq _ _ hrange).trans c.symm)
      have hψ (r : R) : i (ψ r) = j r := by
        have h := c.apply_symm_apply (Subalgebra.equivOfEq _ _ hrange (a r))
        exact congrArg Subtype.val h
      have hψcomm : E.Commutes E ψ := by
        intro r
        apply hi
        have hiF : E.Commutes F i := hF
        calc
          i (ψ (E r)) = τ.val (i (E r)) := hψ (E r)
          _ = τ.val (F (i r)) := congrArg τ.val (hiF r)
          _ = F (τ.val (i r)) := τ.property (i r)
          _ = F (i (ψ r)) := congrArg (Operator.apply F) (hψ r).symm
          _ = i (E (ψ r)) := (hiF (ψ r)).symm
      refine ⟨⟨ψ, hψcomm⟩, Subtype.ext ?_⟩
      apply localizationAlgEquiv_ext (R := R)
      exact fun r => (hext ⟨ψ, hψcomm⟩ r).trans (hψ r)
  let β : operatorAutomorphisms K E ≃* operatorAutomorphisms K F :=
    { Equiv.ofBijective extend hbij with
      map_mul' := by
        intro τ υ
        apply Subtype.ext
        apply localizationAlgEquiv_ext (R := R)
        intro r
        change (extend (τ * υ)).val (i r) = (extend τ).val ((extend υ).val (i r))
        rw [hext, hext, hext]
        rfl }
  let e := α.trans β
  have haction (g : G) : (e g).val.toRingEquiv = matrixFractionAutomorphism δ E Y g := by
    change (extend (α g)).val.toRingEquiv = _
    rw [hα g]
    rfl
  refine ⟨e, haction, fun g τ => ?_⟩
  have hg (r : R) : (e g).val (i r) = i ((matrixAutomorphism δ E Y g).val r) := by
    change (extend (α g)).val (i r) = _
    rw [hext, hα]
  constructor
  · rintro rfl
    exact hg
  · intro h
    apply Subtype.ext
    exact localizationAlgEquiv_ext (R := R) (fun r => (hg r).trans (h r).symm)

section TensorEvaluation

open MatrixGroupCoordinates (CoordinatePolynomial evalAt)

private theorem tensorHom_commutes {kind : OperatorKind} {L P V S : Type*}
    [CommRing L] [CommRing P] [CommRing V] [CommRing S] [Algebra L P] [Algebra L V]
    {E : Operator kind P} {F : Operator kind V} {G : Operator kind (P ⊗[L] V)}
    {H : Operator kind S} (hG : Specs.tensorLaws (R := L) E F G)
    (m : P ⊗[L] V →+* S)
    (hleft : E.Commutes H (m.comp includeLeftRingHom))
    (hright : F.Commutes H (m.comp (includeRight : V →ₐ[L] P ⊗[L] V).toRingHom)) :
    G.Commutes H m := by
  intro x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [Operator.map_add, map_add, ha, hb]
  | tmul a b =>
    have hp (p : P) (v : V) : m (p ⊗ₜ[L] v) = m (p ⊗ₜ[L] 1) * m (1 ⊗ₜ[L] v) := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have ha : m (E a ⊗ₜ[L] 1) = H (m (a ⊗ₜ[L] 1)) := hleft a
    have hb : m (1 ⊗ₜ[L] F b) = H (m (1 ⊗ₜ[L] b)) := hright b
    cases kind with
    | differential =>
      have h := hG.1 a b
      change G (a ⊗ₜ[L] b) = (E a ⊗ₜ[L] b) + (a ⊗ₜ[L] F b) at h
      rw [h, map_add, hp (E a) b, hp a (F b), ha, hb, hp a b]
      change H.toDerivation _ * _ + _ * H.toDerivation _ = H.toDerivation (_ * _)
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ac_rfl
    | difference =>
      have h := hG.1.1 a b
      change G (a ⊗ₜ[L] b) = E a ⊗ₜ[L] F b at h
      rw [h, hp (E a) (F b), ha, hb, hp a b]
      exact (H.toRingEquiv.map_mul _ _).symm

private theorem injective_of_operatorSimple {kind : OperatorKind} {S T : Type*}
    [CommRing S] [CommRing T] [Nontrivial T] {E : Operator kind S} {F : Operator kind T}
    (hs : E.IsSimple) (f : S →+* T) (hf : E.Commutes F f) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).2
  refine (hs.2 _ ?_).resolve_right (RingHom.ker_ne_top f)
  cases kind with
  | differential =>
    intro x hx
    change f x = 0 at hx
    change f (E x) = 0
    rw [hf, hx, Operator.map_zero]
  | difference =>
    constructor
    · intro x hx
      change f x = 0 at hx
      change f (E x) = 0
      rw [hf, hx, Operator.map_zero]
    · intro x hx
      change f x = 0 at hx
      change f (E.toRingEquiv.symm x) = 0
      rw [hf.difference_symm, hx, map_zero]

private theorem evalAt_map {C S T : Type*} [CommRing C] [CommRing S] [CommRing T]
    [Algebra C S] [Algebra C T] {n : ℕ} (f : S →ₐ[C] T) (B : GL (Fin n) S) :
    evalAt (GeneralLinearGroup.map f.toRingHom B) = f.comp (evalAt B) := by
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨i, j⟩ | z
  · simp [MatrixGroupCoordinates.evalAt_entry]
  · cases z
    rw [AlgHom.comp_apply, MatrixGroupCoordinates.evalAt_inverseDeterminant,
      MatrixGroupCoordinates.evalAt_inverseDeterminant]
    exact determinantInverse_map f.toRingHom B

private theorem evalAt_range {C S : Type*} [CommRing C] [CommRing S] [Algebra C S]
    {n : ℕ} (B : GL (Fin n) S) : (evalAt (C := C) B).range = matrixGeneratedSubalgebra C B := by
  change (MvPolynomial.aeval _).range = _
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr 1
  apply Set.ext
  intro x
  constructor
  · rintro ⟨ij | ⟨⟩, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨ij, rfl⟩
    · exact Set.mem_insert _ _
  · rintro (rfl | hx)
    · exact ⟨Sum.inr (), rfl⟩
    · obtain ⟨ij, rfl⟩ := hx
      exact ⟨Sum.inl ij, rfl⟩

private theorem evalAt_ratio_surjective {C T : Type*} [CommRing C] [CommRing T]
    [Algebra C T] {n : ℕ} {Z : GL (Fin n) T}
    {B : GL (Fin n) (matrixGeneratedSubalgebra C Z)}
    (hB : GeneralLinearGroup.map (matrixGeneratedSubalgebra C Z).val.toRingHom B = Z) :
    Function.Surjective (evalAt (C := C) B) := by
  let D := matrixGeneratedSubalgebra C Z
  have hr : (D.val.comp (evalAt B)).range = D := by
    rw [← evalAt_map, hB, evalAt_range]
  intro d
  have hd : (d : T) ∈ (D.val.comp (evalAt B)).range := hr.symm ▸ d.property
  obtain ⟨p, hp⟩ := (D.val.comp (evalAt B)).mem_range.mp hd
  exact ⟨p, Subtype.ext hp⟩

private theorem map_tensorRatio {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
    [Algebra K R] {n : ℕ} (Y : GL (Fin n) R) (f : R ⊗[K] R →+* S)
    {l r : R →+* S} (hl : f.comp includeLeftRingHom = l)
    (hr : f.comp (includeRight : R →ₐ[K] R ⊗[K] R).toRingHom = r) :
    GeneralLinearGroup.map f (tensorRatio K Y) =
      (GeneralLinearGroup.map l Y)⁻¹ * GeneralLinearGroup.map r Y := by
  unfold tensorRatio Specs.tensorRatio
  rw [map_mul, map_inv]
  change (GeneralLinearGroup.map (f.comp includeLeftRingHom) Y)⁻¹ *
    GeneralLinearGroup.map (f.comp (includeRight : R →ₐ[K] R ⊗[K] R).toRingHom) Y = _
  rw [hl, hr]

end TensorEvaluation

set_option maxHeartbeats 1600000 in
/-- Specialization along the torsor identifies evaluations of the ratio algebra
with matrices of operator automorphisms. -/
theorem galoisEvaluation : Specs.galoisEvaluation.{u, v} := by
  intro kind K _ R _ _ n δ A E Y hk hpv hY
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  let C := Specs.constantSubfield δ
  let : Algebra C R := Algebra.compHom R (Specs.constantSubfield δ).subtype
  let : IsScalarTower C K R := IsScalarTower.of_algebraMap_eq' rfl
  let T := R ⊗[K] R
  let D : Subalgebra C T := picardVessiotCoordinateAlgebra δ Y
  let G := matrixGaloisGroup δ E Y
  let U := R ⊗[C] D
  let : CommRing U := Algebra.TensorProduct.instCommRing
  let : Algebra R U := Algebra.TensorProduct.leftAlgebra
  let : Algebra C U := Algebra.TensorProduct.leftAlgebra
  let F := Operator.tensor hpv.1.1 hpv.1.1
  have hF := Operator.tensor_laws hpv.1.1 hpv.1.1
  have hT := picardVessiotTensor δ A E Y F hk hpv hY hF
  dsimp only at hT
  obtain ⟨_, _, hD, _, _, L, φ, hL, _, B, hB, hY₂⟩ := hT
  change Operator kind U at L
  change Operator.AlgEquiv R L F at φ
  change GL (Fin n) D at B
  change GeneralLinearGroup.map D.val.toRingHom B = tensorRatio K Y at hB
  let : Nontrivial R := hpv.2.1.1
  have hgen := matrixGeneratedSubalgebra_of_fundamental hk hpv Y hY
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y hgen
  have hconstants := hasConstantField_of_finiteType hk hpv.2.1 hpv.1.1
  let ι : C →ₐ[C] R := Algebra.ofId C R
  have hι : Function.Injective ι :=
    hpv.1.2.comp (Operator.constantSubfieldEmbedding_injective δ)
  let right : R →ₐ[K] T := includeRight
  have hpoints (f : D →ₐ[C] C) : GeneralLinearGroup.map f.toRingHom B ∈ G := by
    let q : U →ₐ[R] R := lift (AlgHom.id R R) (ι.comp f) (fun _ _ => Commute.all _ _)
    let m : T →ₐ[R] R := q.comp φ.val.symm.toAlgHom
    let ψ : R →ₐ[K] R := (m.restrictScalars K).comp right
    have hleft : q.toRingHom.comp (includeLeftRingHom : R →+* U) = RingHom.id R :=
      RingHom.ext (fun x => by
        change q (x ⊗ₜ[C] (1 : D)) = x
        change x * (ι.comp f) 1 = x
        rw [map_one, mul_one])
    have hright : q.toRingHom.comp (includeRight : D →ₐ[C] U).toRingHom =
        ι.toRingHom.comp f.toRingHom := RingHom.ext (fun d => by
          change q ((1 : R) ⊗ₜ[C] d) = ι (f d)
          change (1 : R) * ι (f d) = ι (f d)
          exact one_mul _)
    have hq : L.Commutes E q := by
      apply tensorHom_commutes hL q.toRingHom
      · rw [hleft]
        exact Operator.Commutes.id E
      · rw [hright]
        intro d
        have hc : E.IsConstant (ι (f d)) := (hconstants _).2 ⟨f d, rfl⟩
        change ι (f (Specs.apply (Specs.trivial kind D) d)) = E (ι (f d))
        cases kind with
        | differential =>
          change E.toDerivation (ι (f d)) = 0 at hc
          change ι (f 0) = E.toDerivation (ι (f d))
          rw [map_zero, map_zero, hc]
        | difference =>
          exact hc.symm
    have hm : F.Commutes E m :=
      hq.comp (Operator.Commutes.inverse (f := φ.val.toEquiv) φ.property)
    have hψ : E.Commutes E ψ := hm.comp hF.2.2
    have hmat : GeneralLinearGroup.map ψ.toRingHom Y =
        Y * GeneralLinearGroup.map (constantsIn δ) (GeneralLinearGroup.map f.toRingHom B) := by
      have h := congrArg (GeneralLinearGroup.map m.toRingHom) hY₂
      have hmq : m.toRingHom.comp φ.val.toRingHom = q.toRingHom := by
        exact RingHom.ext (fun x => congrArg q (φ.val.symm_apply_apply x))
      change GeneralLinearGroup.map (m.toRingHom.comp φ.val.toRingHom)
        (GeneralLinearGroup.map (includeLeftRingHom : R →+* U) Y *
          GeneralLinearGroup.map (includeRight : D →ₐ[C] U).toRingHom B) =
        GeneralLinearGroup.map ψ.toRingHom Y at h
      rw [hmq, map_mul] at h
      change GeneralLinearGroup.map (q.toRingHom.comp (includeLeftRingHom : R →+* U)) Y *
        GeneralLinearGroup.map (q.toRingHom.comp (includeRight : D →ₐ[C] U).toRingHom) B = _
        at h
      rw [hleft, hright, GeneralLinearGroup.map_id, MonoidHom.id_apply] at h
      exact h.symm
    let bK := GeneralLinearGroup.map C.subtype (GeneralLinearGroup.map f.toRingHom B)
    have hfRange := range_eq_of_image_matrix hgen ψ (AlgHom.id K R) bK hmat
    have hsurj : Function.Surjective ψ :=
      (AlgHom.range_eq_top _).1 (hfRange.trans Algebra.range_id)
    let τ := AlgEquiv.ofBijective ψ ⟨injective_of_operatorSimple hpv.2.1 ψ.toRingHom hψ, hsurj⟩
    exact ⟨⟨τ, hψ⟩, hmat⟩
  let forward : (D →ₐ[C] C) → G := fun f => ⟨GeneralLinearGroup.map f.toRingHom B, hpoints f⟩
  have hBsurj : Function.Surjective (MatrixGroupCoordinates.evalAt (C := C) B) :=
    evalAt_ratio_surjective hB
  have hinj : Function.Injective forward := by
    intro f g h
    have hm : GeneralLinearGroup.map f.toRingHom B = GeneralLinearGroup.map g.toRingHom B :=
      congrArg Subtype.val h
    apply AlgHom.ext
    intro d
    obtain ⟨p, rfl⟩ := hBsurj d
    have hh := congrArg (MatrixGroupCoordinates.evalAt (C := C)) hm
    rw [evalAt_map f, evalAt_map g] at hh
    exact DFunLike.congr_fun hh p
  let M (g : G) : T →ₐ[K] R :=
    lift (AlgHom.id K R) (matrixAutomorphism δ E Y g).val.toAlgHom (fun _ _ => Commute.all _ _)
  have hMleft (g : G) : (M g).toRingHom.comp includeLeftRingHom = RingHom.id R :=
    RingHom.ext (fun r => by
      change M g (r ⊗ₜ[K] (1 : R)) = r
      change r * (matrixAutomorphism δ E Y g).val 1 = r
      rw [map_one, mul_one])
  have hMright (g : G) : (M g).toRingHom.comp right.toRingHom =
      (matrixAutomorphism δ E Y g).val.toRingHom :=
    RingHom.ext (fun r => by
      change M g ((1 : R) ⊗ₜ[K] r) = _
      change (1 : R) * (matrixAutomorphism δ E Y g).val r = _
      exact one_mul _)
  have hM (g : G) : F.Commutes E (M g) := by
    apply tensorHom_commutes hF (M g).toRingHom
    · rw [hMleft]
      exact Operator.Commutes.id E
    · change E.Commutes E ((M g).toRingHom.comp right.toRingHom)
      rw [hMright]
      exact (matrixAutomorphism δ E Y g).property
  let s (g : G) : D →ₐ[C] R :=
    { (M g).toRingHom.comp D.val.toRingHom with
      commutes' := fun c => (M g).commutes (c : K) }
  let eι := AlgEquiv.ofInjective ι hι
  let backward (g : G) : D →ₐ[C] C :=
    eι.symm.toAlgHom.comp ((s g).codRestrict ι.range (fun d =>
      (hconstants _).1 ((hM g).isConstant (hD d))))
  have hback (g : G) (d : D) : ι (backward g d) = M g (d : T) := by
    exact congrArg Subtype.val (eι.apply_symm_apply ((s g).codRestrict _ _ d))
  have hrightInv (g : G) : forward (backward g) = g := by
    apply Subtype.ext
    apply mapGL_injective ι.toRingHom hι
    have hb : ι.toRingHom.comp (backward g).toRingHom =
        (M g).toRingHom.comp D.val.toRingHom := RingHom.ext (hback g)
    change GeneralLinearGroup.map (ι.toRingHom.comp (backward g).toRingHom) B =
      GeneralLinearGroup.map (constantsIn δ) g.val
    calc
      GeneralLinearGroup.map (ι.toRingHom.comp (backward g).toRingHom) B =
          GeneralLinearGroup.map (M g).toRingHom (tensorRatio K Y) := by
        rw [hb, GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hB]
      _ = Y⁻¹ * GeneralLinearGroup.map (matrixAutomorphism δ E Y g).val.toRingHom Y := by
        simpa only [GeneralLinearGroup.map_id, MonoidHom.id_apply] using
          map_tensorRatio Y (M g).toRingHom (hMleft g) (hMright g)
      _ = GeneralLinearGroup.map (constantsIn δ) g.val := by
        rw [matrixAutomorphism_spec Y g, inv_mul_cancel_left]
  let e : (D →ₐ[C] C) ≃ G :=
    ⟨forward, backward, fun f => hinj (hrightInv (forward f)), hrightInv⟩
  exact ⟨B, hB, e, fun _ => rfl, hback⟩

open scoped MatrixGroupCoordinates.Specs in
set_option maxHeartbeats 1000000 in
/-- The ratio relations cut out the group, and evaluation identifies the ratio algebra
with its polynomial coordinate algebra. -/
theorem galoisCoordinateAlgebra : Specs.galoisCoordinateAlgebra.{u, v} := by
  intro kind K _ R _ _ n δ A E Y hk hpv hY
  change OperatorField kind K at δ
  change Operator kind R at E
  change LinearSystem kind K n at A
  change δ.IsBaseField at hk
  change IsPicardVessiotRing δ A E at hpv
  change A.IsFundamental E Y at hY
  let C := Specs.constantSubfield δ
  let : IsAlgClosed C := hk.2
  let : Algebra C R := Algebra.compHom R (Specs.constantSubfield δ).subtype
  let T := R ⊗[K] R
  let D : Subalgebra C T := picardVessiotCoordinateAlgebra δ Y
  let Z := tensorRatio K Y
  let G := matrixGaloisGroup δ E Y
  let S : Set (GL (Fin n) C) := G
  let P := MatrixGroupCoordinates.CoordinatePolynomial C n
  obtain ⟨B, hB, points, hpoints, _⟩ := galoisEvaluation δ A E Y hk hpv hY
  change GL (Fin n) D at B
  change GeneralLinearGroup.map D.val.toRingHom B = Z at hB
  let ev : P →ₐ[C] D := MatrixGroupCoordinates.evalAt B
  let I := RingHom.ker ev
  have hs : Function.Surjective ev := evalAt_ratio_surjective hB
  have hcomp : D.val.comp ev = MatrixGroupCoordinates.evalAt Z := by
    rw [← hB, evalAt_map]
  have hI : tensorRatioRelations δ Y = I := by
    ext p
    change MatrixGroupCoordinates.evalAt (C := C) Z p = 0 ↔ ev p = 0
    rw [← hcomp]
    exact (map_eq_zero_iff D.val Subtype.val_injective)
  have heval (f : D →ₐ[C] C) :
      MatrixGroupCoordinates.evalAt (points f).val = f.comp ev := by
    rw [hpoints, evalAt_map]
  have hS : S = MatrixGroupCoordinates.zeroLocus (I : Set P) := by
    ext g
    constructor
    · intro hg p hp
      let f := points.symm ⟨g, hg⟩
      have h := heval f
      rw [points.apply_symm_apply] at h
      change MatrixGroupCoordinates.evalAt g p = 0
      rw [h, AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero]
    · intro hg
      let evg : P →ₐ[C] C := MatrixGroupCoordinates.evalAt g
      have hIg : RingHom.ker ev.toRingHom ≤ RingHom.ker evg.toRingHom := hg
      let f := ev.liftOfSurjective hs evg hIg
      have h : (points f).val = g := by
        apply Units.ext
        apply Matrix.ext
        intro i j
        have hval := DFunLike.congr_fun (heval f) (MvPolynomial.X (Sum.inl (i, j)))
        rw [MatrixGroupCoordinates.evalAt_entry, AlgHom.comp_apply,
          AlgHom.liftOfSurjective_apply, MatrixGroupCoordinates.evalAt_entry] at hval
        exact hval
      exact h ▸ (points f).property
  have hclosed : MatrixGroupCoordinates.IsAlgebraicSubgroup G :=
    (MatrixGroupCoordinates.isClosed_iff_zeroLocus S).2 ⟨I, hS⟩
  let : Algebra.FiniteType C D := Algebra.FiniteType.of_surjective ev hs
  let : Nontrivial D := (points.symm (1 : G)).toRingHom.domain_nontrivial
  let F := Operator.tensor hpv.1.1 hpv.1.1
  have hT := picardVessiotTensor δ A E Y F hk hpv hY (Operator.tensor_laws hpv.1.1 hpv.1.1)
  let : IsReduced D := hT.2.2.2.2.1
  have hker : I = MatrixGroupCoordinates.vanishingIdeal S := by
    ext p
    rw [MatrixGroupCoordinates.mem_vanishingIdeal]
    constructor
    · intro hp g
      let f := points.symm g
      have h := heval f
      rw [points.apply_symm_apply] at h
      rw [h, AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero]
    · intro hp
      apply RingHom.mem_ker.mpr
      by_contra h
      obtain ⟨f, hf⟩ := existsAlgHomOfNeZero C D (ev p) h
      apply hf
      exact (DFunLike.congr_fun (heval f) p).symm.trans (hp (points f))
  let e : MatrixGroupCoordinates.CoordinateRing S ≃ₐ[C] D :=
    (Ideal.quotientEquivAlgOfEq C hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hs)
  have hz : S = MatrixGroupCoordinates.zeroLocus (tensorRatioRelations δ Y : Set P) :=
    hI.symm ▸ hS
  refine ⟨hz, hclosed, hI.trans hker, e.symm, ?_⟩
  intro p
  change D.val (e (MatrixGroupCoordinates.coordinateMap S p)) = _
  have he : e (MatrixGroupCoordinates.coordinateMap S p) = ev p := rfl
  rw [he]
  exact DFunLike.congr_fun hcomp p

end

end GaloisFormalization.PV
