import Specs.LinearAlgebraicGroups.Representation.CharacterRing
import LinearAlgebraicGroups.Representation.FormalCharacters
import LinearAlgebraicGroups.Representation.SimpleClassification
import LinearAlgebraicGroups.Representation.DominantOrder
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Ring.TransferInstance

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj Classical TensorProduct
open LinearAlgebraicGroups.Specs

universe u

namespace LinearAlgebraicGroups.Representation.CharacterRing

open Specs.CharacterRing
open Specs.CharacterDescent (Character)
open Specs.FormalCharacters (Equivariant formalCharacter tensorRepresentation)
open Specs.RootWeightAction (Representation weightSpace)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.SimpleClassification (SocleModel)
open Specs.InducedNonvanishing (Dominant)
open Specs.PrimitiveLine (IsSimple IsStable IsEquivariant)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

section Invariants

variable {X W : Type*} [CommGroup X] [Group W] (a : W →* MulAut X)

private theorem invariant_iff (f : MonoidAlgebra ℤ X) :
    f ∈ invariantRing a ↔ ∀ w x, f.coeff (a w x) = f.coeff x := by
  constructor
  · intro hf w x
    have h := congrArg (fun g : MonoidAlgebra ℤ X => g.coeff (a w x)) (hf w)
    simpa [Finsupp.equivMapDomain_apply] using h.symm
  · intro hf w
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    simp only [MonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
    change f.coeff ((a w).symm x) = f.coeff x
    simpa only [MulEquiv.apply_symm_apply] using (hf w ((a w).symm x)).symm

private theorem coeff_orbitSum [Finite W] (x y : X) :
    (orbitSum a x).coeff y = if ∃ w, a w x = y then 1 else 0 := by
  classical
  letI := Fintype.ofFinite W
  change (∑ z ∈ Finset.univ.image (fun w : W => a w x),
    MonoidAlgebra.single z (1 : ℤ)).coeff y = _
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem y (by simpa using h)]
    · simp
    · intro z _ hne
      simp [hne]
  · apply Finset.sum_eq_zero
    intro z hz
    have hn : z ≠ y := by
      rintro rfl
      exact h (by simpa using hz)
    simp [hn]

private theorem orbit_iff_translate (x y : X) (v : W) :
    (∃ w, a w x = a v y) ↔ ∃ w, a w x = y := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨v⁻¹ * w, ?_⟩
    rw [map_mul]
    change a v⁻¹ (a w x) = y
    rw [hw, map_inv]
    exact (a v).symm_apply_apply y
  · rintro ⟨w, hw⟩
    exact ⟨v * w, by simp [hw]⟩

private def invariantOrbitSum [Finite W] (x : X) : invariantRing a :=
  ⟨orbitSum a x, (invariant_iff a _).2 fun w y => by
    classical
    rw [coeff_orbitSum, coeff_orbitSum, orbit_iff_translate]⟩

variable {A : Type*} (i : A ↪ X)

private def coordinates : invariantRing a →ₗ[ℤ] (A →₀ ℤ) :=
  (Finsupp.lcomapDomain i i.injective).comp
    ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap.comp
      (invariantRing a).subtype.toAddMonoidHom.toIntLinearMap)

private theorem coordinates_apply (f : invariantRing a) (j : A) :
    coordinates a i f j = f.val.coeff (i j) := rfl

private theorem coordinates_injective (h : ∀ x, ∃ j w, a w x = i j) :
    Function.Injective (coordinates a i) := by
  intro f g heq
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  obtain ⟨j, w, hw⟩ := h x
  have hf := (invariant_iff a _).1 f.property w x
  have hg := (invariant_iff a _).1 g.property w x
  rw [← hf, ← hg, hw]
  exact DFunLike.congr_fun heq j

private theorem coordinates_orbitSum [Finite W]
    (h : ∀ j l : A, (∃ w, a w (i j) = i l) ↔ j = l) (j : A) :
    coordinates a i (invariantOrbitSum a (i j)) = Finsupp.single j 1 := by
  classical
  ext l
  rw [coordinates_apply, show (invariantOrbitSum a (i j)).val = orbitSum a (i j) from rfl,
    coeff_orbitSum, h, Finsupp.single_apply]

private theorem coordinates_orbitExpansion [Finite W]
    (h : ∀ j l : A, (∃ w, a w (i j) = i l) ↔ j = l) :
    (coordinates a i).comp
      (Finsupp.linearCombination ℤ (fun j => invariantOrbitSum a (i j))) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j c
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.linearCombination_single,
    map_smul, coordinates_orbitSum a i h, Finsupp.smul_single, smul_eq_mul, mul_one]

private def orbitCoordinates [Finite W]
    (existsRep : ∀ x, ∃ j w, a w x = i j)
    (uniqueRep : ∀ j l : A, (∃ w, a w (i j) = i l) ↔ j = l) :
    invariantRing a ≃ₗ[ℤ] (A →₀ ℤ) :=
  LinearEquiv.ofBijective (coordinates a i)
    ⟨coordinates_injective a i existsRep, fun f =>
      ⟨_, DFunLike.congr_fun (coordinates_orbitExpansion a i uniqueRep) f⟩⟩

end Invariants

section Triangular

variable {A : Type*} (height : A → ℕ) (row : A → A →₀ ℤ)

private theorem triangular_bijective
    (diagonal : ∀ j, row j j = 1)
    (lower : ∀ j l, j ≠ l → row j l ≠ 0 → height l < height j) :
    Function.Bijective (Finsupp.linearCombination ℤ row) := by
  classical
  let L := Finsupp.linearCombination ℤ row
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).2
    intro v hv
    by_contra hn
    have hm : v.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image v.support height hm
    have hz : L v j = 0 := DFunLike.congr_fun (LinearMap.mem_ker.mp hv) j
    have hsum : L v j = v j := by
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single_of_mem j hj]
      · rw [diagonal, mul_one]
      · intro l hl hne
        have hzero : row l j = 0 :=
          by_contra fun h => (not_lt_of_ge (hmax l hl)) (lower l j hne h)
        rw [hzero, mul_zero]
    exact (Finsupp.mem_support_iff.mp hj) (hsum.symm.trans hz)
  · rw [← LinearMap.range_eq_top]
    have hs : ∀ j, Finsupp.single j (1 : ℤ) ∈ LinearMap.range L := by
      have inductionStep (n : ℕ) : ∀ j, height j = n →
          Finsupp.single j (1 : ℤ) ∈ LinearMap.range L := by
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro j hj
          let rest := row j - Finsupp.single j 1
          have hr : rest ∈ LinearMap.range L := by
            rw [← Finsupp.sum_single rest]
            apply Submodule.sum_mem
            intro l hl
            have hn : rest l ≠ 0 := Finsupp.mem_support_iff.mp hl
            have hne : j ≠ l := by
              rintro rfl
              exact hn (by simp [rest, diagonal])
            have hc : row j l ≠ 0 := by
              simpa [rest, Finsupp.single_apply, hne] using hn
            have ht : height l < n := hj ▸ lower j l hne hc
            simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
              (LinearMap.range L).smul_mem (rest l) (ih (height l) ht l rfl)
          have hrow : row j ∈ LinearMap.range L :=
            ⟨Finsupp.single j 1, by simp [L, Finsupp.linearCombination_single]⟩
          simpa [rest] using (LinearMap.range L).sub_mem hrow hr
      exact fun j => inductionStep _ j rfl
    apply top_unique
    intro f _
    rw [← Finsupp.sum_single f]
    apply Submodule.sum_mem
    intro j _
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
      (LinearMap.range L).smul_mem (f j) (hs j)

end Triangular


section ExactSequences

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open Specs.RootWeightAction (act actLinear extendVector)
open Specs.PrimitiveLine (orbitCoefficient)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.RationalRepresentations (pointsCoactionEquiv)
open private extendMap_apply from LinearAlgebraicGroups.Representation.FormalCharacters
open private fromCoaction toCoaction from_toCoaction act_contract contract_natural
  inclusion_equivariant generates_of_simple stable_iff
  from LinearAlgebraicGroups.Representation.PrimitiveLine
open private coordinateIso from LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private contract from LinearAlgebraicGroups.Representation.PrimitiveLine
open private quotientCoaction from LinearAlgebraicGroups.Unipotent.Criteria

private theorem equivariant_of_coefficients {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (h : IsEquivariant ρ σ f) : Equivariant ρ σ f := by
  intro R g
  let F := ((LinearMap.toMatrix' f).map (algebraMap k R)).mulVecLin
  have hcomm (ℓ : R →ₗ[k] k) (x : I → R) (j : J) :
      ℓ (F x j) = f (fun i => ℓ (x i)) j := by
    rw [← LinearMap.toMatrix'_mulVec f]
    simp [F, Matrix.mulVec, dotProduct, map_sum, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hext (v : I → k) : F (act ρ R g (extendVector R v)) =
      act σ R g (F (extendVector R v)) := by
    funext j
    by_contra hn
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hn)
    apply hℓ
    rw [map_sub, hcomm, show F (extendVector R v) = extendVector R (f v) from
      extendMap_apply f R v, sub_eq_zero]
    exact congrFun (h R g ℓ v) j
  have hlinear : F.comp (actLinear ρ R g) = (actLinear σ R g).comp F := by
    apply (Pi.basisFun R I).ext
    intro i
    have hbi : extendVector R (Pi.basisFun k I i) = Pi.basisFun R I i := by
      funext j
      by_cases hj : j = i <;> simp [extendVector, Pi.basisFun_apply, hj]
    exact hbi ▸ hext (Pi.basisFun k I i)
  exact fun v => LinearMap.congr_fun hlinear v

private theorem class_exact {U V W : Rep G} (h : ShortExact U V W) :
    ofRep V = ofRep U + ofRep W := by
  have hz : (exactRelations G).mkQ
      (Finsupp.single V 1 - (Finsupp.single U 1 + Finsupp.single W 1)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := exactRelations G)).mpr (Submodule.subset_span ⟨U, V, W, ⟨h⟩, rfl⟩)
  simpa only [map_sub, map_add, sub_eq_zero, ofRep] using hz

private theorem equivariant_zero {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (ρ : Representation G.val I) (σ : Representation G.val J) :
    Equivariant ρ σ (0 : (I → k) →ₗ[k] (J → k)) := by
  apply equivariant_of_coefficients
  intro R g ℓ v
  change 0 = fun j => ℓ (act σ R g (extendVector R 0) j)
  have hz : extendVector R (0 : J → k) = 0 := by
    funext j
    exact map_zero (algebraMap k R)
  rw [hz]
  change 0 = fun j => ℓ (actLinear σ R g 0 j)
  rw [map_zero (actLinear σ R g)]
  funext j
  exact (map_zero ℓ).symm

private theorem class_zero (V : Rep G) [Subsingleton (V.index → k)] :
    ofRep V = 0 := by
  have h : ShortExact V V V :=
    ⟨0, 0, equivariant_zero _ _, equivariant_zero _ _,
      Function.injective_of_subsingleton _, fun _ => by simp [Subsingleton.elim _ (0 : V.index → k)],
      Function.surjective_to_subsingleton _⟩
  exact left_eq_add.mp (class_exact h)

private theorem class_iso {V W : Rep G} (f : (V.index → k) ≃ₗ[k] (W.index → k))
    (hf : IsEquivariant V.action W.action f.toLinearMap) : ofRep V = ofRep W := by
  let Z : Rep G := ⟨PEmpty.{u+1}, {
    app := fun _ => GrpCat.ofHom 1
    naturality := by
      intro R S a
      apply GrpCat.ext
      intro g
      change 1 = ((Specs.StandardGroups.generalLinearPoints k PEmpty.{u+1}).map a).hom 1
      exact (map_one _).symm }⟩
  letI : Subsingleton (Z.index → k) := by dsimp [Z]; infer_instance
  have he : ShortExact V W Z :=
    ⟨f.toLinearMap, 0, equivariant_of_coefficients hf, equivariant_zero _ _,
      f.injective, fun _ => by simp, Function.surjective_to_subsingleton _⟩
  exact ((class_exact he).trans (by rw [class_zero Z, add_zero])).symm

private theorem coefficient_equivariance {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {A : HopfAlgebraCategory k}
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ρ : Representation G.val I) {V : Type u} [AddCommGroup V] [Module k V]
    (b : Module.Basis J k V) (δ : RightComodule k A V) (p : (I → k) →ₗ[k] V)
    (hp : δ.coaction.comp p = (p.rTensor A).comp (toCoaction e (Pi.basisFun k I) ρ).coaction) :
    IsEquivariant ρ (fromCoaction e b δ) (b.equivFun.toLinearMap.comp p) := by
  intro R g ℓ v
  obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective g
  have hs := act_contract e (Pi.basisFun k I) (toCoaction e (Pi.basisFun k I) ρ) R a.ofConv ℓ v
  rw [from_toCoaction] at hs
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at hs
  have ht := act_contract e b δ R a.ofConv ℓ (p v)
  change b.equivFun (p (fun i => ℓ (act ρ R (e.hom.app R (toConv a.ofConv)) (extendVector R v) i))) =
    fun j => ℓ (act (fromCoaction e b δ) R (e.hom.app R (toConv a.ofConv))
      (extendVector R (b.equivFun (p v))) j)
  rw [hs, ht, contract_natural]
  exact congrArg (fun z => b.equivFun (contract (ℓ.comp a.ofConv.toLinearMap) z))
    (LinearMap.congr_fun hp v).symm

/-- A stable subspace and its quotient give a short exact sequence in finite bases. -/
private theorem exact_of_stable (V : Rep G) (M : Submodule k (V.index → k))
    (hM : IsStable V.action M) :
    ∃ U W : Rep G, Nonempty (ShortExact U V W) ∧
      Module.finrank k (U.index → k) = Module.finrank k M ∧
      Module.finrank k (W.index → k) = Module.finrank k ((V.index → k) ⧸ M) := by
  let e := pointIso (coordinateIso G)
  let A := coordinateHopf ⟨G.val, G.property.1⟩
  let δ := toCoaction e (Pi.basisFun k V.index) V.action
  have hco := (stable_iff CyclicHighestWeight.cyclicHighestWeight.1 V.action A e M).mp hM
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction δ M).mp hco
  let Q := (V.index → k) ⧸ M
  let p : (V.index → k) →ₗ[k] Q := M.mkQ
  let f := M.liftQ ((p.rTensor A).comp δ.coaction) (by
    intro x hx
    obtain ⟨y, hy⟩ := hco ⟨x, hx⟩
    change p.rTensor A (δ.coaction x) = 0
    rw [← hy, ← LinearMap.rTensor_comp_apply]
    have hz : p.comp M.subtype = 0 := by
      ext z
      exact (Submodule.Quotient.mk_eq_zero (p := M)).mpr z.property
    rw [hz, LinearMap.rTensor_zero, LinearMap.zero_apply])
  have hf : f.comp p = (p.rTensor A).comp δ.coaction := Submodule.liftQ_mkQ _ _ _
  let σ := quotientCoaction A δ p M.mkQ_surjective f hf
  let b := (Module.finBasis k M).reindex (Equiv.ulift.symm :
    Fin (Module.finrank k M) ≃ ULift.{u} (Fin (Module.finrank k M)))
  let c := (Module.finBasis k Q).reindex (Equiv.ulift.symm :
    Fin (Module.finrank k Q) ≃ ULift.{u} (Fin (Module.finrank k Q)))
  let U : Rep G := ⟨_, fromCoaction e b τ⟩
  let W : Rep G := ⟨_, fromCoaction e c σ⟩
  let inc := M.subtype.comp b.equivFun.symm.toLinearMap
  let proj := c.equivFun.toLinearMap.comp p
  refine ⟨U, W, ⟨⟨inc, proj, ?_, ?_, ?_, ?_, ?_⟩⟩,
    (LinearEquiv.finrank_eq b.equivFun).symm, (LinearEquiv.finrank_eq c.equivFun).symm⟩
  · exact equivariant_of_coefficients (inclusion_equivariant e V.action M b τ hτ)
  · exact equivariant_of_coefficients (coefficient_equivariance e V.action c σ p hf)
  · exact M.subtype_injective.comp b.equivFun.symm.injective
  · intro x
    change c.equivFun (p x) = 0 ↔ x ∈ LinearMap.range inc
    rw [map_eq_zero_iff _ c.equivFun.injective, ← LinearMap.mem_ker, Submodule.ker_mkQ,
      LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  · exact c.equivFun.surjective.comp M.mkQ_surjective

/-- In the exact-sequence quotient, simple classes span by induction on dimension. -/
private theorem span_of_simple (A : Type*) (S : A → Rep G)
    (classify : ∀ V : Rep G, IsSimple V.action → ∃ j, ofRep V = ofRep (S j)) :
    Function.Surjective (Finsupp.linearCombination ℤ (fun j => ofRep (S j))) := by
  classical
  let L := Finsupp.linearCombination ℤ (fun j => ofRep (S j))
  have hgen (n : ℕ) : ∀ V : Rep G, Module.finrank k (V.index → k) = n →
      ofRep V ∈ LinearMap.range L := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V hV
      by_cases hz : n = 0
      · letI := (Module.finrank_zero_iff (R := k)).mp (hV.trans hz)
        rw [class_zero V]
        exact Submodule.zero_mem _
      by_cases hs : IsSimple V.action
      · obtain ⟨j, hj⟩ := classify V hs
        exact ⟨Finsupp.single j 1, by simpa [L, Finsupp.linearCombination_single] using hj.symm⟩
      have htop : (⊤ : Submodule k (V.index → k)) ≠ ⊥ := by
        intro h
        have hdim := congrArg (fun M : Submodule k (V.index → k) => Module.finrank k M) h
        exact hz (hV.symm.trans (by simpa using hdim))
      have hex : ∃ M : Submodule k (V.index → k), IsStable V.action M ∧ M ≠ ⊥ ∧ M ≠ ⊤ := by
        by_contra h
        apply hs
        refine ⟨htop, fun M hM => ?_⟩
        by_contra hm
        exact h ⟨M, hM, (not_or.mp hm).1, (not_or.mp hm).2⟩
      obtain ⟨M, hM, hbot, hproper⟩ := hex
      have hdim := M.finrank_quotient_add_finrank
      have hp : 0 < Module.finrank k M := Nat.pos_of_ne_zero (fun h => hbot (Submodule.finrank_eq_zero.mp h))
      have hq : 0 < Module.finrank k ((V.index → k) ⧸ M) := by
        apply Nat.pos_of_ne_zero
        intro h
        letI : Subsingleton ((V.index → k) ⧸ M) := Module.finrank_zero_iff.mp h
        apply hproper
        apply top_unique
        intro x _
        exact (Submodule.Quotient.mk_eq_zero (p := M)).mp (Subsingleton.elim _ 0)
      obtain ⟨U, W, ⟨seq⟩, hU, hW⟩ := exact_of_stable V M hM
      rw [class_exact seq]
      exact Submodule.add_mem _
        (ih _ (by omega) U rfl)
        (ih _ (by omega) W rfl)
  intro x
  obtain ⟨f, rfl⟩ := (exactRelations G).mkQ_surjective x
  change (exactRelations G).mkQ f ∈ LinearMap.range L
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro V _
  rw [← Finsupp.smul_single_one V (f V), map_smul]
  exact (LinearMap.range L).smul_mem (f V) (hgen _ V rfl)

open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open private coefficientFormula exactAdditivity tensorMultiplicativity weylInvariance characterOfBasis
  from LinearAlgebraicGroups.Representation.FormalCharacters
open private weylTransport characterValue_one from LinearAlgebraicGroups.Representation.RootWeightAction

private def restrictedCharacter {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    [IsCommMonObj T.group.X] {D : Datum T} (e : Identification D) (V : Rep G) :
    invariantRing (weylAction e) :=
  ⟨formalCharacter T V.action, (invariant_iff _ _).2
    fun w χ => weylInvariance hs e (fun ρ => weylTransport ρ e) V.action w χ⟩

private def restrictionLinear {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    [IsCommMonObj T.group.X] {D : Datum T} (e : Identification D) :
    K₀ G →ₗ[ℤ] invariantRing (weylAction e) := by
  let L := Finsupp.linearCombination ℤ (restrictedCharacter hs e)
  refine (exactRelations G).liftQ L (Submodule.span_le.mpr ?_)
  rintro _ ⟨U, V, W, ⟨seq⟩, rfl⟩
  apply LinearMap.mem_ker.mpr
  simp only [map_sub, map_add, L, Finsupp.linearCombination_single, one_smul, sub_eq_zero]
  apply Subtype.ext
  exact exactAdditivity T hs U.action V.action W.action seq.incl seq.proj
    seq.equivIncl seq.equivProj seq.injective seq.exactness seq.surjective

private theorem restrictionLinear_ofRep {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    [IsCommMonObj T.group.X] {D : Datum T} (e : Identification D) (V : Rep G) :
    restrictionLinear hs e (ofRep V) = restrictedCharacter hs e V := by
  change Finsupp.linearCombination ℤ (restrictedCharacter hs e) (Finsupp.single V 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

private theorem character_trivial (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) :
    formalCharacter T (Specs.CharacterRing.Rep.trivial G).action = 1 := by
  rw [characterOfBasis T hs (Specs.CharacterRing.Rep.trivial G).action (Pi.basisFun k PUnit.{u+1})
    (fun _ => 1)]
  · simp [MonoidAlgebra.one_def]
  · intro j
    apply Specs.RootWeightAction.mem_weightSpace.mpr
    intro R t
    rw [characterValue_one, one_smul]
    change (1 : Matrix PUnit.{u+1} PUnit.{u+1} R).mulVec _ = _
    exact Matrix.one_mulVec _

private theorem restriction_ring {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    [IsCommMonObj T.group.X] {D : Datum T} (e : Identification D)
    (bij : Function.Bijective (restrictionLinear hs e)) :
    let add₀ : Add (K₀ G) := inferInstance
    ∃ (ring : CommRing (K₀ G)), letI := ring
      letI : Add (K₀ G) := ⟨ring.add⟩
      (∀ x y : K₀ G, x + y = add₀.add x y) ∧
      (∀ V W : Rep G, ofRep (V.tensor W) = ofRep V * ofRep W) ∧
      ofRep (Specs.CharacterRing.Rep.trivial G) = 1 ∧
      ∃ restriction : K₀ G ≃+* invariantRing (weylAction e),
        ∀ V : Rep G, (restriction (ofRep V) : MonoidAlgebra ℤ (Character T.group)) =
          formalCharacter T V.action := by
  let l := LinearEquiv.ofBijective (restrictionLinear hs e) bij
  let f := l.toEquiv
  have hgen (V : Rep G) : f (ofRep V) = restrictedCharacter hs e V :=
    restrictionLinear_ofRep hs e V
  refine ⟨f.commRing, ?_, ?_, ?_, f.ringEquiv, fun V => congrArg Subtype.val (hgen V)⟩
  · intro x y
    change f.symm (f x + f y) = _
    exact f.symm_apply_eq.mpr (l.map_add x y).symm
  · intro V W
    apply f.injective
    change f (ofRep (V.tensor W)) = f (f.symm (f (ofRep V) * f (ofRep W)))
    rw [f.apply_symm_apply, hgen, hgen, hgen]
    apply Subtype.ext
    exact tensorMultiplicativity T hs V.action W.action
  · apply f.injective
    change f (ofRep (Specs.CharacterRing.Rep.trivial G)) = f (f.symm 1)
    rw [f.apply_symm_apply, hgen]
    exact Subtype.ext (character_trivial T hs)

end ExactSequences

section HighestWeights

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open Specs.AbstractPairing (Datum Root)
open Specs.DatumAndWeyl (Identification)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.RootWeightAction (SimpleRoot)
open Specs.DominantOrder (twoRhoCoroot)
open Specs.SimpleRoots (evaluate)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private coefficientFormula exactAdditivity tensorMultiplicativity weylInvariance
  from LinearAlgebraicGroups.Representation.FormalCharacters
open private weylTransport from LinearAlgebraicGroups.Representation.RootWeightAction
open private generates_of_simple from LinearAlgebraicGroups.Representation.PrimitiveLine
open private coordinateIso from LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private baseSimpleRoot from LinearAlgebraicGroups.Representation.ParabolicLineWeights

private theorem dominant_base_iff (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (b : D.rootDatum.Base)
    (simple : ∀ a : Root P.torus, a ∈ b.support ↔ ∃ x : SimpleRoot P.torus P.positive, x.val = a)
    (χ : Character P.torus.group) :
    Dominant P χ ↔ Specs.DominantOrder.IsDominant D.rootDatum b (Additive.ofMul χ) := by
  rw [LinearAlgebraicGroups.Representation.InducedNonvanishing.dominant_iff_datum
    LinearAlgebraicGroups.Classification.CentralIsogenies.centralIsogenyComparison P D χ]
  constructor
  · intro h a ha
    obtain ⟨x, rfl⟩ := (simple a).mp ha
    exact h x
  · intro h x
    exact h x.val ((simple x.val).mpr ⟨x, rfl⟩)

private theorem dominant_orbits (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    {D : Datum P.torus} (e : Identification D) (b : D.rootDatum.Base)
    (hdom : ∀ χ, Dominant P χ ↔ Specs.DominantOrder.IsDominant D.rootDatum b (Additive.ofMul χ))
    (horbit : ∀ χ : Additive (Character P.torus.group), ∃! ξ,
      Specs.DominantOrder.IsDominant D.rootDatum b ξ ∧
        ∃ w : D.rootDatum.weylGroup, w.val.weightEquiv χ = ξ) :
    (∀ χ, ∃ j : dominantWeights P, ∃ w, weylAction e w χ = j.val) ∧
    (∀ j l : dominantWeights P, (∃ w, weylAction e w j.val = l.val) ↔ j = l) := by
  constructor
  · intro χ
    obtain ⟨ξ, ⟨hd, w, hw⟩, _⟩ := horbit (Additive.ofMul χ)
    refine ⟨⟨Additive.toMul ξ, (hdom _).mpr hd⟩, w, ?_⟩
    exact Additive.ofMul.injective ((e.characterAction w χ).symm.trans hw)
  · intro j l
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨ξ, _, hu⟩ := horbit (Additive.ofMul j.val)
      have hj := hu (Additive.ofMul j.val) ⟨(hdom _).mp j.property, 1, by simp⟩
      have hl := hu (Additive.ofMul l.val) ⟨(hdom _).mp l.property, w,
        (e.characterAction w j.val).trans (congrArg Additive.ofMul hw)⟩
      exact Subtype.ext (Additive.ofMul.injective (hj.trans hl.symm))
    · rintro rfl
      exact ⟨1, by simp⟩

private theorem height_increases (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (f : Additive (Character P.torus.group) →ₗ[ℤ] ℤ)
    (nonnegative : ∀ j : dominantWeights P, 0 ≤ f (Additive.ofMul j.val))
    (simple : ∀ a : SimpleRoot P.torus P.positive, f (Additive.ofMul a.val.val) = 2)
    (j l : dominantWeights P) (hne : j ≠ l)
    (hle : Specs.RootWeightAction.DominanceLE P.torus P.positive l.val j.val) :
    (f (Additive.ofMul l.val)).toNat < (f (Additive.ofMul j.val)).toNat := by
  obtain ⟨c, hc⟩ := hle
  have hnonempty : c.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro hz
    subst c
    apply hne
    apply Subtype.ext
    exact div_eq_one.mp (by simpa using congrArg Additive.toMul hc)
  change Additive.ofMul j.val - Additive.ofMul l.val = _ at hc
  have heq := congrArg f hc
  simp only [map_sub, Finsupp.sum, map_sum, map_nsmul, simple] at heq
  have hp : 0 < ∑ i ∈ c.support, c i • (2 : ℤ) := by
    apply Finset.sum_pos (fun i hi => ?_) hnonempty
    have hn : 0 < c i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    rw [nsmul_eq_mul]
    positivity
  have hlt : f (Additive.ofMul l.val) < f (Additive.ofMul j.val) := by omega
  exact (Int.toNat_lt_toNat ((nonnegative l).trans_lt hlt)).mpr hlt

private theorem simple_characters (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (S : ∀ j : dominantWeights P, SocleModel P U j.val) :
    (∀ j, (formalCharacter P.torus (S j).socleAction).coeff j.val = 1) ∧
    (∀ j l : dominantWeights P, j ≠ l →
      (formalCharacter P.torus (S j).socleAction).coeff l.val ≠ 0 →
      Specs.RootWeightAction.DominanceLE P.torus P.positive l.val j.val) := by
  obtain ⟨comm, D, hhigh⟩ := CyclicHighestWeight.cyclicHighestWeight.2
    G P.reductive P.torus P.positive P.split P.maximal P.positiveBorel P.inPositive
  letI := comm
  constructor
  · intro j
    rw [(coefficientFormula P.torus P.split (S j).socleAction).2,
      Specs.FormalCharacters.multiplicity, (S j).highestLine,
      finrank_span_singleton (S j).primitive.1]
    rfl
  · intro j l hne hn
    let V := S j
    let v := V.socleBasis.equivFun V.highestVector
    have hgen := generates_of_simple CyclicHighestWeight.cyclicHighestWeight.1 V.socleAction
      _ (pointIso (coordinateIso G)) V.simple V.primitive.1
    have htop := ((hhigh U hU V.socleAction j.val v V.primitive).2 hgen).2.1
    apply htop l.val (fun h => hne (Subtype.ext h.symm))
    intro hb
    apply hn
    rw [(coefficientFormula P.torus P.split V.socleAction).2, Specs.FormalCharacters.multiplicity,
      hb, finrank_bot]
    rfl

private theorem characterRingFor (P : OppositeBorelPair G) [comm : IsCommMonObj P.torus.group.X]
    {D : Datum P.torus} (e : Identification D) [Finite D.rootDatum.weylGroup]
    (U : ClosedSubgroup P.positive.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (height : dominantWeights P → ℕ)
    (decreases : ∀ j l : dominantWeights P, j ≠ l →
      Specs.RootWeightAction.DominanceLE P.torus P.positive l.val j.val → height l < height j)
    (existsRep : ∀ χ, ∃ j : dominantWeights P, ∃ w, weylAction e w χ = j.val)
    (uniqueRep : ∀ j l : dominantWeights P, (∃ w, weylAction e w j.val = l.val) ↔ j = l) :
    ResultFor P := by
  classical
  obtain ⟨hasWeight, _, models⟩ := SimpleClassification.classification G P U hU
  choose S hS using fun j : dominantWeights P => models j.val j.property
  let i : dominantWeights P ↪ Character P.torus.group := ⟨Subtype.val, Subtype.val_injective⟩
  let o := orbitCoordinates (weylAction e) i existsRep uniqueRep
  let L := Finsupp.linearCombination ℤ (fun j => ofRep (simpleRep (S j)))
  let r := restrictionLinear P.split e
  have hL : Function.Surjective L := by
    apply span_of_simple
    intro V hV
    obtain ⟨χ, ⟨hχ, hw⟩, _⟩ := hasWeight V.action hV
    let j : dominantWeights P := ⟨χ, hχ⟩
    obtain ⟨f, hf⟩ := (hS j V.action hV).mpr hw
    exact ⟨j, class_iso f hf⟩
  let row (j : dominantWeights P) := o (restrictedCharacter P.split e (simpleRep (S j)))
  obtain ⟨diag, lower⟩ := simple_characters P U hU S
  have hrow (j l : dominantWeights P) :
      row j l = (formalCharacter P.torus (S j).socleAction).coeff l.val := rfl
  have hdiag (j : dominantWeights P) : row j j = 1 := (hrow j j).trans (diag j)
  have hlower (j l : dominantWeights P) (hne : j ≠ l) (hn : row j l ≠ 0) :=
    lower j l hne ((hrow j l) ▸ hn)
  have hcomp : o.toLinearMap.comp (r.comp L) = Finsupp.linearCombination ℤ row := by
    apply Finsupp.lhom_ext
    intro j n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, L, r,
      Finsupp.linearCombination_single, map_smul, restrictionLinear_ofRep, row]
  have hb := triangular_bijective height row hdiag
    (fun j l hne hn => decreases j l hne (hlower j l hne hn))
  rw [← hcomp] at hb
  have hLi : Function.Injective L := by
    intro v w h
    exact hb.1 (by change o (r (L v)) = o (r (L w)); rw [h])
  have hr : Function.Bijective r := by
    constructor
    · intro x y he
      obtain ⟨v, rfl⟩ := hL x
      obtain ⟨w, rfl⟩ := hL y
      exact congrArg L (hb.1 (congrArg o he))
    · intro x
      obtain ⟨v, hv⟩ := hb.2 (o x)
      exact ⟨L v, o.injective hv⟩
  let orbBasis := (Finsupp.basisSingleOne (R := ℤ)).map o.symm
  let simpBasis := (Finsupp.basisSingleOne (R := ℤ)).map (LinearEquiv.ofBijective L ⟨hLi, hL⟩)
  letI : Finite e.image.labels := e.image.finite
  refine ⟨coefficientFormula P.torus P.split, exactAdditivity P.torus P.split,
    tensorMultiplicativity P.torus P.split, comm, D, e, U, hU,
    weylInvariance P.split e (fun ρ => weylTransport ρ e), S, orbBasis, simpBasis,
    ?_, ?_, ?_, restriction_ring P.split e hr⟩
  · intro j
    have h : orbBasis j = invariantOrbitSum (weylAction e) (i j) := by
      apply o.injective
      change o (o.symm (Finsupp.single j 1)) = _
      rw [o.apply_symm_apply]
      exact (coordinates_orbitSum _ _ uniqueRep j).symm
    exact congrArg Subtype.val h
  · intro j
    change L (Finsupp.single j 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  · intro j
    let c := row j - Finsupp.single j 1
    refine ⟨c, ?_, ?_⟩
    · intro l hl
      have hn := Finsupp.mem_support_iff.mp hl
      have hne : j ≠ l := by
        rintro rfl
        exact hn (by simp [c, hdiag])
      exact ⟨hne.symm, hlower j l hne (by simpa [c, Finsupp.single_apply, hne] using hn)⟩
    · let sumOrbits := Finsupp.linearCombination ℤ
        (fun l : dominantWeights P => invariantOrbitSum (weylAction e) (i l))
      have hcomb : o.toLinearMap.comp sumOrbits = LinearMap.id :=
        coordinates_orbitExpansion _ _ uniqueRep
      have he : restrictedCharacter P.split e (simpleRep (S j)) =
          invariantOrbitSum (weylAction e) (i j) + sumOrbits c := by
        apply o.injective
        rw [map_add, show o (invariantOrbitSum (weylAction e) (i j)) = Finsupp.single j 1 from
          coordinates_orbitSum _ _ uniqueRep j]
        have hc : o (sumOrbits c) = c := DFunLike.congr_fun hcomb c
        rw [hc]
        change row j = Finsupp.single j 1 + (row j - Finsupp.single j 1)
        abel
      let coe := (invariantRing (weylAction e)).subtype.toAddMonoidHom.toIntLinearMap
      have hcoe := congrArg coe he
      rw [map_add] at hcoe
      change _ = _ + coe (sumOrbits c) at hcoe
      rw [show coe (sumOrbits c) = c.sum (fun l n => n • orbitSum (weylAction e) l.val) from by
        rw [show sumOrbits c = c.sum (fun l n => n • invariantOrbitSum (weylAction e) (i l)) from rfl,
          map_finsuppSum]
        simp only [map_smul]
        rfl] at hcoe
      exact hcoe

private theorem resultFor (P : OppositeBorelPair G) : ResultFor P := by
  classical
  have hG := P.reductive
  obtain ⟨comm, D, ⟨e⟩, order⟩ := DominantOrder.dominantOrder
    G hG P.torus P.split P.maximal
  letI := comm
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  letI := e.image.finite
  letI : Finite D.rootDatum.weylGroup := Finite.of_injective e.labelEquiv e.labelEquiv.injective
  obtain ⟨_, _, _, borels, _, _, radicals⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G hG P.torus P.split P.maximal
  obtain ⟨U, _, _, hU, _⟩ := radicals P.positive P.positiveBorel P.inPositive
  obtain ⟨c, _, hc, _, hp⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      G hG P.torus P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  have hreg (a : Root P.torus) : evaluate D c (D.rootDatum.root a) ≠ 0 := by
    change D.rootDatum.toLinearMap (D.rootDatum.root a) (Additive.ofMul c) ≠ 0
    rw [D.root_eq, D.pairing_eq]
    exact hc a
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.RootData.SimpleRoots.baseFor D.rootDatum (evaluate D c) hreg
  let positives := subgroupRoots P.torus P.positive
  have hb' : Specs.DominantOrder.IsBaseFor D.rootDatum positives b := by
    intro a
    change b.IsPos a ↔ a ∈ subgroupRoots P.torus P.positive
    rw [hb.positive_iff, hp]
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root a) (Additive.ofMul c) ↔ _
    rw [D.root_eq, D.pairing_eq]
    rfl
  have laws := (order positives (borels.1 P.positive P.positiveBorel P.inPositive)).2 b hb'
  have simple (a : Root P.torus) : a ∈ b.support ↔
      ∃ x : SimpleRoot P.torus P.positive, x.val = a := baseSimpleRoot hp.symm hb a
  have hdom := dominant_base_iff P D b simple
  obtain ⟨hex, hu⟩ := dominant_orbits P e b hdom laws.orbitRepresentative
  let f := D.rootDatum.toLinearMap.flip (twoRhoCoroot D.rootDatum positives)
  have hnonneg (j : dominantWeights P) := laws.nonnegative _ ((hdom _).mp j.property)
  have hsimple (a : SimpleRoot P.torus P.positive) : f (Additive.ofMul a.val.val) = 2 := by
    rw [← D.root_eq]
    exact laws.simplePairing a.val ((simple a.val).mpr ⟨a, rfl⟩)
  exact characterRingFor P e U hU (fun j => (f (Additive.ofMul j.val)).toNat)
    (height_increases P f hnonneg hsimple) hex hu

/-- Restriction to the marked split maximal torus identifies the Grothendieck
ring of finite-dimensional rational representations with the Weyl invariants. -/
theorem characterRing : Statement.{u} := by
  intro k _ G hG T B hT hmax hB hTB
  obtain ⟨_, _, _, borels, _⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G hG T hT hmax
  obtain ⟨f, hf, hpos⟩ := borels.1 B hB hTB
  have hneg : Specs.BorelsAndChambers.IsPositiveSystem T (subgroupRoots T B)ᶜ := by
    refine ⟨-f, fun a h => hf a (neg_eq_zero.mp h), ?_⟩
    rw [hpos]
    ext a
    change ¬ 0 < f (Additive.ofMul a.val) ↔ 0 < -f (Additive.ofMul a.val)
    rw [not_lt, neg_pos]
    exact ⟨fun h => lt_of_le_of_ne h (hf a), le_of_lt⟩
  obtain ⟨N, hN, hTN, hOpp⟩ := borels.2.1 _ hneg
  let P : OppositeBorelPair G := ⟨T, B, N, hG, hT, hmax, hB, hN, hTB, hTN, hOpp⟩
  exact ⟨P, rfl, rfl, resultFor P⟩

end HighestWeights

end
end LinearAlgebraicGroups.Representation.CharacterRing
