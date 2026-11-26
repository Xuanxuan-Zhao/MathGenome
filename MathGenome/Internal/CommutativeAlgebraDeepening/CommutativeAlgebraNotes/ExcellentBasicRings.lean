import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellentBasicRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.BasicGRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.OpenRegularLocus
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover

/-! Excellence of complete Noetherian local rings, fields, the integers,
and finite-type algebras over fields or the integers. -/

namespace CommutativeAlgebraNotes.Excellence

universe u v w

open AdvCommAlg.CohenMacaulay
  (CohenMacaulayRing regularLocal_cohenMacaulay regularLocal_localization_atPrime universally_catenary)

private theorem catenary_of_regular_base (S : Type u) (B : Type v) [CommRing S] [CommRing B]
    [IsRegularRing S] [Algebra S B] [Algebra.FiniteType S B] : Catenary B := by
  let := Algebra.FiniteType.isNoetherianRing S B
  have hCM : CohenMacaulayRing S := by
    intro p
    exact regularLocal_cohenMacaulay (Localization.AtPrime p.asIdeal)
  exact (catenary_iff B).mpr (universally_catenary S hCM B)

private theorem finiteType_compHom {S : Type u} {R : Type v} (B : Type w)
    [CommRing S] [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    {f : S →+* R} (hf : f.FiniteType) :
    letI := Algebra.compHom B f
    Algebra.FiniteType S B := by
  let := Algebra.compHom B f
  apply RingHom.finiteType_algebraMap.mp
  exact (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType R B)).comp hf

/-- A complete Noetherian local ring is excellent. -/
theorem completeLocal_excellent : Specs.completeLocal_excellentType.{u} := by
  intro R _ _ _ _
  refine ⟨inferInstance, completeLocal_isGRing R, ?_, ?_⟩
  · intro B _ _ _
    exact isOpen_regularLocus_completeLocal R B
  · obtain ⟨S, _, _, _, f, _, hf, _⟩ := CoefficientRings.completeRegularCover R
    let : IsRegularRing S := isRegularRing_iff.mpr (regularLocal_localization_atPrime S)
    intro B _ _ _
    let := Algebra.compHom B f
    let := finiteType_compHom B (RingHom.FiniteType.of_surjective f hf)
    exact catenary_of_regular_base S B

/-- A finite-type algebra over a field is excellent. -/
theorem finiteTypeField_excellent : Specs.finiteTypeField_excellentType.{u,v} := by
  intro k R _ _ _ _
  let := Algebra.FiniteType.isNoetherianRing k R
  have h (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
      IsOpen (regularLocus B) ∧ Catenary B := by
    let := Algebra.compHom B (algebraMap k R)
    let := finiteType_compHom B (RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType k R))
    exact ⟨isOpen_regularLocus_field k B, catenary_of_regular_base k B⟩
  exact ⟨inferInstance, finiteTypeField_isGRing k R,
    fun B _ _ _ => (h B).1, fun B _ _ _ => (h B).2⟩

/-- A finite-type algebra over the integers is excellent. -/
theorem finiteTypeInt_excellent : Specs.finiteTypeInt_excellentType.{u} := by
  intro R _ _
  let := Algebra.FiniteType.isNoetherianRing ℤ R
  have h (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
      IsOpen (regularLocus B) ∧ Catenary B := by
    let : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType ℤ R) (inferInstance : Algebra.FiniteType R B)
    exact ⟨isOpen_regularLocus_int B, catenary_of_regular_base ℤ B⟩
  exact ⟨inferInstance, finiteTypeInt_isGRing R,
    fun B _ _ _ => (h B).1, fun B _ _ _ => (h B).2⟩

theorem field_excellent : Specs.field_excellentType.{u} := by
  intro k _
  exact finiteTypeField_excellent k k

theorem int_excellent : Specs.int_excellentType :=
  finiteTypeInt_excellent ℤ

end CommutativeAlgebraNotes.Excellence
