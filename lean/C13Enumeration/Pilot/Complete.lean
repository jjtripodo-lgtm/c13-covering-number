import C13Enumeration.Pilot.Source01
import C13Enumeration.Pilot.Source02
import C13Enumeration.Pilot.Source03
import C13Enumeration.Pilot.Source04
import C13Enumeration.Pilot.Source05
import C13Enumeration.Pilot.Source06
import C13Enumeration.Pilot.Source07
import C13Enumeration.Pilot.Source08
import C13Enumeration.Pilot.Source09
import C13Enumeration.Pilot.Source10
import C13Enumeration.Pilot.Source11
import C13Enumeration.Pilot.Source12
import C13Enumeration.Pilot.Source13
import C13Enumeration.Pilot.Source14
import C13Enumeration.Pilot.Source15
import C13Enumeration.Pilot.Source16
import C13Enumeration.Pilot.Source17
import C13Enumeration.Pilot.Source18
import C13Enumeration.Pilot.Source19
import C13Enumeration.Pilot.Source20
import C13Enumeration.Pilot.Source21
import C13Enumeration.Pilot.Source22
import C13Enumeration.Pilot.Source23
import C13Enumeration.Pilot.Source24
import C13Enumeration.Pilot.Source25
import C13Enumeration.Pilot.Source26
import C13Enumeration.Pilot.Source27
import C13Enumeration.Pilot.Source28
import C13Enumeration.Pilot.Source29
import C13Enumeration.Pilot.Source30
import C13Enumeration.Pilot.Source31
import C13Enumeration.Pilot.Source32
import C13Enumeration.Pilot.Source33
import C13Enumeration.Pilot.Source34
import C13Enumeration.Pilot.Source35
import C13Enumeration.Pilot.Source36
import C13Enumeration.Pilot.Source37
import C13Enumeration.Pilot.Source38
import C13Enumeration.Pilot.Source39
import C13Enumeration.Pilot.Source40
import C13Enumeration.Pilot.Source41
import C13Enumeration.Pilot.Source42
import C13Enumeration.Pilot.Source43
import C13Enumeration.Pilot.Source44
import C13Enumeration.Pilot.Source45
import C13Enumeration.Pilot.Source46
import C13Enumeration.Pilot.Source47
import C13Enumeration.Pilot.Source48
import C13Enumeration.Pilot.Source49
import C13Enumeration.Pilot.Source50
import C13Enumeration.Pilot.Source51
import C13Enumeration.Pilot.Source52
import C13Enumeration.Pilot.Source53
import C13Enumeration.Pilot.Source54
import C13Enumeration.Pilot.Source55
import C13Enumeration.Pilot.Source56
import C13Enumeration.Pilot.Source57
import C13Enumeration.Pilot.Source58
import C13Enumeration.Pilot.Source59
import C13Enumeration.Pilot.Source60
import C13Enumeration.Pilot.Source61
import C13Enumeration.Pilot.Source62
import C13Enumeration.Pilot.Source63
import C13Enumeration.Pilot.Source64
import C13Enumeration.Pilot.Source65
import C13Enumeration.Pilot.Source66
import C13Enumeration.Pilot.Source67
import C13Enumeration.Pilot.Source68
namespace C13.Enumeration.Pilot
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000

def CompleteSource (K : Family Point) : Prop :=
  ∀ (c : Point) (e : Equiv.Perm Point), e hole = 0 → e c = hole →
    transport e (link K c) = link link01 0 → emitPencil K c 0 e = expected

theorem ordinary_sources_complete : ∀ K ∈ ordinaryList, CompleteSource K := by
  simp only [ordinaryList,List.forall_mem_cons,List.forall_mem_nil,and_true]
  exact ⟨Source01.complete,Source02.complete,Source03.complete,Source04.complete,Source05.complete,Source06.complete,Source07.complete,Source08.complete,Source09.complete,Source10.complete,Source11.complete,Source12.complete,Source13.complete,Source14.complete,Source15.complete,Source16.complete,Source17.complete,Source18.complete,Source19.complete,Source20.complete,Source21.complete,Source22.complete,Source23.complete,Source24.complete,Source25.complete,Source26.complete,Source27.complete,Source28.complete,Source29.complete,Source30.complete,Source31.complete,Source32.complete,Source33.complete,Source34.complete,Source35.complete,Source36.complete,Source37.complete,Source38.complete,Source39.complete,Source40.complete,Source41.complete,Source42.complete,Source43.complete,Source44.complete,Source45.complete,Source46.complete,Source47.complete,Source48.complete,Source49.complete,Source50.complete,Source51.complete,Source52.complete,Source53.complete,Source54.complete,Source55.complete,Source56.complete,Source57.complete,Source58.complete,Source59.complete,Source60.complete,Source61.complete,Source62.complete,Source63.complete,Source64.complete,Source65.complete,Source66.complete,Source67.complete,(by intro x hx; simp at hx)⟩

#check ordinary_sources_complete

/-- All 68 catalog families, all twelve source centers, and unrestricted maps. -/
theorem every_source_pencil_eq (K : Family Point) (hK : K ∈ catalog)
    (c : Point) (e : Equiv.Perm Point) (he : e hole = 0) (hc : e c = hole)
    (hs : transport e (link K c) = link link01 0) : emitPencil K c 0 e = expected := by
  obtain h | h := Finset.mem_insert.mp hK
  · subst K
    exact Source68.complete c e he hc hs
  · exact ordinary_sources_complete K (List.mem_toFinset.mp h) c e he hc hs

#check every_source_pencil_eq

theorem expected_mem_completeDomain : expected ∈ completeDomain catalog hole link01 hole 0 := by
  apply (mem_completeDomain_iff ..).mpr
  refine ⟨link01,?_,Equiv.swap hole 0,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#check expected_mem_completeDomain

/-- The actual semantic full domain, not a filtered residual or chosen-source subset. -/
theorem complete_domain_eq_singleton : completeDomain catalog hole link01 hole 0 = {expected} := by
  ext P
  constructor
  · intro hP
    obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
      C13.Raw.completeDomain_has_punctured_witness catalog hole link01 hole 0
        (by decide +kernel) (by simp [link01,hole]) P hP
    have hp := every_source_pencil_eq K hK c e he hce hstar
    have hemit : emitPencil K c 0 e = P := by
      unfold emitPencil
      rw [mapFamily_equiv]
      exact hout
    exact Finset.mem_singleton.mpr (hemit.symm.trans hp)
  · intro hP
    have hp := Finset.mem_singleton.mp hP
    exact hp.symm ▸ expected_mem_completeDomain
end C13.Enumeration.Pilot
