import C13Enumeration.DegreeEightPilot.Source01
import C13Enumeration.DegreeEightPilot.Source02
import C13Enumeration.DegreeEightPilot.Source03
import C13Enumeration.DegreeEightPilot.Source04
import C13Enumeration.DegreeEightPilot.Source05
import C13Enumeration.DegreeEightPilot.Source06
import C13Enumeration.DegreeEightPilot.Source07
import C13Enumeration.DegreeEightPilot.Source08
import C13Enumeration.DegreeEightPilot.Source09
import C13Enumeration.DegreeEightPilot.Source10
import C13Enumeration.DegreeEightPilot.Source11
import C13Enumeration.DegreeEightPilot.Source12
import C13Enumeration.DegreeEightPilot.Source13
import C13Enumeration.DegreeEightPilot.Source14
import C13Enumeration.DegreeEightPilot.Source15
import C13Enumeration.DegreeEightPilot.Source16
import C13Enumeration.DegreeEightPilot.Source17
import C13Enumeration.DegreeEightPilot.Source18
import C13Enumeration.DegreeEightPilot.Source19
import C13Enumeration.DegreeEightPilot.Source20
import C13Enumeration.DegreeEightPilot.Source21
import C13Enumeration.DegreeEightPilot.Source22
import C13Enumeration.DegreeEightPilot.Source23
import C13Enumeration.DegreeEightPilot.Source24
import C13Enumeration.DegreeEightPilot.Source25
import C13Enumeration.DegreeEightPilot.Source26
import C13Enumeration.DegreeEightPilot.Source27
import C13Enumeration.DegreeEightPilot.Source28
import C13Enumeration.DegreeEightPilot.Source29
import C13Enumeration.DegreeEightPilot.Source30
import C13Enumeration.DegreeEightPilot.Source31
import C13Enumeration.DegreeEightPilot.Source32
import C13Enumeration.DegreeEightPilot.Source33
import C13Enumeration.DegreeEightPilot.Source34
import C13Enumeration.DegreeEightPilot.Source35
import C13Enumeration.DegreeEightPilot.Source36
import C13Enumeration.DegreeEightPilot.Source37
import C13Enumeration.DegreeEightPilot.Source38
import C13Enumeration.DegreeEightPilot.Source39
import C13Enumeration.DegreeEightPilot.Source40
import C13Enumeration.DegreeEightPilot.Source41
import C13Enumeration.DegreeEightPilot.Source42
import C13Enumeration.DegreeEightPilot.Source43
import C13Enumeration.DegreeEightPilot.Source44
import C13Enumeration.DegreeEightPilot.Source45
import C13Enumeration.DegreeEightPilot.Source46
import C13Enumeration.DegreeEightPilot.Source47
import C13Enumeration.DegreeEightPilot.Source48
import C13Enumeration.DegreeEightPilot.Source49
import C13Enumeration.DegreeEightPilot.Source50
import C13Enumeration.DegreeEightPilot.Source51
import C13Enumeration.DegreeEightPilot.Source52
import C13Enumeration.DegreeEightPilot.Source53
import C13Enumeration.DegreeEightPilot.Source54
import C13Enumeration.DegreeEightPilot.Source55
import C13Enumeration.DegreeEightPilot.Source56
import C13Enumeration.DegreeEightPilot.Source57
import C13Enumeration.DegreeEightPilot.Source58
import C13Enumeration.DegreeEightPilot.Source59
import C13Enumeration.DegreeEightPilot.Source60
import C13Enumeration.DegreeEightPilot.Source61
import C13Enumeration.DegreeEightPilot.Source62
import C13Enumeration.DegreeEightPilot.Source63
import C13Enumeration.DegreeEightPilot.Source64
import C13Enumeration.DegreeEightPilot.Source65
import C13Enumeration.DegreeEightPilot.Source66
import C13Enumeration.DegreeEightPilot.Source67
import C13Enumeration.DegreeEightPilot.Source68
namespace C13.Enumeration.DegreeEightPilot
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def SourceRepresented (K : Family Point) : Prop :=
  ∀ (c : Point) (e : Equiv.Perm Point), e hole = 4 → e c = hole →
    transport e (link K c) = link link01 4 →
    ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p (emitPencil K c 4 e)

theorem ordinary_sources_complete : ∀ K ∈ ordinaryList, SourceRepresented K := by
  simp only [ordinaryList,List.forall_mem_cons]
  exact ⟨Source01.complete,Source02.complete,Source03.complete,Source04.complete,Source05.complete,Source06.complete,Source07.complete,Source08.complete,Source09.complete,Source10.complete,Source11.complete,Source12.complete,Source13.complete,Source14.complete,Source15.complete,Source16.complete,Source17.complete,Source18.complete,Source19.complete,Source20.complete,Source21.complete,Source22.complete,Source23.complete,Source24.complete,Source25.complete,Source26.complete,Source27.complete,Source28.complete,Source29.complete,Source30.complete,Source31.complete,Source32.complete,Source33.complete,Source34.complete,Source35.complete,Source36.complete,Source37.complete,Source38.complete,Source39.complete,Source40.complete,Source41.complete,Source42.complete,Source43.complete,Source44.complete,Source45.complete,Source46.complete,Source47.complete,Source48.complete,Source49.complete,Source50.complete,Source51.complete,Source52.complete,Source53.complete,Source54.complete,Source55.complete,Source56.complete,Source57.complete,Source58.complete,Source59.complete,Source60.complete,Source61.complete,Source62.complete,Source63.complete,Source64.complete,Source65.complete,Source66.complete,Source67.complete,(by intro x hx; simp at hx)⟩

theorem every_source (K : Family Point) (hK : K ∈ catalog) : SourceRepresented K := by
  obtain h | h := Finset.mem_insert.mp hK
  · subst K; exact Source68.complete
  · exact ordinary_sources_complete K (List.mem_toFinset.mp h)

theorem complete_decoded_domain :
    codedDomain.supported.domain.1 = (4 : Point).val ∧
    ∀ P ∈ completeDomain catalog hole link01 hole 4,
      ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p P := by
  refine ⟨rfl,?_⟩
  intro P hP
  obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
    C13.Raw.completeDomain_has_punctured_witness catalog hole link01 hole 4
      (by decide +kernel) (by simp [link01,hole]) P hP
  obtain ⟨p,hp,hrep⟩ := every_source K hK c e he hce hstar
  have hPout : emitPencil K c 4 e = P := by
    unfold emitPencil
    rw [mapFamily_equiv]
    exact hout
  exact ⟨p,hp,hPout ▸ hrep⟩
end C13.Enumeration.DegreeEightPilot
