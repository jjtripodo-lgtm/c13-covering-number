import C13Enumeration.RawClass9.CoverageQ6Source01
import C13Enumeration.RawClass9.CoverageQ6Source02
import C13Enumeration.RawClass9.CoverageQ6Source03
import C13Enumeration.RawClass9.CoverageQ6Source04
import C13Enumeration.RawClass9.CoverageQ6Source05
import C13Enumeration.RawClass9.CoverageQ6Source06
import C13Enumeration.RawClass9.CoverageQ6Source07
import C13Enumeration.RawClass9.CoverageQ6Source08
import C13Enumeration.RawClass9.CoverageQ6Source09
import C13Enumeration.RawClass9.CoverageQ6Source10
import C13Enumeration.RawClass9.CoverageQ6Source11
import C13Enumeration.RawClass9.CoverageQ6Source12
import C13Enumeration.RawClass9.CoverageQ6Source13
import C13Enumeration.RawClass9.CoverageQ6Source14
import C13Enumeration.RawClass9.CoverageQ6Source15
import C13Enumeration.RawClass9.CoverageQ6Source16
import C13Enumeration.RawClass9.CoverageQ6Source17
import C13Enumeration.RawClass9.CoverageQ6Source18
import C13Enumeration.RawClass9.CoverageQ6Source19
import C13Enumeration.RawClass9.CoverageQ6Source20
import C13Enumeration.RawClass9.CoverageQ6Source21
import C13Enumeration.RawClass9.CoverageQ6Source22
import C13Enumeration.RawClass9.CoverageQ6Source23
import C13Enumeration.RawClass9.CoverageQ6Source24
import C13Enumeration.RawClass9.CoverageQ6Source25
import C13Enumeration.RawClass9.CoverageQ6Source26
import C13Enumeration.RawClass9.CoverageQ6Source27
import C13Enumeration.RawClass9.CoverageQ6Source28
import C13Enumeration.RawClass9.CoverageQ6Source29
import C13Enumeration.RawClass9.CoverageQ6Source30
import C13Enumeration.RawClass9.CoverageQ6Source31
import C13Enumeration.RawClass9.CoverageQ6Source32
import C13Enumeration.RawClass9.CoverageQ6Source33
import C13Enumeration.RawClass9.CoverageQ6Source34
import C13Enumeration.RawClass9.CoverageQ6Source35
import C13Enumeration.RawClass9.CoverageQ6Source36
import C13Enumeration.RawClass9.CoverageQ6Source37
import C13Enumeration.RawClass9.CoverageQ6Source38
import C13Enumeration.RawClass9.CoverageQ6Source39
import C13Enumeration.RawClass9.CoverageQ6Source40
import C13Enumeration.RawClass9.CoverageQ6Source41
import C13Enumeration.RawClass9.CoverageQ6Source42
import C13Enumeration.RawClass9.CoverageQ6Source43
import C13Enumeration.RawClass9.CoverageQ6Source44
import C13Enumeration.RawClass9.CoverageQ6Source45
import C13Enumeration.RawClass9.CoverageQ6Source46
import C13Enumeration.RawClass9.CoverageQ6Source47
import C13Enumeration.RawClass9.CoverageQ6Source48
import C13Enumeration.RawClass9.CoverageQ6Source49
import C13Enumeration.RawClass9.CoverageQ6Source50
import C13Enumeration.RawClass9.CoverageQ6Source51
import C13Enumeration.RawClass9.CoverageQ6Source52
import C13Enumeration.RawClass9.CoverageQ6Source53
import C13Enumeration.RawClass9.CoverageQ6Source54
import C13Enumeration.RawClass9.CoverageQ6Source55
import C13Enumeration.RawClass9.CoverageQ6Source56
import C13Enumeration.RawClass9.CoverageQ6Source57
import C13Enumeration.RawClass9.CoverageQ6Source58
import C13Enumeration.RawClass9.CoverageQ6Source59
import C13Enumeration.RawClass9.CoverageQ6Source60
import C13Enumeration.RawClass9.CoverageQ6Source61
import C13Enumeration.RawClass9.CoverageQ6Source62
import C13Enumeration.RawClass9.CoverageQ6Source63
import C13Enumeration.RawClass9.CoverageQ6Source64
import C13Enumeration.RawClass9.CoverageQ6Source65
import C13Enumeration.RawClass9.CoverageQ6Source66
import C13Enumeration.RawClass9.CoverageQ6Source67
import C13Enumeration.RawClass9.CoverageQ6Source68
namespace C13.Enumeration.RawClass9.Domain6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000

def SourceRepresented (K : Family Point) : Prop :=
  ∀ (c : Point) (e : Equiv.Perm Point), e hole = 6 → e c = hole →
    transport e (link K c) = link link09 6 →
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil K c 6 e)

theorem ordinary_sources_complete : ∀ K ∈ ordinaryList, SourceRepresented K := by
  simp only [ordinaryList,List.forall_mem_cons]
  exact ⟨CoverageQ6Source01.complete,CoverageQ6Source02.complete,CoverageQ6Source03.complete,CoverageQ6Source04.complete,CoverageQ6Source05.complete,CoverageQ6Source06.complete,CoverageQ6Source07.complete,CoverageQ6Source08.complete,CoverageQ6Source09.complete,CoverageQ6Source10.complete,CoverageQ6Source11.complete,CoverageQ6Source12.complete,CoverageQ6Source13.complete,CoverageQ6Source14.complete,CoverageQ6Source15.complete,CoverageQ6Source16.complete,CoverageQ6Source17.complete,CoverageQ6Source18.complete,CoverageQ6Source19.complete,CoverageQ6Source20.complete,CoverageQ6Source21.complete,CoverageQ6Source22.complete,CoverageQ6Source23.complete,CoverageQ6Source24.complete,CoverageQ6Source25.complete,CoverageQ6Source26.complete,CoverageQ6Source27.complete,CoverageQ6Source28.complete,CoverageQ6Source29.complete,CoverageQ6Source30.complete,CoverageQ6Source31.complete,CoverageQ6Source32.complete,CoverageQ6Source33.complete,CoverageQ6Source34.complete,CoverageQ6Source35.complete,CoverageQ6Source36.complete,CoverageQ6Source37.complete,CoverageQ6Source38.complete,CoverageQ6Source39.complete,CoverageQ6Source40.complete,CoverageQ6Source41.complete,CoverageQ6Source42.complete,CoverageQ6Source43.complete,CoverageQ6Source44.complete,CoverageQ6Source45.complete,CoverageQ6Source46.complete,CoverageQ6Source47.complete,CoverageQ6Source48.complete,CoverageQ6Source49.complete,CoverageQ6Source50.complete,CoverageQ6Source51.complete,CoverageQ6Source52.complete,CoverageQ6Source53.complete,CoverageQ6Source54.complete,CoverageQ6Source55.complete,CoverageQ6Source56.complete,CoverageQ6Source57.complete,CoverageQ6Source58.complete,CoverageQ6Source59.complete,CoverageQ6Source60.complete,CoverageQ6Source61.complete,CoverageQ6Source62.complete,CoverageQ6Source63.complete,CoverageQ6Source64.complete,CoverageQ6Source65.complete,CoverageQ6Source66.complete,CoverageQ6Source67.complete,(by intro x hx; simp at hx)⟩

theorem every_source (K : Family Point) (hK : K ∈ catalog) : SourceRepresented K := by
  obtain h | h := Finset.mem_insert.mp hK
  · subst K
    exact CoverageQ6Source68.complete
  · exact ordinary_sources_complete K (List.mem_toFinset.mp h)

/-- Completeness for the entire actual raw point-labelled domain, before any support or arc filter. -/
theorem complete_raw_domain : raw6.supported.domain.1 = (6 : Point).val ∧
    ∀ P ∈ completeDomain catalog hole link09 hole 6,
      ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p P := by
  refine ⟨rfl,?_⟩
  intro P hP
  obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
    C13.Raw.completeDomain_has_punctured_witness catalog hole link09 hole 6
      (by decide +kernel) (by simp [link09,hole]) P hP
  obtain ⟨p,hp,hrep⟩ := every_source K hK c e he hce hstar
  have hPout : emitPencil K c 6 e = P := by
    unfold emitPencil
    rw [mapFamily_equiv]
    exact hout
  exact ⟨p,hp,hPout ▸ hrep⟩
end C13.Enumeration.RawClass9.Domain6
