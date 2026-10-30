import C13Enumeration.RawClass9.CoverageQ8Source01
import C13Enumeration.RawClass9.CoverageQ8Source02
import C13Enumeration.RawClass9.CoverageQ8Source03
import C13Enumeration.RawClass9.CoverageQ8Source04
import C13Enumeration.RawClass9.CoverageQ8Source05
import C13Enumeration.RawClass9.CoverageQ8Source06
import C13Enumeration.RawClass9.CoverageQ8Source07
import C13Enumeration.RawClass9.CoverageQ8Source08
import C13Enumeration.RawClass9.CoverageQ8Source09
import C13Enumeration.RawClass9.CoverageQ8Source10
import C13Enumeration.RawClass9.CoverageQ8Source11
import C13Enumeration.RawClass9.CoverageQ8Source12
import C13Enumeration.RawClass9.CoverageQ8Source13
import C13Enumeration.RawClass9.CoverageQ8Source14
import C13Enumeration.RawClass9.CoverageQ8Source15
import C13Enumeration.RawClass9.CoverageQ8Source16
import C13Enumeration.RawClass9.CoverageQ8Source17
import C13Enumeration.RawClass9.CoverageQ8Source18
import C13Enumeration.RawClass9.CoverageQ8Source19
import C13Enumeration.RawClass9.CoverageQ8Source20
import C13Enumeration.RawClass9.CoverageQ8Source21
import C13Enumeration.RawClass9.CoverageQ8Source22
import C13Enumeration.RawClass9.CoverageQ8Source23
import C13Enumeration.RawClass9.CoverageQ8Source24
import C13Enumeration.RawClass9.CoverageQ8Source25
import C13Enumeration.RawClass9.CoverageQ8Source26
import C13Enumeration.RawClass9.CoverageQ8Source27
import C13Enumeration.RawClass9.CoverageQ8Source28
import C13Enumeration.RawClass9.CoverageQ8Source29
import C13Enumeration.RawClass9.CoverageQ8Source30
import C13Enumeration.RawClass9.CoverageQ8Source31
import C13Enumeration.RawClass9.CoverageQ8Source32
import C13Enumeration.RawClass9.CoverageQ8Source33
import C13Enumeration.RawClass9.CoverageQ8Source34
import C13Enumeration.RawClass9.CoverageQ8Source35
import C13Enumeration.RawClass9.CoverageQ8Source36
import C13Enumeration.RawClass9.CoverageQ8Source37
import C13Enumeration.RawClass9.CoverageQ8Source38
import C13Enumeration.RawClass9.CoverageQ8Source39
import C13Enumeration.RawClass9.CoverageQ8Source40
import C13Enumeration.RawClass9.CoverageQ8Source41
import C13Enumeration.RawClass9.CoverageQ8Source42
import C13Enumeration.RawClass9.CoverageQ8Source43
import C13Enumeration.RawClass9.CoverageQ8Source44
import C13Enumeration.RawClass9.CoverageQ8Source45
import C13Enumeration.RawClass9.CoverageQ8Source46
import C13Enumeration.RawClass9.CoverageQ8Source47
import C13Enumeration.RawClass9.CoverageQ8Source48
import C13Enumeration.RawClass9.CoverageQ8Source49
import C13Enumeration.RawClass9.CoverageQ8Source50
import C13Enumeration.RawClass9.CoverageQ8Source51
import C13Enumeration.RawClass9.CoverageQ8Source52
import C13Enumeration.RawClass9.CoverageQ8Source53
import C13Enumeration.RawClass9.CoverageQ8Source54
import C13Enumeration.RawClass9.CoverageQ8Source55
import C13Enumeration.RawClass9.CoverageQ8Source56
import C13Enumeration.RawClass9.CoverageQ8Source57
import C13Enumeration.RawClass9.CoverageQ8Source58
import C13Enumeration.RawClass9.CoverageQ8Source59
import C13Enumeration.RawClass9.CoverageQ8Source60
import C13Enumeration.RawClass9.CoverageQ8Source61
import C13Enumeration.RawClass9.CoverageQ8Source62
import C13Enumeration.RawClass9.CoverageQ8Source63
import C13Enumeration.RawClass9.CoverageQ8Source64
import C13Enumeration.RawClass9.CoverageQ8Source65
import C13Enumeration.RawClass9.CoverageQ8Source66
import C13Enumeration.RawClass9.CoverageQ8Source67
import C13Enumeration.RawClass9.CoverageQ8Source68
namespace C13.Enumeration.RawClass9.Domain8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000

def SourceRepresented (K : Family Point) : Prop :=
  ∀ (c : Point) (e : Equiv.Perm Point), e hole = 8 → e c = hole →
    transport e (link K c) = link link09 8 →
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil K c 8 e)

theorem ordinary_sources_complete : ∀ K ∈ ordinaryList, SourceRepresented K := by
  simp only [ordinaryList,List.forall_mem_cons]
  exact ⟨CoverageQ8Source01.complete,CoverageQ8Source02.complete,CoverageQ8Source03.complete,CoverageQ8Source04.complete,CoverageQ8Source05.complete,CoverageQ8Source06.complete,CoverageQ8Source07.complete,CoverageQ8Source08.complete,CoverageQ8Source09.complete,CoverageQ8Source10.complete,CoverageQ8Source11.complete,CoverageQ8Source12.complete,CoverageQ8Source13.complete,CoverageQ8Source14.complete,CoverageQ8Source15.complete,CoverageQ8Source16.complete,CoverageQ8Source17.complete,CoverageQ8Source18.complete,CoverageQ8Source19.complete,CoverageQ8Source20.complete,CoverageQ8Source21.complete,CoverageQ8Source22.complete,CoverageQ8Source23.complete,CoverageQ8Source24.complete,CoverageQ8Source25.complete,CoverageQ8Source26.complete,CoverageQ8Source27.complete,CoverageQ8Source28.complete,CoverageQ8Source29.complete,CoverageQ8Source30.complete,CoverageQ8Source31.complete,CoverageQ8Source32.complete,CoverageQ8Source33.complete,CoverageQ8Source34.complete,CoverageQ8Source35.complete,CoverageQ8Source36.complete,CoverageQ8Source37.complete,CoverageQ8Source38.complete,CoverageQ8Source39.complete,CoverageQ8Source40.complete,CoverageQ8Source41.complete,CoverageQ8Source42.complete,CoverageQ8Source43.complete,CoverageQ8Source44.complete,CoverageQ8Source45.complete,CoverageQ8Source46.complete,CoverageQ8Source47.complete,CoverageQ8Source48.complete,CoverageQ8Source49.complete,CoverageQ8Source50.complete,CoverageQ8Source51.complete,CoverageQ8Source52.complete,CoverageQ8Source53.complete,CoverageQ8Source54.complete,CoverageQ8Source55.complete,CoverageQ8Source56.complete,CoverageQ8Source57.complete,CoverageQ8Source58.complete,CoverageQ8Source59.complete,CoverageQ8Source60.complete,CoverageQ8Source61.complete,CoverageQ8Source62.complete,CoverageQ8Source63.complete,CoverageQ8Source64.complete,CoverageQ8Source65.complete,CoverageQ8Source66.complete,CoverageQ8Source67.complete,(by intro x hx; simp at hx)⟩

theorem every_source (K : Family Point) (hK : K ∈ catalog) : SourceRepresented K := by
  obtain h | h := Finset.mem_insert.mp hK
  · subst K
    exact CoverageQ8Source68.complete
  · exact ordinary_sources_complete K (List.mem_toFinset.mp h)

/-- Completeness for the entire actual raw point-labelled domain, before any support or arc filter. -/
theorem complete_raw_domain : raw8.supported.domain.1 = (8 : Point).val ∧
    ∀ P ∈ completeDomain catalog hole link09 hole 8,
      ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p P := by
  refine ⟨rfl,?_⟩
  intro P hP
  obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
    C13.Raw.completeDomain_has_punctured_witness catalog hole link09 hole 8
      (by decide +kernel) (by simp [link09,hole]) P hP
  obtain ⟨p,hp,hrep⟩ := every_source K hK c e he hce hstar
  have hPout : emitPencil K c 8 e = P := by
    unfold emitPencil
    rw [mapFamily_equiv]
    exact hout
  exact ⟨p,hp,hPout ▸ hrep⟩
end C13.Enumeration.RawClass9.Domain8
