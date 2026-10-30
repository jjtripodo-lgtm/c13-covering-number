import C13Enumeration.Census.Figure6Closed0
import C13Enumeration.Census.Figure6Closed1
import C13Enumeration.Census.Figure6Closed2
import C13Enumeration.Census.Figure6Closed3
import C13Enumeration.Census.Figure6Closed4
import C13Covering.OrbitAllSources

namespace C13.Enumeration.Census
open Finset C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

def hardQuadruples : List (Finset Point) :=
  [Figure6Case0.points,Figure6Case1.points,Figure6Case2.points,
   Figure6Case3.points,Figure6Case4.points]

theorem hardQuadruples_count : hardQuadruples.length = 5 := rfl

theorem five_figure6_cover_obstructions (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = figure6)
    (Q : Finset Point) (hQ : Q ∈ hardQuadruples)
    (hmin : ∀ q ∈ Q, degree F q = 15) (houtside : (outside F hole).card ≤ 14) : False := by
  simp only [hardQuadruples,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl
  · exact Figure6Case0.actual_cover_obstruction hclass F hcover hroot hmin houtside
  · exact Figure6Case1.actual_cover_obstruction hclass F hcover hroot hmin houtside
  · exact Figure6Case2.actual_cover_obstruction hclass F hcover hroot hmin houtside
  · exact Figure6Case3.actual_cover_obstruction hclass F hcover hroot hmin houtside
  · exact Figure6Case4.actual_cover_obstruction hclass F hcover hroot hmin houtside

/-- Closes exactly the five literal exceptional foursets. The published
classification remains explicit; no global fourset census is assumed here. -/
theorem five_figure6_no29 (hpublished : PublishedClassification1995)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = figure6)
    (Q : Finset Point) (hQ : Q ∈ hardQuadruples)
    (hmin : ∀ q ∈ Q, degree F q = 15) : F.card ≠ 29 := by
  intro h29
  have hclass : ClassifiesMinimumLinks catalog hole :=
    classification_of_source_coverage rawSources catalog hole hpublished
      C13.OrbitPilot.AllSources.catalog_covers_all_raw_sources
  apply five_figure6_cover_obstructions hclass F hcover hroot Q hQ hmin
  have hd : degree F hole = 15 := by
    rw [← link_card,hroot]
    decide +kernel
  have hc := degree_add_outside F hole
  omega

end C13.Enumeration.Census
