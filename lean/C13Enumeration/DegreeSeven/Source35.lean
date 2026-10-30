import C13Enumeration.DegreeSeven.Lookup
import C13Enumeration.RawClass9.Domain6
import C13Enumeration.RawClass9.Domain8
namespace C13.Enumeration.DegreeSeven.Source35
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
open C13.Enumeration.RawClass9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem avoids_hole : ∀ B ∈ link35, hole ∉ B := by simp [link35,hole]

def target01 : Target := normalizedTarget link35 1 8 raw8
  RawClass9.Source35Center01Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center01Q8.hole_fixed RawClass9.Source35Center01Q8.center_image RawClass9.Source35Center01Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target03 : Target := normalizedTarget link35 3 8 raw8
  RawClass9.Source35Center03Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center03Q8.hole_fixed RawClass9.Source35Center03Q8.center_image RawClass9.Source35Center03Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target06 : Target := normalizedTarget link35 6 8 raw8
  RawClass9.Source35Center06Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center06Q8.hole_fixed RawClass9.Source35Center06Q8.center_image RawClass9.Source35Center06Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target09 : Target := normalizedTarget link35 9 6 raw6
  RawClass9.Source35Center09Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center09Q6.hole_fixed RawClass9.Source35Center09Q6.center_image RawClass9.Source35Center09Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target10 : Target := normalizedTarget link35 10 8 raw8
  RawClass9.Source35Center10Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center10Q8.hole_fixed RawClass9.Source35Center10Q8.center_image RawClass9.Source35Center10Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target11 : Target := normalizedTarget link35 11 8 raw8
  RawClass9.Source35Center11Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source35Center11Q8.hole_fixed RawClass9.Source35Center11Q8.center_image RawClass9.Source35Center11Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def entries : List Target := [target01,target03,target06,target09,target10,target11]

theorem covered (q : Point) (h : (link link35 q).card = 7) :
    ∃ t ∈ entries, t.family = link35 ∧ t.point = q := by
  have hm := RawClass9.CoverageQ8Source35.centers_checked q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target01,by simp [entries],rfl,rfl⟩
  · exact ⟨target03,by simp [entries],rfl,rfl⟩
  · exact ⟨target06,by simp [entries],rfl,rfl⟩
  · exact ⟨target09,by simp [entries],rfl,rfl⟩
  · exact ⟨target10,by simp [entries],rfl,rfl⟩
  · exact ⟨target11,by simp [entries],rfl,rfl⟩
end C13.Enumeration.DegreeSeven.Source35
