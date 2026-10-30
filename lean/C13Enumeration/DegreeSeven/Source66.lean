import C13Enumeration.DegreeSeven.Lookup
import C13Enumeration.RawClass9.Domain6
import C13Enumeration.RawClass9.Domain8
namespace C13.Enumeration.DegreeSeven.Source66
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
open C13.Enumeration.RawClass9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem avoids_hole : ∀ B ∈ link66, hole ∉ B := by simp [link66,hole]

def target00 : Target := normalizedTarget link66 0 6 raw6
  RawClass9.Source66Center00Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center00Q6.hole_fixed RawClass9.Source66Center00Q6.center_image RawClass9.Source66Center00Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target03 : Target := normalizedTarget link66 3 8 raw8
  RawClass9.Source66Center03Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center03Q8.hole_fixed RawClass9.Source66Center03Q8.center_image RawClass9.Source66Center03Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target06 : Target := normalizedTarget link66 6 8 raw8
  RawClass9.Source66Center06Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center06Q8.hole_fixed RawClass9.Source66Center06Q8.center_image RawClass9.Source66Center06Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target07 : Target := normalizedTarget link66 7 6 raw6
  RawClass9.Source66Center07Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center07Q6.hole_fixed RawClass9.Source66Center07Q6.center_image RawClass9.Source66Center07Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target09 : Target := normalizedTarget link66 9 8 raw8
  RawClass9.Source66Center09Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center09Q8.hole_fixed RawClass9.Source66Center09Q8.center_image RawClass9.Source66Center09Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target11 : Target := normalizedTarget link66 11 6 raw6
  RawClass9.Source66Center11Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source66Center11Q6.hole_fixed RawClass9.Source66Center11Q6.center_image RawClass9.Source66Center11Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def entries : List Target := [target00,target03,target06,target07,target09,target11]

theorem covered (q : Point) (h : (link link66 q).card = 7) :
    ∃ t ∈ entries, t.family = link66 ∧ t.point = q := by
  have hm := RawClass9.CoverageQ8Source66.centers_checked q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target00,by simp [entries],rfl,rfl⟩
  · exact ⟨target03,by simp [entries],rfl,rfl⟩
  · exact ⟨target06,by simp [entries],rfl,rfl⟩
  · exact ⟨target07,by simp [entries],rfl,rfl⟩
  · exact ⟨target09,by simp [entries],rfl,rfl⟩
  · exact ⟨target11,by simp [entries],rfl,rfl⟩
end C13.Enumeration.DegreeSeven.Source66
