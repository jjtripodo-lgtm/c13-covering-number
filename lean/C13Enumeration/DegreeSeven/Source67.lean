import C13Enumeration.DegreeSeven.Lookup
import C13Enumeration.RawClass9.Domain6
import C13Enumeration.RawClass9.Domain8
namespace C13.Enumeration.DegreeSeven.Source67
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
open C13.Enumeration.RawClass9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem avoids_hole : ∀ B ∈ link67, hole ∉ B := by simp [link67,hole]

def target00 : Target := normalizedTarget link67 0 6 raw6
  RawClass9.Source67Center00Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center00Q6.hole_fixed RawClass9.Source67Center00Q6.center_image RawClass9.Source67Center00Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target02 : Target := normalizedTarget link67 2 8 raw8
  RawClass9.Source67Center02Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center02Q8.hole_fixed RawClass9.Source67Center02Q8.center_image RawClass9.Source67Center02Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target05 : Target := normalizedTarget link67 5 8 raw8
  RawClass9.Source67Center05Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center05Q8.hole_fixed RawClass9.Source67Center05Q8.center_image RawClass9.Source67Center05Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def target07 : Target := normalizedTarget link67 7 6 raw6
  RawClass9.Source67Center07Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center07Q6.hole_fixed RawClass9.Source67Center07Q6.center_image RawClass9.Source67Center07Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target09 : Target := normalizedTarget link67 9 6 raw6
  RawClass9.Source67Center09Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center09Q6.hole_fixed RawClass9.Source67Center09Q6.center_image RawClass9.Source67Center09Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target11 : Target := normalizedTarget link67 11 8 raw8
  RawClass9.Source67Center11Q8.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source67Center11Q8.hole_fixed RawClass9.Source67Center11Q8.center_image RawClass9.Source67Center11Q8.star_image
  RawClass9.Domain8.complete_raw_domain.2

def entries : List Target := [target00,target02,target05,target07,target09,target11]

theorem covered (q : Point) (h : (link link67 q).card = 7) :
    ∃ t ∈ entries, t.family = link67 ∧ t.point = q := by
  have hm := RawClass9.CoverageQ8Source67.centers_checked q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target00,by simp [entries],rfl,rfl⟩
  · exact ⟨target02,by simp [entries],rfl,rfl⟩
  · exact ⟨target05,by simp [entries],rfl,rfl⟩
  · exact ⟨target07,by simp [entries],rfl,rfl⟩
  · exact ⟨target09,by simp [entries],rfl,rfl⟩
  · exact ⟨target11,by simp [entries],rfl,rfl⟩
end C13.Enumeration.DegreeSeven.Source67
