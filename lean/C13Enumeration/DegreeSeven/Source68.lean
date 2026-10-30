import C13Enumeration.DegreeSeven.Lookup
import C13Enumeration.RawClass9.Domain6
import C13Enumeration.RawClass9.Domain8
namespace C13.Enumeration.DegreeSeven.Source68
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
open C13.Enumeration.RawClass9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem avoids_hole : ∀ B ∈ figure6, hole ∉ B := by simp [figure6,hole]

def target00 : Target := normalizedTarget figure6 0 6 raw6
  RawClass9.Source68Center00Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center00Q6.hole_fixed RawClass9.Source68Center00Q6.center_image RawClass9.Source68Center00Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target01 : Target := normalizedTarget figure6 1 6 raw6
  RawClass9.Source68Center01Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center01Q6.hole_fixed RawClass9.Source68Center01Q6.center_image RawClass9.Source68Center01Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target02 : Target := normalizedTarget figure6 2 6 raw6
  RawClass9.Source68Center02Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center02Q6.hole_fixed RawClass9.Source68Center02Q6.center_image RawClass9.Source68Center02Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target03 : Target := normalizedTarget figure6 3 6 raw6
  RawClass9.Source68Center03Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center03Q6.hole_fixed RawClass9.Source68Center03Q6.center_image RawClass9.Source68Center03Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target06 : Target := normalizedTarget figure6 6 6 raw6
  RawClass9.Source68Center06Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center06Q6.hole_fixed RawClass9.Source68Center06Q6.center_image RawClass9.Source68Center06Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target07 : Target := normalizedTarget figure6 7 6 raw6
  RawClass9.Source68Center07Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center07Q6.hole_fixed RawClass9.Source68Center07Q6.center_image RawClass9.Source68Center07Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target08 : Target := normalizedTarget figure6 8 6 raw6
  RawClass9.Source68Center08Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center08Q6.hole_fixed RawClass9.Source68Center08Q6.center_image RawClass9.Source68Center08Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target09 : Target := normalizedTarget figure6 9 6 raw6
  RawClass9.Source68Center09Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center09Q6.hole_fixed RawClass9.Source68Center09Q6.center_image RawClass9.Source68Center09Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target10 : Target := normalizedTarget figure6 10 6 raw6
  RawClass9.Source68Center10Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center10Q6.hole_fixed RawClass9.Source68Center10Q6.center_image RawClass9.Source68Center10Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def target11 : Target := normalizedTarget figure6 11 6 raw6
  RawClass9.Source68Center11Q6.normalizer (by decide +kernel) avoids_hole
  RawClass9.Source68Center11Q6.hole_fixed RawClass9.Source68Center11Q6.center_image RawClass9.Source68Center11Q6.star_image
  RawClass9.Domain6.complete_raw_domain.2

def entries : List Target := [target00,target01,target02,target03,target06,target07,target08,target09,target10,target11]

theorem covered (q : Point) (h : (link figure6 q).card = 7) :
    ∃ t ∈ entries, t.family = figure6 ∧ t.point = q := by
  have hm := RawClass9.CoverageQ8Source68.centers_checked q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target00,by simp [entries],rfl,rfl⟩
  · exact ⟨target01,by simp [entries],rfl,rfl⟩
  · exact ⟨target02,by simp [entries],rfl,rfl⟩
  · exact ⟨target03,by simp [entries],rfl,rfl⟩
  · exact ⟨target06,by simp [entries],rfl,rfl⟩
  · exact ⟨target07,by simp [entries],rfl,rfl⟩
  · exact ⟨target08,by simp [entries],rfl,rfl⟩
  · exact ⟨target09,by simp [entries],rfl,rfl⟩
  · exact ⟨target10,by simp [entries],rfl,rfl⟩
  · exact ⟨target11,by simp [entries],rfl,rfl⟩
end C13.Enumeration.DegreeSeven.Source68
