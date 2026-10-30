import Mathlib.Tactic.FinCases
import C13Enumeration.Canonical.Atlas
import C13Enumeration.DegreeSeven.Source65
namespace C13.Enumeration.Canonical.Normalizers.Source65
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev normalizer00 := RawClass9.Source65Center00Q6.normalizer

def record00 : Record templates where
  family := link65
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 6
  normalizer := normalizer00
  hole_fixed := RawClass9.Source65Center00Q6.hole_fixed
  center_image := RawClass9.Source65Center00Q6.center_image
  star_image := RawClass9.Source65Center00Q6.star_image

def normalizer01 : Equiv.Perm Point where
  toFun := ![3,2,0,1,5,10,6,7,4,11,9,8,12]
  invFun := ![2,3,1,0,8,4,6,7,11,10,5,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record01 : Record templates where
  family := link65
  center := 1
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 19
  normalizer := normalizer01
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

def normalizer02 : Equiv.Perm Point where
  toFun := ![4,7,6,5,0,3,2,1,8,11,10,9,12]
  invFun := ![4,7,6,5,0,3,2,1,8,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record02 : Record templates where
  family := link65
  center := 2
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 35
  normalizer := normalizer02
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer03 := RawClass9.Source65Center03Q8.normalizer

def record03 : Record templates where
  family := link65
  center := 3
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 1
  normalizer := normalizer03
  hole_fixed := RawClass9.Source65Center03Q8.hole_fixed
  center_image := RawClass9.Source65Center03Q8.center_image
  star_image := RawClass9.Source65Center03Q8.star_image

def normalizer04 : Equiv.Perm Point where
  toFun := ![10,5,6,7,2,3,0,1,4,11,8,9,12]
  invFun := ![6,7,4,5,8,1,2,3,10,11,0,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record04 : Record templates where
  family := link65
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 19
  normalizer := normalizer04
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer05 := RawClass9.Source65Center05Q6.normalizer

def record05 : Record templates where
  family := link65
  center := 5
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 6
  normalizer := normalizer05
  hole_fixed := RawClass9.Source65Center05Q6.hole_fixed
  center_image := RawClass9.Source65Center05Q6.center_image
  star_image := RawClass9.Source65Center05Q6.star_image

abbrev normalizer06 := RawClass9.Source65Center06Q8.normalizer

def record06 : Record templates where
  family := link65
  center := 6
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 1
  normalizer := normalizer06
  hole_fixed := RawClass9.Source65Center06Q8.hole_fixed
  center_image := RawClass9.Source65Center06Q8.center_image
  star_image := RawClass9.Source65Center06Q8.star_image

def normalizer07 : Equiv.Perm Point where
  toFun := ![3,0,1,2,7,4,5,6,8,11,10,9,12]
  invFun := ![1,2,3,0,5,6,7,4,8,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record07 : Record templates where
  family := link65
  center := 7
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 35
  normalizer := normalizer07
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

def normalizer08 : Equiv.Perm Point where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record08 : Record templates where
  family := link65
  center := 8
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 60
  normalizer := normalizer08
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer09 := RawClass9.Source65Center09Q6.normalizer

def record09 : Record templates where
  family := link65
  center := 9
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 6
  normalizer := normalizer09
  hole_fixed := RawClass9.Source65Center09Q6.hole_fixed
  center_image := RawClass9.Source65Center09Q6.center_image
  star_image := RawClass9.Source65Center09Q6.star_image

abbrev normalizer10 := RawClass9.Source65Center10Q8.normalizer

def record10 : Record templates where
  family := link65
  center := 10
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 1
  normalizer := normalizer10
  hole_fixed := RawClass9.Source65Center10Q8.hole_fixed
  center_image := RawClass9.Source65Center10Q8.center_image
  star_image := RawClass9.Source65Center10Q8.star_image

abbrev normalizer11 := RawClass9.Source65Center11Q8.normalizer

def record11 : Record templates where
  family := link65
  center := 11
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source65.avoids_hole
  template := 1
  normalizer := normalizer11
  hole_fixed := RawClass9.Source65Center11Q8.hole_fixed
  center_image := RawClass9.Source65Center11Q8.center_image
  star_image := RawClass9.Source65Center11Q8.star_image

def entries : List (Record templates) := [record00,record01,record02,record03,record04,record05,record06,record07,record08,record09,record10,record11]

theorem covered (q : Point) (hq : q ≠ hole) : ∃ r ∈ entries, r.family = link65 ∧ r.center = q := by
  fin_cases q
  · exact ⟨record00,by simp [entries],rfl,rfl⟩
  · exact ⟨record01,by simp [entries],rfl,rfl⟩
  · exact ⟨record02,by simp [entries],rfl,rfl⟩
  · exact ⟨record03,by simp [entries],rfl,rfl⟩
  · exact ⟨record04,by simp [entries],rfl,rfl⟩
  · exact ⟨record05,by simp [entries],rfl,rfl⟩
  · exact ⟨record06,by simp [entries],rfl,rfl⟩
  · exact ⟨record07,by simp [entries],rfl,rfl⟩
  · exact ⟨record08,by simp [entries],rfl,rfl⟩
  · exact ⟨record09,by simp [entries],rfl,rfl⟩
  · exact ⟨record10,by simp [entries],rfl,rfl⟩
  · exact ⟨record11,by simp [entries],rfl,rfl⟩
  · exact (hq rfl).elim
end C13.Enumeration.Canonical.Normalizers.Source65
