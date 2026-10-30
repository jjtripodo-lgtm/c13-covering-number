import Mathlib.Tactic.FinCases
import C13Enumeration.Canonical.Atlas
import C13Enumeration.DegreeSeven.Source61
namespace C13.Enumeration.Canonical.Normalizers.Source61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def normalizer00 : Equiv.Perm Point where
  toFun := ![8,9,11,10,5,0,6,7,1,4,2,3,12]
  invFun := ![5,8,10,11,9,4,6,7,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record00 : Record templates where
  family := link61
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 34
  normalizer := normalizer00
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer01 := RawClass9.Source61Center01Q8.normalizer

def record01 : Record templates where
  family := link61
  center := 1
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 1
  normalizer := normalizer01
  hole_fixed := RawClass9.Source61Center01Q8.hole_fixed
  center_image := RawClass9.Source61Center01Q8.center_image
  star_image := RawClass9.Source61Center01Q8.star_image

def normalizer02 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record02 : Record templates where
  family := link61
  center := 2
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 35
  normalizer := normalizer02
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer03 := RawClass9.Source61Center03Q8.normalizer

def record03 : Record templates where
  family := link61
  center := 3
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 1
  normalizer := normalizer03
  hole_fixed := RawClass9.Source61Center03Q8.hole_fixed
  center_image := RawClass9.Source61Center03Q8.center_image
  star_image := RawClass9.Source61Center03Q8.star_image

def normalizer04 : Equiv.Perm Point where
  toFun := ![0,11,8,9,6,7,4,5,10,1,2,3,12]
  invFun := ![0,9,10,11,6,7,4,5,2,3,8,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record04 : Record templates where
  family := link61
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 8
  normalizer := normalizer04
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

def normalizer05 : Equiv.Perm Point where
  toFun := ![1,2,0,3,11,8,10,9,6,5,7,4,12]
  invFun := ![2,0,1,3,11,9,8,10,5,7,6,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record05 : Record templates where
  family := link61
  center := 5
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 34
  normalizer := normalizer05
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer06 := RawClass9.Source61Center06Q8.normalizer

def record06 : Record templates where
  family := link61
  center := 6
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 1
  normalizer := normalizer06
  hole_fixed := RawClass9.Source61Center06Q8.hole_fixed
  center_image := RawClass9.Source61Center06Q8.center_image
  star_image := RawClass9.Source61Center06Q8.star_image

abbrev normalizer07 := RawClass9.Source61Center07Q8.normalizer

def record07 : Record templates where
  family := link61
  center := 7
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 1
  normalizer := normalizer07
  hole_fixed := RawClass9.Source61Center07Q8.hole_fixed
  center_image := RawClass9.Source61Center07Q8.center_image
  star_image := RawClass9.Source61Center07Q8.star_image

def normalizer08 : Equiv.Perm Point where
  toFun := ![1,10,8,9,11,0,2,3,6,7,5,4,12]
  invFun := ![5,0,6,7,11,10,8,9,2,3,1,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record08 : Record templates where
  family := link61
  center := 8
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 35
  normalizer := normalizer08
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

def normalizer09 : Equiv.Perm Point where
  toFun := ![10,2,1,3,8,0,9,11,4,6,5,7,12]
  invFun := ![5,2,1,3,8,10,9,11,4,6,0,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record09 : Record templates where
  family := link61
  center := 9
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 8
  normalizer := normalizer09
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer10 := RawClass9.Source61Center10Q8.normalizer

def record10 : Record templates where
  family := link61
  center := 10
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 1
  normalizer := normalizer10
  hole_fixed := RawClass9.Source61Center10Q8.hole_fixed
  center_image := RawClass9.Source61Center10Q8.center_image
  star_image := RawClass9.Source61Center10Q8.star_image

abbrev normalizer11 := RawClass9.Source61Center11Q6.normalizer

def record11 : Record templates where
  family := link61
  center := 11
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source61.avoids_hole
  template := 6
  normalizer := normalizer11
  hole_fixed := RawClass9.Source61Center11Q6.hole_fixed
  center_image := RawClass9.Source61Center11Q6.center_image
  star_image := RawClass9.Source61Center11Q6.star_image

def entries : List (Record templates) := [record00,record01,record02,record03,record04,record05,record06,record07,record08,record09,record10,record11]

theorem covered (q : Point) (hq : q ≠ hole) : ∃ r ∈ entries, r.family = link61 ∧ r.center = q := by
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
end C13.Enumeration.Canonical.Normalizers.Source61
