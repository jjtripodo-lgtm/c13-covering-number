import Mathlib.Tactic.FinCases
import C13Enumeration.Canonical.Atlas
import C13Enumeration.DegreeSeven.Source51
namespace C13.Enumeration.Canonical.Normalizers.Source51
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def normalizer00 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record00 : Record templates where
  family := link51
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 18
  normalizer := normalizer00
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer01 := RawClass9.Source51Center01Q8.normalizer

def record01 : Record templates where
  family := link51
  center := 1
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer01
  hole_fixed := RawClass9.Source51Center01Q8.hole_fixed
  center_image := RawClass9.Source51Center01Q8.center_image
  star_image := RawClass9.Source51Center01Q8.star_image

abbrev normalizer02 := RawClass9.Source51Center02Q8.normalizer

def record02 : Record templates where
  family := link51
  center := 2
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer02
  hole_fixed := RawClass9.Source51Center02Q8.hole_fixed
  center_image := RawClass9.Source51Center02Q8.center_image
  star_image := RawClass9.Source51Center02Q8.star_image

abbrev normalizer03 := RawClass9.Source51Center03Q8.normalizer

def record03 : Record templates where
  family := link51
  center := 3
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer03
  hole_fixed := RawClass9.Source51Center03Q8.hole_fixed
  center_image := RawClass9.Source51Center03Q8.center_image
  star_image := RawClass9.Source51Center03Q8.star_image

def normalizer04 : Equiv.Perm Point where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record04 : Record templates where
  family := link51
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 50
  normalizer := normalizer04
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

def normalizer05 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record05 : Record templates where
  family := link51
  center := 5
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 17
  normalizer := normalizer05
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer06 := RawClass9.Source51Center06Q6.normalizer

def record06 : Record templates where
  family := link51
  center := 6
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 6
  normalizer := normalizer06
  hole_fixed := RawClass9.Source51Center06Q6.hole_fixed
  center_image := RawClass9.Source51Center06Q6.center_image
  star_image := RawClass9.Source51Center06Q6.star_image

def normalizer07 : Equiv.Perm Point where
  toFun := ![10,8,9,11,5,7,6,4,3,1,0,2,12]
  invFun := ![10,9,11,8,7,4,6,5,1,2,0,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record07 : Record templates where
  family := link51
  center := 7
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 17
  normalizer := normalizer07
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer08 := RawClass9.Source51Center08Q8.normalizer

def record08 : Record templates where
  family := link51
  center := 8
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer08
  hole_fixed := RawClass9.Source51Center08Q8.hole_fixed
  center_image := RawClass9.Source51Center08Q8.center_image
  star_image := RawClass9.Source51Center08Q8.star_image

abbrev normalizer09 := RawClass9.Source51Center09Q8.normalizer

def record09 : Record templates where
  family := link51
  center := 9
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer09
  hole_fixed := RawClass9.Source51Center09Q8.hole_fixed
  center_image := RawClass9.Source51Center09Q8.center_image
  star_image := RawClass9.Source51Center09Q8.star_image

def normalizer10 : Equiv.Perm Point where
  toFun := ![6,11,10,9,4,7,8,5,0,3,2,1,12]
  invFun := ![8,11,10,9,4,7,0,5,6,3,2,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def record10 : Record templates where
  family := link51
  center := 10
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 18
  normalizer := normalizer10
  hole_fixed := by decide +kernel
  center_image := by decide +kernel
  star_image := by decide +kernel

abbrev normalizer11 := RawClass9.Source51Center11Q8.normalizer

def record11 : Record templates where
  family := link51
  center := 11
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source51.avoids_hole
  template := 1
  normalizer := normalizer11
  hole_fixed := RawClass9.Source51Center11Q8.hole_fixed
  center_image := RawClass9.Source51Center11Q8.center_image
  star_image := RawClass9.Source51Center11Q8.star_image

def entries : List (Record templates) := [record00,record01,record02,record03,record04,record05,record06,record07,record08,record09,record10,record11]

theorem covered (q : Point) (hq : q ≠ hole) : ∃ r ∈ entries, r.family = link51 ∧ r.center = q := by
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
end C13.Enumeration.Canonical.Normalizers.Source51
