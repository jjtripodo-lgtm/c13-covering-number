import C13Global.Irredundance
import C13Global.Data.Source17
import C13Global.Data.Source18
import C13Global.Data.Source19
import C13Global.Data.Source20
import C13Global.Data.Source21
import C13Global.Data.Source22
import C13Global.Data.Source23
import C13Global.Data.Source24
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses17 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3857, 1792)]
theorem checked17 : privateTripleCheckB Source17.rootCodes witnesses17 = true := by decide +kernel
theorem root_binding17 : decodeSource Source17.rootCodes = link17 := by decide +kernel
theorem private17 : PrivateTriples link17 := by
  rw [← root_binding17]
  exact privateTripleCheck_sound Source17.rootCodes witnesses17 checked17

def witnesses18 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3905, 1792)]
theorem checked18 : privateTripleCheckB Source18.rootCodes witnesses18 = true := by decide +kernel
theorem root_binding18 : decodeSource Source18.rootCodes = link18 := by decide +kernel
theorem private18 : PrivateTriples link18 := by
  rw [← root_binding18]
  exact privateTripleCheck_sound Source18.rootCodes witnesses18 checked18

def witnesses19 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3850, 1792)]
theorem checked19 : privateTripleCheckB Source19.rootCodes witnesses19 = true := by decide +kernel
theorem root_binding19 : decodeSource Source19.rootCodes = link19 := by decide +kernel
theorem private19 : PrivateTriples link19 := by
  rw [← root_binding19]
  exact privateTripleCheck_sound Source19.rootCodes witnesses19 checked19

def witnesses20 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3906, 1792)]
theorem checked20 : privateTripleCheckB Source20.rootCodes witnesses20 = true := by decide +kernel
theorem root_binding20 : decodeSource Source20.rootCodes = link20 := by decide +kernel
theorem private20 : PrivateTriples link20 := by
  rw [← root_binding20]
  exact privateTripleCheck_sound Source20.rootCodes witnesses20 checked20

def witnesses21 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3845, 1792), (497, 112)]
theorem checked21 : privateTripleCheckB Source21.rootCodes witnesses21 = true := by decide +kernel
theorem root_binding21 : decodeSource Source21.rootCodes = link21 := by decide +kernel
theorem private21 : PrivateTriples link21 := by
  rw [← root_binding21]
  exact privateTripleCheck_sound Source21.rootCodes witnesses21 checked21

def witnesses22 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3845, 1792), (1265, 112)]
theorem checked22 : privateTripleCheckB Source22.rootCodes witnesses22 = true := by decide +kernel
theorem root_binding22 : decodeSource Source22.rootCodes = link22 := by decide +kernel
theorem private22 : PrivateTriples link22 := by
  rw [← root_binding22]
  exact privateTripleCheck_sound Source22.rootCodes witnesses22 checked22

def witnesses23 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3845, 1792), (498, 112)]
theorem checked23 : privateTripleCheckB Source23.rootCodes witnesses23 = true := by decide +kernel
theorem root_binding23 : decodeSource Source23.rootCodes = link23 := by decide +kernel
theorem private23 : PrivateTriples link23 := by
  rw [← root_binding23]
  exact privateTripleCheck_sound Source23.rootCodes witnesses23 checked23

def witnesses24 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3845, 1792), (1266, 112)]
theorem checked24 : privateTripleCheckB Source24.rootCodes witnesses24 = true := by decide +kernel
theorem root_binding24 : decodeSource Source24.rootCodes = link24 := by decide +kernel
theorem private24 : PrivateTriples link24 := by
  rw [← root_binding24]
  exact privateTripleCheck_sound Source24.rootCodes witnesses24 checked24
end C13.Global.PrivateData
