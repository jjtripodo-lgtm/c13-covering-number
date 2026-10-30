import C13Global.Irredundance
import C13Global.Data.Source09
import C13Global.Data.Source10
import C13Global.Data.Source11
import C13Global.Data.Source12
import C13Global.Data.Source13
import C13Global.Data.Source14
import C13Global.Data.Source15
import C13Global.Data.Source16
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses09 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (1265, 112)]
theorem checked09 : privateTripleCheckB Source09.rootCodes witnesses09 = true := by decide +kernel
theorem root_binding09 : decodeSource Source09.rootCodes = link09 := by decide +kernel
theorem private09 : PrivateTriples link09 := by
  rw [← root_binding09]
  exact privateTripleCheck_sound Source09.rootCodes witnesses09 checked09

def witnesses10 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (500, 112)]
theorem checked10 : privateTripleCheckB Source10.rootCodes witnesses10 = true := by decide +kernel
theorem root_binding10 : decodeSource Source10.rootCodes = link10 := by decide +kernel
theorem private10 : PrivateTriples link10 := by
  rw [← root_binding10]
  exact privateTripleCheck_sound Source10.rootCodes witnesses10 checked10

def witnesses11 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (1268, 112)]
theorem checked11 : privateTripleCheckB Source11.rootCodes witnesses11 = true := by decide +kernel
theorem root_binding11 : decodeSource Source11.rootCodes = link11 := by decide +kernel
theorem private11 : PrivateTriples link11 := by
  rw [← root_binding11]
  exact privateTripleCheck_sound Source11.rootCodes witnesses11 checked11

def witnesses12 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (1008, 112)]
theorem checked12 : privateTripleCheckB Source12.rootCodes witnesses12 = true := by decide +kernel
theorem root_binding12 : decodeSource Source12.rootCodes = link12 := by decide +kernel
theorem private12 : PrivateTriples link12 := by
  rw [← root_binding12]
  exact privateTripleCheck_sound Source12.rootCodes witnesses12 checked12

def witnesses13 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (1520, 112)]
theorem checked13 : privateTripleCheckB Source13.rootCodes witnesses13 = true := by decide +kernel
theorem root_binding13 : decodeSource Source13.rootCodes = link13 := by decide +kernel
theorem private13 : PrivateTriples link13 := by
  rw [← root_binding13]
  exact privateTripleCheck_sound Source13.rootCodes witnesses13 checked13

def witnesses14 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (3312, 112)]
theorem checked14 : privateTripleCheckB Source14.rootCodes witnesses14 = true := by decide +kernel
theorem root_binding14 : decodeSource Source14.rootCodes = link14 := by decide +kernel
theorem private14 : PrivateTriples link14 := by
  rw [← root_binding14]
  exact privateTripleCheck_sound Source14.rootCodes witnesses14 checked14

def witnesses15 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 1041), (2725, 2081), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3845, 1792)]
theorem checked15 : privateTripleCheckB Source15.rootCodes witnesses15 = true := by decide +kernel
theorem root_binding15 : decodeSource Source15.rootCodes = link15 := by decide +kernel
theorem private15 : PrivateTriples link15 := by
  rw [← root_binding15]
  exact privateTripleCheck_sound Source15.rootCodes witnesses15 checked15

def witnesses16 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (245, 112), (3849, 1792)]
theorem checked16 : privateTripleCheckB Source16.rootCodes witnesses16 = true := by decide +kernel
theorem root_binding16 : decodeSource Source16.rootCodes = link16 := by decide +kernel
theorem private16 : PrivateTriples link16 := by
  rw [← root_binding16]
  exact privateTripleCheck_sound Source16.rootCodes witnesses16 checked16
end C13.Global.PrivateData
