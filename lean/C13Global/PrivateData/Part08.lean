import C13Global.Irredundance
import C13Global.Data.Source65
import C13Global.Data.Source66
import C13Global.Data.Source67
import C13Global.Data.Source68
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses65 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (498, 112), (3972, 1792)]
theorem checked65 : privateTripleCheckB Source65.rootCodes witnesses65 = true := by decide +kernel
theorem root_binding65 : decodeSource Source65.rootCodes = link65 := by decide +kernel
theorem private65 : PrivateTriples link65 := by
  rw [← root_binding65]
  exact privateTripleCheck_sound Source65.rootCodes witnesses65 checked65

def witnesses66 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (1266, 112), (3876, 1792)]
theorem checked66 : privateTripleCheckB Source66.rootCodes witnesses66 = true := by decide +kernel
theorem root_binding66 : decodeSource Source66.rootCodes = link66 := by decide +kernel
theorem private66 : PrivateTriples link66 := by
  rw [← root_binding66]
  exact privateTripleCheck_sound Source66.rootCodes witnesses66 checked66

def witnesses67 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (1266, 112), (3912, 1792)]
theorem checked67 : privateTripleCheckB Source67.rootCodes witnesses67 = true := by decide +kernel
theorem root_binding67 : decodeSource Source67.rootCodes = link67 := by decide +kernel
theorem private67 : PrivateTriples link67 := by
  rw [← root_binding67]
  exact privateTripleCheck_sound Source67.rootCodes witnesses67 checked67

def witnesses68 : List (Code × Code) := [(63, 11), (455, 67), (3591, 515), (3465, 137), (3185, 1041), (945, 145), (633, 73), (2890, 74), (2738, 530), (1394, 82), (1210, 138), (1740, 76), (1844, 532), (2292, 84), (2364, 268)]
theorem checked68 : privateTripleCheckB Source68.rootCodes witnesses68 = true := by decide +kernel
theorem root_binding68 : decodeSource Source68.rootCodes = figure6 := by decide +kernel
theorem private68 : PrivateTriples figure6 := by
  rw [← root_binding68]
  exact privateTripleCheck_sound Source68.rootCodes witnesses68 checked68
end C13.Global.PrivateData
