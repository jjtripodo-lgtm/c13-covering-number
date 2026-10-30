import C13Global.Irredundance
import C13Global.Data.Source57
import C13Global.Data.Source58
import C13Global.Data.Source59
import C13Global.Data.Source60
import C13Global.Data.Source61
import C13Global.Data.Source62
import C13Global.Data.Source63
import C13Global.Data.Source64
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses57 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3858, 1792)]
theorem checked57 : privateTripleCheckB Source57.rootCodes witnesses57 = true := by decide +kernel
theorem root_binding57 : decodeSource Source57.rootCodes = link57 := by decide +kernel
theorem private57 : PrivateTriples link57 := by
  rw [← root_binding57]
  exact privateTripleCheck_sound Source57.rootCodes witnesses57 checked57

def witnesses58 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3874, 1792)]
theorem checked58 : privateTripleCheckB Source58.rootCodes witnesses58 = true := by decide +kernel
theorem root_binding58 : decodeSource Source58.rootCodes = link58 := by decide +kernel
theorem private58 : PrivateTriples link58 := by
  rw [← root_binding58]
  exact privateTripleCheck_sound Source58.rootCodes witnesses58 checked58

def witnesses59 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3906, 1792)]
theorem checked59 : privateTripleCheckB Source59.rootCodes witnesses59 = true := by decide +kernel
theorem root_binding59 : decodeSource Source59.rootCodes = link59 := by decide +kernel
theorem private59 : PrivateTriples link59 := by
  rw [← root_binding59]
  exact privateTripleCheck_sound Source59.rootCodes witnesses59 checked59

def witnesses60 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3860, 1792)]
theorem checked60 : privateTripleCheckB Source60.rootCodes witnesses60 = true := by decide +kernel
theorem root_binding60 : decodeSource Source60.rootCodes = link60 := by decide +kernel
theorem private60 : PrivateTriples link60 := by
  rw [← root_binding60]
  exact privateTripleCheck_sound Source60.rootCodes witnesses60 checked60

def witnesses61 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3876, 1792)]
theorem checked61 : privateTripleCheckB Source61.rootCodes witnesses61 = true := by decide +kernel
theorem root_binding61 : decodeSource Source61.rootCodes = link61 := by decide +kernel
theorem private61 : PrivateTriples link61 := by
  rw [← root_binding61]
  exact privateTripleCheck_sound Source61.rootCodes witnesses61 checked61

def witnesses62 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3972, 1792)]
theorem checked62 : privateTripleCheckB Source62.rootCodes witnesses62 = true := by decide +kernel
theorem root_binding62 : decodeSource Source62.rootCodes = link62 := by decide +kernel
theorem private62 : PrivateTriples link62 := by
  rw [← root_binding62]
  exact privateTripleCheck_sound Source62.rootCodes witnesses62 checked62

def witnesses63 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (498, 112), (3858, 1792)]
theorem checked63 : privateTripleCheckB Source63.rootCodes witnesses63 = true := by decide +kernel
theorem root_binding63 : decodeSource Source63.rootCodes = link63 := by decide +kernel
theorem private63 : PrivateTriples link63 := by
  rw [← root_binding63]
  exact privateTripleCheck_sound Source63.rootCodes witnesses63 checked63

def witnesses64 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (498, 112), (3906, 1792)]
theorem checked64 : privateTripleCheckB Source64.rootCodes witnesses64 = true := by decide +kernel
theorem root_binding64 : decodeSource Source64.rootCodes = link64 := by decide +kernel
theorem private64 : PrivateTriples link64 := by
  rw [← root_binding64]
  exact privateTripleCheck_sound Source64.rootCodes witnesses64 checked64
end C13.Global.PrivateData
