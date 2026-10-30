import C13Global.Irredundance
import C13Global.Data.Source49
import C13Global.Data.Source50
import C13Global.Data.Source51
import C13Global.Data.Source52
import C13Global.Data.Source53
import C13Global.Data.Source54
import C13Global.Data.Source55
import C13Global.Data.Source56
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses49 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3972, 1792)]
theorem checked49 : privateTripleCheckB Source49.rootCodes witnesses49 = true := by decide +kernel
theorem root_binding49 : decodeSource Source49.rootCodes = link49 := by decide +kernel
theorem private49 : PrivateTriples link49 := by
  rw [← root_binding49]
  exact privateTripleCheck_sound Source49.rootCodes witnesses49 checked49

def witnesses50 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3888, 1792)]
theorem checked50 : privateTripleCheckB Source50.rootCodes witnesses50 = true := by decide +kernel
theorem root_binding50 : decodeSource Source50.rootCodes = link50 := by decide +kernel
theorem private50 : PrivateTriples link50 := by
  rw [← root_binding50]
  exact privateTripleCheck_sound Source50.rootCodes witnesses50 checked50

def witnesses51 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3984, 1792)]
theorem checked51 : privateTripleCheckB Source51.rootCodes witnesses51 = true := by decide +kernel
theorem root_binding51 : decodeSource Source51.rootCodes = link51 := by decide +kernel
theorem private51 : PrivateTriples link51 := by
  rw [← root_binding51]
  exact privateTripleCheck_sound Source51.rootCodes witnesses51 checked51

def witnesses52 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (497, 112), (3857, 1792)]
theorem checked52 : privateTripleCheckB Source52.rootCodes witnesses52 = true := by decide +kernel
theorem root_binding52 : decodeSource Source52.rootCodes = link52 := by decide +kernel
theorem private52 : PrivateTriples link52 := by
  rw [← root_binding52]
  exact privateTripleCheck_sound Source52.rootCodes witnesses52 checked52

def witnesses53 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (497, 112), (3873, 1792)]
theorem checked53 : privateTripleCheckB Source53.rootCodes witnesses53 = true := by decide +kernel
theorem root_binding53 : decodeSource Source53.rootCodes = link53 := by decide +kernel
theorem private53 : PrivateTriples link53 := by
  rw [← root_binding53]
  exact privateTripleCheck_sound Source53.rootCodes witnesses53 checked53

def witnesses54 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (497, 112), (3874, 1792)]
theorem checked54 : privateTripleCheckB Source54.rootCodes witnesses54 = true := by decide +kernel
theorem root_binding54 : decodeSource Source54.rootCodes = link54 := by decide +kernel
theorem private54 : PrivateTriples link54 := by
  rw [← root_binding54]
  exact privateTripleCheck_sound Source54.rootCodes witnesses54 checked54

def witnesses55 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (497, 112), (3906, 1792)]
theorem checked55 : privateTripleCheckB Source55.rootCodes witnesses55 = true := by decide +kernel
theorem root_binding55 : decodeSource Source55.rootCodes = link55 := by decide +kernel
theorem private55 : PrivateTriples link55 := by
  rw [← root_binding55]
  exact privateTripleCheck_sound Source55.rootCodes witnesses55 checked55

def witnesses56 : List (Code × Code) := [(819, 35), (3267, 67), (3132, 44), (972, 76), (1365, 69), (2725, 37), (2650, 74), (1450, 42), (2457, 137), (1641, 41), (1686, 134), (2406, 38), (287, 7), (753, 112), (3905, 1792)]
theorem checked56 : privateTripleCheckB Source56.rootCodes witnesses56 = true := by decide +kernel
theorem root_binding56 : decodeSource Source56.rootCodes = link56 := by decide +kernel
theorem private56 : PrivateTriples link56 := by
  rw [← root_binding56]
  exact privateTripleCheck_sound Source56.rootCodes witnesses56 checked56
end C13.Global.PrivateData
