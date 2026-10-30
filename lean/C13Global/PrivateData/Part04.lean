import C13Global.Irredundance
import C13Global.Data.Source33
import C13Global.Data.Source34
import C13Global.Data.Source35
import C13Global.Data.Source36
import C13Global.Data.Source37
import C13Global.Data.Source38
import C13Global.Data.Source39
import C13Global.Data.Source40
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses33 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3876, 1792)]
theorem checked33 : privateTripleCheckB Source33.rootCodes witnesses33 = true := by decide +kernel
theorem root_binding33 : decodeSource Source33.rootCodes = link33 := by decide +kernel
theorem private33 : PrivateTriples link33 := by
  rw [← root_binding33]
  exact privateTripleCheck_sound Source33.rootCodes witnesses33 checked33

def witnesses34 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3908, 1792)]
theorem checked34 : privateTripleCheckB Source34.rootCodes witnesses34 = true := by decide +kernel
theorem root_binding34 : decodeSource Source34.rootCodes = link34 := by decide +kernel
theorem private34 : PrivateTriples link34 := by
  rw [← root_binding34]
  exact privateTripleCheck_sound Source34.rootCodes witnesses34 checked34

def witnesses35 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3972, 1792)]
theorem checked35 : privateTripleCheckB Source35.rootCodes witnesses35 = true := by decide +kernel
theorem root_binding35 : decodeSource Source35.rootCodes = link35 := by decide +kernel
theorem private35 : PrivateTriples link35 := by
  rw [← root_binding35]
  exact privateTripleCheck_sound Source35.rootCodes witnesses35 checked35

def witnesses36 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3888, 1792)]
theorem checked36 : privateTripleCheckB Source36.rootCodes witnesses36 = true := by decide +kernel
theorem root_binding36 : decodeSource Source36.rootCodes = link36 := by decide +kernel
theorem private36 : PrivateTriples link36 := by
  rw [← root_binding36]
  exact privateTripleCheck_sound Source36.rootCodes witnesses36 checked36

def witnesses37 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3920, 1792)]
theorem checked37 : privateTripleCheckB Source37.rootCodes witnesses37 = true := by decide +kernel
theorem root_binding37 : decodeSource Source37.rootCodes = link37 := by decide +kernel
theorem private37 : PrivateTriples link37 := by
  rw [← root_binding37]
  exact privateTripleCheck_sound Source37.rootCodes witnesses37 checked37

def witnesses38 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3936, 1792)]
theorem checked38 : privateTripleCheckB Source38.rootCodes witnesses38 = true := by decide +kernel
theorem root_binding38 : decodeSource Source38.rootCodes = link38 := by decide +kernel
theorem private38 : PrivateTriples link38 := by
  rw [← root_binding38]
  exact privateTripleCheck_sound Source38.rootCodes witnesses38 checked38

def witnesses39 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (4032, 1792)]
theorem checked39 : privateTripleCheckB Source39.rootCodes witnesses39 = true := by decide +kernel
theorem root_binding39 : decodeSource Source39.rootCodes = link39 := by decide +kernel
theorem private39 : PrivateTriples link39 := by
  rw [← root_binding39]
  exact privateTripleCheck_sound Source39.rootCodes witnesses39 checked39

def witnesses40 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3857, 1792)]
theorem checked40 : privateTripleCheckB Source40.rootCodes witnesses40 = true := by decide +kernel
theorem root_binding40 : decodeSource Source40.rootCodes = link40 := by decide +kernel
theorem private40 : PrivateTriples link40 := by
  rw [← root_binding40]
  exact privateTripleCheck_sound Source40.rootCodes witnesses40 checked40
end C13.Global.PrivateData
