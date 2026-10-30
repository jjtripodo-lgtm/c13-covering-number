import C13Global.Irredundance
import C13Global.Data.Source41
import C13Global.Data.Source42
import C13Global.Data.Source43
import C13Global.Data.Source44
import C13Global.Data.Source45
import C13Global.Data.Source46
import C13Global.Data.Source47
import C13Global.Data.Source48
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses41 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3905, 1792)]
theorem checked41 : privateTripleCheckB Source41.rootCodes witnesses41 = true := by decide +kernel
theorem root_binding41 : decodeSource Source41.rootCodes = link41 := by decide +kernel
theorem private41 : PrivateTriples link41 := by
  rw [← root_binding41]
  exact privateTripleCheck_sound Source41.rootCodes witnesses41 checked41

def witnesses42 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3969, 1792)]
theorem checked42 : privateTripleCheckB Source42.rootCodes witnesses42 = true := by decide +kernel
theorem root_binding42 : decodeSource Source42.rootCodes = link42 := by decide +kernel
theorem private42 : PrivateTriples link42 := by
  rw [← root_binding42]
  exact privateTripleCheck_sound Source42.rootCodes witnesses42 checked42

def witnesses43 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3858, 1792)]
theorem checked43 : privateTripleCheckB Source43.rootCodes witnesses43 = true := by decide +kernel
theorem root_binding43 : decodeSource Source43.rootCodes = link43 := by decide +kernel
theorem private43 : PrivateTriples link43 := by
  rw [← root_binding43]
  exact privateTripleCheck_sound Source43.rootCodes witnesses43 checked43

def witnesses44 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3906, 1792)]
theorem checked44 : privateTripleCheckB Source44.rootCodes witnesses44 = true := by decide +kernel
theorem root_binding44 : decodeSource Source44.rootCodes = link44 := by decide +kernel
theorem private44 : PrivateTriples link44 := by
  rw [← root_binding44]
  exact privateTripleCheck_sound Source44.rootCodes witnesses44 checked44

def witnesses45 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3970, 1792)]
theorem checked45 : privateTripleCheckB Source45.rootCodes witnesses45 = true := by decide +kernel
theorem root_binding45 : decodeSource Source45.rootCodes = link45 := by decide +kernel
theorem private45 : PrivateTriples link45 := by
  rw [← root_binding45]
  exact privateTripleCheck_sound Source45.rootCodes witnesses45 checked45

def witnesses46 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3860, 1792)]
theorem checked46 : privateTripleCheckB Source46.rootCodes witnesses46 = true := by decide +kernel
theorem root_binding46 : decodeSource Source46.rootCodes = link46 := by decide +kernel
theorem private46 : PrivateTriples link46 := by
  rw [← root_binding46]
  exact privateTripleCheck_sound Source46.rootCodes witnesses46 checked46

def witnesses47 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3876, 1792)]
theorem checked47 : privateTripleCheckB Source47.rootCodes witnesses47 = true := by decide +kernel
theorem root_binding47 : decodeSource Source47.rootCodes = link47 := by decide +kernel
theorem private47 : PrivateTriples link47 := by
  rw [← root_binding47]
  exact privateTripleCheck_sound Source47.rootCodes witnesses47 checked47

def witnesses48 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (1265, 112), (3908, 1792)]
theorem checked48 : privateTripleCheckB Source48.rootCodes witnesses48 = true := by decide +kernel
theorem root_binding48 : decodeSource Source48.rootCodes = link48 := by decide +kernel
theorem private48 : PrivateTriples link48 := by
  rw [← root_binding48]
  exact privateTripleCheck_sound Source48.rootCodes witnesses48 checked48
end C13.Global.PrivateData
