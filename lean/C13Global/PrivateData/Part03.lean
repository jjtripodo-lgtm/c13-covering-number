import C13Global.Irredundance
import C13Global.Data.Source25
import C13Global.Data.Source26
import C13Global.Data.Source27
import C13Global.Data.Source28
import C13Global.Data.Source29
import C13Global.Data.Source30
import C13Global.Data.Source31
import C13Global.Data.Source32
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses25 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3845, 1792), (2544, 112)]
theorem checked25 : privateTripleCheckB Source25.rootCodes witnesses25 = true := by decide +kernel
theorem root_binding25 : decodeSource Source25.rootCodes = link25 := by decide +kernel
theorem private25 : PrivateTriples link25 := by
  rw [← root_binding25]
  exact privateTripleCheck_sound Source25.rootCodes witnesses25 checked25

def witnesses26 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3857, 1792)]
theorem checked26 : privateTripleCheckB Source26.rootCodes witnesses26 = true := by decide +kernel
theorem root_binding26 : decodeSource Source26.rootCodes = link26 := by decide +kernel
theorem private26 : PrivateTriples link26 := by
  rw [← root_binding26]
  exact privateTripleCheck_sound Source26.rootCodes witnesses26 checked26

def witnesses27 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3873, 1792)]
theorem checked27 : privateTripleCheckB Source27.rootCodes witnesses27 = true := by decide +kernel
theorem root_binding27 : decodeSource Source27.rootCodes = link27 := by decide +kernel
theorem private27 : PrivateTriples link27 := by
  rw [← root_binding27]
  exact privateTripleCheck_sound Source27.rootCodes witnesses27 checked27

def witnesses28 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3905, 1792)]
theorem checked28 : privateTripleCheckB Source28.rootCodes witnesses28 = true := by decide +kernel
theorem root_binding28 : decodeSource Source28.rootCodes = link28 := by decide +kernel
theorem private28 : PrivateTriples link28 := by
  rw [← root_binding28]
  exact privateTripleCheck_sound Source28.rootCodes witnesses28 checked28

def witnesses29 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3858, 1792)]
theorem checked29 : privateTripleCheckB Source29.rootCodes witnesses29 = true := by decide +kernel
theorem root_binding29 : decodeSource Source29.rootCodes = link29 := by decide +kernel
theorem private29 : PrivateTriples link29 := by
  rw [← root_binding29]
  exact privateTripleCheck_sound Source29.rootCodes witnesses29 checked29

def witnesses30 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3874, 1792)]
theorem checked30 : privateTripleCheckB Source30.rootCodes witnesses30 = true := by decide +kernel
theorem root_binding30 : decodeSource Source30.rootCodes = link30 := by decide +kernel
theorem private30 : PrivateTriples link30 := by
  rw [← root_binding30]
  exact privateTripleCheck_sound Source30.rootCodes witnesses30 checked30

def witnesses31 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3906, 1792)]
theorem checked31 : privateTripleCheckB Source31.rootCodes witnesses31 = true := by decide +kernel
theorem root_binding31 : decodeSource Source31.rootCodes = link31 := by decide +kernel
theorem private31 : PrivateTriples link31 := by
  rw [← root_binding31]
  exact privateTripleCheck_sound Source31.rootCodes witnesses31 checked31

def witnesses32 : List (Code × Code) := [(819, 259), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (497, 112), (3860, 1792)]
theorem checked32 : privateTripleCheckB Source32.rootCodes witnesses32 = true := by decide +kernel
theorem root_binding32 : decodeSource Source32.rootCodes = link32 := by decide +kernel
theorem private32 : PrivateTriples link32 := by
  rw [← root_binding32]
  exact privateTripleCheck_sound Source32.rootCodes witnesses32 checked32
end C13.Global.PrivateData
