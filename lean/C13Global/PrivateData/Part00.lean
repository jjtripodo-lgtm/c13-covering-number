import C13Global.Irredundance
import C13Global.Data.Source01
import C13Global.Data.Source02
import C13Global.Data.Source03
import C13Global.Data.Source04
import C13Global.Data.Source05
import C13Global.Data.Source06
import C13Global.Data.Source07
import C13Global.Data.Source08
namespace C13.Global.PrivateData
open C13.SourceData C13.Enumeration
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def witnesses01 : List (Code × Code) := [(819, 529), (3267, 2113), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3843, 1792)]
theorem checked01 : privateTripleCheckB Source01.rootCodes witnesses01 = true := by decide +kernel
theorem root_binding01 : decodeSource Source01.rootCodes = link01 := by decide +kernel
theorem private01 : PrivateTriples link01 := by
  rw [← root_binding01]
  exact privateTripleCheck_sound Source01.rootCodes witnesses01 checked01

def witnesses02 : List (Code × Code) := [(819, 259), (3267, 1027), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3845, 1792)]
theorem checked02 : privateTripleCheckB Source02.rootCodes witnesses02 = true := by decide +kernel
theorem root_binding02 : decodeSource Source02.rootCodes = link02 := by decide +kernel
theorem private02 : PrivateTriples link02 := by
  rw [← root_binding02]
  exact privateTripleCheck_sound Source02.rootCodes witnesses02 checked02

def witnesses03 : List (Code × Code) := [(819, 259), (3267, 1027), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3857, 1792)]
theorem checked03 : privateTripleCheckB Source03.rootCodes witnesses03 = true := by decide +kernel
theorem root_binding03 : decodeSource Source03.rootCodes = link03 := by decide +kernel
theorem private03 : PrivateTriples link03 := by
  rw [← root_binding03]
  exact privateTripleCheck_sound Source03.rootCodes witnesses03 checked03

def witnesses04 : List (Code × Code) := [(819, 259), (3267, 1027), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3905, 1792)]
theorem checked04 : privateTripleCheckB Source04.rootCodes witnesses04 = true := by decide +kernel
theorem root_binding04 : decodeSource Source04.rootCodes = link04 := by decide +kernel
theorem private04 : PrivateTriples link04 := by
  rw [← root_binding04]
  exact privateTripleCheck_sound Source04.rootCodes witnesses04 checked04

def witnesses05 : List (Code × Code) := [(819, 259), (3267, 1027), (3132, 2068), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3852, 1792)]
theorem checked05 : privateTripleCheckB Source05.rootCodes witnesses05 = true := by decide +kernel
theorem root_binding05 : decodeSource Source05.rootCodes = link05 := by decide +kernel
theorem private05 : PrivateTriples link05 := by
  rw [← root_binding05]
  exact privateTripleCheck_sound Source05.rootCodes witnesses05 checked05

def witnesses06 : List (Code × Code) := [(819, 259), (3267, 1027), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (243, 112), (3908, 1792)]
theorem checked06 : privateTripleCheckB Source06.rootCodes witnesses06 = true := by decide +kernel
theorem root_binding06 : decodeSource Source06.rootCodes = link06 := by decide +kernel
theorem private06 : PrivateTriples link06 := by
  rw [← root_binding06]
  exact privateTripleCheck_sound Source06.rootCodes witnesses06 checked06

def witnesses07 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 261), (2725, 517), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (245, 112)]
theorem checked07 : privateTripleCheckB Source07.rootCodes witnesses07 = true := by decide +kernel
theorem root_binding07 : decodeSource Source07.rootCodes = link07 := by decide +kernel
theorem private07 : PrivateTriples link07 := by
  rw [← root_binding07]
  exact privateTripleCheck_sound Source07.rootCodes witnesses07 checked07

def witnesses08 : List (Code × Code) := [(819, 529), (3267, 67), (3132, 1036), (972, 76), (1365, 69), (2725, 133), (2650, 74), (1450, 138), (2457, 137), (1641, 73), (1686, 134), (2406, 70), (63, 7), (3843, 1792), (497, 112)]
theorem checked08 : privateTripleCheckB Source08.rootCodes witnesses08 = true := by decide +kernel
theorem root_binding08 : decodeSource Source08.rootCodes = link08 := by decide +kernel
theorem private08 : PrivateTriples link08 := by
  rw [← root_binding08]
  exact privateTripleCheck_sound Source08.rootCodes witnesses08 checked08
end C13.Global.PrivateData
