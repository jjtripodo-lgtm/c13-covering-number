import C13Covering.OrbitRepresentatives.Part0
import C13Covering.OrbitRepresentatives.Part1
import C13Covering.OrbitRepresentatives.Part2
import C13Covering.OrbitRepresentatives.Part3
import C13Covering.OrbitRepresentatives.Part4
import C13Covering.OrbitRepresentatives.Part5
import C13Covering.OrbitRepresentatives.Part6
import C13Covering.OrbitRepresentatives.Part7
import C13Covering.OrbitRepresentatives.Part8
namespace C13.OrbitPilot.Representatives
open C13.OrbitPilot.Word
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem all_representatives (j : Fin 67) :
    catalogRepresentative j = indexedCompletion (representativeIndex j) := by
  fin_cases j
  · exact Part0.representative00
  · exact Part0.representative01
  · exact Part0.representative02
  · exact Part0.representative03
  · exact Part0.representative04
  · exact Part0.representative05
  · exact Part0.representative06
  · exact Part0.representative07
  · exact Part1.representative08
  · exact Part1.representative09
  · exact Part1.representative10
  · exact Part1.representative11
  · exact Part1.representative12
  · exact Part1.representative13
  · exact Part1.representative14
  · exact Part1.representative15
  · exact Part2.representative16
  · exact Part2.representative17
  · exact Part2.representative18
  · exact Part2.representative19
  · exact Part2.representative20
  · exact Part2.representative21
  · exact Part2.representative22
  · exact Part2.representative23
  · exact Part3.representative24
  · exact Part3.representative25
  · exact Part3.representative26
  · exact Part3.representative27
  · exact Part3.representative28
  · exact Part3.representative29
  · exact Part3.representative30
  · exact Part3.representative31
  · exact Part4.representative32
  · exact Part4.representative33
  · exact Part4.representative34
  · exact Part4.representative35
  · exact Part4.representative36
  · exact Part4.representative37
  · exact Part4.representative38
  · exact Part4.representative39
  · exact Part5.representative40
  · exact Part5.representative41
  · exact Part5.representative42
  · exact Part5.representative43
  · exact Part5.representative44
  · exact Part5.representative45
  · exact Part5.representative46
  · exact Part5.representative47
  · exact Part6.representative48
  · exact Part6.representative49
  · exact Part6.representative50
  · exact Part6.representative51
  · exact Part6.representative52
  · exact Part6.representative53
  · exact Part6.representative54
  · exact Part6.representative55
  · exact Part7.representative56
  · exact Part7.representative57
  · exact Part7.representative58
  · exact Part7.representative59
  · exact Part7.representative60
  · exact Part7.representative61
  · exact Part7.representative62
  · exact Part7.representative63
  · exact Part8.representative64
  · exact Part8.representative65
  · exact Part8.representative66

end C13.OrbitPilot.Representatives
