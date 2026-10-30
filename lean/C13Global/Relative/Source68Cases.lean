import C13Global.Relative.Source68Witnesses
namespace C13.Global.Relative.Source68
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source68
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def dualPart00 : List (Finset Point) := [{0,1,2,3},{0,3,6,9},{0,6,10,11},{0,7,8,9},{1,3,7,10},{1,6,8,10},{1,7,9,11},{2,3,8,11},{2,6,7,11},{2,8,9,10},{0,1,2,6},{0,1,2,7},{0,1,2,8},{0,1,2,9},{0,1,2,10}]

theorem dual_actual_part00 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart00) : ActualObstruction figure6 Q := by
  simp only [dualPart00,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query000 halph
  · exact query096 halph
  · exact query154 halph
  · exact query155 halph
  · exact query221 halph
  · exact query270 halph
  · exact query279 halph
  · exact query309 halph
  · exact query352 halph
  · exact query365 halph
  · exact query003 halph
  · exact query004 halph
  · exact query005 halph
  · exact query006 halph
  · exact query007 halph

def dualPart01 : List (Finset Point) := [{0,1,2,11},{0,1,6,8},{0,1,7,8},{0,1,9,11},{0,1,10,11},{0,2,6,7},{0,2,7,8},{0,2,9,10},{0,2,10,11},{0,3,7,8},{0,3,7,10},{0,3,8,11},{0,3,10,11},{0,6,7,8},{0,7,8,10}]

theorem dual_actual_part01 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart01) : ActualObstruction figure6 Q := by
  simp only [dualPart01,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query008 halph
  · exact query031 halph
  · exact query035 halph
  · exact query043 halph
  · exact query044 halph
  · exact query066 halph
  · exact query071 halph
  · exact query078 halph
  · exact query080 halph
  · exact query099 halph
  · exact query101 halph
  · exact query105 halph
  · exact query108 halph
  · exact query145 halph
  · exact query156 halph

def dualPart02 : List (Finset Point) := [{0,7,8,11},{0,7,10,11},{0,8,10,11},{0,9,10,11},{1,2,6,7},{1,2,6,8},{1,2,9,10},{1,2,9,11},{1,3,6,8},{1,3,6,9},{1,3,8,11},{1,3,9,11},{1,6,7,8},{1,6,8,9},{1,6,8,11}]

theorem dual_actual_part02 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart02) : ActualObstruction figure6 Q := by
  simp only [dualPart02,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query157 halph
  · exact query160 halph
  · exact query163 halph
  · exact query164 halph
  · exact query186 halph
  · exact query187 halph
  · exact query198 halph
  · exact query199 halph
  · exact query215 halph
  · exact query216 halph
  · exact query225 halph
  · exact query227 halph
  · exact query265 halph
  · exact query269 halph
  · exact query271 halph

def dualPart03 : List (Finset Point) := [{1,6,9,11},{1,8,9,11},{1,9,10,11},{2,3,6,7},{2,3,6,9},{2,3,7,10},{2,3,9,10},{2,6,7,8},{2,6,7,9},{2,6,7,10},{2,6,9,10},{2,7,9,10},{2,9,10,11},{3,6,7,9},{3,6,7,10}]

theorem dual_actual_part03 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart03) : ActualObstruction figure6 Q := by
  simp only [dualPart03,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query273 halph
  · exact query282 halph
  · exact query284 halph
  · exact query298 halph
  · exact query300 halph
  · exact query305 halph
  · exact query310 halph
  · exact query349 halph
  · exact query350 halph
  · exact query351 halph
  · exact query356 halph
  · exact query362 halph
  · exact query368 halph
  · exact query406 halph
  · exact query407 halph

def dualPart04 : List (Finset Point) := [{3,6,8,9},{3,6,8,11},{3,6,9,10},{3,6,9,11},{3,7,8,10},{3,7,8,11},{3,7,9,10},{3,7,10,11},{3,8,9,11},{3,8,10,11},{0,1,3,6},{0,1,3,7},{0,1,3,9},{0,1,3,10},{0,1,6,10}]

theorem dual_actual_part04 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart04) : ActualObstruction figure6 Q := by
  simp only [dualPart04,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query409 halph
  · exact query411 halph
  · exact query412 halph
  · exact query413 halph
  · exact query416 halph
  · exact query417 halph
  · exact query418 halph
  · exact query420 halph
  · exact query422 halph
  · exact query423 halph
  · exact query011 halph
  · exact query012 halph
  · exact query014 halph
  · exact query015 halph
  · exact query033 halph

def dualPart05 : List (Finset Point) := [{0,1,7,9},{0,2,3,6},{0,2,3,8},{0,2,3,9},{0,2,3,11},{0,2,6,11},{0,2,8,9},{0,3,6,10},{0,3,6,11},{0,3,7,9},{0,3,8,9},{0,6,7,9},{0,6,7,11},{0,6,8,9},{0,6,8,10}]

theorem dual_actual_part05 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart05) : ActualObstruction figure6 Q := by
  simp only [dualPart05,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query036 halph
  · exact query047 halph
  · exact query049 halph
  · exact query050 halph
  · exact query052 halph
  · exact query070 halph
  · exact query075 halph
  · exact query097 halph
  · exact query098 halph
  · exact query100 halph
  · exact query103 halph
  · exact query146 halph
  · exact query148 halph
  · exact query149 halph
  · exact query150 halph

def dualPart06 : List (Finset Point) := [{0,6,9,10},{0,6,9,11},{0,7,9,11},{0,8,9,10},{1,2,3,7},{1,2,3,8},{1,2,3,10},{1,2,3,11},{1,2,7,11},{1,2,8,10},{1,3,6,10},{1,3,7,9},{1,3,7,11},{1,3,8,10},{1,6,7,10}]

theorem dual_actual_part06 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart06) : ActualObstruction figure6 Q := by
  simp only [dualPart06,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query152 halph
  · exact query153 halph
  · exact query159 halph
  · exact query161 halph
  · exact query168 halph
  · exact query169 halph
  · exact query171 halph
  · exact query172 halph
  · exact query194 halph
  · exact query196 halph
  · exact query217 halph
  · exact query220 halph
  · exact query222 halph
  · exact query224 halph
  · exact query267 halph

def dualPart07 : List (Finset Point) := [{1,6,7,11},{1,6,10,11},{1,7,8,9},{1,7,8,10},{1,7,9,10},{1,7,10,11},{1,8,9,10},{2,3,6,11},{2,3,7,11},{2,3,8,9},{2,3,8,10},{2,6,8,10},{2,6,8,11},{2,6,10,11},{2,7,8,9}]

theorem dual_actual_part07 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart07) : ActualObstruction figure6 Q := by
  simp only [dualPart07,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query268 halph
  · exact query274 halph
  · exact query275 halph
  · exact query276 halph
  · exact query278 halph
  · exact query280 halph
  · exact query281 halph
  · exact query302 halph
  · exact query306 halph
  · exact query307 halph
  · exact query308 halph
  · exact query354 halph
  · exact query355 halph
  · exact query358 halph
  · exact query359 halph

def dualPart08 : List (Finset Point) := [{2,7,8,11},{2,7,9,11},{2,8,9,11},{2,8,10,11},{6,7,9,11},{6,7,10,11},{6,8,9,10},{6,8,10,11},{7,8,9,10},{7,8,9,11},{0,1,3,8},{0,1,3,11},{0,1,6,9},{0,1,6,11},{0,1,7,10}]

theorem dual_actual_part08 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart08) : ActualObstruction figure6 Q := by
  simp only [dualPart08,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query361 halph
  · exact query363 halph
  · exact query366 halph
  · exact query367 halph
  · exact query484 halph
  · exact query485 halph
  · exact query486 halph
  · exact query488 halph
  · exact query490 halph
  · exact query491 halph
  · exact query013 halph
  · exact query016 halph
  · exact query032 halph
  · exact query034 halph
  · exact query037 halph

def dualPart09 : List (Finset Point) := [{0,1,7,11},{0,1,8,9},{0,1,8,10},{0,2,3,7},{0,2,3,10},{0,2,6,9},{0,2,6,10},{0,2,7,9},{0,2,7,11},{0,2,8,10},{0,2,8,11},{0,3,6,7},{0,3,6,8},{0,3,9,10},{0,3,9,11}]

theorem dual_actual_part09 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart09) : ActualObstruction figure6 Q := by
  simp only [dualPart09,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query038 halph
  · exact query039 halph
  · exact query040 halph
  · exact query048 halph
  · exact query051 halph
  · exact query068 halph
  · exact query069 halph
  · exact query072 halph
  · exact query074 halph
  · exact query076 halph
  · exact query077 halph
  · exact query094 halph
  · exact query095 halph
  · exact query106 halph
  · exact query107 halph

def dualPart10 : List (Finset Point) := [{0,6,7,10},{0,6,8,11},{0,7,9,10},{0,8,9,11},{1,2,3,6},{1,2,3,9},{1,2,6,10},{1,2,6,11},{1,2,7,9},{1,2,7,10},{1,2,8,9},{1,2,8,11},{1,3,6,7},{1,3,7,8},{1,3,9,10}]

theorem dual_actual_part10 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart10) : ActualObstruction figure6 Q := by
  simp only [dualPart10,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query147 halph
  · exact query151 halph
  · exact query158 halph
  · exact query162 halph
  · exact query167 halph
  · exact query170 halph
  · exact query189 halph
  · exact query190 halph
  · exact query192 halph
  · exact query193 halph
  · exact query195 halph
  · exact query197 halph
  · exact query214 halph
  · exact query219 halph
  · exact query226 halph

def dualPart11 : List (Finset Point) := [{1,3,10,11},{1,6,7,9},{1,6,9,10},{1,7,8,11},{1,8,10,11},{2,3,6,8},{2,3,7,8},{2,3,9,11},{2,3,10,11},{2,6,8,9},{2,6,9,11},{2,7,8,10},{2,7,10,11},{3,6,7,11},{3,6,8,10}]

theorem dual_actual_part11 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart11) : ActualObstruction figure6 Q := by
  simp only [dualPart11,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query228 halph
  · exact query266 halph
  · exact query272 halph
  · exact query277 halph
  · exact query283 halph
  · exact query299 halph
  · exact query303 halph
  · exact query311 halph
  · exact query312 halph
  · exact query353 halph
  · exact query357 halph
  · exact query360 halph
  · exact query364 halph
  · exact query408 halph
  · exact query410 halph

def dualPart12 : List (Finset Point) := [{3,6,10,11},{3,7,8,9},{3,7,9,11},{3,8,9,10},{6,7,8,9},{6,7,8,10},{6,7,8,11},{6,9,10,11},{7,9,10,11},{8,9,10,11},{0,1,6,7},{0,1,9,10},{0,2,6,8},{0,2,9,11},{0,3,7,11}]

theorem dual_actual_part12 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart12) : ActualObstruction figure6 Q := by
  simp only [dualPart12,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query414 halph
  · exact query415 halph
  · exact query419 halph
  · exact query421 halph
  · exact query480 halph
  · exact query481 halph
  · exact query482 halph
  · exact query489 halph
  · exact query493 halph
  · exact query494 halph
  · exact query030 halph
  · exact query042 halph
  · exact query067 halph
  · exact query079 halph
  · exact query102 halph

def dualPart13 : List (Finset Point) := [{0,3,8,10},{1,2,7,8},{1,2,10,11},{1,3,6,11},{1,3,8,9},{2,3,6,10},{2,3,7,9},{6,7,9,10},{6,8,9,11},{7,8,10,11},{0,1,8,11},{0,2,7,10},{1,2,6,9},{3,6,7,8},{3,9,10,11}]

theorem dual_actual_part13 (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualPart13) : ActualObstruction figure6 Q := by
  simp only [dualPart13,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query104 halph
  · exact query191 halph
  · exact query200 halph
  · exact query218 halph
  · exact query223 halph
  · exact query301 halph
  · exact query304 halph
  · exact query483 halph
  · exact query487 halph
  · exact query492 halph
  · exact hhard {0,1,8,11} (by decide +kernel)
  · exact hhard {0,2,7,10} (by decide +kernel)
  · exact hhard {1,2,6,9} (by decide +kernel)
  · exact hhard {3,6,7,8} (by decide +kernel)
  · exact hhard {3,9,10,11} (by decide +kernel)

theorem dualQuads_parts : dualQuads = dualPart00 ++ dualPart01 ++ dualPart02 ++ dualPart03 ++ dualPart04 ++ dualPart05 ++ dualPart06 ++ dualPart07 ++ dualPart08 ++ dualPart09 ++ dualPart10 ++ dualPart11 ++ dualPart12 ++ dualPart13 := by rfl

theorem dual_actual (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction figure6 Q := by
  rw [dualQuads_parts] at hQ
  simp only [List.mem_append,or_assoc] at hQ
  rcases hQ with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13
  · exact dual_actual_part00 halph hhard Q h00
  · exact dual_actual_part01 halph hhard Q h01
  · exact dual_actual_part02 halph hhard Q h02
  · exact dual_actual_part03 halph hhard Q h03
  · exact dual_actual_part04 halph hhard Q h04
  · exact dual_actual_part05 halph hhard Q h05
  · exact dual_actual_part06 halph hhard Q h06
  · exact dual_actual_part07 halph hhard Q h07
  · exact dual_actual_part08 halph hhard Q h08
  · exact dual_actual_part09 halph hhard Q h09
  · exact dual_actual_part10 halph hhard Q h10
  · exact dual_actual_part11 halph hhard Q h11
  · exact dual_actual_part12 halph hhard Q h12
  · exact dual_actual_part13 halph hhard Q h13
end C13.Global.Relative.Source68
