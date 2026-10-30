import C13Enumeration.PartialStar
import Mathlib.Data.Fin.VecNotation
import C13Covering.SourceLiterals
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def values : Array Nat := #[4,1,1,1,2,2,0,2,1,1,4,1,0,1,3,1,1,1,1,0,1,1,1,1,3,0,1,1,3,1,1,1,0,1,3,1,1,1,0,1,1,1,3,1,1,0,1,1,3,1,1,0,2,1,1,1,3,1,0,1,1,1,2,1,0,2,1,1,1,1,3,0,1,1,1,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,1,1,1,1,0,3,1,1,2,1,0,1,1,3,1,1,1,0,1,3,1,1,1,0,1,1,1,3,1,1,0,1,1,3,1,1,0,4,1,1,1,2,2,0,2,1,1,4,1,0,1,3,1,1,1,1,0,1,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link09 6) a b := by decide +kernel

def maps : List (Point → Point) := [
  ![0,1,2,3,4,5,12,7,8,9,10,11,6],
  ![0,1,2,9,4,5,12,7,8,3,10,11,6],
  ![0,1,8,3,4,5,12,7,2,9,10,11,6],
  ![0,1,8,9,4,5,12,7,2,3,10,11,6],
  ![0,11,2,3,4,5,12,7,8,9,10,1,6],
  ![0,11,2,9,4,5,12,7,8,3,10,1,6],
  ![0,11,8,3,4,5,12,7,2,9,10,1,6],
  ![0,11,8,9,4,5,12,7,2,3,10,1,6],
  ![0,3,2,1,4,7,12,5,8,11,10,9,6],
  ![0,3,2,11,4,7,12,5,8,1,10,9,6],
  ![0,3,8,1,4,7,12,5,2,11,10,9,6],
  ![0,3,8,11,4,7,12,5,2,1,10,9,6],
  ![0,9,2,1,4,7,12,5,8,11,10,3,6],
  ![0,9,2,11,4,7,12,5,8,1,10,3,6],
  ![0,9,8,1,4,7,12,5,2,11,10,3,6],
  ![0,9,8,11,4,7,12,5,2,1,10,3,6],
  ![0,1,3,2,5,4,12,7,9,8,10,11,6],
  ![0,1,3,8,5,4,12,7,9,2,10,11,6],
  ![0,1,9,2,5,4,12,7,3,8,10,11,6],
  ![0,1,9,8,5,4,12,7,3,2,10,11,6],
  ![0,11,3,2,5,4,12,7,9,8,10,1,6],
  ![0,11,3,8,5,4,12,7,9,2,10,1,6],
  ![0,11,9,2,5,4,12,7,3,8,10,1,6],
  ![0,11,9,8,5,4,12,7,3,2,10,1,6],
  ![0,2,3,1,5,7,12,4,9,11,10,8,6],
  ![0,2,3,11,5,7,12,4,9,1,10,8,6],
  ![0,2,9,1,5,7,12,4,3,11,10,8,6],
  ![0,2,9,11,5,7,12,4,3,1,10,8,6],
  ![0,8,3,1,5,7,12,4,9,11,10,2,6],
  ![0,8,3,11,5,7,12,4,9,1,10,2,6],
  ![0,8,9,1,5,7,12,4,3,11,10,2,6],
  ![0,8,9,11,5,7,12,4,3,1,10,2,6],
  ![0,3,1,2,7,4,12,5,11,8,10,9,6],
  ![0,3,1,8,7,4,12,5,11,2,10,9,6],
  ![0,3,11,2,7,4,12,5,1,8,10,9,6],
  ![0,3,11,8,7,4,12,5,1,2,10,9,6],
  ![0,9,1,2,7,4,12,5,11,8,10,3,6],
  ![0,9,1,8,7,4,12,5,11,2,10,3,6],
  ![0,9,11,2,7,4,12,5,1,8,10,3,6],
  ![0,9,11,8,7,4,12,5,1,2,10,3,6],
  ![0,2,1,3,7,5,12,4,11,9,10,8,6],
  ![0,2,1,9,7,5,12,4,11,3,10,8,6],
  ![0,2,11,3,7,5,12,4,1,9,10,8,6],
  ![0,2,11,9,7,5,12,4,1,3,10,8,6],
  ![0,8,1,3,7,5,12,4,11,9,10,2,6],
  ![0,8,1,9,7,5,12,4,11,3,10,2,6],
  ![0,8,11,3,7,5,12,4,1,9,10,2,6],
  ![0,8,11,9,7,5,12,4,1,3,10,2,6],
  ![10,1,2,3,4,5,12,7,8,9,0,11,6],
  ![10,1,2,9,4,5,12,7,8,3,0,11,6],
  ![10,1,8,3,4,5,12,7,2,9,0,11,6],
  ![10,1,8,9,4,5,12,7,2,3,0,11,6],
  ![10,11,2,3,4,5,12,7,8,9,0,1,6],
  ![10,11,2,9,4,5,12,7,8,3,0,1,6],
  ![10,11,8,3,4,5,12,7,2,9,0,1,6],
  ![10,11,8,9,4,5,12,7,2,3,0,1,6],
  ![10,3,2,1,4,7,12,5,8,11,0,9,6],
  ![10,3,2,11,4,7,12,5,8,1,0,9,6],
  ![10,3,8,1,4,7,12,5,2,11,0,9,6],
  ![10,3,8,11,4,7,12,5,2,1,0,9,6],
  ![10,9,2,1,4,7,12,5,8,11,0,3,6],
  ![10,9,2,11,4,7,12,5,8,1,0,3,6],
  ![10,9,8,1,4,7,12,5,2,11,0,3,6],
  ![10,9,8,11,4,7,12,5,2,1,0,3,6],
  ![10,1,3,2,5,4,12,7,9,8,0,11,6],
  ![10,1,3,8,5,4,12,7,9,2,0,11,6],
  ![10,1,9,2,5,4,12,7,3,8,0,11,6],
  ![10,1,9,8,5,4,12,7,3,2,0,11,6],
  ![10,11,3,2,5,4,12,7,9,8,0,1,6],
  ![10,11,3,8,5,4,12,7,9,2,0,1,6],
  ![10,11,9,2,5,4,12,7,3,8,0,1,6],
  ![10,11,9,8,5,4,12,7,3,2,0,1,6],
  ![10,2,3,1,5,7,12,4,9,11,0,8,6],
  ![10,2,3,11,5,7,12,4,9,1,0,8,6],
  ![10,2,9,1,5,7,12,4,3,11,0,8,6],
  ![10,2,9,11,5,7,12,4,3,1,0,8,6],
  ![10,8,3,1,5,7,12,4,9,11,0,2,6],
  ![10,8,3,11,5,7,12,4,9,1,0,2,6],
  ![10,8,9,1,5,7,12,4,3,11,0,2,6],
  ![10,8,9,11,5,7,12,4,3,1,0,2,6],
  ![10,3,1,2,7,4,12,5,11,8,0,9,6],
  ![10,3,1,8,7,4,12,5,11,2,0,9,6],
  ![10,3,11,2,7,4,12,5,1,8,0,9,6],
  ![10,3,11,8,7,4,12,5,1,2,0,9,6],
  ![10,9,1,2,7,4,12,5,11,8,0,3,6],
  ![10,9,1,8,7,4,12,5,11,2,0,3,6],
  ![10,9,11,2,7,4,12,5,1,8,0,3,6],
  ![10,9,11,8,7,4,12,5,1,2,0,3,6],
  ![10,2,1,3,7,5,12,4,11,9,0,8,6],
  ![10,2,1,9,7,5,12,4,11,3,0,8,6],
  ![10,2,11,3,7,5,12,4,1,9,0,8,6],
  ![10,2,11,9,7,5,12,4,1,3,0,8,6],
  ![10,8,1,3,7,5,12,4,11,9,0,2,6],
  ![10,8,1,9,7,5,12,4,11,3,0,2,6],
  ![10,8,11,3,7,5,12,4,1,9,0,2,6],
  ![10,8,11,9,7,5,12,4,1,3,0,2,6]
]
theorem maps_count : maps.length = 96 := by rfl
def step := starStep (link link09 6) (link link09 6) matrix matrix
def finish := mapFinish link09 hole 6
def table0 : Point → Point := anchorTable hole hole 6
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 10 10
def table3 : Point → Point := put table2 1 1
def table4 : Point → Point := put table3 2 2
def table5 : Point → Point := put table4 3 3
def table6 : Point → Point := put table5 4 4
def table7 : Point → Point := put table6 5 5
def table8 : Point → Point := put table7 7 7
def table9 : Point → Point := put table8 8 8
def table10 : Point → Point := put table9 9 9
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table4 3 9
def table13 : Point → Point := put table12 4 4
def table14 : Point → Point := put table13 5 5
def table15 : Point → Point := put table14 7 7
def table16 : Point → Point := put table15 8 8
def table17 : Point → Point := put table16 9 3
def table18 : Point → Point := put table17 11 11
def table19 : Point → Point := put table3 2 3
def table20 : Point → Point := put table19 3 2
def table21 : Point → Point := put table20 4 5
def table22 : Point → Point := put table21 5 4
def table23 : Point → Point := put table22 7 7
def table24 : Point → Point := put table23 8 9
def table25 : Point → Point := put table24 9 8
def table26 : Point → Point := put table25 11 11
def table27 : Point → Point := put table19 3 8
def table28 : Point → Point := put table27 4 5
def table29 : Point → Point := put table28 5 4
def table30 : Point → Point := put table29 7 7
def table31 : Point → Point := put table30 8 9
def table32 : Point → Point := put table31 9 2
def table33 : Point → Point := put table32 11 11
def table34 : Point → Point := put table3 2 8
def table35 : Point → Point := put table34 3 3
def table36 : Point → Point := put table35 4 4
def table37 : Point → Point := put table36 5 5
def table38 : Point → Point := put table37 7 7
def table39 : Point → Point := put table38 8 2
def table40 : Point → Point := put table39 9 9
def table41 : Point → Point := put table40 11 11
def table42 : Point → Point := put table34 3 9
def table43 : Point → Point := put table42 4 4
def table44 : Point → Point := put table43 5 5
def table45 : Point → Point := put table44 7 7
def table46 : Point → Point := put table45 8 2
def table47 : Point → Point := put table46 9 3
def table48 : Point → Point := put table47 11 11
def table49 : Point → Point := put table3 2 9
def table50 : Point → Point := put table49 3 2
def table51 : Point → Point := put table50 4 5
def table52 : Point → Point := put table51 5 4
def table53 : Point → Point := put table52 7 7
def table54 : Point → Point := put table53 8 3
def table55 : Point → Point := put table54 9 8
def table56 : Point → Point := put table55 11 11
def table57 : Point → Point := put table49 3 8
def table58 : Point → Point := put table57 4 5
def table59 : Point → Point := put table58 5 4
def table60 : Point → Point := put table59 7 7
def table61 : Point → Point := put table60 8 3
def table62 : Point → Point := put table61 9 2
def table63 : Point → Point := put table62 11 11
def table64 : Point → Point := put table2 1 2
def table65 : Point → Point := put table64 2 1
def table66 : Point → Point := put table65 3 3
def table67 : Point → Point := put table66 4 7
def table68 : Point → Point := put table67 5 5
def table69 : Point → Point := put table68 7 4
def table70 : Point → Point := put table69 8 11
def table71 : Point → Point := put table70 9 9
def table72 : Point → Point := put table71 11 8
def table73 : Point → Point := put table65 3 9
def table74 : Point → Point := put table73 4 7
def table75 : Point → Point := put table74 5 5
def table76 : Point → Point := put table75 7 4
def table77 : Point → Point := put table76 8 11
def table78 : Point → Point := put table77 9 3
def table79 : Point → Point := put table78 11 8
def table80 : Point → Point := put table64 2 3
def table81 : Point → Point := put table80 3 1
def table82 : Point → Point := put table81 4 5
def table83 : Point → Point := put table82 5 7
def table84 : Point → Point := put table83 7 4
def table85 : Point → Point := put table84 8 9
def table86 : Point → Point := put table85 9 11
def table87 : Point → Point := put table86 11 8
def table88 : Point → Point := put table80 3 11
def table89 : Point → Point := put table88 4 5
def table90 : Point → Point := put table89 5 7
def table91 : Point → Point := put table90 7 4
def table92 : Point → Point := put table91 8 9
def table93 : Point → Point := put table92 9 1
def table94 : Point → Point := put table93 11 8
def table95 : Point → Point := put table64 2 9
def table96 : Point → Point := put table95 3 1
def table97 : Point → Point := put table96 4 5
def table98 : Point → Point := put table97 5 7
def table99 : Point → Point := put table98 7 4
def table100 : Point → Point := put table99 8 3
def table101 : Point → Point := put table100 9 11
def table102 : Point → Point := put table101 11 8
def table103 : Point → Point := put table95 3 11
def table104 : Point → Point := put table103 4 5
def table105 : Point → Point := put table104 5 7
def table106 : Point → Point := put table105 7 4
def table107 : Point → Point := put table106 8 3
def table108 : Point → Point := put table107 9 1
def table109 : Point → Point := put table108 11 8
def table110 : Point → Point := put table64 2 11
def table111 : Point → Point := put table110 3 3
def table112 : Point → Point := put table111 4 7
def table113 : Point → Point := put table112 5 5
def table114 : Point → Point := put table113 7 4
def table115 : Point → Point := put table114 8 1
def table116 : Point → Point := put table115 9 9
def table117 : Point → Point := put table116 11 8
def table118 : Point → Point := put table110 3 9
def table119 : Point → Point := put table118 4 7
def table120 : Point → Point := put table119 5 5
def table121 : Point → Point := put table120 7 4
def table122 : Point → Point := put table121 8 1
def table123 : Point → Point := put table122 9 3
def table124 : Point → Point := put table123 11 8
def table125 : Point → Point := put table2 1 3
def table126 : Point → Point := put table125 2 1
def table127 : Point → Point := put table126 3 2
def table128 : Point → Point := put table127 4 7
def table129 : Point → Point := put table128 5 4
def table130 : Point → Point := put table129 7 5
def table131 : Point → Point := put table130 8 11
def table132 : Point → Point := put table131 9 8
def table133 : Point → Point := put table132 11 9
def table134 : Point → Point := put table126 3 8
def table135 : Point → Point := put table134 4 7
def table136 : Point → Point := put table135 5 4
def table137 : Point → Point := put table136 7 5
def table138 : Point → Point := put table137 8 11
def table139 : Point → Point := put table138 9 2
def table140 : Point → Point := put table139 11 9
def table141 : Point → Point := put table125 2 2
def table142 : Point → Point := put table141 3 1
def table143 : Point → Point := put table142 4 4
def table144 : Point → Point := put table143 5 7
def table145 : Point → Point := put table144 7 5
def table146 : Point → Point := put table145 8 8
def table147 : Point → Point := put table146 9 11
def table148 : Point → Point := put table147 11 9
def table149 : Point → Point := put table141 3 11
def table150 : Point → Point := put table149 4 4
def table151 : Point → Point := put table150 5 7
def table152 : Point → Point := put table151 7 5
def table153 : Point → Point := put table152 8 8
def table154 : Point → Point := put table153 9 1
def table155 : Point → Point := put table154 11 9
def table156 : Point → Point := put table125 2 8
def table157 : Point → Point := put table156 3 1
def table158 : Point → Point := put table157 4 4
def table159 : Point → Point := put table158 5 7
def table160 : Point → Point := put table159 7 5
def table161 : Point → Point := put table160 8 2
def table162 : Point → Point := put table161 9 11
def table163 : Point → Point := put table162 11 9
def table164 : Point → Point := put table156 3 11
def table165 : Point → Point := put table164 4 4
def table166 : Point → Point := put table165 5 7
def table167 : Point → Point := put table166 7 5
def table168 : Point → Point := put table167 8 2
def table169 : Point → Point := put table168 9 1
def table170 : Point → Point := put table169 11 9
def table171 : Point → Point := put table125 2 11
def table172 : Point → Point := put table171 3 2
def table173 : Point → Point := put table172 4 7
def table174 : Point → Point := put table173 5 4
def table175 : Point → Point := put table174 7 5
def table176 : Point → Point := put table175 8 1
def table177 : Point → Point := put table176 9 8
def table178 : Point → Point := put table177 11 9
def table179 : Point → Point := put table171 3 8
def table180 : Point → Point := put table179 4 7
def table181 : Point → Point := put table180 5 4
def table182 : Point → Point := put table181 7 5
def table183 : Point → Point := put table182 8 1
def table184 : Point → Point := put table183 9 2
def table185 : Point → Point := put table184 11 9
def table186 : Point → Point := put table2 1 8
def table187 : Point → Point := put table186 2 1
def table188 : Point → Point := put table187 3 3
def table189 : Point → Point := put table188 4 7
def table190 : Point → Point := put table189 5 5
def table191 : Point → Point := put table190 7 4
def table192 : Point → Point := put table191 8 11
def table193 : Point → Point := put table192 9 9
def table194 : Point → Point := put table193 11 2
def table195 : Point → Point := put table187 3 9
def table196 : Point → Point := put table195 4 7
def table197 : Point → Point := put table196 5 5
def table198 : Point → Point := put table197 7 4
def table199 : Point → Point := put table198 8 11
def table200 : Point → Point := put table199 9 3
def table201 : Point → Point := put table200 11 2
def table202 : Point → Point := put table186 2 3
def table203 : Point → Point := put table202 3 1
def table204 : Point → Point := put table203 4 5
def table205 : Point → Point := put table204 5 7
def table206 : Point → Point := put table205 7 4
def table207 : Point → Point := put table206 8 9
def table208 : Point → Point := put table207 9 11
def table209 : Point → Point := put table208 11 2
def table210 : Point → Point := put table202 3 11
def table211 : Point → Point := put table210 4 5
def table212 : Point → Point := put table211 5 7
def table213 : Point → Point := put table212 7 4
def table214 : Point → Point := put table213 8 9
def table215 : Point → Point := put table214 9 1
def table216 : Point → Point := put table215 11 2
def table217 : Point → Point := put table186 2 9
def table218 : Point → Point := put table217 3 1
def table219 : Point → Point := put table218 4 5
def table220 : Point → Point := put table219 5 7
def table221 : Point → Point := put table220 7 4
def table222 : Point → Point := put table221 8 3
def table223 : Point → Point := put table222 9 11
def table224 : Point → Point := put table223 11 2
def table225 : Point → Point := put table217 3 11
def table226 : Point → Point := put table225 4 5
def table227 : Point → Point := put table226 5 7
def table228 : Point → Point := put table227 7 4
def table229 : Point → Point := put table228 8 3
def table230 : Point → Point := put table229 9 1
def table231 : Point → Point := put table230 11 2
def table232 : Point → Point := put table186 2 11
def table233 : Point → Point := put table232 3 3
def table234 : Point → Point := put table233 4 7
def table235 : Point → Point := put table234 5 5
def table236 : Point → Point := put table235 7 4
def table237 : Point → Point := put table236 8 1
def table238 : Point → Point := put table237 9 9
def table239 : Point → Point := put table238 11 2
def table240 : Point → Point := put table232 3 9
def table241 : Point → Point := put table240 4 7
def table242 : Point → Point := put table241 5 5
def table243 : Point → Point := put table242 7 4
def table244 : Point → Point := put table243 8 1
def table245 : Point → Point := put table244 9 3
def table246 : Point → Point := put table245 11 2
def table247 : Point → Point := put table2 1 9
def table248 : Point → Point := put table247 2 1
def table249 : Point → Point := put table248 3 2
def table250 : Point → Point := put table249 4 7
def table251 : Point → Point := put table250 5 4
def table252 : Point → Point := put table251 7 5
def table253 : Point → Point := put table252 8 11
def table254 : Point → Point := put table253 9 8
def table255 : Point → Point := put table254 11 3
def table256 : Point → Point := put table248 3 8
def table257 : Point → Point := put table256 4 7
def table258 : Point → Point := put table257 5 4
def table259 : Point → Point := put table258 7 5
def table260 : Point → Point := put table259 8 11
def table261 : Point → Point := put table260 9 2
def table262 : Point → Point := put table261 11 3
def table263 : Point → Point := put table247 2 2
def table264 : Point → Point := put table263 3 1
def table265 : Point → Point := put table264 4 4
def table266 : Point → Point := put table265 5 7
def table267 : Point → Point := put table266 7 5
def table268 : Point → Point := put table267 8 8
def table269 : Point → Point := put table268 9 11
def table270 : Point → Point := put table269 11 3
def table271 : Point → Point := put table263 3 11
def table272 : Point → Point := put table271 4 4
def table273 : Point → Point := put table272 5 7
def table274 : Point → Point := put table273 7 5
def table275 : Point → Point := put table274 8 8
def table276 : Point → Point := put table275 9 1
def table277 : Point → Point := put table276 11 3
def table278 : Point → Point := put table247 2 8
def table279 : Point → Point := put table278 3 1
def table280 : Point → Point := put table279 4 4
def table281 : Point → Point := put table280 5 7
def table282 : Point → Point := put table281 7 5
def table283 : Point → Point := put table282 8 2
def table284 : Point → Point := put table283 9 11
def table285 : Point → Point := put table284 11 3
def table286 : Point → Point := put table278 3 11
def table287 : Point → Point := put table286 4 4
def table288 : Point → Point := put table287 5 7
def table289 : Point → Point := put table288 7 5
def table290 : Point → Point := put table289 8 2
def table291 : Point → Point := put table290 9 1
def table292 : Point → Point := put table291 11 3
def table293 : Point → Point := put table247 2 11
def table294 : Point → Point := put table293 3 2
def table295 : Point → Point := put table294 4 7
def table296 : Point → Point := put table295 5 4
def table297 : Point → Point := put table296 7 5
def table298 : Point → Point := put table297 8 1
def table299 : Point → Point := put table298 9 8
def table300 : Point → Point := put table299 11 3
def table301 : Point → Point := put table293 3 8
def table302 : Point → Point := put table301 4 7
def table303 : Point → Point := put table302 5 4
def table304 : Point → Point := put table303 7 5
def table305 : Point → Point := put table304 8 1
def table306 : Point → Point := put table305 9 2
def table307 : Point → Point := put table306 11 3
def table308 : Point → Point := put table2 1 11
def table309 : Point → Point := put table308 2 2
def table310 : Point → Point := put table309 3 3
def table311 : Point → Point := put table310 4 4
def table312 : Point → Point := put table311 5 5
def table313 : Point → Point := put table312 7 7
def table314 : Point → Point := put table313 8 8
def table315 : Point → Point := put table314 9 9
def table316 : Point → Point := put table315 11 1
def table317 : Point → Point := put table309 3 9
def table318 : Point → Point := put table317 4 4
def table319 : Point → Point := put table318 5 5
def table320 : Point → Point := put table319 7 7
def table321 : Point → Point := put table320 8 8
def table322 : Point → Point := put table321 9 3
def table323 : Point → Point := put table322 11 1
def table324 : Point → Point := put table308 2 3
def table325 : Point → Point := put table324 3 2
def table326 : Point → Point := put table325 4 5
def table327 : Point → Point := put table326 5 4
def table328 : Point → Point := put table327 7 7
def table329 : Point → Point := put table328 8 9
def table330 : Point → Point := put table329 9 8
def table331 : Point → Point := put table330 11 1
def table332 : Point → Point := put table324 3 8
def table333 : Point → Point := put table332 4 5
def table334 : Point → Point := put table333 5 4
def table335 : Point → Point := put table334 7 7
def table336 : Point → Point := put table335 8 9
def table337 : Point → Point := put table336 9 2
def table338 : Point → Point := put table337 11 1
def table339 : Point → Point := put table308 2 8
def table340 : Point → Point := put table339 3 3
def table341 : Point → Point := put table340 4 4
def table342 : Point → Point := put table341 5 5
def table343 : Point → Point := put table342 7 7
def table344 : Point → Point := put table343 8 2
def table345 : Point → Point := put table344 9 9
def table346 : Point → Point := put table345 11 1
def table347 : Point → Point := put table339 3 9
def table348 : Point → Point := put table347 4 4
def table349 : Point → Point := put table348 5 5
def table350 : Point → Point := put table349 7 7
def table351 : Point → Point := put table350 8 2
def table352 : Point → Point := put table351 9 3
def table353 : Point → Point := put table352 11 1
def table354 : Point → Point := put table308 2 9
def table355 : Point → Point := put table354 3 2
def table356 : Point → Point := put table355 4 5
def table357 : Point → Point := put table356 5 4
def table358 : Point → Point := put table357 7 7
def table359 : Point → Point := put table358 8 3
def table360 : Point → Point := put table359 9 8
def table361 : Point → Point := put table360 11 1
def table362 : Point → Point := put table354 3 8
def table363 : Point → Point := put table362 4 5
def table364 : Point → Point := put table363 5 4
def table365 : Point → Point := put table364 7 7
def table366 : Point → Point := put table365 8 3
def table367 : Point → Point := put table366 9 2
def table368 : Point → Point := put table367 11 1
def table369 : Point → Point := put table0 0 10
def table370 : Point → Point := put table369 10 0
def table371 : Point → Point := put table370 1 1
def table372 : Point → Point := put table371 2 2
def table373 : Point → Point := put table372 3 3
def table374 : Point → Point := put table373 4 4
def table375 : Point → Point := put table374 5 5
def table376 : Point → Point := put table375 7 7
def table377 : Point → Point := put table376 8 8
def table378 : Point → Point := put table377 9 9
def table379 : Point → Point := put table378 11 11
def table380 : Point → Point := put table372 3 9
def table381 : Point → Point := put table380 4 4
def table382 : Point → Point := put table381 5 5
def table383 : Point → Point := put table382 7 7
def table384 : Point → Point := put table383 8 8
def table385 : Point → Point := put table384 9 3
def table386 : Point → Point := put table385 11 11
def table387 : Point → Point := put table371 2 3
def table388 : Point → Point := put table387 3 2
def table389 : Point → Point := put table388 4 5
def table390 : Point → Point := put table389 5 4
def table391 : Point → Point := put table390 7 7
def table392 : Point → Point := put table391 8 9
def table393 : Point → Point := put table392 9 8
def table394 : Point → Point := put table393 11 11
def table395 : Point → Point := put table387 3 8
def table396 : Point → Point := put table395 4 5
def table397 : Point → Point := put table396 5 4
def table398 : Point → Point := put table397 7 7
def table399 : Point → Point := put table398 8 9
def table400 : Point → Point := put table399 9 2
def table401 : Point → Point := put table400 11 11
def table402 : Point → Point := put table371 2 8
def table403 : Point → Point := put table402 3 3
def table404 : Point → Point := put table403 4 4
def table405 : Point → Point := put table404 5 5
def table406 : Point → Point := put table405 7 7
def table407 : Point → Point := put table406 8 2
def table408 : Point → Point := put table407 9 9
def table409 : Point → Point := put table408 11 11
def table410 : Point → Point := put table402 3 9
def table411 : Point → Point := put table410 4 4
def table412 : Point → Point := put table411 5 5
def table413 : Point → Point := put table412 7 7
def table414 : Point → Point := put table413 8 2
def table415 : Point → Point := put table414 9 3
def table416 : Point → Point := put table415 11 11
def table417 : Point → Point := put table371 2 9
def table418 : Point → Point := put table417 3 2
def table419 : Point → Point := put table418 4 5
def table420 : Point → Point := put table419 5 4
def table421 : Point → Point := put table420 7 7
def table422 : Point → Point := put table421 8 3
def table423 : Point → Point := put table422 9 8
def table424 : Point → Point := put table423 11 11
def table425 : Point → Point := put table417 3 8
def table426 : Point → Point := put table425 4 5
def table427 : Point → Point := put table426 5 4
def table428 : Point → Point := put table427 7 7
def table429 : Point → Point := put table428 8 3
def table430 : Point → Point := put table429 9 2
def table431 : Point → Point := put table430 11 11
def table432 : Point → Point := put table370 1 2
def table433 : Point → Point := put table432 2 1
def table434 : Point → Point := put table433 3 3
def table435 : Point → Point := put table434 4 7
def table436 : Point → Point := put table435 5 5
def table437 : Point → Point := put table436 7 4
def table438 : Point → Point := put table437 8 11
def table439 : Point → Point := put table438 9 9
def table440 : Point → Point := put table439 11 8
def table441 : Point → Point := put table433 3 9
def table442 : Point → Point := put table441 4 7
def table443 : Point → Point := put table442 5 5
def table444 : Point → Point := put table443 7 4
def table445 : Point → Point := put table444 8 11
def table446 : Point → Point := put table445 9 3
def table447 : Point → Point := put table446 11 8
def table448 : Point → Point := put table432 2 3
def table449 : Point → Point := put table448 3 1
def table450 : Point → Point := put table449 4 5
def table451 : Point → Point := put table450 5 7
def table452 : Point → Point := put table451 7 4
def table453 : Point → Point := put table452 8 9
def table454 : Point → Point := put table453 9 11
def table455 : Point → Point := put table454 11 8
def table456 : Point → Point := put table448 3 11
def table457 : Point → Point := put table456 4 5
def table458 : Point → Point := put table457 5 7
def table459 : Point → Point := put table458 7 4
def table460 : Point → Point := put table459 8 9
def table461 : Point → Point := put table460 9 1
def table462 : Point → Point := put table461 11 8
def table463 : Point → Point := put table432 2 9
def table464 : Point → Point := put table463 3 1
def table465 : Point → Point := put table464 4 5
def table466 : Point → Point := put table465 5 7
def table467 : Point → Point := put table466 7 4
def table468 : Point → Point := put table467 8 3
def table469 : Point → Point := put table468 9 11
def table470 : Point → Point := put table469 11 8
def table471 : Point → Point := put table463 3 11
def table472 : Point → Point := put table471 4 5
def table473 : Point → Point := put table472 5 7
def table474 : Point → Point := put table473 7 4
def table475 : Point → Point := put table474 8 3
def table476 : Point → Point := put table475 9 1
def table477 : Point → Point := put table476 11 8
def table478 : Point → Point := put table432 2 11
def table479 : Point → Point := put table478 3 3
def table480 : Point → Point := put table479 4 7
def table481 : Point → Point := put table480 5 5
def table482 : Point → Point := put table481 7 4
def table483 : Point → Point := put table482 8 1
def table484 : Point → Point := put table483 9 9
def table485 : Point → Point := put table484 11 8
def table486 : Point → Point := put table478 3 9
def table487 : Point → Point := put table486 4 7
def table488 : Point → Point := put table487 5 5
def table489 : Point → Point := put table488 7 4
def table490 : Point → Point := put table489 8 1
def table491 : Point → Point := put table490 9 3
def table492 : Point → Point := put table491 11 8
def table493 : Point → Point := put table370 1 3
def table494 : Point → Point := put table493 2 1
def table495 : Point → Point := put table494 3 2
def table496 : Point → Point := put table495 4 7
def table497 : Point → Point := put table496 5 4
def table498 : Point → Point := put table497 7 5
def table499 : Point → Point := put table498 8 11
def table500 : Point → Point := put table499 9 8
def table501 : Point → Point := put table500 11 9
def table502 : Point → Point := put table494 3 8
def table503 : Point → Point := put table502 4 7
def table504 : Point → Point := put table503 5 4
def table505 : Point → Point := put table504 7 5
def table506 : Point → Point := put table505 8 11
def table507 : Point → Point := put table506 9 2
def table508 : Point → Point := put table507 11 9
def table509 : Point → Point := put table493 2 2
def table510 : Point → Point := put table509 3 1
def table511 : Point → Point := put table510 4 4
def table512 : Point → Point := put table511 5 7
def table513 : Point → Point := put table512 7 5
def table514 : Point → Point := put table513 8 8
def table515 : Point → Point := put table514 9 11
def table516 : Point → Point := put table515 11 9
def table517 : Point → Point := put table509 3 11
def table518 : Point → Point := put table517 4 4
def table519 : Point → Point := put table518 5 7
def table520 : Point → Point := put table519 7 5
def table521 : Point → Point := put table520 8 8
def table522 : Point → Point := put table521 9 1
def table523 : Point → Point := put table522 11 9
def table524 : Point → Point := put table493 2 8
def table525 : Point → Point := put table524 3 1
def table526 : Point → Point := put table525 4 4
def table527 : Point → Point := put table526 5 7
def table528 : Point → Point := put table527 7 5
def table529 : Point → Point := put table528 8 2
def table530 : Point → Point := put table529 9 11
def table531 : Point → Point := put table530 11 9
def table532 : Point → Point := put table524 3 11
def table533 : Point → Point := put table532 4 4
def table534 : Point → Point := put table533 5 7
def table535 : Point → Point := put table534 7 5
def table536 : Point → Point := put table535 8 2
def table537 : Point → Point := put table536 9 1
def table538 : Point → Point := put table537 11 9
def table539 : Point → Point := put table493 2 11
def table540 : Point → Point := put table539 3 2
def table541 : Point → Point := put table540 4 7
def table542 : Point → Point := put table541 5 4
def table543 : Point → Point := put table542 7 5
def table544 : Point → Point := put table543 8 1
def table545 : Point → Point := put table544 9 8
def table546 : Point → Point := put table545 11 9
def table547 : Point → Point := put table539 3 8
def table548 : Point → Point := put table547 4 7
def table549 : Point → Point := put table548 5 4
def table550 : Point → Point := put table549 7 5
def table551 : Point → Point := put table550 8 1
def table552 : Point → Point := put table551 9 2
def table553 : Point → Point := put table552 11 9
def table554 : Point → Point := put table370 1 8
def table555 : Point → Point := put table554 2 1
def table556 : Point → Point := put table555 3 3
def table557 : Point → Point := put table556 4 7
def table558 : Point → Point := put table557 5 5
def table559 : Point → Point := put table558 7 4
def table560 : Point → Point := put table559 8 11
def table561 : Point → Point := put table560 9 9
def table562 : Point → Point := put table561 11 2
def table563 : Point → Point := put table555 3 9
def table564 : Point → Point := put table563 4 7
def table565 : Point → Point := put table564 5 5
def table566 : Point → Point := put table565 7 4
def table567 : Point → Point := put table566 8 11
def table568 : Point → Point := put table567 9 3
def table569 : Point → Point := put table568 11 2
def table570 : Point → Point := put table554 2 3
def table571 : Point → Point := put table570 3 1
def table572 : Point → Point := put table571 4 5
def table573 : Point → Point := put table572 5 7
def table574 : Point → Point := put table573 7 4
def table575 : Point → Point := put table574 8 9
def table576 : Point → Point := put table575 9 11
def table577 : Point → Point := put table576 11 2
def table578 : Point → Point := put table570 3 11
def table579 : Point → Point := put table578 4 5
def table580 : Point → Point := put table579 5 7
def table581 : Point → Point := put table580 7 4
def table582 : Point → Point := put table581 8 9
def table583 : Point → Point := put table582 9 1
def table584 : Point → Point := put table583 11 2
def table585 : Point → Point := put table554 2 9
def table586 : Point → Point := put table585 3 1
def table587 : Point → Point := put table586 4 5
def table588 : Point → Point := put table587 5 7
def table589 : Point → Point := put table588 7 4
def table590 : Point → Point := put table589 8 3
def table591 : Point → Point := put table590 9 11
def table592 : Point → Point := put table591 11 2
def table593 : Point → Point := put table585 3 11
def table594 : Point → Point := put table593 4 5
def table595 : Point → Point := put table594 5 7
def table596 : Point → Point := put table595 7 4
def table597 : Point → Point := put table596 8 3
def table598 : Point → Point := put table597 9 1
def table599 : Point → Point := put table598 11 2
def table600 : Point → Point := put table554 2 11
def table601 : Point → Point := put table600 3 3
def table602 : Point → Point := put table601 4 7
def table603 : Point → Point := put table602 5 5
def table604 : Point → Point := put table603 7 4
def table605 : Point → Point := put table604 8 1
def table606 : Point → Point := put table605 9 9
def table607 : Point → Point := put table606 11 2
def table608 : Point → Point := put table600 3 9
def table609 : Point → Point := put table608 4 7
def table610 : Point → Point := put table609 5 5
def table611 : Point → Point := put table610 7 4
def table612 : Point → Point := put table611 8 1
def table613 : Point → Point := put table612 9 3
def table614 : Point → Point := put table613 11 2
def table615 : Point → Point := put table370 1 9
def table616 : Point → Point := put table615 2 1
def table617 : Point → Point := put table616 3 2
def table618 : Point → Point := put table617 4 7
def table619 : Point → Point := put table618 5 4
def table620 : Point → Point := put table619 7 5
def table621 : Point → Point := put table620 8 11
def table622 : Point → Point := put table621 9 8
def table623 : Point → Point := put table622 11 3
def table624 : Point → Point := put table616 3 8
def table625 : Point → Point := put table624 4 7
def table626 : Point → Point := put table625 5 4
def table627 : Point → Point := put table626 7 5
def table628 : Point → Point := put table627 8 11
def table629 : Point → Point := put table628 9 2
def table630 : Point → Point := put table629 11 3
def table631 : Point → Point := put table615 2 2
def table632 : Point → Point := put table631 3 1
def table633 : Point → Point := put table632 4 4
def table634 : Point → Point := put table633 5 7
def table635 : Point → Point := put table634 7 5
def table636 : Point → Point := put table635 8 8
def table637 : Point → Point := put table636 9 11
def table638 : Point → Point := put table637 11 3
def table639 : Point → Point := put table631 3 11
def table640 : Point → Point := put table639 4 4
def table641 : Point → Point := put table640 5 7
def table642 : Point → Point := put table641 7 5
def table643 : Point → Point := put table642 8 8
def table644 : Point → Point := put table643 9 1
def table645 : Point → Point := put table644 11 3
def table646 : Point → Point := put table615 2 8
def table647 : Point → Point := put table646 3 1
def table648 : Point → Point := put table647 4 4
def table649 : Point → Point := put table648 5 7
def table650 : Point → Point := put table649 7 5
def table651 : Point → Point := put table650 8 2
def table652 : Point → Point := put table651 9 11
def table653 : Point → Point := put table652 11 3
def table654 : Point → Point := put table646 3 11
def table655 : Point → Point := put table654 4 4
def table656 : Point → Point := put table655 5 7
def table657 : Point → Point := put table656 7 5
def table658 : Point → Point := put table657 8 2
def table659 : Point → Point := put table658 9 1
def table660 : Point → Point := put table659 11 3
def table661 : Point → Point := put table615 2 11
def table662 : Point → Point := put table661 3 2
def table663 : Point → Point := put table662 4 7
def table664 : Point → Point := put table663 5 4
def table665 : Point → Point := put table664 7 5
def table666 : Point → Point := put table665 8 1
def table667 : Point → Point := put table666 9 8
def table668 : Point → Point := put table667 11 3
def table669 : Point → Point := put table661 3 8
def table670 : Point → Point := put table669 4 7
def table671 : Point → Point := put table670 5 4
def table672 : Point → Point := put table671 7 5
def table673 : Point → Point := put table672 8 1
def table674 : Point → Point := put table673 9 2
def table675 : Point → Point := put table674 11 3
def table676 : Point → Point := put table370 1 11
def table677 : Point → Point := put table676 2 2
def table678 : Point → Point := put table677 3 3
def table679 : Point → Point := put table678 4 4
def table680 : Point → Point := put table679 5 5
def table681 : Point → Point := put table680 7 7
def table682 : Point → Point := put table681 8 8
def table683 : Point → Point := put table682 9 9
def table684 : Point → Point := put table683 11 1
def table685 : Point → Point := put table677 3 9
def table686 : Point → Point := put table685 4 4
def table687 : Point → Point := put table686 5 5
def table688 : Point → Point := put table687 7 7
def table689 : Point → Point := put table688 8 8
def table690 : Point → Point := put table689 9 3
def table691 : Point → Point := put table690 11 1
def table692 : Point → Point := put table676 2 3
def table693 : Point → Point := put table692 3 2
def table694 : Point → Point := put table693 4 5
def table695 : Point → Point := put table694 5 4
def table696 : Point → Point := put table695 7 7
def table697 : Point → Point := put table696 8 9
def table698 : Point → Point := put table697 9 8
def table699 : Point → Point := put table698 11 1
def table700 : Point → Point := put table692 3 8
def table701 : Point → Point := put table700 4 5
def table702 : Point → Point := put table701 5 4
def table703 : Point → Point := put table702 7 7
def table704 : Point → Point := put table703 8 9
def table705 : Point → Point := put table704 9 2
def table706 : Point → Point := put table705 11 1
def table707 : Point → Point := put table676 2 8
def table708 : Point → Point := put table707 3 3
def table709 : Point → Point := put table708 4 4
def table710 : Point → Point := put table709 5 5
def table711 : Point → Point := put table710 7 7
def table712 : Point → Point := put table711 8 2
def table713 : Point → Point := put table712 9 9
def table714 : Point → Point := put table713 11 1
def table715 : Point → Point := put table707 3 9
def table716 : Point → Point := put table715 4 4
def table717 : Point → Point := put table716 5 5
def table718 : Point → Point := put table717 7 7
def table719 : Point → Point := put table718 8 2
def table720 : Point → Point := put table719 9 3
def table721 : Point → Point := put table720 11 1
def table722 : Point → Point := put table676 2 9
def table723 : Point → Point := put table722 3 2
def table724 : Point → Point := put table723 4 5
def table725 : Point → Point := put table724 5 4
def table726 : Point → Point := put table725 7 7
def table727 : Point → Point := put table726 8 3
def table728 : Point → Point := put table727 9 8
def table729 : Point → Point := put table728 11 1
def table730 : Point → Point := put table722 3 8
def table731 : Point → Point := put table730 4 5
def table732 : Point → Point := put table731 5 4
def table733 : Point → Point := put table732 7 7
def table734 : Point → Point := put table733 8 3
def table735 : Point → Point := put table734 9 2
def table736 : Point → Point := put table735 11 1
end C13.Enumeration.Template6
