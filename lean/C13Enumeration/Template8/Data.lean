import C13Enumeration.PartialStar
import Mathlib.Data.Fin.VecNotation
import C13Covering.SourceLiterals
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def values : Array Nat := #[4,2,1,1,3,1,1,1,0,2,2,2,0,2,4,1,1,1,3,1,1,0,2,2,2,0,1,1,3,1,1,1,3,1,0,1,1,1,0,1,1,1,3,1,1,1,3,0,1,1,1,0,3,1,1,1,3,1,1,1,0,1,1,1,0,1,3,1,1,1,3,1,1,0,1,1,1,0,1,1,3,1,1,1,3,1,0,1,1,1,0,1,1,1,3,1,1,1,3,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,1,1,1,1,1,1,0,3,1,1,0,2,2,1,1,1,1,1,1,0,1,3,1,0,2,2,1,1,1,1,1,1,0,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link09 8) a b := by decide +kernel

def maps : List (Point → Point) := [
  ![0,1,2,3,4,5,6,7,12,9,10,11,8],
  ![0,1,2,7,4,5,6,3,12,9,10,11,8],
  ![0,1,6,3,4,5,2,7,12,9,10,11,8],
  ![0,1,6,7,4,5,2,3,12,9,10,11,8],
  ![0,1,3,2,4,5,7,6,12,9,11,10,8],
  ![0,1,3,6,4,5,7,2,12,9,11,10,8],
  ![0,1,7,2,4,5,3,6,12,9,11,10,8],
  ![0,1,7,6,4,5,3,2,12,9,11,10,8],
  ![1,0,3,2,5,4,7,6,12,9,10,11,8],
  ![1,0,3,6,5,4,7,2,12,9,10,11,8],
  ![1,0,7,2,5,4,3,6,12,9,10,11,8],
  ![1,0,7,6,5,4,3,2,12,9,10,11,8],
  ![1,0,2,3,5,4,6,7,12,9,11,10,8],
  ![1,0,2,7,5,4,6,3,12,9,11,10,8],
  ![1,0,6,3,5,4,2,7,12,9,11,10,8],
  ![1,0,6,7,5,4,2,3,12,9,11,10,8]
]
theorem maps_count : maps.length = 16 := by rfl
def step := starStep (link link09 8) (link link09 8) matrix matrix
def finish := mapFinish link09 hole 8
def table0 : Point → Point := anchorTable hole hole 8
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 1 1
def table3 : Point → Point := put table2 2 2
def table4 : Point → Point := put table3 3 3
def table5 : Point → Point := put table4 4 4
def table6 : Point → Point := put table5 5 5
def table7 : Point → Point := put table6 6 6
def table8 : Point → Point := put table7 7 7
def table9 : Point → Point := put table8 9 9
def table10 : Point → Point := put table9 10 10
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table3 3 7
def table13 : Point → Point := put table12 4 4
def table14 : Point → Point := put table13 5 5
def table15 : Point → Point := put table14 6 6
def table16 : Point → Point := put table15 7 3
def table17 : Point → Point := put table16 9 9
def table18 : Point → Point := put table17 10 10
def table19 : Point → Point := put table18 11 11
def table20 : Point → Point := put table2 2 3
def table21 : Point → Point := put table20 3 2
def table22 : Point → Point := put table21 4 4
def table23 : Point → Point := put table22 5 5
def table24 : Point → Point := put table23 6 7
def table25 : Point → Point := put table24 7 6
def table26 : Point → Point := put table25 9 9
def table27 : Point → Point := put table26 10 11
def table28 : Point → Point := put table27 11 10
def table29 : Point → Point := put table20 3 6
def table30 : Point → Point := put table29 4 4
def table31 : Point → Point := put table30 5 5
def table32 : Point → Point := put table31 6 7
def table33 : Point → Point := put table32 7 2
def table34 : Point → Point := put table33 9 9
def table35 : Point → Point := put table34 10 11
def table36 : Point → Point := put table35 11 10
def table37 : Point → Point := put table2 2 6
def table38 : Point → Point := put table37 3 3
def table39 : Point → Point := put table38 4 4
def table40 : Point → Point := put table39 5 5
def table41 : Point → Point := put table40 6 2
def table42 : Point → Point := put table41 7 7
def table43 : Point → Point := put table42 9 9
def table44 : Point → Point := put table43 10 10
def table45 : Point → Point := put table44 11 11
def table46 : Point → Point := put table37 3 7
def table47 : Point → Point := put table46 4 4
def table48 : Point → Point := put table47 5 5
def table49 : Point → Point := put table48 6 2
def table50 : Point → Point := put table49 7 3
def table51 : Point → Point := put table50 9 9
def table52 : Point → Point := put table51 10 10
def table53 : Point → Point := put table52 11 11
def table54 : Point → Point := put table2 2 7
def table55 : Point → Point := put table54 3 2
def table56 : Point → Point := put table55 4 4
def table57 : Point → Point := put table56 5 5
def table58 : Point → Point := put table57 6 3
def table59 : Point → Point := put table58 7 6
def table60 : Point → Point := put table59 9 9
def table61 : Point → Point := put table60 10 11
def table62 : Point → Point := put table61 11 10
def table63 : Point → Point := put table54 3 6
def table64 : Point → Point := put table63 4 4
def table65 : Point → Point := put table64 5 5
def table66 : Point → Point := put table65 6 3
def table67 : Point → Point := put table66 7 2
def table68 : Point → Point := put table67 9 9
def table69 : Point → Point := put table68 10 11
def table70 : Point → Point := put table69 11 10
def table71 : Point → Point := put table0 0 1
def table72 : Point → Point := put table71 1 0
def table73 : Point → Point := put table72 2 2
def table74 : Point → Point := put table73 3 3
def table75 : Point → Point := put table74 4 5
def table76 : Point → Point := put table75 5 4
def table77 : Point → Point := put table76 6 6
def table78 : Point → Point := put table77 7 7
def table79 : Point → Point := put table78 9 9
def table80 : Point → Point := put table79 10 11
def table81 : Point → Point := put table80 11 10
def table82 : Point → Point := put table73 3 7
def table83 : Point → Point := put table82 4 5
def table84 : Point → Point := put table83 5 4
def table85 : Point → Point := put table84 6 6
def table86 : Point → Point := put table85 7 3
def table87 : Point → Point := put table86 9 9
def table88 : Point → Point := put table87 10 11
def table89 : Point → Point := put table88 11 10
def table90 : Point → Point := put table72 2 3
def table91 : Point → Point := put table90 3 2
def table92 : Point → Point := put table91 4 5
def table93 : Point → Point := put table92 5 4
def table94 : Point → Point := put table93 6 7
def table95 : Point → Point := put table94 7 6
def table96 : Point → Point := put table95 9 9
def table97 : Point → Point := put table96 10 10
def table98 : Point → Point := put table97 11 11
def table99 : Point → Point := put table90 3 6
def table100 : Point → Point := put table99 4 5
def table101 : Point → Point := put table100 5 4
def table102 : Point → Point := put table101 6 7
def table103 : Point → Point := put table102 7 2
def table104 : Point → Point := put table103 9 9
def table105 : Point → Point := put table104 10 10
def table106 : Point → Point := put table105 11 11
def table107 : Point → Point := put table72 2 6
def table108 : Point → Point := put table107 3 3
def table109 : Point → Point := put table108 4 5
def table110 : Point → Point := put table109 5 4
def table111 : Point → Point := put table110 6 2
def table112 : Point → Point := put table111 7 7
def table113 : Point → Point := put table112 9 9
def table114 : Point → Point := put table113 10 11
def table115 : Point → Point := put table114 11 10
def table116 : Point → Point := put table107 3 7
def table117 : Point → Point := put table116 4 5
def table118 : Point → Point := put table117 5 4
def table119 : Point → Point := put table118 6 2
def table120 : Point → Point := put table119 7 3
def table121 : Point → Point := put table120 9 9
def table122 : Point → Point := put table121 10 11
def table123 : Point → Point := put table122 11 10
def table124 : Point → Point := put table72 2 7
def table125 : Point → Point := put table124 3 2
def table126 : Point → Point := put table125 4 5
def table127 : Point → Point := put table126 5 4
def table128 : Point → Point := put table127 6 3
def table129 : Point → Point := put table128 7 6
def table130 : Point → Point := put table129 9 9
def table131 : Point → Point := put table130 10 10
def table132 : Point → Point := put table131 11 11
def table133 : Point → Point := put table124 3 6
def table134 : Point → Point := put table133 4 5
def table135 : Point → Point := put table134 5 4
def table136 : Point → Point := put table135 6 3
def table137 : Point → Point := put table136 7 2
def table138 : Point → Point := put table137 9 9
def table139 : Point → Point := put table138 10 10
def table140 : Point → Point := put table139 11 11
end C13.Enumeration.Template8
