module Model2 where 

import List
import Model

snowWhite' :: Entity
snowWhite' = T

girl', boy', princess', dwarf', giant', 
  child', person', man', woman', thing' :: OnePlacePred
girl'     = list2OnePlacePred [S,T,A,D,G]
boy'      = list2OnePlacePred [M,Y]
princess' = list2OnePlacePred [E,S]
dwarf'    = list2OnePlacePred [B,R]
giant'    = list2OnePlacePred []
wizard'   = list2OnePlacePred [W,V]
child'    = \ x -> (girl' x  || boy' x)
person'   = \ x -> (child' x || princess' x || dwarf' x 
                             || giant' x    || wizard' x) 
man'      = \ x -> (dwarf' x || giant' x    || wizard' x) 
woman'    = \ x -> princess' x 
thing'    = \ x -> not (person' x || x == Unspec)

laugh', cheer', shudder' :: OnePlacePred
laugh'   = list2OnePlacePred [A,G,E,T]
cheer'   = list2OnePlacePred [M,D]
shudder' = list2OnePlacePred []

