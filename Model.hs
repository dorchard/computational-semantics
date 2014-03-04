module Model where 

import Data.List

data Entity = A | B | C | D | E | F | G
            | H | I | J | K | L | M | N 
            | O | P | Q | R | S | T | U 
            | V | W | X | Y | Z | Unspec
     deriving (Eq,Show,Bounded,Enum)

entities :: [Entity]
entities =  [minBound..maxBound] 

snowWhite, alice, dorothy, goldilocks, littleMook, atreyu
                                                :: Entity

snowWhite  = S
alice      = A
dorothy    = D
goldilocks = G 
littleMook = M
atreyu     = Y

type OnePlacePred   = Entity -> Bool
type TwoPlacePred   = Entity -> Entity -> Bool
type ThreePlacePred = Entity -> Entity -> Entity -> Bool

list2OnePlacePred :: [Entity] -> OnePlacePred
list2OnePlacePred xs = \ x -> elem x xs

girl, boy, princess, dwarf, giant, wizard, sword, dagger
                                         :: OnePlacePred

girl     = list2OnePlacePred [S,A,D,G]
boy      = list2OnePlacePred [M,Y]
princess = list2OnePlacePred [E]
dwarf    = list2OnePlacePred [B,R]
giant    = list2OnePlacePred [T]
wizard   = list2OnePlacePred [W,V]
sword    = list2OnePlacePred [F]
dagger   = list2OnePlacePred [X]

child, person, man, woman, male, female, thing :: OnePlacePred

child  = \ x -> (girl x  || boy x)
person = \ x -> (child x || princess x || dwarf x 
                         || giant x    || wizard x) 
man    = \ x -> (dwarf x || giant x || wizard x) 
woman  = \ x -> princess x 
male   = \ x -> (man x || boy x) 
female = \ x -> (woman x || girl x)
thing  = \ x -> not (person x || x == Unspec)

laugh, cheer, shudder :: OnePlacePred

laugh   = list2OnePlacePred [A,G,E]
cheer   = list2OnePlacePred [M,D]
shudder = list2OnePlacePred [S]

love, admire, help, defeat :: TwoPlacePred

love   = curry (`elem` [(Y,E),(B,S),(R,S)])
admire = curry (`elem` [(x,G) | x <- entities, person x])
help   = curry (`elem` [(W,W),(V,V),(S,B),(D,M)])
defeat = curry (`elem` [(x,y) | x <- entities, 
                                y <- entities,
                                dwarf x && giant y]
                    ++ [(A,W),(A,V)])

curry3 :: ((a,b,c) -> d) -> a -> b -> c -> d
curry3 f x y z = f (x,y,z)

give :: ThreePlacePred
give = curry3 (`elem` [(T,S,X),(A,E,S)])

kill :: ThreePlacePred
kill = curry3 (`elem` [(Y,T,F),(Unspec,D,X),
                       (Unspec,M,Unspec)])

passivize :: TwoPlacePred -> OnePlacePred
passivize r = \ x -> r Unspec x

self ::  (a -> a -> b) -> a -> b
self p = \ x -> p x x 

