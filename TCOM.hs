module TCOM where 

import Data.List
import FSynF
import Model

allNum, noNum :: Int -> Int -> Bool
allNum = \ m n -> m == 0
noNum  = \ m n -> n == 0 

atleastNum, atmostNum :: Int -> Int -> Int -> Bool
atleastNum k = \ m n -> n >= k
atmostNum  k = \ m n -> n <= k

atleast2butnotall :: Int -> Int -> Bool
atleast2butnotall = \ m n -> m > 0 && n >= 2

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x,y,z) =  f x y z 

rel3 :: Entity -> Entity -> Entity -> Bool
rel3 D x y = love x y 
rel3 E x y = not (love x y)
rel3 _ _ _ = False 

intSent :: Sent -> Bool 
intSent (Sent np vp) = (intNP np) (intVP vp)

intNP :: NP -> (Entity -> Bool) -> Bool
intNP SnowWhite     = \ p -> p snowWhite 
intNP Alice         = \ p -> p alice
intNP Dorothy       = \ p -> p dorothy
intNP Goldilocks    = \ p -> p goldilocks
intNP LittleMook    = \ p -> p littleMook
intNP Atreyu        = \ p -> p atreyu
intNP (NP1 det cn)  = (intDET det) (intCN cn) 
intNP (NP2 det rcn) = (intDET det) (intRCN rcn) 

intVP :: VP -> Entity -> Bool 
intVP Laughed   = \ x -> laugh x
intVP Cheered   = \ x -> cheer x 
intVP Shuddered = \ x -> shudder x 

intVP (VP1 tv np) = 
  \ subj -> intNP np (\ obj -> intTV tv subj obj)
intVP (VP2 dv np1 np2) = 
  \ subj -> intNP np1 (\ iobj -> intNP np2 (\ dobj -> 
                         intDV dv subj iobj dobj))

intTV :: TV -> Entity -> Entity -> Bool
intTV Loved    = \ x y -> love x y
intTV Admired  = \ x y -> admire x y
intTV Helped   = \ x y -> help x y
intTV Defeated = \ x y -> defeat x y

intDV :: DV -> Entity -> Entity -> Entity -> Bool
intDV Gave = \ x y z -> give x y z

intCN :: CN -> Entity -> Bool
intCN Girl     = \ x -> girl x
intCN Boy      = \ x -> boy x
intCN Princess = \ x -> princess x
intCN Dwarf    = \ x -> dwarf x 
intCN Giant    = \ x -> giant x 
intCN Wizard   = \ x -> wizard x 
intCN Sword    = \ x -> sword x
intCN Dagger   = \ x -> dagger x

intDET :: DET -> 
         (Entity -> Bool) -> (Entity -> Bool) -> Bool

intDET Some p q = any q (filter p entities)

intDET Every p q = all q (filter p entities)

intDET The p q = singleton plist && q (head plist) 
          where 
              plist = filter p entities
              singleton [x] = True 
              singleton  _  = False

intDET No p q = not (intDET Some p q) 

intDET Most p q = length pqlist > length (plist \\ qlist)
    where 
         plist  = filter p entities 
         qlist  = filter q entities 
         pqlist = filter q plist

intRCN :: RCN -> Entity -> Bool
intRCN (RCN1 cn _ vp) = 
       \ e -> ((intCN cn e) && (intVP vp e))

intRCN (RCN2 cn _ np tv) = 
   \ e -> ((intCN cn e) && 
           (intNP np (\ subj -> (intTV tv subj e))))

