module EAI where 
import FSynF
import Model
import Model2
import TCOM

data World = W1 | W2 | W3 deriving (Eq,Show)

worlds :: [World]
worlds = [W1,W2,W3]

type IEntity = World -> Entity
type IBool   = World -> Bool

iSnowWhite :: IEntity
iSnowWhite W1 = snowWhite
iSnowWhite W2 = snowWhite'
iSnowWhite W3 = snowWhite'

iGirl, iPrincess, iPerson :: World -> Entity -> Bool
iGirl     W1 = girl
iGirl     W2 = girl'
iGirl     W3 = girl' 
iPrincess W1 = princess
iPrincess W2 = princess'
iPrincess W3 = girl'
iPerson   W1 = person
iPerson   W2 = person'
iPerson   W3 = person'

iLaugh, iShudder :: World -> Entity -> Bool
iLaugh W1 =  laugh 
iLaugh W2 =  laugh'  
iLaugh W3 =  laugh' 
iShudder W1 =  shudder 
iShudder W2 =  shudder' 
iShudder W3 =  shudder' 

iCatch :: World -> Entity -> Entity -> Bool
iCatch W1 = \ x y -> False
iCatch W2 = \ x y -> False
iCatch W3 = \ x y -> elem x [B,R,T] && girl' y

iSent :: Sent -> IBool
iSent (Sent np vp) = iNP np (iVP vp)

iNP :: NP -> (IEntity -> IBool) -> IBool

iNP SnowWhite = \ p -> p iSnowWhite

iNP Everyone  = \ p i -> all (\x -> p (\j -> x) i) 
      (filter (\y -> iPerson i y) entities)
iNP Someone  = \ p i -> any (\x -> p (\j -> x) i) 
      (filter (\y -> iPerson i y) entities)
iNP (NP1 det cn)  = iDET det (iCN cn) 
iNP (NP2 det rcn) = iDET det (iRCN rcn) 

iDET :: DET -> (IEntity -> IBool) 
            -> (IEntity -> IBool) -> IBool
iDET Some p q = \ i -> any (\x -> q (\j -> x) i) 
      (filter (\x -> p (\j -> x) i) entities)
iDET Every p q = \ i -> all (\x -> q (\j -> x) i) 
      (filter (\x -> p (\j -> x) i) entities)
iDET No p q = \ i -> not (any (\x -> q (\j -> x) i) 
      (filter (\x -> p (\j -> x) i) entities))

iVP :: VP -> IEntity -> IBool
iVP Laughed   = \ x i -> iLaugh i (x i) 
iVP Shuddered = \ x i -> iShudder i (x i) 

iVP (VP3 attitude to inf) = iAV attitude (iINF inf) 

iCN :: CN -> IEntity -> IBool 
iCN Girl = \ x i -> iGirl i (x i) 
iCN Princess = \ x i -> iPrincess i (x i) 

iRCN (RCN3 adj cn) = iADJ adj (iCN cn)

eval1 = iSent (Sent SnowWhite Laughed) W1
eval2 = iSent (Sent SnowWhite Laughed) W2
eval3 = iSent (Sent Someone Shuddered) W1
eval4 = iSent (Sent Someone Shuddered) W2
eval5 = iSent (Sent (NP1 Every Girl) Shuddered) W1
eval6 = iSent (Sent (NP1 Every Girl) Shuddered) W2
eval7 = iSent (Sent (NP1 Some Girl) Shuddered) W1
eval8 = iSent (Sent (NP1 Some Girl) Shuddered) W2

iADJ :: ADJ -> (IEntity -> IBool) -> IEntity -> IBool
iADJ Fake = \ p x i -> 
  not (p x i) && any (\ j -> p x j) worlds 

eval9 = iSent 
  (Sent (NP1 Some Princess) Shuddered) W1
eval10 = iSent 
  (Sent (NP2 Some (RCN3 Fake Princess)) Shuddered) W1
eval11 = iSent 
  (Sent (NP2 Some (RCN3 Fake Princess)) Shuddered) W2

iINF :: INF -> IEntity -> IBool
iINF Laugh   = \ x i -> iLaugh i (x i) 
iINF Shudder = \ x i -> iShudder i (x i)
iINF (INF tinf np) = \ s -> iNP np (\ o -> iTINF tinf s o)

iTINF :: TINF -> IEntity -> IEntity -> IBool 
iTINF Catch = \x y w -> iCatch w (x w) (y w)

iAttit :: AV -> IEntity -> IBool 
iAttit Wanted x = \i -> elem i [W2,W3]
iAttit Hoped  x = \i -> i == W3

iAV :: AV -> (IEntity -> IBool) -> (IEntity -> IBool)
iAV Wanted p = \ x i -> 
  and [ p x j | j <- worlds, iAttit Wanted x j ]
iAV Hoped  p = \ x i -> 
  and [ p x j | j <- worlds, iAttit Hoped  x j ]

eval12 = iSent (Sent SnowWhite 
  (VP3 Wanted To (INF Catch (NP1 Some Girl)))) W1
eval13 = iSent (Sent SnowWhite 
  (VP3 Wanted To (INF Catch (NP1 No Girl)))) W2

data Judgement = IsTrue Sent 
               | IsNec  Sent 
               | IsCont Sent deriving Show

iJudgement :: Judgement -> IBool
iJudgement (IsTrue s) = \ i -> iSent s i
iJudgement (IsNec s) = \ i -> 
  all (\j -> iSent s j) worlds
iJudgement (IsCont s) = \ i -> 
  iSent s i && not (all (\j -> iSent s j) worlds)

judgement1,judgement2,judgement3,judgement4 :: Bool
judgement1 = iJudgement 
  (IsTrue (Sent (NP1 Some Girl) Shuddered)) W1
judgement2 = iJudgement 
  (IsTrue (Sent (NP1 Some Girl) Shuddered)) W2
judgement3 = iJudgement 
  (IsNec  (Sent (NP1 Some Girl) Shuddered)) W1
judgement4 = iJudgement 
  (IsCont (Sent (NP1 Some Girl) Shuddered)) W1

iProp :: (World -> Entity -> Bool) -> IEntity -> IBool
iProp x = \ y i -> x i (y i) 

vpINT :: VP -> World -> Entity -> Bool
vpINT Laughed   = iLaugh
vpINT Shuddered = iShudder

intensVP :: VP -> IEntity -> IBool
intensVP = iProp . vpINT

eProp :: (IEntity -> IBool) -> World -> Entity -> Bool
eProp y = \ j x -> y (\k -> x) j

iPropToB :: (World -> ((Entity -> Bool) -> Bool)) 
                           -> (IEntity -> IBool) -> IBool
iPropToB x = \ y i -> x i (eProp y i) 

ePropToB :: ((IEntity -> IBool) -> IBool) -> 
      World -> (Entity -> Bool) -> Bool
ePropToB y = \ j x -> y (iProp (\k -> x)) j

iPropToPropToB :: 
  (World -> (Entity -> Bool) -> (Entity -> Bool) -> Bool)
         -> (IEntity -> IBool) -> (IEntity -> IBool) -> IBool
iPropToPropToB x = \ y1 y2 i -> 
   x i (eProp y1 i) (eProp y2 i) 

ePropToPropToB :: 
     ((IEntity -> IBool) -> (IEntity -> IBool) -> IBool) -> 
      World -> (Entity -> Bool) -> (Entity -> Bool) -> Bool
ePropToPropToB y = \ j x1 x2  -> 
   y (iProp (\k -> x1)) (iProp (\k -> x2)) j

detINT :: DET ->  World -> 
    (Entity -> Bool) -> (Entity -> Bool) -> Bool
detINT det = \ i -> intDET det

intensDET :: DET -> (IEntity -> IBool) 
                 -> (IEntity -> IBool) -> IBool
intensDET = iPropToPropToB . detINT

isSnoww :: IEntity -> Bool
isSnoww x = and [ x i == iSnowWhite i | i <- worlds ]

myY :: IEntity -> IBool
myY x | isSnoww x = \i -> i == W1
      | otherwise = \i -> False 

myY' :: IEntity  -> IBool
myY' = iProp (eProp myY)

