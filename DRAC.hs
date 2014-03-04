module DRAC where 

import Data.List
import Model
import P hiding (person)

type Context = [Entity]
type Prop    = [Context]
type Trans   = Context -> Prop
type Idx     = Int

lookupIdx :: Context -> Idx -> Entity 
lookupIdx []     i = error "undefined context element"
lookupIdx (x:xs) 0 = x
lookupIdx (x:xs) i = lookupIdx xs (i-1)

extend :: Context -> Entity -> Context 
extend = \ c e -> c ++ [e]

neg :: Trans -> Trans
neg = \ phi c -> if phi c == [] then [c] else []

conj :: Trans -> Trans -> Trans 
conj = \ phi psi c -> concat [ psi c' | c' <- (phi c) ]

impl :: Trans -> Trans -> Trans 
impl = \ phi psi ->  neg (phi `conj` (neg psi))

exists :: Trans
exists = \ c -> [ (extend c x) | x <- [minBound..maxBound]]

forAll :: Trans -> Trans
forAll = \ phi -> neg (exists `conj` (neg phi))

context :: Context
context = [A,D,G,M,Y]

anchor :: Entity -> Context -> Idx 
anchor = \ e c -> anchor' e c 0 where 
  anchor' e []     i = error (show e ++ " is not anchored")
  anchor' e (x:xs) i | e == x    = i 
                     | otherwise = anchor' e xs (i+1)

name2entity :: String -> Entity
name2entity "snowwhite"  = snowWhite
name2entity "alice"      = alice 
name2entity "dorothy"    = dorothy 
name2entity "goldilocks" = goldilocks 
name2entity "littlemook" = littleMook
name2entity "atreyu"     = atreyu 

name2pred :: String -> OnePlacePred
name2pred "laugh"     = laugh
name2pred "laughed"   = laugh
name2pred "cheer"     = cheer
name2pred "cheered"   = cheer
name2pred "shudder"   = shudder 
name2pred "shuddered" = shudder 

name2pred "thing"      = thing 
name2pred "things"     = thing
name2pred "person"     = person
name2pred "persons"    = person
name2pred "boy"        = boy 
name2pred "boys"       = boy 
name2pred "man"        = man
name2pred "men"        = man
name2pred "girl"       = girl
name2pred "girls"      = girl
name2pred "woman"      = woman
name2pred "women"      = woman
name2pred "princess"   = princess
name2pred "princesses" = princess

name2pred "dwarf"      = dwarf
name2pred "dwarfs"     = dwarf
name2pred "dwarves"    = dwarf
name2pred "giant"      = giant
name2pred "giants"     = giant
name2pred "wizard"     = wizard
name2pred "wizards"    = wizard
name2pred "sword"      = sword
name2pred "swords"     = sword
name2pred "dagger"     = dagger
name2pred "daggers"    = dagger

name2binpred :: String -> TwoPlacePred
name2binpred "love"     = love
name2binpred "loved"    = love
name2binpred "admire"   = admire
name2binpred "admired"  = admire
name2binpred "help"     = help 
name2binpred "helped"   = help 
name2binpred "defeat"   = defeat
name2binpred "defeated" = defeat

name2terpred :: String -> ThreePlacePred
name2terpred "give" = give 
name2terpred "gave" = give 

blowupPred :: OnePlacePred -> Idx -> Trans
blowupPred = \ pred i c -> if   pred (lookupIdx c i) 
                           then [c] 
                           else []

blowupPred2 :: TwoPlacePred -> Idx -> Idx -> Trans
blowupPred2 = \ pred i1 i2 c -> 
                      let l1 = lookupIdx c i1
                          l2 = lookupIdx c i2
                      in  if   pred l1 l2
                          then [c] 
                          else []

blowupPred3 :: ThreePlacePred -> Idx -> Idx -> Idx -> Trans
blowupPred3 = \ pred i1 i2 i3 c -> 
                         let l1 = lookupIdx c i1
                             l2 = lookupIdx c i2
                             l3 = lookupIdx c i3
                         in  if   pred l1 l2 l3 
                                  then [c] 
                                  else []

dintTXT :: ParseTree Cat Cat -> Trans
dintTXT (Branch (Cat "_" "TXT" _ _) [s,cnj,txt])  = 
                (dintTXT s) `conj` (dintTXT txt)
dintTXT (Branch (Cat "_" "S" _ _)   [cond,s1,s2]) = 
                (dintTXT s1) `impl` (dintTXT s2)
dintTXT (Branch (Cat "_" "S" _ _)   [np,vp])      = 
                (dintNP np) (dintVP vp) 

dintREL :: ParseTree Cat Cat -> Idx -> Trans
dintREL (Branch (Cat  _  "COMP" _ _) [rel,s]) = dintREL s
dintREL (Branch (Cat  _  "COMP" _ _) [s])     = dintREL s 
dintREL (Branch (Cat "_" "S"    _ _) 
          [Leaf (Cat "#" "NP"   _ _),vp])     = dintVP vp 
dintREL (Branch (Cat "_" "S"    _ _) [np,vp]) = 
                       \ i -> (dintNP np) (dintVPgap vp i)

dintVPgap :: ParseTree Cat Cat -> Idx -> Idx -> Trans
dintVPgap (Branch (Cat  _   "VP" _  _) 
            [Leaf (Cat name "VP" _ [_]),
             Leaf (Cat "#"  "NP" _  _ )]) =
          blowupPred2 (name2binpred name)

dintNP :: ParseTree Cat Cat -> (Idx -> Trans) -> Trans
dintNP (Leaf (Cat name "NP" _ _)) = 
  \ p c -> p (anchor (name2entity name) c) c 
dintNP (Branch (Cat _ "NP" _ _) [det,cn]) = 
  (dintDET det) (dintCN cn) 

dintCN :: ParseTree Cat Cat -> Idx -> Trans
dintCN (Leaf (Cat name "CN" _ _)) = 
   blowupPred (name2pred name) 
dintCN (Branch (Cat _ "CN" _ _) [cn,rel]) = \ i -> 
  (dintCN cn i) `conj` (dintREL rel i)

dintDET :: ParseTree Cat Cat -> 
           (Idx -> Trans) -> (Idx -> Trans) -> Trans
dintDET (Leaf (Cat "every" "DET" _ _)) =
  \ phi psi c -> let i = length c in
        neg (exists `conj` (phi i) `conj` (neg (psi i))) c
dintDET (Leaf (Cat "some" "DET" _ _)) = 
  \ phi psi c -> let i = length c in
        (exists `conj` (phi i) `conj` (psi i)) c
dintDET (Leaf (Cat "a" "DET" _ _)) = 
  \ phi psi c -> let i = length c in
        (exists `conj` (phi i) `conj` (psi i)) c
dintDET (Leaf (Cat "no" "DET" _ _)) = 
  \ phi psi c -> let i = length c in
        neg (exists `conj` (phi i) `conj` (psi i)) c 
dintDET (Leaf (Cat "the" "DET" _ _)) = 
  \ phi psi c -> let i = length c in 
               ((unique (phi i)) `conj` 
                 exists `conj` (phi i) `conj` (psi i)) c

singleton :: [a] -> Bool
singleton [x] = True 
singleton  _  = False 

unique :: Trans -> Trans
unique phi c | singleton xs = [c]
             | otherwise    = []
    where xs = [ x | x <- entities, 
                     phi (extend c x) /= [] ]

dintVP :: ParseTree Cat Cat -> Idx -> Trans
dintVP (Branch (Cat _    "VP" _ _ ) 
         [Leaf (Cat name "VP" _ [])])          = 
        blowupPred (name2pred name) 
dintVP (Branch (Cat _    "VP" _  _) 
         [Leaf (Cat name "VP" _ [_]),np])      = 
        \ subj -> dintNP np (\ obj -> 
        (blowupPred2 (name2binpred name)) subj obj)
dintVP (Branch (Cat _    "VP" _  _   ) 
         [Leaf (Cat name "VP" _ [_,_]),np,pp]) = 
        \ subj -> dintNP np (\ iobj -> dintPP pp (\ dobj -> 
        (blowupPred3 (name2terpred name)) subj iobj dobj))

dintVP (Branch (Cat _        "VP" _ _ ) 
         [Leaf (Cat "did"    "AUX" _ []),vp]) = dintVP vp
dintVP (Branch (Cat _        "VP" _ _) 
         [Leaf (Cat "didn't" "AUX" _ []),vp]) = 
                                    \ i -> neg (dintVP vp i)

dintPP :: ParseTree Cat Cat -> (Idx -> Trans) -> Trans
dintPP (Branch (Cat _ "PP" _ _) [prep,np]) = dintNP np 

evl :: ParseTree Cat Cat -> Prop
evl = \ txt -> dintTXT txt context 

prc :: String -> [Prop]
prc string = map evl (parses string)

lift :: Trans -> Context -> (Context -> Bool) -> Bool
lift phi c p = any p (phi c)

data Sent = Sent NP VP | If Sent Sent | Txt Sent Sent
          deriving (Eq,Show)
data NP   = SnowWhite  | Alice | Dorothy | Goldilocks 
          | LittleMook | Atreyu
          | PRO Idx    | He | She | It
          | NP1 DET CN | NP2 DET RCN 
          deriving (Eq,Show)
data DET  = Every | Some | No | The 
          deriving (Eq,Show)
data CN   = Girl   | Boy    | Princess | Dwarf | Giant 
          | Wizard | Sword  | Poison 
          deriving (Eq,Show) 
data RCN  = RCN1 CN That VP | RCN2 CN That NP TV
          deriving (Eq,Show)
data That = That deriving (Eq,Show)
data REFL = Self deriving (Eq,Show)

data VP   = Laughed | Cheered | Shuddered 
          | VP1 TV NP    | VP2 TV REFL 
          | VP3 DV NP NP | VP4 DV REFL NP 
          | VP5 AUX INF  
          deriving (Eq,Show) 
data TV   = Loved   | Admired | Helped | Defeated
          deriving (Eq,Show)
data DV   = Gave deriving (Eq,Show)

data AUX  = DidNot deriving (Eq,Show) 

data INF  = Laugh | Cheer  | Shudder 
          | INF1  TINF NP  | INF2  DINF NP NP 
          deriving (Eq,Show) 
data TINF = Love  | Admire | Help | Defeat 
          deriving (Eq,Show) 
data DINF = Give deriving (Eq,Show) 

intS :: Sent -> Trans
intS (Sent np vp) = (intNP np) (intVP vp)
intS (If   s1 s2) = (intS s1) `impl` (intS s2)
intS (Txt  s1 s2) = (intS s1) `conj` (intS s2)

intNP :: NP -> (Idx -> Trans) -> Trans
intNP SnowWhite  = \ p c -> p (anchor snowWhite  c) c
intNP Alice      = \ p c -> p (anchor alice      c) c
intNP Dorothy    = \ p c -> p (anchor dorothy    c) c
intNP Goldilocks = \ p c -> p (anchor goldilocks c) c
intNP LittleMook = \ p c -> p (anchor littleMook c) c
intNP (PRO i)    = \ p   -> p i 

intNP (NP1 det cn)  = (intDET det) (intCN cn) 
intNP (NP2 det rcn) = (intDET det) (intRCN rcn) 

intVP :: VP -> Idx -> Trans 
intVP Laughed          = blowupPred laugh
intVP Cheered          = blowupPred cheer
intVP Shuddered        = blowupPred shudder
intVP (VP1 tv np)      = \s -> intNP np (\o -> intTV tv s o) 
intVP (VP2 tv _)       = self (intTV tv)
intVP (VP3 dv np1 np2) = \s -> intNP np1 (\io -> intNP np2 
                        (\o -> intDV dv s io o))
intVP (VP4 dv _ np)    = self (\s io -> intNP np (\o -> 
                                        intDV dv s io o))
intVP (VP5 _not inf)   = \s -> neg (intINF inf s)

intTV :: TV -> Idx -> Idx -> Trans
intTV Loved    = blowupPred2 love 
intTV Admired  = blowupPred2 admire 
intTV Helped   = blowupPred2 help
intTV Defeated = blowupPred2 defeat

intDV :: DV -> Idx -> Idx -> Idx -> Trans
intDV Gave = blowupPred3 give

intINF :: INF -> Idx -> Trans
intINF Laugh               = intVP Laughed
intINF Cheer               = intVP Cheered
intINF Shudder             = intVP Shuddered 
intINF (INF1 tinf np)      = \s -> intNP np (\o -> 
                                   intTINF tinf s o)
intINF (INF2 dinf np1 np2) = \s -> intNP np1 (\io -> 
                                   intNP np2 (\o  -> 
                                   intDINF dinf s io o))

intTINF :: TINF -> Idx -> Idx -> Trans
intTINF Love   = intTV Loved
intTINF Admire = intTV Admired
intTINF Help   = intTV Helped
intTINF Defeat = intTV Defeated

intDINF :: DINF -> Idx -> Idx -> Idx -> Trans
intDINF Give   = intDV Gave

intCN :: CN -> Idx -> Trans
intCN Girl     = blowupPred girl
intCN Boy      = blowupPred boy
intCN Princess = blowupPred princess
intCN Dwarf    = blowupPred dwarf
intCN Giant    = blowupPred giant
intCN Wizard   = blowupPred wizard
intCN Sword    = blowupPred sword

intDET :: DET -> (Idx -> Trans) -> (Idx -> Trans) -> Trans

intDET Some  = \ phi psi c -> let i = length c in
               (exists `conj` (phi i) `conj` (psi i)) c 
intDET Every = \ phi psi c -> let i = length c in
       neg (exists `conj` (phi i) `conj` (neg (psi i))) c

intDET No    = \ phi psi c -> let i = length c in
             neg (exists `conj` (phi i) `conj` (psi i)) c 
intDET The   = \ phi psi c -> let i = length c in 
               ((unique (phi i)) `conj` 
                 exists `conj` (phi i) `conj` (psi i)) c

intRCN :: RCN -> Idx -> Trans
intRCN (RCN1 cn _ vp)   = \i -> conj (intCN cn i) 
                                     (intVP vp i)
intRCN (RCN2 cn _ np v) = \i -> conj (intCN cn i) 
                                     (intNP np (intTV v i))

eval :: Sent -> Prop
eval = \ s -> intS s context 

ex1  = Sent Dorothy Cheered
ex2  = Sent Dorothy Laughed
ex3  = Sent Dorothy (VP5 DidNot Laugh)
ex4  = Txt  (Sent Dorothy Cheered)
            (Sent LittleMook Cheered)
ex5  = Txt  (Sent Dorothy Cheered)
            (Sent (PRO 1) (VP1 Admired (NP1 Some Girl)))
ex6  = Sent (NP1 Some Boy) (VP1 Loved (NP1 Some Princess))
ex7  = Sent (NP1 Some Boy) (VP1 Loved (NP1 The Princess))

ex8  = Sent (NP1 Some Boy) (VP1 Defeated (NP1 No Giant))
ex9  = Sent (NP1 The  Boy) (VP1 Defeated (NP1 No Giant))
ex10 = Sent (NP1 Some Boy) (VP1 Loved (NP1 The Princess))

ex11 = Sent (NP1 No   Boy) (VP1 Loved Goldilocks)
ex12 = Sent (NP1 Some Boy) (VP1 Loved SnowWhite)
ex13 = Sent LittleMook (VP1 Loved    (NP1 Some Princess))
ex14 = Sent LittleMook (VP1 Defeated (NP2 Some (RCN1 Giant 
                                That (VP1 Loved Alice))))
ex15 = Sent (NP1 No Wizard) (VP1 Loved Dorothy)
ex16 = Sent (NP2 No (RCN1 Giant That 
                    (VP1 Defeated LittleMook))) 
            (VP1 Loved Dorothy)
ex17 = Sent (NP2 Some(RCN1 Princess That 
                     (VP1 Admired LittleMook))) 
            (VP1 Loved Dorothy)
ex19 = Sent (PRO 2) (VP1 Loved   (PRO 1))
ex20 = Sent (PRO 2) (VP1 Admired (PRO 1))
ex18 = Sent (NP1 The  Boy)  (VP1 Loved SnowWhite)
ex21 = Sent (NP1 Some Girl) (VP2 Admired Self)
ex22 = Sent (NP1 No   Boy)  (VP2 Admired Self)

data Constraint = C1 VP Idx 
                | C2 TV Idx Idx 
                | C3 DV Idx Idx Idx
                | C4 VP Idx 
                | C5 TV Idx Idx 
                | C6 DV Idx Idx Idx
                deriving Eq

instance Show Constraint where 
  show (C1 vp i)     = show vp ++ (' ':show i)
  show (C2 tv i j)   = show tv ++ (' ':show i) 
                               ++ (' ':show j)
  show (C3 dv i j k) = show dv ++ (' ':show i) 
                               ++ (' ':show j) 
                               ++ (' ':show k)

  show (C4 vp i)     = '-':show vp ++ (' ':show i)
  show (C5 tv i j)   = '-':show tv ++ (' ':show i) 
                                   ++ (' ':show j)
  show (C6 dv i j k) = '-':show dv ++ (' ':show i) 
                                   ++ (' ':show j) 
                                   ++ (' ':show k)

maxIndex  :: Constraint -> Idx
maxIndex (C1 vp i)     = i
maxIndex (C2 tv i j)   = max i j 
maxIndex (C3 dv i j k) = maximum [i,j,k]
maxIndex (C4 vp i)     = i
maxIndex (C5 tv i j)   = max i j 
maxIndex (C6 dv i j k) = maximum [i,j,k]

type Context' = ([(Idx,Entity)],[Constraint])
type Prop'    = [Context']
type Trans'   = Context' -> Bool -> Prop'

size :: Context' -> Int
size (c,co) = length c

lookupIdx' :: Context' -> Idx -> Entity 
lookupIdx' ([],co)       j = error "undefined context item"
lookupIdx' ((i,x):xs,co) j | i == j    = x
                           | otherwise = lookupIdx' (xs,co) j

adjust :: (Idx,Entity) -> Context' -> Context'
adjust (i,x) (c,co) 
     | elem (i,x) c = (((i,x):(filter (/=(i,x)) c)),co)
     | otherwise    = error "item not found in context"

extend' :: Context' -> Entity -> Context' 
extend' = \ (c,co) e -> let i = length c in (((i,e):c),co)

success :: Context' -> Trans' -> Bool
success = \ c phi -> phi c True /= []

cutoff :: [Context'] -> Idx -> [Context']
cutoff []          i = []
cutoff ((c,co):cs) i = (cutoffc c i,cutoffco co i)
                      :(cutoff cs i) 
  where 
     cutoffc []         i             = []
     cutoffc ((j,x):xs) i | j >= i    = cutoffc xs i
                          | otherwise = (j,x):(cutoffc xs i)
     cutoffco []        i             = []
     cutoffco (co:cos)  i 
                   | maxIndex co >= i = cutoffco cos i
                   | otherwise        = co:(cutoffco cos i)

neg' :: Trans' -> Trans'
neg' = \ phi c b -> if b then phi c False
                         else cutoff (phi c True) (size c)

conj' :: Trans' -> Trans' -> Trans' 
conj' = \ phi psi c b -> if b 
      then concat [ psi c' True | c' <- phi c True ] 
      else if any (\c' -> psi c' True /= []) (phi c True)
           then []
           else if   (phi c True) == [] then (phi c False)
                else nub (cutoff (concat [psi c' False  | 
                                          c' <- phi c True]) 
                                 (size c))

impl' ::  Trans' -> Trans' -> Trans' 
impl' = \ phi psi ->  neg' (phi `conj'` (neg' psi))

exists' :: Trans'
exists' = \ c b -> if   b 
                   then [ (extend' c e) | e <- entities ]
                   else []

blowupPred' :: (Entity -> Bool) -> Idx -> Trans'
blowupPred' = \ pred i c  b -> 
     let 
         e  = lookupIdx' c i 
         c' = adjust (i,e) c
     in  
         if  b 
         then if   pred e 
              then [c'] 
              else []
         else if   pred e 
              then [] 
              else [c']

blowupVP :: VP -> OnePlacePred -> Idx -> Trans'
blowupVP = \ vp pred i c b -> 
         let 
             e        = lookupIdx' c i 
             (c',cos) = adjust (i,e) c
             co       = C1 vp i
             co'      = C4 vp i
         in  
             if   b 
             then if   pred e 
                  then [(c',co:cos)] 
                  else []
             else if   pred e 
                  then [] 
                  else [(c',co':cos)]

blowupTV :: TV -> TwoPlacePred -> Idx -> Idx -> Trans'
blowupTV = \ tv pred subj obj c b -> 
        let 
            e1       = lookupIdx' c subj
            e2       = lookupIdx' c obj 
            (c',cos) = adjust (subj,e1) (adjust (obj,e2) c)
            co       = C2 tv subj obj
            co'      = C5 tv subj obj
        in  
            if   b 
            then if   pred e1 e2 
                 then [(c',co:cos)] 
                 else []
            else if pred e1 e2 
                 then [] 
                 else [(c',co':cos)]

blowupDV :: DV  -> ThreePlacePred -> 
            Idx -> Idx -> Idx -> Trans'
blowupDV = \ dv pred subj iobj dobj c b -> 
        let 
            e1       = lookupIdx' c subj
            e2       = lookupIdx' c iobj 
            e3       = lookupIdx' c dobj 
            (c',cos) = adjust (subj,e1) 
                      (adjust (iobj,e2)
                      (adjust (dobj,e3) c))
            co       = C3 dv subj iobj dobj
            co'      = C6 dv subj iobj dobj
        in  
            if   b 
            then if   pred e1 e2 e3 
                 then [(c',co:cos)] 
                 else []
            else if   pred e1 e2 e3 
                 then [] 
                 else [(c',co':cos)]

resolveMASC :: Context' -> [Idx]
resolveMASC (c,co)  = resolveMASC' c where
  resolveMASC' []                     = [] 
  resolveMASC' ((i,x):xs) | male x    = i : resolveMASC' xs
                          | otherwise = resolveMASC' xs

resolveFEM :: Context' -> [Idx]
resolveFEM (c,co)  = resolveFEM' c where
  resolveFEM' []                     = [] 
  resolveFEM' ((i,x):xs) | female x  = i : resolveFEM' xs
                         | otherwise = resolveFEM' xs

resolveNEU :: Context' -> [Idx]
resolveNEU (c,co)  = resolveNEU' c where
  resolveNEU'  []                     = [] 
  resolveNEU'  ((i,x):xs) | thing x   = i : resolveNEU' xs
                          | otherwise = resolveNEU' xs

resolveNAME :: Entity -> Context' -> (Idx,Context')
resolveNAME x c | i /= -1   = (i,c)
                | otherwise = (j,extend' c x)
  where i                                 = index x c 
        j                                 = size c 
        index x ([],co)                   = -1
        index x ((i,y):xs,co) | x == y    = i 
                              | otherwise = index x (xs,co)

nonCoref :: (Idx -> Idx -> Trans') -> Idx -> Idx -> Trans'
nonCoref = \ p i j c b -> if   i /= j 
                          then (p i j c b) 
                          else []

nonCoref2 :: (Idx -> Idx -> Idx -> Trans') ->
              Idx -> Idx -> Idx -> Trans'
nonCoref2 = \ p i j k c b -> if   i /= j && j /= k && i /= k 
                             then (p i j k c b) 
                             else []

intS' :: Sent -> Trans'
intS' (Sent np vp) = (intNP' np) (intVP' vp)
intS' (If   s1 s2) = (intS' s1) `impl'` (intS' s2)
intS' (Txt  s1 s2) = (intS' s1) `conj'` (intS' s2)

intNP' :: NP -> (Idx -> Trans') -> Trans'
intNP' SnowWhite  = \p c -> 
                    let (i,c') = resolveNAME snowWhite c
                    in  p i c'
intNP' Alice      = \p c -> 
                    let (i,c') = resolveNAME alice c
                    in  p i c'
intNP' Dorothy    = \p c -> 
                    let (i,c') = resolveNAME dorothy c
                    in  p i c'
intNP' Goldilocks = \p c -> 
                    let (i,c') = resolveNAME goldilocks c
                    in  p i c'
intNP' LittleMook = \p c -> 
                    let (i,c') = resolveNAME littleMook c
                    in  p i c'

intNP' He  = \p c b -> concat [p i c b | i <- resolveMASC c]
intNP' She = \p c b -> concat [p i c b | i <- resolveFEM  c]
intNP' It  = \p c b -> concat [p i c b | i <- resolveNEU  c]
intNP' (PRO i)       = \ p c ->  p i c 
intNP' (NP1 det cn)  = (intDET' det) (intCN' cn) 
intNP' (NP2 det rcn) = (intDET' det) (intRCN' rcn)

intVP' :: VP -> Idx -> Trans'
intVP' (VP1 tv np)      = \ s -> intNP'  np (\ o -> 
                          nonCoref (intTV' tv) s o) 
intVP' (VP2 tv refl)    = self (intTV' tv)
intVP' (VP3 dv np1 np2) = \ s -> intNP' np1 (\ io -> 
                                 intNP' np2 (\ o  -> 
                          nonCoref2 (intDV' dv) s io o))
intVP' (VP4 dv refl np) = self (\ s io -> intNP' np (\ o -> 
                                          intDV' dv s io o))
intVP' (VP5 _not inf)   = \ s -> neg' (intINF' inf s)

intVP' Laughed   = blowupVP Laughed   laugh
intVP' Cheered   = blowupVP Cheered   cheer 
intVP' Shuddered = blowupVP Shuddered shudder 

intTV' :: TV -> Idx -> Idx -> Trans'
intTV' Loved    = blowupTV Loved    love 
intTV' Admired  = blowupTV Admired  admire 
intTV' Helped   = blowupTV Helped   help 
intTV' Defeated = blowupTV Defeated defeat 

intDV' :: DV -> Idx -> Idx -> Idx -> Trans'
intDV' Gave     = blowupDV Gave     give

intINF' :: INF -> Idx -> Trans'
intINF' Laugh               = intVP' Laughed
intINF' Cheer               = intVP' Cheered
intINF' Shudder             = intVP' Shuddered 
intINF' (INF1 tinf np)      = \ s -> intNP' np  (\ o -> 
                                     intTINF' tinf s o)
intINF' (INF2 dinf np1 np2) = \ s -> intNP' np1 (\ io -> 
                                     intNP' np2 (\ o  -> 
                                     intDINF' dinf s io o))

intTINF' :: TINF -> Idx -> Idx -> Trans'
intTINF' Love   = intTV' Loved
intTINF' Admire = intTV' Admired
intTINF' Help   = intTV' Helped
intTINF' Defeat = intTV' Defeated

intDINF' :: DINF -> Idx -> Idx -> Idx -> Trans'
intDINF' Give   = intDV' Gave

intCN' :: CN -> Idx -> Trans'
intCN' Girl     = blowupPred' girl 
intCN' Boy      = blowupPred' boy
intCN' Princess = blowupPred' princess
intCN' Dwarf    = blowupPred' dwarf
intCN' Giant    = blowupPred' giant
intCN' Wizard   = blowupPred' wizard
intCN' Sword    = blowupPred' sword

unique' :: Idx -> Trans' -> Trans'
unique' i phi c b = 
 if b == singleton xs then [c] else [] 
   where xs = [ x | x <- entities, success (extend' c x) phi ]

intDET' :: DET -> (Idx -> Trans') 
               -> (Idx -> Trans') -> Trans'
intDET' Some  = \ phi psi c -> let i = size c in 
                 (exists' `conj'` (phi i) `conj'` (psi i)) c
intDET' Every = \ phi psi c -> let i = size c in 
                (impl' (exists' `conj'` (phi i)) 
                       (psi i)) c
intDET' No    = \ phi psi c -> let i = size c in 
                (impl' (exists' `conj'` (phi i)) 
                       (neg' (psi i))) c
intDET' The   = \ phi psi c -> let i = size c in 
                (conj' (unique' i (phi i)) 
                        exists' `conj'` (phi i) 
                                `conj'` (psi i)) c

intRCN' :: RCN -> Idx -> Trans'
intRCN' (RCN1 cn _ vp)    = \i -> conj' (intCN' cn i) 
                                        (intVP' vp i)
intRCN' (RCN2 cn _ np tv) = \i -> conj' (intCN' cn i) 
                             (intNP' np (intTV' tv i))

convert :: Context -> Context'
convert c = (convert' c (length c - 1),[]) 
       where convert' []     i = []
             convert' (x:xs) i = (i,x):(convert' xs (i-1))

eval' :: Sent -> Prop'
eval' s = intS' s (convert context) True

evalFresh :: Sent -> Prop'
evalFresh s = intS' s ([],[]) True

nex1 = Sent He (VP1 Admired (NP1 Some Girl))

nex2 = Sent (NP1 Some Dwarf) (VP1 Defeated (NP1 The Giant))

nex2a = Sent (NP1 Some Dwarf) (VP1 Defeated (NP1 The Giant)) 
        `Txt` (Sent He Cheered)

nex2b = Sent (NP1 Some Dwarf) (VP1 Defeated (NP1 The Giant)) 
        `Txt` (Sent He (VP5 DidNot Cheer))

nex3 = (Sent LittleMook Cheered) `Txt` 
       (Sent He (VP1 Admired (NP1 Some Girl)))

nex4 = Txt (Sent (NP1 Some Dwarf) (VP5 DidNot Shudder))
           (Sent He (VP1 Defeated (NP1 Some Giant)))

nex5 = (Sent LittleMook (VP5 DidNot (INF1 Admire Dorothy)))
       `Txt` (Sent He Cheered)

nex6 = Txt (Sent (NP1 Some Dwarf) 
                 (VP5 DidNot (INF1 Admire Dorothy)))
           (Sent He (VP5 DidNot Cheer))

nex7 = Sent (NP1 Some Giant) 
            (VP5 DidNot (INF1 Admire (NP1 Some Princess)))

nex8  = (Sent (NP1 The Princess) (VP1 Defeated (NP1 The Giant))) 
        `Txt` (Sent She (VP1 Admired He))
nex9  = Sent He (VP1 Loved He)
nex10 = Sent He (VP2 Admired Self)
nex11 = Sent He (VP1 Admired He)
nex12 = Sent (NP1 The Giant ) (VP2 Admired Self)
nex13 = Txt (Sent (NP1 The Princess ) (VP2 Admired Self)) 
            (Sent She (VP1 Loved (NP1 The Giant)))
nex14 = Txt (Sent (NP1 Some Boy) (VP2 Admired Self))
            (Sent (NP1 Some Princess) (VP1 Loved He))
nex15 = If  (Sent (NP1 Some Boy) (VP2 Admired Self))
            (Sent (NP1 Some Giant) (VP1 Loved He))
nex16 = Txt (Sent (NP1 No Girl) (VP1 Helped LittleMook))
            (Sent (NP1 Some Princess) (VP1 Loved He))

