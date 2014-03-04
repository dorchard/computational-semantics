module HRAS where 

import Data.List 
import Model
import FSynF hiding (Form,Term,Var,Eq,Neg,
                     Impl,Equi,Conj,Disj)
import TCOM
import P     

data RL a r = Zero r 
            | Succ (RL a (a -> r))

type REL a = RL a Bool 

arity :: RL a b -> Int
arity (Zero _) = 0 
arity (Succ r) = succ (arity r)

apply :: REL a -> a -> REL a
apply (Zero _) _ = error "no argument position left"
apply (Succ r) x = apply' r x

apply' :: RL a (a -> r) -> a -> RL a r 
apply' (Zero f) x = Zero (f x)
apply' (Succ r) x = Succ (apply' r x)

abstract :: Int -> (a -> REL a) -> REL a
abstract = abstract'

abstract' :: Int -> (a -> RL a b) -> RL a b
abstract' 0 f = Succ (Zero (\ x -> charF (f x)))
  where charF :: RL a r -> r 
        charF (Zero f) = f 
        charF (Succ _) = error "arity error"
abstract' n f = Succ (abstract' (n-1) (\ x -> relF (f x)))
  where relF :: RL a r -> RL a (a -> r)
        relF (Zero _)  = error "nullary rel"
        relF (Succ r)  = r

encode0 :: Bool -> REL a
encode0 b = Zero b

encode1 :: (a -> Bool) -> REL a
encode1 f = Succ (Zero f)

encode2 :: (a -> a -> Bool) -> REL a
encode2 f = Succ (Succ (Zero f))

encode3 :: (a -> a -> a -> Bool) -> REL a
encode3 f = Succ (Succ (Succ (Zero f)))

decode0 :: REL a -> Bool
decode0 (Zero b) = b 
decode0 r        = error ("relation of arity " ++ ar)
        where ar = show (arity r)

decode1 :: REL a -> a -> Bool
decode1 (Succ (Zero f)) = f 
decode1 r               = error ("relation of arity " ++ ar)
               where ar = show (arity r)

listUncurry :: REL a -> [a] -> Bool
listUncurry   (Zero b) []     = b
listUncurry r@(Succ _) (x:xs) = listUncurry (apply r x) xs

rel2lists :: [a] -> REL a -> [[a]]
rel2lists domain (Zero b) = [[] | b ]
rel2lists domain (Succ r) = 
   [ x: tuple | x     <- domain, 
                tuple <- 
                 rel2lists domain (apply (Succ r) x) ]

upred2lists :: [a] -> (a -> Bool) -> [[a]]
upred2lists domain p = [ [x]     | x <- filter p domain ]

bpred2lists :: [a] -> (a -> a -> Bool) -> [[a]]
bpred2lists domain p = [ [x,y]   | x <- domain, 
                                   y <- domain,
                                   p x y             ]
tpred2lists :: [a] -> (a -> a -> a -> Bool) -> [[a]]
tpred2lists domain p = [ [x,y,z] | x <- domain, 
                                   y <- domain,
                                   z <- domain,
                                   p x y z         ]

lists2rel ::  Eq a => Int -> [[a]] -> REL a 
lists2rel 0 [[]] = Zero True
lists2rel 0 []   = Zero False
lists2rel n xss  = abstract (n-1) r 
       where r x = let yss = filter (\ xs -> head xs == x) xss
                   in  lists2rel (n-1) (map tail yss) 

listCurry :: Int -> ([a] -> Bool) -> REL a
listCurry 0 f = Zero (f [])
listCurry n f = abstract (n-1) g 
 where g x    = listCurry (n-1) (h x) 
       h x xs = f (x:xs) 

liftOp :: (Bool -> Bool -> Bool) -> REL a -> REL a -> REL a
liftOp op (Zero b)   (Zero c)   = Zero (op b c) 
liftOp op r@(Succ _) s@(Succ _) = 
  abstract n (\ x -> liftOp op (apply r x) (apply s x))
     where n = arity r - 1
liftOp op _          _          = error "arity mismatch"

conjR :: REL a -> REL a -> REL a
conjR = liftOp (&&)

disjR :: REL a -> REL a -> REL a
disjR = liftOp (||)

negR :: REL a -> REL a
negR (Zero b)   = Zero (not b)
negR r@(Succ _) = abstract n (\x -> negR (apply r x))
        where n = arity r - 1

type KQ a = REL a -> REL a 

liftQ :: ((a -> Bool) -> Bool) -> KQ a
liftQ f r 
 | arity r == 0 = error "no argument position left"
 | arity r == 1 = Zero (f (decode1 r))
 | otherwise    = abstract (n-1) g
    where g x   = liftQ f (apply r x)
          n     = arity r - 1

swap :: REL a -> REL a
swap r    = abstract n (\ x -> 
              abstract (n-1) (\ y -> 
                (apply (apply r y) x)))
  where n = arity r - 1

qscopeReversal :: KQ a -> KQ a -> KQ a
qscopeReversal q1 q2 = q2 . q1 . swap

role :: Int -> [a] -> a
role n es = es !! (n-1)

roles :: [Int] -> [a] -> [a]
roles []     _  = []
roles (i:is) es = role i es : roles is es 

extr :: Eq a => [Int] -> [[a]] -> [[a]]
extr is ess = nub [ roles is es | es <- ess ]

extract :: Eq a => [a] -> [Int] -> REL a -> REL a 
extract domain is r = 
  lists2rel n (extr is (rel2lists domain r))
      where n = length is 

extr2lists :: Eq a => [a] -> [Int] -> REL a -> [[a]]
extr2lists domain is = 
  rel2lists domain . extract domain is

data VerbPhrase = V1 VP | V2 TV | V3 DV 

instance Show VerbPhrase where 
  show (V1 vp) = show vp 
  show (V2 vp) = show vp
  show (V3 vp) = show vp

relVP :: VerbPhrase -> REL Entity 
relVP (V1 Laughed)   = encode1 laugh
relVP (V1 Cheered)   = encode1 cheer
relVP (V1 Shuddered) = encode1 shudder
relVP (V2 Loved)     = encode2 love
relVP (V2 Admired)   = encode2 admire
relVP (V2 Helped)    = encode2 help
relVP (V2 Defeated)  = encode2 defeat
relVP (V3 Gave)      = encode3 give

relNP :: NP -> KQ Entity
relNP = liftQ . intNP

relNPs :: [NP] -> KQ Entity
relNPs [] = id 
relNPs (np:nps) = relNP np . relNPs nps

relSent :: [NP] -> VerbPhrase -> REL Entity
relSent nps vp = (relNPs nps) (relVP vp)

eval :: [NP] -> VerbPhrase -> Bool 
eval nps vp 
 | length nps == arity (relVP vp) = decode0 (relSent nps vp) 
 | otherwise                      = error "arity mismatch"

perms :: [a] -> [[a]]
perms []     = [[]]
perms (x:xs) = concat (map (insrt x) (perms xs))
  where 
   insrt :: a -> [a] -> [[a]]
   insrt x []     = [[x]]
   insrt x (y:ys) = (x:y:ys) : map (y:) (insrt x ys)

permsInPar :: [a] -> [b] -> [([a],[b])]
permsInPar xs ys = map unzip (perms (zip xs ys))

permRelNPs :: Eq a  => 
              [a]   -> 
              REL a -> 
              [NP]  -> [([Int],REL a,[NP])]
permRelNPs domain rel nps = 
  [  (perm,extract domain perm rel,pnps) | 
     (perm,pnps) <- permsInPar [1..length nps] nps  ]

allScopings :: [NP] -> VerbPhrase -> [([Int],Bool)]
allScopings nps vp = 
 [(perm, decode0 ((relNPs pnps) newrel))
     | (perm, newrel, pnps) <- 
           permRelNPs entities (relVP vp) nps, 
           arity (relVP vp) == length nps      ]

data RForm = MkRForm [Int] LF deriving Eq

instance Show RForm where 
  show (MkRForm [] lf) = show lf
  show (MkRForm is lf) = " \\" ++ show (map Var is) 
                               ++ " -> " ++ show lf

freshIdx :: RForm -> Int
freshIdx (MkRForm _ lf) = freshIndex [lf]

type KQLF   = RForm -> RForm 

data KOp = MkKOp Int KQLF 

instance Show KOp where 
  show (MkKOp n q) = 
   "\\ R -> " ++ show (q (MkRForm is (Rel "R" is')))
       where k     = freshIdx rform 
             rform = q (MkRForm js (Rel "R" js'))
             js    = take n (repeat 0)
             js'   = map Var js
             is    = map (+k) [0..n-1]
             is'   = map Var is

neg :: KQLF 
neg (MkRForm is lf) = MkRForm is (Neg lf)

ng :: KOp
ng = MkKOp 0 neg

liftKQLF :: ((Term -> LF) -> LF) -> KQLF
liftKQLF np (MkRForm [] lf) 
   = error "No argument position left"
liftKQLF np (MkRForm (i:is) lf) 
   = MkRForm is (np (\ x -> (subi i x lf)))

substi :: Int -> Term -> Term -> Term 
substi i x (Const name)         = Const name
substi i x (Var n) | n == i     = x
                   | otherwise  = Var n
                   | x == Var n = error "bad substitution"

subi :: Int -> Term -> LF -> LF 
subi i x (Rel name ts)  = Rel name (map (substi i x) ts)
subi i x (Eq t1 t2)     = Eq (substi i x t1) (substi i x t2)
subi i x (Neg lf)       = Neg (subi i x lf)
subi i x (Impl lf1 lf2) = Impl (subi i x lf1) (subi i x lf2)
subi i x (Equi lf1 lf2) = Equi (subi i x lf1) (subi i x lf2)
subi i x (Conj lfs)     = Conj (map (subi i x) lfs) 
subi i x (Disj lfs)     = Disj (map (subi i x) lfs) 
subi i x (Qt gq abs1 abs2) = 
                Qt gq (sbi i x abs1) (sbi i x abs2)

sbi :: Int -> Term -> Abstract -> Abstract
sbi i x (MkAbstract j lf) 
  | i == j    = MkAbstract 0 lf
  | otherwise = MkAbstract j (subi i x lf)

lfVerbPhrase :: VerbPhrase -> RForm
lfVerbPhrase (V1 Laughed)   = 
  MkRForm [1]     (Rel "laugh"   [Var 1])
lfVerbPhrase (V1 Cheered)   = 
  MkRForm [1]     (Rel "cheer"   [Var 1])

lfVerbPhrase (V1 Shuddered) = 
  MkRForm [1]     (Rel "shudder" [Var 1])
lfVerbPhrase (V2 Loved)     = 
  MkRForm [1,2]   (Rel "love"    [Var 2,Var 1])
lfVerbPhrase (V2 Admired)   = 
  MkRForm [1,2]   (Rel "admire"  [Var 2,Var 1])
lfVerbPhrase (V2 Helped)    = 
  MkRForm [1,2]   (Rel "help"    [Var 2,Var 1])
lfVerbPhrase (V2 Defeated)  = 
  MkRForm [1,2]   (Rel "defeat"  [Var 2,Var 1])
lfVerbPhrase (V3 Gave)      = 
  MkRForm [1,2,3] (Rel "give"    [Var 3,Var 2,Var 1])

trNP :: NP -> KQLF 
trNP = liftKQLF . lfNP

lfNP :: NP -> (Term -> LF) -> LF
lfNP SnowWhite     = \ p -> p (Const "SnowWhite"  )
lfNP Alice         = \ p -> p (Const "Alice"      )
lfNP Dorothy       = \ p -> p (Const "Dorothy"    )
lfNP Goldilocks    = \ p -> p (Const "Goldilocks" )
lfNP LittleMook    = \ p -> p (Const "LittleMook" )
lfNP Atreyu        = \ p -> p (Const "Atreyu"     )
lfNP (NP1 det cn)  = (lfDET det) (lfCN cn) 

opNP :: NP -> KOp
opNP = MkKOp 1 . trNP 

lfCN :: CN -> Term -> LF
lfCN Girl     = \ t -> Rel "girl"     [t]
lfCN Boy      = \ t -> Rel "boy"      [t]
lfCN Princess = \ t -> Rel "princess" [t] 
lfCN Dwarf    = \ t -> Rel "dwarf"    [t] 
lfCN Giant    = \ t -> Rel "giant"    [t] 
lfCN Wizard   = \ t -> Rel "wizard"   [t] 
lfCN Sword    = \ t -> Rel "sword"    [t] 
lfCN Dagger   = \ t -> Rel "dagger"   [t] 

lfDET :: DET -> (Term -> LF) -> (Term -> LF) -> LF
lfDET Some = \ p q -> let i = fresh[p,q] in 
             Qt Sm (MkAbstract i (p (Var i))) 
                   (MkAbstract i (q (Var i)))
lfDET Every = \ p q -> let i = fresh[p,q] in 
              Qt All (MkAbstract i (p (Var i))) 
                     (MkAbstract i (q (Var i)))
lfDET No = \ p q -> let i = fresh[p,q] in 
             Neg (Qt Sm (MkAbstract i (p (Var i))) 
                        (MkAbstract i (q (Var i))))
lfDET The = \ p q -> let i = fresh[p,q] in 
              Qt Th (MkAbstract i (p (Var i))) 
                    (MkAbstract i (q (Var i)))

lfSent :: [NP] -> VerbPhrase -> RForm 
lfSent []       vp = lfVerbPhrase vp
lfSent (np:nps) vp = trNP np (lfSent nps vp)

uForm :: [NP] -> VerbPhrase -> ([KOp],RForm)
uForm nps vp = (f nps, lfVerbPhrase vp)
     where f = map (MkKOp 1 . trNP) 

