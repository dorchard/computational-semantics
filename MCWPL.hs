module MCWPL where 

import Data.List
import FSynF
import Model

type LF = Formula Term

lfSent :: Sent -> LF
lfSent (Sent np vp) = (lfNP np) (lfVP vp)

lfNP :: NP -> (Term -> LF) -> LF
lfNP SnowWhite     = \ p -> p (Struct "SnowWhite"  [])
lfNP Alice         = \ p -> p (Struct "Alice"      [])
lfNP Dorothy       = \ p -> p (Struct "Dorothy"    [])
lfNP Goldilocks    = \ p -> p (Struct "Goldilocks" [])
lfNP LittleMook    = \ p -> p (Struct "LittleMook" [])
lfNP Atreyu        = \ p -> p (Struct "Atreyu"     [])
lfNP (NP1 det cn)  = (lfDET det) (lfCN cn) 
lfNP (NP2 det rcn) = (lfDET det) (lfRCN rcn) 

lfVP :: VP -> Term -> LF
lfVP Laughed   = \ t -> Atom "laugh"   [t]
lfVP Cheered   = \ t -> Atom "cheer"   [t]
lfVP Shuddered = \ t -> Atom "shudder" [t]

lfVP (VP1 tv np) =
    \ subj -> lfNP np (\ obj -> lfTV tv (subj,obj))
lfVP (VP2 dv np1 np2) = 
    \ subj -> lfNP np1 (\ iobj -> lfNP np2 (\ dobj -> 
                          lfDV dv (subj,iobj,dobj)))

lfTV :: TV -> (Term,Term) -> LF
lfTV Loved    = \ (t1,t2) -> Atom "love"   [t1,t2]
lfTV Admired  = \ (t1,t2) -> Atom "admire" [t1,t2]
lfTV Helped   = \ (t1,t2) -> Atom "help"   [t1,t2]
lfTV Defeated = \ (t1,t2) -> Atom "defeat" [t1,t2]

lfDV :: DV -> (Term,Term,Term) -> LF
lfDV Gave = \ (t1,t2,t3) -> Atom "give" [t1,t2,t3]

lfCN :: CN -> Term -> LF
lfCN Girl     = \ t -> Atom "girl"     [t]
lfCN Boy      = \ t -> Atom "boy"      [t]

lfCN Princess = \ t -> Atom "princess" [t] 
lfCN Dwarf    = \ t -> Atom "dwarf"    [t] 
lfCN Giant    = \ t -> Atom "giant"    [t] 
lfCN Wizard   = \ t -> Atom "wizard"   [t] 
lfCN Sword    = \ t -> Atom "sword"    [t] 
lfCN Dagger   = \ t -> Atom "dagger"   [t] 

lfDET :: DET -> (Term -> LF) -> (Term -> LF) -> LF

bInLF :: LF -> [Int]
bInLF (Atom _ _)                  = []
bInLF (Eq _ _)                    = []
bInLF (Neg lf)                    = bInLF lf 
bInLF (Impl lf1 lf2)              = bInLFs [lf1,lf2] 
bInLF (Equi lf1 lf2)              = bInLFs [lf1,lf2]

bInLF (Conj lfs)                  = bInLFs lfs 
bInLF (Disj lfs)                  = bInLFs lfs 
bInLF (Forall (Variable _ [i]) f) = i : bInLF f 
bInLF (Exists (Variable _ [i]) f) = i : bInLF f 

bInLFs :: [LF] -> [Int]
bInLFs = nub . concat . map bInLF

freshIndex  :: [LF] -> Int
freshIndex lfs = i+1
       where i = maximum (0:(bInLFs lfs))

fresh :: [Term -> LF] -> Int
fresh preds   = freshIndex (map ($ dummy) preds) 
  where dummy = Struct "" []

lfDET Some  p q = Exists v (Conj [p (Var v), q (Var v)]) 
        where v = Variable "x" [fresh[p,q]]
lfDET Every p q = Forall v (Impl (p (Var v)) (q (Var v))) 
        where v = Variable "x" [fresh[p,q]]
lfDET No    p q = Neg (Exists v (Conj [p (Var v),q (Var v)]))
        where v = Variable "x" [fresh[p,q]]

lfDET The p q = Exists v1 (Conj 
                 [Forall v2 (Equi (p (Var v2)) 
                                  (Eq (Var v1) (Var v2))), 
                  q (Var v1)])
      where
           i  = fresh[p,q]
           v1 = Variable "x" [i]
           v2 = Variable "x" [i+1]

lfRCN :: RCN -> Term -> LF
lfRCN (RCN1 cn _ vp)    = \ t -> Conj [lfCN cn t, lfVP vp t]
lfRCN (RCN2 cn _ np tv) = \ t -> Conj [lfCN cn t, 
                       lfNP np (\ subj -> lfTV tv (subj,t))]

lf1 = lfSent (Sent (NP1 Some Dwarf) 
                   (VP1 Defeated (NP1 Some Giant))) 
lf2 = lfSent (Sent (NP2 The (RCN2 Wizard 
                                  That Dorothy Admired)) 
                    Laughed) 
lf3 = lfSent (Sent (NP2 The (RCN1 Princess 
                                  That (VP1 Helped Alice))) 
                    Shuddered)

type Interp a = String -> [a] -> Bool

int0 :: Interp Entity
int0 "Laugh"   = \ [x]     -> laugh x
int0 "Cheer"   = \ [x]     -> cheer x
int0 "Shudder" = \ [x]     -> shudder x
int0 "Love"    = \ [x,y]   -> love y x 
int0 "Admire"  = \ [x,y]   -> admire y x
int0 "Help"    = \ [x,y]   -> help y x
int0 "Defeat"  = \ [x,y]   -> defeat y x
int0 "Give"    = \ [x,y,z] -> give z y x

type Lookup a = Variable -> a

change :: Lookup a -> Variable -> a -> Lookup a 
change g x d = \ v -> if x == v then d else g v

ass0 :: Lookup Entity
ass0 = \ v -> A

ass1 :: Lookup Entity 
ass1 = change ass0 y B

eval :: Eq a => 
    [a]              -> 
    Interp a         -> 
    Lookup a         -> 
    Formula Variable -> Bool

eval domain i = eval' where 
  eval' g (Atom str vs) = i str (map g vs)
  eval' g (Eq   v1 v2)  = (g v1) == (g v2) 
  eval' g (Neg  f)      = not (eval' g f)
  eval' g (Impl f1 f2)  = not ((eval' g f1) && 
                               not (eval' g f2))
  eval' g (Equi f1 f2)  = (eval' g f1) == (eval' g f2)
  eval' g (Conj fs)     = and (map (eval' g) fs)
  eval' g (Disj fs)     = or  (map (eval' g) fs)
  eval' g (Forall v f)  = and [ eval' (change g v d) f | 
                                d <- domain ]
  eval' g (Exists v f)  = or  [ eval' (change g v d) f | 
                                d <- domain ]

int1 :: String -> [Int] -> Bool
int1 "R" = rconvert (<)
     where 
           rconvert :: (a -> a -> Bool) -> [a] -> Bool
           rconvert r [x,y] = r x y 

ass2 :: Variable -> Int
ass2 v = if v == x then 1 else if v == y then 2 else 0

type FInterp a = String -> [a] -> a

zero = Struct "zero" []

fint1 :: FInterp Int 
fint1 "zero"  []    = 0
fint1 "s"     [i]   = succ i
fint1 "plus"  [i,j] = i + j 
fint1 "times" [i,j] = i * j 

type TVal a = Term -> a

liftLookup :: FInterp a -> Lookup a -> TVal a 
liftLookup fint g (Var v)         = g v
liftLookup fint g (Struct str ts) = 
           fint str (map (liftLookup fint g) ts)

evl :: Eq a => 
  [a]          -> 
  Interp  a    -> 
  FInterp a    -> 
  Lookup  a    -> 
  Formula Term -> Bool

evl domain i fint = evl' where 
   lift = liftLookup fint 
   evl' g (Atom str ts) = i str (map (lift g) ts)
   evl' g (Eq   t1 t2)  = lift g t1 == lift g t2
   evl' g (Neg  f)      = not (evl' g f)
   evl' g (Impl f1 f2)  = not ((evl' g f1) && 
                               not (evl' g f2))
   evl' g (Equi f1 f2)  = evl' g f1 == evl' g f2
   evl' g (Conj fs)     = and (map (evl' g) fs)
   evl' g (Disj fs)     = or  (map (evl' g) fs)
   evl' g (Forall v f)  = and [ evl' (change g v d) f | 
                                d <- domain ]
   evl' g (Exists v f)  = or  [ evl' (change g v d) f | 
                                d <- domain ]

formula3 = Forall x (Forall y (Impl (Atom "R" [tx,ty])
                    (Exists z
                      (Conj [Atom "R" [tx,tz],
                             Atom "R" [tz,ty]]))))

formula4 =  Impl (Atom "R" [tx,ty])
                 (Exists z
                   (Conj [Atom "R" [tx,tz],
                          Atom "R" [tz,ty]]))

int3 :: String -> [Entity] -> Bool
int3 "R" = \ [x,y] -> defeat y x

fint2 :: String -> [Entity] -> Entity
fint2 "zero" [] = A

