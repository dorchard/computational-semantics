module CAIA where

import Data.List 

data Agent = A | B | C | D | E deriving (Eq,Ord,Enum)

a,alice, b,bob, c,carol, d,dave, e,ernie  :: Agent
a = A; alice = A
b = B; bob   = B
c = C; carol = C
d = D; dave  = D
e = E; ernie = E

instance Show Agent where
  show A = "a"; show B = "b"; 
  show C = "c"; show D = "d"; 
  show E = "e"

data Prop = P Int | Q Int | R Int deriving (Eq,Ord)

instance Show Prop where 
  show (P 0) = "p"; show (P i) = "p" ++ show i 
  show (Q 0) = "q"; show (Q i) = "q" ++ show i 
  show (R 0) = "r"; show (R i) = "r" ++ show i

data EpistM state = Mo { 
       dom       :: [state],
       agents    :: [Agent],
       valuation :: [(state,[Prop])],
       rels      :: [(Agent,state,state)],
       actual    :: [state] 
                        } deriving (Eq,Show)

exampleModel :: EpistM Integer
exampleModel = 
 Mo [0..3]
    [a..c]
    [(0,[]),(1,[P 0]),(2,[Q 0]),(3,[P 0, Q 0])]
    ([ (a,x,x) | x <- [0..3] ] ++
     [ (b,x,x) | x <- [0..3] ] ++
     [ (c,x,y) | x <- [0..3], y <- [0..3] ])
    [1]

type Rel a = [(a,a)]

containedIn :: Eq a => [a] -> [a] -> Bool
containedIn xs ys = all (\ x -> elem x ys) xs

cnv :: Rel a -> Rel a
cnv r = [ (y,x) | (x,y) <- r ]

infixr 5 @@

(@@) :: Eq a => Rel a -> Rel a -> Rel a
r @@ s = nub [ (x,z) | (x,y) <- r, (w,z) <- s, y == w ]

reflR :: Eq a => [a] -> Rel a -> Bool
reflR xs r = [(x,x) | x <- xs] `containedIn` r 

symmR :: Eq a => Rel a -> Bool
symmR r = cnv r `containedIn` r

transR :: Eq a => Rel a -> Bool
transR r = (r @@ r) `containedIn` r

isS5 :: Eq a => [a] -> Rel a -> Bool
isS5 xs r = reflR xs r && transR r && symmR r 

rel :: Agent -> EpistM a -> Rel a
rel a model = [ (x,y) | (b,x,y) <- rels model, a == b ]

rel2partition :: Ord a => [a] -> Rel a -> [[a]]
rel2partition []     r = []
rel2partition (x:xs) r = xclass : rel2partition (xs\\xclass) r
             where xclass = x : [ y | y <- xs, (x,y) `elem` r ]

showS5 :: (Ord a,Show a) => EpistM a -> [String]
showS5 m = show (dom m)
           : show (valuation m)
           : map show [ (a,(rel2partition (dom m)) (rel a m)) 
                                           | a <- (agents m)] 
         ++ [show (actual m)]

displayS5 ::  (Ord a,Show a) => EpistM a -> IO()
displayS5 = putStrLn . unlines . showS5

initM :: [Agent] -> [Prop] -> EpistM Integer
initM ags props = (Mo worlds ags val accs points) 
   where worlds = [0..(2^k-1)]
         k      = length props
         val    = zip worlds (sortL (powerList props))
         accs   = [ (ag,st1,st2) | ag  <- ags, 
                                   st1 <- worlds, 
                                   st2 <- worlds  ]
         points = worlds

powerList  :: [a] -> [[a]]
powerList  []     = [[]]
powerList  (x:xs) = (powerList xs) ++ (map (x:) (powerList xs))

sortL :: Ord a => [[a]] -> [[a]]
sortL  = sortBy (\ xs ys -> if   length xs < length ys 
                            then LT
                            else if   length xs > length ys 
                                 then GT
                                 else compare xs ys) 

lfp :: Eq a => (a -> a) -> a -> a
lfp f x | x == f x  = x
        | otherwise = lfp f (f x)

rtc :: Ord a => [a] -> Rel a -> Rel a
rtc xs r = lfp (\ s -> (sort.nub) (s ++ (r@@s))) i
 where i = [ (x,x) | x <- xs ]

data Form = Top 
          | Prop Prop 
          | Neg  Form 
          | Conj [Form]
          | Disj [Form]
          | K    EE Form 
          | PA   Form Form
          | PC   [(Prop,Form)] Form
          deriving (Eq,Ord)

data EE = Agent Agent 
        | Test Form
        | Cmp  EE EE
        | Sum  [EE]
        | Star EE
        deriving (Eq,Ord)

p = Prop (P 0)
q = Prop (Q 0)

instance Show Form where 
  show Top           = "T" 
  show (Prop p)      = show p
  show (Neg f)       = '-':(show f)
  show (Conj fs)     = '&': show fs
  show (Disj fs)     = 'v': show fs
  show (K e f)       = '[':show e ++"]"++show f 
  show (PA f1 f2)    = '[':'!': show f1  ++"]"++show f2 
  show (PC s f)      = show s ++ show f

instance Show EE where 
  show (Agent a)   = show a 
  show (Test f)    = '?': show f
  show (Cmp e1 e2) = show e1  ++ ";" ++ show e2 
  show (Sum es)    = 'U': show es
  show (Star e)    = '(': show e  ++ ")*" 

ck :: [Agent] -> Form -> Form 
ck ags f = K (Star (Sum [Agent a | a <- ags])) f

apply :: Eq a => [(a,b)] -> a -> b
apply [] _ = error "argument not in list"
apply ((x,z):xs) y | x == y    = z
                   | otherwise = apply xs y

rightS :: Ord a => a -> Rel a -> [a]
rightS x r = (sort.nub) [ z | (y,z) <- r, x == y ]

isTrueAt :: Ord state => EpistM state -> state -> Form -> Bool
isTrueAt m w Top       = True 
isTrueAt m w (Prop p)  = p `elem` (concat 
                         [ ps | (w',ps) <- valuation m, w'==w])
isTrueAt m w (Neg  f)  = not (isTrueAt m w f) 
isTrueAt m w (Conj fs) = and (map (isTrueAt m w) fs)
isTrueAt m w (Disj fs) = or  (map (isTrueAt m w) fs)

isTrueAt m w (K e f)   = and (map (flip (isTrueAt m) f) 
                                  (rightS w (evalEE m e)))

isTrueAt m w (PA f1 f2) = not (isTrueAt m  w f1) 
                          ||   isTrueAt m' w f2 
               where m' = upd_pa m f1 

isTrueAt m w (PC s f) = isTrueAt (upd_pc m s) w f

evalEE :: Ord state => EpistM state -> EE -> Rel state
evalEE m (Agent a)   = rel a m 
evalEE m (Test f)    = [(w,w) | w <- dom m, isTrueAt m w f]
evalEE m (Cmp e1 e2) = (evalEE m e1) @@ (evalEE m e2)
evalEE m (Sum (es))  = (sort.nub) (concat (map (evalEE m) es))
evalEE m (Star e)    = rtc (dom m) (evalEE m e)

test1 = isTrueAt (initM [a..c] [P 0]) 0 
                 (ck [a..c] (Neg (K (Agent a) p)))

isTrue :: Ord state => EpistM state -> Form -> Bool
isTrue m f = and [ isTrueAt m s f | s <- actual m ]

test2 = isTrue (initM [a..c] [P 0]) 
               (ck [a..c] (Neg (K (Agent a) p)))

upd_pa :: Ord state => EpistM state -> Form -> EpistM state
upd_pa m@(Mo states  agents val  rels  actual)  f = 
         (Mo states' agents val' rels' actual') 
   where 
     states' = [  s      |  s      <- states, 
                            isTrueAt m s f    ]
     val'    = [ (s,p)   | (s,p)   <- val, 
                            s `elem` states'  ]
     rels'   = [ (a,x,y) | (a,x,y) <- rels, 
                            x `elem` states',
                            y `elem` states'  ]
     actual' = [  s      |  s      <- actual, 
                            s `elem` states'  ]

type Subst = [(Prop,Form)]

upd_pc :: Ord state => EpistM state -> Subst -> EpistM state
upd_pc m@(Mo worlds agents val  acc points) subst = 
         (Mo worlds agents val' acc points) 
   where 
     val' = [ (w,[p | p <- ps, isTrueAt m w (liftS subst p)]) 
             | w <- worlds ]
     ps   = (sort.nub) (concat (map snd val))
     liftS :: Subst -> Prop -> Form
     liftS []         p             = Prop p 
     liftS ((x,z):xs) y | x == y    = z 
                        | otherwise = liftS xs y 

m0 = initM [a..c] [P 0,Q 0]

convert :: Eq state => EpistM state -> EpistM Integer
convert (Mo states  agents val  rels  actual) = 
         Mo states' agents val' rels' actual'
   where 
     states' = map f states
     val'    = map (\ (x,y)   -> (f x,y))     val
     rels'   = map (\ (x,y,z) -> (x,f y,f z)) rels
     actual' = map f actual
     f       = apply (zip states [0..])

gsm :: Ord state => EpistM state ->  EpistM state
gsm (Mo states  ags val  rel  points) = 
     Mo states' ags val' rel' points
   where 
     states' = closure rel ags points
     val'    = [(s,ps)    | (s,ps)    <- val, 
                             s  `elem` states'  ]
     rel'    = [(ag,s,s') | (ag,s,s') <- rel, 
                             s  `elem` states', 
                             s' `elem` states'  ]

closure ::  Ord state => [(Agent,state,state)] -> 
                         [Agent] -> [state] -> [state]
closure rel agents xs = lfp f xs where
 f = \ ys -> (nub.sort) (ys ++ (expand rel agents ys))

expand :: Ord state => [(Agent,state,state)] -> 
                       [Agent] -> [state] -> [state]
expand rel agents ys = (nub.sort.concat) 
  [ alternatives rel ag state | ag    <- agents, 
                                state <- ys      ]

alternatives :: Eq state => [(Agent,state,state)] -> 
                              Agent -> state -> [state]
alternatives rel ag current = [ s' | (a,s,s') <- rel, 
                                      a == ag, s == current ] 

p1, p2, p3, p4 :: Form 
p1 = Prop (P 1); p2 = Prop (P 2)
p3 = Prop (P 3); p4 = Prop (P 4)

computeAcc :: Agent -> [Integer] -> [Prop] -> [(Integer,[Prop])] 
                    -> [(Agent,Integer,Integer)]
computeAcc ag states props val = 
 [ (ag,x,y) | x <- states, y <- states, 
              apply val x \\ props == apply val y \\ props ]

initMuddy :: EpistM Integer
initMuddy = Mo states 
               [a..d]
               valuation
               (computeAcc a states [P 1] valuation ++
                computeAcc b states [P 2] valuation ++
                computeAcc c states [P 3] valuation ++
                computeAcc d states [P 4] valuation)
               [7]
  where states    = [0..15]
        valuation = zip states (powerList [P 1,P 2,P 3,P 4])

m1 = convert (upd_pa initMuddy (Disj [p1,p2,p3,p4]))

aK =  Disj [K (Agent a) p1, K (Agent a) (Neg p1)]
bK =  Disj [K (Agent b) p2, K (Agent b) (Neg p2)]
cK =  Disj [K (Agent c) p3, K (Agent c) (Neg p3)]
dK =  Disj [K (Agent d) p4, K (Agent d) (Neg p4)]

m2 = convert (upd_pa m1 (Conj [Neg aK,Neg bK,Neg cK,Neg dK]))

m3 = convert (upd_pa m2 (Conj [Neg aK,Neg bK,Neg cK,Neg dK]))

m4 = convert (upd_pa m3 (Conj [Neg aK, bK, cK, dK]))

