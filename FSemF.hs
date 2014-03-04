module FSemF where 

import Data.List
import Data.Char (toUpper)
import FSynF

type Grid = [(Column,Row)]

exampleGrid :: Grid
exampleGrid = [(A',9),
               (B',4),(B',5),(B',6),(B',7),(B',9),
               (C',9),(D',4),(E',4),(F',4),
               (G',4),(G',7),(G',8),(G',9),
               (H',1),(H',4),(I',1)]

attacks :: Grid
attacks = [(F',9),(E',8),(D',7),(C',6)]

battleship, frigate, sub1, sub2, destroyer :: Grid
battleship = [(D',4),(E',4),(F',4),(G',4),(H',4)]
frigate    = [(B',4),(B',5),(B',6),(B',7)]
sub1       = [(A',9),(B',9),(C',9)]
sub2       = [(G',7),(G',8),(G',9)]
destroyer  = [(H',1),(I',1)]

type State = ([Grid],Grid) 

shipsDistrib :: [Grid]
shipsDistrib = [battleship,frigate,sub1,sub2,destroyer]

exampleState = (shipsDistrib,attacks)

noClashes :: State -> Bool
noClashes (distrib,_) = nodups (concat distrib) 
  where nodups []     = True
        nodups (x:xs) = notElem x xs && nodups xs

hit :: Attack -> State -> Bool
hit pos (gs,_) = elem pos (concat gs)

missed :: Attack -> State -> Bool
missed pos = not . (hit pos)

defeated :: State -> Bool
defeated  (gs,g) = all (`elem` g) (concat gs)

updateBattle :: Attack -> State -> State
updateBattle p (gs,g) = (gs, insert p g)

propNames :: Form -> [String]
propNames (P name) = [name]
propNames (Ng f)   = propNames f
propNames (Cnj fs) = (sort.nub.concat) (map propNames fs)
propNames (Dsj fs) = (sort.nub.concat) (map propNames fs)

genVals :: [String] -> [[(String,Bool)]]
genVals [] = [[]]
genVals (name:names) = map ((name,True) :) (genVals names) 
                    ++ map ((name,False):) (genVals names)

allVals :: Form -> [[(String,Bool)]]
allVals = genVals . propNames 

eval :: [(String,Bool)] -> Form -> Bool
eval [] (P c)    = error ("no info about " ++ show c)
eval ((i,b):xs) (P c) 
     | c == i    = b 
     | otherwise = eval xs (P c) 

eval xs (Ng f)   = not (eval xs f)
eval xs (Cnj fs) = all (eval xs) fs
eval xs (Dsj fs) = any (eval xs) fs

tautology :: Form -> Bool
tautology f = all (\ v -> eval v f) (allVals f)

satisfiable :: Form -> Bool
satisfiable f = any (\ v -> eval v f) (allVals f)

contradiction :: Form -> Bool
contradiction = not . satisfiable

implies :: Form -> Form -> Bool
implies f1 f2 = contradiction (Cnj [f1,Ng f2])

update :: [[(String,Bool)]] -> Form -> [[(String,Bool)]]
update vals f = [ v | v <- vals, eval v f ]

samepos :: Pattern -> Pattern -> Int
samepos _      []                 = 0 
samepos []     _                  = 0 
samepos (x:xs) (y:ys) | x == y    = samepos xs ys + 1
                      | otherwise = samepos xs ys 

occurscount ::  Pattern -> Pattern -> Int
occurscount xs []       = 0
occurscount xs (y:ys) 
          | y `elem` xs = occurscount (delete y xs) ys + 1
          | otherwise   = occurscount xs ys 

reaction :: Pattern -> Pattern -> [Answer]
reaction secret guess = take n (repeat Black) 
                     ++ take m (repeat White)
    where n = samepos secret guess 
          m = occurscount secret guess - n 

secret = [Red,Blue,Green,Yellow]

updateMM :: [Pattern] -> Pattern -> Feedback -> [Pattern]
updateMM state guess answer = 
   [ xs | xs <- state, reaction xs guess == answer ]

string2pattern :: String -> Pattern 
string2pattern = convertP . (map toUpper)

convertP :: String -> Pattern
convertP []       = []
convertP (' ':xs) =          convertP xs
convertP ('R':xs) = Red    : convertP xs
convertP ('Y':xs) = Yellow : convertP xs
convertP ('B':xs) = Blue   : convertP xs
convertP ('G':xs) = Green  : convertP xs
convertP ('O':xs) = Orange : convertP xs

playMM :: IO ()
playMM = 
  do 
    putStrLn "Give a sequence of four colours from RGBYO"
    s <- getLine 
    if (string2pattern s) /= secret 
      then 
        let answer = reaction secret (string2pattern s) in 
        do 
          putStrLn (show answer)
          putStrLn "Please make another guess"
          playMM
      else putStrLn "correct"

