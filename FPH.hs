module FPH

where 

import Data.List
import Data.Char

square :: Int -> Int
square x = x * x

hword :: String -> Bool
hword []     = False 
hword (x:xs) = (x == 'h') || (hword xs)

gen :: Int -> String 
gen 0 = "Sentences can go on" 
gen n = gen (n-1) ++ " and on"

genS :: Int -> String 
genS n = gen n ++ "."

story :: Int -> String
story 0 = 
 "Let's cook and eat that final missionary, and off to bed."
story k = 
 "The night was pitch dark, mysterious and deep.\n"
 ++ "Ten cannibals were seated around a boiling cauldron.\n"
 ++ "Their leader got up and addressed them like this:\n'"
 ++ story (k-1) ++ "'"

reversal :: String -> String 
reversal []    = []
reversal (x:t) = reversal t ++ [x]

sonnet18 = 
 "Shall I compare thee to a summer's day? \n"
 ++ "Thou art more lovely and more temperate: \n"
 ++ "Rough winds do shake the darling buds of May, \n"
 ++ "And summer's lease hath all too short a date: \n"
 ++ "Sometime too hot the eye of heaven shines, \n"
 ++ "And often is his gold complexion dimm'd; \n"
 ++ "And every fair from fair sometime declines, \n"
 ++ "By chance or nature's changing course untrimm'd; \n"
 ++ "But thy eternal summer shall not fade \n"
 ++ "Nor lose possession of that fair thou owest; \n"
 ++ "Nor shall Death brag thou wander'st in his shade, \n"
 ++ "When in eternal lines to time thou growest: \n"
 ++ "  So long as men can breathe or eyes can see, \n"
 ++ "  So long lives this and this gives life to thee."

sonnet73 =
 "That time of year thou mayst in me behold\n"
 ++ "When yellow leaves, or none, or few, do hang\n"
 ++ "Upon those boughs which shake against the cold,\n"
 ++ "Bare ruin'd choirs, where late the sweet birds sang.\n"
 ++ "In me thou seest the twilight of such day\n"
 ++ "As after sunset fadeth in the west,\n"
 ++ "Which by and by black night doth take away,\n"
 ++ "Death's second self, that seals up all in rest.\n"
 ++ "In me thou see'st the glowing of such fire\n"
 ++ "That on the ashes of his youth doth lie,\n"
 ++ "As the death-bed whereon it must expire\n"
 ++ "Consumed with that which it was nourish'd by.\n"
 ++ "This thou perceivest, which makes thy love more strong,\n"
 ++ "To love that well which thou must leave ere long."

count :: Eq a => a -> [a] -> Int
count x []                 = 0 
count x (y:ys) | x == y    = succ (count x ys) 
               | otherwise = count x ys 

average :: [Int] -> Rational 
average [] = error "empty list" 
average xs = toRational (sum xs) / toRational (length xs)

prefix :: Eq a => [a] -> [a] -> Bool
prefix []     ys     = True
prefix (x:xs) []     = False
prefix (x:xs) (y:ys) = (x==y) && prefix xs ys 

preprocess :: String -> String 
preprocess = (map toLower) . filter (`notElem` "?;:,.")

process :: String -> [String]
process = sort . nub . words

cnt :: String -> [(String,Int)]
cnt sonnet = [ (x,n)| x <- (process.preprocess) sonnet, 
                 n <- [count x (words (preprocess sonnet))], 
                 n > 1                             ]

aUml,oUml :: Char
aUml = chr(228) 
oUml = chr(246)

appendSuffixF :: String -> String -> String
appendSuffixF stem suffix = stem ++ map vh suffix
 where vh | or [elem c "aou"           | c <- stem] = back
          | or [elem c [aUml,oUml,'y'] | c <- stem] = front
          | otherwise                               = id

front :: Char -> Char
front s | s == 'a'  = aUml
        | s == 'o'  = oUml
        | s == 'u'  = 'y'
        | otherwise = s

back :: Char -> Char
back s  | s == aUml  = 'a'
        | s == oUml  = 'o'
        | s == 'y'   = 'u'
        | otherwise  = s

data DeclClass = One | Two | Three | Four | Five 

oSlash,aRing :: Char
oSlash = chr(248) 
aRing  = chr(229)

swedishVowels = ['a','i','o','u','e','y',aUml,aRing,oUml,oSlash]

swedishPlural :: String -> DeclClass -> String
swedishPlural noun d = case d of 
  One   -> init noun ++ "or"
  Two   -> init noun ++ "ar"
  Three -> if  (last noun) `elem` swedishVowels
           then noun ++ "r"
           else noun ++ "er"
  Four  -> noun ++ "n"
  Five  -> noun

data Subject   = Chomsky | Montague deriving Show
data Predicate = Wrote String       deriving Show

data Sentence  = S Subject Predicate 

type Sentences = [Sentence]

instance Show Sentence where
  show (S subj pred) = show subj ++ " " ++ show pred

makeP :: String -> Predicate
makeP title = Wrote title

makeS :: Subject -> Predicate -> Sentence
makeS subj pred = S subj pred

myLast        :: [a] -> a
myLast [x]    =  x
myLast (_:xs) =  myLast xs
myLast  _     =  error "myLast: empty list"

data Colour = RGB Int Int Int deriving Show

showColour :: Colour -> String
showColour (RGB 0 0 0)       = "black"
showColour (RGB 255 255 255) = "white"
showColour (RGB 255 0 0)     = "red"
showColour (RGB 0 255 0)     = "green"
showColour (RGB 0 0 255)     = "blue"

showColour (RGB 255 255 0)   = "yellow"
showColour (RGB 0 255 255)   = "cyan"
showColour (RGB 255 0 255)   = "magenta"
showColour c                 = show c 

redAlert  :: Colour -> String
redAlert c@(RGB r _ _) = case r of 
   0 -> show c ++ " has no red"
   _ -> show c ++ " has red"

data Feature = F Attr Value deriving (Eq,Show)

data Attr    = Back | High | Round | Cons deriving (Eq,Show)
data Value   = Plus | Minus               deriving (Eq,Show)

type Phoneme = [Feature]

yawelmaniVowels = [i,a,o,u,e]

i = [F Cons Minus,  F High Plus,  
     F Round Minus, F Back Minus]
a = [F Cons Minus,  F High Minus, 
     F Round Minus, F Back Plus ]
o = [F Cons Minus,  F High Minus, 
     F Round Plus,  F Back Plus ]
u = [F Cons Minus,  F High Plus , 
     F Round Plus,  F Back Plus ]
e = [F Cons Minus,  F High Minus, 
     F Round Minus, F Back Minus]

c = [F Cons Plus]

realize :: Phoneme -> Char
realize x | x == i = 'i'
          | x == a = 'a'
          | x == o = 'o'
          | x == u = 'u'
          | x == e = 'e'
          | x == c = 'c'

fValue :: Attr -> Phoneme -> Value
fValue attr [] = error "feature not found"
fValue attr ((F a v):fs) | attr == a = v
                         | otherwise = fValue attr fs

fMatch :: Attr -> Value -> Phoneme -> Phoneme
fMatch attr value fs = map (match attr value) fs
   where match a v f@(F a' v') | a == a'   = F a' v
                               | otherwise = f

