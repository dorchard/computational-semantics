module CPSS where

import FSynF
import Model
import MCWPL

mkc :: (a -> b) -> a -> (b -> r) -> r 
mkc f x next = next (f x)

raise :: a -> (a -> r) -> r 
raise x = \ f ->  f x

mkc' ::  (a -> b) -> a -> (b -> r) -> r 
mkc' f x = raise (f x)

type Cont a r = a -> r
type Comp a r = Cont a r -> r

cpsConst :: a -> Comp a r
cpsConst c = \ k -> k c

cpsApply :: Comp (a -> b) r -> Comp a r -> Comp b r
cpsApply m n = \ k -> n (\ b -> m (\ a -> k (a b)))

intSent_CPS :: Sent -> Comp Bool Bool
intSent_CPS (Sent np vp) = 
   cpsApply (intVP_CPS vp) (intNP_CPS np) 

intNP_CPS :: NP -> Comp Entity Bool
intNP_CPS SnowWhite  = cpsConst snowWhite
intNP_CPS Alice      = cpsConst alice
intNP_CPS Dorothy    = cpsConst dorothy
intNP_CPS Goldilocks = cpsConst goldilocks
intNP_CPS LittleMook = cpsConst littleMook
intNP_CPS Atreyu     = cpsConst atreyu

intNP_CPS Everyone = \ k -> all k (filter person entities)
intNP_CPS Someone  = \ k -> any k (filter person entities)

intNP_CPS (NP1 det cn) = (intDET_CPS det) (intCN_CPS cn)

intVP_CPS :: VP -> Comp (Entity -> Bool) Bool
intVP_CPS Laughed     = cpsConst laugh
intVP_CPS Cheered     = cpsConst cheer
intVP_CPS Shuddered   = cpsConst shudder
intVP_CPS (VP1 tv np) = cpsApply (intTV_CPS tv) (intNP_CPS np)

intTV_CPS :: TV -> Comp (Entity -> Entity -> Bool) Bool
intTV_CPS Loved    = cpsConst love
intTV_CPS Admired  = cpsConst admire
intTV_CPS Helped   = cpsConst help
intTV_CPS Defeated = cpsConst defeat

intCN_CPS :: CN -> Comp (Entity -> Bool) Bool
intCN_CPS Girl     = cpsConst girl
intCN_CPS Boy      = cpsConst boy
intCN_CPS Princess = cpsConst princess
intCN_CPS Dwarf    = cpsConst dwarf
intCN_CPS Giant    = cpsConst giant
intCN_CPS Sword    = cpsConst sword
intCN_CPS Dagger   = cpsConst dagger 

intDET_CPS :: DET -> (Comp (Entity -> Bool) Bool) 
                            -> (Comp Entity Bool)
intDET_CPS Some  = \ k p -> k (\ q -> 
                   any p (filter q entities)) 
intDET_CPS Every = \ k p -> k (\ q -> 
                   all p (filter q entities)) 
intDET_CPS No    = \ k p -> k (\ q -> 
                   not (any p (filter q entities)))
intDET_CPS The   = \ k p -> k (\ q -> 
                   singleton (filter q entities) 
                   && p (head (filter q entities)))
                 where
                   singleton [x] = True
                   singleton  _  = False

compSent s = intSent_CPS s id

ex1 = compSent (Sent Everyone Laughed)              
ex2 = compSent (Sent Someone Laughed) 
ex3 = compSent (Sent Everyone (VP1 Admired Goldilocks))
ex4 = compSent (Sent Goldilocks (VP1 Admired Everyone))
ex5 = compSent (Sent Goldilocks (VP1 Admired Someone))
ex6 = compSent (Sent (NP1 Some Boy) Laughed)
ex7 = compSent (Sent (NP1 The Princess) Laughed)

cpsApply' :: Comp (a -> b) r -> Comp a r -> Comp b r
cpsApply' m n = \ k -> m (\ a -> n (\ b -> k (a b)))

example_linearScope = (cpsApply  (cpsApply  
  (intTV_CPS Helped) (intNP_CPS Someone)) 
  (intNP_CPS (NP1 Every Wizard))) id 

example_inverseScope = (cpsApply' (cpsApply' 
  (intTV_CPS Helped) (intNP_CPS Someone)) 
  (intNP_CPS Everyone)) id 

