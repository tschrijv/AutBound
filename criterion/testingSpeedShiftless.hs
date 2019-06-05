{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
import System.Random
import Criterion.Main
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
import           Data.List

data Term
  = TmVar HNat
  | TmAbs Term
  | TmApp Term
          Term
  | TmTrue
  | TmFalse
  | TmIf Term
         Term
         Term
  deriving (Show, Eq,Generic, NFData)

data HNat
  = Z
  | STermVar HNat
  deriving (Show, Eq,Generic, NFData)

plus x1 (STermVar x2) = STermVar (plus x1 x2)
plus Z h              = h
plus h Z              = h

instance Ord HNat where
  compare (STermVar h1) (STermVar h2) = compare h1 h2
  compare Z Z                         = EQ
  compare Z _                         = LT
  compare _ Z                         = GT

minus (STermVar h1) (STermVar h2) = minus h1 h2
minus Z Z = Z
minus Z _ = error " You cannot substract zero with a positive number "
minus result Z = result

data Env
  = Nil
  | ETermVar Env
  deriving (Show, Eq)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = STermVar (generateHnatTermVar (n - 1) c)

termmap :: (HNat -> Term -> Term) -> HNat -> Term -> Term
termmap onTermVar c (TmVar hnat) = onTermVar c (TmVar hnat)
termmap onTermVar c (TmAbs x) = TmAbs (termmap onTermVar (STermVar c) x)
termmap onTermVar c (TmApp t1 t2) =
  TmApp (termmap onTermVar c t1) (termmap onTermVar c t2)
termmap onTermVar c (TmTrue) = TmTrue
termmap onTermVar c (TmFalse) = TmFalse
termmap onTermVar c (TmIf t t2 t3) =
  TmIf (termmap onTermVar c t) (termmap onTermVar c t2) (termmap onTermVar c t3)

termshiftHelpplus d c (TmVar hnat)
  | hnat >= c = TmVar (plus hnat d)
  | otherwise = TmVar hnat

termshiftplus :: HNat -> Term -> Term
termshiftplus d t = termmap (termshiftHelpplus d) Z t

termshiftHelpminus d c (TmVar hnat)
  | hnat >= c = TmVar (minus hnat d)
  | otherwise = TmVar hnat

termshiftminus :: HNat -> Term -> Term
termshiftminus d t = termmap (termshiftHelpminus d) Z t

termSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = termshiftplus c sub
  | otherwise = TmVar hnat

termtermSubstitute :: Term -> HNat -> Term -> Term
termtermSubstitute sub orig t = termmap (termSubstituteHelp sub orig) Z t

freeVariablesTerm :: HNat -> Term -> [HNat]
freeVariablesTerm c (TmVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesTerm c (TmAbs x) = nub ((freeVariablesTerm (STermVar c) x))
freeVariablesTerm c (TmApp t1 t2) =
  nub ((freeVariablesTerm c t1) ++ (freeVariablesTerm c t2))
freeVariablesTerm c (TmTrue) = nub ([])
freeVariablesTerm c (TmFalse) = nub ([])
freeVariablesTerm c (TmIf t t2 t3) =
  nub
    ((freeVariablesTerm c t) ++
     (freeVariablesTerm c t2) ++ (freeVariablesTerm c t3))



--end generated code 


randomList :: Int -> IO([Int])
randomList 0 = return []
randomList n = do
  r  <- randomRIO (1,3)
  rs <- randomList (n-1)
  return (r:rs) 

genMultiple :: Int->Int->[[Int]]
genMultiple 0 _ =  []
genMultiple nbLists lengthlist = (newval: newrest )
            where 
                newval= replicate lengthlist 1
                newrest = genMultiple (nbLists-1) lengthlist

genMultipleRandom :: Int->Int->IO([[Int]])
genMultipleRandom 0 _ = return []
genMultipleRandom nbLists lengthlist = do 
            newrand<-randomList lengthlist
            newrest <- genMultipleRandom (nbLists-1) lengthlist
            return (newrand: newrest )
generateTerms :: [Int]->Term 
generateTerms [1] = TmVar (STermVar Z) 
generateTerms [2] = TmVar Z 
generateTerms [3] = TmVar Z 
--generateTerms (1:rest) = TmAbs (generateTerms rest)
generateTerms (_:rest) = TmIf (generateTerms rest) (generateTerms rest) (generateTerms rest)
--generateTerms (3:rest) = TmApp (TmAbs (generateTerms rest )) (generateTerms rest)

--genBenchesTerms :: [[Int]] ->[Term]
genBenchesTerms [] = []
genBenchesTerms (ints:rest) = (generateTerms ints : genBenchesTerms rest)

genBenchesTermsIO [] = return []
genBenchesTermsIO (ints:rest) = do 
                newrest <- genBenchesTermsIO rest
                return (generateTerms ints : newrest)

genBenches [] _= return []
genBenches (term1:rest) nb= do 
               restbench<- genBenches rest (nb+1)
               return ( (bench (show nb)  $ nf (termshiftplus (generateHnatTermVar 10 Z) ) (term1))  : restbench)

main = do 
    result<-return [replicate i 1 |i <- [3..7]]
    benches <- (genBenches (genBenchesTerms (result)) 0)
    finalres<- defaultMain [  bgroup "testTerms"  benches ]
    return finalres
    
