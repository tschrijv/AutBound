{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
import System.Random
import Criterion.Main
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
import Control.Exception (evaluate)
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

genMultipleRandom :: Int->Int->IO([[Int]])
genMultipleRandom 0 _ = return []
genMultipleRandom nbLists lengthlist = do 
            newrand1<-evaluate (replicate 5 2)
            newrand2<-evaluate (replicate lengthlist 2)
            newrest <- genMultipleRandom (nbLists-2) lengthlist
            return (newrand1 :(newrand2: newrest ))


genTmAbs :: Term -> Int -> Term
genTmAbs t 0 = t 
genTmAbs t n = TmAbs (genTmAbs t (n-1) )



generateTerms1 :: [Int]->Term 
generateTerms1 [1] =  TmTrue
generateTerms1 [2] = TmVar (generateHnatTermVar 1 Z)
generateTerms1 [3] = TmTrue
--generateTerms (1:rest) = TmAbs (generateTerms rest)
generateTerms1 (_:rest) = TmIf (generateTerms1 rest) (generateTerms1 rest) (generateTerms1 rest)
--generateTerms (3:rest) = TmApp (TmAbs (generateTerms rest )) (generateTerms rest)



generateTerms :: [Int]->Term 
generateTerms [1] =  TmTrue
generateTerms [2] = TmVar (generateHnatTermVar 100 Z)
generateTerms [3] = TmTrue
--generateTerms (1:rest) = TmAbs (generateTerms rest)
generateTerms (_:rest) = TmIf (generateTerms rest) (generateTerms rest) (generateTerms rest)
--generateTerms (3:rest) = TmApp (TmAbs (generateTerms rest )) (generateTerms rest)

--genBenchesTerms :: [[Int]] ->[Term]
genBenchesTerms [] = []
genBenchesTerms (ints:ints2:rest) = ( (generateTerms1 ints) :( genTmAbs (generateTerms ints2) 100 )  : genBenchesTerms rest)

genBenchesTermsIO [] = return []
genBenchesTermsIO (ints:rest) = do 
                newrest <- genBenchesTermsIO rest
                return (generateTerms ints : newrest)

genBenches [] _= return []
genBenches (term1: (term2 :rest)) nb= do 
               restbench<- genBenches rest (nb+1)
               return ( (bench (show nb)  $ nf (termtermSubstitute (term1 ) Z) (term2))  : restbench)

main = do 
    result1<- ( genMultipleRandom 10 5)  
    result2<- ( genMultipleRandom 10 7) 
    result3<- ( genMultipleRandom 10 9)  
    benches <- (genBenches (genBenchesTerms ( result1++result2++result3)) 0)
    finalres<- defaultMain [  bgroup "testTerms"  benches ]
    return finalres