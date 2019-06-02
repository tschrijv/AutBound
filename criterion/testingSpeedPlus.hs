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
  | ETermVar  Env
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
  | hnat == plus orig c = termshiftplus orig sub
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
                
generateTerms :: [Int]->HNat 
generateTerms [_] = Z
--generateTerms (1:rest) = TmAbs (generateTerms rest)
generateTerms (_:rest) = STermVar (generateTerms rest)
--generateTerms (3:rest) = TmApp (TmAbs (generateTerms rest )) (generateTerms rest)

genBenchesTerms :: [[Int]] ->[HNat]
genBenchesTerms [] = []
genBenchesTerms (ints:rest) = (generateTerms ints : (genBenchesTerms rest))

genBenchesTermsIO [] = return []
genBenchesTermsIO (ints:rest) = do 
                newrest <- genBenchesTermsIO rest
                return (generateTerms ints : newrest)
--genBenches :: [HNat]-> Int-> [Benchmark]
genBenches [] _=  []
genBenches (hnat: rest) nb= ( (bench (show nb)  $ nf (plus (STermVar Z) ) (hnat) )  : (genBenches rest (nb+1)))

main = (     defaultMain [  bgroup "testTerms"  (result) ])
        where 
            bench1= generateHnatTermVar 100 Z
            bench2= generateHnatTermVar 1000 Z
            bench3= generateHnatTermVar 10000 Z
            bench4=  generateHnatTermVar 100000 Z
            result=genBenches(bench1:bench2:bench3:bench4  : []) 0