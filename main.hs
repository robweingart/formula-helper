import Control.Monad.Writer.Lazy
import Data.Bifunctor
import qualified Data.Map as M
import Data.Maybe
import Data.List

type VarId = String
type PredId = String

data Formula = FTrue
  | FFalse
  | Pred PredId [VarId]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll VarId Formula
  | Exists VarId Formula
  deriving (Eq, Ord)


instance Show Formula where
  show = showFormula . normalize

-- Input must be normalized (all associative operators applied as if left-associative)
showFormula :: Formula -> String
showFormula FTrue = "1"
showFormula FFalse = "0"
showFormula (Pred p []) = p
showFormula (Pred p xs) = p ++ "(" ++ intercalate ", " xs ++ ")"
showFormula (Not x) = "¬" ++ showFormula x
showFormula (And x y) = "(" ++ showNoBrackets (And x y) ++ ")"
showFormula (Or x y) = "(" ++ showNoBrackets (Or x y) ++ ")"
showFormula (Implies x y) = "(" ++ showFormula x ++ " → " ++ showFormula y ++ ")"
showFormula (Iff x y) = "(" ++ showFormula x ++ " ↔ " ++ showFormula y ++ ")"
showFormula (ForAll v x) = "∀" ++ v ++ show x
showFormula (Exists v x) = "∃" ++ v ++ show x

showNoBrackets :: Formula -> String
showNoBrackets (And x (And y z)) = showFormula x ++ " ∧ " ++ showNoBrackets (And y z)
showNoBrackets (And x y) = showFormula x ++ " ∧ " ++ showFormula y
showNoBrackets (Or x (Or y z)) = showFormula x ++ " ∨ " ++ showNoBrackets (Or y z)
showNoBrackets (Or x y) = showFormula x ++ " ∨ " ++ showFormula y

normalize :: Formula -> Formula
normalize (Not x) = Not (normalize x)
normalize (And (And x y) z) = And (normalize x) (normalize (And y z))
normalize (And x y) = And (normalize x) (normalize y)
normalize (Or (Or x y) z) = Or (normalize x) (normalize (Or y z))
normalize (Or x y) = Or (normalize x) (normalize y)
normalize (Implies x y) = Implies (normalize x) (normalize y)
normalize (Iff x y) = Iff (normalize x) (normalize y)
normalize (ForAll v x) = ForAll v (normalize x)
normalize (Exists v x) = Exists v (normalize x)
normalize x = x

mapWorking :: (Formula -> Formula) -> Writer [Formula] Formula -> Writer [Formula] Formula
mapWorking f = mapWriter (second (map f))

withWorking1 :: (Formula -> Formula) -> (Formula -> Writer [Formula] Formula) -> Formula -> Writer [Formula] Formula
withWorking1 f eval x = do
  tell [f x]
  withWorkingSkip1 f eval x

withWorkingSkip1 :: (Formula -> Formula) -> (Formula -> Writer [Formula] Formula) -> Formula -> Writer [Formula] Formula
withWorkingSkip1 f eval x = do
  ex <- mapWorking f (eval x)
  return (f ex)

withWorking2 :: (Formula -> Formula -> Formula) -> (Formula -> Writer [Formula] Formula) -> Formula -> Formula -> Writer [Formula] Formula
withWorking2 f eval x y = do
  tell [f x y]
  withWorkingSkip2 f eval x y

withWorkingSkip2 :: (Formula -> Formula -> Formula) -> (Formula -> Writer [Formula] Formula) -> Formula -> Formula -> Writer [Formula] Formula
withWorkingSkip2 f eval x y = do
  ex <- mapWorking (`f` y) (eval x)
  ey <- mapWorking (f ex) (eval y)
  return (f ex ey)

-- Removes Implies and Iff
expandArrows :: Formula -> Writer [Formula] Formula
expandArrows p@(Implies x y) = do
  tell [p]
  expandArrows (Or (Not x) y)
expandArrows p@(Iff x y) = do
  tell [p]
  expandArrows (And (Implies x y) (Implies y x))
expandArrows (Not x) = withWorking1 Not expandArrows x
expandArrows (And x y) = withWorking2 And expandArrows x y
expandArrows (Or x y) = withWorking2 Or expandArrows x y
expandArrows x = return x

-- Input must be quantifier-free
toNNF :: Formula -> Writer [Formula] Formula
toNNF (Not (Not x)) = withWorking1 id toNNF x
toNNF (Not (And x y)) = withWorking2 Or toNNF (Not x) (Not y)
toNNF (Not (Or x y)) = withWorking2 And toNNF (Not x) (Not y)
toNNF (Not p@(Implies _ _)) = withWorking1 Not expandArrows p >>= toNNF
toNNF (Not p@(Iff _ _)) = withWorking1 Not expandArrows p >>= toNNF
toNNF (And x y) = withWorkingSkip2 And toNNF x y
toNNF (Or x y) = withWorkingSkip2 Or toNNF x y
toNNF p@(Implies _ _) = expandArrows p >>= toNNF
toNNF p@(Iff _ _) = expandArrows p >>= toNNF
toNNF x = return x

-- Input must be in PNF
toCNF :: Formula -> Writer [Formula] Formula
toCNF (ForAll v x) = withWorking1 (ForAll v) toCNF x
toCNF (Exists v x) = withWorking1 (Exists v) toCNF x
toCNF p = toNNF p >>= toCNF'

toCNF' :: Formula -> Writer [Formula] Formula
toCNF' (Or (And x y) z) = withWorking2 And toCNF' (Or x z) (Or y z)
toCNF' (Or x (And y z)) = withWorking2 And toCNF' (Or x y) (Or x z)
toCNF' (Not x) = withWorkingSkip1 Not toCNF' x
toCNF' (And x y) = withWorkingSkip2 And toCNF' x y
toCNF' (Or x y) = withWorkingSkip2 Or toCNF' x y
toCNF' x = return x


type SubFs = M.Map Formula String

rep :: SubFs -> Formula -> Formula
rep _ FTrue = FTrue
rep _ FFalse = FFalse
rep _ (Pred s []) = Pred s []
rep subfs x = Pred ("p_" ++ name) []
  where
    name = fromMaybe "ERROR" (M.lookup x subfs)

subformulae :: Formula -> SubFs
subformulae = subformulae' M.empty

subformulae' :: SubFs -> Formula -> SubFs
subformulae' subfs FTrue = subfs
subformulae' subfs FFalse = subfs
subformulae' subfs (Pred s []) = subfs
subformulae' subfs p@(Not x) = subfs' `M.union` subfsX
  where
    subfs' = sfAdd p subfs
    subfsX = subformulae' subfs' x
subformulae' subfs p@(And x y) = subfs' `M.union` subfsX `M.union` subfsY
  where
    subfs' = sfAdd p subfs
    subfsX = subformulae' subfs' x
    subfsY = subformulae' subfsX y
subformulae' subfs p@(Or x y) = subfs' `M.union` subfsX `M.union` subfsY
  where
    subfs' = sfAdd p subfs
    subfsX = subformulae' subfs' x
    subfsY = subformulae' subfsX y
subformulae' subfs p@(Implies x y) = subfs' `M.union` subfsX `M.union` subfsY
  where
    subfs' = sfAdd p subfs
    subfsX = subformulae' subfs' x
    subfsY = subformulae' subfsX y
subformulae' subfs p@(Iff x y) = subfs' `M.union` subfsX `M.union` subfsY
  where
    subfs' = sfAdd p subfs
    subfsX = subformulae' subfs' x
    subfsY = subformulae' subfsX y

sfAdd :: Formula -> SubFs -> SubFs
sfAdd x subfs = M.insert x (show (M.size subfs)) subfs

tseitin :: Formula -> Writer [Formula] Formula
tseitin x = do
  tell parts
  tell [x']
  toCNF x'
  where
    subfs = subformulae x
    parts = tseitinParts subfs x
    x' = foldl And (rep subfs x) parts

tseitinParts :: SubFs -> Formula -> [Formula]
tseitinParts subfs x = map (tseitinPart subfs) (M.keys subfs)
    

tseitinPart :: SubFs -> Formula -> Formula
tseitinPart subfs p@(Not x) = Iff (rep subfs p) (Not (rep subfs x)) 
tseitinPart subfs p@(And x y) = Iff (rep subfs p) (And (rep subfs x) (rep subfs y)) 
tseitinPart subfs p@(Or x y) = Iff (rep subfs p) (Or (rep subfs x) (rep subfs y)) 
tseitinPart subfs p@(Implies x y) = Iff (rep subfs p) (Implies (rep subfs x) (rep subfs y)) 
tseitinPart subfs p@(Iff x y) = Iff (rep subfs p) (Iff (rep subfs x) (rep subfs y)) 

rename :: Formula -> Formula
rename = id -- TODO

toPNF :: Formula -> Writer [Formula] Formula
toPNF = toPNF' . rename

toPNF' :: Formula -> Writer [Formula] Formula
toPNF' FTrue = return FTrue
toPNF' FFalse = return FFalse
toPNF' p@(Pred s xs) = return p
toPNF' (Not (Not f)) = withWorking1 id toPNF' f
toPNF' (Not f) = withWorking1 Not toPNF' f >>= toPNFStep
toPNF' (And x y) = withWorking2 And toPNF' x y >>= toPNFStep
toPNF' (Or x y) = withWorking2 Or toPNF' x y >>= toPNFStep
toPNF' p@(Implies _ _) = expandArrows p >>= toPNF'
toPNF' p@(Iff _ _) = expandArrows p >>= toPNF'
toPNF' (ForAll v f) = withWorkingSkip1 (ForAll v) toPNF' f
toPNF' (Exists v f) = withWorkingSkip1 (Exists v) toPNF' f

-- Everything except the outer layer must already be in PNF
toPNFStep :: Formula -> Writer [Formula] Formula
toPNFStep (Not (ForAll p f)) = withWorking1 (Exists p) toPNF' (Not f)
toPNFStep (Not (Exists p f)) = withWorking1 (ForAll p) toPNF' (Not f)
toPNFStep (And (ForAll v x) y) = withWorking1 (ForAll v) toPNFStep (And x y)
toPNFStep (And (Exists v x) y) = withWorking1 (Exists v) toPNFStep (And x y)
toPNFStep (And x (ForAll v y)) = withWorking1 (ForAll v) toPNFStep (And x y)
toPNFStep (And x (Exists v y)) = withWorking1 (Exists v) toPNFStep (And x y)
toPNFStep (Or (ForAll v x) y) = withWorking1 (ForAll v) toPNFStep (Or x y)
toPNFStep (Or (Exists v x) y) = withWorking1 (Exists v) toPNFStep (Or x y)
toPNFStep (Or x (ForAll v y)) = withWorking1 (ForAll v) toPNFStep (Or x y)
toPNFStep (Or x (Exists v y)) = withWorking1 (Exists v) toPNFStep (Or x y)
toPNFStep f = return f

toCPNF :: Formula -> Writer [Formula] Formula
toCPNF f = toPNF f >>= toCNF

printWorking :: Writer [Formula] Formula -> IO ()
printWorking w = mapM_ print $ dedup (working ++ [res])
  where
    (res, working) = runWriter w

dedup :: Eq a => [a] -> [a]
dedup [] = []
dedup [x] = [x]
dedup (x : y : ys)
  | x == y    = dedup (y : ys)
  | otherwise = x : dedup (y : ys)
