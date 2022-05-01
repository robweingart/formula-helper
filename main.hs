import Control.Monad.Writer.Lazy
import Data.Bifunctor
import qualified Data.Map as M
import Data.Maybe

data Formula = FTrue | FFalse | Var String | Not Formula | And Formula Formula | Or Formula Formula | Implies Formula Formula | Iff Formula Formula
  deriving (Eq, Ord)

instance Show Formula where
  show FTrue = "1"
  show FFalse = "0"
  show (Var s) = s
  show (Not x@(And _ _)) = "¬(" ++ show x ++ ")"
  show (Not x@(Or _ _)) = "¬(" ++ show x ++ ")"
  show (Not x) = "¬" ++ show x
  show (And x@(Or _ _) y@(Or _ _)) = "(" ++ show x ++ ") ∧ (" ++ show y ++ ")"
  show (And x@(Or _ _) y) = "(" ++ show x ++ ") ∧ " ++ show y
  show (And x y@(Or _ _)) = show x ++ " ∧ (" ++ show y ++ ")"
  show (And x y) = show x ++ " ∧ " ++ show y
  show (Or x@(And _ _) y@(And _ _)) = "(" ++ show x ++ ") ∨ (" ++ show y ++ ")"
  show (Or x@(And _ _) y) = "(" ++ show x ++ ") ∨ " ++ show y
  show (Or x y@(And _ _)) = show x ++ " ∨ (" ++ show y ++ ")"
  show (Or x y) = show x ++ " ∨ " ++ show y
  show (Implies x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
  show (Iff x y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"

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

toCNF :: Formula -> Writer [Formula] Formula
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
rep _ (Var s) = Var s
rep subfs x = Var ("p_" ++ name)
  where
    name = fromMaybe "ERROR" (M.lookup x subfs)

subformulae :: Formula -> SubFs
subformulae = subformulae' M.empty

subformulae' :: SubFs -> Formula -> SubFs
subformulae' subfs FTrue = subfs
subformulae' subfs FFalse = subfs
subformulae' subfs (Var s) = subfs
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
