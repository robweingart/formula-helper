{-# LANGUAGE FlexibleContexts #-}

import Control.Monad.Writer
import Control.Monad.State
import Data.Bifunctor
import qualified Data.Map as M
import Data.Maybe
import Data.List

type VarId = String
type PredId = String
type FuncId = String

data Val = Func VarId [Val]
  deriving (Eq, Ord)

data Formula = FTrue
  | FFalse
  | Pred PredId [Val]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll VarId Formula
  | Exists VarId Formula
  deriving (Eq, Ord)

instance Show Val where
  show (Func s []) = s
  show (Func f xs) = f ++ "(" ++ intercalate ", " (map show xs) ++ ")"


instance Show Formula where
  show = showFormula . normalize

-- Input must be normalized (all associative operators applied as if left-associative)
showFormula :: Formula -> String
showFormula FTrue = "1"
showFormula FFalse = "0"
showFormula (Pred p []) = p
showFormula (Pred p xs) = p ++ "(" ++ intercalate ", " (map show xs) ++ ")"
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

mapWorking :: MonadWriter [Formula] m => (Formula -> Formula) -> m Formula -> m Formula
mapWorking = censor . map

work1 :: MonadWriter [Formula] m => (Formula -> Formula) -> (Formula -> m Formula) -> Formula -> m Formula
work1 f eval x = do
  step (f x)
  wrap f (eval x)

step :: MonadWriter [Formula] m => Formula -> m ()
step x = tell [x]

(<:>) :: MonadWriter [Formula] m => Formula -> m Formula -> m Formula
(<:>) x y = do
  tell [x]
  y

wrap :: MonadWriter [Formula] m => (Formula -> Formula) -> m Formula -> m Formula
wrap f x = do
  ex <- mapWorking f x
  return (f ex)

work2 :: MonadWriter [Formula] m => (Formula -> Formula -> Formula) -> (Formula -> m Formula) -> Formula -> Formula -> m Formula
work2 f eval x y = do
  step (f x y)
  wrap2 f eval x y

wrap2 :: MonadWriter [Formula] m => (Formula -> Formula -> Formula) -> (Formula -> m Formula) -> Formula -> Formula -> m Formula
wrap2 f eval x y = do
  ex <- mapWorking (`f` y) (eval x)
  ey <- mapWorking (f ex) (eval y)
  return (f ex ey)

-- Removes Implies and Iff
expandArrows :: MonadWriter [Formula] m => Formula -> m Formula
expandArrows p@(Implies x y) = do
  tell [p]
  expandArrows (Or (Not x) y)
expandArrows p@(Iff x y) = do
  tell [p]
  expandArrows (And (Implies x y) (Implies y x))
expandArrows (Not x) = work1 Not expandArrows x
expandArrows (And x y) = work2 And expandArrows x y
expandArrows (Or x y) = work2 Or expandArrows x y
expandArrows x = return x

-- Input must be quantifier-free
toNNF :: Formula -> Writer [Formula] Formula
toNNF p@(Not (Not x)) = toNNF x
toNNF (Not (And x y)) = work2 Or toNNF (Not x) (Not y)
toNNF (Not (Or x y)) = work2 And toNNF (Not x) (Not y)
toNNF (Not p@(Implies _ _)) = work1 Not expandArrows p >>= toNNF
toNNF (Not p@(Iff _ _)) = work1 Not expandArrows p >>= toNNF
toNNF (And x y) = wrap2 And toNNF x y
toNNF (Or x y) = wrap2 Or toNNF x y
toNNF p@(Implies _ _) = expandArrows p >>= toNNF
toNNF p@(Iff _ _) = expandArrows p >>= toNNF
toNNF x = return x

-- Input must be in PNF
toCNF :: Formula -> Writer [Formula] Formula
toCNF (ForAll v x) = work1 (ForAll v) toCNF x
toCNF (Exists v x) = work1 (Exists v) toCNF x
toCNF p = toNNF p >>= toCNF'

toCNF' :: Formula -> Writer [Formula] Formula
toCNF' (Or (And x y) z) = work2 And toCNF' (Or x z) (Or y z)
toCNF' (Or x (And y z)) = work2 And toCNF' (Or x y) (Or x z)
toCNF' (Not x) = wrap Not (toCNF' x)
toCNF' (And x y) = wrap2 And toCNF' x y
toCNF' (Or x y) = wrap2 Or toCNF' x y
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
rename f = evalState (rename' M.empty f) M.empty

type Counts = M.Map VarId Int

rename' :: M.Map VarId VarId -> Formula -> State Counts Formula
rename' _ FTrue = return FTrue
rename' _ FFalse = return FFalse
rename' bound (Pred p xs) = return $ Pred p (applyRename bound xs)
rename' bound (Not x) = do
  x' <- rename' bound x
  return $ Not x'
rename' bound (And x y) = renameBranch bound And x y
rename' bound (Or x y) = renameBranch bound Or x y
rename' bound (Implies x y) = renameBranch bound Implies x y
rename' bound (Iff x y) = renameBranch bound Iff x y
rename' bound (ForAll v x) = renameQuantifier bound ForAll v x
rename' bound (Exists v x) = renameQuantifier bound Exists v x

renameBranch :: M.Map VarId VarId -> (Formula -> Formula -> Formula) -> Formula -> Formula -> State Counts Formula
renameBranch bound f x y = do
  x' <- rename' bound x
  y' <- rename' bound y
  return $ f x' y'

renameQuantifier :: M.Map VarId VarId -> (VarId -> Formula -> Formula) -> VarId -> Formula -> State Counts Formula
renameQuantifier bound qf v x = do
  uses <- get
  let n = fromMaybe 0 (M.lookup v uses)
  let n' = n + 1
  put (M.insert v n' uses)
  let v' = v ++ show n'
  let bound' = M.insert v v' bound
  x' <- rename' bound' x
  return $ qf v' x'

applyRename :: M.Map VarId VarId -> [Val] -> [Val]
applyRename bound = map (\(Func x []) -> Func (fromMaybe x (M.lookup x bound)) [])

toPNF :: Formula -> Writer [Formula] Formula
toPNF = toPNF' . rename

toPNF' :: Formula -> Writer [Formula] Formula
toPNF' FTrue = return FTrue
toPNF' FFalse = return FFalse
toPNF' p@(Pred s xs) = return p
toPNF' (Not (Not f)) = work1 id toPNF' f
toPNF' (Not f) = work1 Not toPNF' f >>= toPNFStep
toPNF' (And x y) = work2 And toPNF' x y >>= toPNFStep
toPNF' (Or x y) = work2 Or toPNF' x y >>= toPNFStep
toPNF' p@(Implies _ _) = expandArrows p >>= toPNF'
toPNF' p@(Iff _ _) = expandArrows p >>= toPNF'
toPNF' (ForAll v f) = wrap (ForAll v) (toPNF' f)
toPNF' (Exists v f) = wrap (Exists v) (toPNF' f)

-- Everything except the outer layer must already be in PNF
toPNFStep :: Formula -> Writer [Formula] Formula
toPNFStep (Not (ForAll p f)) = work1 (Exists p) toPNF' (Not f)
toPNFStep (Not (Exists p f)) = work1 (ForAll p) toPNF' (Not f)
toPNFStep (And (ForAll v x) y) = work1 (ForAll v) toPNFStep (And x y)
toPNFStep (And (Exists v x) y) = work1 (Exists v) toPNFStep (And x y)
toPNFStep (And x (ForAll v y)) = work1 (ForAll v) toPNFStep (And x y)
toPNFStep (And x (Exists v y)) = work1 (Exists v) toPNFStep (And x y)
toPNFStep (Or (ForAll v x) y) = work1 (ForAll v) toPNFStep (Or x y)
toPNFStep (Or (Exists v x) y) = work1 (Exists v) toPNFStep (Or x y)
toPNFStep (Or x (ForAll v y)) = work1 (ForAll v) toPNFStep (Or x y)
toPNFStep (Or x (Exists v y)) = work1 (Exists v) toPNFStep (Or x y)
toPNFStep f = return f

toCPNF :: Formula -> Writer [Formula] Formula
toCPNF f = toPNF f >>= toCNF

skolemize :: Formula -> Writer [Formula] Formula
skolemize f = do
  f' <- toCPNF f
  return $ evalState (skolemize' [] f') (M.empty, M.empty)

type SkolemState = (M.Map Int Int, M.Map Val Val)

skolemize' :: [Val] -> Formula -> State SkolemState Formula
skolemize' _ FTrue = return FTrue
skolemize' _ FFalse = return FFalse
skolemize' vs p@(Pred _ _) = do
  (_, renames) <- get
  return $ skolemRename vs renames p
skolemize' vs (Not x) = do
  x' <- skolemize' vs x
  return $ Not x'
skolemize' vs (And x y) = skolemizeBranch vs And x y
skolemize' vs (Or x y) = skolemizeBranch vs Or x y
skolemize' vs (Implies x y) = skolemizeBranch vs Implies x y
skolemize' vs (Iff x y) = skolemizeBranch vs Iff x y
skolemize' vs (ForAll v x) = do
  x' <- skolemize' (Func v [] : vs) x
  return $ ForAll v x'
skolemize' vs (Exists v x) = do
  (predNums, renames) <- get
  let m = length vs
  let n = fromMaybe 0 (M.lookup m predNums) + 1
  let i = skolemId m n
  let val = Func i (reverse vs)
  put (M.insert m n predNums, M.insert (Func v []) val renames)
  skolemize' vs x

skolemId :: Int -> Int -> VarId
skolemId m n = "skolem_" ++ show m ++ "ary_" ++ show n

skolemizeBranch :: [Val] -> (Formula -> Formula -> Formula) -> Formula -> Formula -> State SkolemState Formula
skolemizeBranch xs f x y = do
  x' <- skolemize' xs x
  y' <- skolemize' xs y
  return $ f x' y'

skolemRename :: [Val] -> M.Map Val Val -> Formula -> Formula
skolemRename us renames (Pred t xs) = Pred t $ map (skolemRename' us renames) xs

skolemRename' :: [Val] -> M.Map Val Val -> Val -> Val
skolemRename' us renames val = fromMaybe val $ M.lookup val renames

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

var :: String -> Val
var s = Func s []
