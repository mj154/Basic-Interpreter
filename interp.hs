{-# LANGUAGE GADTs #-}

-- import Control.Monad

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Enviornment for statically scoped eval

type Env = [(String,FBAEVal)]

-- substitution
substitute :: String -> FBAE -> FBAE -> FBAE
substitute i v (Num x) = (Num x)

substitute i v (Plus l r) =
  (Plus (substitute i v l)(substitute i v r))

substitute i v (Minus l r) =
  (Minus (substitute i v l)(substitute i v r))

substitute i v (Mult l r) =
  (Mult (substitute i v l)(substitute i v r))

substitute i v (Div l r) =
  (Div (substitute i v l)(substitute i v r))

substitute i v (Bind i' v' b') =
  if i==i' then (Bind i' (substitute i v v') b')
  else (Bind i' (substitute i v v')(substitute i v b'))

substitute i v (Lambda i' t' b') =
  (Lambda i' t' (substitute i v b'))

substitute i v (App f a) =
  (App (substitute i v f) (substitute i v a))

substitute i v (Id i') =
  if i' == i then v
  else (Id i')

substitute i v (Boolean b) = (Boolean b)

substitute i v (And l r) = (And (substitute i v l)(substitute i v r))

substitute i v (Or l r) = (Or (substitute i v l)(substitute i v r))

substitute i v (Leq l r) = (Leq (substitute i v l)(substitute i v r))

substitute i v (IsZero x) = IsZero(substitute i v x)

substitute i v (If c t e) = (If (substitute i v c)(substitute i v t)(substitute i v e))

substitute i v (Fix f) = Fix (substitute i v f)








-- Statically scoped eval
         
evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM e (Num x) = Just (NumV x)

evalM e (Plus l r) = do {
  (NumV l') <- (evalM e l);
  (NumV r') <- (evalM e r);
  return (NumV (l'+r'))
}

evalM e (Minus l r) = do {
  (NumV l') <- (evalM e l);
  (NumV r') <- (evalM e r);
  return (NumV (l'-r'))
}

evalM e (Mult l r) = do {
  (NumV l') <- (evalM e l);
  (NumV r') <- (evalM e r);
  return (NumV (l'*r'))
}

evalM e (Div l r) = do {
  (NumV l') <- (evalM e l);
  (NumV r') <- (evalM e r);
  return (NumV (l' `div` r'))
}

evalM e (Bind i v b) = do {
  v' <- (evalM e v);
  evalM ((i,v'):e) b
}

evalM e (Lambda i t b) = Just (ClosureV i b e)

evalM e (App f a) = do {
  (ClosureV i b e') <- (evalM e f);
  a' <- (evalM e a);
  (evalM ((i,a'):e') b)
}

evalM e (Id i) = (lookup i e)
evalM e (Boolean b) = Just (BooleanV b)
evalM e (And l r) = do {
  (BooleanV l') <- (evalM e l);
  (BooleanV r') <- (evalM e r);
  return (BooleanV (l'&&r'))
}

evalM e (Or l r) = do {
  (BooleanV l') <- (evalM e l);
  (BooleanV r') <- (evalM e r);
  return (BooleanV (l'||r'))
}

evalM e (Leq l r) = do {
  (NumV l') <- (evalM e l);
  (NumV r') <- (evalM e r);
  return (BooleanV (l'<=r'))
}

evalM e (IsZero i) = do {
  (NumV i') <- (evalM e i);
  return (BooleanV (i'==0))
}

evalM e (If c t e') = do {
  (BooleanV c') <- (evalM e c);
  if c' then(evalM e t)
  else (evalM e e')
}

evalM e (Fix f) = do {
  (ClosureV i b e') <- (evalM e f);
  t <- Just TNum;
  (evalM e' (substitute i (Fix (Lambda i t b)) b))
}

-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM c (Num n) = Just TNum
typeofM c (Boolean b) = Just TBool

typeofM c (Plus l r) = do {
  TNum <- (typeofM c l);
  TNum <- (typeofM c r);
  return TNum
}


typeofM c (Minus l r) = do {
  TNum <- (typeofM c l);
  TNum <- (typeofM c r);
  return TNum
}

typeofM c (Mult l r) = do {
  TNum <- (typeofM c l);
  TNum <- (typeofM c r);
  return TNum
}

typeofM c (Div l r) = do {
  TNum <- (typeofM c l);
  TNum <- (typeofM c r);
  return TNum
}

typeofM c (And l r) = do {
  TBool <- (typeofM c l);
  TBool <- (typeofM c r);
  return TBool
}

typeofM c (Or l r) = do {
  TBool <- (typeofM c l);
  TBool <- (typeofM c r);
  return TBool
}


typeofM c (Leq l r) = do {
  TNum <- (typeofM c l);
  TNum <- (typeofM c r);
  return TBool
}

typeofM c (IsZero i) = do {
  TNum <- (typeofM c i);
  return TBool
}

typeofM c (If c' t e) = do {
  TBool <- (typeofM c c');
  t' <- (typeofM c t);
  e' <- (typeofM c e);
  if e' == t' then return t'
  else Nothing
}

typeofM c (Bind i v b) = do {
  v' <- (typeofM c v);
  (typeofM ((i,v'):c)b)
}

typeofM c (Lambda i t b) = do {
  t' <- (typeofM ((i,t):c)b);
  return (t:->:t')
}

typeofM c (App f a) = do {
  a' <- (typeofM c a);
  (d:->:r) <- (typeofM c f);
  if a' == d then return r
  else Nothing
}

typeofM c (Id i) = lookup i c

typeofM c (Fix f) = do {
  (d:->:r) <- (typeofM c f);
  return r
}

-- Interpreter

interp :: FBAE -> (Maybe FBAEVal)
interp f =
  let e = [] in
    do {
      typeofM e f;
      evalM e f
    }

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).

test1 = (Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x")
                                                           (Num 1)))))))
         (App (Fix (Id "f")) (Num 3)))


run_test = do
  putStrLn $ show $ interp test1