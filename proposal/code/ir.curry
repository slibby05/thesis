-- This is a basic A-Normal form for Curry
-- All expressions must be trivial

-- That means function calls must evaluate have fully evaluated arguments
-- Note: This isn't the same as eager evaluation.
-- If I have f (4 + 2)
-- then that will be converted to
-- let x = 4 + 2 in f x
-- x is still a thunk, so if f never uses it, then x is never evaluated

-- I tried to base this on the Icurry definition, but I needed to change it to use trivial expressions
-- There are a few questions I still have

-- should or force it's arguments to be atoms?
-- the implementation is really easy
-- every or expression is x = a ? b
-- where a and b are literals or variables
-- this makes failure propogation trivial
--
-- on the other hand ? kind of behaves like a control flow structure
-- so it might be a better idea to seperate it out entirely
-- This would probably give better results for backtracking compilers

-- should I have both Or and free variables?
-- They're technically both equivalent, but there might be some optimizations
-- that work better with one form or another, and I'm not sure if keeping them
-- seperate is worth it.

-- changing this to IName or QName doesn't change anything.
data Name = String

data Expr
  = Exempt             -- failure
  | Atom Atom          -- return a literal or a variable
  | Apply Name [Atom]  -- tail call function application
  | Part Name Atom     -- return a partial application
  | ApplyCon Name Atom -- return a value (constructor application must be fully applied, otherwise it's a Part)
  | LetAp   (Name, Atom, [Atom]) Expr --function applicaton
  | LetPart (Name, Atom, [Atom]) Expr --partial application
  | LetCon  (Name, Atom, [Atom]) Expr --Constructor application
  | LetOr   (Name, Atom, Atom)   Expr --let x = y ? z in expr
  | letFree [Name] Expr               --let x,y,z free in expr
  | Case Atom [BranchExpr]  -- It's debatible weather or not the argument to a case should be an expression or an atom

data Atom
  = Var Name
  | Lit Literal
  | Reference Int  -- from Icurry, but I think this is just a variable


