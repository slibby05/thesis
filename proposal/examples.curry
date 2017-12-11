
-------------------------------------------------------
-- Partial evaluation
-------------------------------------------------------

-- Partial evaluation is cool, but it's very limited.
-- The basic idea is to take a curry program and evaluate all of the right hand sides of functions.
--
-- Example: suppose we have
square x = x * x
power x n = 
  | n == 1         = x
  | n `mod` 2 == 0 = power (square x) (n `div` 2)
  | otherwise      = x * power x (n-1)

-- if we evaluate this expression with n=4, then we have
-- power x 4 
-- ~> | 4 `mod` 2 == 0 = power (square x) (4 `div` 2)
-- ~> let y = square x in | 2 `mod` 2 == 0 = power (square y) (2 `div` 2)
-- ~> let y = square x in | n == 1 = square y
-- ~> let y = square x in square y
-- resulting in the specialized rule
-- power x 4 = let y = square x in square y

-- This is a really good result, but unfortunately it's not consistent.

-- The first problem is the current partial evaluator only runs on expressions
-- that have been marked by the programmer.
-- so the programmer would have to put
-- PEVAL $ power x 4
-- in the program in order to get this result.
-- I'm not sure if this is a limitation of partial evaluation in general,
-- but it is a limit of the current curry partial evaluator.

-- The next, and more serious, problem is that partial evaluation is still evaluation.
-- This means that a partial evaluator cannot produce an optimized program if it can't compute part of it.
-- Consider the following example
complicatedMapInc :: (Int -> Int) -> Int -> Int
complicatedMapInc f x = f (x + ((2 + 3) `div` 5))


-- We don't know what the function f does, but it's clear that (2+3) `div` 5 should be reduced to 1
-- So we should be able to reduce this to
-- simpleMapInc f x = f (x+1)
-- Unfortunately a partial evaluator can't discover this, 
-- because we don't even know if the argument to f is needed.
--
-- In fact this is true whenever there is an unknown function application,
-- or whenever the partial evaluator can't evaluate a function application.
catalan n
 | n == 1         = 1
 | n `mod` 2 == 0 = catalan (n `div` 2)
 | otherwise      = catalan (3*n+1)
oddProduct n = foldl (*) (catalan n) [1..n]

-- In this case we need to evaluate catalan, but the partial evaluator can't determine that it will halt
-- So we can't optimize anything about the fold expression.

------------------------------------------------------------------------------------
-- Haskell optimizations
------------------------------------------------------------------------------------

-- Unfortunately I don't have a lot of information about the haskell optimizations in kics2 yet.
-- Right now kics2 itself does some analysis, but doesn't make non-trivial optimizations based on this
-- analysis.
-- 

-- I suspect that the following program will not be optimized by the haskell compiler, but I'm not entirely sure

sumOn n = (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10) / (n ? failed)

--Clearly this expression should be optimized to
--sumOn n = 55/n

--However, program contains a non-deterministic statement
--This statement is only in part of the expression, but the rest of the expression is marked as
--non-deterministic by the curry compiler.
--Since non-determinism is represented by a Tree in kics2, the ghc cannot optimize it.
--Furthermore ghc is going to have a hard time optimizing any deterministic subexpressions
--because they will all look non-deterministic.

--if kics2 were to evaluate (n ? failed) it could determine that the expression is actually deterministic
--Then ghc could optimize a lot, but this never happens


-- UPDATE: I finally figured out how to get the generated llvm or asm code from ghc inside kics
-- after doing this, I've determined that ghc is not able to optimize any expression with non-determinism
-- so the ability to optimize non-deterministic expression would be a huge benifit.
-- Even if we can only optimize deterministic subexpressions.

{- for reference here's the above expression compiled to haskell with kics2

nd_C_sumOn :: forall t0 . (Curry_Prelude.Curry
  t0) => Curry_Prelude.OP_uscore_Dict_hash_Fractional t0 -> t0 -> IDSupply
  -> Cover -> ConstStore -> t0
nd_C_sumOn x1 x2 s cd cs = let s137 = s
  in s137 `seq` (let s136 = leftSupply s137
                     s138 = rightSupply s137
                     s133 = leftSupply s138
                     s135 = rightSupply s138
  in s136 `seq` (s138 `seq` (s133 `seq` (s135 `seq` Curry_Prelude.nd_C_apply
  (let s132 = leftSupply s133
       s134 = rightSupply s133
       s0 = leftSupply s134
       s130 = rightSupply s134
  in s132 `seq` (s134 `seq` (s0 `seq` (s130 `seq` Curry_Prelude.nd_C_apply
  (Curry_Prelude.nd_OP_slash x1 s0 cd cs) (let s129 = leftSupply s130
                                               s131 = rightSupply s130
                                               s122 = leftSupply s131
                                               s128 = rightSupply s131
  in s129 `seq` (s131 `seq` (s122 `seq` (s128 `seq` Curry_Prelude.nd_C_apply
  (let s121 = leftSupply s122
       s123 = rightSupply s122
       s3 = leftSupply s123
       s119 = rightSupply s123
  in s121 `seq` (s123 `seq` (s3 `seq` (s119 `seq` Curry_Prelude.nd_C_apply
  (let s2 = leftSupply s3
       s1 = rightSupply s3
  in s2 `seq` (s1 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s1 cd cs) s2 cd cs)) (let s118 = leftSupply s119
                               s120 = rightSupply s119
                               s111 = leftSupply s120
                               s117 = rightSupply s120
  in s118 `seq` (s120 `seq` (s111 `seq` (s117 `seq` Curry_Prelude.nd_C_apply
  (let s110 = leftSupply s111
       s112 = rightSupply s111
       s6 = leftSupply s112
       s108 = rightSupply s112
  in s110 `seq` (s112 `seq` (s6 `seq` (s108 `seq` Curry_Prelude.nd_C_apply
  (let s5 = leftSupply s6
       s4 = rightSupply s6
  in s5 `seq` (s4 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s4 cd cs) s5 cd cs)) (let s107 = leftSupply s108
                               s109 = rightSupply s108
                               s100 = leftSupply s109
                               s106 = rightSupply s109
  in s107 `seq` (s109 `seq` (s100 `seq` (s106 `seq` Curry_Prelude.nd_C_apply
  (let s99 = leftSupply s100
       s101 = rightSupply s100
       s9 = leftSupply s101
       s97 = rightSupply s101
  in s99 `seq` (s101 `seq` (s9 `seq` (s97 `seq` Curry_Prelude.nd_C_apply
  (let s8 = leftSupply s9
       s7 = rightSupply s9
  in s8 `seq` (s7 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s7 cd cs) s8 cd cs)) (let s96 = leftSupply s97
                               s98 = rightSupply s97
                               s89 = leftSupply s98
                               s95 = rightSupply s98
  in s96 `seq` (s98 `seq` (s89 `seq` (s95 `seq` Curry_Prelude.nd_C_apply
  (let s88 = leftSupply s89
       s90 = rightSupply s89
       s12 = leftSupply s90
       s86 = rightSupply s90
  in s88 `seq` (s90 `seq` (s12 `seq` (s86 `seq` Curry_Prelude.nd_C_apply
  (let s11 = leftSupply s12
       s10 = rightSupply s12
  in s11 `seq` (s10 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s10 cd cs) s11 cd cs)) (let s85 = leftSupply s86
                                 s87 = rightSupply s86
                                 s78 = leftSupply s87
                                 s84 = rightSupply s87
  in s85 `seq` (s87 `seq` (s78 `seq` (s84 `seq` Curry_Prelude.nd_C_apply
  (let s77 = leftSupply s78
       s79 = rightSupply s78
       s15 = leftSupply s79
       s75 = rightSupply s79
  in s77 `seq` (s79 `seq` (s15 `seq` (s75 `seq` Curry_Prelude.nd_C_apply
  (let s14 = leftSupply s15
       s13 = rightSupply s15
  in s14 `seq` (s13 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s13 cd cs) s14 cd cs)) (let s74 = leftSupply s75
                                 s76 = rightSupply s75
                                 s67 = leftSupply s76
                                 s73 = rightSupply s76
  in s74 `seq` (s76 `seq` (s67 `seq` (s73 `seq` Curry_Prelude.nd_C_apply
  (let s66 = leftSupply s67
       s68 = rightSupply s67
       s18 = leftSupply s68
       s64 = rightSupply s68
  in s66 `seq` (s68 `seq` (s18 `seq` (s64 `seq` Curry_Prelude.nd_C_apply
  (let s17 = leftSupply s18
       s16 = rightSupply s18
  in s17 `seq` (s16 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s16 cd cs) s17 cd cs)) (let s63 = leftSupply s64
                                 s65 = rightSupply s64
                                 s56 = leftSupply s65
                                 s62 = rightSupply s65
  in s63 `seq` (s65 `seq` (s56 `seq` (s62 `seq` Curry_Prelude.nd_C_apply
  (let s55 = leftSupply s56
       s57 = rightSupply s56
       s21 = leftSupply s57
       s53 = rightSupply s57
  in s55 `seq` (s57 `seq` (s21 `seq` (s53 `seq` Curry_Prelude.nd_C_apply
  (let s20 = leftSupply s21
       s19 = rightSupply s21
  in s20 `seq` (s19 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s19 cd cs) s20 cd cs)) (let s52 = leftSupply s53
                                 s54 = rightSupply s53
                                 s45 = leftSupply s54
                                 s51 = rightSupply s54
  in s52 `seq` (s54 `seq` (s45 `seq` (s51 `seq` Curry_Prelude.nd_C_apply
  (let s44 = leftSupply s45
       s46 = rightSupply s45
       s24 = leftSupply s46
       s42 = rightSupply s46
  in s44 `seq` (s46 `seq` (s24 `seq` (s42 `seq` Curry_Prelude.nd_C_apply
  (let s23 = leftSupply s24
       s22 = rightSupply s24
  in s23 `seq` (s22 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s22 cd cs) s23 cd cs)) (let s41 = leftSupply s42
                                 s43 = rightSupply s42
                                 s34 = leftSupply s43
                                 s40 = rightSupply s43
  in s41 `seq` (s43 `seq` (s34 `seq` (s40 `seq` Curry_Prelude.nd_C_apply
  (let s33 = leftSupply s34
       s35 = rightSupply s34
       s27 = leftSupply s35
       s32 = rightSupply s35
  in s33 `seq` (s35 `seq` (s27 `seq` (s32 `seq` Curry_Prelude.nd_C_apply
  (let s26 = leftSupply s27
       s25 = rightSupply s27
  in s26 `seq` (s25 `seq` Curry_Prelude.nd_OP_plus
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s25 cd cs) s26 cd cs)) (let s31 = leftSupply s32
                                 s30 = rightSupply s32
  in s31 `seq` (s30 `seq` Curry_Prelude.nd_C_apply (let s29 = leftSupply s30
                                                        s28 = rightSupply s30
  in s29 `seq` (s28 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s28 cd cs) s29 cd cs)) (Curry_Prelude.C_Int (1)) s31 cd cs)) s33 cd cs))))
  (let s39 = leftSupply s40
       s38 = rightSupply s40
  in s39 `seq` (s38 `seq` Curry_Prelude.nd_C_apply (let s37 = leftSupply s38
                                                        s36 = rightSupply s38
  in s37 `seq` (s36 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s36 cd cs) s37 cd cs)) (Curry_Prelude.C_Int (2)) s39 cd cs)) s41 cd cs))))
  s44 cd cs)))) (let s50 = leftSupply s51
                     s49 = rightSupply s51
  in s50 `seq` (s49 `seq` Curry_Prelude.nd_C_apply (let s48 = leftSupply s49
                                                        s47 = rightSupply s49
  in s48 `seq` (s47 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s47 cd cs) s48 cd cs)) (Curry_Prelude.C_Int (3)) s50 cd cs)) s52 cd cs))))
  s55 cd cs)))) (let s61 = leftSupply s62
                     s60 = rightSupply s62
  in s61 `seq` (s60 `seq` Curry_Prelude.nd_C_apply (let s59 = leftSupply s60
                                                        s58 = rightSupply s60
  in s59 `seq` (s58 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s58 cd cs) s59 cd cs)) (Curry_Prelude.C_Int (4)) s61 cd cs)) s63 cd cs))))
  s66 cd cs)))) (let s72 = leftSupply s73
                     s71 = rightSupply s73
  in s72 `seq` (s71 `seq` Curry_Prelude.nd_C_apply (let s70 = leftSupply s71
                                                        s69 = rightSupply s71
  in s70 `seq` (s69 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s69 cd cs) s70 cd cs)) (Curry_Prelude.C_Int (5)) s72 cd cs)) s74 cd cs))))
  s77 cd cs)))) (let s83 = leftSupply s84
                     s82 = rightSupply s84
  in s83 `seq` (s82 `seq` Curry_Prelude.nd_C_apply (let s81 = leftSupply s82
                                                        s80 = rightSupply s82
  in s81 `seq` (s80 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s80 cd cs) s81 cd cs)) (Curry_Prelude.C_Int (6)) s83 cd cs)) s85 cd cs))))
  s88 cd cs)))) (let s94 = leftSupply s95
                     s93 = rightSupply s95
  in s94 `seq` (s93 `seq` Curry_Prelude.nd_C_apply (let s92 = leftSupply s93
                                                        s91 = rightSupply s93
  in s92 `seq` (s91 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s91 cd cs) s92 cd cs)) (Curry_Prelude.C_Int (7)) s94 cd cs)) s96 cd cs))))
  s99 cd cs)))) (let s105 = leftSupply s106
                     s104 = rightSupply s106
  in s105 `seq` (s104 `seq` Curry_Prelude.nd_C_apply (let s103 = leftSupply s104
                                                          s102 = rightSupply
                                                            s104
  in s103 `seq` (s102 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s102 cd cs) s103 cd cs)) (Curry_Prelude.C_Int (8)) s105 cd cs)) s107 cd
  cs)))) s110 cd cs)))) (let s116 = leftSupply s117
                             s115 = rightSupply s117
  in s116 `seq` (s115 `seq` Curry_Prelude.nd_C_apply (let s114 = leftSupply s115
                                                          s113 = rightSupply
                                                            s115
  in s114 `seq` (s113 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s113 cd cs) s114 cd cs)) (Curry_Prelude.C_Int (9)) s116 cd cs)) s118 cd
  cs)))) s121 cd cs)))) (let s127 = leftSupply s128
                             s126 = rightSupply s128
  in s127 `seq` (s126 `seq` Curry_Prelude.nd_C_apply (let s125 = leftSupply s126
                                                          s124 = rightSupply
                                                            s126
  in s125 `seq` (s124 `seq` Curry_Prelude.nd_C_fromInteger
  (Curry_Prelude.nd_OP_uscore_super_hash_Prelude_dot_Fractional_hash_Prelude_dot_Num
  x1 s124 cd cs) s125 cd cs)) (Curry_Prelude.C_Int (10)) s127 cd cs)) s129 cd
  cs)))) s132 cd cs)))) (Curry_Prelude.nd_OP_qmark x2 (Curry_Prelude.d_C_failed
  cd cs) s135 cd cs) s136 cd cs))))

-}
