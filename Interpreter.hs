
{--
How pairs work.

Pairs are used in order to implement linked lists. The first element of a pair must be either an Int or a Bool,
but the second element may be another pair which may have a pair as its second element as well.

If lists/pairs are used as the args for a function, they must both have the same number of elements.
If they do, the function performs its work on elements of each list in the same position and returns a
list/pair as a result.
--}


data Expr= N Int | Add Expr Expr | Mul Expr Expr | Sub Expr Expr
	   | And Expr Expr | Or Expr Expr |Not Expr |If Expr Expr Expr |Equal Expr Expr
	   | Lam Type String Expr | App Expr Expr | Var String |P (Expr,Expr)
	   | B Bool
           deriving(Show,Eq)

data Type = TNum |TBool |TFunc Type Type -- |TPair Type Type |TList Type
		deriving (Show, Eq)

data Val = VB Bool | VP (Val, Val) |
			VN Int | VLam Expr  deriving (Show, Eq)

{-
	typecheck ::Expr                  ->Type
				suspicious expression ->type it returns
	Makes sure an expression uses types correctly and either returns 
	a value of a single type or  returns an error.
-}			
typecheck ::Expr->Type
typecheck (N _)=TNum
typecheck (B _)=TBool
typecheck (Add a b)= if typecheck a==TNum && typecheck b==TNum then TNum else error "typecheck failure in add."
typecheck (Mul a b)= if typecheck a==TNum && typecheck b==TNum then TNum else error "typecheck failure in mul."
typecheck (Sub a b)= if typecheck a==TNum && typecheck b==TNum then TNum else error "typecheck failure in sub."
typecheck (Or a b)= if typecheck a==TBool && typecheck b==TBool then TBool else error "typecheck failure in or."
typecheck (And a b)= if typecheck a==TBool && typecheck b==TBool then TBool else error "typecheck failure in and."
typecheck (Not a)= if typecheck a==TBool then TBool else error "typecheck failure in not."
typecheck (If a b c)= if typecheck a==TBool && typecheck b==typecheck c then typecheck c else error "typecheck failure in if."
typecheck (Equal a b)= if typecheck a==typecheck b then TBool else error "typecheck failure in equal."
typecheck (App a b)= case typecheck a of
					(TFunc from to)->if(typecheck b==from) then to else error "typecheck failure in app."
					_ -> error "This line should never print."
typecheck (Lam t s b)= TFunc t (typecheck(subst s (dummyVal t) b))
typecheck something = error $"Can't typecheck "++show something

{-
	dummyVal ::Type       ->Expr
			   typeDesired->expr of that type
	Used by typecheck when evaluating lambdas. 
	Given a type, returns a member of that type that can be substituted in.
-}
dummyVal ::Type->Expr
dummyVal(TNum)=(N 1)
dummyVal(TBool)=(B True)
dummyVal(TFunc a b)= (Lam a "x" (dummyVal b))


exec ::Expr ->Val
exec(a)=case (typecheck a) of
		(TNum) -> (eval a)
		(TBool) -> (eval a)
		(TFunc _ _) -> (eval a)
{-
subst :: String -> Expr  ->      Expr
           var     replacement   thingToSubThrough Done 
-}
subst :: String -> Expr  -> Expr -> Expr
subst str rep body =case body of
			(N a)->body
			(B a)->body
			--(P (arg1,arg2))->P((subst str rep arg1),(subst str rep arg2))
			(Var st)->if(st==str) then rep else (Var st)
			(Add arg1 arg2)->Add (subst str rep arg1)(subst str rep arg2)
			(Mul arg1 arg2)->Mul (subst str rep arg1)(subst str rep arg2)
			(Sub arg1 arg2)->Sub (subst str rep arg1)(subst str rep arg2)
			(And arg1 arg2)->And (subst str rep arg1)(subst str rep arg2)
			(Or arg1 arg2)->Or (subst str rep arg1)(subst str rep arg2)
			(Not arg1)->Not (subst str rep arg1)
			(If arg1 arg2 arg3)->If (subst str rep arg1)(subst str rep arg2)(subst str rep arg3)
			(Equal arg1 arg2)->Equal(subst str rep arg1)(subst str rep arg2)
			(Lam t st b)-> Lam t st (subst str rep b)
			(App arg1 arg2)->App (subst str rep arg1)(subst str rep arg2)
			something ->error $ "Invalid args for substitution." ++show something
{-
	eval ::Expr  ->Val
		   input ->result
-}
eval :: Expr -> Val
eval (Mul a b) = case(eval a,eval b) of
					(VN x, VN y) -> VN(x*y)
					--(VP( VN c,VN d),VP( VN e,VN f))->VP(VN(c*e),VN(d*f))
					--(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c*e),eval(Mul (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Invalid args for multiplication."
				   
				   
                             
--Addition
eval (Add a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n + m)
					--((VP( VN c,VN d),VP( VN e,VN f)))->(VP(VN(c+e),VN(d+f)))
					--(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c+e),eval(Add (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error $ "Invalid args for addition."

eval (Lam t str body)=VLam (Lam t str body)
			
eval (App lam var) = case (lam) of
					(Lam t str body)-> eval $ subst str var body
					_ -> error "Invalid args for application."
			
eval (Var param) = error "Can't evaluate variables."
			
eval (Sub a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n - m)
					--(VP( VN c,VN d),VP( VN e,VN f))->VP(VN(c-e),VN(d-f))
					--(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c-e),eval(Sub (makeExpr (VP d)) (makeExpr (VP f))))
					something -> error $ "Subtraction needs two numbers. We have "++ show something++"."

eval(If condition thenCase elseCase)=case (eval(condition)) of
					(VB True)->eval(thenCase)
					(VB False)->eval(elseCase)
					_-> error "Invalid args for if."


--Simple Number
eval (N a) = VN a

--Boolean Functions
eval(B b)=VB b

eval(And a b) = case (eval a, eval b) of
					(VB x, VB y) -> VB (x && y)
					--(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c&&e),VB(d&&f))
					--(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c&&e),eval(And (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for and."

eval(Or a b)=case (eval a, eval b) of
					(VB x, VB y) -> VB (x|| y)
					--(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c||e),VB(d||f))
					--(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c||e),eval(Or (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for or."

eval(Not a)=case (eval a) of
				(VB x) -> VB (not(x))
				--(VP( VB c,VB d))->VP(VB(not(c)),VB(not(d)))
				--(VP( VB c,VP d))->VP(VB(not(c)),eval(Not(makeExpr (VP d))))
				_ -> error "Inappropriate arguments for not."

eval(Equal a b)=case (eval a, eval b) of
					(VN x, VN y) -> VB (x==y)
					--(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c&&e),VB(d&&f))
					--(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c&&e),eval(And (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for equals."

{-
	makeExpr :: Val   ->Expr
				result->input
	Inverts eval.

-}
					
					
makeExpr :: Val -> Expr 
makeExpr(VB a)=(B a)
makeExpr(VN a)=(N a)
makeExpr(VP (a,b))=P(makeExpr a,makeExpr b)
makeExpr(VLam (Lam t str body))=Lam t str body

--Num tests
n1 = Mul (Add(N 2)(N 3))(N 4)
n2 = Add (N 2)  (Mul (N 3) (N 4))
n3 = Sub (N 10)(N 9)
n4 = N 123

--Pair tests\
{-
p1 = Mul (P((N 2),(N 2))) (Mul (P((N 3),(N 4))) (P((N 3),(N 4))))
p1A= VP(VN 18,VN 32)
p2 = Or(P((B True),(B False)))(P((B False),(B False)))
p2A= VP(VB True, VB False)
-}
--Bool tests

b1= And (B True) (B True)
b2= And (B False) (B False)
b3= Or b1 (B False)
b4= Or (B False) (B False)
b5= Or(B True)(B False)
b6= And(B True)(B False)
b7= Or(B False)(B False)
b8= And(B True)(B True)
b9= Not (B True)
b10=Not (B False)
b11=Equal(N 5)(N 5)
b12=Equal(N 5)(N 6)

--Eval Func tests
f1 = Lam (TNum)"x" (Mul (N 5)(Var "x"))
f1A=VLam(Lam (TNum)"x" (Mul (N 5)(Var "x")))
f2 = App f1 (N 1)
f3 = Lam (TNum)"x" (Mul (N 5)(Var "y"))
f3A= VLam(Lam (TNum)"x" (Mul (N 5)(Var "y")))
f4 = App f3 (N 1)--Generates exception.
f5 = Lam (TNum)"y" (App (Lam (TNum) "x" (Mul (Var "x")(Var "y")))(Var "y"))
f5A = VLam(Lam (TNum) "y" (App (Lam (TNum)"x" (Mul (Var "x")(Var "y")))(Var "y")))
f6 = App f5 (N 5)

--Subst tests
s1Q=subst ("x")(N 5) (Lam (TNum)"y"(Mul (Var  "x")(Var "y")))
s1A=(Lam (TNum)"y"(Mul (N 5)(Var "y")))
s2Q=subst ("x")(N 5) (Lam (TNum)"y"(Mul (Var  "z")(Var "y")))
s2A=(Lam (TNum)"y"(Mul (Var  "z")(Var "y")))
s3Q=subst ("x")(N 5) (Lam (TNum)"y"(Sub (Var  "z")(Var "y")))
s3A=(Lam (TNum)"y"(Sub (Var  "z")(Var "y")))
s4Q=subst ("x")(N 5) ((Mul (Var  "x")(Var "x")))
s4A=((Mul (N 5)(N 5)))
s5Q=subst ("y")(N 12) (If (Equal (N 5)(Var "y"))(Mul (Var "y")(Var "y"))(Add (Var "y")(Var "y")))
s5A = If(Equal (N 5)(N 12))(Mul (N 12)(N 12))(Add (N 12)(N 12))
--s6Q= subst ("x")(N 4) (Mul (P((N 2),Var "x")) (Mul (P(Var "x",(N 4))) (P((N 3),Var "x"))))
--s6A= Mul (P (N 2,N 4)) (Mul (P (N 4,N 4))(P(N 3,N 4)))
--s6Evaled=VP(VN 24,VN 64)

--Type tests that succeed.
t1 = Lam TBool "x" (If (Var "x")(N 5)(N 6))
t2 = App t1 (B True)
t3 = Lam TNum "y" (Lam TBool "x" (If (Var "x")(Var "y")(N 6)))

--Expressions that return a value but fail typechecking.
maybe1 = If(B True)(N 4)(B True)

--Type tests that fail.
fail1 = If(N 5)(N 4)(N 3)
fail2 = And (N 5)(B True)

-- tests paired with their expected answers
numTests = [(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123)]-- ,(s4A,VN 25),(s5A,VN 24),(s6A,s6Evaled)]

--pairTests=[(p1,p1A),(p2,p2A)]

boolTests=[(b1,VB True),(b2,VB False),(b3,VB True),(b4,VB False)
			,(b5,VB True),(b6,VB False),(b7,VB False),(b8,VB True)
			,(b9,VB False),(b10,VB True),(b11,VB True),(b12,VB False)]
			
funcTests=[(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
			,(f6,VN 25)]
		
subTests=[(s1Q,s1A),(s2Q,s2A),(s3Q,s3A),(s4Q,s4A),(s5Q,s5A)]--,(s6Q,s6A)]

typeTests=[ (n1,TNum),(n2,TNum),(n3,TNum),(n4,TNum),(b1,TBool),
			(b2,TBool),(b3,TBool),(b4,TBool),(b5,TBool),(b6,TBool),
			(b7,TBool),(b8,TBool),(b9,TBool),(b10,TBool),(b11,TBool),
			(b12,TBool),(f1,TFunc TNum TNum),(f2,TNum),(t1,TFunc TBool TNum),
			(t2,TNum),(t3,TFunc TNum (TFunc TBool TNum))]

-- are tests paired up with their actual results?
test_results = map (\(t,v)-> (eval t)==v) numTests
--pairTestResults = map (\(t,v)-> (eval t)==v) pairTests
boolTestResults = map (\(t,v)-> (eval t)==v) boolTests
funcTestResults = map (\(t,v)-> (eval t)==v) funcTests
subTestResults = map (\(t,v)-> t==v) subTests
typeTestResults = map (\(t,v)-> (typecheck t)==v) typeTests

-- were all tests okay?
okay = (and test_results)&&(and boolTestResults)  &&  (and subTestResults)  &&  (and funcTestResults)  && (and typeTestResults)