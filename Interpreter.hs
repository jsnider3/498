
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
	   | Lam Expr | App Expr Expr |P (Expr,Expr)-- | Var String 
	   | B Bool |DeBruijn Int
           deriving(Show,Eq)


data Val = VB Bool | VP (Val, Val) |
			VN Int | VLam Expr  deriving (Show, Eq)

{-
subst :: Int       -> Expr       -> Expr
         Depth     replacement   thingToSubThrough
-}
subst :: Int       -> Expr       -> Expr-> Expr
subst deb rep (N a)=(N a)
subst deb rep (B a)=(B a)
subst deb rep body =case body of
			(P (arg1,arg2))->P((subst deb rep arg1),(subst deb rep arg2))
			(DeBruijn n)->if(n==deb) then rep else (if(n>deb) then(DeBruijn (n-1)) else (DeBruijn n))
			(Add arg1 arg2)->Add (subst deb rep arg1)(subst deb rep arg2)
			(Mul arg1 arg2)->Mul (subst deb rep arg1)(subst deb rep arg2)
			(Sub arg1 arg2)->Sub (subst deb rep arg1)(subst deb rep arg2)
			(And arg1 arg2)->And (subst deb rep arg1)(subst deb rep arg2)
			(Or arg1 arg2)->Or (subst deb rep arg1)(subst deb rep arg2)
			(Not arg1)->Not (subst deb rep arg1)
			(If arg1 arg2 arg3)->If (subst deb rep arg1)(subst deb rep arg2)(subst deb rep arg3)
			(Equal arg1 arg2)->Equal(subst deb rep arg1)(subst deb rep arg2)
			(Lam b)-> Lam (subst (deb+1) rep b )
			(App arg1 arg2)->App (subst deb rep arg1)(subst deb rep arg2)
			_ ->error "Invalid args for substitution."

eval :: Expr -> Val
eval(P (a,b))=VP(eval a, eval b)
--Multiply
eval (Mul a b) = case(eval a,eval b) of
					(VN x, VN y) -> VN(x*y)
					(VP( VN c,VN d),VP( VN e,VN f))->VP(VN(c*e),VN(d*f))
					(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c*e),eval(Mul (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Invalid args for multiplication."

--Addition
eval (Add a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n + m)
					((VP( VN c,VN d),VP( VN e,VN f)))->(VP(VN(c+e),VN(d+f)))
					(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c+e),eval(Add (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error $ "Invalid args for addition."

eval (Lam body)=VLam (Lam body)
			
eval (App lam var) = case (lam) of
					(Lam body)-> eval $ subst 1 var body
					_ -> error "Invalid application body."
			
eval (DeBruijn num) = error "Can't evaluate variables."
			
eval (Sub a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n - m)
					(VP( VN c,VN d),VP( VN e,VN f))->VP(VN(c-e),VN(d-f))
					(VP( VN c,VP d),VP( VN e,VP f))->VP(VN(c-e),eval(Sub (makeExpr (VP d)) (makeExpr (VP f))))
					something -> error $ "Subtraction needs two numbers. We have "++ show something++"."

eval(If condition thenCase elseCase)=case (eval(condition)) of
					(VB True)->eval(thenCase)
					(VB False)->eval(elseCase)
					_-> error "Invalid condition for if."


--Simple Number
eval (N a) = VN a

--Boolean Functions
eval(B b)=VB b

eval(And a b) = if(typecheck a b)
				then case (eval a, eval b) of
					(VB x, VB y) -> VB (x && y)
					(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c&&e),VB(d&&f))
					(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c&&e),eval(And (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for and."

eval(Or a b)=case (eval a, eval b) of
					(VB x, VB y) -> VB (x|| y)
					(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c||e),VB(d||f))
					(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c||e),eval(Or (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for or."

eval(Not a)=case (eval a) of
				(VB x) -> VB (not(x))
				(VP( VB c,VB d))->VP(VB(not(c)),VB(not(d)))
				(VP( VB c,VP d))->VP(VB(not(c)),eval(Not(makeExpr (VP d))))
				_ -> error "Inappropriate arguments for not."

eval(Equal a b)=case (eval a, eval b) of
					(VN x, VN y) -> VB (x==y)
					(VP( VN c,VN d),VP( VN e,VN f))->VP(VB(c==e),VB(d==f))
					(VP( VN c,VP d),VP( VN e,VP f))->VP(VB(c==e),eval(Equal (makeExpr (VP d)) (makeExpr (VP f))))
					(VB x, VB y) -> VB (x==y)
					(VP( VB c,VB d),VP( VB e,VB f))->VP(VB(c==e),VB(d==f))
					(VP( VB c,VP d),VP( VB e,VP f))->VP(VB(c==e),eval(Equal (makeExpr (VP d)) (makeExpr (VP f))))
					_ -> error "Inappropriate arguments for equals."


makeExpr :: Val -> Expr 
makeExpr(VB a)=(B a)
makeExpr(VN a)=(N a)
makeExpr(VP (a,b))=P(makeExpr a,makeExpr b)
makeExpr(VLam (Lam body))=Lam body

--Num tests
t1 = Mul (Add(N 2)(N 3))(N 4)
t2 = Add (N 2)  (Mul (N 3) (N 4))
t3 = Sub (N 10)(N 9)
t4 = N 123

--Pair tests
p1 = Mul (P((N 2),(N 2))) (Mul (P((N 3),(N 4))) (P((N 3),(N 4))))
p1A= VP(VN 18,VN 32)
p2 = Or(P((B True),(B False)))(P((B False),(B False)))
p2A= VP(VB True, VB False)

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
f1 = Lam (Mul (N 5)(DeBruijn 1))
f1A=VLam(Lam (Mul (N 5)(DeBruijn 1)))
f2 = App f1 (N 1)
f3 = Lam (Mul (N 5)(DeBruijn 2))
f3A= VLam(Lam (Mul (N 5)(DeBruijn 2)))
f4 = App f3 (N 1)--Generates exception.
f5 = Lam (App (Lam (Mul (DeBruijn 1)(DeBruijn 2)))(DeBruijn 1))
f5A = VLam(Lam (App (Lam (Mul (DeBruijn 1)(DeBruijn 2)))(DeBruijn 1)))
f6 = App f5 (N 5)
--f7 = (App (Lam (Mul (DeBruijn 1)(DeBruijn 3)))(N 5))
--f7A = (App (Lam (Mul (DeBruijn 1)(DeBruijn 3)))(N 5))


--Subst tests
s1Q=subst (1)(N 5) (Lam (Mul (DeBruijn 1)(DeBruijn 2)))
s1A= (Lam (Mul (DeBruijn 1)(N 5)))
s2Q=subst (4)(N 5) (Lam (Mul (DeBruijn 3)(DeBruijn 2)))
s2A=(Lam (Mul (DeBruijn 3)(DeBruijn 2)))
s3Q=subst (4)(N 5) (Lam (Sub (DeBruijn 3)(DeBruijn 2)))
s3A=(Lam (Sub (DeBruijn 3)(DeBruijn 2)))
s4Q=subst (1)(N 5) ((Mul (DeBruijn 1)(DeBruijn 1)))
s4A=((Mul (N 5)(N 5)))
s5Q=subst (2)(N 12) (If (Equal (N 5)(DeBruijn 2))(Mul (DeBruijn 2)(DeBruijn 2))(Add (DeBruijn 2)(DeBruijn 2)))
s5A = If(Equal (N 5)(N 12))(Mul (N 12)(N 12))(Add (N 12)(N 12))
s6Q= subst (1)(N 4) (Mul (P((N 2),(DeBruijn 1))) (Mul (P((DeBruijn 1),(N 4))) (P((N 3),(DeBruijn 1)))))
s6A= Mul (P (N 2,N 4)) (Mul (P (N 4,N 4))(P(N 3,N 4)))
s6Evaled=VP(VN 24,VN 64)
s7= subst 1 (N 5)(Mul (DeBruijn 1)(DeBruijn 3))
s7A = Mul (N 5)(DeBruijn 2)


-- tests paired with their expected answers
numTests = [(t1,VN 20),(t2,VN 14),(t3,VN 1),(t4,VN 123)]-- ,(s4A,VN 25),(s5A,VN 24),(s6A,s6Evaled)]

pairTests=[(p1,p1A),(p2,p2A)]

boolTests=[(b1,VB True),(b2,VB False),(b3,VB True),(b4,VB False)
			,(b5,VB True),(b6,VB False),(b7,VB False),(b8,VB True)
			,(b9,VB False),(b10,VB True),(b11,VB True),(b12,VB False)]
		
funcTests=[(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
			,(f6,VN 25)]
			
subTests=[(s1Q,s1A),(s2Q,s2A),(s3Q,s3A),(s4Q,s4A),(s5Q,s5A),(s6Q,s6A),(s7,s7A)]

-- are tests paired up with their actual eval results?
numTestResults = map (\(t,v)-> (eval t)==v) numTests
pairTestResults = map (\(t,v)-> (eval t)==v) pairTests
boolTestResults = map (\(t,v)-> (eval t)==v) boolTests
funcTestResults = map (\(t,v)-> (eval t)==v) funcTests
subTestResults = map (\(t,v)-> t==v) subTests

-- were all tests okay?
okay = (and numTestResults)&&(and boolTestResults) && (and funcTestResults) &&(and subTestResults)