--DEBUG THe way I'm using fix right now, it's not passing variables correctly.
{-TODO Typecheck | eval
TL/TR     Done   | Done
Case      Done   | Done
As        Done   | Done
Fix       Done   | Done

-}
--For Pairs and Lists, Add, Mul, Sub, And, Or, and Not are done by performing the op on each element and building pairs/lists from the result.
	--For Equals on the other hand the result is true if and only if every element is the same as the corresponding element or false.
--Lists of length 0 are disallowed by the typechecker.

data Expr= N Int | Add Expr Expr | Mul Expr Expr | Sub Expr Expr
	   | And Expr Expr | Or Expr Expr |Not Expr |If Expr Expr Expr |Equal Expr Expr
	   | Lam Type String Expr | App Expr Expr | Var String |Tuple[Expr]
	   | B Bool |List Expr Expr 
	   |Null --Null is the Unit Type
	   |Concat Expr Expr |Get Expr Expr |Head Expr |Rest Expr
	   |Record [(String,Expr)] |GetRec String Expr 
	   |Fix Expr|LetN[(String,Expr)] Expr | Func String 
	   |TL Expr| TR Expr| Case Expr Expr Expr |As Expr Type 
           deriving(Show,Eq)
		   
data Type = TNum |TBool | Type :-> Type  |TTuple [Type] |TList Type Int |TRecord |TNull |TSum Type Type
		deriving (Show, Eq)

data Val = VB Bool | VTuple [Val] | VList Val Val |VNull | VL Val |VR Val|
			VN Int | VLam Expr |VRecord [(String,Expr)] deriving (Show, Eq) --There's no VApp because applications can always be reduced further.

{-
	typecheck ::Expr                  ->Type
				suspicious expression ->type it returns
	Makes sure an expression uses types correctly and either returns 
	a value of a single type or  returns an error.
-}			
typecheck ::Expr->[(String,Type)]->Type
typecheck (N _)env=TNum
typecheck (B _)env=TBool
typecheck (Null)env=TNull
typecheck (Add a b)env= if typecheck a env==typecheck b env&&simplifyType(typecheck b env)==TNum  then typecheck a env else error $"Invalid arguments for add. We have "++show (a,b)++"."
typecheck (Mul a b)env= if typecheck a env==typecheck b env &&simplifyType(typecheck b env)==TNum  then typecheck a env else error $"Invalid arguments for mul. We have "++show (a,b)++"."
typecheck (Sub a b)env= if typecheck a env==typecheck b env &&simplifyType(typecheck b env)==TNum  then typecheck a env else error $"Invalid arguments for sub. We have "++show (a,b)++"."
typecheck (Or  a b)env= if typecheck a env==typecheck b env &&simplifyType(typecheck b env)==TBool then typecheck a env else error $"Invalid arguments for or.  We have "++show (a,b)++"."
typecheck (And a b)env= if typecheck a env==typecheck b env &&simplifyType(typecheck b env)==TBool then typecheck a env else error $"Invalid arguments for and. We have "++show (a,b)++"."
typecheck (If a b c)env= if typecheck a env==TBool 
						then if typecheck b env ==typecheck c env 
								then typecheck c env
								else error "Then/Else must be same type in if."
						else error "Conditions for if must be boolean type"
typecheck (Not a)env= if simplifyType(typecheck a env)==TBool then typecheck a env else error $"Typecheck failure for not. We have "++show a++"."
typecheck (Tuple a)env = TTuple (zipWith typecheck a (replicate (length a)env))
typecheck (Equal _ _)env= TBool
typecheck (App lam var)env= case typecheck lam env of
					(from :-> to)->if(typecheck var env==from) then to else error "Input to a lambda is of inappropriate type."
					_ -> error "Application is done to a non-lambda."
typecheck (Lam t s b)env= t :-> (typecheck b ((s,t):env))
typecheck (Concat a b)env=case (typecheck a env,typecheck b env) of
							(TList type1 alen,TList type2 blen) ->if type1==type2 then TList type1 (alen+blen) else error "Can't concat lists of different types."
							_ -> error "Can't concat non-lists."
typecheck (Get index list)env=case(typecheck index env,typecheck list env) of
							(TNum,TList type1 _)-> type1
							_ -> error "Get requires a list to work with."
typecheck (Head a)env=case(typecheck a env) of
						(TTuple (head:_))-> head
						(TList type1 _)->type1
						_ -> error "Head only works on pairs and lists."
typecheck (Rest a)env=case(typecheck a env) of
						(TTuple [_,rest])->rest
						(TList listType len)->case (a) of
									(List _ Null) ->TNull --I'm not sure if I should return null if they try to call rest on the end of the list or crash.
									(List _ _) -> TList listType (len-1)
						_ -> error "Rest only works on pairs and lists."
typecheck (List head rest)env=case (typecheck head env) of
							(TNull) -> error "Lists cannot be headed by null."
							(TList _ _)-> error "Lists cannot be headed by lists."
							(goodType)->case (typecheck rest env) of
										(TNull)->(TList goodType 1)
										(TList goodtype len)->(TList goodtype (len+1))
										(goodtype)-> error "List was terminated inappropriately."
										_ -> error "Lists cannot be mixed type."
typecheck (Fix (Lam t s b))env= (typecheck (Lam t s b)env):->(typecheck (Lam t s b)env)
typecheck (Fix something)env=error$"Typecheck for fix failed. The body is "++show something++"."
typecheck (Var st) env = lookupType st env
typecheck (TL a) env = typecheck a env
typecheck (TR b) env = typecheck b env
typecheck (As expr ty) env = case (expr,ty) of
								(TL a,TSum left right)->if(typecheck a env==left) then if(left==right) then error "Sums must be two different types." else TSum left right else error"Typecheck of as failed."
								(TR b,TSum left right)->if(typecheck b env==right)then if(left==right) then error "Sums must be two different types." else TSum left right else error"Typecheck of as failed."
typecheck (Case expr left right) env=case(typecheck expr env) of
										TSum l r-> if(typecheck left env==typecheck right env)then typecheck left env else error$"Cases have different return types."
										_->error $"Case doesn't typecheck to sum."
typecheck something env= error $"Can't typecheck "++show something
lookupType ::String->[(String,Type)]->Type
lookupType st ((s,t):env) = if(st==s) then t else lookupType st env
lookupType st []= error $"Variable not found in environment."


{-
	simplifyType ::Type -> Type
	Takes type and either returns TNum or TBool depending on the root.
-}
simplifyType ::Type -> Type
simplifyType(TNum)=TNum
simplifyType(TBool)=TBool
simplifyType(TList ty _)=ty
simplifyType(TTuple (t1:t2))=case (simplifyType t1,simplifyType (TTuple t2)) of
							(TNum,TNum)->TNum
							(TNum,TNull)->TNum
							(TBool,TBool)->TBool
							(TBool,TNull)->TBool
							_->TNull
simplifyType(_)=TNull

{-
	exec :: Expr         -> Val
			thingToCheck -> What it returns
	Make sure the Expr is typesafe and if it evaluate it.
-}

exec ::Expr ->Val
exec(a)= (typecheck a) `seq` (eval a)

{-
subst :: String -> Expr  ->      Expr
           var     replacement   thingToSubThrough Done 
-}
subst :: String -> Expr  -> Expr -> Expr
subst _ _ (N a)=(N a)
subst _ _ (B a)=(B a)
subst _ _ (Null)=Null
subst str rep body =case body of
			Var st->if(st==str) then rep else (Var st)
			Func name->if(name==str) then rep else (Func name)
			Add arg1 arg2->Add (subst str rep arg1)(subst str rep arg2)
			Mul arg1 arg2->Mul (subst str rep arg1)(subst str rep arg2)
			Sub arg1 arg2->Sub (subst str rep arg1)(subst str rep arg2)
			And arg1 arg2->And (subst str rep arg1)(subst str rep arg2)
			Or arg1 arg2->Or (subst str rep arg1)(subst str rep arg2)
			Not arg1->Not (subst str rep arg1)
			If arg1 arg2 arg3->If (subst str rep arg1)(subst str rep arg2)(subst str rep arg3)
			Equal arg1 arg2->Equal(subst str rep arg1)(subst str rep arg2)
			Lam t st b-> if(st==str) then (Lam t st b) else Lam t st (subst str rep b)
			App arg1 arg2->App (subst str rep arg1)(subst str rep arg2)
			Tuple a->Tuple(map(subst str rep) a)
			Get index list->(Get (subst str rep index)(subst str rep list))
			Rest a->Rest(subst str rep a)
			Head a->Head(subst str rep a)
			List head rest->List (subst str rep head)(subst str rep rest)
			Fix expr-> Fix (subst str rep expr)
			As expr ty->As (subst str rep expr)ty
			TL a->subst str rep a
			TR b->subst str rep b
			something ->error $ "Invalid body for substitution. We have " ++show something++" The string we're looking for is "++show str++" and the replacement is "++show rep++"."

{-
	eval ::Expr  ->Val
		   input ->result
-}
eval :: Expr -> Val

eval (N a) = VN a
eval (Tuple a)=VTuple (map eval a)
eval (B b)=VB b
eval (Lam t str body)=VLam (Lam t str body)
eval (List a b)=VList (eval a)(eval b)
eval (Null)=VNull
eval (Var _) = error "Can't evaluate variables."
eval (Equal a b)=VB ((eval a)==(eval b))
eval (Record fields)=VRecord fields

--Numerical Functions
eval (Mul a b) = case(eval a,eval b) of
					(VN x, VN y) -> VN(x*y)
					(VTuple(c),VTuple(e))->VTuple(map(eval)(zipWith (Mul) (map (makeExpr)c) (map (makeExpr)e)))
					(VList c d,VList e f)->VList (eval(Mul (makeExpr c)(makeExpr e))) (eval(Mul (makeExpr d)(makeExpr f)))
					(VNull,VNull)->VNull 
					something -> error $"Invalid args for multiplication. We have "++ show something++"."				   
					
eval (Add a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n + m)
					(VTuple(c),VTuple(e))->VTuple(map(eval)(zipWith (Add) (map (makeExpr)c) (map (makeExpr)e)))
					(VList c d,VList e f)->VList (eval(Add (makeExpr c)(makeExpr e))) (eval(Add (makeExpr d)(makeExpr f)))
					(VNull,VNull)->VNull
					something -> error $ "Invalid args for addition. We have "++ show something++"."
	
eval (Sub a b) = case (eval a, eval b) of
					(VN n, VN m) -> VN (n - m)
					(VTuple(c),VTuple(e))->VTuple(map(eval)(zipWith (Sub) (map (makeExpr)c) (map (makeExpr)e)))
					(VList c d,VList e f)->VList (eval(Sub (makeExpr c)(makeExpr e))) (eval(Sub (makeExpr d)(makeExpr f)))
					(VNull,VNull)->VNull
					something -> error $ "Subtraction needs two numbers. We have "++ show something++"."

eval (App lam var) = case (eval lam) of
					VLam(Lam t str body)->  eval$ subst str var body
					something -> error $"Invalid args for application. We have "++ show something++"."

--Boolean Functions					
eval(If condition thenCase elseCase)=case (eval condition) of
					VB True->eval(thenCase)
					VB False->eval(elseCase)
					something-> error $"Invalid condition for if. We have "++show something++"."

eval(And a b) = case (eval a, eval b) of
					(VB x, VB y) -> VB (x && y)
					(VTuple(c),VTuple(e))->VTuple(map(eval)(zipWith (And) (map (makeExpr)c) (map (makeExpr)e)))
					(VList c d,VList e f)->VList (eval(And (makeExpr c)(makeExpr e))) (eval(And (makeExpr d)(makeExpr f)))
					(VNull,VNull)->VNull
					something -> error $"Inappropriate arguments for and. We have " ++show something ++"."

eval(Or a b)=case (eval a, eval b) of
					(VB x, VB y) -> VB (x|| y)
					(VTuple(c),VTuple(e))->VTuple(map(eval)(zipWith (Or) (map (makeExpr)c) (map (makeExpr)e)))
					(VList c d,VList e f)->VList (eval(Or (makeExpr c)(makeExpr e))) (eval(Or (makeExpr d)(makeExpr f)))
					(VNull,VNull)->VNull
					something -> error $"Inappropriate arguments for or. We have "++show something++"."

eval(Not a)=case (eval a) of
				(VB x) -> VB (not(x))
				(VTuple(c))->VTuple(map(eval)(map(Not) (map makeExpr c)))
				(VList c d)->VList (eval(Not (makeExpr c))) (eval(Not (makeExpr d)))
				(VNull)->VNull
				something -> error $"Inappropriate arguments for not. We have "  ++show something++"."

--List and pair functions		
eval(Concat a b)=case (a) of
						(Null) -> eval b
						(List head rest)->eval(List head (makeExpr(eval(Concat rest b))))
						_ ->error $ "Concat failed. We have "++show (a,b)++"."
eval(Get index list)=case (eval index) of --Get the indexth member of list.
						(VN num)->if(num<=0) then error "Index out of bounds."
									else if num==1 
										then eval(Head list) 
										else eval(Get (N (num-1)) (makeExpr(eval (Rest(list)))))
eval(Head (List a _))=eval a --Get the first element in list.
eval(Head (something))=eval something --I think this executing is a bug.
eval(Rest (List _ b))=eval b
eval(GetRec str (Record [(k,v)]))=if(str==k)then eval v else error "Key not found."
eval(GetRec str (Record ((k,v):record)))=if(str==k)then eval v else eval(GetRec str (Record record))
eval(LetN ((str,be):more) body)=eval (LetN more (subst str be body))
eval(LetN [(str,be)] body)=eval (subst str be body)
eval(Fix body) =eval(App body (Fix body))--subst name (Fix name body) body)
eval(As expr _)=eval expr
eval(TL a)=eval a
eval(TR a)=eval a
eval(Case expr left right)=case(typecheck(makeExpr(eval expr)) []) of
							(ty)->case(typecheck expr []) of
								(TSum l r)->if(ty==l)then eval left else if(ty==r)then eval right else error$"Case types unmatching."
								_ ->error$"Case expr not of sum type."

{-case(typecheck(makeExpr(eval expr))) of
							(left)->eval left
							(right)->eval right
-}
eval something = error $"No pattern to evaluate "++show something++"."

{-
	makeExpr :: Val   ->Expr
				result->input
	Inverts eval.

-}		
makeExpr :: Val -> Expr 
makeExpr(VB a)=(B a)
makeExpr(VN a)=(N a)
makeExpr(VTuple a)= Tuple (map makeExpr a) 
makeExpr(VLam (Lam t str body))=Lam t str body
makeExpr(VList a b)=List (makeExpr a)(makeExpr b)
makeExpr(VNull)=Null
--makeExpr(VDone)=Done

--Num tests
n1 = Mul (Add(N 2)(N 3))(N 4)
n2 = Add (N 2)  (Mul (N 3) (N 4))
n3 = Sub (N 10)(N 9)
n4 = N 123

--List and Pair tests

p1 = Mul (Tuple[(N 2),(N 2)]) (Mul (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
p1A= VTuple[(VN 18),(VN 32)]
p2 = Or(Tuple[(B True),(B False)])(Tuple[(B False),(B False)])
p2A= VTuple[(VB True),(VB False)]
p3 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 2)])
p4 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 3)])
p7 = Add (Tuple[(N 2),(N 2)]) (Add (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
p8 = Sub (Tuple[(N 2),(N 2)]) (Sub (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
p9 = Not(Tuple[B True, B False])

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
s6Q= subst ("x")(N 4) (Mul (Tuple[(N 2),Var "x"]) (Mul (Tuple[Var "x",(N 4)]) (Tuple[(N 3),Var "x"])))
s6A= Mul (Tuple [N 2,N 4]) (Mul (Tuple[N 4,N 4])(Tuple[N 3,N 4]))
s6Evaled=VTuple[VN 24,VN 64]
s7Q= subst ("x")(B True) (And (Tuple[(B True),Var "x"]) (And (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"])))
s7A= (And (Tuple[B True,B True]) (And (Tuple[B True,B False]) (Tuple[B True,B True])))
s7Evaled=VTuple[VB True,VB False]
s8Q= subst ("x")(B True) (Or (Tuple[(B True),Var "x"]) (Or (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"])))
s8A= (Or (Tuple[B True,B True]) (Or (Tuple[B True,B False]) (Tuple[B True,B True])))
s8Evaled=VTuple[VB True,VB True]
s9=subst ("x")(B True) ((Not (Var  "x")))
s9A=Not (B True)
s10 = subst ("x")(N 3) (Get (Var "x")(List (N 1) (List (N 2)(List (Var "x")(Null)))))
s10A= Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
s11 = subst ("x")(N 1) (Head (Tuple[Var "x",N 6]))
s11A=(Head (Tuple[N 1,N 6]))
s12 = subst ("x")(N 1)(Rest (List (Var "x") (List (N 1)(Null))))
s12A=Rest (List (N 1) (List (N 1)(Null)))
s13 = subst ("x")(N 1)(List(N 5)(List (Var "x")(Null)))
s13A = List(N 5)(List (N 1)(Null))

--Type tests that succeed.
t1 = Lam TBool "x" (If (Var "x")(N 5)(N 6))
t2 = App t1 (B True)
t3 = Lam TNum "y" (Lam TBool "x" (If (Var "x")(Var "y")(N 6)))
t4 = And (B True)(B True)
t5 = Equal (Null)(B True)
t6 = Concat(List (N 5)(Null))(List (N 1)(Null))
t8 = List(N 5)(List (N 1)(Null))
t9 = Lam (TList TNum 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))
t10 = Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
t11 = Rest (List (N 1) (List (N 1)(Null)))
t12 = Mul t8 t8
t13 = Add t8 t8
t14 = Sub t8 t8
t15 = List(B True)(List (B False)(Null))
t16 = And t15 t15
t17 = Not t15
t18 = Or t15 t17

--Expressions that return a value but fail typechecking.
maybe1 = If(B True)(N 4)(B True)--Mixing types in if statements.
maybe2 = If(B False)(N 4)(B True)--Mixing types in if statements.
maybe3 = Concat(List (N 5)(Null))(List (B True)(Null)) --Mixing types in lists.
maybe3Ans= VList (VN 5)(VList (VB True)(VNull))
maybe4 =App(Lam TBool "x" (If (B True)(N 5)(N 6)))(N 5) --Input to lambda is of wrong type.
maybe5=Case(sum1)(N 0)(B True)

--Expressions that crash and fail typechecking.
fail1 = If(N 5)(N 4)(N 3)
fail2 = And (N 5)(B True)
fail3 = Case(N 5)(N 4)(N 3)

--SumTests
sum1=If(B True)(As (TL (N 5))(TSum TNum TBool))(As (TR (B True))(TSum TNum TBool))
sum2=If(B False)(As (TL (N 5))(TSum TNum TBool))(As (TR (B True))(TSum TNum TBool))
case1=Case(sum1)(N 0)(N 1)
case2=Case(sum2)(N 0)(N 1)


-- tests paired with their expected answers
numTests = [(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123) ,(s4A,VN 25),
			(s5A,VN 24),(s6A,s6Evaled),(maybe1,(VN 4)),(maybe2,(VB True)),
			(maybe3,maybe3Ans),(maybe4,VN 5)]

pairTests=[(p1,p1A),(p2,p2A),(p3,VB True),(p4,VB False)]

boolTests=[(b1,VB True),(b2,VB False),(b3,VB True),(b4,VB False)
			,(b5,VB True),(b6,VB False),(b7,VB False),(b8,VB True)
			,(b9,VB False),(b10,VB True),(b11,VB True),(b12,VB False)
			,(t5,VB False)]
			
execTests=[(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123) ,(s4A,VN 25),
			(s5A,VN 24),(s6A,s6Evaled)
			,(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
			,(f6,VN 25),(t4,VB True),(t5,VB False),(t6,(VList (VN 5)(VList (VN 1)(VNull))))
			,(t8,VList (VN 5)(VList (VN 1)(VNull)))
			,(t9, VLam (Lam (TList TNum 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))))
			,(t10,VN 3),(t11,VList (VN 1)(VNull)),(t12,VList (VN 25)(VList (VN 1)(VNull))),(t13,VList (VN 10)(VList (VN 2)(VNull)))
			,(t14,VList (VN 0)(VList (VN 0)(VNull))),(t15,VList (VB True)(VList (VB False)(VNull)))
			,(t16,VList (VB True)(VList (VB False)(VNull))),(t17,VList (VB False)(VList (VB True)(VNull))),(t18,VList (VB True)(VList (VB True)(VNull)))
			,(s7A,VTuple[VB True,VB False]),(p7,VTuple[VN 8,VN 10]),(p8,VTuple[VN 2,VN 2])
			,(p9,VTuple[VB False,VB True]),(s8A,s8Evaled),(sum1,VN 5),(sum2,VB True),(case1,VN 0),(case2,VN 1)]
			
funcTests=[(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
			,(f6,VN 25)]
		
subTests=[(s1Q,s1A),(s2Q,s2A),(s3Q,s3A),(s4Q,s4A),(s5Q,s5A),(s6Q,s6A),(s7Q,s7A),(s8Q,s8A),
		   (s9,s9A),(s10,s10A),(s11,s11A),(s12,s12A),(s13,s13A)]

typeTests=[ (n1,TNum),(n2,TNum),(n3,TNum),(n4,TNum),(b1,TBool),
			(b2,TBool),(b3,TBool),(b4,TBool),(b5,TBool),(b6,TBool),
			(b7,TBool),(b8,TBool),(b9,TBool),(b10,TBool),(b11,TBool),
			(b12,TBool),(f1,TNum :-> TNum),(f2,TNum),(t1,TBool :-> TNum),
			(t2,TNum),(t3,TNum :-> (TBool :-> TNum)),(t4,TBool),(Null,TNull),
			(s7A,TTuple [TBool,TBool]),(t11,TList TNum 1),(sum1,TSum TNum TBool),
			(sum2,TSum TNum TBool),(case1,TNum),(case2,TNum)]

-- are tests paired up with their actual results?
test_results = map (\(t,v)-> eval t==v) numTests
pairTestResults = map (\(t,v)-> eval t==v) pairTests
boolTestResults = map (\(t,v)-> eval t==v) boolTests
funcTestResults = map (\(t,v)-> eval t==v) funcTests
execTestResults = map (\(t,v)-> exec t==v) execTests
subTestResults = map (\(t,v)-> t==v) subTests
typeTestResults = map (\(t,v)-> typecheck t []==v) typeTests

-- ###This works correctly but doesn't use fix.
--factorial = (Lam TNum "x" (Fix "fac"(If (Equal (Var "x")(N 1))(N 1)(Mul (Var "x")(App(factorial) (Sub (Var "x") (N 1))))))) 
--run=App factorial (N 2)
-- ###This runs infinitely for inputs greater than 1.
--factorial = (Lam TNum "x" (Fix "fac"(If (Equal (Var "x")(N 1))(N 1)(Mul (Var "x")(App(Lam TNum "x"(Func "fac")) (Sub (Var "x") (N 1))))))) 
--run=App factorial (N 2)
-- ###This crashes for inputs greater than 1.
factorial = Fix (Lam (TNum :-> TNum)"fac"(Lam TNum "x" ((If (Equal (Var "x")(N 1))(N 1)(Mul (Var "x")(App((Var "fac")) (Sub (Var "x") (N 1))))))) )
run=App factorial (N 3)
--step1=Fix ("fac" (If (Equal(N 2)(N 1))(N 1)(Mul (N 2)(App (Var "fac")(Sub (N 2)(N 1))))))
-- were all tests okay?
okay = (and test_results)&&(and boolTestResults)  &&  (and subTestResults)  &&  (and funcTestResults)  && (and typeTestResults)  &&(and pairTestResults) &&(and execTestResults)

main = do
	putStrLn("okay is " ++show okay)