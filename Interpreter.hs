--Changes since Project 6.5
--Perfect Typechecking for Records
--Distinguish between TReal and TInt
--Add subtype::Type->Type->Bool method and commonType
--In a lot of scenarios, typecheck will now return Top as the return type of an expression instead of crashing.
	--This indicates that that's the smallest Type which contains all of the possible values.
import Control.Parallel
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
data Expr= N Int | F Float| Add Expr Expr | Mul Expr Expr | Sub Expr Expr
	   | And Expr Expr | Or Expr Expr |Not Expr |If Expr Expr Expr |Equal Expr Expr| B Bool
	   | Lam Type String Expr | App Expr Expr | Var String |Tuple[Expr]
	   |List Expr Expr 
	   |Null --Null is the Unit Type
	   |Done
	   |Concat Expr Expr |Get Expr Expr |Head Expr |Rest Expr
	   |Record [(String,Expr)] |GetRec String Expr 
	   |Fix Expr|LetN[(String,Expr)] Expr  
	   |TL Expr| TR Expr| Case Expr Expr Expr |As Expr Type 
	   |Seq [Expr] |Set Type String Expr |Lookup String |While Expr Expr
	   |Top|Bottom
           deriving(Show,Eq)
		   
data Type = TInt | TReal |TBool | Type :-> Type  |TTuple [Type] | TyL Type | TyR Type |TList Type Int |TRecord[(String,Type)]|TNull |TSum Type Type|TDone|TTop|TBottom
		deriving (Show, Eq)

data Val = VB Bool | VTuple [Val] | VList Val Val |VNull | VL Val |VR Val|VDone|
			VN Int |VF Float| VLam Expr |VRecord [(String,Expr)]|VTop|VBottom deriving (Show, Eq) --There's no VApp because applications can always be reduced further.

type Dict a  b =Map.Map a b
type Env =Dict String Val --deriving (Show,Eq)
type TEnv=Dict String Type --deriving(Show,Eq)	

{-
	typecheck ::Expr                  ->Type
				suspicious expression ->type it returns
	Makes sure an expression uses types correctly and either returns 
	a value of a single type or  returns an error.
-}			
typecheck ::Expr->State TEnv Type --[(String,Type)]->([(String,Type)],Type)
typecheck (N _)=return TInt
typecheck (F _)=return TReal
typecheck (B _)=return TBool
typecheck (Null)=return TNull
typecheck (Equal _ _)= return TBool
typecheck (Add a b)= typecheck (Sub a b)
typecheck (Mul a b)= typecheck (Sub a b)
typecheck (Sub a b)= do
	env<-get
	if subtype(simplifyType(evalState(typecheck a)env)) TReal &&subtype(simplifyType(evalState(typecheck b)env)) TReal  then return$commonType(evalState(typecheck a)env)(evalState(typecheck b)env)  else error $"Typecheck failure for arithmetic operation. We have "++show (a,b)++"."
typecheck (Or  a b)= typecheck(And a b)
typecheck (And a b)= do
	env<-get
	if subtype(simplifyType(evalState(typecheck a)env)) TBool &&simplifyType(evalState(typecheck b)env)==TBool  then typecheck a  else error $"Typecheck failure for boolean operation. We have "++show (a,b)++"."
typecheck (If a b c)= do
	env<-get
	if evalState(typecheck a)env==TBool 
						then if execState(typecheck b)env  ==execState(typecheck c)env
								then return $commonType(evalState(typecheck b)env)(evalState(typecheck c)env)
								else error "If clauses change state inappropriately."
						else error "Conditions for if must be boolean type"
typecheck (Done)=return TDone
typecheck (Not a)= do
	env<-get
	if simplifyType(evalState(typecheck a)env)==TBool then typecheck a  else error $"Typecheck failure for not. We have "++show a++"."
typecheck (Tuple a) = do
	env<-get
	return(TTuple (zipWith (evalState)(map typecheck a)(replicate (length a)env )))
typecheck (App (Fix lam)var)=do
	env<-get
	case(evalState(typecheck (Fix lam))env)of
								((from:->to):->(from1:->to1))->if subtype(evalState(typecheck var )env)from&&subtype from from1&&subtype to1 to then do{put $execState(purgeEnv(lam))env; return to1} else error $"Input to a lambda is of inappropriate type. We have "++show(evalState(typecheck var )env)++" but want "++show from++"."
								_ -> error "Typecheck failed, at an Application to a fix."
typecheck (App lam var)= do
	env<-get
	case (evalState(typecheck lam)env ) of
					(from :-> to)->if subtype(evalState(typecheck var)env)from then do{put $execState(purgeEnv(lam))env; return to} else error $"Input to a lambda is of inappropriate type. We have "++show(evalState(typecheck var )env)++" but want "++show from++"."
					_ -> error "Application is done to a non-lambda."
typecheck (Lam t s b)= do
	env<-get
	put $(Map.insert s t env)
	env<-get
	case evalState(typecheck b)env of
							(x)->if evalState(free(s,t))env then return(t:->x)else error "Attempt to change type of var."
typecheck (Concat a b)=do
	env<-get
	case (evalState(typecheck a)env ,evalState(typecheck b)env ) of
							(TList type1 alen,TList type2 blen) ->return(TList (commonType type1 type2) (alen+blen))
							_ -> error "Can't concat non-lists."
typecheck (Get index list)=do
	env<-get
	case(evalState(typecheck index)env ,evalState(typecheck list)env ) of
							(TInt,TList type1 _)-> return(type1)
							_ -> error "Get requires a list to work with."
typecheck (Head a)=do
	env<-get
	case evalState(typecheck a)env of
						(TList type1 _)->return(type1)
						_ -> error "Head only works on pairs and lists."
typecheck (Rest a)=do
	env<-get
	case evalState(typecheck a)env of
						(TList listType len)->case (a) of
									(List _ Null) ->return(TNull) --I'm not sure if I should return null if they try to call rest on the end of the list or crash.
									(List _ _) -> return(TList listType (len-1))
						_ -> error "Rest only works on pairs and lists."
typecheck (List head rest)=do
	env<-get
	case evalState(typecheck head)env of
							(TNull) -> error "Lists cannot be headed by null."
							(TList _ _)-> error "Lists cannot be headed by lists."
							(goodType)->case evalState(typecheck rest )env of
										(TNull)->return $TList goodType 1
										(TList type2 len)->return $TList (commonType goodType type2) (len+1)
										(type2)-> error "List was terminated inappropriately."
typecheck (Fix (Lam t s b))= (typecheck (Lam t s b))-- :->(typecheck (Lam t s b))--DEBUG
typecheck (Fix something)=error$"Typecheck for fix failed. The body is "++show something++"."
typecheck (Var st) = do
	env<-get
	lookupType st
typecheck (As expr ty)= do
	env<-get
	case (expr,ty) of
								(TL a,TSum left right)->if subtype(evalState(typecheck a)env)left then if(left==right) then error "Sums must be two different types. TL" else return(TSum left right) else error"Typecheck of as failed. TL"
								(TR b,TSum left right)->if subtype(evalState(typecheck b)env)right then if(left==right) then error "Sums must be two different types. TR" else return(TSum left right) else error"Typecheck of as failed. TR"
typecheck (Case expr left right)=do
	env<-get
	case evalState(typecheck expr)env of
										TSum l r-> case (evalState(typecheck left)env,evalState(typecheck right)env) of
														(a:->b,c:->d)->if(subtype l a&&subtype r c)then return (commonType b d) else error$"Typechecking failure for case lambda."++show (a:->b)++" "++show (c:->d)++" "++show (TSum l r)
														_->error$"Case doesn't have two lambdas."
										_->error $"Case doesn't typecheck to sum."
typecheck(Seq [a])=typecheck a
typecheck(Seq (a:b))=do
	env<-get
	put $execState(typecheck a)env
	typecheck (Seq b)
typecheck(While guard body)=do
	env<-get
	case evalState(typecheck guard)env of
									(TBool)-> (typecheck body) `seq` return(TDone)
									_->error $"Guard must be boolean"
typecheck(Lookup name)=do
	env<-get
	(lookupType name)
typecheck(Set ty name expr)=do
	env<-get
	if(subtype(evalState(typecheck expr)env)ty)then if evalState(free(name,ty))env then do {put $(Map.insert name ty env);return TDone}else error "Attempt to change type of variable." else error $"Set is assigning a non"++show ty++" to a "++show ty++" variable."
typecheck(Record fields)= do
	env<-get
	return(TRecord $ zip(map fst fields)((zipWith evalState(map typecheck(map snd fields))(replicate (length fields)env))))
typecheck(GetRec str (Record[(k,v)]))=if(k==str)then typecheck v  else error $"Record doesn't possess the specified field."
typecheck(GetRec str (Record((k,v):record)))=if(k==str)then typecheck v  else typecheck(GetRec str (Record record))
typecheck something = error $"Can't typecheck "++show something

{-
	commonType ::Type->Type->Type
-}
commonType ::Type->Type->Type
commonType (TRecord a)(TRecord b)=TRecord(intersect a b)
commonType a b=if(subtype a b)then b else if subtype b a then a else TTop
{-
	subType ::Type->Type->Bool
-}
subtype ::Type->Type->Bool
subtype TInt TReal=True
subtype (a:->b)(c:->d)=subtype c a && subtype b d
subtype TBottom _=True
subtype _ TTop=True
subtype (TRecord rec1)(TRecord rec2)=length (rec2\\rec1)==0
subtype a b=if(a==b) then True else False

{-
	lookupType ::String->TEnv->Type
	Searches the environment and returns the type of the variable specified.
-}
lookupType ::String->State TEnv Type
lookupType st  = do
	env<-get
	case Map.lookup st env of
		(Just x)->return x
		_->error $"Variable "++show st++" not found in environment."
	{-case env of
		[]->error $"Variable "++show st++" not found in environment."
		((s,v):rest)->if(st==s) then return v else do{return $evalState(lookupType st)rest}
	-}
{-
	purgeEnv::Env->Expr->Env
	Removes the lambda variables from the environment when it's removed by an application.
-}
purgeEnv::Expr->State TEnv Bool
purgeEnv(Lam t s b)=do
	env<-get
	put $Map.delete s env
	return True
purgeEnv (Fix b)= purgeEnv(b)
purgeEnv _=return False --error $"Attempt to purge something not part of an application. We have"++show thing
{-
	free::(String,Type)->TEnv->Bool
	Checks the environment to make sure that a given variable name is not already defined in the environment as having a different type. 
	I thought of making it crash if you declared a variable twice with the same type, but that would have been both problematic and picky.
-}
free::(String,Type)->State TEnv Bool
free(s,t)=do
	env<-get
	case Map.lookup s env of
		(Just ty)->return (t==ty)
		_->return True
		
	return True
	{-case env of
					[]->return True
					(name,ty):rest->if(name==s&&not(t==ty))then return False else do{put rest;free(s,t)}
	-}
{-
	simplifyType ::Type -> Type
	Takes type and either returns TReal or TBool depending on the root.
-}
simplifyType ::Type -> Type
simplifyType(TInt)=TInt
simplifyType(TReal)=TReal
simplifyType(TBool)=TBool
simplifyType(TList ty _)=ty
simplifyType(TTuple (t1:t2))=case (simplifyType t1,simplifyType (TTuple t2)) of
							(TReal,TReal)->TReal
							(TReal,TNull)->TReal
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
exec(a)= evalState(typecheck a)Map.empty `seq` (evalState(eval a )Map.empty)

{-
subst :: String -> Expr  ->      Expr
           var     replacement   thingToSubThrough Done 
-}
subst :: String -> Expr  -> Expr -> Expr
subst _ _ (N a)=(N a)
subst _ _ (F a)=(F a)
subst _ _ (B a)=(B a)
subst _ _ (Null)=Null
subst _ _ (Lookup name)=Lookup name
subst str rep body =case body of
			Var st->if(st==str) then rep else (Var st)
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
			TL a->TL $ subst str rep a
			TR b->TR $ subst str rep b
			LetN things body-> LetN (zip(map fst things)(map(subst str rep)(map snd things))) (subst str rep body)  
			Seq a -> Seq (map (subst str rep) a)
			Set ty name a ->Set ty name (subst str rep a)
			While guard body->While (subst str rep guard)(subst str rep body)
			something ->error $ "Invalid body for substitution. We have " ++show something++" The string we're looking for is "++show str++" and the replacement is "++show rep++"."

{-
	eval ::Expr  ->Val
		   input ->result
-}

eval :: Expr -> State Env Val

eval (N a) = return (VN a)
eval (F a) = return (VF a)
eval (Tuple a)=do
	env<-get
	return(VTuple (zipWith (evalState)(map eval a)(replicate (length a)env )))
--(zipWith typecheck a (replicate (length a)env))

eval (B b)=return(VB b)
eval (Lam t str body)=return(VLam (Lam t str body))
eval (List a b)=do
	env <-get
	first<-eval a
	s2nd<-eval b
	return (VList (first)(s2nd))
	--return(VList (eval a)(eval b))
eval (Null)=return(VNull)
eval (Var _) = error "Can't evaluate variables."
eval (Equal a b)=do
	first<-eval a
	s2nd<-eval b
	return (VB(first==s2nd))
eval (Record fields)=return(VRecord fields)

--Numerical Functions 

eval (Mul a b) = do
	env <-get
	case (evalState(eval a) env,evalState(eval b)env) of
			(VN x, VN y) -> return(VN(x*y))
			(VN x, VF y) -> return(VF ((fromIntegral x)*y))
			(VF x, VN y) -> return(VF(x*(fromIntegral y)))
			(VF x, VF y) -> return(VF(x*y))
			something -> error $"Invalid args for multiplication. We have "++ show something++"."
					

eval (Add a b) = do
	env <-get
	case (evalState(eval a) env,evalState(eval b)env) of
			(VN x, VN y) -> return(VN(x+y))
			(VN x, VF y) -> return(VF ((fromIntegral x)+y))
			(VF x, VN y) -> return(VF(x+(fromIntegral y)))
			(VF x, VF y) -> return(VF(x+y))
			something -> error $"Invalid args for multiplication. We have "++ show something++"."
	
eval (Sub a b) = do
	env <-get
	case (evalState(eval a) env,evalState(eval b)env) of
			(VN x, VN y) -> return(VN(x-y))
			(VN x, VF y) -> return(VF ((fromIntegral x)-y))
			(VF x, VN y) -> return(VF(x-(fromIntegral y)))
			(VF x, VF y) -> return(VF(x-y))
			something -> error $"Invalid args for multiplication. We have "++ show something++"."	

eval (App lam var) = do
	env<-get
	case evalState(eval lam)env of
					(VLam(Lam t str body))-> eval ( subst str var body)
					something -> error $"Invalid args for application. We have "++ show something++" as our lambda."

--Boolean Functions					
eval(If condition thenCase elseCase)=do
	env<-get
	case evalState(eval condition)env of
					(VB True)->eval(thenCase) 
					(VB False)->eval(elseCase)
					something-> error $"Invalid condition for if. We have "++show something++"."

eval(And a b) = do
	env <-get
	case (evalState(eval a) env,evalState(eval b)env) of
			(VB x, VB y) -> return(VB(x&&y))
			something -> error $"Invalid args for multiplication. We have "++ show something++"."	
						
eval(Or a b)=do
	env <-get
	case (evalState(eval a) env,evalState(eval b)env) of
			(VB x, VB y) -> return(VB(x||y))
			something -> error $"Invalid args for multiplication. We have "++ show something++"."
						

eval(Not a)=do
	env <-get
	case(evalState(eval a) env) of
					(VB x)->return(VB(not x))
					(n)->error $"Attempt to not" ++show a 

--List and pair functions		
eval(Concat a b)=do
	env <-get
	case (a) of
						(Null) -> eval b
						(List head rest)->eval(List head (makeExpr(evalState(eval(Concat rest b))env)))
						_ ->error $ "Concat failed. We have "++show (a,b)++"."
eval(Get index list)=do
	env <-get
	case evalState(eval index)env of --Get the indexth member of list.
						(VN num)->if(num<=0) then error "Index out of bounds."
									else if num==1 
										then eval(Head list) 
										else eval(Get (N (num-1)) (makeExpr(evalState(eval (Rest(list)))env)))
eval(Head (List a _))=eval a--Get the first element in list.
eval(Head (something))=eval something--I think this executing is a bug.
eval(Rest (List _ b))= eval b
eval(GetRec str (Record [(k,v)]))=if(str==k)then (eval v ) else error "Key not found."
eval(GetRec str (Record ((k,v):record)))=if(str==k)then eval v  else eval(GetRec str (Record record))
eval(LetN [(str,be)] body)=eval (subst str be body) 
eval(LetN ((str,be):more) body)=eval (LetN more (subst str be body)) 
eval(Fix body) =eval(App body (Fix body))--subst name (Fix name body) body)
eval(As expr _)=eval expr 
eval(TL a)=do
	env <-get
	return(VL(evalState(eval a)env))
eval(TR a)=do
	env <-get
	return(VR(evalState(eval a)env))
eval(Case expr left right)=do
	env <-get
	case evalState(eval expr)env of
							(VL a)->eval(App left (makeExpr a))
							(VR b)->eval(App right(makeExpr b))
							(thing)->error $"Case returned "++show thing++"."

eval(Seq [a])=  eval a
eval(Seq (a:b))=do
	env<-get
	put $execState(eval a)env
	eval (Seq b)
eval(Set _ name a)=do
	env<-get
	put $execState(setHelper(name,evalState(eval a)env))env
	return VDone
eval(Lookup str)=do
	env<-get
	return $evalState(lookupState str)env
eval(While guard body)=do
	env<-get
	case evalState(eval guard)env of
								(VB True )->do
											put $execState(eval body)env
											eval(While guard body)
								(VB False)->return(VDone)
								_-> error$"Do while failure in false."
eval(Done) =return(VDone)
eval something = error $"No pattern to evaluate "++show something++"."

{-
	setHelper::(String,Val)->State Env Bool
	Redefines the value of a variable in the environment or gives it one if it was previously undefined.
-}	
setHelper::(String,Val)->State Env ()
setHelper (name,val) = do
	env<-get
	put$Map.insert name val env
	{-case env of
		((s,v):rest)->if(name==s)
							then put$(name,val):rest
							else put$(s,v):(execState(setHelper (name,val))rest)
		[]->put [(name,val)]
		-}
{-
	lookupState ::String->State Env Val
	Given the name of a variable either returns its value in the environment or crashes.
-}	
lookupState ::String->State Env Val
lookupState st  = do
	env<-get
	case Map.lookup st env of
		(Just x)->return x
		_->error $"Variable "++show st++" not found in environment."
		
	{-case env of
		[]->error $"Variable " ++show st++" not found in environment."
		((s,v):rest)->if(st==s) then return v else do{return $evalState(lookupState st)rest}
	-}

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
makeExpr(VRecord stuff)=Record stuff
makeExpr(VNull)=Null
--makeExpr(VDone)=Done

--Num tests
n1 = Mul (Add(N 2)(N 3))(N 4)
n2 = Add (N 2)  (Mul (N 3) (N 4))
n3 = Sub (N 10)(N 9)
n4 = N 123

--List and Pair tests

-- p1 = Mul (Tuple[(N 2),(N 2)]) (Mul (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
p1A= VTuple[(VN 18),(VN 32)]
-- p2 = Or(Tuple[(B True),(B False)])(Tuple[(B False),(B False)])
p2A= VTuple[(VB True),(VB False)]
p3 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 2)])
p4 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 3)])
-- p7 = Add (Tuple[(N 2),(N 2)]) (Add (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
-- p8 = Sub (Tuple[(N 2),(N 2)]) (Sub (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
--p9 = Not(Tuple[B True, B False])

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
f1 = Lam (TInt)"x" (Mul (N 5)(Var "x"))
f1A=VLam(Lam (TInt)"x" (Mul (N 5)(Var "x")))
f2 = App f1 (N 1)
f3 = Lam (TInt)"x" (Mul (N 5)(Var "y"))
f3A= VLam(Lam (TInt)"x" (Mul (N 5)(Var "y")))
f4 = App f3 (N 1)--Generates exception.
f5 = Lam (TInt)"y" (App (Lam (TInt) "x" (Mul (Var "x")(Var "y")))(Var "y"))
f5A = VLam(Lam (TInt) "y" (App (Lam (TInt)"x" (Mul (Var "x")(Var "y")))(Var "y")))
f6 = App f5 (N 5)

--Subst tests
s1Q=subst ("x")(N 5) (Lam (TReal)"y"(Mul (Var  "x")(Var "y")))
s1A=(Lam (TReal)"y"(Mul (N 5)(Var "y")))
s2Q=subst ("x")(N 5) (Lam (TReal)"y"(Mul (Var  "z")(Var "y")))
s2A=(Lam (TReal)"y"(Mul (Var  "z")(Var "y")))
s3Q=subst ("x")(N 5) (Lam (TReal)"y"(Sub (Var  "z")(Var "y")))
s3A=(Lam (TReal)"y"(Sub (Var  "z")(Var "y")))
s4Q=subst ("x")(N 5) ((Mul (Var  "x")(Var "x")))
s4A=((Mul (N 5)(N 5)))
s5Q=subst ("y")(N 12) (If (Equal (N 5)(Var "y"))(Mul (Var "y")(Var "y"))(Add (Var "y")(Var "y")))
s5A = If(Equal (N 5)(N 12))(Mul (N 12)(N 12))(Add (N 12)(N 12))
--s6Q= subst ("x")(N 4) (Mul (Tuple[(N 2),Var "x"]) (Mul (Tuple[Var "x",(N 4)]) (Tuple[(N 3),Var "x"])))
--s6A= Mul (Tuple [N 2,N 4]) (Mul (Tuple[N 4,N 4])(Tuple[N 3,N 4]))
s6Evaled=VTuple[VN 24,VN 64]
--s7Q= subst ("x")(B True) (And (Tuple[(B True),Var "x"]) (And (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"])))
--s7A= (And (Tuple[B True,B True]) (And (Tuple[B True,B False]) (Tuple[B True,B True])))
-- s7Evaled=VTuple[VB True,VB False]
-- s8Q= subst ("x")(B True) (Or (Tuple[(B True),Var "x"]) (Or (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"])))
-- s8A= (Or (Tuple[B True,B True]) (Or (Tuple[B True,B False]) (Tuple[B True,B True])))
-- s8Evaled=VTuple[VB True,VB True]
s9=subst ("x")(B True) ((Not (Var  "x")))
s9A=Not (B True)
s10 = subst ("x")(N 3) (Get (Var "x")(List (N 1) (List (N 2)(List (Var "x")(Null)))))
s10A= Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
s11=subst ("x")(B True) ((And (Var  "x")(Var "x")))
s11A=((And(B True)(B True)))
s12 = subst ("x")(N 1)(Rest (List (Var "x") (List (N 1)(Null))))
s12A=Rest (List (N 1) (List (N 1)(Null)))
s13 = subst ("x")(N 1)(List(N 5)(List (Var "x")(Null)))
s13A = List(N 5)(List (N 1)(Null))
s14 = subst ("x")(N 1) $Head(List (N 1) (List (N 2)(List (Var "x")(Null))))
s14A=Head ((List (N 1) (List (N 2)(List (N 1)(Null)))))
s15=subst ("x")(B True) ((Or (Var  "x")(Var "x")))
s15A=((Or(B True)(B True)))

--Type tests that succeed.
t1 = Lam TBool "x" (If (Var "x")(N 5)(N 6))
t2 = App t1 (B True)
t3 = Lam TInt "y" (Lam TBool "x" (If (Var "x")(Var "y")(N 6)))
t4 = And (B True)(B True)
t5 = Equal (Null)(B True)
t6 = Concat(List (N 5)(Null))(List (N 1)(Null))
t8 = List(N 5)(List (N 1)(Null))
t9 = Lam (TList TReal 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))
t10 = Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
t11 = Rest (List (N 1) (List (N 1)(Null)))
t12 = (List (F 1.5) (List (N 2)(List (N 3)(Null))))
--t12 = Mul t8 t8
--t13 = Add t8 t8
--t14 = Sub t8 t8
--t15 = List(B True)(List (B False)(Null))
--t16 = And t15 t15
--t17 = Not t15
--t18 = Or t15 t17

--Expressions that return a value but fail typechecking.
maybe1 = If(B True)(N 4)(B True)--Mixing types in if statements.
maybe2 = If(B False)(N 4)(B True)--Mixing types in if statements.
maybe3 = Concat(List (N 5)(Null))(List (B True)(Null)) --Mixing types in lists.
maybe3Ans= VList (VN 5)(VList (VB True)(VNull))
maybe4 =App(Lam TBool "x" (If (B True)(N 5)(N 6)))(N 5) --Input to lambda is of wrong type.
maybe5=Case(sum1)(Lam TReal "x" (Var "x"))(Lam TBool "x" (Var "x"))

--Expressions that crash and fail typechecking.
fail1 = If(N 5)(N 4)(N 3)
fail2 = And (N 5)(B True)
fail3 = Case(N 5)(N 4)(N 3)

--Record tests
rec1=Record[("age",N 18),("shoe-size",N 14)]
rec1T=TRecord[("age",TInt),("shoe-size",TInt)]
rec2=GetRec "shoe-size" rec1
rec3=GetRec "age" rec1
rec4=Record[("age",N 18),("shoe-size",N 14),("numfeet",N 2)]
rec4T=TRecord[("age",TInt),("shoe-size",TInt),("numfeet",TInt)]

--SumTests
sum1=If(B True)(As (TL (N 5))(TSum TInt TBool))(As (TR (B True))(TSum TInt TBool))
sum2=If(B False)(As (TL (N 5))(TSum TInt TBool))(As (TR (B True))(TSum TInt TBool))
case1=Case(sum1)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
case2=Case(sum2)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
sum2Point5=(If(Var "x")(As (TL (If(Var "x")(N 5)(N 4)))(TSum TReal TBool))(As (TR (Var "x"))(TSum TReal TBool)))
sum3=Lam TBool "x" sum2Point5
sum4=App sum3 (B True)
sum5=App sum3 (B False)
case3=Case(sum4)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
case4=Case(sum5)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))

--SeqTests
while1=While(B True)(N 3)
assign1=Seq[Set TInt "x" (N 1),Lookup "x"]
assign2=Seq[Set TInt "x" (N 1),Set TInt "y" (N 2),Lookup "x"]

--FloatTests
fl1=Mul(F 3.4)(N 3)
fl2=Mul(N 3)(F 3.2)
fl3=Mul(F 3.4)(F 3.2)
fl4=Add(F 3.4)(N 3)
fl5=Add(N 3)(F 3.2)
fl6=Add(F 3.4)(F 3.2)
fl7=Sub(F 3.4)(N 3)
fl8=Sub(N 3)(F 3.2)
fl9=Sub(F 3.4)(F 3.2)

--Typing continued
typ0000=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Var "y"))--Applying TReal->TReal to TReal->TReal. Succeeds
typ0001=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Var "y"))--Applying TReal->TReal to TReal->TInt. Fails.
typ0010=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Mul (Var "y")(F 3)))--Applying TReal->TReal to TInt->TReal. Succeeds
typ0011=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Mul (Var "y")(F 3.4)))--Applying TReal->TReal to TInt->TInt. Fails.
typ0100=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TReal->TInt to TReal->TReal. Succeeds
typ0101=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TReal->TInt to TReal->TInt. Succeeds
typ0110=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TInt->TReal to TReal->TInt. Fails
typ0111=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (N 3))--Applying TReal->TInt to TInt TInt. Succeeds.
typ1000=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TInt->TReal to TR->TR
typ1001=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TI->TR to TR->TI
typ1010=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3)))--Applying TInt->TReal to TInt->TReal. Succeeds
typ1011=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TInt->TReal to TInt->TInt. Fails.
typ1100=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (N 3))--Applying TInt->TInt to TReal->TReal.Fails
typ1101=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (N 3))--Applying TI->TI to TR->TI. Fails
typ1110=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" ((Var "y")))--App TI->TI to TI->TR
typ1111=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" ((Var "y")))

-- tests paired with their expected answers
numTests = [(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123) ,(s4A,VN 25),
			(s5A,VN 24),(maybe1,(VN 4)),(maybe2,(VB True)), --(s6A,s6Evaled),
			(maybe3,maybe3Ans),(maybe4,VN 5),(fl1,VF (3.4*3)),(fl2,VF 9.6),(fl3,VF 10.88)
			,(fl4,VF 6.4),(fl5,VF 6.2),(fl6,VF (3.4+3.2)),(fl7,VF (3.4-3)),(fl8,VF (3-3.2)),(fl9,VF (3.4-3.2))]

pairTests=[(p3,VB True),(p4,VB False)]--(p1,p1A),(p2,p2A),

boolTests=[(b1,VB True),(b2,VB False),(b3,VB True),(b4,VB False)
			,(b5,VB True),(b6,VB False),(b7,VB False),(b8,VB True)
			,(b9,VB False),(b10,VB True),(b11,VB True),(b12,VB False)
			,(t5,VB False)]
			
execTests=[(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123) ,(s4A,VN 25),
			(s5A,VN 24) -- ,(s6A,s6Evaled)
			,(f1,f1A),(f2,VN 5),(f5,f5A)
			,(f6,VN 25),(t4,VB True),(t5,VB False),(t6,(VList (VN 5)(VList (VN 1)(VNull))))
			,(t8,VList (VN 5)(VList (VN 1)(VNull)))
			,(t9, VLam (Lam (TList TReal 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))))
			,(t10,VN 3),(t11,VList (VN 1)(VNull))--,(t12,VList (VN 25)(VList (VN 1)(VNull))),(t13,VList (VN 10)(VList (VN 2)(VNull)))
			--,(t14,VList (VN 0)(VList (VN 0)(VNull))),(t15,VList (VB True)(VList (VB False)(VNull)))
			--,(t16,VList (VB True)(VList (VB False)(VNull))),(t17,VList (VB False)(VList (VB True)(VNull))),(t18,VList (VB True)(VList (VB True)(VNull)))
			--,(p7,VTuple[VN 8,VN 10]),(p8,VTuple[VN 2,VN 2]) --,(s7A,VTuple[VB True,VB False])
			,(sum1,VL(VN 5)),(sum2,VR(VB True)),(case1,VN 5),(case2,VN 4),(rec1,VRecord[("age",N 18),("shoe-size",N 14)])
			,(rec2,VN 14),(rec3,VN 18),(App fibonacci (N 4),VN 3),(sum4,VL(VN 5)),(sum5,VR(VB False)),(case3,VN 5),(case4,VN 3)
			,(s14A,VN 1),(Done,VDone)]--,(s15A,VN 6)] --(s8A,s8Evaled),(p9,VTuple[VB False,VB True]),
			
funcTests=[(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
			,(f6,VN 25)]
		
subTests=[(s1Q,s1A),(s2Q,s2A),(s3Q,s3A),(s4Q,s4A),(s5Q,s5A), --(s6Q,s6A),(s7Q,s7A),(s8Q,s8A),
		   (s9,s9A),(s10,s10A),(s11,s11A),(s12,s12A),(s13,s13A),(s14,s14A),(s15,s15A)]

typeTests=[ (n1,TInt),(n2,TInt),(n3,TInt),(n4,TInt),(b1,TBool),
			(b2,TBool),(b3,TBool),(b4,TBool),(b5,TBool),(b6,TBool),
			(b7,TBool),(b8,TBool),(b9,TBool),(b10,TBool),(b11,TBool),
			(b12,TBool),(f1,TInt :-> TInt),(f2,TInt),(t1,TBool :-> TInt),
			(t2,TInt),(t3,TInt :-> (TBool :-> TInt)),(t4,TBool),(Null,TNull),
			(t6,TList TInt 2),(t10,TInt),(t11,TList TInt 1),(sum1,TSum TInt TBool), --(s7A,TTuple [TBool,TBool]),
			(sum2,TSum TInt TBool),(case1,TReal),(case2,TReal),(factorial,(TInt :->TInt):->(TInt:->TInt)),
			(Tuple [N 3,N 2, B True],TTuple[TInt,TInt,TBool]),(run,TInt),
			(while1,TDone),(assign1,TInt),(t12,TList TReal 3),(rec1,rec1T),(rec4,rec4T)]
			
subtypeTests=[(TInt,TReal,True),(TReal,TReal,True),(TReal,TInt,False),(rec4T,rec1T,True),(rec1T,rec4T,False)
				,(TTop,TBottom,False),(TBottom,TTop,True),(rec1T,rec4T,False)]

-- are tests paired up with their actual results?
testResults = map (\(t,v)-> evalState(eval t)Map.empty==v) numTests
----fst and snd
pairTestResults = map (\(t,v)-> exec t==v) pairTests
boolTestResults = map (\(t,v)-> exec t==v) boolTests
funcTestResults = map (\(t,v)-> exec t==v) funcTests
execTestResults = map (\(t,v)-> exec t==v) execTests
subTestResults  = map (\(t,v)-> t==v) subTests
typeTestResults = map (\(t,v)-> evalState(typecheck t)Map.empty==v) typeTests
subtypeTestResults = map (\(t,r,v)-> subtype t r==v) subtypeTests


factorial = Fix (Lam (TInt :-> TInt)"fac"(Lam TInt "x" ((If (Equal (Var "x")(N 1))(N 1)(Mul (Var "x")(App((Var "fac")) (Sub (Var "x") (N 1))))))) )
run=App factorial (N 4)
fibonacci=Lam (TInt) "limit" 
	(Seq[Set TInt "x0" (N 0),
		Set TInt "x1" (N 1),
		Set TInt "count" (N 0),
		While(Not(Equal (Lookup "count")(Var "limit")))
		(Seq [
			Set TInt "x0"(Add(Lookup "x0")(Lookup "x1")),
			Set TInt "x1"(Sub(Lookup "x0")(Lookup "x1")),
			Set TInt "count" (Add(Lookup "count")(N 1))
			]),
		Lookup "x0"
	])
	
maybeWhile=Seq[Set TInt "cnt" (N 0) ,
		While(Not(Equal (Lookup "cnt")(N 2)))
		(Seq [
			If(Equal (Lookup "cnt")(N 1)) (Lookup "x")(N 0),
			If(Equal (Lookup "cnt")(N 0)) (Set TInt "x" (N 0))(Done),
			Set TInt "cnt" (Add(Lookup "cnt")(N 1))
			])	
			]
-- were all tests okay?
okay = (and testResults)&&(and boolTestResults)  &&  (and subTestResults)  &&  (and funcTestResults)  && (and typeTestResults)  &&(and pairTestResults) &&(and execTestResults)&&(and subtypeTestResults)

main = do
	putStrLn (show(evalState(eval (App factorial (N 3)))Map.empty))
	putStrLn (show(evalState(eval (App fibonacci (N 4)))Map.empty))
	putStrLn("okay is " ++show okay)