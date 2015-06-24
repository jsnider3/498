data Expr= Mul Expr Expr | Add Expr Expr | Max Expr Expr | Min Expr Expr | 
	   Dif Expr Expr | Sub Expr Expr | Neg Expr | Abs Expr | Sqr Expr | N Int
--Multiply
eval (Mul a b) = eval(a)*eval(b)
--Addition
eval (Add a b) = eval(a)+eval(b)
--Maximum
eval (Max a b) |  eval(a)>=eval(b)=eval(a)
	       |  eval(a)<eval(b) =eval(b)
--Minimum
eval (Min a b) |  eval(a)<=eval(b)=eval(a)
	       |  eval(a)>eval(b) =eval(b)
--Difference
eval (Dif a b) = eval(Max (a) (b))-eval(Min (a) (b))
--Subtraction
eval (Sub a b) = eval(a)-eval(b)
--Negation
eval (Neg a) = eval(Sub (N 0) a)
--Absolute Value
eval (Abs a) | eval(a)<0  = eval(Neg a)
	     | eval(a)>=0 = eval(a)
--Square
eval (Sqr a) = eval(Mul a a)
--Simple Number
eval (N a) = a

t1 = Mul(Add(N 2)(N 3))(N 4)
t2 = Add (N 2)  (Mul (N 3) (N 4))
t3 = Max (N 5)(N 8)
t4 = Min (N 5)(N 8)
t5 = Dif (N 5)(N 8)
t6 = Sub (N 10)(N 9)
t7 = Neg (N 10)
t8 = Neg (Neg (N 10))
t9 = Abs (Neg (N 12))
t10= Sqr (N 12)
t11= N 123
t12= Dif(Sqr t8)(t9)

-- tests paired with their expected answers
tests = [(t1,20),(t2,14),(t3,8),(t4,5),
	 (t5,3),(t6,1),(t7,-10),(t8,10),
	 (t9,12),(t10,144),(t11,123),(t12,88)]

-- are tests paired up with their actual eval results?
test_results = map (\(t,v)-> (eval t)==v) tests

-- were all tests okay?
okay = and test_results