import Pruviloj
import Pruviloj.Derive.DecEq

%hide Abs
%hide lookup

%language ElabReflection
%default total

data Typ 
    = Base
    | Arrow Typ Typ

Uninhabited (Base = Arrow _ _) where
    uninhabited Refl impossible

decEqTyp : (ty1, ty2 : Typ) -> Dec (ty1 = ty2)
%runElab (deriveDecEq `{decEqTyp})

DecEq Typ where
    decEq = decEqTyp

data Term 
    = Var String
    | Abs String Typ Term
    | App Term Term

data Value : Term -> Type where
    AbsVal : Value (Abs _ _ _)

Uninhabited (Value (Var _)) where
    uninhabited _ impossible

Uninhabited (Value (App _ _)) where
    uninhabited _ impossible

subst : String -> Term -> Term -> Term
subst x s (Var y) with (decEq x y) 
    | (Yes _) = s
    | (No _) = Var y
subst x s (Abs y ty t) with (decEq x y) 
    | (Yes _) = Abs x ty t
    | (No _) = Abs y ty (subst x s t)
subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)

data Eval : Term -> Term -> Type where
    EApp1 : Eval t1 t1' -> Eval (App t1 t2) (App t1' t2)
    EApp2 : Value v1 -> Eval t2 t2' -> Eval (App v1 t2) (App v1 t2')
    EAppAbs : Value v2 -> t1' = subst x v2 t1 -> Eval (App (Abs x ty t1) v2) t1'

Ctx : Type
Ctx = List (String, Typ)

data In : (String, Typ) -> Ctx -> Type where
    Here : In (x, ty) ((x, ty)::ctx)
    There : (x = y -> Void) -> In (y, ty1) ctx -> In (y, ty1) ((x, ty2)::ctx)

Uninhabited (In x []) where
    uninhabited _ impossible

inDrop : (x = y -> Void) -> In (x, tt1) ((y, tt2)::ctx) -> In (x, tt1) ctx
inDrop p Here = absurd (p Refl)
inDrop _ (There _ pi) = pi

lookup : (x : String) -> (ctx : Ctx) -> Dec (ty ** In (x, ty) ctx)
lookup _ [] = No (\ (_ ** pi) => uninhabited pi)
lookup x ((y, ty1) :: ctx) with (decEq x y)
    lookup x ((x, ty1) :: ctx) | (Yes Refl) = Yes (ty1 ** Here)
    | (No contra1) with (lookup x ctx) 
        | (Yes (ty ** pi)) = Yes (ty ** There (contra1 . sym) pi)
        | (No contra2) = No (\(ty1 ** pi1) => 
            contra2 (ty1 ** inDrop contra1 pi1))

Subset : {z : (String, Typ)} -> (ctx1, ctx2 : Ctx) -> Type
Subset {z = z} ctx1 ctx2 = In z ctx1 -> In z ctx2

subsetNil : Subset [] ctx
subsetNil _ impossible

subsetCons : ({z : (String, Typ)} -> Subset {z = z} ctx1 ctx2) -> Subset ((x, ty)::ctx1) ((x, ty)::ctx2)
subsetCons _ Here = Here
subsetCons ps (There p pi) = 
    There p (ps pi)

subsetDrop : Subset ((x, ty1)::(x, ty2)::ctx) ((x, ty1)::ctx)
subsetDrop Here = Here
subsetDrop (There p Here) = absurd (p Refl)
subsetDrop (There p (There _ pi)) = There p pi

subsetSwap : (x = y -> Void) -> Subset ((y, ty1)::(x, ty2)::ctx) ((x, ty2)::(y, ty1)::ctx)
subsetSwap p Here = There p Here
subsetSwap _ (There _ Here) = Here
subsetSwap _ (There p1 (There p2 pi)) = There p2 (There p1 pi)

inUniqueType : In (x, ty1) ctx -> In (x, ty2) ctx -> ty1 = ty2
inUniqueType Here Here = Refl
inUniqueType Here (There p _) = absurd (p Refl)
inUniqueType (There p _) Here = absurd (p Refl)
inUniqueType (There _ pi1) (There _ pi2) = inUniqueType pi1 pi2

data Typed : Ctx -> Term -> Typ -> Type where
    TVar : In (x, ty) ctx -> Typed ctx (Var x) ty
    TAbs : Typed ((x, ty1) :: ctx) t2 ty2 -> Typed ctx (Abs x ty1 t2) (Arrow ty1 ty2)
    TApp : Typed ctx t1 (Arrow ty1 ty2) -> Typed ctx t2 ty1 -> Typed ctx (App t1 t2) ty2

Uninhabited (Typed [] (Var _) _) where
    uninhabited (TVar _) impossible

typedChange : Typed ctx1 t ty -> ({z : (String, Typ)} -> Subset {z = z} ctx1 ctx2) -> Typed ctx2 t ty
typedChange (TVar pi) ps = TVar (ps pi)
typedChange (TAbs pt) ps = TAbs (typedChange pt (subsetCons ps))
typedChange (TApp pt1 pt2) ps = 
    let ih1 = typedChange pt1 ps in
    let ih2 = typedChange pt2 ps in
    TApp ih1 ih2

typedWeaken : Typed [] t ty -> Typed ctx t ty
typedWeaken pt = typedChange pt subsetNil
        
typedDrop : Typed ((x, ty1)::(x, ty2)::ctx) t ty -> Typed ((x, ty1)::ctx) t ty
typedDrop pt = typedChange pt subsetDrop
        
typedSwap : (x = y -> Void) -> Typed ((y, ty1)::(x, ty2)::ctx) t ty -> Typed ((x, ty2)::(y, ty1)::ctx) t ty
typedSwap pe pt = typedChange pt (subsetSwap pe)

typedUniqueType : (Typed ctx t ty1) -> (Typed ctx t ty2) -> ty1 = ty2
typedUniqueType (TVar pi1) (TVar pi2) = inUniqueType pi1 pi2
typedUniqueType (TAbs pt1) (TAbs pt2) with (typedUniqueType pt1 pt2)
    | Refl = Refl
typedUniqueType (TApp pt1 _) (TApp pt2 _) with (typedUniqueType pt1 pt2)
    | Refl = Refl

progress : (t : Term) -> Typed [] t ty -> Either (Value t) (t' ** Eval t t')
progress (Var _) (TVar _) impossible
progress (Abs _ _ _) (TAbs _) = Left AbsVal
progress (App t1 t2) (TApp pt1 pt2) with (progress t1 pt1) 
    | (Right (t1' ** pe)) = Right ((App t1' t2) ** EApp1 pe)
    | (Left pv1) with (progress t2 pt2) 
        | (Right (t2' ** pe)) = Right ((App t1 t2') ** EApp2 pv1 pe)    
        | (Left pv2) with (pv1)
            progress (App (Abs x _ t) t2) _ | _ | (Left pv2) | AbsVal = 
                Right (subst x t2 t ** EAppAbs pv2 Refl)

substyyped : {x : String} -> {s : Term} -> (t : Term) -> Typed [] s ty1 -> Typed ((x, ty1) :: ctx) t ty2 -> Typed ctx (subst x s t) ty2
substyyped {x=x} (Var y) pt1 pt2 with (decEq x y) 
    substyyped _ pt1 (TVar Here) | (Yes Refl) = typedWeaken pt1
    substyyped _ _ (TVar (There peq _)) | (Yes Refl) = absurd (peq Refl)
    substyyped _ _ (TVar Here) | (No contra) = absurd (contra Refl)
    substyyped _ _ (TVar (There _ pi)) | (No contra) = TVar pi
substyyped {x=x} (Abs y _ t) pt1 (TAbs pt2) with (decEq x y) 
    substyyped _ _ (TAbs pt2) | (Yes Refl) = TAbs (typedDrop pt2)
    substyyped (Abs _ _ t) pt1 (TAbs pt2) | (No pe) = 
        let ih = substyyped t pt1 (typedSwap pe pt2) in 
        TAbs ih
substyyped (App t1 t2) pt1 (TApp pt2 pt3) = 
    let ih1 = substyyped t1 pt1 pt2 in
    let ih2 = substyyped t2 pt1 pt3 in
    TApp ih1 ih2

preservation : (t : Term) -> Typed [] t ty -> Eval t t' -> Typed [] t' ty
preservation (App t1 _) (TApp pt1 pt2) (EApp1 pe) = 
    TApp (preservation t1 pt1 pe) pt2
preservation (App (Abs _ _ _) t2) (TApp pt1 pt2) (EApp2 AbsVal pe) =
    TApp pt1 (preservation t2 pt2 pe)
preservation (App (Abs _ _ t1) _) (TApp (TAbs pt1) pt2) (EAppAbs _ peq) = 
    rewrite peq in
    substyyped t1 pt2 pt1

data LongEval : Term -> Term -> Type where
    LValue : Value v -> LongEval v v
    LEval : Eval t1 t2 -> LongEval t2 t3 -> LongEval t1 t3

partial
eval' : (t : Term) -> Typed [] t ty -> (t' ** LongEval t t') 
eval' t pt with (progress t pt)
    | (Left vt) = (t ** LValue vt)
    | (Right (t' ** pe)) = 
        let (t2 ** ple) = eval' t' (preservation t pt pe) in
        (t2 ** LEval pe ple)
     
typecheckLemma : Typed ctx (App t1 t2) ty -> Typed ctx t1 (Arrow ty1 ty2) -> Typed ctx t2 ty3 -> ty1 = ty3
typecheckLemma (TApp pt1 pt2) pt3 pt4 with (typedUniqueType pt1 pt3) 
    | Refl with (typedUniqueType pt2 pt4) 
        | Refl = Refl

typecheck : (t : Term) -> (ctx : Ctx) -> Dec (ty ** Typed ctx t ty)
typecheck (Var x) ctx with (lookup x ctx)
    | (Yes (ty ** pi)) = Yes (ty ** TVar pi)
    | (No contra) = No (\(ty ** TVar pi) => contra (ty ** pi))
typecheck (Abs x ty1 t) ctx with (typecheck t ((x, ty1)::ctx))
    | (Yes (ty2 ** pt)) = Yes (Arrow ty1 ty2 ** TAbs pt)
    | (No contra) = No (\(Arrow _ ty4 ** TAbs pt) => contra (ty4 ** pt))
typecheck (App t1 t2) ctx with (typecheck t1 ctx) 
    | (No contra) = No (\(ty ** TApp pt1 _) => contra (Arrow _ ty ** pt1))
    | (Yes (Base ** pt)) = 
        No (\(_ ** TApp pt1 _) => uninhabited (typedUniqueType pt pt1))
    | (Yes (Arrow ty1 ty2 ** pt1)) with (typecheck t2 ctx)
        | (No contra) = No (\(_ ** TApp _ pt2) => contra (_ ** pt2))
        | (Yes (ty3 ** pt2)) with (decEq ty1 ty3)
            | (No contra) = No (\(ty ** pt3) => 
                contra (typecheckLemma pt3 pt1 pt2))
            | (Yes p) = Yes (ty2 ** TApp pt1 (rewrite p in pt2))

partial
eval : (t : Term) -> Either ((ty ** Typed [] t ty), (t' ** LongEval t t')) ((ty ** Typed [] t ty) -> Void)
eval t with (typecheck t []) 
    | (Yes (ty ** pt)) = Left ((ty ** pt), (eval' t pt))
    | (No contra) = Right contra
