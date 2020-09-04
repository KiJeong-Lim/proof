Require Export List.

Module CoC.

  Import ListNotations.

  Section preliminary.

    Fixpoint predecessor (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n'
      end
    .

    Inductive Ordering : Set :=
    | LT : Ordering
    | EQ : Ordering
    | GT : Ordering
    .

    Fixpoint compare (lhs : nat) (rhs : nat) : Ordering :=
      match lhs, rhs with
      | 0, 0 => EQ
      | S lhs', S rhs' => compare lhs' rhs'
      | 0, S rhs' => GT
      | S lhs', 0 => LT
      end
    .

  End preliminary.

  Section Syntax.
  
    Inductive ObjSort : Set :=
    | OSKind : ObjSort
    | OSProp : ObjSort
    .

    Inductive ObjTerm : Set :=
    | OTSort : ObjSort -> ObjTerm
    | OTIdx : nat -> ObjTerm
    | OTAbs : ObjTerm -> ObjTerm -> ObjTerm
    | OTApp : ObjTerm -> ObjTerm -> ObjTerm
    | OTProd : ObjTerm -> ObjTerm -> ObjTerm
    .  
  
    Definition ObjEnv := list ObjTerm.

  End Syntax.

  Section ReductionRule.

    Fixpoint lift (t : ObjTerm) (n : nat) (k : nat) : ObjTerm :=
      match t with
      | OTSort s => OTSort s
      | OTIdx i =>
        match compare i k with
        | LT | EQ => OTIdx (i + k)
        | GT => OTIdx i
        end
      | OTAbs t1 t2 => OTAbs (lift t1 n k) (lift t2 n (S k))
      | OTApp t1 t2 => OTApp (lift t1 n k) (lift t2 n k)
      | OTProd t1 t2 => OTProd (lift t1 n k) (lift t2 n (S k))
      end
    .

    Fixpoint subst (t : ObjTerm) (k : nat) (t' : ObjTerm) : ObjTerm :=
      match t with
      | OTSort s => OTSort s
      | OTIdx i =>
        match compare i k with
        | LT => OTIdx i
        | EQ => lift t' k 0
        | GT => OTIdx (predecessor i)
        end
      | OTAbs t1 t2 => OTAbs (subst t1 k t') (subst t2 (S k) t')
      | OTApp t1 t2 => OTApp (subst t1 k t') (subst t2 k t')
      | OTProd t1 t2 => OTProd (subst t1 k t') (subst t2 (S k) t')
      end
    .

    Inductive BetaReducesTo : ObjTerm -> ObjTerm -> Prop :=
    | BR_BETA :
      forall _T _M _N : ObjTerm,
      BetaReducesTo (OTApp (OTAbs _T _M) _N) (subst _M 0 _N)
    | BR_ABS_L :
      forall _M _M' _N : ObjTerm,
      BetaReducesTo _M _M' ->
      BetaReducesTo (OTAbs _M _N) (OTAbs _M' _N)
    | BR_ABS_R :
      forall _M _N _N' : ObjTerm,
      BetaReducesTo _N _N' ->
      BetaReducesTo (OTAbs _M _N) (OTAbs _M _N')
    | BR_APP_L :
      forall _M1 _M2 _N1 : ObjTerm,
      BetaReducesTo _M1 _N1 ->
      BetaReducesTo (OTApp _M1 _M2) (OTApp _N1 _M2)
    | BR_APP_R :
      forall _M1 _M2 _N2 : ObjTerm,
      BetaReducesTo _M2 _N2 ->
      BetaReducesTo (OTApp _M1 _M2) (OTApp _M1 _N2)
    | BR_PROD_L :
      forall _M1 _N1 _M2 : ObjTerm,
      BetaReducesTo _M1 _N1 ->
      BetaReducesTo (OTProd _M1 _M2) (OTProd _N1 _M2)
    | BR_PROD_R :
      forall _M1 _M2 _N2 : ObjTerm,
      BetaReducesTo _M2 _N2 ->
      BetaReducesTo (OTProd _M1 _M2) (OTProd _M1 _N2)
    .

    

  End ReductionRule.
  

End CoC.