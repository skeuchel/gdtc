Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Section Lambda.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* Function Types. *)
  Inductive LType (A : Set) : Set :=
    TArrow : A -> A -> LType A.

  Definition LType_fmap : forall (A B : Set) (f : A -> B), 
    LType A -> LType B := 
    fun A B f e => 
      match e with 
        | TArrow t1 t2 => TArrow _ (f t1) (f t2)
      end.

  Global Instance LType_Functor : Functor LType :=
    {| fmap := LType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Sub_LType_D  : LType :<: D}.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D _ _}.
  
  Definition tarrow' (t1 t2 : DType) := inject' (TArrow _ t1 t2).
  Definition tarrow (t1 t2 : Fix D) 
    {UP'_t1 : Universal_Property'_fold t1}
    {UP'_t2 : Universal_Property'_fold t2}
    : Fix D := proj1_sig (tarrow' (exist _ t1 UP'_t1) (exist _ t2 UP'_t2)).

   Global Instance UP'_tarrow (t1 t2 : Fix D) 
     {UP'_t1 : Universal_Property'_fold t1}
     {UP'_t2 : Universal_Property'_fold t2}
     : Universal_Property'_fold (tarrow t1 t2) := 
     proj2_sig (tarrow' (exist _ t1 UP'_t1) (exist _ t2 UP'_t2)).

  (* Induction Principle for Arrow Types. *)
  Definition ind_alg_LType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop) 
    (H : forall t1 t2
      (IHt1 : UP'_P P t1) 
      (IHt2 : UP'_P P t2),
      UP'_P P (@tarrow _ _ (proj1_sig IHt1) (proj1_sig IHt2)))
    (d : LType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TArrow t1 t2 => exist _ _ (H (proj1_sig t1) (proj1_sig t2) (proj2_sig t1) (proj2_sig t2))
    end.

  (* Algebra for testing type equality. *)

  Definition isTArrow : DType -> option (_ * _) :=
    fun typ =>
      match project (proj1_sig typ) with
       | Some (TArrow t1 t2)  => Some (t1, t2)
       | None                 => None
      end.

  Definition eq_TArrowR := prod ((eq_DTypeR D) -> (eq_DTypeR D) -> bool) (sig (Universal_Property'_fold (F := D))).
  Inductive eq_TArrowName := eq_tarrowname.
  Context {eq_TArrow_D : forall T, FAlgebra eq_TArrowName T eq_TArrowR D}.
  Definition eq_TArrow  := mfold _ (fun _ => @f_algebra _ _ _ _ (eq_TArrow_D _)).
  
  Definition LType_eq_TArrow (R : Set) (rec : R -> eq_TArrowR) 
    (e : LType R) : eq_TArrowR := 
    match e with
      | TArrow t1 t2 => (fun t1' t2' => 
        andb (t1' (snd (rec t1))) (t2' (snd (rec t2))),
        inject' (TArrow _ (snd (rec t1)) (snd (rec t2))))
    end.
  Global Instance MAlgebra_eq_TArrow_LType T:
    FAlgebra eq_TArrowName T eq_TArrowR LType | 4 :=
      {| f_algebra := LType_eq_TArrow T|}.

  Context {WF_TArrow_eq_DT : forall T, @WF_FAlgebra eq_TArrowName T _ _ _
    Sub_LType_D (MAlgebra_eq_TArrow_LType T) (eq_TArrow_D _)}. 

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.

  Definition eq_TArrow_eq_P (d : Fix D) (d_UP' : Universal_Property'_fold d) :=
    proj1_sig (snd (eq_TArrow d)) = d /\
    forall t1 t2, fst (eq_TArrow d) (eq_DType _ (proj1_sig t1)) (eq_DType _ (proj1_sig t2)) = true -> 
      (forall d1 : Names.DType D, eq_DType D (proj1_sig t1) d1 = true -> proj1_sig t1 = proj1_sig d1) -> 
      (forall d2 : Names.DType D, eq_DType D (proj1_sig t2) d2 = true -> proj1_sig t2 = proj1_sig d2) -> 
      d = proj1_sig (tarrow' t1 t2).
  Inductive eq_TArrow_eqName := eq_tarrow_eqname.
  Context {eq_TArrow_eq_DT : PAlgebra eq_TArrow_eqName (sig (UP'_P eq_TArrow_eq_P)) D}.
  Variable WF_Ind_TArrow_eq_D : WF_Ind eq_TArrow_eq_DT.
  Lemma eq_TArrow_eq : forall (d1 : DType), eq_TArrow_eq_P (proj1_sig d1) (proj2_sig d1).
    intro; eapply (proj2_sig (Ind (P := UP'_P eq_TArrow_eq_P) _ (proj2_sig d1))).
  Qed.

  Global Instance PAlgebra_eq_TArrow_eq_LType :
    PAlgebra eq_TArrow_eqName (sig (UP'_P eq_TArrow_eq_P)) LType.
    constructor; unfold Algebra; intros.
    apply ind_alg_LType; try assumption; intros.
    econstructor; unfold eq_TArrow_eq_P; intros; split.
    unfold eq_TArrow, mfold, tarrow at 1, tarrow', inject'; simpl.
    rewrite wf_functor; simpl; unfold in_t; 
      rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)); simpl;
        rewrite wf_functor; simpl.
    destruct IHt1 as [UP'_t1 [eq_t1 t1']]; destruct IHt2 as [UP'_t2 [eq_t2 t2']].
    unfold tarrow; simpl; rewrite wf_functor; simpl.    
    rewrite <- eq_t1 at -1; rewrite <- eq_t2 at -1; reflexivity.
    intros; unfold eq_TArrow, mfold, tarrow, tarrow', inject' in H0; simpl in H0.
    repeat rewrite wf_functor in H0; simpl in H0; unfold in_t in H0; 
      rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)) in H0; 
        simpl in H0.
    destruct (andb_true_eq _ _ (sym_eq H0)).
    unfold tarrow; simpl; repeat rewrite wf_functor; simpl.
    rewrite (H1 _ (sym_eq H3)), (H2 _ (sym_eq H4)).
    destruct IHt1 as [UP'_t1 [eq_t1 t1']]; destruct IHt2 as [UP'_t2 [eq_t2 t2']].
    rewrite <- eq_t1 at 1; rewrite <- eq_t2 at 1; reflexivity.
  Defined.

  Definition Default_eq_TArrow {D'}
    {Fun_D : Functor D'}
    {sub_D'_D : D' :<: D}
    (R : Set) (rec : R -> eq_TArrowR) 
    (e : D' R) : eq_TArrowR := 
    (fun _ _ => false, in_t_UP' _ _ (@inj _ _ sub_D'_D _ (fmap (fun r => snd (rec r)) e))).

  Definition LType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D) 
    (e : LType R) : eq_DTypeR D :=
    match e with 
      | TArrow t1 t2 => fun t3 => (fst (eq_TArrow (proj1_sig t3))) (rec t1) (rec t2)
    end.

  Global Instance MAlgebra_eq_DType_LType T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) LType :=
    {| f_algebra := LType_eq_DType T|}.

  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_LType_D (MAlgebra_eq_DType_LType T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_DType_eq_LType :
    PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) LType.
    constructor; unfold Algebra; intros.
    apply ind_alg_LType; try assumption.
    intros; econstructor; unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tarrow, tarrow', inject' in H0; simpl in H0;
      repeat rewrite wf_functor in H0; simpl in H0; unfold in_t in H0. 
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H0; simpl in H0.
    destruct IHt1 as [UP'_t1 eq_t1]; destruct IHt2 as [UP'_t2 eq_t2].
    unfold eq_DType_eq_P in eq_t1, eq_t2.
    apply sym_eq; apply eq_TArrow_eq; eauto.
  Defined.

  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D}.
  Variable WF_Ind_DType_eq_D : WF_Ind eq_DType_eq_DT.

  (* End type equality section. *)


  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Lambda Expressions *)
  Inductive Lambda (A E : Set) : Set :=
  | Var : A -> Lambda A E
  | App : E -> E -> Lambda A E
  | Lam : DType -> (A -> E) -> Lambda A E.

  (** Functor Instance **)

  Definition fmapLambda {A} : forall {X Y: Set}, (X -> Y) -> (Lambda A X -> Lambda A Y):=
    fun _ _ f e =>
      match e with
       | Var a      => Var _ _ a
       | App e1 e2  => App _ _ (f e1) (f e2)
       | Lam t g    => Lam _ _ t (fun a => f (g a))
      end.

  Global Instance LambdaFunctor A : Functor (Lambda A) := 
  {| fmap := fmapLambda
   |}.
  (* fmap fusion *)
  intros. destruct a; unfold fmapLambda; reflexivity.
  (* fmap id *)
  intros; destruct a; unfold fmapLambda. 
     reflexivity. reflexivity. unfold id. unfold id.
     assert ((fun x => a x) = a).
       apply functional_extensionality; intro. reflexivity.
    rewrite H. reflexivity.
  Defined.

  Variable F : Set -> Set -> Set.
  Context {Sub_Lambda_F : forall A : Set, Lambda A :<: F A}.
  Context {Fun_F : forall A, Functor (F A)}.
  Definition Exp (A : Set) := Exp (F A).

  (* Constructors + Universal Property. *)

  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_F A) _ _}.

  Definition var' {A : Set} (a : A) : Exp A := inject' (Var _ _ a).
  Definition var {A : Set} (a : A) : Fix (F A) := proj1_sig (var' a).
  Global Instance UP'_var {A : Set} (a : A) : 
    Universal_Property'_fold (var a) := proj2_sig (var' a).

  Definition app' {A : Set} (e1 e2 : Exp A) :=
    inject' (App _ _ e1 e2).
  Definition app {A : Set} 
    (e1 e2 : Fix (F A))
    {e1_UP' : Universal_Property'_fold e1}
    {e2_UP' : Universal_Property'_fold e2}
    : 
    Fix (F A) := proj1_sig (app' (exist _ _ e1_UP') (exist _ _ e2_UP')).
  
  Global Instance UP'_app {A : Set} (e1 e2 : Fix (F A))
    {e1_UP' : Universal_Property'_fold e1}
    {e2_UP' : Universal_Property'_fold e2}
    :
    Universal_Property'_fold (app e1 e2) :=
    proj2_sig (app' (exist _ _ e1_UP') (exist _ _ e2_UP')).
  
  Definition lam' {A : Set} 
    (t1 : DType) 
    (f : A -> sig (Universal_Property'_fold (F := F A))) 
    : 
    Exp A := inject' (Lam _ _ t1 f).
  Definition lam {A : Set}
    (t1 : DType) 
    (f : A -> Fix (F A)) 
    {f_UP' : forall a, Universal_Property'_fold (f a)} 
    :
    Fix (F A) := proj1_sig (lam' t1 (fun a => exist _ _ (f_UP' a))).
  
   Global Instance UP'_lam {A : Set} 
     (t1 : DType) 
     (f : A -> Fix (F A)) 
     {f_UP' : forall a, Universal_Property'_fold (f a)}
     :
     Universal_Property'_fold (lam t1 f) := proj2_sig (lam' t1 (fun a => exist _ _ (f_UP' a))).

  (* Induction Principle for Lambda. *)
  Definition ind_alg_Lambda {A : Set} 
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop) 
    (H : forall x, UP'_P P (var x)) 
    (H0 : forall e1 e2
      (IHe1 : UP'_P P e1) 
      (IHe2 : UP'_P P e2),
      UP'_P P (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)))
    (H1 : forall t1 f
      (IHf : forall a, UP'_P P (f a)),
      UP'_P P (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))))
    (e : Lambda A (sig (UP'_P P))) : sig (UP'_P P) :=
    match e with
      | Var x => exist _ _ (H x)
      | App e1 e2 => 
        exist _ _ (H0 (proj1_sig e1) (proj1_sig e2) (proj2_sig e1) (proj2_sig e2))
      | Lam t1 f => exist _ _ (H1 t1 (fun a => proj1_sig (f a)) (fun a => proj2_sig (f a)))
    end.

  (* Typing for Lambda Expressions. *)
  
  Definition Lambda_typeof (R : Set) (rec : R -> typeofR D) (e : Lambda (typeofR D) R) : typeofR D:= 
  match e with
    | Var v => v
    | App e1 e2 => 
      match (rec e1, rec e2) with
                   | (Some t1, Some t3) => 
                     match (isTArrow t1) with 
                       | Some (t1, t2) => 
                         if (eq_DType (eq_DType_DT := eq_DType_DT) D (proj1_sig t1) t3) then Some t2 else None
                       | _ => None
                     end
                   | _ => None
                 end
    | Lam t1 f => 
      match rec (f (Some t1)) with
                   | Some t2 => Some (inject' (TArrow _ t1 t2))
                   | _ => None
      end
  end.

  Global Instance MAlgebra_typeof_Lambda T:
    FAlgebra TypeofName T (typeofR D) (Lambda (typeofR D)) :=
    {| f_algebra := Lambda_typeof T|}.

  (* Function Values. *)

  Inductive ClosValue (A : Set) : Set :=
  | Clos : Exp nat -> Env A -> ClosValue A.

  Definition Clos_fmap : forall (A B : Set) (f : A -> B), 
    ClosValue A -> ClosValue B := fun A B f e => 
      match e with 
        | Clos f' env => Clos _ f' (map f env)
      end.

   Global Instance Clos_Functor : Functor ClosValue :=
     {| fmap := Clos_fmap |}.
     destruct a; simpl.
     assert (map g (map f e0) = map (fun e1 : A => g (f e1)) e0) as eq_map by 
       (clear; induction e0; simpl; eauto; erewrite IHe0; reflexivity).
     rewrite eq_map; reflexivity.
     (* fmap_id *)
     destruct a. unfold Clos_fmap. rewrite map_id. reflexivity.
   Defined.

  Variable V : Set -> Set.
  Context {Sub_ClosValue_V : ClosValue :<: V}.
  Context {Fun_V : Functor V}.
  Definition Value := Value V.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_ClosValue_V : WF_Functor _ _ (Sub_ClosValue_V) _ _}.

  Definition closure' f env : Value := inject' (Clos _ f env).
  Definition closure 
    (f : Fix (F nat))
    {f_UP' : Universal_Property'_fold f}
    (env : Env (sig (Universal_Property'_fold (F := V)))) 
      : 
      Fix V := proj1_sig (closure' (exist _ _ f_UP') env).

  Global Instance UP'_closure 
    (f : Fix (F nat))
    {f_UP' : Universal_Property'_fold f}
    (env : Env (sig (Universal_Property'_fold (F := V)))) 
     : 
     Universal_Property'_fold (closure f env) := 
     proj2_sig (closure' (exist _ _ f_UP') env).

  (* Constructor Testing for Function Values. *)

  Definition isClos : Fix V -> option _ :=
    fun exp =>
     match project exp with
      | Some (Clos f env)  => Some (f, env)
      | None             => None
     end.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Context {Sub_BotValue_V : BotValue :<: V}.
   Definition bot' : Value := bot' _.

  Definition Lambda_eval : Mixin (Exp nat) (Lambda nat) (evalR V) :=
    fun rec e => 
     match e with 
       | Var v => fun env => 
         match lookup env v with 
           | Some y => y
           | None => stuck' 20
         end
       | App e1 e2 => fun env => 
         let reced := (rec e1 env) in
           match isClos (proj1_sig reced) with
             | Some (f, env') => rec f (insert _ (rec e2 env) env')
             | None => if isBot _ (proj1_sig reced) then bot' else stuck' 5
           end
       | Lam t1 f => fun env => closure' (f (length env)) env
     end.
   
  Global Instance MAlgebra_eval_Lambda :
    FAlgebra EvalName (Exp nat) (evalR V) (Lambda nat) :=
    {| f_algebra := Lambda_eval|}.
  
  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import String.
  Require Import Ascii.

  Global Instance MAlgebra_DTypePrint_AType T:
    FAlgebra DTypePrintName T DTypePrintR LType :=
    {| f_algebra := fun rec e => 
      match e with 
        TArrow t1 t2 => append "(" ((rec t1) ++ " -> " ++ (rec t2) ++ ")")
      end
      |}.

  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR D}.

   Definition Lambda_ExpPrint (R : Set) (rec : R -> ExpPrintR) 
     (e : Lambda nat R) : ExpPrintR := 
     match e with 
       | Var v => fun n => append "x" (String (ascii_of_nat (v)) EmptyString)
       | App e1 e2 => fun n => append "(" ((rec e1 n) ++ ") @ (" ++ (rec e2 n) ++ ")")
       | Lam t1 f => fun n => append "\x" ((String (ascii_of_nat n) EmptyString) ++
         " : " ++ (DTypePrint _ (proj1_sig t1)) ++ ". " ++ 
         (rec (f n) (S n)) ++ ")")
     end.

   Global Instance MAlgebra_Print_Lambda T :
     FAlgebra ExpPrintName T ExpPrintR (Lambda nat) :=
     {| f_algebra := Lambda_ExpPrint T|}.
   
   Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR (F nat)}.

    Global Instance MAlgebra_ValuePrint_AType T:
    FAlgebra ValuePrintName T ValuePrintR ClosValue :=
    {| f_algebra := fun rec e => 
      match e with 
        | Clos f _ => append "\x0. " (ExpPrint _ (proj1_sig f))
      end |}.

  (* ============================================== *)
  (* SUBVALUE RELATION FOR LAMBDAS                  *)
  (* ============================================== *)

    Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.

    Inductive SubValue_Clos (A : SubValue_i V -> Prop) : SubValue_i V -> Prop :=
      SV_Clos : forall f f' env env' v v', 
        proj1_sig f = proj1_sig f' -> 
        P2_Env (fun e e' : Value => A (mk_SubValue_i V e e')) env env' -> 
        proj1_sig v = proj1_sig (closure' f env) ->
        proj1_sig v' = proj1_sig (closure' f' env') -> 
        SubValue_Clos A (mk_SubValue_i _ v v').

    Definition ind_alg_SV_Clos (P : SubValue_i V -> Prop) 
      (P' : Env Value -> Env Value -> Prop)
      (H : forall f f' env env' v v', 
        proj1_sig f = proj1_sig f' -> 
        P' env env' -> 
        proj1_sig v = proj1_sig (closure' f env) ->
        proj1_sig v' = proj1_sig (closure' f' env') ->         
        P (mk_SubValue_i _ v v'))
      (H0 : P' nil nil)
      (H1 : forall i env env', P i -> P' env env' -> 
        P' (sv_a _ i :: env) (sv_b _ i :: env'))
      i (e : SubValue_Clos P i) : P i :=
      match e in SubValue_Clos _ i return P i with
        | SV_Clos f f' env env' v v' f_eq Sub_env_env' v_eq v'_eq => 
          H f f' env env' v v' f_eq 
          ((fix P_Env_ind' (env : Env _) (env' : Env _) 
            (P_env_env' : P2_Env (fun e e' => P (mk_SubValue_i _ e e')) env env') := 
            match P_env_env' in P2_Env _ As Bs return P' As Bs with
              | P2_Nil => H0
              | P2_Cons a b As Bs P_a_b P_As_Bs => 
                H1 (mk_SubValue_i _ a b) As Bs P_a_b (P_Env_ind' _ _ P_As_Bs)
            end) _ _ Sub_env_env') v_eq v'_eq
      end.

    Definition SV_Clos_ifmap (A B : SubValue_i V -> Prop) i (g : forall i, A i -> B i)
      (SV_a : SubValue_Clos A i) : SubValue_Clos B i :=
      match SV_a in SubValue_Clos _ i return SubValue_Clos B i with
        | SV_Clos f f' env env' v v' f_eq Sub_env_env' v_eq v'_eq => 
          SV_Clos B f f' env env' v v' f_eq 
          ((fix P_Env_ind' (env : Env _) (env' : Env _) 
            (P_env_env' : P2_Env (fun e e' => A (mk_SubValue_i _ e e')) env env') := 
            match P_env_env' in P2_Env _ As Bs return P2_Env (fun e e' => B (mk_SubValue_i _ e e')) As Bs with
              | P2_Nil => P2_Nil _ 
              | P2_Cons a b As Bs P_a_b P_As_Bs => 
                P2_Cons (fun e e' : Names.Value V => B {| sv_a := e; sv_b := e' |}) 
                a b As Bs (g (mk_SubValue_i _ a b) P_a_b) (P_Env_ind' _ _ P_As_Bs)
            end) _ _ Sub_env_env') v_eq v'_eq
      end.

    Global Instance iFun_SV_Clos : iFunctor SubValue_Clos.
      constructor 1 with (ifmap := SV_Clos_ifmap).
      destruct a; simpl; intros.
      apply (f_equal (fun P_env' => SV_Clos C f0 f' env env' v v' e P_env' e0 e1)).
      clear; revert env env' p; eapply P2_Env_ind'; simpl; intros; congruence.
      destruct a; simpl; intros.
      apply (f_equal (fun P_env' => SV_Clos A f f' env env' v v' e P_env' e0 e1)).
      clear; revert env env' p; eapply P2_Env_ind'; simpl; intros.
      reflexivity.
      unfold id.
      rewrite <- H at -1.
      apply (f_equal (fun P_env' => 
        P2_Cons (fun e e' : Names.Value V => A {| sv_a := e; sv_b := e' |}) _ _ _ _ P_a_b P_env')).
      reflexivity.
    Defined.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

    Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
    Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Lambda nat) (F nat)
      (Sub_Lambda_F nat) (MAlgebra_eval_Lambda) (eval_F)}.
    
   (* Continuity of Evaluation. *)

    Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
    Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.
    Context {Sub_SV_Clos_SV : Sub_iFunctor SubValue_Clos SV}.
    
  (* Lit case. *)
    
    Lemma eval_continuous_Exp_H : forall x, 
      UP'_P (eval_continuous_Exp_P V (F nat) SV) (var x).
      unfold eval_continuous_Exp_P; econstructor; simpl; intros;
        eauto with typeclass_instances.
      unfold beval, mfold, var; simpl; repeat rewrite wf_functor; simpl.
      rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      caseEq (@lookup Value gamma x); unfold Value in *|-*;
        rewrite H2.
      destruct (P2_Env_lookup _ _ _ _ _ H0 _ _ H2) as [v' [lookup_v' Sub_v_v']].
      unfold Value; rewrite lookup_v'; eauto.
      unfold Value; rewrite (P2_Env_Nlookup _ _ _ _ _ H0 _ H2).
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    Qed.
    
  (* Lambda case. *)
    
    Lemma eval_continuous_Exp_H1 : forall t1 f
      (IHf : forall a, UP'_P (eval_continuous_Exp_P V (F nat) SV) (f a)), 
      UP'_P (eval_continuous_Exp_P V (F nat) SV) 
      (@lam _ t1 _ (fun a => (proj1_sig (IHf a)))).
      unfold eval_continuous_Exp_P; econstructor; simpl; intros.
      unfold beval, mfold, lam; simpl; repeat rewrite wf_functor;
        simpl; rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F )); simpl.
      eapply (inject_i (subGF := Sub_SV_Clos_SV)); econstructor; eauto.
      simpl; repeat rewrite wf_functor; simpl.
      assert (f (Datatypes.length gamma) = (f (Datatypes.length gamma'))) as f_eq by
        (rewrite (P2_Env_length _ _ _ _ _ H0); reflexivity).
      rewrite f_eq; eauto.
    Qed.
    
  (* App case. *)
    
    Context {Dis_Clos_Bot : Distinct_Sub_Functor _ Sub_ClosValue_V Sub_BotValue_V}.
    Context {iFun_SV : iFunctor SV}.

    Global Instance SV_proj1_b_Clos : 
      iPAlgebra SV_proj1_b_Name (SV_proj1_b_P _ SV) SubValue_Clos.
      econstructor; intros.
      unfold iAlgebra; intros.
      eapply ind_alg_SV_Clos with (P' := fun env env' => Sub_Environment V SV env env'); 
        try eassumption; intros.
      unfold SV_proj1_b_P; intros; simpl.
      apply (inject_i (subGF := Sub_SV_Clos_SV));
        econstructor; eauto.
      simpl in *|-*.
      congruence.
      constructor.
      constructor; eauto.
      unfold SV_proj1_b_P in H0.
      destruct i0; simpl.
      destruct sv_b as [sv_b1 sv_b2].
      apply (H0 sv_b1 sv_b2 (refl_equal _)).
    Qed.

    Global Instance SV_proj1_a_Clos : 
      iPAlgebra SV_proj1_a_Name (SV_proj1_a_P _ SV) SubValue_Clos.
      econstructor; intros.
      unfold iAlgebra; intros.
      eapply ind_alg_SV_Clos with (P' := fun env env' => Sub_Environment V SV env env'); 
        try eassumption; intros.
      unfold SV_proj1_a_P; intros; simpl.
      apply (inject_i (subGF := Sub_SV_Clos_SV));
        econstructor; eauto.
      simpl in *|-*.
      congruence.
      constructor.
      constructor; eauto.
      unfold SV_proj1_a_P in H0.
      destruct i0; simpl.
      destruct sv_a as [sv_a1 sv_a2].
      apply (H0 sv_a1 sv_a2 (refl_equal _)).
    Qed.

    Global Instance SV_invertBot_Clos : 
      iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SubValue_Clos.
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros.
      inversion H; subst; simpl.
      unfold SV_invertBot_P; intros.
      simpl in H4; rewrite H3 in H4.
      unfold closure', bot, Names.bot, inject' in H4.
      elimtype False; eapply (inject_discriminate  Dis_Clos_Bot).
      unfold inject; apply H4.
    Qed.

    Context {SV_proj1_b_SV :
      iPAlgebra SV_proj1_b_Name (SV_proj1_b_P _ SV) SV}.    
    Context {SV_proj1_a_SV :
      iPAlgebra SV_proj1_a_Name (SV_proj1_a_P _ SV) SV}.    
    Context {SV_invertBot_SV :
      iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.    

  (* Inversion principles for function SubValues. *)
    Definition SV_invertClos_P (i : SubValue_i V) := 
      SubValue _ SV i /\
      forall f env, proj1_sig (sv_a _ i) = proj1_sig (closure' f env) -> 
        exists f', exists env', proj1_sig f' = proj1_sig f /\
          proj1_sig (sv_b _ i) = proj1_sig (closure' f' env') 
          /\ Sub_Environment V SV env env'.
    
    Inductive SV_invertClos_Name := ece_invertclosure_name.
    Context {SV_invertClos_SV :
      iPAlgebra SV_invertClos_Name SV_invertClos_P SV}.    
    
    Global Instance SV_invertClos_refl : 
      iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertClos_P.
      inversion H; subst; simpl; intros.
      split; intros.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; simpl; eauto.
      repeat eexists _; repeat split; eauto.
      rewrite <- H0; eauto.
      eapply Sub_Environment_refl; eauto.
    Defined.

    Global Instance SV_invertClos_Clos : 
      iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_Clos).
      econstructor; intros.
      unfold iAlgebra; intros.
      eapply ind_alg_SV_Clos with (P' := fun env env' =>
        forall env'',
        map (@proj1_sig _ _) env'' = map (@proj1_sig _ _) env -> Sub_Environment V SV env'' env' ); 
      try eassumption; intros.
      unfold SV_invertClos_P; intros.
      simpl in *|-*.
      apply (f_equal out_t) in H2.
      repeat rewrite out_in_inverse in H2.
      repeat rewrite wf_functor in H2; simpl in H2.
      apply (f_equal (prj (Sub_Functor := Sub_ClosValue_V))) in H2.
      repeat rewrite prj_inj in H2; injection H2; intros; 
        subst.
      split; intros.
      apply (inject_i (subGF := Sub_SV_Clos_SV)); econstructor; eauto.
      eapply H1; reflexivity.
      generalize (inj_prj _ _ H2); intros H5; apply (f_equal in_t) in H5.
      rewrite in_out_inverse in H5; simpl.
      rewrite wf_functor; simpl; assumption.
      exact (proj2_sig v).
      simpl; eauto.
      exists f'; exists env'; repeat split; eauto.
      rewrite H5 in H4; rewrite out_in_inverse, wf_functor, prj_inj in H4;
        simpl in H4; injection H4; intros; congruence.
      rewrite H5 in H4; rewrite out_in_inverse, wf_functor, prj_inj in H4;
        simpl in H4; injection H4; intros; subst; eauto.
      destruct env''; try discriminate; constructor.
      unfold SV_invertClos_P in H0.
      destruct env''; try discriminate; injection H2; intros; subst; 
        constructor; eauto.
      destruct H0 as [i' H0]; destruct s; eapply (SV_proj1_a _ _ _ i0); eauto.
      eapply H1; eauto.
    Qed.
  
    Variable Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV.

    Global Instance SV_invertClos_Bot : 
      iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertClos_P.
      inversion H; subst; simpl; intros.
      split; intros.
      apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
      elimtype False.
      rewrite H0 in H1.
      eapply (inject_discriminate Dis_Clos_Bot); unfold inject in *|-*; simpl in *|-*; eauto.
    Defined.

    Definition SV_invertClos := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertClos_SV)).

    Definition SV_invertClos'_P (i : SubValue_i V) := 
      SubValue _ SV i /\
      forall f env, proj1_sig (sv_b _ i) = proj1_sig (closure' f env) -> 
        proj1_sig (sv_a _ i) = bot _ \/
        (exists f, 
          exists env', proj1_sig (sv_a _ i) = proj1_sig (closure' f env') /\ 
          Sub_Environment V SV env' env).

    Inductive SV_invertClos'_Name := ece_invertclosure'_name.
    Variable SV_invertClos'_SV : iPAlgebra SV_invertClos'_Name SV_invertClos'_P SV.    

    Global Instance SV_invertClos'_refl : 
      iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertClos'_P.
      inversion H; subst; simpl; split; intros.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; auto.
      right; eexists; eexists; split; eauto.
      rewrite H0; eauto.
      eapply Sub_Environment_refl; eauto.
    Defined.

    Global Instance SV_invertClos'_Bot : 
      iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertClos'_P.
      inversion H; subst; simpl; split; intros; eauto.
      apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; assumption.
    Defined.

    Global Instance SV_invertClos'_Clos : 
      iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_Clos).
      econstructor; intros.
      unfold iAlgebra; intros.
      eapply ind_alg_SV_Clos with (P' := fun env env' =>
        forall env'',
          map (@proj1_sig _ _) env'' = map (@proj1_sig _ _) env' -> 
          Sub_Environment V SV env env''); 
      try eassumption; intros.
      unfold SV_invertClos'_P; intros; simpl; split; intros.
      apply (inject_i (subGF := Sub_SV_Clos_SV)); econstructor; eauto.
      eapply H1.
      reflexivity.
      right; exists f; exists env; split.
      rewrite H2; reflexivity.
      rewrite H3 in H4; simpl in H4.
      apply (f_equal out_t) in H4; repeat rewrite out_in_inverse, wf_functor in H4;
        simpl in H4; apply (f_equal (prj (sub_F := ClosValue))) in H4; 
          repeat rewrite prj_inj in H4; injection H4; intros; subst.
      eauto.
      destruct env''; try discriminate; constructor.
      unfold SV_invertClos_P in H0.
      destruct env''; try discriminate; injection H2; intros; subst; 
        constructor; eauto.
      destruct H0 as [i' H0]; destruct s; eapply (SV_proj1_b _ _ _ i0); eauto.
      eapply H1; eauto.
    Qed.

    Definition SV_invertClos' := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertClos'_SV)).
    
    Lemma eval_continuous_Exp_H0 : forall e1 e2
      (IHe1 : UP'_P (eval_continuous_Exp_P V (F nat) SV) e1) 
      (IHe2 : UP'_P (eval_continuous_Exp_P V (F nat) SV) e2), 
      UP'_P (eval_continuous_Exp_P V (F nat) SV) (@app _ _ _ (proj1_sig IHe1) (proj1_sig IHe2)).
    Proof.
      intros; destruct IHe1 as [UP'_e1 IHe1];
        destruct IHe2 as [UP'_e2 IHe2].
      unfold eval_continuous_Exp_P; econstructor; simpl; intros;
        eauto with typeclass_instances.
      unfold beval, mfold, app; simpl; repeat rewrite wf_functor;
        simpl; rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F )); simpl.
    unfold isClos.
    repeat erewrite bF_UP_in_out.
    caseEq (project (G := ClosValue)
      (proj1_sig  (boundedFix_UP m f_algebra
        (fun _ : Env (Names.Value V) => Names.bot' V)
        (exist Universal_Property'_fold e1 UP'_e1) gamma))).
    generalize (H (exist _ e1 UP'_e1) _ _ _ H0 H1) as Sub_e1_m_e1_n; intro.
    generalize (project_inject _ _ Clos_Functor _ _ _ _ (proj2_sig _) H2) as Eval_m; intro.
    destruct c.
    destruct (SV_invertClos _ Sub_e1_m_e1_n) as [_ SF'];
      destruct (SF' _ _ Eval_m) as [f' [env' [f'_eq [Eval_n Sub_env_env']]]].
    simpl in Eval_n; unfold eval, mfold in Eval_n.
    unfold beval, evalR, Names.Exp in Eval_n; unfold beval, evalR, Names.Exp.
    rewrite Eval_n; simpl.
    unfold project; rewrite out_in_fmap, fmap_fusion, wf_functor,
      prj_inj; simpl.
    rewrite Eval_m.
    unfold inject; simpl; rewrite out_in_fmap, fmap_fusion, wf_functor, prj_inj; simpl.
    assert (boundedFix_UP m f_algebra (fun _ : Env (Names.Value V) => Names.bot' V)
        e
        (insert (Names.Value V)
           (boundedFix_UP m f_algebra
              (fun _ : Env (Names.Value V) => Names.bot' V)
              (exist Universal_Property'_fold e2 UP'_e2) gamma)
           (map
              (fun e3 : sig Universal_Property'_fold =>
               in_t_UP' V Fun_V (out_t_UP' V Fun_V (proj1_sig e3))) e0)) = 
        boundedFix_UP m f_algebra (fun _ : Env (Names.Value V) => Names.bot' V)
        f'
        (insert (Names.Value V)
           (boundedFix_UP m f_algebra
              (fun _ : Env (Names.Value V) => Names.bot' V)
              (exist Universal_Property'_fold e2 UP'_e2) gamma)
           (map
              (fun e3 : sig Universal_Property'_fold =>
               in_t_UP' V Fun_V (out_t_UP' V Fun_V (proj1_sig e3))) e0))) by 
    (revert f'_eq; clear; induction m; simpl; eauto;
      intros; rewrite f'_eq; auto).
    rewrite H3.
    eapply H.
    eapply P2_Env_insert.
    generalize SV_proj1_a_SV SV_proj1_b_SV iFun_SV Sub_env_env'; clear; intros; induction Sub_env_env'; 
      simpl; constructor; eauto.
    generalize (SV_proj1_a V SV _ _ H
      (proj1_sig (in_t_UP' V Fun_V (out_t_UP' V Fun_V (proj1_sig a))))
      (proj2_sig _) (sym_eq (in_out_UP'_inverse _ _ _ (proj2_sig a)))).
    intros; generalize (SV_proj1_b V SV _ _ H0
      (proj1_sig (in_t_UP' V Fun_V (out_t_UP' V Fun_V (proj1_sig b))))
      (proj2_sig _) (in_out_UP'_inverse _ _ _ (proj2_sig b))).
    intros; apply H1.
    eapply H; eauto.
    auto.
    unfold beval, evalR, Names.Exp in H2; unfold beval, evalR, Names.Exp.
    rewrite H2.
    unfold isBot.
    caseEq (project (G := BotValue) (proj1_sig
      (boundedFix_UP m f_algebra
        (fun _ : Env (Names.Value V) => Names.bot' V)
        (exist Universal_Property'_fold e1 UP'_e1) gamma))).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor.
    eauto.
    caseEq (project (G := ClosValue) (proj1_sig
      (boundedFix_UP n f_algebra
        (fun _ : Env (Names.Value V) => Names.bot' V)
        (exist Universal_Property'_fold e1 UP'_e1) gamma'))).
    destruct c.
    generalize (H (exist _ e1 UP'_e1) _ _ _ H0 H1) as Sub_e1_m_e1_n; intro.
    simpl in Sub_e1_m_e1_n.
    generalize (project_inject _ _ Clos_Functor _ _ _ _ (proj2_sig _) H4) 
      as Eval_n; intro.
    destruct (SV_invertClos' _ Sub_e1_m_e1_n) as [_ SF'];
      destruct (SF' _ _ Eval_n) as [Eval_m | 
        [f' [env' [Eval_m Sub_env_env']]]]; simpl in Eval_m.
    unfold beval, evalR, Names.Exp in *|-*; rewrite Eval_m in H3.
    unfold project, bot, Names.bot' in H3.
    simpl in H3.
    rewrite wf_functor in H3; simpl in H3; unfold Bot_fmap in H3.
    rewrite out_in_fmap, wf_functor, prj_inj in H3; discriminate.
    unfold beval, evalR, Names.Exp in *|-*; rewrite Eval_m in H2.
    unfold project in H2; rewrite out_in_fmap, fmap_fusion, 
      wf_functor, prj_inj in H2; discriminate.
    caseEq (project (G := BotValue) (proj1_sig
      (boundedFix_UP n f_algebra
        (fun _ : Env (Names.Value V) => Names.bot' V)
        (exist Universal_Property'_fold e1 UP'_e1) gamma'))).
    destruct b.
    generalize (project_inject _ _ _ _ _ _ _ 
      (proj2_sig _) H5); clear H5; intro Eval_n.
    generalize (H (exist _ _ UP'_e1) _ _ _ H0 H1) as Sub_e1_m_e1_n; intro.
    simpl in Sub_e1_m_e1_n.
    generalize (SV_invertBot _ SV _ _ Sub_e1_m_e1_n Eval_n). simpl; 
      intros Eval_m; unfold beval, evalR, Names.Exp in *|-*; rewrite Eval_m in H3.
    unfold project, bot, Names.bot' in H3.
    simpl in H3.
    rewrite wf_functor in H3; simpl in H3; unfold Bot_fmap in H3.
    rewrite out_in_fmap, wf_functor, prj_inj in H3; discriminate.
    eapply (inject_i (subGF := Sub_SV_refl_SV)); constructor.
    reflexivity.
  Qed.

    Global Instance Lambda_eval_continuous_Exp  : 
    PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (F nat) SV))) (Lambda nat).
      constructor; unfold Algebra; intros.
      eapply ind_alg_Lambda.
      apply eval_continuous_Exp_H.
      apply eval_continuous_Exp_H0.
      apply eval_continuous_Exp_H1.
      assumption.
    Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF EXPRESSIONS                     *)
  (* ============================================== *)
    
    (** SuperFunctor for Equivalence Relation. **)
    
    Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
    Definition E_eqv A B := iFix (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' := 
      E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').
    Variable funEQV_E : forall A B, iFunctor (EQV_E A B).

    (* Projection doesn't affect Equivalence Relation.*)

    Inductive Lambda_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
    | Var_eqv : forall (gamma : Env _) gamma' n a b e e', 
      lookup gamma n = Some a -> lookup gamma' n = Some b -> 
      proj1_sig e = var a -> 
      proj1_sig e' = var b -> 
      Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' e e')
    | App_eqv : forall (gamma : Env _) gamma' a b a' b' e e', 
      E (mk_eqv_i _ _ _ gamma gamma' a a') -> 
      E (mk_eqv_i _ _ _ gamma gamma' b b') -> 
      proj1_sig e = proj1_sig (app' a b) ->  
      proj1_sig e' = proj1_sig (app' a' b') -> 
      Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' e e')
    | Lam_eqv : forall (gamma : Env _) gamma' f g t1 t2 e e', 
      (forall (a : A) (b : B), E (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))) -> 
      proj1_sig t1 = proj1_sig t2 -> 
      proj1_sig e = proj1_sig (lam' t1 f) ->
      proj1_sig e' = proj1_sig (lam' t2 g) ->  
      Lambda_eqv _ _ E (mk_eqv_i _ _ _ gamma gamma' e e').

    Definition ind_alg_Lambda_eqv 
      (A B : Set)
      (P : eqv_i F A B -> Prop) 
      (H : forall gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq,
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (H0 : forall gamma gamma' a b a' b' e e'       
        (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b'))
        e_eq e'_eq, 
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (H1 : forall gamma gamma' f g t1 t2 e e'
        (IHf : forall a b, P (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b)))
        t1_eq e_eq e'_eq, 
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      i (e : Lambda_eqv A B P i) : P i :=
      match e in Lambda_eqv _ _ _ i return P i with 
        | Var_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq => 
          H gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | App_eqv gamma gamma' a b a' b' e e' 
          eqv_a_a' eqv_b_b' e_eq e'_eq => 
          H0 gamma gamma' a b a' b' e e' 
          eqv_a_a' eqv_b_b' e_eq e'_eq 
        | Lam_eqv gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq => 
          H1 gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq
      end.

    Definition Lambda_eqv_ifmap (A B : Set)
      (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i) 
      (eqv_a : Lambda_eqv A B A' i) : Lambda_eqv A B B' i :=
      match eqv_a in Lambda_eqv _ _ _ i return Lambda_eqv _ _ _ i with
        | Var_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq => 
          Var_eqv _ _ _ gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | App_eqv gamma gamma' a b a' b' e e' 
          eqv_a_a' eqv_b_b' e_eq e'_eq => 
          App_eqv _ _ _ gamma gamma' a b a' b' e e' 
          (f _ eqv_a_a') (f _ eqv_b_b') e_eq e'_eq 
        | Lam_eqv gamma gamma' f' g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq => 
          Lam_eqv _ _ _ gamma gamma' f' g t1 t2 e e'
          (fun a b => f _ (eqv_f_g a b)) t1_eq e_eq e'_eq
      end.

    Global Instance iFun_Lambda_eqv A B : iFunctor (Lambda_eqv A B).
      constructor 1 with (ifmap := Lambda_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; unfold id; eauto.
      rewrite (functional_extensionality_dep _ a); eauto.
      intros; apply functional_extensionality_dep; eauto.
    Defined.

    Variable Sub_Lambda_eqv_EQV_E : forall A B, 
      Sub_iFunctor (Lambda_eqv A B) (EQV_E A B).

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) (F (typeofR _))}.

     Global Instance EQV_proj1_Lambda_eqv : 
       forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (Lambda_eqv _ _).
       econstructor; intros.
       unfold iAlgebra; intros; apply ind_alg_Lambda_eqv; 
         unfold EQV_proj1_P; simpl; intros; subst.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor; simpl; eauto.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
       destruct a; destruct a'; eapply IHa; eauto.
       destruct b; destruct b'; eapply IHb; eauto.
       apply (inject_i (subGF := Sub_Lambda_eqv_EQV_E A B)); econstructor 3; simpl; eauto.
       intros; caseEq (f a); caseEq (g b); apply IHf; eauto.
       rewrite H2; simpl; eauto.
       rewrite H3; simpl; eauto.
       apply H.
     Qed.

  (* ============================================== *)
  (* WELL-FORMED FUNCTION VALUES                    *)
  (* ============================================== *)

    Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
    Variable funWFV : iFunctor WFV.
    Variable typeof_rec : Exp (typeofR D) -> typeofR D.
    (** Functions are well-formed **)

    Inductive WFValue_Clos 
      (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop := 
    | WFV_Clos : forall (f : option DType -> Names.Exp _) f' env gamma gamma' f'_UP
      (t1 t2 t3 t4 : DType) v T,
      proj1_sig v = proj1_sig (closure' (exist _ (proj1_sig (f' (List.length gamma))) f'_UP) env) -> 
      proj1_sig T = proj1_sig (tarrow' t1 t2) -> 
      (forall a b, E_eqvC (insert _ a gamma) (insert _ b gamma') (f a) (f' b)) ->
      (forall n b, lookup gamma' n = Some b -> 
        exists T, lookup gamma b = Some T) -> 
      List.length gamma = List.length gamma' -> 
      P2_Env (fun v T => match T with 
                           | Some T => WFV (mk_WFValue_i _ _ v T)
                           | _ => False 
                         end) env gamma -> 
      (forall n b, lookup gamma' n = Some b -> b = n) -> 
      typeof_rec (f (Some t4)) = Some t3 ->
      proj1_sig t2 = proj1_sig t3 -> 
      proj1_sig t4 = proj1_sig t1 ->       
      WFValue_Clos  WFV (mk_WFValue_i D V v T).

    Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
      (Sub_Lambda_F _) (MAlgebra_typeof_Lambda T) (Typeof_F _)}.

    Context {WF_Value_continous_alg : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

    Definition ind_alg_WFV_Clos
      (P : WFValue_i D V -> Prop) 
      (P' : Env Value -> Env (option DType) -> Prop)
      (H : forall f f' env gamma gamma' f'_UP t1 t2 t3 t4 v T
        v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma' 
        P2_env lookup_gamma'' type_of_f t3_eq t4_eq,
        P' env gamma -> 
        P (mk_WFValue_i _ _ v T))
      (H0 : P' nil nil)
      (H1 : forall a b env env', 
        match b with
          | Some T => P {| wfv_a := a; wfv_b := T |}
          | None => False
        end -> P' env env' -> 
        P' (a :: env) (b :: env'))
      i (e : WFValue_Clos  P i) : P i :=
      match e in WFValue_Clos _ i return P i with
        | WFV_Clos f f' env gamma gamma' f'_UP t1 t2 t3 t4 v T
        v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma' 
        P2_env lookup_gamma'' type_of_f t3_eq t4_eq => 
        H f f' env gamma gamma' f'_UP t1 t2 t3 t4 v T
        v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma' 
        P2_env lookup_gamma'' type_of_f t3_eq t4_eq
        ((fix P_Env_ind' (env : Env Value) (env' : Env (option DType)) 
          (P_env_env' : P2_Env (fun v T => match T with 
                                             | Some T => P (mk_WFValue_i _ _ v T)
                                             | _ => False 
                                           end) env env') := 
          match P_env_env' in P2_Env _ As Bs return P' As Bs with
            | P2_Nil => H0
            | P2_Cons a b As Bs P_a_b P_As_Bs => 
              H1 a b As Bs P_a_b (P_Env_ind' _ _ P_As_Bs)
          end) env gamma P2_env)
      end.

    Definition WFV_Clos_ifmap 
      (A B : WFValue_i D V -> Prop) i 
      (g : forall i, A i -> B i) 
      (WFV_a : WFValue_Clos  A i) : WFValue_Clos  B i :=
      match WFV_a in (WFValue_Clos _ s) return (WFValue_Clos  B s)
        with
        | WFV_Clos f f' env gamma gamma' f'_UP t1 t2 t3 t4 v T
        v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma' 
        P2_env lookup_gamma'' type_of_f t3_eq t4_eq => 
        WFV_Clos _ f f' env gamma gamma' f'_UP t1 t2 t3 t4 v T
        v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma' 
        ((fix P_Env_ind' (env : Env _) (env' : Env _) 
          (P_env_env' : P2_Env (fun v T => match T with 
                                             | Some T => A (mk_WFValue_i _ _ v T)
                                             | _ => False 
                                           end) env env') :=
          match P_env_env' in P2_Env _ As Bs return 
            P2_Env (fun v T => match T with 
                                 | Some T => B (mk_WFValue_i _ _ v T)
                                 | _ => False 
                               end) As Bs with
            | P2_Nil => P2_Nil _ 
            | P2_Cons a b As Bs P_a_b P_As_Bs => 
              P2_Cons (fun v T => match T with 
                                    | Some T => B (mk_WFValue_i _ _ v T)
                                    | _ => False 
                                  end) 
              a b As Bs ((match b as b' return 
                            (match b' with 
                               | Some T => A (mk_WFValue_i _ _ a T)
                               | _ => False 
                             end) -> 
                            (match b' with 
                               | Some T => B (mk_WFValue_i _ _ a T)
                               | _ => False 
                             end) with 
                            | Some T => fun P_a_b' => g (mk_WFValue_i _ _ a T) P_a_b'
                            | None => fun P_a_b' => P_a_b'
                          end) P_a_b) (P_Env_ind' _ _ P_As_Bs)
          end) _ _ P2_env)        
        lookup_gamma'' type_of_f t3_eq t4_eq
      end.
    
    Global Instance iFun_WFV_Clos
      : iFunctor (WFValue_Clos ).
      constructor 1 with (ifmap := WFV_Clos_ifmap ).
      destruct a; simpl; intros;
        apply (f_equal (fun G => WFV_Clos C f0 f' env gamma gamma' f'_UP
          t1 t2 t3 t4 v T e e0 e1 e2 e3 G e4 e5 e6 e7)).
      generalize gamma p; clear; induction env; dependent inversion p; subst.
      reflexivity.
      rewrite IHenv.
      apply (f_equal (fun G => P2_Cons
     (fun (v : Names.Value V) (T : option (Names.DType D)) =>
      match T with
      | Some T0 => C {| wfv_a := v; wfv_b := T0 |}
      | None => False
      end) a b env Bs G (((fix P_Env_ind' (env0 : Env (Names.Value V))
                      (env' : Env (option (Names.DType D)))
                      (P_env_env' : P2_Env
                                      (fun (v : Names.Value V)
                                         (T : option (Names.DType D)) =>
                                       match T with
                                       | Some T0 =>
                                           A {| wfv_a := v; wfv_b := T0 |}
                                       | None => False
                                       end) env0 env') {struct P_env_env'} :
         P2_Env
           (fun (v : Names.Value V) (T : option (Names.DType D)) =>
            match T with
            | Some T0 => C {| wfv_a := v; wfv_b := T0 |}
            | None => False
            end) env0 env' :=
         match
           P_env_env' in (P2_Env _ As Bs0)
           return
             (P2_Env
                (fun (v : Names.Value V) (T : option (Names.DType D)) =>
                 match T with
                 | Some T0 => C {| wfv_a := v; wfv_b := T0 |}
                 | None => False
                 end) As Bs0)
         with
         | P2_Nil =>
             P2_Nil
               (fun (v : Names.Value V) (T : option (Names.DType D)) =>
                match T with
                | Some T0 => C {| wfv_a := v; wfv_b := T0 |}
                | None => False
                end)
         | P2_Cons a0 b0 As Bs0 P_a_b P_As_Bs =>
             P2_Cons
               (fun (v : Names.Value V) (T : option (Names.DType D)) =>
                match T with
                | Some T0 => C {| wfv_a := v; wfv_b := T0 |}
                | None => False
                end) a0 b0 As Bs0
               (match
                  b0 as b'
                  return
                    (match b' with
                     | Some T => A {| wfv_a := a0; wfv_b := T |}
                     | None => False
                     end ->
                     match b' with
                     | Some T => C {| wfv_a := a0; wfv_b := T |}
                     | None => False
                     end)
                with
                | Some T =>
                    fun P_a_b' : A {| wfv_a := a0; wfv_b := T |} =>
                    g {| wfv_a := a0; wfv_b := T |}
                      (f {| wfv_a := a0; wfv_b := T |} P_a_b')
                | None => fun P_a_b' : False => P_a_b'
                end P_a_b) (P_Env_ind' As Bs0 P_As_Bs)
         end) env Bs p0)))).
      destruct b; auto.
      destruct a; simpl; intros;
        apply (f_equal (fun G => WFV_Clos _ f f' env gamma gamma' f'_UP
          t1 t2 t3 t4 v T e e0 e1 e2 e3 G e4 e5 e6 e7)).
      generalize gamma p; clear; induction env; dependent inversion p; subst.
      reflexivity.
      rewrite IHenv.
      apply (f_equal (fun y => P2_Cons
     (fun (v : Names.Value V) (T : option (Names.DType D)) =>
      match T with
      | Some T0 => A {| wfv_a := v; wfv_b := T0 |}
      | None => False
      end) a b env Bs y p0)).
      destruct b; reflexivity.
    Defined.

    Variable Sub_WFV_Clos_WFV : Sub_iFunctor WFValue_Clos WFV.
    Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

     Global Instance WFV_proj1_a_Clos  : 
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) (WFValue_Clos ).
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_a_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_Clos_WFV )); econstructor; simpl; eauto.
       rewrite H11; rewrite H0; simpl; reflexivity.
       rewrite H1; simpl; reflexivity.
       generalize gamma H5; clear; induction env; intros; inversion H5; 
         subst; constructor.
       destruct b.
       unfold WFV_proj1_a_P in H1; unfold WFValueC, WFValue in H1;
         destruct a; eapply H1; eauto.
       eauto.
       eauto.
     Defined.

     Global Instance WFV_proj1_b_Clos  : 
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) (WFValue_Clos ).
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_Clos_WFV )); econstructor; simpl; eauto.
       rewrite H11; rewrite H0; simpl; reflexivity.
       rewrite H11; rewrite H1; reflexivity.
       generalize gamma H5; clear; induction env; intros; inversion H5; 
         subst; constructor.
       destruct b.
       unfold WFV_proj1_b_P in H1; unfold WFValueC, WFValue in H1.
         destruct d; eapply H1; eauto.
       eauto.
       eauto.
     Defined.

    (* Inversion principles for Well-formed natural numbers. *)
    Definition WF_invertClos_P  (i : WFValue_i D V) := 
      WFValue _ _ WFV i /\
      forall t1 t2, proj1_sig (wfv_b _ _ i) = proj1_sig (tarrow' t1 t2) ->
      WFValue_Clos  (iFix WFV) i \/ WFValue_Bot _ _ (iFix WFV) i.

    Inductive WF_invertClos_Name := wfv_invertclosure_name.
    Context {WF_invertClos_WFV : 
      iPAlgebra WF_invertClos_Name (WF_invertClos_P ) WFV}.    

    Global Instance WF_invertClos_Clos  : 
      iPAlgebra WF_invertClos_Name (WF_invertClos_P ) (WFValue_Clos ).
      econstructor; intros.
      unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
        P2_Env (fun v T => match T with 
                             | Some T => WFValueC _ _ WFV v T
                             | _ => False 
                           end)).
      inversion H; subst; simpl; intros; split.
      eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
        econstructor 1 with (f'_UP := f'_UP0); simpl in *|-*; eauto.
      left; econstructor 1 with (f'_UP := f'_UP0); simpl in *|-*; eauto; try congruence.
      rewrite T_e1 in H11; apply (f_equal out_t) in H11; 
        repeat rewrite out_in_inverse in H11.
      repeat rewrite wf_functor in H11; simpl in H11;
      apply (f_equal prj) in H11; repeat rewrite prj_inj in H11;
        injection H11; intros.
      congruence.
      rewrite T_e1 in H11; apply (f_equal out_t) in H11; 
        repeat rewrite out_in_inverse in H11.
      repeat rewrite wf_functor in H11; simpl in H11;
      apply (f_equal prj) in H11; repeat rewrite prj_inj in H11;
        injection H11; intros.
      congruence.
      constructor.
      constructor.
      destruct b; destruct H0; eauto.
      eassumption.
      exact H.
    Defined.

    Global Instance WF_invertClos_Bot  : 
      iPAlgebra WF_invertClos_Name (WF_invertClos_P ) (WFValue_Bot _ _).
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertClos_P.
      inversion H; subst; simpl; intros.
      split.
      apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
      right; econstructor; eassumption.
    Defined.

    Definition WF_invertClos  := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertClos_WFV )).

    Definition WF_invertClos'_P  (i : WFValue_i D V) := 
      WFValue _ _ WFV i /\
      forall v : ClosValue _, proj1_sig (wfv_a _ _ i) = inject v ->
      WFValue_Clos  (iFix WFV) i.

    Inductive WF_invertClos'_Name := wfv_invertclosure'_name.
    Context {WF_invertClos'_WFV : 
      iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) WFV}.    

    Global Instance WF_invertClos'_Clos  : 
      iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) (WFValue_Clos ).
      econstructor; intros.
      unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
        P2_Env (fun v T => match T with 
                             | Some T => WFValueC _ _ WFV v T
                             | _ => False 
                           end)).
      inversion H; subst; simpl; intros; split.
      eapply (inject_i (subGF := Sub_WFV_Clos_WFV )); 
        econstructor 1 with (f'_UP := f'_UP0);
        simpl in *|-*; eauto.
      intros; econstructor 1 with (f'_UP := f'_UP0); simpl in *|-*; eauto.
      left; econstructor; simpl in *|-*; eauto; try congruence.
      intros; constructor; auto.
      destruct b; destruct H0; auto.
      assumption.
    Defined.

    Global Instance WF_invertClos'_Bot  : 
      iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) (WFValue_Bot _ _).
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertClos'_P.
      inversion H; subst; simpl; intros.
      split.
      apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
      rewrite H0; intros.
      elimtype False.
       eapply (inject_discriminate Dis_Clos_Bot); unfold inject in *|-*; simpl in *|-*; eauto;
         apply f_equal; apply f_equal; apply sym_eq; eapply H10.
    Defined.

    Definition WF_invertClos'  := 
      ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertClos'_WFV )).

     Context {WFV_proj1_a_WFV :
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFV}.    
     Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFV}.

    Global Instance WFV_Value_continuous_Clos : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SubValue_Clos.
    Proof.
      constructor; unfold iAlgebra; intros.
      eapply ind_alg_SV_Clos with (P' := fun env env' => forall env0 gamma, 
        P2_Env (fun (v0 : Names.Value V) (T0 : option (Names.DType D)) =>
          match T0 with
            | Some T1 => iFix WFV {| wfv_a := v0; wfv_b := T1 |}
            | None => False
          end) env0 gamma -> 
        map (@proj1_sig _ _) env0 = map (@proj1_sig _ _) env' ->
        P2_Env (fun (v0 : Names.Value V) (T0 : option (Names.DType D)) =>
          match T0 with
            | Some T1 => iFix WFV {| wfv_a := v0; wfv_b := T1 |}
            | None => False
          end) env gamma); try eassumption.
      unfold WF_Value_continuous_P; intros.
      destruct (WF_invertClos'  _ H4) as [_ H5]; simpl in H5; generalize (H5 _ H3); clear H5.
      intros H3'; inversion H3'; subst.
      rewrite H3 in H7; simpl in H7.
      apply in_t_UP'_inject in H7; repeat rewrite wf_functor in H7;
        simpl in H7.
      apply (f_equal (prj (sub_F := ClosValue))) in H7.
      repeat rewrite prj_inj in H7; injection H7; intros; subst;
        clear H7.
      destruct f as [f f_UP].
      simpl in H0.
      revert f_UP H2; rewrite H0; intros.
      apply (inject_i (subGF := (Sub_WFV_Clos_WFV ))).
      econstructor 1 with (f' := f'0) (env := env) (gamma := gamma)
        (f'_UP := f_UP); eauto.
      intros; destruct env0; simpl in H1; try discriminate; auto.
      intros; destruct env0; simpl in H1; try discriminate; auto.
      inversion H2; subst.
      econstructor.
      destruct b; try destruct H6.
      simpl in H3; injection H3; intros; subst.
      apply H0.
      destruct (v) as [v v_UP']; destruct (sv_b V i0) as [b b_UP'].
      eapply WFV_proj1_a with (i := {| wfv_a := exist _ _ v_UP'; wfv_b := d |});
        auto.
      eapply H1; eauto.
      injection H3; intros; auto.
    Defined.

    Lemma isClos_closure : forall t1 f, isClos (proj1_sig (closure' t1 f)) = 
      Some (t1, map (fun e => in_t_UP' _ _ (out_t_UP' _ _ e)) (map (@proj1_sig _ _) f)).
      intros; unfold isClos, project; simpl; rewrite out_in_fmap; 
        repeat rewrite wf_functor; simpl; rewrite prj_inj; auto.
    Qed.

    Lemma isClos_bot : isClos (proj1_sig (bot')) = None.
      intros; unfold isClos, project; simpl; rewrite out_in_fmap; 
        repeat rewrite wf_functor; simpl; unfold Bot_fmap.
      caseEq (prj (sub_F := ClosValue) (inj (Bot (sig (Universal_Property'_fold (F := V)))))).
      elimtype False;  apply inj_prj in H.
      eapply (inject_discriminate Dis_Clos_Bot); unfold inject in *|-*; simpl in *|-*; 
        apply f_equal; apply f_equal; apply sym_eq; eapply H.
      auto.
    Qed.

    Lemma isBot_closure : forall t1 f, isBot _ (proj1_sig (closure' t1 f)) = false.
      intros; unfold isBot, project; simpl; rewrite out_in_fmap; 
        repeat rewrite wf_functor; simpl. 
      caseEq (prj (sub_F := BotValue) (inj (Clos _ t1 
        (map (fun e : Fix V => in_t_UP' V Fun_V (out_t_UP' V Fun_V e))
          (map (@proj1_sig _ _) f))))).
      elimtype False;  apply inj_prj in H.
      eapply (inject_discriminate Dis_Clos_Bot); unfold inject in *|-*; simpl in *|-*; 
        apply f_equal; apply f_equal; eapply H.
      auto.
    Qed.

    Lemma isBot_bot : isBot _ (proj1_sig (bot')) = true.
      intros; unfold isBot, project; simpl; rewrite out_in_fmap; 
        repeat rewrite wf_functor; simpl. 
      rewrite prj_inj; unfold Bot_fmap; auto.
    Qed.

    Context {EQV_proj1_EQV : forall A B, 
      iPAlgebra EQV_proj1_Name (@EQV_proj1_P _ _ (EQV_E) A B) (EQV_E A B)}.    

    Global Instance Lambda_eqv_eval_soundness_alg : forall eval_rec,
      iPAlgebra soundness_XName 
      (soundness_X'_P D V F EQV_E WFV
        typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_F _))
        (f_algebra (FAlgebra := eval_F))) (Lambda_eqv _ _).
    Proof. 
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_Lambda_eqv; try eassumption; 
        unfold soundness_X'_P, eval_alg_Soundness_P; simpl; intros.
      (* Var Case *) 
       rewrite e'_eq; split.
       apply inject_i; econstructor; eauto.
       intros; unfold var, var'; simpl; erewrite out_in_fmap;
         repeat rewrite wf_functor; simpl.
       rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
       destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]]; 
         simpl in *|-*.
       rewrite (WF_gamma' _ _ lookup_b) in *|-*.
       destruct (P2_Env_lookup' _ _ _ _ _ WF_gamma'' _ _ lookup_a) as [v [lookup_v WF_v]];
           unfold Value; rewrite lookup_v.
       destruct a; eauto.
       rename H0 into typeof_d.
       rewrite e_eq in typeof_d; unfold typeof, mfold, var in typeof_d;
         simpl in typeof_d; rewrite wf_functor in typeof_d; simpl in typeof_d;
           rewrite out_in_fmap in typeof_d; rewrite wf_functor in typeof_d;
             simpl in typeof_d;
               rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)) in typeof_d;
                 simpl in typeof_d; injection typeof_d; intros; subst; auto.
       destruct WF_v.
       (* app case *)
       destruct (IHa IH) as [eqv_a _]; destruct (IHb IH) as [eqv_b _].
       rewrite e'_eq; split.
       apply inject_i; econstructor 2; simpl; try apply e_eq; try apply e'_eq; eauto.       
       intros; simpl; erewrite out_in_fmap;
         repeat rewrite wf_functor; simpl.
       rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
       destruct a' as [a' UP_a'].
       rename H0 into typeof_e.
       rewrite e_eq in typeof_e; unfold typeof, mfold, var in typeof_e;
         simpl in typeof_e; rewrite wf_functor in typeof_e; simpl in typeof_e;
           rewrite out_in_fmap in typeof_e; rewrite wf_functor in typeof_e;
             simpl in typeof_e;
               rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)) in typeof_e;
                 simpl in typeof_e.
       caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig a)))); rename H0 into typeof_a;
         rewrite typeof_a in typeof_e; try discriminate.
       caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig b)))); rename H0 into typeof_b;
         rewrite typeof_b in typeof_e; try discriminate.
       caseEq (isTArrow d); rewrite H0 in typeof_e; try discriminate.
       destruct p as [t1 t2].
       caseEq (eq_DType D (proj1_sig t1) d0); rename H1 into eq_t1; 
         rewrite eq_t1 in typeof_e; try discriminate; injection typeof_e; intros; subst; clear typeof_e.
       assert (E_eqv (typeofR D) nat
         {|
           env_A := gamma;
           env_B := gamma';
           eqv_a := (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig a)));
           eqv_b := exist Universal_Property'_fold a' UP_a'|}) as eqv_a' by
       (apply (EQV_proj1 _ EQV_E _ _ _ eqv_a); simpl; auto;
         rewrite <- (in_out_UP'_inverse _ _ (proj1_sig a)) at -1;
           simpl; auto; exact (proj2_sig _)).
       generalize (IH (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig a))) _ _ _ 
         WF_gamma'' d eqv_a' typeof_a);
         intros WF_a'.
       unfold isTArrow in H0.
       caseEq (project (proj1_sig d)); rename H1 into typeof_d;
         rewrite typeof_d in H0; try discriminate; destruct l.
       unfold project in typeof_d; apply inj_prj in typeof_d.
       apply (f_equal (fun g => proj1_sig (in_t_UP' D Fun_D g))) in typeof_d;
         rewrite in_out_UP'_inverse in typeof_d; [simpl in typeof_d | exact (proj2_sig d)].
       destruct (WF_invertClos  _ WF_a') as [_ VWF_a']; clear WF_a'; 
         destruct (VWF_a' s s0 typeof_d) as [WF_a' | WF_a']; inversion WF_a'; subst.
       simpl; rewrite H3.
       rewrite isClos_closure; simpl.
       rewrite (eval_rec_proj).
       assert (WF_eqv_environment_P D V WFV (insert _ (Some t4) gamma0, 
         insert _ (Datatypes.length gamma'0) gamma'0) 
       (insert _ (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig b'))) gamma'')
         (map (fun e0 : Fix V => in_t_UP' _ _ (out_t_UP' _ _ e0))
           (map (@proj1_sig _ _) env)))).
       eapply WF_eqv_environment_P_insert; repeat split; eauto.
       simpl; revert WFV_proj1_a_WFV funWFV H8; clear; 
         intros; induction H8; simpl; constructor; auto.
       destruct b; auto.
       eapply WFV_proj1_a with (i := {| wfv_a := a; wfv_b := d |}); 
         auto.       
       erewrite <- in_out_UP'_inverse; simpl; auto; exact (proj2_sig _).
       rewrite eval_rec_proj.
       destruct b' as [b' b'_UP']; destruct t4 as [t4 t4_UP'].
       eapply WFV_proj1_b with (i := {| wfv_a := _; wfv_b := d0 |}); auto.
       eapply IH; eauto.
       apply (EQV_proj1 _ EQV_E _ _ _ eqv_b); simpl.
       erewrite <- in_out_UP'_inverse; simpl; auto; exact (proj2_sig _).
       erewrite <- in_out_UP'_inverse; simpl; auto; exact (proj2_sig _).
       simpl.
    simpl in H12; rewrite H12; apply sym_eq.
    rewrite typeof_d in H4; simpl in H4; apply in_t_UP'_inject in H4;
      repeat rewrite wf_functor in H4.
    apply (f_equal (prj (sub_F := LType))) in H4;
      repeat rewrite prj_inj in H4; injection H4; injection H0;
        intros; subst;  apply sym_eq;
          eapply (eq_DType_eq D WF_Ind_DType_eq_D); auto.
    rewrite <- H14; auto.
    destruct T as [T UP_T]; eapply WFV_proj1_b with (i := {| wfv_a := _; wfv_b := t3 |}); auto.
    eapply IH; eauto; simpl.
    generalize (H5 (Some t4) (Datatypes.length gamma0)).
    destruct (f (Some t4)); destruct (f' (Datatypes.length gamma0)); simpl; 
      intros.
    rewrite H7 in H2.
    eapply (EQV_proj1 _ EQV_E _ _ _ H2); simpl; auto.
    simpl; rewrite <- H11.
    rewrite typeof_d in H4.
    simpl in H4; apply in_t_UP'_inject in H4;
      repeat rewrite wf_functor in H4.
    apply (f_equal (prj (sub_F := LType))) in H4;
      repeat rewrite prj_inj in H4; injection H4; 
        injection H0; intros; subst; auto.
    simpl; rewrite H2.
    unfold inject; generalize isClos_bot; simpl; intro H'; rewrite H'.
    generalize isBot_bot; simpl; intro H''; rewrite H''.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
    (* lam case *)
    rewrite e'_eq; split; intros.
    generalize (fun a b => proj1 (IHf a b IH)); intro IHf'.
    apply inject_i; econstructor 3; eauto.
    rewrite e_eq in H0; simpl in H0; rewrite out_in_fmap in H0;
      rewrite fmap_fusion in H0; rewrite wf_functor in H0.
    rewrite wf_algebra in H0; simpl.
    unfold fmap in H0; simpl in H0.
    caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig (f (Some t1))))));
    rename H1 into typeof_f; unfold DType, Names.DType, UP'_F in *|-*;
      rewrite typeof_f in H0; try discriminate.
    injection H0; intros; subst; clear H0.
    intros; simpl; erewrite out_in_fmap;
      repeat rewrite wf_functor; simpl.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
    caseEq ((in_t_UP' (F nat) (Fun_F nat)
              (out_t_UP' (F nat) (Fun_F nat)
                 (proj1_sig (g (Datatypes.length gamma'')))))).
    simpl.
    generalize (f_equal (@proj1_sig _ _) H0).
    rewrite in_out_UP'_inverse; simpl; intros; try (exact (proj2_sig _)).
    clear H0; revert u; rewrite <- H1; intros.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
    apply (inject_i (subGF := Sub_WFV_Clos_WFV)).
    revert u;  rewrite (P2_Env_length _ _ _ _ _ WF_gamma''); intros.
    eapply WFV_Clos with (f' := g) (gamma := gamma).
    simpl; repeat rewrite wf_functor; simpl; auto.
    simpl; reflexivity.
    intros; apply (proj1 (IHf a b IH)).
    auto.
    auto.
    auto.
    auto.
    rewrite <- typeof_rec_proj in typeof_f; apply typeof_f.
    reflexivity.
    reflexivity.
  Defined.

   End Lambda.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
