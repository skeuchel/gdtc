Require Import Functors.
Require Import List.
Require Import FunctionalExtensionality.

Section Names. 

  (* ============================================== *)
  (* ENVIRONMENTS                                   *)
  (* ============================================== *)

  Definition Env (A : Set) := list A.
 
  Fixpoint lookup {A: Set} (As : Env A) (i : nat) : option A :=
    match As, i with 
      | nil, _  => None
      | cons _ As', S i' => lookup As' i'
      | cons a _, 0 => Some a
    end.
  
  Fixpoint insert (A : Set) (e : A) (env : Env A) : Env A := 
    match env in list _ return Env A with 
      | nil => cons e (nil)
      | cons e' env' => cons e' (@insert _ e env')
    end.
  
  Definition empty A : Env A := nil.


  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)


  (** SuperFunctor for Types. **)
  Variable DT : Set -> Set.
  Context {Fun_DT : Functor DT}.
  Definition DType := UP'_F DT.


  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)


  (** SuperFunctor for Values. **)

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Definition Value := UP'_F V.

  (** ERROR VALUES **)

   Inductive StuckValue (A : Set) : Set :=
    | Stuck : nat -> StuckValue A.

   Context {Sub_StuckValue_V : StuckValue :<: V}.

   Definition Stuck_fmap : forall (A B : Set) (f : A -> B), 
     StuckValue A -> StuckValue B := fun A B _ e => 
       match e with 
         | Stuck n => Stuck _ n
       end.

   Global Instance Stuck_Functor : Functor StuckValue :=
     {| fmap := Stuck_fmap |}.
     destruct a; reflexivity.
     (* fmap_id *)
     destruct a; reflexivity.
   Defined.

   (* Constructor + Universal Property. *)
   Context {WF_SubStuckValue_V : WF_Functor _ _ Sub_StuckValue_V _ _}.
   
   Definition stuck' (n : nat) : Value := inject' (Stuck _ n).
   Definition stuck (n : nat) : Fix V := proj1_sig (stuck' n).

   Global Instance UP'_stuck {n : nat} : 
     Universal_Property'_fold (stuck n) := proj2_sig (stuck' n).
   
   (* Induction Principle for Stuckor Values. *)

  Definition ind_alg_Stuck (P : Fix V -> Prop) 
    (H : forall n, P (stuck n)) 
      (e : StuckValue (sig P)) : sig P :=
    match e with
      | Stuck n => exist P (stuck n) (H n)
    end.

  Definition ind_palg_Stuck (Name : Set) (P : Fix V -> Prop) (H : forall n, P (stuck n)) : 
    PAlgebra Name (sig P) StuckValue :=
    {| p_algebra := ind_alg_Stuck P H|}.

   (** BOTTOM VALUES **)

   Inductive BotValue (A : Set) : Set :=
   | Bot : BotValue A.

   Context {Sub_BotValue_V : BotValue :<: V}.

   Definition Bot_fmap : forall (A B : Set) (f : A -> B), 
     BotValue A -> BotValue B := fun A B _ _ => Bot _.

   Global Instance Bot_Functor : Functor BotValue :=
     {| fmap := Bot_fmap |}.
     destruct a; reflexivity.
     (* fmap_id *)
     destruct a. reflexivity.
   Defined.
   
   (* Constructor + Universal Property. *)
   Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V _ _}.

   Definition bot' : Value := inject' (Bot _).
   Definition bot : Fix V := proj1_sig bot'.
   Global Instance UP'_bot : Universal_Property'_fold bot :=
     proj2_sig bot'.

  Definition ind_alg_Bot (P : Fix V -> Prop) 
    (H : P bot) 
      (e : BotValue (sig P)) : sig P :=
    match e with
      | Bot => exist P bot H
    end.

  (* Constructor Testing for Bottom Values. *)

  Definition isBot : Fix V -> bool :=
    fun exp =>
      match project exp with
       | Some Bot  => true
       | None      => false
      end.


  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)
 
  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Definition Exp := UP'_F E.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)

   
  (** TYPING **)

  Definition typeofR  := option DType.
  Inductive TypeofName : Set := typeofname.
  Context {Typeof_E : forall T,
    FAlgebra TypeofName T typeofR E}.
  Definition typeof :=
    mfold _ (fun _ => @f_algebra _ _ _ _ (Typeof_E _)).

  (** EVALUATION **)

  Definition evalR : Set := Env Value -> Value.

  Inductive EvalName := evalname.

  Context {eval_E : forall T, FAlgebra EvalName T evalR E}.
  Definition eval := mfold _ (fun _ => @f_algebra _ _ _ _ (eval_E _)).

  Context {beval_E : FAlgebra EvalName Exp evalR E}.

  Definition beval (n: nat) :=
    boundedFix_UP n (@f_algebra _ _ _ _ beval_E) (fun _ => bot').

  (** DTYPE EQUALITY **)
    
  Definition eq_DTypeR := DType -> bool.
  Inductive eq_DTypeName := eq_dtypename.
  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T eq_DTypeR DT}.
  Definition eq_DType := mfold _ (fun _ => @f_algebra _ _ _ _ (eq_DType_DT _)).

  Definition eq_DType_eq_P (d : Fix DT) (d_UP' : Universal_Property'_fold d) := forall d2,
    eq_DType d d2 = true -> d = proj1_sig d2.
  Inductive eq_DType_eqName := eq_dtype_eqname.
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName (sig (UP'_P eq_DType_eq_P)) DT}.
  Variable WF_Ind_eq_DT : WF_Ind eq_DType_eq_DT.
  Lemma eq_DType_eq : forall (d1 : DType), eq_DType_eq_P (proj1_sig d1) (proj2_sig d1).
    intro; eapply (proj2_sig (Ind (P := UP'_P eq_DType_eq_P) _ (proj2_sig d1))).
  Qed.

  (** PRETTY PRINTING **)

  Require Import String.
  Require Import Ascii.

  Definition DTypePrintR := string.
  Inductive DTypePrintName := dtypeprintname.
  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR DT}.
  Definition DTypePrint := mfold _ (fun _ => @f_algebra _ _ _ _ (DTypePrint_DT _)).

  Definition ExpPrintR := nat -> string.
  Inductive ExpPrintName := expprintname.
  Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR E}.
  Definition ExpPrint e := mfold _ (fun _ => @f_algebra _ _ _ _ (ExpPrint_E _)) e 48.

  Definition ValuePrintR := string.
  Inductive ValuePrintName := valueprintname.
  Context {ValuePrint_V : forall T, FAlgebra ValuePrintName T ValuePrintR V}.
  Definition ValuePrint := mfold _ (fun _ => @f_algebra _ _ _ _ (ValuePrint_V _)).

  (* Printers for Bot and Stuck *)
   Global Instance MAlgebra_ValuePrint_BotValue T : FAlgebra ValuePrintName T ValuePrintR BotValue :=
     {| f_algebra :=  fun _ _ => append "bot" "" |}.

   Global Instance MAlgebra_ValuePrint_StuckValue T : FAlgebra ValuePrintName T ValuePrintR StuckValue :=
     {| f_algebra :=  
       fun _ e => match e with 
                      | Stuck n => append "Stuck " (String (ascii_of_nat (n + 48)) EmptyString)
                    end|}.  

  (* ============================================== *)
  (* PREDICATE LIFTERS FOR LISTS                    *)
  (* ============================================== *)

    (* Unary Predicates.*)
    Inductive P_Env {A : Set} (P : A -> Prop) : forall (env : Env A), Prop :=
    | P_Nil : P_Env P nil
    | P_Cons : forall a (As : Env _), P a -> P_Env P As -> 
      P_Env P (cons a As).

    Lemma P_Env_lookup : forall A (env : Env A) P,
      P_Env P env -> 
      forall n v, 
        lookup env n = Some v -> P v.
      intros A env P P_env; induction P_env;
        destruct n; simpl; intros; try discriminate.
      injection H0; intros; subst; eauto.
      eauto.
    Qed.  

    Lemma P_Env_Lookup : forall A (env : Env A) (P : A -> Prop),
      (forall n v, 
        lookup env n = Some v -> P v) -> 
      P_Env P env.
      intros A env P H; induction env; constructor.
      eapply (H 0); eauto.
      apply IHenv; intros; eapply (H (S n)); eauto.
    Qed.  

    Lemma P_Env_insert : forall A (env : Env A) (P : A -> Prop),
      P_Env P env -> forall a, P a -> P_Env P (insert _ a env).
      induction env; simpl; intros; constructor; eauto.
      inversion H; subst; eauto.
      eapply IHenv; inversion H; eauto.
    Qed.
      
    (* Binary Predicates.*)
    Inductive P2_Env {A B : Set} (P : A -> B -> Prop) : forall (env : Env A) (env : Env B), Prop :=
    | P2_Nil : P2_Env P nil nil
    | P2_Cons : forall a b (As : Env _) (Bs : Env _), P a b -> P2_Env P As Bs -> 
      P2_Env P (cons a As) (cons b Bs).

    Lemma P2_Env_lookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> 
      forall n v, 
        lookup env n = Some v -> exists v', lookup env' n = Some v' /\
          P v v'.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      exists b; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.  

    Lemma P2_Env_lookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> 
      forall n v, 
        lookup env' n = Some v -> exists v', lookup env n = Some v' /\
          P v' v.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      eexists; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.  

    Lemma P2_Env_Nlookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> 
      forall n,
        lookup env n = None -> lookup env' n = None.
      intros A B env env' P P_env_env'; induction P_env_env'; 
        destruct n; simpl; intros; try discriminate; auto.
    Qed.  
    
    Lemma P2_Env_Nlookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> 
      forall n,
        lookup env' n = None -> lookup env n = None.
      intros A B env env' P P_env_env'; induction P_env_env'; 
        destruct n; simpl; intros; try discriminate; auto.
    Qed.  
    
    Lemma P2_Env_length : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> List.length env = List.length env'.
      intros; induction H; simpl; congruence.
    Qed.
    
    Lemma P2_Env_insert : forall A B (env : Env A) (env' : Env B) (P : A -> B -> Prop),
      P2_Env P env env' -> 
      forall a b, P a b -> P2_Env P (insert _ a env) (insert _ b env').
      intros; induction H; simpl; constructor; eauto.
      constructor.
    Qed.

    (* Need this better induction principle when we're reasoning about 
       Functors that use P2_Envs. *)
    Definition P2_Env_ind' := 
    fun (A B : Set) (P : A -> B -> Prop) (P0 : forall As Bs, P2_Env P As Bs -> Prop)
      (f : P0 _ _ (P2_Nil _))
      (f0 : forall (a : A) (b : B) (As : Env A) (Bs : Env B) (ABs : P2_Env P As Bs)
        (P_a_b : P a b), P0 _ _ ABs -> P0 _ _ (P2_Cons P a b As Bs P_a_b ABs)) =>
        fix F (env : Env A) (env0 : Env B) (p : P2_Env P env env0) {struct p} :
        P0 env env0 p :=
        match p in (P2_Env _ env1 env2) return (P0 env1 env2 p) with
        | P2_Nil => f
        | P2_Cons a b As Bs y p0 => f0 a b As Bs p0 y (F As Bs p0)
      end.

  (* ============================================== *)
  (* SUBVALUE RELATION                              *)
  (* ============================================== *)


    Record SubValue_i : Set := mk_SubValue_i 
      {sv_a : Value;
        sv_b : Value}.
    
    (** SuperFunctor for SubValue Relation. **)
    
    Variable SV : (SubValue_i -> Prop) -> SubValue_i -> Prop.
    Definition SubValue := iFix SV.
    Definition SubValueC V1 V2:= SubValue (mk_SubValue_i V1 V2).
    Variable funSV : iFunctor SV.

    (** Subvalue is reflexive **)
    Inductive SubValue_refl (A : SubValue_i -> Prop) : SubValue_i -> Prop :=
      SV_refl : forall v v', 
        proj1_sig v = proj1_sig v' -> 
        SubValue_refl A (mk_SubValue_i v v').

    Definition ind_alg_SV_refl (P : SubValue_i -> Prop) 
      (H : forall v v', proj1_sig v = proj1_sig v' -> P (mk_SubValue_i v v'))
      i (e : SubValue_refl P i) : P i :=
      match e in SubValue_refl _ i return P i with
        | SV_refl v v' eq_v => H v v' eq_v
      end.

    Definition SV_refl_ifmap (A B : SubValue_i -> Prop) i (f : forall i, A i -> B i) 
      (SV_a : SubValue_refl A i) : SubValue_refl B i :=
      match SV_a in (SubValue_refl _ s) return (SubValue_refl B s)
        with
        | SV_refl v v' H => SV_refl B v v' H
      end.

    Global Instance iFun_SV_refl : iFunctor SubValue_refl.
      constructor 1 with (ifmap := SV_refl_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable Sub_SV_refl_SV : Sub_iFunctor SubValue_refl SV.

    (** Bot is Bottom element for this relation **)
    Inductive SubValue_Bot (A : SubValue_i -> Prop) : SubValue_i -> Prop :=
      SV_Bot : forall v v', 
        proj1_sig v = inject (Bot _) -> 
        SubValue_Bot A (mk_SubValue_i v v').

    Definition ind_alg_SV_Bot (P : SubValue_i -> Prop) 
      (H : forall v v' v_eq, P (mk_SubValue_i v v'))
      i (e : SubValue_Bot P i) : P i :=
      match e in SubValue_Bot _ i return P i with
        | SV_Bot v v' v_eq => H v v' v_eq
      end.

    Definition SV_Bot_ifmap (A B : SubValue_i -> Prop) i (f : forall i, A i -> B i) 
      (SV_a : SubValue_Bot A i) : SubValue_Bot B i :=
      match SV_a in (SubValue_Bot _ s) return (SubValue_Bot B s)
        with
        | SV_Bot v v' H => SV_Bot B v v' H
      end.

    Global Instance iFun_SV_Bot : iFunctor SubValue_Bot.
      constructor 1 with (ifmap := SV_Bot_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable Sub_SV_Bot_SV : Sub_iFunctor SubValue_Bot SV.
      

    (* Inversion principle for Bottom SubValues. *)
    Definition SV_invertBot_P (i : SubValue_i) := 
      proj1_sig (sv_b i) = bot -> proj1_sig (sv_a i) = bot.

    Inductive SV_invertBot_Name := ece_invertbot_name.
    Context {SV_invertBot_SV :
      iPAlgebra SV_invertBot_Name SV_invertBot_P SV}.    

    Global Instance SV_invertBot_refl : 
      iPAlgebra SV_invertBot_Name SV_invertBot_P (SubValue_refl).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertBot_P.
      inversion H; subst; simpl; congruence.
    Defined.

    Global Instance SV_invertBot_Bot : 
      iPAlgebra SV_invertBot_Name SV_invertBot_P SubValue_Bot.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertBot_P.
      inversion H; subst; simpl; eauto.
    Defined.

    Definition SV_invertBot := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertBot_SV)).
    (* End Inversion principle for SubValue.*)

    (* Projection doesn't affect SubValue Relation.*)

     Definition SV_proj1_b_P (i :SubValue_i) := 
      forall b' H, b' = proj1_sig (sv_b i) ->  
      SubValueC (sv_a i) (exist _ b' H).

     Inductive SV_proj1_b_Name := sv_proj1_b_name.
     Context {SV_proj1_b_SV :
       iPAlgebra SV_proj1_b_Name SV_proj1_b_P SV}.    
     
     Definition SV_proj1_b := 
       ifold_ SV _ (ip_algebra (iPAlgebra := SV_proj1_b_SV)).
     
     Global Instance SV_proj1_b_refl : 
       iPAlgebra SV_proj1_b_Name SV_proj1_b_P SubValue_refl.
       econstructor; intros.
       unfold iAlgebra; intros; unfold SV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; simpl; congruence.
     Defined.

    Global Instance SV_proj1_b_Bot : 
      iPAlgebra SV_proj1_b_Name SV_proj1_b_P SubValue_Bot.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_proj1_b_P.
      inversion H; subst; simpl; eauto.
      intros; revert H1; rewrite H2; intros.
      apply inject_i.
      constructor; assumption.
    Defined. 

    Definition SV_proj1_a_P (i : SubValue_i) := 
      forall a' H, proj1_sig (sv_a i) = a' -> 
        SubValueC (exist _ a' H) (sv_b i).

    Inductive SV_proj1_a_Name := sv_proj1_a_name.
    Context {SV_proj1_a_SV :
      iPAlgebra SV_proj1_a_Name SV_proj1_a_P SV}.    

    Definition SV_proj1_a := 
      ifold_ SV _ (ip_algebra (iPAlgebra := SV_proj1_a_SV)).

    Global Instance SV_proj1_a_refl : 
      iPAlgebra SV_proj1_a_Name SV_proj1_a_P SubValue_refl.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_proj1_a_P.
      inversion H; subst; simpl; intros.
      revert H1; rewrite <- H2; intros.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; simpl; eauto.
    Defined.

    Global Instance SV_proj1_a_Bot : 
      iPAlgebra SV_proj1_a_Name SV_proj1_a_P SubValue_Bot.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_proj1_a_P.
      inversion H; subst; simpl; eauto.
      intros; revert H1; rewrite <- H2, H0; intros.
      apply inject_i.
      constructor; reflexivity.
    Defined. 

    (** SubValue lifted to Environments **)    
    Definition Sub_Environment (env env' : Env _) :=
      P2_Env SubValueC env env'.

    Lemma Sub_Environment_refl : forall (env : Env _),
      Sub_Environment env env.
      induction env; econstructor; eauto.
      apply (inject_i (subGF := Sub_SV_refl_SV)); 
        constructor; reflexivity.
    Qed.

  (* ============================================== *)
  (* EVALUATION IS CONTINUOUS                        *)
  (* ============================================== *)

    (** Helper property for proof of continuity of evaluation. **)
    Definition eval_continuous_Exp_P (e : Fix E) 
      (e_UP' : Universal_Property'_fold e) :=
      forall (m : nat),
        (forall (e0 : Exp)
          (gamma gamma' : Env Value) (n : nat),
          Sub_Environment gamma gamma' ->
          m <= n -> SubValueC (beval m e0 gamma) (beval n e0 gamma')) ->
        forall (gamma gamma' : Env Value) (n : nat),
          Sub_Environment gamma gamma' ->
          m <= n -> 
          SubValueC (beval (S m) (exist _ _ e_UP') gamma) (beval (S n) (exist _ _ e_UP') gamma').

    Inductive EC_ExpName := ec_expname.

    Variable eval_continuous_Exp_E : PAlgebra EC_ExpName (sig (UP'_P eval_continuous_Exp_P)) E.    
    Variable WF_Ind_EC_Exp : WF_Ind eval_continuous_Exp_E.

    (** Evaluation is continuous. **)
    Lemma beval_continuous : forall m,
      forall (e : Exp) (gamma gamma' : Env _), 
        forall n (Sub_G_G' : Sub_Environment gamma gamma'),
          m <= n -> 
          SubValueC (beval m e gamma) (beval n e gamma').
      induction m; simpl.
      intros; eapply in_ti; eapply inj_i; econstructor; simpl; eauto.
      intros; destruct n; try (inversion H; fail).
      assert (m <= n) as le_m_n0 by auto with arith; clear H.
      revert m IHm gamma gamma' n Sub_G_G' le_m_n0.
      fold (eval_continuous_Exp_P (proj1_sig e)).
      apply (proj2_sig (Ind (P := UP'_P eval_continuous_Exp_P) _ (proj2_sig e))).
    Qed.        

  (* ============================================== *)
  (* WELL-FORMED VALUES RELATION                     *)
  (* ============================================== *)

    Record WFValue_i : Set := mk_WFValue_i 
      {wfv_a : Value;
        wfv_b : DType}.
    
    (** SuperFunctor for Well-Formed Value Relation. **)
    
    Variable WFV : (WFValue_i -> Prop) -> WFValue_i -> Prop.
    Definition WFValue := iFix WFV.
    Definition WFValueC V T:= WFValue (mk_WFValue_i V T).
    Variable funWFV : iFunctor WFV.

    (** Bottom is well-formed **)

    Inductive WFValue_Bot (A : WFValue_i -> Prop) : WFValue_i -> Prop :=
      WFV_Bot : forall v T, 
        proj1_sig v = inject (Bot _) -> 
        WFValue_Bot A (mk_WFValue_i v T).

    Definition ind_alg_WFV_Bot (P : WFValue_i -> Prop) 
      (H : forall v T v_eq, P (mk_WFValue_i v T))
      i (e : WFValue_Bot P i) : P i :=
      match e in WFValue_Bot _ i return P i with
        | WFV_Bot v T v_eq => H v T v_eq
      end.

    Definition WFV_Bot_ifmap (A B : WFValue_i -> Prop) i (f : forall i, A i -> B i) 
      (WFV_a : WFValue_Bot A i) : WFValue_Bot B i :=
      match WFV_a in (WFValue_Bot _ s) return (WFValue_Bot B s)
        with
        | WFV_Bot v T H => WFV_Bot B v T H
      end.

    Global Instance iFun_WFV_Bot : iFunctor WFValue_Bot.
      constructor 1 with (ifmap := WFV_Bot_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable WF_WFV_Bot_WFV : Sub_iFunctor WFValue_Bot WFV.

    Definition WF_Environment env env' :=
      P2_Env (fun v T => 
        match T with 
          | Some T => WFValueC v T
          | None => False
        end) env env'.

    (* Projection doesn't affect WFValue Relation.*)

     Definition WFV_proj1_a_P (i :WFValue_i) := 
      forall a' H, a' = proj1_sig (wfv_a i) ->  
        WFValueC (exist _ a' H) (wfv_b i).

     Inductive WFV_proj1_a_Name := wfv_proj1_a_name.
     Context {WFV_proj1_a_WFV :
       iPAlgebra WFV_proj1_a_Name WFV_proj1_a_P WFV}.    
     
     Definition WFV_proj1_a := 
       ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_proj1_a_WFV)).
     
     Global Instance WFV_proj1_a_Bot : 
       iPAlgebra WFV_proj1_a_Name WFV_proj1_a_P WFValue_Bot.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_a_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := WF_WFV_Bot_WFV)); constructor; simpl; congruence.
     Defined.

     Definition WFV_proj1_b_P (i :WFValue_i) := 
      forall b' H, b' = proj1_sig (wfv_b i) ->  
        WFValueC (wfv_a i) (exist _ b' H).

     Inductive WFV_proj1_b_Name := wfv_proj1_b_name.
     Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name WFV_proj1_b_P WFV}.    
     
     Definition WFV_proj1_b := 
       ifold_ WFV _ (ip_algebra (iPAlgebra := WFV_proj1_b_WFV)).
     
     Global Instance WFV_proj1_b_Bot : 
       iPAlgebra WFV_proj1_b_Name WFV_proj1_b_P WFValue_Bot.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := WF_WFV_Bot_WFV)); constructor; simpl; congruence.
     Defined.

  (* ============================================== *)
  (* Evaluation preserves Well-Formedness           *)
  (* ============================================== *)

    Definition WF_Value_continuous_P i := 
      forall T, WFValueC (sv_b i) T -> WFValueC (sv_a i) T.

    Inductive WFV_ContinuousName : Set := wfv_continuousname.
    
    Context {WF_Value_continous_alg : iPAlgebra WFV_ContinuousName WF_Value_continuous_P SV}.

    Global Instance WFV_Value_continuous_refl  : 
      iPAlgebra WFV_ContinuousName WF_Value_continuous_P SubValue_refl.
      constructor; unfold iAlgebra; intros.
      inversion H; subst.
      unfold WF_Value_continuous_P; simpl; intros.
      unfold WFValueC in H1.
      destruct v; apply (WFV_proj1_a _ H1); eauto.
    Qed.

    Global Instance WFV_Value_continuous_Bot  : 
      iPAlgebra WFV_ContinuousName WF_Value_continuous_P SubValue_Bot.
      constructor; unfold iAlgebra; intros.
      inversion H; subst.
      unfold WF_Value_continuous_P; simpl; intros.
      apply inject_i; constructor; auto.
    Qed.

    Lemma WF_Value_continous : forall v v',
      SubValueC v v' -> 
      WF_Value_continuous_P (mk_SubValue_i v v').
      intros; apply (ifold_ SV); try assumption.
      apply ip_algebra.
    Qed.

    Lemma WF_Value_beval : forall m n,
      forall (e : Exp) gamma gamma' T
        (Sub_G_G' : Sub_Environment gamma' gamma),
        m <= n -> 
        WFValueC (beval n e gamma) T -> 
        WFValueC (beval m e gamma') T.
      intros; eapply WF_Value_continous.
      eapply beval_continuous; try eassumption.
      eassumption.
    Qed.

    Variable (WF_MAlg_typeof : WF_MAlgebra Typeof_E).
    Variable (WF_MAlg_eval : WF_MAlgebra eval_E).

    Definition eval_alg_Soundness_P 
      (P_bind : Set)
      (P : P_bind -> Env Value -> Prop)
      (E' : Set -> Set)
      (Fun_E' : Functor E')
      (pb : P_bind)
      (typeof_rec : UP'_F E' -> typeofR)
      (eval_rec : Exp -> evalR)
      (typeof_F : Mixin (UP'_F E') E' typeofR)
      (eval_F : Mixin Exp E evalR)
      (e : (Fix E') * (Fix E)) 
      (e_UP' : Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e)) := 
      forall 
        (eval_rec_proj : forall e, eval_rec e = eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e))))
        (typeof_rec_proj : forall e, typeof_rec e = typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e))))
      gamma'' (WF_gamma'' : P pb gamma'')
      (IHa : forall pb gamma'' (WF_gamma'' : P pb gamma'') (a : (UP'_F E' * Exp)), 
          (forall T, 
            typeof_F typeof_rec (out_t_UP' _ _ (proj1_sig (fst a))) = Some T ->
            WFValueC (eval_F eval_rec (out_t_UP' _ _ (proj1_sig (snd a))) gamma'') T) -> 
          forall T, typeof_rec (fst a) = Some T -> 
            WFValueC (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig (snd a)))) gamma'') T),
        forall T : DType,
          typeof_F typeof_rec (out_t_UP' _ _ (fst e)) = Some T ->
          WFValueC (eval_F eval_rec (out_t_UP' _ _ (snd e)) gamma'') T.

    Inductive eval_Soundness_alg_Name := eval_soundness_algname.

    Variable eval_Soundness_alg_F : forall typeof_rec eval_rec,
      PAlgebra eval_Soundness_alg_Name (sig (UP'_P2 (eval_alg_Soundness_P unit 
        (fun _ _ => True) _ _ tt
        typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _)) (f_algebra (FAlgebra := eval_E _))))) E.
    Variable WF_Ind_eval_Soundness_alg : forall typeof_rec eval_rec, 
      @WF_Ind2 E E E eval_Soundness_alg_Name Fun_E Fun_E Fun_E
      (UP'_P2 (eval_alg_Soundness_P _ _ _ _ tt typeof_rec eval_rec _ _)) _ _ (eval_Soundness_alg_F _ _).

    Definition eval_soundness_P (e : Fix E) (e_UP' : Universal_Property'_fold e) :=
      forall gamma'' T, typeof e = Some T -> 
        WFValueC (eval e gamma'') T.

    Lemma eval_Soundness : forall (e : Exp),
      forall gamma'' T, typeof (proj1_sig e) = Some T -> 
        WFValueC (eval (proj1_sig e) gamma'') T.
      intros.      
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig e)).
      simpl; unfold typeof, eval, fold_, mfold, in_t.
      rewrite wf_malgebra; unfold mfold.
      destruct (Ind2 (Ind_Alg := eval_Soundness_alg_F 
        (fun e => typeof (proj1_sig e)) (fun e => eval (proj1_sig e)))
        _ (proj2_sig e)) as [e' eval_e'].
      unfold eval_alg_Soundness_P in eval_e'.
      eapply eval_e'; intros; auto; try constructor.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      rewrite (@in_out_UP'_inverse _ _ (proj1_sig _) (proj2_sig _)); auto.
      unfold eval, mfold; simpl; unfold in_t; rewrite wf_malgebra; unfold mfold; apply H0; auto.
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig (fst a)) (proj2_sig (fst a))) in H1.
      simpl in H1; unfold typeof, mfold, in_t in H1.
      rewrite wf_malgebra in H1; apply H1.
      rewrite <- (@in_out_inverse _ _ (proj1_sig e) (proj2_sig e)) in H.
      simpl in H; unfold typeof, mfold, in_t in H; simpl in H.
      rewrite <- wf_malgebra.
      simpl; unfold out_t_UP'.
      rewrite Fusion with (g := (fmap in_t)). 
      apply H.
      exact (proj2_sig _).
      intros; repeat rewrite fmap_fusion; reflexivity.
    Qed.

End Names.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
