Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.

Section Bool.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Boolean Type. *)
  Inductive BType (A : Set) : Set :=
  | TBool : BType A.

  Definition BType_fmap : forall (A B : Set) (f : A -> B), 
    BType A -> BType B := fun A B _ _ => TBool _.

  Global Instance BType_Functor : Functor BType :=
    {| fmap := BType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_BType_D  : BType :<: D}.

   (* Constructor + Universal Property. *)
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D _ _}.
  
  Definition tbool' : DType := inject' (TBool _).
  Definition tbool : Fix D := proj1_sig tbool'. 
  Global Instance UP'_tbool : 
    Universal_Property'_fold tbool := proj2_sig tbool'.
  
  (* Induction Principle for Nat Types. *)
  Definition ind_alg_BType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop) 
    (H : UP'_P P tbool)
    (d : BType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TBot => exist _ _ H 
    end.

    Lemma WF_ind_alg_BType (Name : Set)
    (P : forall e : Fix D, Universal_Property'_fold e -> Prop) 
    (H : UP'_P P tbool)
    {Sub_BType_D' : BType :<: D} :
    (forall a, inj (Sub_Functor := Sub_BType_D) a =
      inj (A := Fix D) (Sub_Functor := Sub_BType_D') a) ->
      WF_Ind (Name := Name) {| p_algebra := ind_alg_BType P H|}.
      constructor; intros.
      simpl; unfold ind_alg_BType; destruct e; simpl.
      unfold tbool; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.

  (* Type Equality Section. *)
  Definition isTBool : Fix D -> bool :=
   fun typ =>
     match project typ with
      | Some TBool => true
      | None      => false
     end.

  Definition BType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D) 
    (e : BType R) : eq_DTypeR D :=
    match e with 
      | TBool => fun t => isTBool (proj1_sig t)
    end.
  
  Global Instance MAlgebra_eq_DType_Bool T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) BType :=
    {| f_algebra := BType_eq_DType T|}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_BType_D (MAlgebra_eq_DType_Bool T) (eq_DType_DT _)}.

  Global Instance PAlgebra_eq_DType_eq_BType :
    PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) BType.
    constructor; unfold Algebra; intros.
    econstructor; unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tbool, tbool', inject' in H0; simpl in H0;
      repeat rewrite wf_functor in H0; simpl in H0; unfold in_t in H0. 
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H0; simpl in H0.
    unfold isTBool in H0.
    caseEq (project (proj1_sig d2)); rewrite H1 in H0;
      try discriminate; destruct b.
    unfold project in H1.
    apply inj_prj in H1.
    unfold tbool, tbool'; simpl; rewrite wf_functor; simpl.
    unfold BType_fmap.
    generalize (f_equal (in_t_UP' _ _ ) H1); intros.
    apply (f_equal (@proj1_sig _ _)) in H2;
      rewrite in_out_UP'_inverse in H2.
    rewrite H2; simpl; rewrite wf_functor; simpl; unfold BType_fmap;
      reflexivity.
    exact (proj2_sig d2).
  Defined.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Bool (a : Set) : Set :=
  | BLit : bool -> Bool a
  | If : a -> a -> a -> Bool a.

  Definition Bool_fmap (B C : Set) (f : B -> C) (Aa : Bool B) : Bool C :=
    match Aa with 
      | BLit n => BLit _ n
      | If i t e => If _ (f i) (f t) (f e)
    end.
      
  Global Instance Bool_Functor : Functor Bool :=
    {| fmap := Bool_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Definition Exp := Exp F.
  Context {Sub_Bool_F : Bool :<: F}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_Bool_F : WF_Functor _ _ Sub_Bool_F _ _}.
  Definition blit' (b : bool) : Exp := 
    inject' (BLit _ b).
  Definition blit (b : bool) : Fix F := proj1_sig (blit' b).
  Global Instance UP'_blit {b : bool} : 
    Universal_Property'_fold (blit b) := proj2_sig (blit' b).

  Definition cond' (i t e : Exp) : Exp := 
    inject' (If _ i t e).

  Definition cond (i t e : Fix F) 
    {UP'_i : Universal_Property'_fold i}
    {UP'_t : Universal_Property'_fold t}
    {UP'_e : Universal_Property'_fold e}
    : Fix F := proj1_sig (cond' (exist _ _ UP'_i) (exist _ _ UP'_t) (exist _ _ UP'_e)).

  Global Instance UP'_cond  {i t e : Fix F } 
    {UP'_i : Universal_Property'_fold i}
    {UP'_t : Universal_Property'_fold t}
    {UP'_e : Universal_Property'_fold e}
    :
    Universal_Property'_fold (cond i t e) :=
    proj2_sig (cond' (exist _ _ UP'_i) (exist _ _ UP'_t) (exist _ _ UP'_e)).

  (* Induction Principle for Bool. *)
  Definition ind_alg_Bool
    (P : forall e : Fix (F), Universal_Property'_fold e -> Prop) 
    (H : forall b, UP'_P P (blit b))
    (H0 : forall i t e
      (IHi : UP'_P P i) 
      (IHt : UP'_P P t)
      (IHe : UP'_P P e),
      UP'_P P (@cond i t e (proj1_sig IHi) (proj1_sig IHt) (proj1_sig IHe)))
    (e : Bool (sig (UP'_P P))) 
    : 
    sig (UP'_P P) :=
    match e with
      | BLit n => exist _ (blit n) (H n)
      | If i t e => exist (UP'_P P) _
        (H0 (proj1_sig i) (proj1_sig t) (proj1_sig e) (proj2_sig i) (proj2_sig t) (proj2_sig e))
    end.

  Definition ind2_alg_Bool
    {E E' : Set -> Set}
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Bool_E : Bool :<: E}
    {Sub_Bool_E' : Bool :<: E'}
    (P : forall e : (Fix E) * (Fix E'), 
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop) 
    (H : forall b, UP'_P2 P (inject (BLit _ b), inject (BLit _ b)))
    (H0 : forall i t el
      (IHi : UP'_P2 P i) 
      (IHt : UP'_P2 P t)
      (IHel : UP'_P2 P el),
      UP'_P2 P (inject (If _ (exist _ _ (proj1 (proj1_sig IHi))) 
        (exist _ _ (proj1 (proj1_sig IHt))) (exist _ _(proj1 (proj1_sig IHel)))),
      inject (If _ (exist _ _ (proj2 (proj1_sig IHi))) 
        (exist _ _ (proj2 (proj1_sig IHt))) (exist _ _ (proj2 (proj1_sig IHel))))))
      (e : Bool (sig (UP'_P2 P))) 
        : 
        sig (UP'_P2 P) :=
    match e with
      | BLit b => exist _ _ (H b)
      | If i t e => exist (UP'_P2 P) _
        (H0 (proj1_sig i) (proj1_sig t) (proj1_sig e)
          (proj2_sig i) (proj2_sig t) (proj2_sig e)) 
    end.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Boolmetic Expressions. *)

  Definition Bool_typeof (R : Set) (rec : R -> typeofR D) 
     (e : Bool R) : typeofR D := 
     match e with 
       | BLit n => Some (inject' (TBool _))
       | If i t e => match (rec i) with
                         | Some TI => 
                           match isTBool (proj1_sig TI) with
                             | true => match (rec t), (rec e) with 
                                         | Some TT, Some TE => 
                                           match eq_DType D (proj1_sig TT) TE with 
                                             | true => Some TT
                                             | false => None
                                           end
                                         | _, _ => None
                                       end
                             | false => None
                           end
                         | _ => None
                       end
     end.

  Global Instance MAlgebra_typeof_Bool T:
    FAlgebra TypeofName T (typeofR D) Bool :=
    {| f_algebra := Bool_typeof T|}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Boolmetic Values. *)
   Inductive BoolValue (A : Set) : Set :=
   | VB : bool -> BoolValue A.
   
   Definition VB_fmap : forall (A B : Set) (f : A -> B), 
     BoolValue A -> BoolValue B := 
     fun A B _ e => match e with 
                      | VB n => VB _ n
                    end.

   Global Instance VB_Functor : Functor BoolValue :=
     {| fmap := VB_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.
   Context {Sub_BoolValue_V : BoolValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_BoolValue_F : WF_Functor _ _ Sub_BoolValue_V _ _}.

  Definition vb' (b : bool) : Value := inject' (VB _ b).
  Definition vb (b : bool) : Fix V := proj1_sig (vb' b).

   Global Instance UP'_vb {b : bool} : 
     Universal_Property'_fold (vb b) := proj2_sig (vb' b).

   (* Constructor Testing for Boolmetic Values. *)

   Definition isVB : Fix V -> option bool :=
     fun exp =>
       match project exp with
        | Some (VB b) => Some b
        | None        => None
       end.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Definition stuck : nat -> Fix V := stuck _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Context {Sub_BotValue_V : BotValue :<: V}.

   (* Evaluation Algebra for Boolemetic Expressions. *)
  
   Definition Bool_eval (R : Set) (rec : R -> evalR V) 
     (e : Bool R) : evalR V :=
       match e with 
         | BLit b => (fun _ => vb' b)
         | If i t e => (fun env => 
           let i' := (rec i env) in 
             match (isVB (proj1_sig i')) with 
               | Some true => rec t env 
               | Some false => rec e env
               | None => if (@isBot _ Fun_V Sub_BotValue_V (proj1_sig i'))
                          then bot' V
                          else stuck' 5
             end)
       end.

  Global Instance MAlgebra_eval_Bool T :
    FAlgebra EvalName T (evalR V) Bool :=
    {| f_algebra := Bool_eval T |}.


  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.
  
  Global Instance MAlgebra_DTypePrint_BType T:
    FAlgebra DTypePrintName T DTypePrintR BType :=
    {| f_algebra := fun rec e => append "tbool" "" |}.

  Global Instance MAlgebra_ExpPrint_Bool T :
    FAlgebra ExpPrintName T (ExpPrintR) Bool :=
    {| f_algebra := fun rec e => 
      match e with 
        | BLit true => fun i => append "true" ""
        | BLit false => fun i => append "false" ""
        | If i t e => fun i' => append "(if (" ((rec i i') ++ ") then (" ++ (rec t i') ++ ") else ("++ (rec e i')++"))")
    end |}.

  Global Instance MAlgebra_ValuePrint_BType T :
    FAlgebra ValuePrintName T ValuePrintR BoolValue :=
    {| f_algebra := fun rec e => 
      match e with 
        | VB true => append "true" ""
        | VB false => append "false" ""
      end |}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName Exp (evalR V) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Bool) (F)
    (Sub_Bool_F) (MAlgebra_eval_Bool (Exp)) eval_F}.

  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

  Context {Dis_VB_Bot : Distinct_Sub_Functor _ Sub_BoolValue_V Sub_BotValue_V}.

    (* Inversion principles for natural number SubValues. *)
  Definition SV_invertVB_P (i : SubValue_i V) := 
    forall b, proj1_sig (sv_a _ i) = vb b -> 
      proj1_sig (sv_b _ i) = vb b.

    Inductive SV_invertVB_Name := ece_invertvb_name.
    Context {SV_invertVB_SV :
      iPAlgebra SV_invertVB_Name SV_invertVB_P SV}.    

    Global Instance SV_invertVB_refl : 
      iPAlgebra SV_invertVB_Name SV_invertVB_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVB_P.
      inversion H; subst; simpl; congruence.
    Defined.

    Lemma SV_invertVB_default : forall V' 
      (Fun_V' : Functor V')
      (SV' : (SubValue_i V -> Prop) -> SubValue_i V -> Prop)
      (sub_V'_V : V' :<: V)
      (WF_V' : WF_Functor V' V sub_V'_V Fun_V' Fun_V),
      (forall (i : SubValue_i V) (H : SV' SV_invertVB_P i), 
        exists v', proj1_sig (sv_a _ i) = inject v') -> 
      Distinct_Sub_Functor _ Sub_BoolValue_V sub_V'_V -> 
      iPAlgebra SV_invertVB_Name SV_invertVB_P SV'.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVB_P.
      destruct (H _ H1) as [v' eq_v'].
      intros; rewrite eq_v' in H2.
      elimtype False.
      unfold vb, inject, vb', inject' in H2; simpl in H2.
      apply sym_eq in H2.
      apply (inject_discriminate H0 _ _ H2).
    Defined.

    Global Instance SV_invertVB_Bot : 
      iPAlgebra SV_invertVB_Name SV_invertVB_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVB_P.
      inversion H; subst; simpl; intros.
      elimtype False.
      rewrite H0 in H1.
      unfold vb, inject, vb', inject' in H1; simpl in H1.
      repeat rewrite out_in_inverse, wf_functor in H1; simpl in H1.
      eapply (inject_discriminate Dis_VB_Bot); unfold inject; simpl; eauto.
    Defined.

    Context {iFun_F : iFunctor SV}.
    Definition SV_invertVB := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertVB_SV)).

    Definition SV_invertVB'_P (i : SubValue_i V) := 
      forall n, proj1_sig (sv_b _ i) = vb n -> 
        proj1_sig (sv_a _ i) = vb n \/ proj1_sig (sv_a _ i) = bot _.

    Inductive SV_invertVB'_Name := ece_invertvb'_name.
    Context {SV_invertVB'_SV :
      iPAlgebra SV_invertVB'_Name SV_invertVB'_P SV}.    

    Global Instance SV_invertVB'_refl : 
      iPAlgebra SV_invertVB'_Name SV_invertVB'_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVB'_P.
      inversion H; subst; simpl; eauto.
      intros.
      left; congruence.
    Defined.

    Global Instance SV_invertVB'_Bot : 
      iPAlgebra SV_invertVB'_Name SV_invertVB'_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVB'_P.
      inversion H; subst; simpl; eauto.
    Defined.

    Definition SV_invertVB' := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertVB'_SV)).

    (* End Inversion principles for SubValue.*)
    
    Context {SV_invertBot_SV :
      iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.
    Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.

    Lemma WF_ind_alg_Bool (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop) 
    (H : forall b, UP'_P P (blit b))
    (H0 : forall i t e
      (IHi : UP'_P P i) 
      (IHt : UP'_P P t)
      (IHe : UP'_P P e),
      UP'_P P (@cond i t e (proj1_sig IHi) (proj1_sig IHt) (proj1_sig IHe))) 
    {Sub_Bool_F' : Bool :<: F} :
    (forall a, inj (Sub_Functor := Sub_Bool_F) a =
      inj (A := (Fix (F))) (Sub_Functor := Sub_Bool_F') a) ->
      WF_Ind (Name := Name) {| p_algebra := ind_alg_Bool P H H0|}.
      constructor; intros.
      simpl; unfold ind_alg_Bool; destruct e; simpl.
      unfold blit; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
      unfold cond; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.

  (* ============================================== *)
  (* WELL-FORMED BOOLEAN VALUES                     *)
  (* ============================================== *)

    Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
    Variable funWFV : iFunctor WFV.

    (** Natrual Numbers are well-formed **)

    Inductive WFValue_VB (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop := 
    | WFV_VB : forall n v T, 
      proj1_sig v = vb n -> 
      proj1_sig T = tbool -> 
      WFValue_VB WFV (mk_WFValue_i D V v T).

    Definition ind_alg_WFV_VB (P : WFValue_i D V -> Prop) 
      (H : forall n v T veq Teq, P (mk_WFValue_i _ _ v T))
      i (e : WFValue_VB P i) : P i :=
      match e in WFValue_VB _ i return P i with
        | WFV_VB n v T veq Teq => H n v T veq Teq
      end.

    Definition WFV_VB_ifmap (A B : WFValue_i D V -> Prop) i (f : forall i, A i -> B i) 
      (WFV_a : WFValue_VB A i) : WFValue_VB B i :=
      match WFV_a in (WFValue_VB _ s) return (WFValue_VB B s)
        with
        | WFV_VB n v T veq Teq => WFV_VB B n v T veq Teq
      end.

    Global Instance iFun_WFV_VB : iFunctor WFValue_VB.
      constructor 1 with (ifmap := WFV_VB_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable Sub_WFV_VB_WFV : Sub_iFunctor WFValue_VB WFV.

     Global Instance WFV_proj1_a_VB : 
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFValue_VB.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_a_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; simpl; eauto.
       rewrite H3; eauto.
     Defined.

     Global Instance WFV_proj1_b_VB : 
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFValue_VB.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; simpl; eauto.
       rewrite H3; eauto.
     Defined.

    (* Inversion principles for Well-formed Booleans. *)
    Definition WF_invertVB_P (i : WFValue_i D V) := 
      proj1_sig (wfv_b _ _ i) = tbool ->
      WFValue_VB (iFix WFV) i \/ (proj1_sig (wfv_a D V i) = bot V).

    Inductive WF_invertVB_Name := wfv_invertvb_name.
    Context {WF_invertVB_WFV :
      iPAlgebra WF_invertVB_Name WF_invertVB_P WFV}.    

    Global Instance WF_invertVB_VB : 
      iPAlgebra WF_invertVB_Name WF_invertVB_P WFValue_VB.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertVB_P.
      inversion H; subst; simpl; intros.
      left; econstructor; eassumption.
    Defined.

    Ltac WF_invertVB_default := 
      constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
        inversion H; simpl;
          match goal with 
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ => 
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; eapply (inject_discriminate _ _ _ eq_H0)
          end.

    Global Instance WF_invertVB_Bot : 
      iPAlgebra WF_invertVB_Name WF_invertVB_P (WFValue_Bot _ _).
    Proof.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertVB_P.
      inversion H; subst; simpl; intros.
      inversion H; subst; rewrite H3; right; reflexivity.
    Defined.

    Definition WF_invertVB := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertVB_WFV)).

    Context {WFV_proj1_a_WFV :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFV}.    
    Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFV}.
    Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D}. 
    Variable WF_Ind_DType_eq_D : WF_Ind eq_DType_eq_DT.
    Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

    Lemma Bool_eval_Soundness_H 
      (typeof_R eval_R : Set) typeof_rec eval_rec
      {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
      {WF_eval_F' : @WF_FAlgebra EvalName _ _ Bool F
        Sub_Bool_F (MAlgebra_eval_Bool _) (eval_F')} : 
      forall b : bool,
        forall gamma'' : Env (Names.Value V),
          forall T : Names.DType D,
            Bool_typeof typeof_R typeof_rec (BLit _ b) = Some T ->
            WFValueC D V WFV (Bool_eval eval_R eval_rec (BLit _ b) gamma'') T.
      intros n gamma'' T H4; intros.
      apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
      simpl.
      unfold vb, vb', inject; simpl; eauto.
      unfold typeof, mfold, blit in H4; simpl in H4.
      injection H4; intros; subst.
      reflexivity.
    Defined.

   Lemma Bool_eval_Soundness_H0 
     (typeof_R eval_R : Set) typeof_rec eval_rec
     {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
      {WF_eval_F' : @WF_FAlgebra EvalName _ _ Bool F
        Sub_Bool_F (MAlgebra_eval_Bool _) (eval_F')} : 
      forall (i t el : typeof_R) (i' t' el' : eval_R),
        forall gamma'' : Env (Names.Value V),
          (forall T : Names.DType D,
            typeof_rec i = Some T ->
            WFValueC D V WFV (eval_rec i' gamma'') T) ->
          (forall T : Names.DType D,
            typeof_rec t = Some T ->
            WFValueC D V WFV (eval_rec t' gamma'') T) ->
          (forall T : Names.DType D,
            typeof_rec el = Some T ->
            WFValueC D V WFV (eval_rec el' gamma'') T) -> 
          forall T : Names.DType D,
            Bool_typeof typeof_R typeof_rec (If _ i t el) = Some T ->
            WFValueC D V WFV (Bool_eval eval_R eval_rec (If _ i' t' el') gamma'') T.     
     simpl; intros i t el i' t' el' gamma'' IH_i IH_t IH_el T H4.
      caseEq (typeof_rec i); intros; rename H into typeof_i; 
        unfold typeof, typeofR in typeof_i, H4; rewrite typeof_i in H4; 
          try discriminate.
      caseEq (isTBool (proj1_sig d)); intros; rename H into d_eq; rewrite 
        d_eq in H4; try discriminate.
      caseEq (typeof_rec t); rewrite H in H4; rename H into typeof_t.
      caseEq (typeof_rec el); rewrite H in H4; rename H into typeof_el.
      caseEq (eq_DType _ (proj1_sig d0) d1); rewrite H in H4; rename H into eq_d0_d1.
      injection H4; intros; subst; clear H4.
      unfold isTBool in d_eq.
      caseEq (project (proj1_sig d)); intros; rewrite H in d_eq; 
        try discriminate; clear d_eq; rename H into d_eq; destruct b.
      apply project_inject in d_eq; eauto with typeclass_instances.
      unfold WFValueC in *|-*.
      generalize (IH_i _ typeof_i) as WF_i;
        generalize (IH_t _ typeof_t) as WF_t;
          generalize (IH_el _ typeof_el) as WF_el; intros.
      destruct (WF_invertVB _ WF_i d_eq) as [eval_i' | eval_i']; 
        inversion eval_i'; subst.
      rewrite H1; unfold isVB, project, vb, vb', inject'; simpl;
        rewrite out_in_fmap; repeat rewrite wf_functor; simpl; rewrite prj_inj.
      destruct n.
      unfold eval in WF_t; eapply WF_t.
      unfold eval in WF_el; destruct T as [x u];
        apply (WFV_proj1_b _ _ WFV funWFV _ WF_el x u
          (eq_DType_eq D WF_Ind_DType_eq_D _ _ eq_d0_d1)).
      rewrite H0; unfold bot, isVB, project, inject, inject'; simpl;
        rewrite out_in_fmap; repeat rewrite wf_functor; simpl; unfold Bot_fmap.
      caseEq (prj (Sub_Functor := Sub_BoolValue_V) (A:= (sig (@Universal_Property'_fold V _)))
        (inj (Bot (sig Universal_Property'_fold)))).
      elimtype False; eapply (inject_discriminate Dis_VB_Bot b).
      unfold inject; simpl; apply inj_prj in H; erewrite <- H; reflexivity.
      unfold isBot, project; rewrite out_in_fmap; rewrite wf_functor; 
        unfold Bot_fmap; rewrite prj_inj; simpl.
      apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; reflexivity.
      exact (proj2_sig d).
      discriminate.
      discriminate.
      discriminate.
    Defined.
         
    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) F}.
    Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
      Sub_Bool_F (MAlgebra_typeof_Bool T) (Typeof_F _)}.
    Context {WF_Value_continous_alg : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

    Global Instance Bool_eval_Soundness_alg 
      (P_bind : Set)
      (P : P_bind -> Env Value -> Prop)
      (E' : Set -> Set)
      {Fun_E' : Functor E'}
      {Sub_Bool_E' : Bool :<: E'}
      {WF_Fun_E' : WF_Functor _ _ Sub_Bool_E' _ _}
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR _) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_Bool_E' (MAlgebra_typeof_Bool T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalR V)
      (typeof_rec : UP'_F E' -> typeofR D)
      :
      PAlgebra eval_Soundness_alg_Name (sig (UP'_P2 (@eval_alg_Soundness_P D _ V _ _ _ WFV _ P
        _ _ pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := eval_F))))) Bool.
    Proof.
      econstructor; unfold Algebra; intros.
      eapply (ind2_alg_Bool (@eval_alg_Soundness_P D _ V _ _ _ WFV _ P
        _ _ pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := eval_F)))); try eassumption;
      unfold eval_alg_Soundness_P, UP'_P2; intros.
      constructor.
      exact (conj (proj2_sig (inject' (BLit _ b))) (proj2_sig (blit' b))).
      unfold blit, blit', inject; simpl.
      repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      intros gamma'' WF_gamma'' IHa.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Bool_fmap.
      intros.
      eapply Bool_eval_Soundness_H.
      apply WF_eval_F.
      apply H0.
      (* If Case *)
      destruct i as [i1 i2]; destruct t as [t1 t2]; destruct el as [el1 el2];
        destruct IHi as [[UP'_i1 UP'_i2] IHi];
          destruct IHt as [[UP'_t1 UP'_t2] IHt];
            destruct IHel as [[UP'_el1 UP'_el2] IHel];
              simpl in *|-*.
      constructor.
      split; unfold inject; exact (proj2_sig _).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Bool_fmap.
      intros T; eapply Bool_eval_Soundness_H0.
      apply WF_eval_F.
      apply (IHa _ _ WF_gamma'' (_, exist _ _ UP'_i2)); simpl;
        intros; apply (IHi eval_rec_proj typeof_rec_proj _ WF_gamma'' IHa);
          intros; auto; rewrite <- (in_out_UP'_inverse _ _ i1); auto.
      apply (IHa _ _ WF_gamma'' (_, exist _ _ UP'_t2)); simpl;
        intros; apply (IHt eval_rec_proj typeof_rec_proj _ WF_gamma'' IHa);
          intros; auto; rewrite <- (in_out_UP'_inverse _ _ t1); auto.
      apply (IHa _ _ WF_gamma'' (_, exist _ _ UP'_el2)); simpl;
        intros; apply (IHel eval_rec_proj typeof_rec_proj _ WF_gamma'' IHa);
          intros; auto; rewrite <- (in_out_UP'_inverse _ _ el1); auto.
    Defined.

  (* BLit case. *)

    Lemma eval_continuous_Exp_H : forall b, 
      UP'_P (eval_continuous_Exp_P V F SV) (blit b).
      unfold eval_continuous_Exp_P; intros; econstructor; intros.
      unfold beval, mfold, blit; simpl; unfold inject.
      repeat rewrite out_in_fmap; simpl;
        repeat rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      apply (inject_i (subGF := Sub_SV_refl_SV)).
      constructor.
      reflexivity.
    Qed.

    (* If case. *)

    Lemma eval_continuous_Exp_H0 : forall 
      (i t e : Fix (F))
      (IHi : UP'_P (eval_continuous_Exp_P V F SV) i) 
      (IHt : UP'_P (eval_continuous_Exp_P V F SV) t)
      (IHe : UP'_P (eval_continuous_Exp_P V F SV) e), 
      UP'_P (eval_continuous_Exp_P V F SV) 
      (@cond i t e (proj1_sig IHi) (proj1_sig IHt) (proj1_sig IHe)).
      unfold eval_continuous_Exp_P; intros.
      destruct IHi as [i_UP' IHi].
      destruct IHt as [t_UP' IHt].
      destruct IHe as [e_UP' IHe].
      econstructor; intros; eauto with typeclass_instances.
      unfold beval, mfold, cond; simpl.
      unfold inject; simpl; repeat rewrite out_in_fmap; simpl; 
        repeat rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      repeat erewrite bF_UP_in_out.
      caseEq (project (G := BoolValue) 
        (proj1_sig (boundedFix_UP m f_algebra
          (fun _ : Env (Names.Value V) => bot' V)
          (exist Universal_Property'_fold i i_UP') gamma))).
      unfold isVB at 1, evalR, Names.Exp; rewrite H2.
      destruct b.
      generalize (H (exist _ i i_UP') _ _ _ H0 H1); simpl; intros.
      generalize (inj_prj _ _ H2); rename H2 into H2'; intros.
      assert (proj1_sig
            (boundedFix_UP m f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold i i_UP') gamma) = vb b) as Eval_i. 
      unfold vb, vb', inject'; rewrite <- H2; rewrite in_out_UP'_inverse; eauto.
      exact (proj2_sig _).
      clear H2; rename H3 into SubV_i.
      unfold isVB; unfold eval, mfold in SubV_i.
      generalize (SV_invertVB _ SubV_i _ Eval_i).
      simpl; unfold beval, evalR, Names.Exp.
      intros Eval_i'; rewrite Eval_i'.
      unfold project, vb, vb'; simpl; repeat rewrite out_in_fmap;
        repeat rewrite wf_functor; repeat rewrite prj_inj;
          repeat rewrite wf_functor; simpl.
      destruct b; eapply H; eauto.
      unfold isVB; unfold evalR, Names.Exp in *|-*; rewrite H2.
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP m f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold i i_UP') gamma)));
      unfold isBot; unfold evalR, Names.Exp in *|-*; rewrite H3.
      destruct b;  apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
      caseEq (project (G := BoolValue)
           (proj1_sig
              (boundedFix_UP n f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold i i_UP') gamma'))).
      destruct b.
      generalize (inj_prj _ _ H4); rename H4 into H4'; intros.
      assert (proj1_sig
            (boundedFix_UP n f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold i i_UP') gamma') = vb b) as Eval_i' by 
        (unfold vb, vb', inject'; rewrite <- H4;
          rewrite in_out_UP'_inverse; unfold eval, mfold; eauto;
            exact (proj2_sig _)).
      generalize (H (exist _ i i_UP') _ _ _ H0 H1); simpl; intros SubV_i.
      unfold beval, evalR, Names.Exp in *|-*.
      destruct (SV_invertVB' _ SubV_i _ Eval_i') as [i_eq_vb | i_eq_bot];
        simpl in *|-.
      rewrite i_eq_vb in H2.
      unfold vb, project, inject in H2; simpl in H2; rewrite 
        out_in_fmap in H2.
      rewrite fmap_fusion in H2; rewrite wf_functor in H2; simpl in H2;
        rewrite (prj_inj _ ) in H2; discriminate.
      rewrite i_eq_bot in H3.
      unfold bot, project, inject in H3; simpl in H3; rewrite 
        out_in_fmap in H3.
      rewrite fmap_fusion in H3; rewrite wf_functor in H3; simpl in H3;
        rewrite (prj_inj _ ) in H3; discriminate.
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold i i_UP') gamma'))).
      generalize (inj_prj _ _ H5); rename H5 into H5'; intros.
      destruct b.
      assert (proj1_sig
        (beval _ _ n (exist Universal_Property'_fold i i_UP') gamma') = bot _ ) as Eval_i' by
      (apply (f_equal (in_t_UP' _ _)) in H5; apply (f_equal (@proj1_sig _ _)) in H5;
        rewrite in_out_UP'_inverse in H5; [apply H5 | exact (proj2_sig _)]).
      generalize (H (exist _ i i_UP') _ _ _ H0 H1); simpl; intros SubV_i.
      unfold beval, evalR, Names.Exp in *|-*.
      generalize (SV_invertBot _ SV _ _ SubV_i Eval_i'); simpl; intro H8;
        unfold beval, evalR, Names.Exp in *|-*; rewrite H8 in H3.
      unfold bot, project, inject in H3; simpl in H3; rewrite 
        out_in_fmap in H3.
      rewrite fmap_fusion in H3; rewrite wf_functor in H3; simpl in H3;
        rewrite (prj_inj _ ) in H3; discriminate.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    Qed.

    Global Instance Bool_eval_continuous_Exp  : 
      PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V F SV))) (Bool).
    Proof.
      constructor; unfold Algebra; intros.
      eapply ind_alg_Bool.
      apply eval_continuous_Exp_H.
      apply eval_continuous_Exp_H0.
      assumption.
    Defined.

End Bool.

  Hint Extern 1 (iPAlgebra SV_invertVB_Name (SV_invertVB_P _) _) =>
      constructor; unfold iAlgebra; unfold SV_invertVB_P; intros i H n H0;
        inversion H; subst; simpl in H0; revert H0;
          match goal with H : proj1_sig ?v = _ |- proj1_sig ?v = _ -> _ => rewrite H end; intros;
            elimtype False; apply (inject_discriminate _ _ _ H0).

  Hint Extern 1 (iPAlgebra SV_invertVB'_Name (SV_invertVB'_P _) _) =>
      constructor; unfold iAlgebra; unfold SV_invertVB'_P; intros i H n H0;
        inversion H; subst; simpl in H0; revert H0;
          match goal with H : proj1_sig ?v = _ |- proj1_sig ?v = _ -> _ => rewrite H end; intros;
            elimtype False; apply (inject_discriminate _ _ _ H0).

    Ltac WF_invertVB_default := 
      constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
        inversion H; simpl;
          match goal with 
            eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ => 
              intro eq_H; rewrite eq_H in eq_H0;
                elimtype False; eapply (inject_discriminate _ _ _ eq_H0)
          end.

  Hint Extern 5 (iPAlgebra WF_invertVB_Name (WF_invertVB_P _ _ _) _) =>
    constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
      inversion H; simpl;
        match goal with 
          eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ => 
            intro eq_H; rewrite eq_H in eq_H0;
              elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
                apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)];
                fail
        end : typeclass_instances.

Hint Extern 0 => 
  intros; match goal with 
            |- (PAlgebra eval_Soundness_alg_Name 
              (sig (UP'_P2 (eval_alg_Soundness_P _ _ _ _ _ _ _ _ _ _ _ _ _ _))) Bool) =>
            eapply Bool_eval_Soundness_alg; eauto with typeclass_instances
          end : typeclass_instances.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
