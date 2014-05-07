Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Section Mu.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Fixpoint Expressions *)
  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.

  Inductive Fix_ (A E : Set) : Set :=
  | Mu : DType D -> (A -> E) -> Fix_ A E.

  (** Functor Instance **)

  Definition fmapFix {A} : forall {X Y: Set}, (X -> Y) -> (Fix_ A X -> Fix_ A Y):=
    fun _ _ f e =>
      match e with
       | Mu t g => Mu _ _ t (fun a => f (g a))
      end.

  Global Instance FixFunctor A : Functor (Fix_ A) := 
  {| fmap := fmapFix
   |}.
  Proof.
  (* fmap fusion *)
    intros. destruct a; unfold fmapFix; reflexivity.
  (* fmap id *)
    intros; destruct a; unfold fmapFix. 
    assert ((fun x => a x) = a) by
      (apply functional_extensionality; intro; reflexivity).
    unfold id.
    rewrite H.
    reflexivity.
  Defined.

  Variable F : Set -> Set -> Set.
  Context {Sub_Fix_F : forall A : Set, Fix_ A :<: F A}.
  Context {Fun_F : forall A, Functor (F A)}.
  Definition Exp (A : Set) := Exp (F A).

  (* Constructors + Universal Property. *)

  Context {WF_Sub_Fix_F : forall A, WF_Functor _ _ (Sub_Fix_F A) _ _}.
  
  Definition mu' {A : Set} 
    (t1 : DType D) 
    (f : A -> sig (Universal_Property'_fold (F := F A))) 
    : 
    Exp A := inject' (Mu _ _ t1 f).

  Definition mu {A : Set}
    (t1 : DType D) 
    (f : A -> Fix (F A)) 
    {f_UP' : forall a, Universal_Property'_fold (f a)} 
    :
    Fix (F A) := proj1_sig (mu' t1 (fun a => exist _ _ (f_UP' a))).
  
   Global Instance UP'_mu {A : Set} 
     (t1 : DType D) 
     (f : A -> Fix (F A)) 
     {f_UP' : forall a, Universal_Property'_fold (f a)}
     :
     Universal_Property'_fold (mu t1 f) := 
     proj2_sig (mu' t1 (fun a => exist _ _ (f_UP' a))).

  (* Induction Principle for PLambda. *)
  Definition ind_alg_Fix {A : Set} 
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop) 
    (H : forall t1 f
      (IHf : forall a, UP'_P P (f a)),
      UP'_P P (@mu _ t1 _ (fun a => (proj1_sig (IHf a)))))
    (e : Fix_ A (sig (UP'_P P))) : sig (UP'_P P) :=
    match e with
      | Mu t1 f => 
        exist _ _ (H t1 (fun a => proj1_sig (f a)) (fun a => proj2_sig (f a)))
    end.

  (* Typing for Lambda Expressions. *)
  
  Context {eq_DType_D : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.

  Definition Fix_typeof (R : Set) (rec : R -> typeofR D) (e : Fix_ (typeofR D) R) : typeofR D:= 
  match e with
    | Mu t1 f => match rec (f (Some t1)) with
                     | Some t2 => if (eq_DType D (proj1_sig t1) t2) then
                       Some t1 else None
                     | _ => None
                   end
  end.

  Global Instance MAlgebra_typeof_Fix T:
    FAlgebra TypeofName T (typeofR D) (Fix_ (typeofR D)) :=
    {| f_algebra := Fix_typeof T|}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Definition Value := Value V.

   Variable Sub_StuckValue_V : StuckValue :<: V.
   Definition stuck' : nat -> Value := stuck' _.
   Variable Sub_BotValue_V : BotValue :<: V.
   Definition bot' : Value := bot' _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Definition Fix_eval : Mixin (Exp nat) (Fix_ nat) (evalR V) :=
    fun rec e => 
     match e with 
       | Mu t1 f => fun env => 
         rec (f (length env)) (insert _ (rec (mu' t1 f) env) env)
     end.

(* Evaluation Algebra for Lambda Expressions. *)

  Global Instance MAlgebra_eval_Fix :
    FAlgebra EvalName (Exp nat) (evalR V) (Fix_ nat) :=
    {| f_algebra := Fix_eval|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import String.
  Require Import Ascii.

  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR D}.

   Definition PLambda_ExpPrint (R : Set) (rec : R -> ExpPrintR) 
     (e : Fix_ nat R) : ExpPrintR := 
     match e with 
       | Mu t1 f => fun n => append "|\/| x" ((String (ascii_of_nat n) EmptyString) ++
         " : " ++ (DTypePrint _ (proj1_sig t1)) ++ ". " ++ 
         (rec (f n) (S n)) ++ ")")
     end.

   Global Instance MAlgebra_Print_Fix T :
     FAlgebra ExpPrintName T ExpPrintR (Fix_ nat) :=
     {| f_algebra := PLambda_ExpPrint T|}.
   
   Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR (F nat)}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

    Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
    Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Fix_ nat) (F nat)
      (Sub_Fix_F nat) (MAlgebra_eval_Fix) (eval_F)}.
    
   (* Continuity of Evaluation. *)
    Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
    Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
    Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.
    
  (* Mu case. *)
    
    Lemma eval_continuous_Exp_H : forall t1 f
      (IHf : forall a, UP'_P (eval_continuous_Exp_P V (F _) SV) (f a)), 
      UP'_P (eval_continuous_Exp_P V (F _) SV) 
      (@mu _ t1 _ (fun a => (proj1_sig (IHf a)))).
      unfold eval_continuous_Exp_P; econstructor; simpl; intros.
      unfold beval, mfold, mu; simpl; repeat rewrite wf_functor;
        simpl; rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F )); simpl.
      unfold beval, evalR, Names.Exp in H.
      assert (f (Datatypes.length gamma) = (f (Datatypes.length gamma'))) as f_eq by
        (rewrite (P2_Env_length _ _ _ _ _ H0); reflexivity).
      rewrite f_eq.
      eapply H; eauto.
      eapply P2_Env_insert; eauto.
    Qed.

    Global Instance Fix_eval_continuous_Exp  : 
    PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (F _) SV))) (Fix_ nat).
      constructor; unfold Algebra; intros.
      eapply ind_alg_Fix.
      apply eval_continuous_Exp_H.
      assumption.
    Defined.

    Global Instance WF_PLambda_eval_continuous_Exp 
      {Sub_F_E' :  Fix_ nat :<: F nat} :
      (forall a, inj (Sub_Functor := Sub_Fix_F _) a =
        inj (A := (Fix (F nat))) (Sub_Functor := Sub_F_E') a) -> 
        WF_Ind (sub_F_E := Sub_F_E') Fix_eval_continuous_Exp.
      constructor; intros.
      simpl; unfold ind_alg_Fix; destruct e; simpl.
      unfold mu; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF EXPRESSIONS                     *)
  (* ============================================== *)

    Inductive Fix_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
    | Mu_eqv : forall (gamma : Env _) gamma' f g t1 t2 e e', 
      (forall (a : A) (b : B), 
        E (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))) -> 
      proj1_sig t1 = proj1_sig t2 -> 
      proj1_sig e = proj1_sig (mu' t1 f) ->
      proj1_sig e' = proj1_sig (mu' t2 g) ->  
      Fix_eqv _ _ E (mk_eqv_i _  _ _ gamma gamma' e e').

    Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
    Variable funEQV_E : forall A B, iFunctor (EQV_E A B).

    Definition ind_alg_Fix_eqv 
      (A B : Set)
      (P : eqv_i F A B -> Prop) 
      (H1 : forall gamma gamma' f g t1 t2 e e'
        (IHf : forall a b, 
          P (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b)))
        t1_eq e_eq e'_eq, 
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      i (e : Fix_eqv A B P i) : P i :=
      match e in Fix_eqv _ _ _ i return P i with 
        | Mu_eqv gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq => 
          H1 gamma gamma' f g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq
      end.

    Definition Fix_eqv_ifmap (A B : Set)
      (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i) 
      (eqv_a : Fix_eqv A B A' i) : Fix_eqv A B B' i :=
      match eqv_a in Fix_eqv _ _ _ i return Fix_eqv _ _ _ i with
        | Mu_eqv gamma gamma' f' g t1 t2 e e'
          eqv_f_g t1_eq e_eq e'_eq => 
          Mu_eqv _ _ _ gamma gamma' f' g t1 t2 e e'
          (fun a b => f _ (eqv_f_g a b)) t1_eq e_eq e'_eq
      end.

    Global Instance iFun_Fix_eqv A B : iFunctor (Fix_eqv A B).
      constructor 1 with (ifmap := Fix_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; unfold id; eauto.
      rewrite (functional_extensionality_dep _ a); eauto.
      intros; apply functional_extensionality_dep; eauto.
    Defined.

    Variable Sub_Fix_eqv_EQV_E : forall A B, 
      Sub_iFunctor (Fix_eqv A B) (EQV_E A B).

    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) (F (typeofR _))}.

     Global Instance EQV_proj1_Fix_eqv : 
       forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (Fix_eqv _ _).
       econstructor; intros.
       unfold iAlgebra; intros; apply ind_alg_Fix_eqv; 
         unfold EQV_proj1_P; simpl; intros; subst.
       apply (inject_i (subGF := Sub_Fix_eqv_EQV_E A B)); econstructor; simpl; eauto.
       intros; caseEq (f a); caseEq (g b); apply IHf; eauto.
       rewrite H2; simpl; eauto.
       rewrite H3; simpl; eauto.
       apply H.
     Qed.

     Context {EQV_proj1_EQV : forall A B, 
       iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (EQV_E A B)}.    

  (* ============================================== *)
  (* WELL-FORMED FUNCTION VALUES                    *)
  (* ============================================== *)

    Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
    Variable funWFV : iFunctor WFV.

    Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
      (Sub_Fix_F _) (MAlgebra_typeof_Fix T) (Typeof_F _)}.
    Context {WF_Value_continous_alg : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

    Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.
    Context {eq_DType_eq_D : PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D}.
    Variable WF_Ind_DType_eq_D : WF_Ind eq_DType_eq_D.

     Context {WFV_proj1_a_WFV :
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFV}.    
     Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFV}.    
    Context {eval_continuous_Exp_E : PAlgebra EC_ExpName
      (sig (UP'_P (eval_continuous_Exp_P V (F _) SV))) (F nat)}.
    Context {WF_Ind_EC_Exp : WF_Ind eval_continuous_Exp_E}.

    Global Instance Fix_Soundness eval_rec : 
      iPAlgebra soundness_XName 
      (soundness_X'_P D V F EQV_E WFV
        (fun e => typeof _ _ (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_F _))
        (f_algebra (FAlgebra := eval_F))) (Fix_eqv _ _).
    Proof.
       econstructor; unfold iAlgebra; intros.
       eapply ind_alg_Fix_eqv; try eassumption; unfold soundness_X'_P;
         simpl; intros.
       (* mu case *)
       split; intros.
       apply (inject_i (subGF := Sub_Fix_eqv_EQV_E _ _)) ; econstructor; eauto.
       intros; destruct (IHf a b) as [f_eqv _]; eauto.
       rewrite e_eq; reflexivity.
       rewrite e'_eq; reflexivity.
       unfold eval_alg_Soundness_P.
       unfold beval; simpl; repeat rewrite wf_functor; simpl.
       rewrite e'_eq.
       unfold mu, mu'; simpl; erewrite out_in_fmap;
         repeat rewrite wf_functor; simpl.
       rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl; intros.
       caseEq (g (Datatypes.length gamma'')).
       rewrite <- eval_rec_proj.
       rename H0 into typeof_e.
       rewrite e_eq in typeof_e. 
       rewrite out_in_fmap, fmap_fusion, wf_functor in typeof_e;
         rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)) in typeof_e;
           simpl in typeof_e. 
       rewrite <- typeof_rec_proj in typeof_e.
       caseEq (typeof _ _ (proj1_sig (f (Some t1)))); unfold typeofR, DType, Names.DType, UP'_F in *|-*;
         rename H0 into typeof_f; rewrite typeof_f in typeof_e; try discriminate.
       caseEq (eq_DType _ (proj1_sig t1) d); rename H0 into eq_t1_d;
         rewrite eq_t1_d in typeof_e; try discriminate.
       injection typeof_e; intros; subst; clear typeof_e.
       generalize (eq_DType_eq D WF_Ind_DType_eq_D T d eq_t1_d);
         intros d_eq.
       rewrite eval_rec_proj.
       cut (WFValueC D V WFV (eval_rec (exist _
         (proj1_sig (g (Datatypes.length gamma''))) (proj2_sig (g (Datatypes.length gamma''))))
       (insert (Names.Value V)
         (eval_rec(mu' t2
           (fun a : nat =>
             in_t_UP' (F nat) (Fun_F nat)
             (out_t_UP' (F nat) (Fun_F nat) (proj1_sig (g a)))))
         gamma'') gamma'')) d).
       destruct T as [T T_UP']; destruct d as [d d_UP'].
       intro wf_mu; rewrite <- eval_rec_proj; rewrite H1 in wf_mu; simpl in *|-*.
       apply (WFV_proj1_b _ _ WFV funWFV (mk_WFValue_i _ _ _ _) wf_mu _ _ d_eq).
       intros; destruct (IHf (Some T) (Datatypes.length gamma'')) as [g_eqv _]; eauto.
       destruct (g (Datatypes.length gamma'')) as [gl gl_UP'].
       rewrite eval_rec_proj; eapply IH with 
         (pb := (insert (option (sig Universal_Property'_fold)) (Some T) gamma,
           insert nat (Datatypes.length gamma'') gamma')); eauto.
       assert (Datatypes.length gamma'' = Datatypes.length gamma') by 
         (destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]];
           simpl in *|-*; rewrite <- WF_gamma2; eapply P2_Env_length; eauto).
       rewrite H0.
       eapply WF_eqv_environment_P_insert; eauto.
       destruct T as [T T_UP']; destruct d as [d d_UP'].
       rewrite eval_rec_proj.     
       generalize (fun a b => proj1 (IHf a b IH)) as f_eqv; intros.
       eapply IH.
       eassumption.
       apply (inject_i (subGF := Sub_Fix_eqv_EQV_E _ _)) ; econstructor; simpl;
         try (apply t1_eq); eauto.
       repeat rewrite wf_functor; simpl; repeat apply f_equal;
         apply functional_extensionality; intros.
       rewrite <- (in_out_UP'_inverse _ _ _ (proj2_sig (g x0))) at -1; reflexivity.
       rewrite e_eq.
       revert typeof_f; unfold typeof, mfold, in_t.
       repeat rewrite wf_functor; simpl; rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _));
         simpl; unfold mfold; intros.
       unfold typeofR, DType, Names.DType, UP'_F in *|-*; rewrite typeof_f.
       simpl in eq_t1_d; rewrite eq_t1_d; reflexivity.
     Defined.
 End Mu.
 
(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
