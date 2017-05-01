(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Concrete semantics *)

Set Implicit Arguments.

Require Import List ZArith.
Require Import hpattern vgtac VocabA.
Require Import Global InterCfg IntraCfg IntraNode Syn DomCon DItv.
Require Import SemCommon.

Local Open Scope Z.

Section Sem.

Variable g : G.t.
Let pgm : InterCfg.t := G.icfg g.

Parameter b_not : Z -> Z.
Parameter shiftlt : Z -> Z -> Z.
Parameter shiftrt : Z -> Z -> Z.
Parameter b_and : Z -> Z -> Z.
Parameter b_or : Z -> Z -> Z.
Parameter b_xor : Z -> Z -> Z.

(* NOTE: We do not deal with Float number as of now. *)
Inductive Eval_const : constant -> val_t -> Prop :=
| Eval_const_CInt64_none : forall z, Eval_const (CInt64 None) (val_of_z z)
| Eval_const_CInt64_some : forall z, Eval_const (CInt64 (Some z)) (val_of_z z)
| Eval_const_CChr : forall c, Eval_const (CChr c) (val_of_z c)
| Eval_const_CReal :
    forall z lb ub (Hz : lb <= z <= ub), Eval_const (CReal lb ub) (val_of_z z)
| Eval_const_CEnum : forall z, Eval_const CEnum (val_of_z z).

Inductive Eval_uop : unop -> val_t -> val_t -> Prop :=
| Eval_uop_Neg : forall z, Eval_uop Neg (val_of_z z) (val_of_z (- z))
| Eval_uop_BNot : forall z, Eval_uop BNot (val_of_z z) (val_of_z (b_not z))
| Eval_uop_LNot_t :
    forall z (Ht : z <> 0), Eval_uop LNot (val_of_z z) (val_of_z 0)
| Eval_uop_LNot_f : Eval_uop LNot (val_of_z 0) (val_of_z 1).

Definition c_mod (z1 z2 : Z) := (z1 - (c_div z1 z2) * z2).

Inductive Eval_bop : binop -> val_t -> val_t -> val_t -> Prop :=
| Eval_bop_PlusA :
    forall z1 z2,
      Eval_bop PlusA (val_of_z z1) (val_of_z z2) (val_of_z (z1 + z2))
| Eval_bop_PlusPI :
    forall step alloc o sz st i,
      Eval_bop PlusPI
               (val_of_loc (loc_of_alloc step alloc (o, sz, st) Fields.nil))
               (val_of_z i)
               (val_of_loc (loc_of_alloc step alloc (o + i, sz, st) Fields.nil))
| Eval_bop_IndexPI :
    forall step alloc o sz st i,
      Eval_bop IndexPI
               (val_of_loc (loc_of_alloc step alloc (o, sz, st) Fields.nil))
               (val_of_z i)
               (val_of_loc (loc_of_alloc step alloc (o + i, sz, st) Fields.nil))
| Eval_bop_MinusA :
    forall z1 z2,
      Eval_bop MinusA (val_of_z z1) (val_of_z z2) (val_of_z (z1 - z2))
| Eval_bop_MinusPI :
    forall step alloc o sz st i,
      Eval_bop MinusPI
               (val_of_loc (loc_of_alloc step alloc (o, sz, st) Fields.nil))
               (val_of_z i)
               (val_of_loc (loc_of_alloc step alloc (o - i, sz, st) Fields.nil))
| Eval_bop_Mult :
    forall z1 z2, Eval_bop Mult (val_of_z z1) (val_of_z z2) (val_of_z (z1 * z2))
| Eval_bop_Div :
    forall z1 z2 (Hz : z2 <> 0),
      Eval_bop Div (val_of_z z1) (val_of_z z2) (val_of_z (c_div z1 z2))
| Eval_bop_Mod :
    forall z1 z2 (Hz : z2 <> 0),
      Eval_bop Mod (val_of_z z1) (val_of_z z2) (val_of_z (c_mod z1 z2))
| Eval_bop_Shiftlt :
    forall z1 z2,
      Eval_bop Shiftlt (val_of_z z1) (val_of_z z2) (val_of_z (shiftlt z1 z2))
| Eval_bop_Shiftrt :
    forall z1 z2,
      Eval_bop Shiftrt (val_of_z z1) (val_of_z z2) (val_of_z (shiftrt z1 z2))
| Eval_bop_Lt_t :
    forall z1 z2 (Hlt : z1 < z2),
      Eval_bop Lt (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Lt_f :
    forall z1 z2 (Hge : ~ (z1 < z2)),
      Eval_bop Lt (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_Gt_t :
    forall z1 z2 (Hgt : z1 > z2),
      Eval_bop Gt (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Gt_f :
    forall z1 z2 (Hle : ~ (z1 > z2)),
      Eval_bop Gt (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_Le_t :
    forall z1 z2 (Hle : z1 <= z2),
      Eval_bop Le (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Le_f :
    forall z1 z2 (Hgt : ~ (z1 <= z2)),
      Eval_bop Le (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_Ge_t :
    forall z1 z2 (Hge : z1 >= z2),
      Eval_bop Ge (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Ge_f :
    forall z1 z2 (Hlt : ~ (z1 >= z2)),
      Eval_bop Ge (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_Eq_t :
    forall z1 z2 (Heq : z1 = z2),
      Eval_bop Eq (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Eq_f :
    forall z1 z2 (Hne : z1 <> z2),
      Eval_bop Eq (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_Ne_t :
    forall z1 z2 (Hne : z1 <> z2),
      Eval_bop Ne (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_Ne_f :
    forall z1 z2 (Heq : z1 = z2),
      Eval_bop Ne (val_of_z z1) (val_of_z z2) (val_of_z 0)
| Eval_bop_BAnd :
    forall z1 z2,
      Eval_bop BAnd (val_of_z z1) (val_of_z z2) (val_of_z (b_and z1 z2))
| Eval_bop_BXor :
    forall z1 z2,
      Eval_bop BXor (val_of_z z1) (val_of_z z2) (val_of_z (b_xor z1 z2))
| Eval_bop_BOr :
    forall z1 z2,
      Eval_bop BOr (val_of_z z1) (val_of_z z2) (val_of_z (b_or z1 z2))
| Eval_bop_LAnd_t :
    forall z1 z2 (Hz: z1 <> 0 /\ z2 <> 0),
      Eval_bop LAnd (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_LAnd_lf :
    forall z, Eval_bop LAnd (val_of_z 0) (val_of_z z) (val_of_z 0)
| Eval_bop_LAnd_rf :
    forall z, Eval_bop LAnd (val_of_z z) (val_of_z 0) (val_of_z 0)
| Eval_bop_LOr_lt :
    forall z1 z2 (Hz : z1 <> 0),
      Eval_bop LOr (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_LOr_rt :
    forall z1 z2 (Hz : z2 <> 0),
      Eval_bop LOr (val_of_z z1) (val_of_z z2) (val_of_z 1)
| Eval_bop_LOr_f : Eval_bop LOr (val_of_z 0) (val_of_z 0) (val_of_z 0).

Section SemIntraNode.

Variable step : Step.t.
Variable (cn : InterNode.t).
Let p : Proc.t := InterNode.get_pid cn.

Section SemEval.
Variable (cid : CallId.t).
Variable (m : mem_t).

Definition fields_app1 fs f := Fields.app fs (Fields.cons f Fields.nil).

Inductive Eval_exp : exp -> val_t -> Prop :=
| Eval_Const : forall c pos v (Hc : Eval_const c v), Eval_exp (Const c pos) v
| Eval_Lval :
    forall lv pos l v (Hl : Eval_lv lv l) (Hm : M.MapsTo l v m),
      Eval_exp (Lval lv pos) v
| Eval_SizeOf : forall z pos, Eval_exp (SizeOf (Some z) pos) (val_of_z z)
| Eval_SizeOfE : forall z pos, Eval_exp (SizeOfE (Some z) pos) (val_of_z z)
| Eval_SizeOfStr :
    forall s pos, Eval_exp (SizeOfStr s pos) (val_of_z (string_lengthZ s))
| Eval_AlignOf : forall z pos, Eval_exp (AlignOf z pos) (val_of_z z)
| Eval_AlignOfE : forall e pos z, Eval_exp (AlignOfE e pos) (val_of_z z)
| Eval_UnOp :
    forall op e v v' pos (Hv : Eval_exp e v) (Hu : Eval_uop op v v'),
      Eval_exp (UnOp op e pos) v'
| Eval_BinOp :
    forall op e1 e2 v1 v2 v' pos
           (Hv1 : Eval_exp e1 v1)
           (Hv2 : Eval_exp e2 v2)
           (Hb : Eval_bop op v1 v2 v'),
      Eval_exp (BinOp op e1 e2 pos) v'
| Eval_Question_t :
    forall e1 e2 e3 v z pos
           (Hcond : Eval_exp e1 (val_of_z z))
           (Ht : z <> 0)
           (Hv : Eval_exp e2 v),
      Eval_exp (Question e1 e2 e3 pos) v
| Eval_Question_f :
    forall e1 e2 e3 v pos (Hcond : Eval_exp e1 (val_of_z 0)) (Hv : Eval_exp e3 v),
      Eval_exp (Question e1 e2 e3 pos) v
| Eval_CastE :
    forall e step alloc o sz st st' pos
           o' (Ho': o' = c_div (o * st) st')
           sz' (Hsz': sz' = c_div (sz * st) st')
           l (Hl : l = loc_of_alloc step alloc (o, sz, st) Fields.nil)
           l' (Hl' : l' = loc_of_alloc step alloc (o', sz', st') Fields.nil)
           (Ha : Eval_exp e (val_of_loc l)),
      Eval_exp (CastE (Some st') e pos) (val_of_loc l')
| Eval_AddrOf :
    forall lv pos l (Hl : Eval_lv lv l), Eval_exp (AddrOf lv pos) (val_of_loc l)
| Eval_StartOf :
    forall lv pos l (Hl : Eval_lv lv l), Eval_exp (AddrOf lv pos) (val_of_loc l)

with Eval_lv : lval -> Loc.t -> Prop :=
| Eval_VarLhost_global :
    forall x o pos l (Ho : Resolve_offset (loc_of_gvar x Fields.nil) o l),
      Eval_lv (lval_intro (VarLhost x true) o pos) l
| Eval_VarLhost_local :
    forall x o pos l (Ho : Resolve_offset (loc_of_lvar cid p x Fields.nil) o l),
      Eval_lv (lval_intro (VarLhost x false) o pos) l
| Eval_MemLhost_l :
    forall e o pos l l'
           (Hv : Eval_exp e (val_of_loc l)) (Ho : Resolve_offset l o l'),
      Eval_lv (lval_intro (MemLhost e) o pos) l'

with Resolve_offset : Loc.t -> offset -> Loc.t -> Prop :=
| Resolve_NoOffset : forall l, Resolve_offset l NoOffset l
| Resolve_FOffset :
    forall va fs f o l
           (Ho : Resolve_offset (va, fields_app1 fs f) o l),
      Resolve_offset (va, fs) (FOffset f o) l
| Resolve_IOffset :
    forall alloc o sz st idx e ofs con_l l''
           (Hv : Eval_exp e (val_of_z idx))
           l (Hl : l = loc_of_alloc step alloc (o, sz, st) Fields.nil)
           l' (Hl' : l' = loc_of_alloc step alloc (o + idx, sz, st) Fields.nil)
           (Hm : M.MapsTo con_l (val_of_loc l) m)
           (Ho : Resolve_offset l' ofs l''),
      Resolve_offset con_l (IOffset e ofs) l''.

Inductive Eval_list : list exp -> list val_t -> Prop :=
| Eval_list_nil : Eval_list nil nil
| Eval_list_cons :
    forall e el v vl (Hvl : Eval_list el vl) (Hv : Eval_exp e v),
      Eval_list (e :: el) (v :: vl).

Inductive Eval_lv_opt : option lval -> option Loc.t -> Prop :=
| Eval_lv_none : Eval_lv_opt None None
| Eval_lv_some :
    forall lv l (Hl : Eval_lv lv l), Eval_lv_opt (Some lv) (Some l).

End SemEval.


(* NOTE: When to do function call-related things

* set arguments: the call commands
* remove local variables: the return commands
* push stacks: interprocedural call edge
* pop stacks: interprocedural return edge

Currently, pushing/popping stacks is done in the interprocedural edges
and is a little bit awkward in our setting, in which a user can define
only semantics of commands, not that of edges.  As a result, the
return locations included in the stacks cannot be updated strongly,
though it would not affect the overall precision by the callsite
independency.
 *)

Definition wf_non_rec_mem g m :=
  forall f (Hf : Global.G.is_rec f g = false)
     cid1 cid2 x1 x2 fs1 fs2
     (Hx1 : M.In (elt := val_t) (VarRegion.Inl (Var.Inr (cid1, f, x1)), fs1) m)
     (Hx2 : M.In (elt := val_t) (VarRegion.Inl (Var.Inr (cid2, f, x2)), fs2) m),
    CallId.eq cid1 cid2.

Definition wf_non_rec_call g cid f m :=
  forall (Hf : Global.G.is_rec f g = false)
     cid' f' x fs
     (Hx : M.In (elt := val_t) (VarRegion.Inl (Var.Inr (cid', f', x)), fs) m)
     (Hf : Proc.eq f f'),
    CallId.eq cid cid'.


Inductive Bind_list (cid : CallId.t) (p : Proc.t)
: list vid_t -> list val_t -> mem_t -> mem_t -> Prop :=
| Bind_list_nil : forall m, Bind_list cid p nil nil m m
| Bind_list_cons :
    forall x xl v vl m m'
           l (Hl : l = loc_of_lvar cid p x Fields.nil)
           (Hbl : Bind_list cid p xl vl (M.add l v m) m'),
      Bind_list cid p (x :: xl) (v :: vl) m m'.

Definition val_of_ascii a := val_of_z (Z.of_nat (Ascii.nat_of_ascii a)).

(** Initialize string (array of characters) to memory *)
Inductive Initial_s (a : Allocsite.t)
  : Loc.t -> String.string -> mem_t -> mem_t -> Prop :=
| Initial_s_O :
    forall l o sz (Hl : l = loc_of_alloc step a (o, sz, 1) Fields.nil)
       m m' (Hm : m' = M.add l (val_of_z 0%Z) m)
       (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m'),
      Initial_s a l String.EmptyString m m'
| Initial_s_S :
    forall o sz c s m m' m''
       l (Hl : l = loc_of_alloc step a (o, sz, 1) Fields.nil)
       l' (Hl' : l' = loc_of_alloc step a (o + 1, sz, 1) Fields.nil)
       (Hm : m' = M.add l (val_of_ascii c) m)
       (Htl : Initial_s a l' s m' m'')
       (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m')
       (Hwf3 : wf_non_rec_mem g m''),
      Initial_s a l (String.String c s) m m''.

Definition remove_locals cid m : mem_t :=
  let is_not_local l :=
    match l with
    | (VarRegion.Inl (Var.Inr (cid', p', _)), _) =>
      if CallId.eq_dec cid cid' then false else true
    | _ => true
    end in
  M.filter is_not_local m.

Inductive Run : cmd -> intra_node_state_t -> intra_node_state_t -> Prop :=
| Run_set :
    forall cid m m' d lv e l v pos
           (Hl : Eval_lv cid m lv l)
           (Hv : Eval_exp cid m e v)
           (Hm' : M.add l v m = m')
           (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m'),
      Run (Cset lv e pos) (cid, None, m, d) (cid, None, m', d)
| Run_alloc :
    forall cid m m' d lv e sz l pos
           (Hl : Eval_lv cid m lv l)
           (Hsz : Eval_exp cid m e (val_of_z sz))
           a (Ha : a = Allocsite.Inl cn)
           al (Hal : al = loc_of_alloc step a (0, sz, 1) Fields.nil)
           (Hm' : M.add l (val_of_loc al) m = m')
           (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m'),
      Run (Calloc lv (Array e) pos) (cid, None, m, d) (cid, None, m', d)
| Run_salloc :
    forall cid m m' m'' d lv s l base pos
           (Hl : Eval_lv cid m lv l)
           a (Ha : a = Allocsite.Inl cn)
           sz (Hsz : sz = string_lengthZ s)
           (Hbase : base = loc_of_alloc step a (0, sz, 1) Fields.nil)
           (Hinit : Initial_s a base s m m')
           (Hm'' : M.add l (val_of_loc base) m' = m'')
           (Hwf1 : wf_non_rec_mem g m)
           (Hwf2 : wf_non_rec_mem g m')
           (Hwf3 : wf_non_rec_mem g m''),
      Run (Csalloc lv s pos) (cid, None, m, d) (cid, None, m'', d)
| Run_falloc :
    forall cid m m' d lv name l pos (Hl : Eval_lv cid m lv l)
       (Hm' : M.add l (val_of_proc name) m = m')
       (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m'),
      Run (Cfalloc lv name pos) (cid, None, m, d) (cid, None, m', d)
| Run_assume :
    forall cid m d e z pos (Hv : Eval_exp cid m e (val_of_z z)) (Hprune : z <> 0)
       (Hwf : wf_non_rec_mem g m),
      Run (Cassume e pos) (cid, None, m, d) (cid, None, m, d)
| Run_call :
    forall cid m m' d ret_opt f args l_opt vs callee callee_args pos
           (Hret : Eval_lv_opt cid m ret_opt l_opt)
           (Hf : Eval_exp cid m f (val_of_proc callee))
           (Hf_def : G.is_undef_e f g = None)
           (Hargs : Eval_list cid m args vs)
           (Hargs_p : Some callee_args = InterCfg.get_args pgm callee)
           (Hbind : Bind_list step callee callee_args vs m m')
           (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m'),
      Run (Ccall ret_opt f args pos)
          (cid, None, m, d)
          (step, Some callee, m', (callee, l_opt, cid) :: d)
| Run_return_some :
    forall cid cid' m m' d e v retl pos
           (Hv : Eval_exp cid m e v)
           (Hm' : M.add retl v (remove_locals cid m) = m')
           (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m')
           (Hwf_call : wf_non_rec_call g cid p m),
      Run (Creturn (Some e) pos)
          (cid, None, m, (p, Some retl, cid') :: d)
          (cid', None, m', d)
| Run_return_none :
    forall cid cid' m m' d pos
       (Hm' : remove_locals cid m = m')
       (Hwf1 : wf_non_rec_mem g m) (Hwf2 : wf_non_rec_mem g m')
       (Hwf_call : wf_non_rec_call g cid p m),
      Run (Creturn None pos)
          (cid, None, m, (p, None, cid') :: d)
          (cid', None, m', d)
| Run_asm :
    forall cid opt_ret m d pos (Hwf : wf_non_rec_mem g m),
      Run (Casm pos) (cid, opt_ret, m, d) (cid, opt_ret, m, d)
| Run_skip :
    forall cid opt_ret m d pos (Hwf : wf_non_rec_mem g m),
      Run (Cskip pos) (cid, opt_ret, m, d) (cid, opt_ret, m, d).

End SemIntraNode.

Inductive RunEdge : inter_node_state_t -> inter_node_state_t -> Prop :=
| RunIntra_edge :
    forall p n n' cfg step rets s
           (Hreach : InterCfg.reachables pgm rets p)
           (Hcfg : InterCfg.PidMap.MapsTo p cfg (InterCfg.cfgs pgm))
           (Hedge : IntraCfg.is_succ cfg n n')
           (Hcn_cond: not (InterCfg.is_call_node pgm (p, n))),
      RunEdge ((p, n), step, rets, s) ((p, n'), S step, rets, s)
| RunInter_call :
    forall cn step calls cid callee m d
           (Hreach : InterCfg.reachables pgm calls (InterNode.get_pid cn))
           (Hcn : InterCfg.is_call_node pgm cn)
           (Hsucc : InterCfg.is_succ pgm cn (callee, IntraNode.Entry)),
      RunEdge (cn, step, calls, (cid, Some callee, m, d))
              ((callee, Entry), S step, cn :: calls, (cid, None, m, d))
| RunInter_ret :
    forall p step calln calls s
           (Hreach : InterCfg.reachables pgm (calln :: calls) p)
           retn (Hret : Some retn = InterCfg.returnof pgm calln)
           (Hsucc : InterCfg.is_succ pgm (p, Exit) retn),
      RunEdge ((p, Exit), step, calln :: calls, s) (retn, S step, calls, s).

Axiom init_p : Syn.pid_t.

Definition init_node : InterNode.t := (init_p, Entry).

Definition init_step : Step.t := O.

Definition init_calls : call_nodes_t := nil.

Definition init_callid : CallId.t := O.

Definition init_callee : callee_t := None.

Definition init_mem : M.t val_t := M.empty val_t.

Definition init_stack : stack_t := nil.

Definition init_intra_node_state : intra_node_state_t :=
  (init_callid, init_callee, init_mem, init_stack).

Definition init_s : state_t :=
  (Inputof, (init_node, init_step, init_calls, init_intra_node_state)).

Inductive Sem : state_t -> Prop :=
| Sem_initial : Sem init_s
| Sem_run :
    forall cn step cmd calls s s'
           (Hreach : InterCfg.reachables pgm calls (InterNode.get_pid cn))
           (SemIH : Sem (Inputof, (cn, step, calls, s)))
           (Hcmd : Some cmd = InterCfg.get_cmd pgm cn)
           (Hrun : Run step cn cmd s s'),
      Sem (Outputof, (cn, step, calls, s'))
| Sem_edge :
    forall s s' (SemIH : Sem (Outputof, s)) (Hrun : RunEdge s s'),
      Sem (Inputof, s').

End Sem.

Local Close Scope Z.
