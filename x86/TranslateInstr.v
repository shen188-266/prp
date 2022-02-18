Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Axioms Globalenvs.
Require Import Asm RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
(* Import Hex compcert.encode.Bits.Bits. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import RelocBingen.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope nat_scope.

(** *CAV21: Instruction ,CompCertELF: instruction*)

Definition assertLength {A} (l:list A) n: {length l = n} +
                                          {length l <> n}.
Proof.
  decide equality.
Defined.

Definition builtIn (n:nat): Type := {d:list bool| length d = n}.

Lemma builtin_inj: forall {n} (a b:builtIn n),
    proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n a b H.
  induction a, b.
  simpl in H.
  subst x0.
  f_equal.
  apply UIP_dec.
  apply Nat.eq_dec.
Qed.

Definition u2 := builtIn 2.

Definition u3 := builtIn 3.

Definition u4 := builtIn 4.

Definition u8 := builtIn 8.

Definition u16 := builtIn 16.

Definition u32 := builtIn 32.

Definition nat_to_bits8_opt n : bits :=
  [( n/128 mod 2 =? 1);
  ( n/64 mod 2 =? 1);
  ( n/32 mod 2 =? 1);
  ( n/16 mod 2 =? 1);
  ( n/8 mod 2 =? 1);
  ( n/4 mod 2 =? 1);
  ( n/2 mod 2 =? 1);
  ( n mod 2 =? 1)].

Fixpoint bytes_to_bits_opt (lb:list byte) : bits :=
  match lb with
  | [] => []
  | b::lb' =>(nat_to_bits8_opt (Z.to_nat (Byte.unsigned b))) ++
                                                           (bytes_to_bits_opt lb')
  end.


Program Definition zero32 : u32 :=
  bytes_to_bits_opt (bytes_of_int 4 0).

Program Definition encode_ireg_u3 (r:ireg) : res u3 :=
  do b <- encode_ireg r;
  if assertLength b 3 then    
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_ireg (bs: u3) : res ireg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(RAX)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(RCX)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(RDX)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(RBX)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(RSP)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(RBP)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(RSI)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(RDI)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma ireg_encode_consistency : 
  forall r encoded, 
  encode_ireg_u3 r = OK(encoded) ->
  decode_ireg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_ireg_u3 in H.
  destruct r; simpl in H; 
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma ireg_decode_consistency :
  forall r encoded, 
  decode_ireg encoded = OK(r) -> 
  encode_ireg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_ireg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_ireg_u3; simpl;        (**r calculate encode_ireg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_freg_u3 (r:freg) : res u3 :=
  do b <- encode_freg r;
  if assertLength b 3 then    
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_freg (bs: u3) : res freg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(XMM0)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(XMM1)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(XMM2)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(XMM3)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(XMM4)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(XMM5)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(XMM6)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(XMM7)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma freg_encode_consistency : 
  forall r encoded, 
  encode_freg_u3 r = OK(encoded) ->
  decode_freg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_freg_u3 in H.
  destruct r; simpl in H; 
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma freg_decode_consistency :
  forall r encoded, 
  decode_freg encoded = OK(r) -> 
  encode_freg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_freg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_freg_u3; simpl;        (**r calculate encode_freg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_scale_u2 (ss: Z) :res u2 :=
  do s <- encode_scale ss;
  if assertLength s 2 then    
    OK (exist _ s _)
  else Error (msg "impossible").

Definition decode_scale (bs: u2) : res Z :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(1%Z)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(2%Z)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(4%Z)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(8%Z)      (**r b["011"] *)
  else Error(msg "reg not found")
.

Lemma scale_encode_consistency : 
  forall ss encoded, 
  encode_scale_u2 ss = OK(encoded) ->
  decode_scale encoded = OK(ss).
Proof.
  intros.
  destruct encoded.
  unfold encode_scale_u2 in H; monadInv H.

  destruct (assertLength x0 2); try discriminate.  (**r prove x = x0 *)
  inversion EQ0; subst.

  unfold encode_scale in EQ.
  destruct ss eqn:Ess; try discriminate.
  repeat (destruct p; try discriminate);           (**r generate subgoals for each scale 1/2/4/8 *)
  inversion EQ as [Heq]; subst; simpl;             (**r replace x with exact value *)
  unfold decode_scale; auto.                       (**r get result of function decode_scale *)
Qed.

Program Definition encode_scale_u3 (ss: Z) :res u3 :=
  do s <- encode_scale ss;
  if assertLength s 3 then    
    OK (exist _ s _)
  else Error (msg "impossible").

Lemma scale_decode_consistency :
  forall r encoded, 
  decode_scale encoded = OK(r) -> 
  encode_scale_u2 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1] *)
Admitted.

Program Definition encode_ofs_u8 (ofs :Z) :res u8 :=
  let ofs8 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs8 8 then
    OK (exist _ ofs8 _)
  else Error (msg "impossible").

Program Definition encode_ofs_u16 (ofs :Z) :res u16 :=
  let ofs16 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs16 16 then
    OK (exist _ ofs16 _)
  else Error (msg "impossible").
 
Program Definition encode_ofs_u32 (ofs :Z) :res u32 :=
  let ofs32 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs32 32 then
    OK (exist _ ofs32 _)
  else Error (msg "impossible").

Program Definition decode_ofs_u32 (r:u32) :res Z:=
   let rn := proj1_sig r in
   let n := bits_to_Z rn in
   OK (exist _ n _).
 
(* Addressing mode in CAV21 automatically generated definition *)
Inductive AddrE: Type :=
| AddrE12(uvar3_0:u3)
| AddrE11(uvar32_0:u32)
| AddrE10(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)
| AddrE9(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrE8(uvar3_0:u3)
| AddrE7(uvar32_0:u32)
| AddrE6(uvar3_0:u3)(uvar32_1:u32)
| AddrE5(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrE4(uvar3_0:u3)(uvar32_1:u32).

(* Instruction in CAV21 automatically generated definition *)
Inductive Instruction: Type :=
| Psubl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pbsqrtsd(uvar3_0:u3)(uvar3_1:u3)
| Psbbl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prep_movsl
| Pmovsq_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsq_mr(AddrE:AddrE)(uvar3_0:u3)
| Pminsd(uvar3_0:u3)(uvar3_1:u3)
| Pmaxsd(uvar3_0:u3)(uvar3_1:u3)
| Pbswap32(uvar3_0:u3)
| Pbsrl(uvar3_0:u3)(uvar3_1:u3)
| Pbsfl(uvar3_0:u3)(uvar3_1:u3)
| Paddl_mi(AddrE:AddrE)(uvar32_1:u32)
| Paddl_rr(uvar3_0:u3)(uvar3_1:u3)
| Padcl_rr(uvar3_0:u3)(uvar3_1:u3)
| Padcl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pjcc_rel(uvar4_0:u4)(uvar32_1:u32)
| Pret_iw(uvar16_0:u16)
| Pret
| Pcall_r(uvar3_0:u3)
| Pcall_ofs(uvar32_0:u32)
| Pnop
| Pjmp_m(AddrE:AddrE)
| Pjmp_r(uvar3_0:u3)
| Pjmp_l_rel(uvar32_0:u32)
| Pandps_fm(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_fm(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_f(uvar3_0:u3)(uvar3_1:u3)
| Pcomisd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuld_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubd_ff(uvar3_0:u3)(uvar3_1:u3)
| Paddd_ff(uvar3_0:u3)(uvar3_1:u3)
| Psetcc(uvar4_0:u4)(uvar3_1:u3)
| Pcmov(uvar4_0:u4)(uvar3_1:u3)(uvar3_2:u3)
| Ptestl_rr(uvar3_0:u3)(uvar3_1:u3)
| Ptestl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prorl_ri(AddrE:AddrE)(uvar8_1:u8)
| Prolw_ri(AddrE:AddrE)(uvar8_1:u8)
| Pshld_ri(uvar3_0:u3)(uvar3_1:u3)(uvar8_2:u8)
| Psarl_rcl(uvar3_0:u3)
| Psarl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pshrl_rcl(uvar3_0:u3)
| Pshrl_ri(uvar3_0:u3)(uvar8_1:u8)
| Psall_rcl(uvar3_0:u3)
| Psall_ri(uvar3_0:u3)(uvar8_1:u8)
| Pnotl(uvar3_0:u3)
| Pxorl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pxorl_ri(uvar3_0:u3)(uvar32_1:u32)
| Porl_rr(uvar3_0:u3)(uvar3_1:u3)
| Porl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pidivl_r(uvar3_0:u3)
| Pdivl_r(uvar3_0:u3)
| Pcltd
| Pmull_r(uvar3_0:u3)
| Pimull_ri(uvar3_0:u3)(uvar3_1:u3)(uvar32_2:u32)
| Pimull_rr(uvar3_0:u3)(uvar3_1:u3)
| Psubl_rr(uvar3_0:u3)(uvar3_1:u3)
| Paddl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pnegl(uvar3_0:u3)
| Pleal(AddrE:AddrE)(uvar3_0:u3)
| Pcvttss2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2sd_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2ss_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvttsd2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtss2sd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsd2ss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsw_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovzw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovzw_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovsb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsb_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovzb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovzb_rr(uvar3_0:u3)(uvar3_1:u3)
| Pmovw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_mr(AddrE:AddrE)(uvar3_0:u3)
| Pflds_m(AddrE:AddrE)
| Pfstps_m(AddrE:AddrE)
| Pfstpl_m(AddrE:AddrE)
| Pfldl_m(AddrE:AddrE)
| Pmovss_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovss_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsd_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pmovl_rr(uvar3_0:u3)(uvar3_1:u3).


Section WITH_RELOC_OFS_MAP.

Variable rtbl_ofs_map: reloc_ofs_map_type.

(* Translate ccelf addressing mode to cav21 addr mode *)
Definition translate_Addrmode_AddrE (sofs: Z) (i:instruction) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- instr_reloc_offset i;
        do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          match obase,oindex with
          | None,None =>                    
            OK (AddrE11 zero32)
          | Some base,None =>
            do r <- encode_ireg_u3 base;
              OK (AddrE6 r zero32)
          | None,Some (idx,ss) =>
            do index <- encode_ireg_u3 idx;          
            do scale <- encode_scale_u2 ss;
            if ireg_eq idx RSP then
              (* OK (AddrE7 zero32) *)
              Error (msg "index can not be RSP")
            else
              OK (AddrE9 scale index zero32)
          | Some base,Some (idx,ss) =>
            do scale <- encode_scale_u2 ss;
            do index <- encode_ireg_u3 idx;
            do breg <- encode_ireg_u3 base;          
            if ireg_eq idx RSP then
              Error (msg "index can not be RSP")
                    (* OK (AddrE4 breg zero32)            *)      
            else                                                   
              OK (AddrE5 scale index breg zero32)
          end
        else Error (msg "addend is not equal to ofs")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      do iofs <- instr_reloc_offset i;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        do ofs32 <- encode_ofs_u32 ofs;        
        match obase,oindex with
        | None,None =>            
          OK (AddrE11 ofs32)
        | Some base,None =>
          do r <- encode_ireg_u3 base;          
          OK (AddrE6 r ofs32)             
        | None,Some (idx,ss) =>
          do r <- encode_ireg_u3 idx;
          do scale <- encode_scale_u2 ss;
          if ireg_eq idx RSP then
            (* OK (AddrE7 ofs32) *)
            Error (msg "index can not be RSP")
          else
            OK (AddrE9 scale r ofs32)                          
        | Some base,Some (idx,ss) =>
          do scale <- encode_scale_u2 ss;
          do index <- encode_ireg_u3 idx;
          do breg <- encode_ireg_u3 base;            
          if ireg_eq idx RSP then
            Error (msg "index can not be RSP")
                  (* OK (AddrE4 breg_sig ofs32) *)
          else
            OK (AddrE5 scale index breg ofs32)
        end          
      | _ => Error (msg "impossible")
      end
    end
  end.

(* Translate CAV21 addr mode to ccelf addr mode *)
Definition translate_AddrE_Addrmode (sofs: Z) (i:instruction) (addr:AddrE) : res addrmode :=
  (* need to relocate? *)
  do iofs <- instr_reloc_offset i;
  match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
  | None =>
    match addr with
    | AddrE11 disp =>
      OK (Addrmode None None (inl (bits_to_Z (proj1_sig disp))))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg ( idx);
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else
        OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )  
    | AddrE6 base disp =>
      do b <- decode_ireg ( base);
      OK (Addrmode (Some b) None (inl (bits_to_Z (proj1_sig disp))) )
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg ( idx);
      do b <- decode_ireg ( base);
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | _ => Error (msg "unsupported or impossible")
    end
  | Some _ =>
    do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
    match addr with
    | AddrE11 _ =>
      OK (Addrmode None None (inr (xH,Ptrofs.repr addend)))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg ( idx);      
      OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | AddrE6 base disp =>
      do b <- decode_ireg ( base);
      OK (Addrmode (Some b) None (inr (xH,Ptrofs.repr addend)))
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg ( idx);
      do b <- decode_ireg ( base);
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | _ => Error (msg "unsupported or impossible")
    end
  end.


(* consistency proof *)
Lemma translate_consistency1 : forall ofs i addr addrE,
    translate_Addrmode_AddrE ofs i addr = OK addrE ->
    translate_AddrE_Addrmode ofs i addrE = OK addr.
  intros. destruct addr.
  unfold translate_Addrmode_AddrE in H.
  unfold translate_AddrE_Addrmode.
  destruct base;destruct ofs0;try destruct p;destruct const.
  - monadInv H.
    rewrite EQ.
    cbn [bind].    
    destruct (ZTree.get (x + ofs)%Z rtbl_ofs_map);try congruence.
    monadInv EQ0.
    destruct (ireg_eq i1 RSP);try congruence.
    monadInv EQ5.
Admitted.

(* ccelf instruction to cav21 instruction, unfinished!!! *)
Definition translate_instr (ofs: Z) (i:instruction) : res Instruction :=
  match i with
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg_u3 rd;
    do r1bits <- encode_ireg_u3 r1;
    OK (Pmovl_rr rdbits r1bits)
  | Asm.Pmovl_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovl_rm a rdbits)
  | Asm.Pmovl_ri rd imm =>
    do rdbits <- encode_ireg_u3 rd;
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (Pmovl_ri rdbits imm32)
  | Asm.Pmovl_mr addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovl_mr a rbits)
  | Asm.Pmovsd_ff rd r1 =>
    do rdbits <- encode_freg_u3 rd;
    do r1bits <- encode_freg_u3 r1;
    OK (Pmovsd_ff rdbits r1bits)
  | Asm.Pmovsd_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovsd_fm a rbits)
  | Asm.Pmovsd_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovsd_mf a rbits)
  | Asm.Pmovss_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovss_fm a rbits)
  | Asm.Pmovss_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovss_mf a rbits)
  | Asm.Pfldl_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pfldl_m a)
  | Asm.Pfstpl_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pfstpl_m a)
  | Asm.Pflds_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pflds_m a)
  | Asm.Pfstps_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pfstps_m a)
  (* | Asm.Pxchg_rr rd r => *)
  (*   do rdbits <- encode_ireg_u3 rd; *)
  (*   do rbits <- encode_ireg_u3 r; *)
  (*   Pxchg_rr rdbits rbits *)
  | Asm.Pmovb_mr addr r =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovb_mr a rbits)          
  | Asm.Pmovw_mr addr r =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovw_mr a rbits)           
  | Asm.Pmovzb_rr rd r =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovzb_rr rdbits rbits)
  | Asm.Pmovzb_rm r addr =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovzb_rm a rbits)           
  (*from there*)
  | Asm.Pmovzw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovzw_rm a rbits)
  | Asm.Pmovzw_rr rd rs =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 rs;
     OK (Pmovzw_rr rdbits rbits)
  | Asm.Pmovsb_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovsb_rm a rbits)
  | Asm.Pmovsb_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsb_rr rdbits rbits)  
  | Asm.Pmovw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovzb_rm a rbits)         
  | Asm.Pmovb_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    OK (Pmovzb_rm a rdbits)           
  | Asm.Pmovsw_rm rd addr =>
     do rdbits <- encode_ireg_u3 rd;
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pmovsw_rm a rdbits)
  | Asm.Pmovsw_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsw_rr rdbits rbits) 
  | Asm.Pnegl r =>
     do rbits <- encode_ireg_u3 r;
     OK (Pnegl rbits)
  | Asm.Pleal r addr =>
     do rbits <- encode_ireg_u3 r;
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pleal a rbits)
  | Asm.Pcvttss2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttss2si_rf rdbits rbits)
  | Asm.Pcvtsi2sd_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2sd_fr rdbits rbits)
  | Asm.Pcvtsi2ss_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2ss_fr rdbits rbits)
  | Asm.Pcvttsd2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttsd2si_rf rdbits rbits)
  | Asm.Pcvtss2sd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtss2sd_ff rdbits rbits)
  | Asm.Pcvtsd2ss_ff rd r1=>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtsd2ss_ff rdbits rbits)
  | Asm.Paddl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Paddl_ri rdbits imm32)
  | Asm.Psubl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Psubl_rr rdbits rbits)
  | Asm.Pimull_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pimull_rr rdbits rbits)
  | Asm.Pimull_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pimull_ri rdbits rdbits imm32)
  | Asm.Pmull_r r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pmull_r rbits)
  | Asm.Pcltd => OK (Pcltd)
  | Asm.Pdivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pdivl_r rbits)
  | Asm.Pidivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pidivl_r rbits)
  | Asm.Pandl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pandl_rr rdbits rbits)
  | Asm.Pandl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pandl_ri rdbits imm32)
  | Asm.Porl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Porl_ri rdbits imm32)
  |Asm.Porl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Porl_rr rdbits rbits)
  |Asm.Pxorl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pxorl_rr rdbits rbits)
  | Asm.Pxorl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pxorl_ri rdbits imm32)
  | Asm.Pnotl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pnotl rdbits)
  | Asm.Psall_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Psall_ri rdbits imm8)
  | Asm.Psall_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psall_rcl rdbits)
  | Asm.Pshrl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Pshrl_ri rdbits imm8)
  | Asm.Psarl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Psarl_ri rdbits imm8)
  | Asm.Psarl_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psarl_rcl rdbits)
  | Asm.Pshld_ri rd r1 imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Pshld_ri rdbits rbits imm8)
(*  | Asm.Prolw_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Prolw_ri rdbits imm8) *)
 (* | Asm.Prorl_ri rd imm =>(*define a new function*)
     do a <-  eval_addrmode addr rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Prorl_ri a imm8) *)
  | Asm.Pcmpl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Pcmpl_rr rdbits rbits)
  | Asm.Pcmpl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pcmpl_ri rdbits imm32)
  | Asm.Ptestl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Ptestl_ri rdbits imm32)
  | Asm.Ptestl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Ptestl_rr rdbits rbits)
(*  | Asm.Pcmov c rd r1 =>(*define a new function*)
     do rscond <-(Val.of_optbool (eval_testcond c r1));
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcmov rscond rdbits rbits) *)
(*  | Asm.Psetcc c rd =>
      do rsbits <-(Val.of_optbool (eval_testcond c rd));
      do rdbits <-(Val.of_optbool (eval_testcond c rd));
     OK (Psetcc rsbits rdbits)            *)
  | Asm.Paddd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Paddd_ff rdbits rbits)
  | Asm.Psubd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Psubd_ff rdbits rbits)
  | Asm.Pmuld_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pmuld_ff rdbits rbits)
  | Asm.Pdivs_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pdivsd_ff rdbits rbits)
  | Asm.Pcomisd_ff r1 r2 =>
     do rdbits <- encode_freg_u3 r1;
     do rbits <- encode_freg_u3 r2;
     OK (Pcomisd_ff rdbits rbits)
  | Asm.Pxorps_f rd =>
     do rdbits <- encode_freg_u3 rd;
     OK (Pxorps_f rdbits rdbits)
  | Asm.Pxorps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pxorps_fm a rdbits)
  | Asm.Pandps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pandps_fm a rdbits)
 (*cannot do
 | Asm.Pjmp_l_rel ofs =>(*admitttttttttttttttttttttted*)
     do imm <- Z2u32 ofs;
     OK (Pjmp_l_rel imm) *)
  | Asm.Pjmp_r r sg =>(*admitttttttttttttttttttttted*)
     do rdbits <- encode_ireg_u3 r;
     (*how to use sg*)
     OK (Pjmp_r rdbits)
  | Asm.Pjmp_m addr =>
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pjmp_m a)
  | Asm.Pnop =>
     OK (Pnop)
  | Asm.Pcall_r r sg => (*how to use sg*)
     do rdbits <- encode_ireg_u3 r;
     OK (Pcall_r rdbits)
  | Asm.Pret => OK (Pret)
  | Asm.Pret_iw imm => (*define encode_ofs_u16*)
     do imm16 <- encode_ofs_u16 (Int.intval imm);
     OK (Pret_iw imm16)
(*cannot do | Asm.Pjcc_rel c ofs =>
     OK (Pjcc_rel cond imm) *)
  | Asm.Padcl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Padcl_ri rdbits imm8)
  | Asm.Padcl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Padcl_rr rdbits rbits)
  | Asm.Paddl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Paddl_rr rdbits rbits)
  | Asm.Paddl_mi addr imm =>
     do a <- translate_Addrmode_AddrE ofs i addr;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Paddl_mi a imm32)
  | Asm.Pbsfl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsfl rdbits rbits)
  | Asm.Pbsrl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsrl rdbits rbits)   
  | Asm.Pbswap32 rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pbswap32 rdbits)
  | Asm.Pmaxsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;
     OK (Pmaxsd rdbits rbits)
  | Asm.Pminsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;  
     OK (Pminsd rdbits rbits)
  | Asm.Pmovsq_mr addr rs =>
     do a <- translate_Addrmode_AddrE ofs i addr;
     do rbits <- encode_freg_u3 rs;
     OK (Pmovsq_mr a rbits)
  | Asm.Pmovsq_rm rd addr =>
     do rdbits <- encode_freg_u3 rd;   
     do a <- translate_Addrmode_AddrE ofs i addr;
     OK (Pmovsq_mr a rdbits)
  | Asm.Prep_movsl => OK (Prep_movsl)
  | Asm.Psbbl_rr  rd r2 =>              
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Psbbl_rr rdbits rbits)
  | Asm.Psqrtsd rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pbsqrtsd rdbits rbits)
  | Asm.Psubl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Psubl_ri rdbits imm32)
  | _ => Error (msg "Not exists")
  end.


Definition translate_Instr (ofs: Z) (i:Instruction) : res instruction :=
  match i with
  |Pmovl_rr rdbits r1bits =>
    do rd <- encode_ireg_u3 rdbits;
    do r1 <- encode_ireg_u3 r1bits;
    OK (Pmov_rr rd r1)
  |Pmovl_rm a rdbits =>
    do rd <- encode_ireg_u3 rdbits;
    do addr <- translate_AddrE_Addrmode ofs i a;
    OK (Pmovl_rm rd addr)
  |Pmovl_ri rdbits imm32 =>
    do rdbits <- encode_ireg_u3 rd;
    do imm32 <- encode_ofs_u32 (Int.intval imm);
  | _=>Error (msg "unfinished")
  end.
 
Lemma translate_instr_consistency1 : forall ofs i I,
    translate_instr ofs i = OK I ->
    translate_Instr ofs I = OK i.
Proof.
Admitted.

Lemma translate_Instr_consistency1 : forall ofs i I,
    translate_Instr ofs I = OK i ->
    translate_instr ofs i = OK I.
Proof.
  intros. destruct I.
  -destruct i.
  unfold translate_instr in *. unfold translate_Instr in *.
  

