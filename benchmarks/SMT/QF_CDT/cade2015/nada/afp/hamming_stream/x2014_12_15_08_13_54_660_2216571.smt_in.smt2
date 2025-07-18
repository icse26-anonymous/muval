;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Nat_set$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort Nat_llist$ 0)
(declare-fun lNil$ ()Nat_llist$)
(declare-fun lhd$ (Nat_llist$)Nat$)
(declare-fun ltl$ (Nat_llist$)Nat_llist$)
(declare-fun lCons$ (Nat$ Nat_llist$ )Nat_llist$)
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()Nat$ )
(declare-fun n$a ()Nat$ )
(declare-fun na$ ()Nat$ )
(declare-fun one$ ()Nat$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun lset$ (Nat_llist$ )Nat_set$ )
(declare-fun lnull$ (Nat_llist$ )Bool )
(declare-fun lsetp$ (Nat_llist$ Nat$ )Bool )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun lmerge$ (Nat_llist$ Nat_llist$ )Nat_llist$ )
(declare-fun member$ (Nat$ Nat_set$ )Bool )
(declare-fun smooth$ (Nat$ )Bool )
(declare-fun hamming$ ()Nat_llist$ )
(declare-fun lfinite$ (Nat_llist$ )Bool )
(declare-fun lmember$ (Nat$ Nat_llist$ )Bool )
(declare-fun lmerge$a (Nat_nat_bool_fun_fun$ Nat_llist$ Nat_llist$ )Nat_llist$ )
(declare-fun lsorted$ (Nat_llist$ )Bool )
(declare-fun ldistinct$ (Nat_llist$ )Bool )
(assert (! (not (member$ n$ (lset$ hamming$ ))):named a0 ))
(assert (! (smooth$ n$ ):named a1 ))
(assert (! (less$ n$ na$ ):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (less$ ?v0 na$ )(smooth$ ?v0 ))(member$ ?v0 (lset$ hamming$ )))):named a3 ))
(assert (! (= na$ (times$ p$ n$ )):named a4 ))
(assert (! (= (= hamming$ lNil$ )false ):named a5 ))
(assert (! (ldistinct$ hamming$ ):named a6 ))
(assert (! (lsorted$ hamming$ ):named a7 ))
(assert (! (not (lnull$ hamming$ )):named a8 ))
(assert (! (less$ one$ na$ ):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(lmember$ ?v0 ?v1 ))):named a10 ))
(assert (! (not (lfinite$ hamming$ )):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_llist$ )(?v2 Nat_llist$ ))(=> (member$ ?v0 (lset$ (lmerge$ ?v1 ?v2 )))(or (member$ ?v0 (lset$ ?v1 ))(member$ ?v0 (lset$ ?v2 ))))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_nat_bool_fun_fun$ )(?v2 Nat_llist$ )(?v3 Nat_llist$ ))(=> (member$ ?v0 (lset$ (lmerge$a ?v1 ?v2 ?v3 )))(or (member$ ?v0 (lset$ ?v2 ))(member$ ?v0 (lset$ ?v3 ))))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(lsetp$ ?v1 ?v0 ))):named a14 ))
(assert (! (smooth$ n$a ):named a15 ))
(assert (! (smooth$ na$ ):named a16 ))
(assert (! (=> (forall ((?v0 Nat$ ))(=> (= na$ (times$ p$ ?v0 ))false ))false ):named a17 ))
(check-sat )
;(get-unsat-core )
