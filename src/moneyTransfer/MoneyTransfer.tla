----MODULE MoneyTransfer----
EXTENDS TLC, Naturals, FiniteSets, FiniteSetsExt,
Sequences, FiniteSetsExt_theorems, FiniteSetTheorems

CONSTANTS Empty, NAccount, NTransfer, NAvail

NNat == Nat \ {0}

ASSUME NAccountAssumption == NAccount \in NNat

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME NAvailAssumption == NAvail \in NNat

ASSUME EmptyAssumption == Empty = 0

Account == 1..NAccount

Transfer == 1..NTransfer

EAccount == Account \cup {Empty}

ETransfer == Transfer \cup {Empty}

(***************************************
Transfer -> Account -> credits/debits
Transfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyTransfer {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> <<Empty, Empty>>]

    define {
        opAmount(dc) == dc[3]
        
        transAmount(t) == amount[t]
    
        accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1] = a THEN opAmount(c) ELSE 0, credits)
        
        accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1] = a THEN opAmount(d) ELSE 0, debits)
        
        amountAvail(a) == NAvail + accountCredits(a) - accountDebits(a)
        
        isTransKnownToItem(t, a, dc) == dc[1] = a /\ dc[2] = t
        
        isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)
        
        debitPrecond(t) == ~\E a \in Account:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, credits)
        
        creditPrecond(t) ==
            /\ ~\E a \in Account: isTransKnown(t, a, credits)
            /\ ~isTransKnown(t, accounts[t][2], debits)
            /\ isTransKnown(t, accounts[t][1], debits)
    }

    process (trans \in Transfer)    
    {
        init:
            with (account1 \in Account; account2 \in Account \ {account1}; am \in NNat) {
                await amountAvail(account1) > 0;
                await am <= amountAvail(account1);
                accounts[self] := <<account1, account2>>;
                amount[self] := am;
            };
            
        debit:
            with (a = accounts[self][1]) {
                if (debitPrecond(self)) {
                    debits := debits \cup {<<a, self, transAmount(self)>>};
                } else {
                    skip;
                }
            };
            
        crash:
            either skip or goto debit;

        credit:
            with (a = accounts[self][2]) {
                if (creditPrecond(self)) {
                    credits := credits \cup {<<a, self, transAmount(self)>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "9bf29fc2" /\ chksum(tla) = "b3d8e08")
VARIABLES credits, debits, amount, accounts, pc

(* define statement *)
opAmount(dc) == dc[3]

transAmount(t) == amount[t]

accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1] = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1] = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == NAvail + accountCredits(a) - accountDebits(a)

isTransKnownToItem(t, a, dc) == dc[1] = a /\ dc[2] = t

isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

debitPrecond(t) == ~\E a \in Account:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, credits)

creditPrecond(t) ==
    /\ ~\E a \in Account: isTransKnown(t, a, credits)
    /\ ~isTransKnown(t, accounts[t][2], debits)
    /\ isTransKnown(t, accounts[t][1], debits)


vars == << credits, debits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> <<Empty, Empty>>]
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ \E account1 \in Account:
                   \E account2 \in Account \ {account1}:
                     \E am \in NNat:
                       /\ amountAvail(account1) > 0
                       /\ am <= amountAvail(account1)
                       /\ accounts' = [accounts EXCEPT ![self] = <<account1, account2>>]
                       /\ amount' = [amount EXCEPT ![self] = am]
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << credits, debits >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self][1] IN
                    IF debitPrecond(self)
                       THEN /\ debits' = (debits \cup {<<a, self, transAmount(self)>>})
                       ELSE /\ TRUE
                            /\ UNCHANGED debits
               /\ pc' = [pc EXCEPT ![self] = "crash"]
               /\ UNCHANGED << credits, amount, accounts >>

crash(self) == /\ pc[self] = "crash"
               /\ \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "credit"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "debit"]
               /\ UNCHANGED << credits, debits, amount, accounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self][2] IN
                     IF creditPrecond(self)
                        THEN /\ credits' = (credits \cup {<<a, self, transAmount(self)>>})
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

trans(self) == init(self) \/ debit(self) \/ crash(self) \/ credit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
    
CreditTotal == MapThenSumSet(opAmount, credits)

DebitTotal == MapThenSumSet(opAmount, debits)

AmountIsPending(t) ==
    /\ pc[t] \in {"credit", "debit", "crash"}
    /\ creditPrecond(t)

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

TypeOK ==
    /\ credits \in SUBSET (Account \X Transfer \X Nat)
    /\ \A a \in Account, t \in Transfer: Cardinality({c \in credits: isTransKnownToItem(t, a, c)}) \in 0..1
    /\ debits \in SUBSET (Account \X Transfer \X Nat)
    /\ \A a \in Account, t \in Transfer: Cardinality({d \in debits: isTransKnownToItem(t, a, d)}) \in 0..1
    /\ IsFiniteSet(credits)
    /\ IsFiniteSet(debits)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccount \X EAccount]
    /\ pc \in [Transfer -> {"Done","init","debit","credit", "crash"}]
    /\ NTransferAssumption

Inv ==
    /\ TypeOK
    /\ Imbalance = 0

IndInv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = <<Empty, Empty>>
        \/ /\ accounts[t][1] # accounts[t][2]
            /\ accounts[t][1] # Empty
            /\ accounts[t][2] # Empty
    /\ \A t \in Transfer: pc[t] = "init" => ~\E a \in Account: isTransKnown(t, a, debits)
    /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=>
            /\ accounts[t][1] # Empty
            /\ accounts[t][2] # Empty

IndSpec == /\ IndInv /\ [][Next]_vars

BalanceSmall == 0..1

AmountSmall == 0..2

LimitedIndInv ==
    /\ \A a \in Account: accountCredits(a) \in BalanceSmall
    /\ \A a \in Account: accountDebits(a) \in BalanceSmall
    /\ \A t \in Transfer: transAmount(t) \in AmountSmall


LEMMA transAmountNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount


LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY DEF Transfer
<1>2 \A t \in Transfer: t <= NTransfer BY DEF Transfer
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat


LEMMA ASSUME Init, NAccountAssumption
PROVE Imbalance = 0
<1> USE DEF Init, Account, Transfer
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, transPending, creditPrecond
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


LEMMA debit_DebitTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE DebitTotal' = DebitTotal + transAmount(self)
<1> DEFINE a == accounts[self][1]
<1> DEFINE nadd == <<a, self, transAmount(self)>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin debits BY DEF isTransKnown, isTransKnownToItem
<1>2 debits' = debits \cup {nadd} BY DEF debit
<1>3 \A nb \in debits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY transAmountNat DEF opAmount
<1>5 MapThenSumSet(opAmount, debits') =
    MapThenSumSet(opAmount, debits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 DebitTotal' = DebitTotal + opAmount(nadd)
    BY <1>5 DEF DebitTotal
<1> QED BY <1>6 DEF opAmount


LEMMA debit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal + transAmount(self)
<1>1 transPending' = transPending \cup {self}
    BY DEF transPending, debit, AmountIsPending, isTransKnown
<1> USE DEF IndInv, TypeOK
<1>2 self \notin transPending
    BY DEF transPending, AmountIsPending, isTransKnown, isTransKnownToItem, debitPrecond, creditPrecond
<1>3 transAmount(self) \in Nat BY transAmountNat
<1>4 IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset DEF transPending
<1>5 \A am \in transPending: transAmount(am) \in Nat
    BY DEF AmountIsPending, isTransKnown, transAmount, transPending
<1> HIDE DEF IndInv, TypeOK
<1>6 MapThenSumSet(transAmount, transPending') =
    MapThenSumSet(transAmount, transPending) + transAmount(self)
    BY <1>1, <1>2, <1>3, <1>4, <1>5, MapThenSumSetAddElem
<1>7 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY DEF debit, transPending, AmountIsPending
<1>9 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>7, <1>8
<1> QED BY <1>6, <1>9 DEF AmountPendingTotal


LEMMA debit_CreditTotal == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE CreditTotal' = CreditTotal
PROOF BY DEF IndInv, debit


LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE Imbalance' = Imbalance
PROOF BY debit_DebitTotal, debit_CreditTotal, debit_AmountPendingTotal DEF debit, Imbalance


LEMMA ASSUME IndInv, NEW self \in Transfer, debit(self),
NEW a, a = accounts[self][1],
debitPrecond(self)
PROVE Cardinality({d \in debits': isTransKnownToItem(self, a, d)}) \in 0..1
<1> USE DEF IndInv, TypeOK
<1> DEFINE nadd == <<a, self, transAmount(self)>>
<1> DEFINE selfDebit == {d \in debits: isTransKnownToItem(self, a, d)}
<1> DEFINE selfDebitNext == {d \in debits': isTransKnownToItem(self, a, d)}
<1>1 selfDebit = {} BY DEF isTransKnown, isTransKnownToItem, debitPrecond
<1>2 selfDebitNext = {nadd} BY <1>1 DEF debit, debitPrecond, isTransKnown, isTransKnownToItem
<1>3 Cardinality(selfDebit) = 0 BY <1>1, FS_EmptySet
<1>4 Cardinality(selfDebitNext) = 1 BY <1>2, FS_Singleton
<1> QED BY <1>3, <1>4

====
