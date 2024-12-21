---- MODULE MoneyTransfer_proofsCommon ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetTheorems

CONSTANTS NAccount, NTransfer

ASSUME AccountAssumption == Account = 1..NAccount

ASSUME TransferAssumption == Transfer = 1..NTransfer

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME NAccountAssumption == NAccount \in NNat

ASSUME AvailAssumption == Avail \in NNat

ASSUME EmptyAssumption == Empty = 0


LEMMA transSetIsFinite == IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY TransferAssumption
<1>2 \A t \in Transfer: t <= NTransfer BY TransferAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals, NTransferAssumption DEF NNat


LEMMA accountSetIsFinite == IsFiniteSet(Account)
<1>1 Account \in SUBSET (Nat) BY AccountAssumption
<1>2 \A t \in Account: t <= NAccount BY AccountAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals, NAccountAssumption DEF NNat

====
